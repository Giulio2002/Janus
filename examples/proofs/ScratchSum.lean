import Extracted

/-!
# `ScratchSum(a, b uint64) uint64` with a `sync.Pool`-backed scratch buffer (arm64)

```go
var scratchPool sync.Pool // New is nil

func ScratchSum(a, b uint64) uint64 {
	s, _ := scratchPool.Get().(*scratch)
	if s == nil {
		s = new(scratch)
	}
	s.w[0] = a
	s.w[1] = b
	r := s.w[0] ^ s.w[1]
	scratchPool.Put(s)
	return r
}
```

The pattern of `math/big`'s scratch-stack pool (`getStack`, `stack.free`).

**Guarantee.** For every runtime `R` (the live runtime of `Janus.Contracts.Live`, agent/alloc2's
interface), every implementation of `sync.(*Pool).Get`, `sync.(*Pool).Put` (`PoolGetLive`,
`PoolPutLive`, `Janus/Contracts/Pool.lean`) and `runtime.newobject` (`NewobjectLiveContract`)
satisfying the live contracts for `R`, every live set `L` and budget `bud` at which the runtime's
invariant holds and every Go call state in which `scratchPool` (a pool with a nil `New`) is served
by `R`, the stack window `[SP-4144, SP+24)` is writable and apart from `R.rt` and from the live
objects, the call returns `a ^ b` and:

* the buffer it used, `[d, d+32)`, is a pooled `*scratch` or a fresh one from the allocator, and
  was written (`a`, `b` in its first two words) before it went back to the pool;
* memory changed only in `R.rt`, the stack window and the buffer, and **no object of `L` changed**;
* the runtime's invariant holds again for the same live set `L` (the buffer is not the caller's any
  more) and the budget `bud` (a pooled buffer) or `bud - 32` (a fresh one), so the caller can go on
  calling the runtime.

**Assumptions (all in the statement).** The contracts (docs/RUNTIME-CONTRACTS.md, "sync.Pool"),
for one goroutine (docs/SOUNDNESS.md, "The single-threaded assumption"); that a pooled buffer is a
usable `*scratch` (`BufObj`: 32 writable bytes) is the shape the pool's user fixes, and that the
runtime's memory does not contain the nil page (`∀ r ∈ R.rt, 0 < r.1`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool
  Janus.Contracts Janus.Contracts.Pool

namespace Proof

/-- The frame bookkeeping tactic: a goal `Outside a n X → Outside a n Y ∧ …` about lists of the form
`rt ++ [ranges]` is arithmetic over the atom `Outside a n rt`. -/
macro "frame_sub" : tactic =>
  `(tactic| (intro a n h; simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack] at h ⊢; grind))

/-- The address of `scratchPool` (`ADRP`+`ADD` at `ScratchSum+0x20`). -/
def poolAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.ScratchSum" 8)
    (segWord Extracted.program "example.com/basic.ScratchSum" 9) 0

/-- The type word of `*scratch` (`ADRP`+`ADD` at `ScratchSum+0x2c`), which the type assertion
compares with. -/
def ptrType : Nat :=
  adrpLdTarget (Extracted.entry + 0x2c) (segWord Extracted.program "example.com/basic.ScratchSum" 11)
    (segWord Extracted.program "example.com/basic.ScratchSum" 12) 0

/-- The type descriptor of `scratch` (`ADRP`+`ADD` at `ScratchSum+0x44`), `newobject`'s
argument. -/
def bufType : Nat :=
  adrpLdTarget (Extracted.entry + 0x44) (segWord Extracted.program "example.com/basic.ScratchSum" 17)
    (segWord Extracted.program "example.com/basic.ScratchSum" 18) 0

/-- The shape of a pooled `*scratch`: 32 writable bytes at a non-nil, 8-aligned address, owning
exactly that range. Its contents are arbitrary. -/
def BufObj : PoolShape := fun m d rs =>
  0 < d ∧ d % 8 = 0 ∧ d + 32 ≤ 2 ^ 48 ∧ m.accessible d 32 true = true ∧ rs = [(d, d + 32)]

/-- A range inside the window is outside the runtime. -/
theorem outside_rt_of_win {rt : List (Nat × Nat)} {lo hi a n : Nat} (h : LiveSep [(lo, hi)] rt)
    (h1 : lo ≤ a) (h2 : a + n ≤ hi) : Outside a n rt :=
  Outside.of_sub (h _ (List.mem_singleton_self _)) h1 (by simp only; omega)

/-- The precondition of the `Put` of the buffer `[d, d+32)` (held in the live set `L ++ [(d, d+32)]`) at
the call state `S`, `48` bytes below the entry state `s`, whose memory changed since `s` only in
`R.rt` and the window. -/
theorem putPre (R : RtInv) (L : List (Nat × Nat)) (bd d cP : Nat) (s S : State)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4144 < s.sp.toNat)
    (ha4 : s.sp.toNat + 24 ≤ 2 ^ 48)
    (hw4 : s.mem.accessible (s.sp.toNat - 4144) (4144 + 24) true = true)
    (hal : s.sp.toNat % 16 = 0) (hb4 : 4144 ≤ s.sp.toNat)
    (hgo : Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4144, s.sp.toNat + 24) :: R.rt))
    (hwrt : LiveSep [(s.sp.toNat - 4144, s.sp.toNat + 24)] R.rt)
    (hokP : R.ok cP [poolAddr])
    (hfr : MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))
    (hg : S.regs 28 = s.regs 28) (hsp : S.sp.toNat + 48 = s.sp.toNat) (h30a : (S.regs 30).toNat % 4 = 0)
    (h30b : (S.regs 30).toNat < 2 ^ 48) (h0 : (S.regs 0).toNat = poolAddr) (h1 : (S.regs 1).toNat = ptrType)
    (h2 : (S.regs 2).toNat = d) (hsh : BufObj S.mem d [(d, d + 32)])
    (hwL1 : LiveSep (L ++ [(d, d + 32)]) [(s.sp.toNat - 4144, s.sp.toNat + 24)])
    (hinvS : R.inv bd (L ++ [(d, d + 32)]) (S.regs 28).toNat (view R.rt (L ++ [(d, d + 32)]) S.mem)) :
    CallOK S 4096 3 ∧ StackRoom S 4096 3 ∧ (S.regs 1).toNat = ptrType ∧
      BufObj S.mem (S.regs 2).toNat [(d, d + 32)] ∧ (∀ r ∈ [(d, d + 32)], r ∈ L ++ [(d, d + 32)]) ∧
      LiveAt R cP [(S.regs 0).toNat] (L ++ [(d, d + 32)]) bd 0 (S.regs 28).toNat S.mem
        (calleeStack S 4096 3) := by
  have h := call_pre R (L ++ [(d, d + 32)]) bd 0 cP [(S.regs 0).toNat] (s := s) (S := S)
    (lo := s.sp.toNat - 4144) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 3) (fr := 48) hg1 hg2
    (by omega) hgo hfr hg hsp (by omega) h30a h30b (by decide) (by omega) (by omega) (by omega) ha4
    (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4144) = 4144 + 24 by omega]; exact hw4) hwrt hwL1
    (by rw [h0]; exact hokP) hinvS (Nat.zero_le _)
  exact ⟨h.1, h.2.1, h1, by rw [h2]; exact hsh, fun r hr => by simp at hr; simp [hr], h.2.2⟩

/-- The caller's stack slots a function keeps across its calls: the spilled arguments, the saved
`LR` and frame pointer. -/
def StackFacts (sp0 a b ret fp : Nat) (m : Memory) : Prop :=
  m.readLE (sp0 + 8) 8 = a ∧ m.readLE (sp0 + 16) 8 = b ∧ m.readLE (sp0 - 48) 8 = ret % 2 ^ 64 ∧
    m.readLE (sp0 - 56) 8 = fp

/-- A call (at most three arguments) from the function's frame, `48` bytes below the entry `SP`,
keeps those slots: they lie in the function's window, apart from the runtime, and outside the
callee's. -/
theorem StackFacts.step {rt : List (Nat × Nat)} {sp0 a b ret fp n : Nat} {m m' : Memory}
    (hwrt : LiveSep [(sp0 - 4144, sp0 + 24)] rt) (hsp : 4144 ≤ sp0) (hn : n ≤ 3)
    (h : StackFacts sp0 a b ret fp m)
    (hfr : MemFrame m m' (rt ++ [(sp0 - 48 - 4096, sp0 - 48 - 8), (sp0 - 48 + 8, sp0 - 48 + 8 + 8 * n)])) :
    StackFacts sp0 a b ret fp m' := by
  have hr : ∀ x, sp0 - 4144 ≤ x → x + 8 ≤ sp0 + 24 → Outside x 8 rt := fun x h1 h2 =>
    Outside.of_sub (hwrt _ (List.mem_singleton_self _)) h1 (by simp only; omega)
  have hrd : ∀ x, sp0 - 56 ≤ x → x + 8 ≤ sp0 - 40 ∨ sp0 + 8 ≤ x → x + 8 ≤ sp0 + 24 → Outside x 8 (rt ++
      [(sp0 - 48 - 4096, sp0 - 48 - 8), (sp0 - 48 + 8, sp0 - 48 + 8 + 8 * n)]) := by
    intro x h1 h2 h3
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hr x (by omega) h3, by omega, by omega⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hfr.readLE _ _ (hrd _ (by omega) (Or.inr (by omega)) (by omega))]; exact h1,
    by rw [hfr.readLE _ _ (hrd _ (by omega) (Or.inr (by omega)) (by omega))]; exact h2,
    by rw [hfr.readLE _ _ (hrd _ (by omega) (Or.inl (by omega)) (by omega))]; exact h3,
    by rw [hfr.readLE _ _ (hrd _ (by omega) (Or.inl (by omega)) (by omega))]; exact h4⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (R : RtInv)
    (hget : PoolGetLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Get")
      4096 R ptrType BufObj)
    (hput : PoolPutLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Put")
      4096 R ptrType BufObj)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (a b : BitVec 64) (L : List (Nat × Nat)) (bud : Nat) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 4144 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4144, s.sp.toNat + 24) :: R.rt) ∧
        LiveSep [(s.sp.toNat - 4144, s.sp.toNat + 24)] R.rt ∧
        LiveSep L [(s.sp.toNat - 4144, s.sp.toNat + 24)] ∧
        (∀ r ∈ R.rt, 0 < r.1) ∧ (poolAddr + 40 ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ poolAddr) ∧
        Outside bufType 16 R.rt ∧
        R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
        R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [bufType] ∧
        s.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
        R.inv bud L (s.regs 28).toNat (view R.rt L s.mem) ∧ 32 ≤ bud)
      (fun s s' => (s'.regs 0).toNat = (a ^^^ b).toNat ∧
        ∃ d b', (b' = bud ∨ b' = bud - 32) ∧
          MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24), (d, d + 32)]) ∧
          LiveFrame s.mem s'.mem L [] ∧ R.inv b' L (s.regs 28).toNat (view R.rt L s'.mem)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb4, ha4, hw4⟩, hd, hgo, hwrt, hwL, hrt0, hpin, hbin, hokG, hokP, hokN,
    hnew0, hinv, hbud⟩
  janus_intro hs
  janus_eval_nat hP : poolAddr
  janus_eval_nat hT : ptrType
  janus_eval_nat hB : bufType
  rw [hP] at hpin hokG hokP hnew0
  rw [hB] at hbin
  janus_data hd [hw4]
  have hdesc : s.mem.readLE 737984 8 = 32 ∧ s.mem.readLE (737984 + 8) 8 = 0 :=
    ⟨by rw [h_rodata 737984 8 (by decide +kernel)]; decide +kernel,
      by rw [h_rodata (737984 + 8) 8 (by decide +kernel)]; decide +kernel⟩
  have hbW : Outside 737984 16 [(s.sp.toNat - 4144, s.sp.toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hsp48 : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hpw := hpin
  have hgo' := hgo
  simp only [outside_cons, outside_nil, and_true] at hgo'
  have key1 : ∀ S : State, MemFrame s.mem S.mem [(s.sp.toNat - 4144, s.sp.toNat + 24)] →
      S.regs 28 = s.regs 28 → S.sp.toNat + 48 = s.sp.toNat → (S.regs 30).toNat % 4 = 0 →
      (S.regs 30).toNat < 2 ^ 48 → (S.regs 0).toNat = 1547776 →
      CallOK S 4096 1 ∧ StackRoom S 4096 1 ∧ S.mem.readLE (1547776 + newOffset) 8 = 0 ∧
      LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Get") [(S.regs 0).toNat] L bud 0
        (S.regs 28).toNat S.mem (calleeStack S 4096 1) := by
    intro S hf hg hsp h30a h30b h0
    have h := call_pre R L bud 0 (Extracted.program.contractAddr "sync.(*Pool).Get") [(S.regs 0).toNat]
      (s := s) (S := S) (lo := s.sp.toNat - 4144) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 1) (fr := 48)
      hg1 hg2 (by omega) hgo (hf.widen R.rt) hg hsp (by omega) h30a h30b (by decide) (by omega) (by omega)
      (by omega) ha4
      (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4144) = 4144 + 24 by omega]; exact hw4) hwrt hwL
      (by rw [h0]; exact hokG) (by rw [hg]; exact RtInv.inv_frame hf hwrt hinv) (Nat.zero_le _)
    refine ⟨h.1, h.2.1, ?_, h.2.2⟩
    rw [hf.readLE _ _ (by simp only [newOffset, outside_cons, outside_nil, and_true]; omega)]
    exact hnew0
  janus_run until [Extracted.program.contractAddr "sync.(*Pool).Get"]
  refine Reaches.call (Summary.withExit (hget L bud) hret) rfl
    (key1 _ (by janus_frame) (by simp [setReg]) (by simp [hsp48]; omega) (by simp [setReg])
      (by simp [setReg]) (by simp [setReg])) ?_
  intro s1 hpc1 ⟨r, vr, fl, m1, ex1, ep1, hs1, hfr1, hlf1, hns1, hcase⟩
  subst hs1
  simp only [calleeStack, setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, hsp48] at hfr1 hlf1 hns1 hcase
  have hF1 : MemFrame s.mem m1 (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
    MemFrame.trans (rs := [(s.sp.toNat - 4144, s.sp.toNat + 24)]) (by janus_frame) hfr1 (by frame_sub)
  have hLF1 : LiveFrame s.mem m1 L [] :=
    LiveFrame.trans (LiveFrame.of_win (ws := [(s.sp.toNat - 4144, s.sp.toNat + 24)]) (by janus_frame) hwL) hlf1
      (fun _ _ h => h)
  rcases hcase with ⟨hr0, hr1, hinvG⟩ | ⟨rs, hr0, hSh, hfresh, hinrt, hsep, hinvG⟩
  · -- nothing in the pool: a new buffer
    have hr0' : r 0 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hr0)
    have hr1' : r 1 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hr1)
    -- the descriptor of `scratch` (32 bytes, no pointers), as the runtime's invariant has it
    have hoB : ∀ a k, 737984 ≤ a → a + k ≤ 737984 + 16 →
        Outside a k (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) := fun a k h1 h2 => by
      simp only [outside_append]
      exact ⟨Outside.of_sub hbin h1 h2, Outside.of_sub hbW h1 h2⟩
    have hsz : m1.readLE 737984 8 = 32 := by
      rw [hF1.readLE _ _ (hoB _ _ (Nat.le_refl _) (by omega))]; exact hdesc.1
    have hpb : m1.readLE (737984 + 8) 8 = 0 := by
      rw [hF1.readLE _ _ (hoB _ _ (by omega) (by omega))]; exact hdesc.2
    janus_run until [Extracted.program.contractAddr "runtime.newobject"]
    have key2 : ∀ S : State, S.mem = m1 → S.regs 28 = s.regs 28 → S.sp.toNat + 48 = s.sp.toNat →
        (S.regs 30).toNat % 4 = 0 → (S.regs 30).toNat < 2 ^ 48 → (S.regs 0).toNat = 737984 →
        (NewobjectPre 4096 S ∧ StackRoom S 4096 1 ∧
          LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(S.regs 0).toNat] L bud
            (newobjectRound S) (S.regs 28).toNat S.mem (calleeStack S 4096 1)) ∧
          0 < typSize S.mem (S.regs 0).toNat := by
      intro S hm hg hsp h30a h30b h0
      have hr : typSize S.mem (S.regs 0).toNat = 32 := by simp only [typSize, hm, h0]; exact hsz
      have hp : typPtrBytes S.mem (S.regs 0).toNat = 0 := by simp only [typPtrBytes, hm, h0]; exact hpb
      have hround : newobjectRound S = 32 := by
        simp only [newobjectRound, hr, typNoscan, hp]; decide
      have h := call_pre R L bud 32 (Extracted.program.contractAddr "runtime.newobject") [(S.regs 0).toNat]
        (s := s) (S := S) (lo := s.sp.toNat - 4144) (hi := s.sp.toNat + 24) (stack := 4096) (nargs := 1)
        (fr := 48) hg1 hg2 (by omega) hgo (by rw [hm]; exact hF1) hg hsp (by omega) h30a h30b (by decide)
        (by omega) (by omega) (by omega) ha4
        (by rw [show s.sp.toNat + 24 - (s.sp.toNat - 4144) = 4144 + 24 by omega]; exact hw4) hwrt hwL
        (by rw [h0]; exact hokN) (by rw [hm, hg]; exact hinvG) hbud
      rw [hround]
      refine ⟨⟨⟨h.1, ⟨by omega, ?_⟩, ?_⟩, h.2.1, h.2.2⟩, by omega⟩
      · rw [hm, h0, hF1.accessible]; exact Memory.accessible_mono _ h_data1 (by omega) (by omega)
      · rw [hr]; simp [maxAlloc]
    refine Reaches.call (Summary.withExit (hnew.pos L bud) hret) rfl
      (key2 _ rfl (by simp [setReg, Map.keepABI]) (by simp [hsp48]; omega) (by simp [setReg])
        (by simp [setReg]) (by simp [setReg])) ?_
    intro s2 hpc2 ⟨ptr, junk, f2, v2, m2, ex2, ep2, hs2, hfr2, hlf2, ⟨hobj, hapL⟩, hapS, hinv2⟩
    subst hs2
    simp only [retStateX, calleeStack, newobjectObj, Fresh, newobjectRound, setReg_apply, reduceIte,
      Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hsp48, typSize, typNoscan,
      typPtrBytes, hsz, hpb, Map.keepABI_apply, or_true, true_or, ite_true] at hfr2 hlf2 hobj hapL hapS hinv2
    have hbs : blockSize 32 (0 == 0) = 32 := by decide
    rw [hbs] at hobj hapL hapS hinv2
    obtain ⟨hin, hbd, hacc, hal8, -, hzero, -⟩ := hobj
    have hal8' : BitVec.toNat ptr % 8 = 0 := by simpa using hal8
    have hF2 : MemFrame s.mem m2 (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
      MemFrame.trans hF1 hfr2 (by frame_sub)
    have hw2 : m2.accessible (s.sp.toNat - 4144) (4144 + 24) true = true := by
      rw [hF2.accessible]; exact hw4
    have hacc16 : m2.accessible (BitVec.toNat ptr) 16 true = true :=
      Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    have hptr0 : 0 < BitVec.toNat ptr := by
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := hrt0 r hr
      omega
    have hA8t : m2.accessible (BitVec.toNat ptr) 8 true = true :=
      Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    have hA8f : m2.accessible (BitVec.toNat ptr) 8 false = true :=
      Memory.accessible_sub _ hacc (Or.inl rfl) (Nat.le_refl _) (by omega)
    have hB8t : m2.accessible (BitVec.toNat ptr + 8) 8 true = true :=
      Memory.accessible_mono _ hacc (by omega) (by omega)
    have hB8f : m2.accessible (BitVec.toNat ptr + 8) 8 false = true :=
      Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega)
    have hSF1 : StackFacts s.sp.toNat a.toNat b.toNat ret (s.regs 29).toNat m1 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [hfr1.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack]
          exact ⟨outside_rt_of_win hwrt (by omega) (by omega), by omega, by omega⟩)]
        repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
        rw [Memory.readLE_writeLE_self]
        try first | exact Nat.mod_eq_of_lt a.isLt | exact Nat.mod_eq_of_lt b.isLt | rfl | exact Nat.mod_eq_of_lt (s.regs 29).isLt
    have hSF2 : StackFacts s.sp.toNat a.toNat b.toNat ret (s.regs 29).toNat m2 :=
      StackFacts.step (n := 1) hwrt hb4 (by omega) hSF1 hfr2
    have hpack := And.intro hapL (And.intro hinv2 (And.intro hF1 (And.intro hF2 (And.intro hfr2
      (And.intro hLF1 (And.intro hlf2 (And.intro hfr1 (And.intro hns1 hSF2))))))))
    clear hpc2 hal8 hzero key2 key1 hrt0 hlf2 hlf1 hapS hapL hinv2 hF1 hF2 hfr2 hLF1 hfr1 hns1 hSF2 hSF1 hinvG
    janus_run until [Extracted.program.contractAddr "sync.(*Pool).Put"]
    obtain ⟨hapL, hinv2, hF1, hF2, hfr2, hLF1, hlf2, hfr1, hns1, hSF2⟩ := hpack
    obtain ⟨hA2, hB2, hLR2, hFP2⟩ := hSF2
    rw [hA2, hB2]
    have hpd := InRanges.disjoint hin (hwrt _ (List.mem_singleton_self _))
    simp only at hpd
    have hF3 : MemFrame s.mem ((m2.writeLE (BitVec.toNat ptr) 8 a.toNat).writeLE (BitVec.toNat ptr + 8) 8 b.toNat)
        (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
      (hF2.writeLE_inRanges _ ((hin.sub (a := BitVec.toNat ptr) (n := 8) (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
        ((hin.sub (a := BitVec.toNat ptr + 8) (n := 8) (by omega) (by omega)).append_left _)
    have hSFS3 : StackFacts s.sp.toNat a.toNat b.toNat ret (s.regs 29).toNat
        ((m2.writeLE (BitVec.toNat ptr) 8 a.toNat).writeLE (BitVec.toNat ptr + 8) 8 b.toNat) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
        first | exact hA2 | exact hB2 | exact hLR2 | exact hFP2
    have hnm : ∀ r ∈ L, r ∉ [(BitVec.toNat ptr, BitVec.toNat ptr + 32)] := fun r hr hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact notMem_of_apartAll (by omega) hapL hr
    refine Reaches.call (Summary.withExit (hput (L ++ [(BitVec.toNat ptr, BitVec.toNat ptr + 32)]) (bud - 32)
      [(BitVec.toNat ptr, BitVec.toNat ptr + 32)]) hret) rfl
      (putPre R L (bud - 32) (BitVec.toNat ptr) _ s _ hg1 hg2 hg3 ha4 hw4 hal hb4 hgo hwrt (by rw [hP]; exact hokP)
        hF3 (by simp [setReg, Map.keepABI, callRegs_apply]) (by simp [hsp48]; omega) (by simp [setReg]) (by simp [setReg])
        (by simp [setReg, hP]) (by simp [setReg, hT]) (by simp [setReg])
        (by
          refine ⟨hptr0, hal8', by omega, ?_, rfl⟩
          simp only [Memory.accessible_writeLE]; exact hacc)
        (by
          rw [liveSep_append]
          refine ⟨hwL, ?_⟩
          simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true]
          omega)
        (by
          have := RtInv.inv_frame' (ws := [(BitVec.toNat ptr, BitVec.toNat ptr + 32)]) (m := m2)
            (m' := (m2.writeLE (BitVec.toNat ptr) 8 a.toNat).writeLE (BitVec.toNat ptr + 8) 8 b.toNat)
            (((MemFrame.refl m2 [(BitVec.toNat ptr, BitVec.toNat ptr + 32)]).writeLE a.toNat
              (List.mem_singleton_self _) (Nat.le_refl _) (by simp)).writeLE b.toNat
              (List.mem_singleton_self _) (by simp) (by simp <;> omega))
            (fun r hr => Or.inr (by
              simp only [List.mem_singleton] at hr; rw [hr]
              exact ⟨(BitVec.toNat ptr, BitVec.toNat ptr + 32),
                List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by simp⟩)) hinv2
          simpa [setReg, Map.keepABI, callRegs_apply] using this)) ?_
    intro s3 hpc3 ⟨r3, vr3, fl3, m3, ex3, ep3, hs3, hfr3, hlf3, hns3, hinv3⟩
    subst hs3
    simp only [calleeStack, setReg_apply, Map.keepABI_apply, reduceIte, Nat.reduceEqDiff,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hsp48, or_true, true_or, ite_true, callRegs_apply,
      dropAll_append_self hnm] at hfr3 hlf3 hinv3
    have hSF3 := StackFacts.step (n := 3) hwrt hb4 (by omega) hSFS3 hfr3
    obtain ⟨hA3, hB3, hLR3, hFP3⟩ := hSF3
    clear hpc3
    have hret4 := hret.aligned
    have hret48 := hret.user
    janus_run [hA3, hB3, hLR3, hFP3]
    have hLsepQ : LiveSep L [(BitVec.toNat ptr, BitVec.toNat ptr + 32)] := fun r hr => by
      have := hapL r hr
      simp only [Apart] at this
      simp only [outside_cons, outside_nil, and_true]
      omega
    have hstq : MemFrame m2 ((m2.writeLE (BitVec.toNat ptr) 8 a.toNat).writeLE (BitVec.toNat ptr + 8) 8 b.toNat)
        [(BitVec.toNat ptr, BitVec.toNat ptr + 32)] :=
      ((MemFrame.refl m2 [(BitVec.toNat ptr, BitVec.toNat ptr + 32)]).writeLE a.toNat
        (List.mem_singleton_self _) (Nat.le_refl _) (by simp)).writeLE b.toNat
        (List.mem_singleton_self _) (by simp) (by simp <;> omega)
    refine ⟨BitVec.toNat ptr, bud - 32, Or.inr rfl, MemFrame.trans hF3 hfr3 (by frame_sub),
      LiveFrame.trans hLF1 (LiveFrame.trans hlf2 (LiveFrame.trans (LiveFrame.of_win hstq hLsepQ) hlf3
        (fun a n h => h.append_left _)) (fun _ _ h => h)) (fun _ _ h => h), hinv3⟩
  · -- a pooled buffer
    obtain ⟨hd0, hd8, hd48, hdacc, hrs⟩ := hSh
    subst hrs
    have hr0' : r 0 = 685184#64 := BitVec.eq_of_toNat_eq (by simpa [hT] using hr0)
    have hr1' : r 1 ≠ 0#64 := fun h => by simp [h] at hd0
    have hin := hinrt _ (List.mem_singleton_self _)
    simp only [Nat.add_sub_cancel_left] at hin
    have hapL : ApartAll (BitVec.toNat (r 1)) 32 L := by
      have := hfresh _ (List.mem_singleton_self _)
      simpa using this
    have hSF1 : StackFacts s.sp.toNat a.toNat b.toNat ret (s.regs 29).toNat m1 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [hfr1.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack]
          exact ⟨outside_rt_of_win hwrt (by omega) (by omega), by omega, by omega⟩)]
        repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
        rw [Memory.readLE_writeLE_self]
        try first | exact Nat.mod_eq_of_lt a.isLt | exact Nat.mod_eq_of_lt b.isLt | rfl | exact Nat.mod_eq_of_lt (s.regs 29).isLt
    have hw2 : m1.accessible (s.sp.toNat - 4144) (4144 + 24) true = true := by
      rw [hF1.accessible]; exact hw4
    have hA8t : m1.accessible (BitVec.toNat (r 1)) 8 true = true :=
      Memory.accessible_mono _ hdacc (Nat.le_refl _) (by omega)
    have hA8f : m1.accessible (BitVec.toNat (r 1)) 8 false = true :=
      Memory.accessible_sub _ hdacc (Or.inl rfl) (Nat.le_refl _) (by omega)
    have hB8t : m1.accessible (BitVec.toNat (r 1) + 8) 8 true = true :=
      Memory.accessible_mono _ hdacc (by omega) (by omega)
    have hB8f : m1.accessible (BitVec.toNat (r 1) + 8) 8 false = true :=
      Memory.accessible_sub _ hdacc (Or.inl rfl) (by omega) (by omega)
    have hpack := And.intro hapL (And.intro hinvG (And.intro hF1 (And.intro hLF1 (And.intro hfr1
      (And.intro hns1 hSF1)))))
    clear hpc1 key1 hrt0 hlf1 hapL hinvG hF1 hLF1 hfr1 hns1 hSF1 hfresh hinrt hsep
    janus_run until [Extracted.program.contractAddr "sync.(*Pool).Put"]
    obtain ⟨hapL, hinvG, hF1, hLF1, hfr1, hns1, hSF1⟩ := hpack
    obtain ⟨hA2, hB2, hLR2, hFP2⟩ := hSF1
    rw [hA2, hB2]
    have hpd := InRanges.disjoint hin (hwrt _ (List.mem_singleton_self _))
    simp only at hpd
    have hF3 : MemFrame s.mem ((m1.writeLE (BitVec.toNat (r 1)) 8 a.toNat).writeLE (BitVec.toNat (r 1) + 8) 8 b.toNat)
        (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
      (hF1.writeLE_inRanges _ ((hin.sub (a := BitVec.toNat (r 1)) (n := 8) (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
        ((hin.sub (a := BitVec.toNat (r 1) + 8) (n := 8) (by omega) (by omega)).append_left _)
    have hSFS3 : StackFacts s.sp.toNat a.toNat b.toNat ret (s.regs 29).toNat
        ((m1.writeLE (BitVec.toNat (r 1)) 8 a.toNat).writeLE (BitVec.toNat (r 1) + 8) 8 b.toNat) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · repeat rw [Memory.readLE_writeLE_of_disjoint (h := by omega)]
        first | exact hA2 | exact hB2 | exact hLR2 | exact hFP2
    have hnm : ∀ x ∈ L, x ∉ [(BitVec.toNat (r 1), BitVec.toNat (r 1) + 32)] := fun x hx hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact notMem_of_apartAll (by omega) hapL hx
    refine Reaches.call (Summary.withExit (hput (L ++ [(BitVec.toNat (r 1), BitVec.toNat (r 1) + 32)]) bud
      [(BitVec.toNat (r 1), BitVec.toNat (r 1) + 32)]) hret) rfl
      (putPre R L bud (BitVec.toNat (r 1)) _ s _ hg1 hg2 hg3 ha4 hw4 hal hb4 hgo hwrt (by rw [hP]; exact hokP)
        hF3 (by simp [setReg, Map.keepABI, callRegs_apply]) (by simp [hsp48]; omega) (by simp [setReg])
        (by simp [setReg]) (by simp [setReg, hP]) (by simp [setReg, hT]) (by simp [setReg])
        (by
          refine ⟨hd0, hd8, hd48, ?_, rfl⟩
          simp only [Memory.accessible_writeLE]; exact hdacc)
        (by
          rw [liveSep_append]
          refine ⟨hwL, ?_⟩
          simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true]
          omega)
        (by
          have := RtInv.inv_frame' (ws := [(BitVec.toNat (r 1), BitVec.toNat (r 1) + 32)]) (m := m1)
            (m' := (m1.writeLE (BitVec.toNat (r 1)) 8 a.toNat).writeLE (BitVec.toNat (r 1) + 8) 8 b.toNat)
            (((MemFrame.refl m1 [(BitVec.toNat (r 1), BitVec.toNat (r 1) + 32)]).writeLE a.toNat
              (List.mem_singleton_self _) (Nat.le_refl _) (by simp)).writeLE b.toNat
              (List.mem_singleton_self _) (by simp) (by simp <;> omega))
            (fun x hx => Or.inr (by
              simp only [List.mem_singleton] at hx; rw [hx]
              exact ⟨(BitVec.toNat (r 1), BitVec.toNat (r 1) + 32),
                List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by simp⟩)) hinvG
          simpa [setReg, Map.keepABI, callRegs_apply] using this)) ?_
    intro s3 hpc3 ⟨r3, vr3, fl3, m3, ex3, ep3, hs3, hfr3, hlf3, hns3, hinv3⟩
    subst hs3
    simp only [calleeStack, setReg_apply, Map.keepABI_apply, reduceIte, Nat.reduceEqDiff,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hsp48, or_true, true_or, ite_true, callRegs_apply,
      dropAll_append_self hnm] at hfr3 hlf3 hinv3
    have hSF3 := StackFacts.step (n := 3) hwrt hb4 (by omega) hSFS3 hfr3
    obtain ⟨hA3, hB3, hLR3, hFP3⟩ := hSF3
    clear hpc3
    have hret4 := hret.aligned
    have hret48 := hret.user
    janus_run [hA3, hB3, hLR3, hFP3]
    have hLsepQ : LiveSep L [(BitVec.toNat (r 1), BitVec.toNat (r 1) + 32)] := fun x hx => by
      have := hapL x hx
      simp only [Apart] at this
      simp only [outside_cons, outside_nil, and_true]
      omega
    have hstq : MemFrame m1 ((m1.writeLE (BitVec.toNat (r 1)) 8 a.toNat).writeLE (BitVec.toNat (r 1) + 8) 8 b.toNat)
        [(BitVec.toNat (r 1), BitVec.toNat (r 1) + 32)] :=
      ((MemFrame.refl m1 [(BitVec.toNat (r 1), BitVec.toNat (r 1) + 32)]).writeLE a.toNat
        (List.mem_singleton_self _) (Nat.le_refl _) (by simp)).writeLE b.toNat
        (List.mem_singleton_self _) (by simp) (by simp <;> omega)
    refine ⟨BitVec.toNat (r 1), bud, Or.inl rfl, MemFrame.trans hF3 hfr3 (by frame_sub),
      LiveFrame.trans hLF1 (LiveFrame.trans (LiveFrame.of_win hstq hLsepQ) hlf3
        (fun a n h => h.append_left _)) (fun _ _ h => h), hinv3⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The live runtime `R` is the toy bump allocator of `Janus.Contracts.LiveToy` (`toyR`), whose
runtime-owned ranges are the heap, the bump cell and the barrier buffer; `scratch`'s descriptor
is read-only data of the binary. Its `Get` returns nil, its `Put` drops its argument and its
`newobject` hands out the next `64 · Size_` bytes of the heap (code at the three contract
addresses). With them `correctness` applies to a call state of
`ScratchSum(3, 5)` with an empty live set (`nonvacuous`), and the call returns `3 ^ 5` with the
guarantee (`returns`). -/

namespace Witness

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.PoolSat

set_option maxRecDepth 100000

def P : Nat := janus_eval% poolAddr
def bT : Nat := janus_eval% bufType
def pT : Nat := janus_eval% ptrType
def cG : Nat := janus_eval% (Extracted.program.contractAddr "sync.(*Pool).Get")
def cP : Nat := janus_eval% (Extracted.program.contractAddr "sync.(*Pool).Put")
def cN : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")

theorem hP : poolAddr = P := by unfold P; decide
theorem hTy : bufType = bT := by unfold bT; decide
theorem hPT : ptrType = pT := by unfold pT; decide
theorem aG : Extracted.program.contractAddr "sync.(*Pool).Get" = cG := by decide
theorem aP : Extracted.program.contractAddr "sync.(*Pool).Put" = cP := by decide
theorem aN : Extracted.program.contractAddr "runtime.newobject" = cN := by decide

/-- The toy runtime has no type descriptors of its own. -/
def tys : Tys := []

theorem tysOK : TysOK tys := fun t ht => absurd ht (by simp [tys])

/-- The requests it serves. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = cG ∧ args = [P]) ∨ (a = cP ∧ args = [P]) ∨ (a = cN ∧ args = [bT])

def R : RtInv := toyR tys ok

/-- The model code at the three contract addresses. -/
def implAt : List Segment :=
  [{ name := "model.Get", base := cG, words := getCode },
   { name := "model.Put", base := cP, words := putCode },
   { name := "model.newobject", base := cN, words := newobjectCodeD }]

def linked : Program := Extracted.program.link implAt

set_option maxRecDepth 20000 in
theorem hget : PoolGetLive linked cG 4096 R pT BufObj := by
  refine poolGetLive_of_run tys ok linked cG pT BufObj ?_
  intro s hpc h30 h30'
  change ReachesRet linked _ s _
  janus_run
  exact getFinal_eq s

set_option maxRecDepth 20000 in
theorem hput : PoolPutLive linked cP 4096 R pT BufObj := by
  refine poolPutLive_of_run tys tysOK ok linked cP pT BufObj ?_
  intro s hpc h30 h30'
  change ReachesRet linked _ s _
  janus_run
  rfl

set_option maxRecDepth 20000 in
theorem hnew : NewobjectLiveContract linked cN 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  change ReachesRet linked _ s _
  janus_run
  exact finish_newobjectD tysOK pre

/-! ### The call state -/

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

/-- The data segments, and the bump cell `HEAP`; zero elsewhere. -/
def bytes0 (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨P, 40, true⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 0 then 3 else if i = 1 then 5 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [3, 5] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

theorem dataByte_none (a : Nat) (ha : 0x500000 ≤ a) : dataByte a = none := by
  unfold dataByte
  have : Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : d.base + d.bytes.length < 0x500000 := by
      have : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
      exact this d hd
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  rw [this]

theorem inv0 : R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_tys tysOK (m := s0.mem) (b := 0x400) (g := (s0.regs 28).toNat) (by decide) (by decide)
    (fun i hi hi' => ?_) (by decide) (by decide) (by decide) (fun t ht => absurd ht (by simp [tys]))
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega)]

theorem s0_sp : s0.sp.toNat = sp0 := by simp [s0, sp0]
theorem s0_g : (s0.regs 28).toNat = g0 := by simp [s0, g0]

theorem hP' : P = 1547776 := by unfold P; decide
theorem hb' : bT = 737984 := by unfold bT; decide

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 4144 ∧ StackOK s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 28).toNat + 16) 8 ((s0.sp.toNat - 4144, s0.sp.toNat + 24) :: R.rt) ∧
    LiveSep [(s0.sp.toNat - 4144, s0.sp.toNat + 24)] R.rt ∧
    LiveSep [] [(s0.sp.toNat - 4144, s0.sp.toNat + 24)] ∧
    (∀ r ∈ R.rt, 0 < r.1) ∧ (poolAddr + 40 ≤ s0.sp.toNat - 4144 ∨ s0.sp.toNat + 24 ≤ poolAddr) ∧
    Outside bufType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
    R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [bufType] ∧
    s0.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
    R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) ∧ 32 ≤ 0x400 := by
  rw [hP, hTy, aG, aP, aN, s0_sp, s0_g]
  have hrt : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, dataLoaded, ?_, ?_, by simp, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, inv0, by decide⟩
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true, hP', hb', g0, sp0, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · rw [hrt]; simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true, hP', hb', g0, sp0, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · intro r hr
    rw [hrt] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [HEAP, BUMP, WBUF] <;> omega
  · simp only [sp0]; decide
  · rw [hb', hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [hP']; unfold newOffset; decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (ret : Nat) (s : State) (L : List (Nat × Nat))
    (bud : Nat),
    PoolGetLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      ptrType BufObj ∧
    PoolPutLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      ptrType BufObj ∧
    NewobjectLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 5] s ∧
    (GuardOK s 4144 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4144, s.sp.toNat + 24) :: R.rt) ∧
      LiveSep [(s.sp.toNat - 4144, s.sp.toNat + 24)] R.rt ∧
      LiveSep L [(s.sp.toNat - 4144, s.sp.toNat + 24)] ∧
      (∀ r ∈ R.rt, 0 < r.1) ∧ (poolAddr + 40 ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 24 ≤ poolAddr) ∧
      Outside bufType 16 R.rt ∧
      R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
      R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
      R.ok (Extracted.program.contractAddr "runtime.newobject") [bufType] ∧
      s.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
      R.inv bud L (s.regs 28).toNat (view R.rt L s.mem) ∧ 32 ≤ bud) := by
  refine ⟨implAt, R, ret, s0, [], 0x400, ?_, ?_, ?_, hret, setup, pre⟩
  · rw [aG, hPT]; exact hget
  · rw [aP, hPT]; exact hput
  · rw [aN]; exact hnew

/-- So the guarantee is reached: `ScratchSum(3, 5)` returns `3 ^ 5 = 6`, with the runtime's invariant
again for the same (empty) live set. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = (3#64 ^^^ 5#64).toNat ∧
      ∃ d b', (b' = 0x400 ∨ b' = 0x400 - 32) ∧
        MemFrame s0.mem s'.mem (R.rt ++ [(s0.sp.toNat - 4144, s0.sp.toNat + 24), (d, d + 32)]) ∧
        LiveFrame s0.mem s'.mem [] [] ∧ R.inv b' [] (s0.regs 28).toNat (view R.rt [] s'.mem) := by
  have h := correctness implAt R (by rw [aG, hPT]; exact hget) (by rw [aP, hPT]; exact hput)
    (by rw [aN]; exact hnew) 3 5 [] 0x400
    ret hret s0 setup pre
  exact h

end Witness

end Proof
