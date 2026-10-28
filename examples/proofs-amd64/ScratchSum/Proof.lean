import Extracted

/-!
# `ScratchSum(a, b uint64) uint64` with a `sync.Pool`-backed scratch buffer (amd64)

The amd64 counterpart of `examples/proofs/ScratchSum.lean` (see it for the Go source and the guarantee):
`Get`, `new(scratch)` on a miss, two stores, `Put`, and `a ^ b`. The contracts are
`PoolGetLive`/`PoolPutLive` (`Janus/Contracts/PoolAmd64.lean`) and `NewobjectLiveContract64`
(`Janus/Contracts/LiveAmd64.lean`),
for one goroutine (docs/SOUNDNESS.md, "The single-threaded assumption"). The stack window is
`[RSP-4136, RSP+24)`: the return address and the two spilled arguments above `RSP`, the frame
(`RBP`, 24 bytes), the callee's return-address slot and the 4096 bytes the runtime may use.
-/

open Janus Janus.Tactic Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool
  Janus.Contracts Janus.Contracts.Pool Janus.Contracts.PoolAmd64

namespace Proof

def poolAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x1c)
def ptrType : Nat := ripTarget Extracted.program (Extracted.entry + 0x28)
def bufType : Nat := ripTarget Extracted.program (Extracted.entry + 0x3b)

/-- Data addresses evaluated from the extraction (`janus_eval%`), never copied. -/
local macro "ptrN" : term => `(janus_eval% ptrType)
local macro "bufN" : term => `(janus_eval% bufType)

def BufObj : PoolShape := fun m d rs =>
  0 < d ∧ d % 8 = 0 ∧ d + 32 ≤ 2 ^ 48 ∧ m.accessible d 32 true = true ∧ rs = [(d, d + 32)]

/-- A range inside the window is outside the runtime. -/
theorem outside_rt_of_win {rt : List (Nat × Nat)} {lo hi a n : Nat} (h : LiveSep [(lo, hi)] rt)
    (h1 : lo ≤ a) (h2 : a + n ≤ hi) : Outside a n rt :=
  Outside.of_sub (h _ (List.mem_singleton_self _)) h1 (by simp only; omega)

/-- **The precondition of a live call** (amd64) made from a function that owns the stack window
`[lo, hi)`: the call state `S` has `RSP` `fr` bytes below the entry state's `s`, has changed memory
only in `R.rt` and the window, holds a return address below `2^47` at `[RSP]`, and the invariant
holds for `S.mem`. Everything the standard preconditions (`CallOK64`, `StackRoom64`, `LiveAt`) ask
for follows. -/
theorem call_pre64 (R : RtInv) (L : List (Nat × Nat)) (b cost : Nat) (addr : Nat) (args : List Nat)
    {s S : State} {lo hi stack nargs fr : Nat}
    (hg1 : (s.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hg2 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 14).toNat + 16) 8 + (stack + fr) < (s.regs 4).toNat)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 ((lo, hi) :: R.rt))
    (hfr : MemFrame s.mem S.mem (R.rt ++ [(lo, hi)])) (hg : S.regs 14 = s.regs 14)
    (hsp : (S.regs 4).toNat + fr = (s.regs 4).toNat) (hal : (S.regs 4).toNat % 8 = 0)
    (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hstk : stack ≤ (S.regs 4).toNat) (hlo : lo ≤ (S.regs 4).toNat - stack)
    (hhi : (S.regs 4).toNat + 8 + 8 * nargs ≤ hi) (hhi48 : hi ≤ 2 ^ 48)
    (hacc : s.mem.accessible lo (hi - lo) true = true)
    (hwrt : LiveSep [(lo, hi)] R.rt) (hwL : LiveSep L [(lo, hi)])
    (hok : R.ok addr args) (hinv : R.inv b L (S.regs 14).toNat (view R.rt L S.mem)) (hcost : cost ≤ b) :
    CallOK64 S stack nargs ∧ StackRoom64 S stack nargs ∧
      LiveAt R addr args L b cost (S.regs 14).toNat S.mem (liveWin64 S stack nargs) := by
  have hgw : Outside ((s.regs 14).toNat + 16) 8 (R.rt ++ [(lo, hi)]) := by
    simp only [outside_cons, outside_append, outside_nil, and_true] at hgo ⊢
    exact ⟨hgo.2, hgo.1⟩
  refine ⟨⟨hra, hal, hstk, by omega, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hok, hinv, hcost, ?_, ?_⟩
  · rw [hfr.accessible]
    exact Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg]; rw [hfr.accessible]; exact hg2
  · simp only [regG, regSP, stackguard0Offset, stackguard0, hg]
    rw [hfr.readLE _ _ hgw]; omega
  · rw [hg]
    simp only [calleeStack64, outside_cons, outside_nil, and_true]
    simp only [outside_cons, outside_nil, and_true] at hgo
    omega
  · intro r hr
    have := hwL r hr
    simp only [liveWin64, calleeStack64, outside_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  · intro r hr
    have := hwrt (lo, hi) (List.mem_singleton_self _)
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> exact Outside.of_sub this (by simp <;> omega) (by simp <;> omega)

/-- An opaque wrapper: a hypothesis `Hid P` is not scanned by the executor's side-condition
dischargers (a hypothesis with `accessible` facts inside, e.g. a `MemFrame`, would be). -/
@[irreducible] def Hid (P : Prop) : Prop := P

theorem Hid.mk {P : Prop} (h : P) : Hid P := by unfold Hid; exact h
theorem Hid.get {P : Prop} (h : Hid P) : P := by unfold Hid at h; exact h

/-- The frame bookkeeping tactic: a goal `Outside a n X → Outside a n Y ∧ …` about lists of the form
`rt ++ [ranges]` is arithmetic over the atom `Outside a n rt`. -/
macro "frame_sub" : tactic =>
  `(tactic| (intro a n h; simp only [outside_append, outside_cons, outside_nil, and_true, calleeStack64] at h ⊢; grind))

/-- The precondition of the `Put` of the buffer `[d, d+32)` (held in the live set `L ++ [(d, d+32)]`)
at the call state `S`, `40` bytes below the entry state `s`, whose memory changed since `s` only in
`R.rt` and the window. -/
theorem putPre64 (R : RtInv) (L : List (Nat × Nat)) (bd d cP : Nat) (s S : State)
    (hg1 : (s.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hg2 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4136 < (s.regs 4).toNat)
    (ha4 : (s.regs 4).toNat + 24 ≤ 2 ^ 48)
    (hw4 : s.mem.accessible ((s.regs 4).toNat - 4136) (4136 + 24) true = true)
    (hal : (s.regs 4).toNat % 8 = 0) (hb4 : 4136 ≤ (s.regs 4).toNat)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 (((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24) :: R.rt))
    (hwrt : LiveSep [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] R.rt)
    (hokP : R.ok cP [poolAddr])
    (hfr : MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))
    (hg : S.regs 14 = s.regs 14) (hsp : (S.regs 4).toNat + 40 = (s.regs 4).toNat)
    (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47) (h0 : (S.regs 0).toNat = poolAddr)
    (h1 : (S.regs 3).toNat = ptrType) (h2 : (S.regs 1).toNat = d) (hsh : BufObj S.mem d [(d, d + 32)])
    (hwL1 : LiveSep (L ++ [(d, d + 32)]) [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])
    (hinvS : R.inv bd (L ++ [(d, d + 32)]) (S.regs 14).toNat (view R.rt (L ++ [(d, d + 32)]) S.mem)) :
    CallOK64 S 4096 3 ∧ StackRoom64 S 4096 3 ∧ (S.regs 3).toNat = ptrType ∧
      BufObj S.mem (S.regs 1).toNat [(d, d + 32)] ∧ (∀ r ∈ [(d, d + 32)], r ∈ L ++ [(d, d + 32)]) ∧
      LiveAt R cP [(S.regs 0).toNat] (L ++ [(d, d + 32)]) bd 0 (S.regs 14).toNat S.mem
        (liveWin64 S 4096 3) := by
  have h := call_pre64 R (L ++ [(d, d + 32)]) bd 0 cP [(S.regs 0).toNat] (s := s) (S := S)
    (lo := (s.regs 4).toNat - 4136) (hi := (s.regs 4).toNat + 24) (stack := 4096) (nargs := 3) (fr := 40)
    hg1 hg2 (by omega) hgo hfr hg hsp (by omega) hra (by omega) (by omega) (by omega) ha4
    (by rw [show (s.regs 4).toNat + 24 - ((s.regs 4).toNat - 4136) = 4136 + 24 by omega]; exact hw4) hwrt hwL1
    (by rw [h0]; exact hokP) hinvS (Nat.zero_le _)
  exact ⟨h.1, h.2.1, h1, by rw [h2]; exact hsh, fun r hr => by simp at hr; simp [hr], h.2.2⟩

/-- The caller's stack slots a function keeps across its calls: the spilled arguments, the return
address and the saved frame pointer. -/
def StackFacts (sp0 a b ret fp : Nat) (m : Arm64.Memory) : Prop :=
  m.readLE (sp0 + 8) 8 = a ∧ m.readLE (sp0 + 16) 8 = b ∧ m.readLE sp0 8 = ret ∧
    m.readLE (sp0 - 8) 8 = fp

/-- A call (at most three arguments) from the function's frame, `40` bytes below the entry `RSP`,
keeps those slots: they lie in the function's window, apart from the runtime, and outside the
callee's. -/
theorem StackFacts.step {rt : List (Nat × Nat)} {sp0 a b ret fp n : Nat} {m m' : Arm64.Memory}
    (hwrt : LiveSep [(sp0 - 4136, sp0 + 24)] rt) (hsp : 4136 ≤ sp0) (hn : n ≤ 3)
    (h : StackFacts sp0 a b ret fp m)
    (hfr : MemFrame m m' (rt ++ [(sp0 - 40 - 4096, sp0 - 40), (sp0 - 40 + 8, sp0 - 40 + 8 + 8 * n)])) :
    StackFacts sp0 a b ret fp m' := by
  have hr : ∀ x, sp0 - 4136 ≤ x → x + 8 ≤ sp0 + 24 → Outside x 8 rt := fun x h1 h2 =>
    Outside.of_sub (hwrt _ (List.mem_singleton_self _)) h1 (by simp only; omega)
  have hrd : ∀ x, sp0 - 8 ≤ x → x + 8 ≤ sp0 + 24 → Outside x 8 (rt ++
      [(sp0 - 40 - 4096, sp0 - 40), (sp0 - 40 + 8, sp0 - 40 + 8 + 8 * n)]) := by
    intro x h1 h2
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hr x (by omega) h2, by omega, by omega⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hfr.readLE _ _ (hrd _ (by omega) (by omega))]; exact h1,
    by rw [hfr.readLE _ _ (hrd _ (by omega) (by omega))]; exact h2,
    by rw [hfr.readLE _ _ (hrd _ (by omega) (by omega))]; exact h3,
    by rw [hfr.readLE _ _ (hrd _ (by omega) (by omega))]; exact h4⟩

/-- The call's own push of the return address, at `[RSP - 40, RSP - 32)` (apart from the slots). -/
theorem StackFacts.ret {sp0 a b ret fp : Nat} {m : Arm64.Memory} (h : StackFacts sp0 a b ret fp m)
    (hsp : 40 ≤ sp0) (v : Nat) : StackFacts sp0 a b ret fp (m.writeLE (sp0 - 40) 8 v) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact h1
  · rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact h2
  · rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact h3
  · rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]; exact h4

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The end of `ScratchSum` from the call of `Put` on the buffer `[d, d+32)` (written, held in the live
set `L ++ [(d, d+32)]`): the call state `S`, `RSP` `40` bytes below the entry state `s`, memory `mP`
(only `R.rt` and the window changed since `s`). -/
theorem putTail (impl : List Amd64.Segment) (R : RtInv)
    (hput : PoolPutLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Put")
      4096 R ptrType BufObj)
    (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret) (s S : State) (a b : BitVec 64)
    (L : List (Nat × Nat)) (bud bd d : Nat) (mP : Arm64.Memory)
    (hP : poolAddr = 5709280) (hT : ptrType = (ptrN))
    (hg1 : (s.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hg2 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4136 < (s.regs 4).toNat)
    (ha4 : (s.regs 4).toNat + 24 ≤ 2 ^ 48)
    (hw4 : s.mem.accessible ((s.regs 4).toNat - 4136) (4136 + 24) true = true)
    (hal : (s.regs 4).toNat % 8 = 0) (hb4 : 4136 ≤ (s.regs 4).toNat)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 (((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24) :: R.rt))
    (hwrt : LiveSep [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] R.rt)
    (hokP : R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [5709280])
    (hbd : bd = bud ∨ bd = bud - 32)
    (hrip : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put"))
    (hS0 : S.regs 0 = 5709280#64) (hS3 : S.regs 3 = (BitVec.ofNat 64 (ptrN))) (hS1 : S.regs 1 = BitVec.ofNat 64 d)
    (hS4 : S.regs 4 = s.regs 4 - 40#64) (hS5 : S.regs 5 = s.regs 4 - 8#64) (hSg : S.regs 14 = s.regs 14)
    (hSx : S.xmm 15 = s.xmm 15) (hSmem : S.mem = mP) (hd64 : d < 2 ^ 64)
    (hFP : MemFrame s.mem mP (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))
    (hLFP : LiveFrame s.mem mP L [])
    (hra : mP.readLE ((s.regs 4).toNat - 40) 8 = 4755287)
    (hsh : BufObj mP d [(d, d + 32)])
    (hwL1 : LiveSep (L ++ [(d, d + 32)]) [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])
    (hLd : ∀ x ∈ L, x ∉ [(d, d + 32)])
    (hinv : R.inv bd (L ++ [(d, d + 32)]) (s.regs 14).toNat (view R.rt (L ++ [(d, d + 32)]) mP))
    (hSF : StackFacts (s.regs 4).toNat a.toNat b.toNat ret (s.regs 5).toNat mP) :
    Amd64.Tactic.Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧
        ((s'.regs 0).toNat = (a ^^^ b).toNat ∧
        ∃ d b', (b' = bud ∨ b' = bud - 32) ∧
          MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24), (d, d + 32)]) ∧
          LiveFrame s.mem s'.mem L [] ∧ R.inv b' L (s.regs 14).toNat (view R.rt L s'.mem))) := by
  subst hSmem
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hS4n : (S.regs 4).toNat = (s.regs 4).toNat - 40 := by rw [hS4, hsp40]
  refine Reaches.call (Summary.withExit (hput (L ++ [(d, d + 32)]) bd [(d, d + 32)]) hret) hrip
    (putPre64 R L bd d _ s S hg1 hg2 hg3 ha4 hw4 hal hb4 hgo hwrt hokP hFP hSg (by omega)
      (by rw [hS4n]; omega) (by rw [hS0]; simpa using hP.symm) (by rw [hS3, hT]; rfl) (by rw [hS1]; simpa using hd64)
      hsh hwL1 (by rw [hSg]; exact hinv)) ?_
  intro s3 hs3 ⟨r3, x3, y3, fl3, m3, zh3, kr3, hs3', hfr3, hlf3, hns3, hinv3⟩
  subst hs3'
  simp only [calleeStack64, hS4n, MapAmd64.keepABI_apply, dropAll_append_self hLd] at hfr3 hlf3 hinv3
  have hSF3 := StackFacts.step (n := 3) hwrt hb4 (by omega) hSF hfr3
  obtain ⟨hA3, hB3, hLR3, hFP3⟩ := hSF3
  have hret4 := hret.user
  have hw3 : m3.accessible ((s.regs 4).toNat - 4136) (4136 + 24) true = true := by
    rw [hfr3.accessible, hFP.accessible]; exact hw4
  have hra' : S.mem.readLE (S.regs 4).toNat 8 = 4755287 := by rw [hS4n]; exact hra
  have hpack := Hid.mk (And.intro hFP (And.intro hLFP (And.intro hlf3 (And.intro hfr3 (And.intro hsh
    (And.intro hinv3 hinv))))))
  clear hFP hLFP hlf3 hfr3 hsh hinv3 hinv hput hns3 hs3 hSF hwL1 hLd
  have hra2 : S.mem.readLE (s.regs 4 - 40#64).toNat 8 = 4755287 := by rw [hsp40]; exact hra
  janus64_run [hA3, hB3, hLR3, hFP3, hra', hra2, hw3]
  obtain ⟨hFP, hLFP, hlf3, hfr3, hsh, hinv3, hinv⟩ := hpack.get
  refine ⟨d, bd, hbd, MemFrame.trans hFP hfr3 (by frame_sub),
    LiveFrame.trans hLFP (LiveFrame.of_sep hlf3 (fun _ _ => trivial) (fun r hr => List.mem_append_left _ hr))
      (fun _ _ h => h), ?_⟩
  simpa [hSg] using hinv3

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (B : PoolShape)
    (hget : PoolGetLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Get")
      4096 R ptrType B)
    (hput : PoolPutLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Put")
      4096 R ptrType B)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (a b : BitVec 64) (L : List (Nat × Nat)) (bud : Nat) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => B = BufObj ∧ StackGuardOK s 4136 ∧ StackWritable s 4136 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 14).toNat + 16) 8 (((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24) :: R.rt) ∧
        LiveSep [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] R.rt ∧
        LiveSep L [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] ∧
        (∀ r ∈ R.rt, 0 < r.1) ∧ (poolAddr + 40 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ poolAddr) ∧
        Outside bufType 16 R.rt ∧
        R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
        R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [bufType] ∧
        s.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
        R.inv bud L (s.regs 14).toNat (view R.rt L s.mem) ∧ 32 ≤ bud)
      (fun s s' => (s'.regs 0).toNat = (a ^^^ b).toNat ∧
        ∃ d b', (b' = bud ∨ b' = bud - 32) ∧
          MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24), (d, d + 32)]) ∧
          LiveFrame s.mem s'.mem L [] ∧ R.inv b' L (s.regs 14).toNat (view R.rt L s'.mem)) := by
  intro ret hret s hs ⟨hB, hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hbin, hokG, hokP, hokN,
    hnew0, hinv, hbud⟩
  subst hB
  janus64_intro hs
  janus_eval_nat hP : poolAddr
  janus_eval_nat hT : ptrType
  janus_eval_nat hB : bufType
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb4 ha4 hw4 hal
  janus64_data hd [hw4]
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hpw := hpin
  rw [hP] at hokG hokP hnew0
  rw [hB] at hbin
  have hdesc : s.mem.readLE (bufN) 8 = 32 ∧ s.mem.readLE ((bufN) + 8) 8 = 0 :=
    ⟨by rw [h_rodata (bufN) 8 (by decide +kernel)]; decide +kernel,
      by rw [h_rodata ((bufN) + 8) 8 (by decide +kernel)]; decide +kernel⟩
  have hbW : Outside (bufN) 16 [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hgo' := hgo
  simp only [outside_cons, outside_nil, and_true] at hgo'
  have key1 : ∀ S : State, MemFrame s.mem S.mem [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] →
      S.regs 14 = s.regs 14 → (S.regs 4).toNat + 40 = (s.regs 4).toNat → (S.regs 0).toNat = 5709280 →
      S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47 →
      CallOK64 S 4096 1 ∧ StackRoom64 S 4096 1 ∧ S.mem.readLE (5709280 + newOffset) 8 = 0 ∧
      LiveAt R (Extracted.program.contractAddr "sync.(*Pool).Get") [(S.regs 0).toNat] L bud 0
        (S.regs 14).toNat S.mem (liveWin64 S 4096 1) := by
    intro S hf hg' hsp h0 hra
    have h := call_pre64 R L bud 0 (Extracted.program.contractAddr "sync.(*Pool).Get") [(S.regs 0).toNat]
      (s := s) (S := S) (lo := (s.regs 4).toNat - 4136) (hi := (s.regs 4).toNat + 24) (stack := 4096) (nargs := 1)
      (fr := 40) hnw2 hgr (by omega) hgo (hf.widen R.rt) hg' hsp (by omega) hra (by omega) (by omega) (by omega)
      ha4 (by rw [show (s.regs 4).toNat + 24 - ((s.regs 4).toNat - 4136) = 4136 + 24 by omega]; exact hw4)
      hwrt hwL (by rw [h0]; exact hokG) (by rw [hg']; exact RtInv.inv_frame hf hwrt hinv) (Nat.zero_le _)
    refine ⟨h.1, h.2.1, ?_, h.2.2⟩
    rw [hf.readLE _ _ (by simp only [newOffset, outside_cons, outside_nil, and_true]; omega)]
    exact hnew0
  janus64_run until [Extracted.program.contractAddr "sync.(*Pool).Get"]
  refine Reaches.call (Summary.withExit (hget L bud) hret) rfl
    (key1 _ (by janus_frame) (by simp [setRegF]) (by simp [setRegF, hsp40] <;> omega) (by simp [setRegF])
      (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self] <;> omega)) ?_
  intro s1 hs1 ⟨r, x, y, fl, m1, zh1, kr1, hs1', hfr1, hlf1, hns1, hcase⟩
  subst hs1'
  simp only [calleeStack64, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr1 hlf1 hns1 hcase
  have hF1 : MemFrame s.mem m1 (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) :=
    MemFrame.trans (rs := [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) (by janus_frame) hfr1 (by frame_sub)
  have hLF1 : LiveFrame s.mem m1 L [] :=
    LiveFrame.trans (LiveFrame.of_win (ws := [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])
      (by janus_frame) hwL) hlf1 (fun _ _ h => h)
  have hSF1o : ∀ x, (s.regs 4).toNat - 8 ≤ x → x + 8 ≤ (s.regs 4).toNat + 24 →
      Outside x 8 (R.rt ++ [((s.regs 4).toNat - 40 - 4096, (s.regs 4).toNat - 40),
        ((s.regs 4).toNat - 40 + 8, (s.regs 4).toNat - 40 + 8 + 8 * 1)]) := by
    intro x h1 h2
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨outside_rt_of_win hwrt (by omega) (by omega), by omega, by omega⟩
  have hSF1 : StackFacts (s.regs 4).toNat a.toNat b.toNat ret (s.regs 5).toNat m1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfr1.readLE _ _ (hSF1o _ (by omega) (by omega))]
      repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
      rw [Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt a.isLt
    · rw [hfr1.readLE _ _ (hSF1o _ (by omega) (by omega))]
      repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
      rw [Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt b.isLt
    · rw [hfr1.readLE _ _ (hSF1o _ (by omega) (by omega))]
      repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
      exact h_ret
    · rw [hfr1.readLE _ _ (hSF1o _ (by omega) (by omega))]
      repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
      rw [Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (s.regs 5).isLt
  rcases hcase with ⟨hr0, hr1, hinvG⟩ | ⟨rs, hr0, hSh, hfresh, hinrt, hsep, hinvG⟩
  · have hr0' : r 0 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hr0)
    have hr1' : r 3 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hr1)
    have hbw : (s.regs 4).toNat - 4136 + ((s.regs 4).toNat + 24 - ((s.regs 4).toNat - 4136)) ≤ (bufN) ∨
        (bufN) + 16 ≤ (s.regs 4).toNat - 4136 := by omega
    have hoB : ∀ a k, (bufN) ≤ a → a + k ≤ (bufN) + 16 →
        Outside a k (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) := fun a k h1 h2 => by
      simp only [outside_append]
      exact ⟨Outside.of_sub hbin h1 h2, Outside.of_sub hbW h1 h2⟩
    have hsz : m1.readLE (bufN) 8 = 32 := by
      rw [hF1.readLE _ _ (hoB _ _ (Nat.le_refl _) (by omega))]; exact hdesc.1
    have hpb : m1.readLE ((bufN) + 8) 8 = 0 := by
      rw [hF1.readLE _ _ (hoB _ _ (by omega) (by omega))]; exact hdesc.2
    have hmC : MemFrame m1 (m1.writeLE ((s.regs 4).toNat - 40) 8 4755239)
        [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] := by janus_frame
    have hsz2 : (m1.writeLE ((s.regs 4).toNat - 40) 8 4755239).readLE (bufN) 8 = 32 := by
      rw [hmC.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hsz
    have hpb2 : (m1.writeLE ((s.regs 4).toNat - 40) 8 4755239).readLE ((bufN) + 8) 8 = 0 := by
      rw [hmC.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hpb
    janus64_run until [Extracted.program.contractAddr "runtime.newobject"]
    have key2 : ∀ S : State, S.mem = m1.writeLE ((s.regs 4).toNat - 40) 8 4755239 → S.regs 14 = s.regs 14 →
        (S.regs 4).toNat + 40 = (s.regs 4).toNat → (S.regs 0).toNat = (bufN) →
        (NewobjectPre64 4096 S ∧ StackRoom64 S 4096 1 ∧
          LiveAt R (Extracted.program.contractAddr "runtime.newobject") [(S.regs 0).toNat] L bud
            (newobjectRound64 S) (S.regs 14).toNat S.mem (liveWin64 S 4096 1)) ∧
          0 < typSize S.mem (S.regs 0).toNat := by
      intro S hm hg' hsp h0
      have hr : typSize S.mem (S.regs 0).toNat = 32 := by simp only [typSize, hm, h0]; exact hsz2
      have hp : typPtrBytes S.mem (S.regs 0).toNat = 0 := by simp only [typPtrBytes, hm, h0]; exact hpb2
      have hround : newobjectRound64 S = 32 := by
        simp only [newobjectRound64, hr, typNoscan, hp]; decide
      have hFS : MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) := by
        rw [hm]
        exact MemFrame.trans (rs := R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) hF1
          (hmC.widen R.rt) (fun a n h => ⟨h, h⟩)
      have hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47 := by
        have e : (S.regs 4).toNat = (s.regs 4).toNat - 40 := by omega
        rw [hm, e, Arm64.Memory.readLE_writeLE_self]; omega
      have h := call_pre64 R L bud 32 (Extracted.program.contractAddr "runtime.newobject") [(S.regs 0).toNat]
        (s := s) (S := S) (lo := (s.regs 4).toNat - 4136) (hi := (s.regs 4).toNat + 24) (stack := 4096)
        (nargs := 1) (fr := 40) hnw2 hgr (by omega) hgo hFS hg' hsp (by omega) hra (by omega) (by omega)
        (by omega) ha4
        (by rw [show (s.regs 4).toNat + 24 - ((s.regs 4).toNat - 4136) = 4136 + 24 by omega]; exact hw4)
        hwrt hwL (by rw [h0]; exact hokN)
        (by rw [hg', hm]; exact RtInv.inv_frame hmC hwrt hinvG) hbud
      rw [hround]
      refine ⟨⟨⟨h.1, ⟨by omega, ?_⟩, ?_⟩, h.2.1, h.2.2⟩, by omega⟩
      · rw [hFS.accessible, h0]
        exact Arm64.Memory.accessible_sub _ h_data1 (Or.inl rfl) (Nat.le_refl _) (by omega)
      · rw [hr]; simp [maxAlloc]
    refine Reaches.call (Summary.withExit (hnew.pos L bud) hret) rfl
      (key2 _ rfl (by simp [setRegF, MapAmd64.keepABI]) (by simp [setRegF, hsp40]; omega) (by simp [setRegF])) ?_
    intro s2 hs2' ⟨ptr, junk, f2, x2, yh2, m2, zh2, kr2, hs2, hfr2, hlf2, ⟨hobj, hapL⟩, hapS, hinv2⟩
    subst hs2
    simp only [retState64, calleeStack64, newobjectObj64, Fresh, newobjectRound64, setRegF, reduceIte,
      Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hsp40, typSize, typNoscan,
      typPtrBytes, hsz2, hpb2, MapAmd64.keepABI_apply, or_true, true_or, ite_true] at hfr2 hlf2 hobj hapL hapS hinv2
    have hbs : blockSize 32 (0 == 0) = 32 := by decide
    rw [hbs] at hobj hapL hapS hinv2
    obtain ⟨hin, hbd, hacc, hal8, -, hzero, -⟩ := hobj
    have hal8' : BitVec.toNat ptr % 8 = 0 := by simpa using hal8
    have hptr0 : 0 < BitVec.toNat ptr := by
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := hrt0 r hr
      omega
    have hF2 : MemFrame s.mem m2 (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) := by
      refine MemFrame.trans (rs := R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])
        (rs' := R.rt ++ [((s.regs 4).toNat - 40 - 4096, (s.regs 4).toNat - 40),
          ((s.regs 4).toNat - 40 + 8, (s.regs 4).toNat - 40 + 8 + 8 * 1)]) ?_ hfr2 (by frame_sub)
      exact MemFrame.trans (rs := R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) hF1
        (rs' := R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) (hmC.widen R.rt)
        (fun a n h => ⟨h, h⟩)
    have hLF2 : LiveFrame s.mem m2 L [] :=
      LiveFrame.trans (LiveFrame.trans hLF1 (LiveFrame.of_win hmC hwL) (fun _ _ h => h)) hlf2 (fun _ _ h => h)
    have hSF2 := StackFacts.step (n := 1) hwrt hb4 (by omega) (hSF1.ret (by omega) 4755239) hfr2
    obtain ⟨hA2, hB2, hLR2, hFP2⟩ := hSF2
    have hw2 : m2.accessible ((s.regs 4).toNat - 4136) (4136 + 24) true = true := by
      rw [hF2.accessible]; exact hw4
    have hacc8 : m2.accessible (BitVec.toNat ptr) 8 true = true :=
      Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    have hacc8b : m2.accessible (BitVec.toNat ptr + 8) 8 true = true :=
      Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
    have hpd := InRanges.disjoint hin (hwrt _ (List.mem_singleton_self _))
    simp only at hpd
    have hLsepQ : LiveSep L [(BitVec.toNat ptr, BitVec.toNat ptr + 32)] := fun x hx => by
      have := hapL x hx
      simp only [Apart] at this
      simp only [outside_cons, outside_nil, and_true]
      omega
    have hnm : ∀ x ∈ L, x ∉ [(BitVec.toNat ptr, BitVec.toNat ptr + 32)] := fun x hx hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact notMem_of_apartAll (by omega) hapL hx
    have hpack := Hid.mk (And.intro hF2 (And.intro hLF2 (And.intro hinv2 (And.intro hacc8 (And.intro hacc8b
      (And.intro hapL (And.intro hnm (And.intro hLsepQ (And.intro hin (And.intro hSF1 (And.intro hw2 hacc)))))))))))
    clear hmC hfr2 hlf2 hF2 hLF2 hinv2 hapL hnm hLsepQ hin hapS hzero key2 key1 hF1 hLF1 hfr1 hlf1 hns1 hinvG hSF1 hSF1o
    janus64_run [hA2, hB2, hLR2, hFP2, hw2] until [Extracted.program.contractAddr "sync.(*Pool).Put"]
    obtain ⟨hF2, hLF2, hinv2, hacc8', hacc8b', hapL, hnm, hLsepQ, hin, hSF1, hw2', hacc⟩ := hpack.get
    have hFP : MemFrame s.mem (((m2.writeLE ptr.toNat 8 a.toNat).writeLE (ptr.toNat + 8) 8 b.toNat).writeLE
        ((s.regs 4).toNat - 40) 8 4755287) (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) :=
      ((hF2.writeLE_inRanges _ ((hin.sub (a := ptr.toNat) (n := 8) (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
        ((hin.sub (a := ptr.toNat + 8) (n := 8) (by omega) (by omega)).append_left _)).writeLE_inRanges _
        ⟨((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24), List.mem_append_right _ (List.mem_singleton_self _),
          by omega, by simp only; omega⟩
    have hstq : MemFrame m2 (((m2.writeLE ptr.toNat 8 a.toNat).writeLE (ptr.toNat + 8) 8 b.toNat).writeLE
        ((s.regs 4).toNat - 40) 8 4755287)
        [(ptr.toNat, ptr.toNat + 32), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)] :=
      by
        refine MemFrame.writeLE_inRanges (MemFrame.writeLE_inRanges (MemFrame.writeLE_inRanges
          (MemFrame.refl m2 _) a.toNat ?_) b.toNat ?_) 4755287 ?_
        · exact ⟨(ptr.toNat, ptr.toNat + 32), List.mem_cons_self .., Nat.le_refl _, by simp only; omega⟩
        · exact ⟨(ptr.toNat, ptr.toNat + 32), List.mem_cons_self .., by simp only; omega, by simp only; omega⟩
        · exact ⟨((s.regs 4).toNat - 40, (s.regs 4).toNat - 32), List.mem_cons_of_mem _ (List.mem_singleton_self _),
            Nat.le_refl _, by simp only; omega⟩
    have hLsepQ2 : LiveSep L [(ptr.toNat, ptr.toNat + 32), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)] := by
      intro x hx
      have h1 := hLsepQ x hx
      have h2 := hwL x hx
      simp only [outside_cons, outside_nil, and_true] at h1 h2 ⊢
      omega
    have hSFP : StackFacts (s.regs 4).toNat a.toNat b.toNat ret (s.regs 5).toNat
        (((m2.writeLE ptr.toNat 8 a.toNat).writeLE (ptr.toNat + 8) 8 b.toNat).writeLE
        ((s.regs 4).toNat - 40) 8 4755287) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
        exact hA2
      · repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
        exact hB2
      · repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
        exact hLR2
      · repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
        exact hFP2
    exact putTail impl R hput ret hret s _ a b L bud (bud - 32) ptr.toNat _ hP hT hnw2 hgr hgb ha4 hw4 hal hb4 hgo hwrt
      hokP (Or.inr rfl) rfl (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF, callRegs64_apply, MapAmd64.keepABI_apply])
      (by simp [setRegF, callRegs64_apply, MapAmd64.keepABI_apply]) (by simp [setRegF, h_x15]) rfl ptr.isLt hFP
      (LiveFrame.trans hLF2 (LiveFrame.of_win hstq hLsepQ2) (fun _ _ h => h))
      (by rw [Arm64.Memory.readLE_writeLE_self] <;> omega)
      ⟨hptr0, hal8', by omega, by simp only [Arm64.Memory.accessible_writeLE]; exact hacc, rfl⟩
      (by
        rw [liveSep_append]
        refine ⟨hwL, ?_⟩
        simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true]
        omega)
      hnm
      (by
        have := RtInv.inv_frame' (ws := [(ptr.toNat, ptr.toNat + 32), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)])
          (m := m2) (hstq) (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact Or.inr ⟨(ptr.toNat, ptr.toNat + 32), List.mem_append_right _ (List.mem_singleton_self _),
                Nat.le_refl _, by simp⟩
            · exact Or.inl (outside_rt_of_win hwrt (by omega) (by omega))) hinv2
        simpa using this)
      hSFP
  · -- a pooled buffer
    obtain ⟨hd0, hd8, hd48, hdacc, hrs⟩ := hSh
    subst hrs
    have hr0' : r 0 = (BitVec.ofNat 64 (ptrN)) := BitVec.eq_of_toNat_eq (by simpa [hT] using hr0)
    have hr1' : r 3 ≠ 0#64 := fun h => by simp [h] at hd0
    have hin := hinrt _ (List.mem_singleton_self _)
    simp only [Nat.add_sub_cancel_left] at hin
    have hapL : ApartAll (BitVec.toNat (r 3)) 32 L := by
      have := hfresh _ (List.mem_singleton_self _)
      simpa using this
    obtain ⟨hA1, hB1, hLR1, hFP1⟩ := hSF1
    have hw1 : m1.accessible ((s.regs 4).toNat - 4136) (4136 + 24) true = true := by
      rw [hF1.accessible]; exact hw4
    have hacc8 : m1.accessible (BitVec.toNat (r 3)) 8 true = true :=
      Arm64.Memory.accessible_mono _ hdacc (Nat.le_refl _) (by omega)
    have hacc8b : m1.accessible (BitVec.toNat (r 3) + 8) 8 true = true :=
      Arm64.Memory.accessible_mono _ hdacc (by omega) (by omega)
    have hpd := InRanges.disjoint hin (hwrt _ (List.mem_singleton_self _))
    simp only at hpd
    have hLsepQ : LiveSep L [(BitVec.toNat (r 3), BitVec.toNat (r 3) + 32)] := fun x hx => by
      have := hapL x hx
      simp only [Apart] at this
      simp only [outside_cons, outside_nil, and_true]
      omega
    have hnm : ∀ x ∈ L, x ∉ [(BitVec.toNat (r 3), BitVec.toNat (r 3) + 32)] := fun x hx hm => by
      simp only [List.mem_singleton] at hm; subst hm
      exact notMem_of_apartAll (by omega) hapL hx
    have hpack := Hid.mk (And.intro hF1 (And.intro hLF1 (And.intro hinvG (And.intro hapL (And.intro hnm
      (And.intro hLsepQ (And.intro hin (And.intro hdacc hw1))))))))
    clear hfr1 hlf1 hns1 hF1 hLF1 hinvG hapL hnm hLsepQ hin hfresh hinrt hsep key1 hSF1o
    janus64_run [hA1, hB1, hLR1, hFP1, hw1] until [Extracted.program.contractAddr "sync.(*Pool).Put"]
    obtain ⟨hF1, hLF1, hinvG, hapL, hnm, hLsepQ, hin, hdacc, hw1'⟩ := hpack.get
    have hSFP : StackFacts (s.regs 4).toNat a.toNat b.toNat ret (s.regs 5).toNat
        (((m1.writeLE (BitVec.toNat (r 3)) 8 a.toNat).writeLE (BitVec.toNat (r 3) + 8) 8 b.toNat).writeLE
        ((s.regs 4).toNat - 40) 8 4755287) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
        exact hA1
      · repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
        exact hB1
      · repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
        exact hLR1
      · repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint (h := by omega)]
        exact hFP1
    have hFP : MemFrame s.mem (((m1.writeLE (BitVec.toNat (r 3)) 8 a.toNat).writeLE (BitVec.toNat (r 3) + 8) 8
        b.toNat).writeLE ((s.regs 4).toNat - 40) 8 4755287)
        (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) :=
      ((hF1.writeLE_inRanges _ ((hin.sub (a := BitVec.toNat (r 3)) (n := 8) (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
        ((hin.sub (a := BitVec.toNat (r 3) + 8) (n := 8) (by omega) (by omega)).append_left _)).writeLE_inRanges _
        ⟨((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24), List.mem_append_right _ (List.mem_singleton_self _),
          by omega, by simp only; omega⟩
    have hstq : MemFrame m1 (((m1.writeLE (BitVec.toNat (r 3)) 8 a.toNat).writeLE (BitVec.toNat (r 3) + 8) 8
        b.toNat).writeLE ((s.regs 4).toNat - 40) 8 4755287)
        [(BitVec.toNat (r 3), BitVec.toNat (r 3) + 32), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)] :=
      by
        refine MemFrame.writeLE_inRanges (MemFrame.writeLE_inRanges (MemFrame.writeLE_inRanges
          (MemFrame.refl m1 _) a.toNat ?_) b.toNat ?_) 4755287 ?_
        · exact ⟨(BitVec.toNat (r 3), BitVec.toNat (r 3) + 32), List.mem_cons_self .., Nat.le_refl _, by simp only; omega⟩
        · exact ⟨(BitVec.toNat (r 3), BitVec.toNat (r 3) + 32), List.mem_cons_self .., by simp only; omega, by simp only; omega⟩
        · exact ⟨((s.regs 4).toNat - 40, (s.regs 4).toNat - 32), List.mem_cons_of_mem _ (List.mem_singleton_self _),
            Nat.le_refl _, by simp only; omega⟩
    have hLsepQ2 : LiveSep L [(BitVec.toNat (r 3), BitVec.toNat (r 3) + 32),
        ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)] := by
      intro x hx
      have h1 := hLsepQ x hx
      have h2 := hwL x hx
      simp only [outside_cons, outside_nil, and_true] at h1 h2 ⊢
      omega
    exact putTail impl R hput ret hret s _ a b L bud bud (BitVec.toNat (r 3)) _ hP hT hnw2 hgr hgb ha4 hw4 hal hb4 hgo hwrt
      hokP (Or.inl rfl) rfl (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF, callRegs64_apply, MapAmd64.keepABI_apply])
      (by simp [setRegF, callRegs64_apply, MapAmd64.keepABI_apply]) (by simp [setRegF, MapAmd64.keepX15, h_x15])
      rfl (r 3).isLt hFP
      (LiveFrame.trans hLF1 (LiveFrame.of_win hstq hLsepQ2) (fun _ _ h => h))
      (by rw [Arm64.Memory.readLE_writeLE_self] <;> omega)
      ⟨hd0, hd8, hd48, by simp only [Arm64.Memory.accessible_writeLE]; exact hdacc, rfl⟩
      (by
        rw [liveSep_append]
        refine ⟨hwL, ?_⟩
        simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true]
        omega)
      hnm
      (by
        have := RtInv.inv_frame' (ws := [(BitVec.toNat (r 3), BitVec.toNat (r 3) + 32),
          ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)])
          (m := m1) (hstq) (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact Or.inr ⟨(BitVec.toNat (r 3), BitVec.toNat (r 3) + 32),
                List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by simp⟩
            · exact Or.inl (outside_rt_of_win hwrt (by omega) (by omega))) hinvG
        simpa using this)
      hSFP


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The live runtime `R` is the toy bump allocator of `Janus.Contracts.LiveToy` (`toyR`), whose
runtime-owned ranges are the heap, the bump cell, the barrier buffer and the type descriptors
`tys` (none: `scratch`'s descriptor is read-only data of the binary). Its
`Get` returns nil, its `Put` drops its argument and its `newobject` hands out the next
`64 · Size_` bytes of the heap (code at the three contract addresses). With them `correctness`
applies to a call state of `ScratchSum(3, 5)` with an empty live set (`nonvacuous`), and the call
returns `3 ^ 5` with the guarantee (`returns`). -/

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.PoolSatAmd64
open Janus.Contracts.LiveSat (bump_acc)
open Janus.Contracts.PoolSat (toyInv_init_tys)

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
def implAt : List Amd64.Segment :=
  [{ name := "model.Get", base := cG, bytes := getCode },
   { name := "model.Put", base := cP, bytes := putCode },
   { name := "model.newobject", base := cN, bytes := newobjectCodeD }]

def linked : Amd64.Program := Extracted.program.link implAt

set_option maxRecDepth 20000 in
theorem hget : PoolGetLive linked cG 4096 R pT BufObj := by
  refine poolGetLive_of_run tys linked cG ok pT BufObj ?_
  intro s hpc hra h48 hrs
  change ReachesRet linked _ s _
  janus64_run
  exact ⟨by simp [setRegF], by simp [setRegF], rfl, by simp [retAddrOf], by simp [setRegF], by simp [setRegF],
    by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
theorem hput : PoolPutLive linked cP 4096 R pT BufObj := by
  refine poolPutLive_of_run tys tysOK linked cP ok pT BufObj ?_
  intro s hpc hra h48 hrs
  change ReachesRet linked _ s _
  janus64_run
  exact ⟨rfl, by simp [retAddrOf], by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
theorem hnew : NewobjectLiveContract64 linked cN 4096 R := by
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  have hWs := pre.2.2.2.2.2.2
  have hret : Outside (s.regs 4).toNat 8 (toyRt tys) := by
    have h := hWs ((s.regs 4).toNat, (s.regs 4).toNat + 8) (by simp [liveWin64])
    simp only [Nat.add_sub_cancel_left] at h
    exact h
  have hap : Apart 4194304 8 (s.regs 4).toNat 8 := ((inRanges_bump tys).apart hret).symm
  change ReachesRet linked _ s _
  janus64_run
  exact finish_newobjectD tysOK _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp [setRegF, BUMP]) (by simp [BUMP]) pre

/-! ### The call state -/

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def dataByte (a : Nat) : Option Arm64.Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

/-- The data segments, the bump cell `HEAP` and the return address `ret` at `[RSP]`; zero elsewhere. -/
def bytes0 (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else 0

def mem0 : Arm64.Memory :=
  ⟨bytes0, [⟨sp0 - 4136, 4160, true⟩, ⟨g0, 0x100, false⟩, ⟨P, 40, true⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 0 then 3 else if i = 3 then 5 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

set_option maxRecDepth 100000 in
theorem setup : CallSetup (linked.withExit ret) Extracted.entry [3, 5] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
      intro i h
      rcases i with _ | _ | i
      · rfl
      · rfl
      · exact absurd h (by simp),
    rfl⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
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

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_tys tysOK (m := s0.mem) (b := 0x400) (g := (s0.regs 14).toNat) (by decide) (by decide)
    (fun i hi hi' => ?_) (by decide) (by decide) (by decide) (fun t ht => absurd ht (by simp [tys]))
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]

theorem s0_sp : (s0.regs 4).toNat = sp0 := by simp [s0, sp0]
theorem s0_g : (s0.regs 14).toNat = g0 := by simp [s0, g0]

theorem hP' : P = 5709280 := by unfold P; decide
theorem hb' : bT = (bufN) := by unfold bT; decide

set_option maxRecDepth 100000 in
theorem guard0 : StackGuardOK s0 4136 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [regG, stackguard0Offset, s0_g]; simp [g0]
  · simp only [regG, stackguard0Offset, s0_g]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, s0_g, s0_sp]; decide

set_option maxRecDepth 100000 in
theorem stack0 : StackWritable s0 4136 24 := by
  unfold StackWritable
  simp only [regSP, s0_sp]
  exact ⟨by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 4136 ∧ StackWritable s0 4136 24 ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 14).toNat + 16) 8 (((s0.regs 4).toNat - 4136, (s0.regs 4).toNat + 24) :: R.rt) ∧
    LiveSep [((s0.regs 4).toNat - 4136, (s0.regs 4).toNat + 24)] R.rt ∧
    LiveSep [] [((s0.regs 4).toNat - 4136, (s0.regs 4).toNat + 24)] ∧
    (∀ r ∈ R.rt, 0 < r.1) ∧ (poolAddr + 40 ≤ (s0.regs 4).toNat - 4136 ∨ (s0.regs 4).toNat + 24 ≤ poolAddr) ∧
    Outside bufType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
    R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [bufType] ∧
    s0.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
    R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) ∧ 32 ≤ 0x400 := by
  rw [hP, hTy, aG, aP, aN, s0_sp, s0_g]
  have hrt : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl
  refine ⟨guard0, stack0, by simp [sp0], dataLoaded, ?_, ?_, by simp, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, inv0, by decide⟩
  · rw [hrt]; simp only [outside_cons, outside_nil, and_true, hP', hb', g0, sp0, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · rw [hrt]; simp only [liveSep_cons, liveSep_nil, outside_cons, outside_nil, and_true, hP', hb', g0, sp0, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · intro r hr
    rw [hrt] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [HEAP, BUMP, WBUF] <;> omega
  · simp only [s0_sp, sp0, hP']; decide
  · rw [hb', hrt]; simp only [outside_cons, outside_nil, and_true, HEAP, HEND, HSIZE, BUMP, WBUF]; decide
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [hP']; unfold newOffset; decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (ret : Nat) (s : State) (L : List (Nat × Nat))
    (bud : Nat),
    PoolGetLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      ptrType BufObj ∧
    PoolPutLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      ptrType BufObj ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [3, 5] s ∧
    (BufObj = BufObj ∧ StackGuardOK s 4136 ∧ StackWritable s 4136 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
      Extracted.program.DataLoaded s.mem ∧
      Outside ((s.regs 14).toNat + 16) 8 (((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24) :: R.rt) ∧
      LiveSep [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] R.rt ∧
      LiveSep L [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] ∧
      (∀ r ∈ R.rt, 0 < r.1) ∧ (poolAddr + 40 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ poolAddr) ∧
      Outside bufType 16 R.rt ∧
      R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
      R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
      R.ok (Extracted.program.contractAddr "runtime.newobject") [bufType] ∧
      s.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
      R.inv bud L (s.regs 14).toNat (view R.rt L s.mem) ∧ 32 ≤ bud) := by
  refine ⟨implAt, R, ret, s0, [], 0x400, ?_, ?_, ?_, hret, setup, ⟨rfl, pre⟩⟩
  · rw [aG, hPT]; exact hget
  · rw [aP, hPT]; exact hput
  · rw [aN]; exact hnew

/-- So the guarantee is reached: `ScratchSum(3, 5)` returns `3 ^ 5 = 6`, with the runtime's invariant
again for the same (empty) live set. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = (3#64 ^^^ 5#64).toNat ∧
      ∃ d b', (b' = 0x400 ∨ b' = 0x400 - 32) ∧
        MemFrame s0.mem s'.mem (R.rt ++ [((s0.regs 4).toNat - 4136, (s0.regs 4).toNat + 24), (d, d + 32)]) ∧
        LiveFrame s0.mem s'.mem [] [] ∧ R.inv b' [] (s0.regs 14).toNat (view R.rt [] s'.mem) := by
  have h := correctness implAt R BufObj (by rw [aG, hPT]; exact hget) (by rw [aP, hPT]; exact hput)
    (by rw [aN]; exact hnew) 3 5 [] 0x400
    ret hret s0 setup ⟨rfl, pre⟩
  exact h

end Witness

end Proof
