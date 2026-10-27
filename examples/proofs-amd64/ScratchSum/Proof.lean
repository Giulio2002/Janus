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
    (hP : poolAddr = 5701056) (hT : ptrType = 4822144)
    (hg1 : (s.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hg2 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4136 < (s.regs 4).toNat)
    (ha4 : (s.regs 4).toNat + 24 ≤ 2 ^ 48)
    (hw4 : s.mem.accessible ((s.regs 4).toNat - 4136) (4136 + 24) true = true)
    (hal : (s.regs 4).toNat % 8 = 0) (hb4 : 4136 ≤ (s.regs 4).toNat)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 (((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24) :: R.rt))
    (hwrt : LiveSep [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] R.rt)
    (hokP : R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [5701056])
    (hbd : bd = bud ∨ bd = bud - 32)
    (hrip : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put"))
    (hS0 : S.regs 0 = 5701056#64) (hS3 : S.regs 3 = 4822144#64) (hS1 : S.regs 1 = BitVec.ofNat 64 d)
    (hS4 : S.regs 4 = s.regs 4 - 40#64) (hS5 : S.regs 5 = s.regs 4 - 8#64) (hSg : S.regs 14 = s.regs 14)
    (hSx : S.xmm 15 = s.xmm 15) (hSmem : S.mem = mP) (hd64 : d < 2 ^ 64)
    (hFP : MemFrame s.mem mP (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))
    (hLFP : LiveFrame s.mem mP L [])
    (hra : mP.readLE ((s.regs 4).toNat - 40) 8 = 4752087)
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
  have hra' : S.mem.readLE (S.regs 4).toNat 8 = 4752087 := by rw [hS4n]; exact hra
  have hpack := Hid.mk (And.intro hFP (And.intro hLFP (And.intro hlf3 (And.intro hfr3 (And.intro hsh
    (And.intro hinv3 hinv))))))
  clear hFP hLFP hlf3 hfr3 hsh hinv3 hinv hput hns3 hs3 hSF hwL1 hLd
  have hra2 : S.mem.readLE (s.regs 4 - 40#64).toNat 8 = 4752087 := by rw [hsp40]; exact hra
  janus64_run [hA3, hB3, hLR3, hFP3, hra', hra2, hw3]
  obtain ⟨hFP, hLFP, hlf3, hfr3, hsh, hinv3, hinv⟩ := hpack.get
  refine ⟨d, bd, hbd, MemFrame.trans hFP hfr3 (by frame_sub),
    LiveFrame.trans hLFP (LiveFrame.of_sep hlf3 (fun _ _ => trivial) (fun r hr => List.mem_append_left _ hr))
      (fun _ _ h => h), ?_⟩
  simpa [hSg] using hinv3

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv)
    (hget : PoolGetLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Get")
      4096 R ptrType BufObj)
    (hput : PoolPutLive (Extracted.program.link impl) (Extracted.program.contractAddr "sync.(*Pool).Put")
      4096 R ptrType BufObj)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hRty : ∀ b L g v, R.inv b L g v → v.readLE bufType 8 = 32 ∧ v.readLE (bufType + 8) 8 = 0)
    (a b : BitVec 64) (L : List (Nat × Nat)) (bud : Nat) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => StackGuardOK s 4136 ∧ StackWritable s 4136 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 14).toNat + 16) 8 (((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24) :: R.rt) ∧
        LiveSep [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] R.rt ∧
        LiveSep L [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] ∧
        (∀ r ∈ R.rt, 0 < r.1) ∧ InRanges poolAddr 16 R.rt ∧ InRanges (poolAddr + 16) 16 R.rt ∧ InRanges (poolAddr + 32) 8 R.rt ∧
        InRanges bufType 16 R.rt ∧ Outside bufType 16 L ∧
        R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") [poolAddr] ∧
        R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") [poolAddr] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [bufType] ∧
        s.mem.readLE (poolAddr + newOffset) 8 = 0 ∧
        R.inv bud L (s.regs 14).toNat (view R.rt L s.mem) ∧ 32 ≤ bud)
      (fun s s' => (s'.regs 0).toNat = (a ^^^ b).toNat ∧
        ∃ d b', (b' = bud ∨ b' = bud - 32) ∧
          MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24), (d, d + 32)]) ∧
          LiveFrame s.mem s'.mem L [] ∧ R.inv b' L (s.regs 14).toNat (view R.rt L s'.mem)) := by
  intro ret hret s hs ⟨hg, ⟨hb4, ha4, hw4⟩, hal, hd, hgo, hwrt, hwL, hrt0, hpin, hpin2, hpin3, hbin, hbL, hokG, hokP, hokN,
    hnew0, hinv, hbud⟩
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
  have hpw := pool_disjoint hpin hpin2 hpin3 (hwrt _ (List.mem_singleton_self _)) (by simp only; omega)
  simp only at hpw
  rw [hP] at hokG hokP hnew0
  rw [hB] at hbin hbL hRty
  have hgo' := hgo
  simp only [outside_cons, outside_nil, and_true] at hgo'
  have key1 : ∀ S : State, MemFrame s.mem S.mem [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] →
      S.regs 14 = s.regs 14 → (S.regs 4).toNat + 40 = (s.regs 4).toNat → (S.regs 0).toNat = 5701056 →
      S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47 →
      CallOK64 S 4096 1 ∧ StackRoom64 S 4096 1 ∧ S.mem.readLE (5701056 + newOffset) 8 = 0 ∧
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
    have hbw := InRanges.disjoint hbin (hwrt _ (List.mem_singleton_self _))
    simp only at hbw
    have hdesc := hRty _ _ _ _ hinvG
    have hsz : m1.readLE 4874656 8 = 32 := by
      rw [← readLE_view (rt := R.rt) (L := L) (m := m1) (hbin.sub (Nat.le_refl _) (by omega))
        (Outside.of_sub hbL (Nat.le_refl _) (by omega))]; exact hdesc.1
    have hpb : m1.readLE (4874656 + 8) 8 = 0 := by
      rw [← readLE_view (rt := R.rt) (L := L) (m := m1) (hbin.sub (a := 4874656 + 8) (n := 8) (by omega) (by omega))
        (Outside.of_sub hbL (a := 4874656 + 8) (n := 8) (by omega) (by omega))]; exact hdesc.2
    have hmC : MemFrame m1 (m1.writeLE ((s.regs 4).toNat - 40) 8 4752039)
        [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)] := by janus_frame
    have hsz2 : (m1.writeLE ((s.regs 4).toNat - 40) 8 4752039).readLE 4874656 8 = 32 := by
      rw [hmC.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hsz
    have hpb2 : (m1.writeLE ((s.regs 4).toNat - 40) 8 4752039).readLE (4874656 + 8) 8 = 0 := by
      rw [hmC.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hpb
    janus64_run until [Extracted.program.contractAddr "runtime.newobject"]
    have key2 : ∀ S : State, S.mem = m1.writeLE ((s.regs 4).toNat - 40) 8 4752039 → S.regs 14 = s.regs 14 →
        (S.regs 4).toNat + 40 = (s.regs 4).toNat → (S.regs 0).toNat = 4874656 →
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
    have hSF2 := StackFacts.step (n := 1) hwrt hb4 (by omega) (hSF1.ret (by omega) 4752039) hfr2
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
        ((s.regs 4).toNat - 40) 8 4752087) (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) :=
      ((hF2.writeLE_inRanges _ ((hin.sub (a := ptr.toNat) (n := 8) (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
        ((hin.sub (a := ptr.toNat + 8) (n := 8) (by omega) (by omega)).append_left _)).writeLE_inRanges _
        ⟨((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24), List.mem_append_right _ (List.mem_singleton_self _),
          by omega, by simp only; omega⟩
    have hstq : MemFrame m2 (((m2.writeLE ptr.toNat 8 a.toNat).writeLE (ptr.toNat + 8) 8 b.toNat).writeLE
        ((s.regs 4).toNat - 40) 8 4752087)
        [(ptr.toNat, ptr.toNat + 32), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)] :=
      by
        refine MemFrame.writeLE_inRanges (MemFrame.writeLE_inRanges (MemFrame.writeLE_inRanges
          (MemFrame.refl m2 _) a.toNat ?_) b.toNat ?_) 4752087 ?_
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
        ((s.regs 4).toNat - 40) 8 4752087) := by
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
    have hr0' : r 0 = 4822144#64 := BitVec.eq_of_toNat_eq (by simpa [hT] using hr0)
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
        ((s.regs 4).toNat - 40) 8 4752087) := by
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
        b.toNat).writeLE ((s.regs 4).toNat - 40) 8 4752087)
        (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]) :=
      ((hF1.writeLE_inRanges _ ((hin.sub (a := BitVec.toNat (r 3)) (n := 8) (Nat.le_refl _) (by omega)).append_left _)).writeLE_inRanges _
        ((hin.sub (a := BitVec.toNat (r 3) + 8) (n := 8) (by omega) (by omega)).append_left _)).writeLE_inRanges _
        ⟨((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24), List.mem_append_right _ (List.mem_singleton_self _),
          by omega, by simp only; omega⟩
    have hstq : MemFrame m1 (((m1.writeLE (BitVec.toNat (r 3)) 8 a.toNat).writeLE (BitVec.toNat (r 3) + 8) 8
        b.toNat).writeLE ((s.regs 4).toNat - 40) 8 4752087)
        [(BitVec.toNat (r 3), BitVec.toNat (r 3) + 32), ((s.regs 4).toNat - 40, (s.regs 4).toNat - 32)] :=
      by
        refine MemFrame.writeLE_inRanges (MemFrame.writeLE_inRanges (MemFrame.writeLE_inRanges
          (MemFrame.refl m1 _) a.toNat ?_) b.toNat ?_) 4752087 ?_
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

