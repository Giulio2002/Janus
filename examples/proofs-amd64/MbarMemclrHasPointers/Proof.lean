import Janus
import Extracted

/-!
# `runtime.memclrHasPointers` (amd64) meets the `MemclrHasPointers` contract, with `runtime.bulkBarrierPreWrite` and `runtime.memclrNoHeapPointers` as contracts

**Guarantee.** For every memory model `M` with its laws, every stack bound `d` of the callees and
every code `impl` linked at the contract addresses, if the callees meet `MemAmd64.BulkBarrierOff … M wb d` and `MemclrNoHeapPointers … M d`, the
amd64 machine code of Go 1.26's `runtime.memclrHasPointers` satisfies `Janus.Contracts.MemAmd64.MemclrHasPointers … M wb (d + 48)`: from every
call state with the contract's precondition (the write barrier off) it returns to `[RSP]` without
faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`, `FS` and the control bits of `MXCSR` kept,
memory changed only in `M.priv`, its stack window and the destination, `M.Env` kept, and the `n` bytes at `ptr` are zero.

**What the code does.** No stack check; `PUSHQ BP; SUBQ $0x20, SP`; spill `ptr`, `n` to their
argument slots; `CALL runtime.bulkBarrierPreWrite(ptr, 0, n, nil)` (it checks the barrier itself,
so `wb` is any address the contract's precondition grants); reload `ptr`, `n`;
`CALL runtime.memclrNoHeapPointers(ptr, n)`; `ADDQ; POPQ BP; RET`. At both calls `RSP` is 48 bytes
below the entry `RSP`, so the callees with bound `d` stay within `d + 48`; the second call's
memory differs from the entry also in `M.priv`, so its precondition comes from the first call's
return (`eqPre_ws`: the guard word is outside `M.priv` by the contract).

**Assumptions.** The contract's precondition, `M.Laws`, and the `BulkBarrierOff` and
`MemclrNoHeapPointers` contracts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts.MemAmd64
open Janus.Contracts.Mem (MemModel WriteBarrierOff Zeroed Copied)

namespace Proof

/-- Name the state a run stopped in. -/
theorem reach_name {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

/-- A final state that keeps `RBP`, `R14`, `X15`, `DF` and `FS`, has `RSP + 8` and is at the
return address is `retState` of its own registers, flags and memory (the state part of
`MemAmd64.EqRet.intro`). -/
theorem retState_of {s s' : State} (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) :
    s' = retState s s'.regs s'.xmm s'.ymmHi s'.flags s'.mxcsr s'.mem := by
  obtain ⟨r, rip, fl, xmm, mem, yh, fsb, df, mx, x8, fw⟩ := s'
  simp only at hsp h5 h14 hx hrip hfs hdf hx87 hfw ⊢
  subst hrip hfs hdf hx87 hfw
  simp only [retState, State.mk.injEq, and_true, true_and]
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Janus.Contracts.MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact hsp
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [Janus.Contracts.MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-- `EqPre` at a call site `S` whose memory differs from the entry `s` only in the entry's
callee window (frame pushes and argument spills), with `RSP` at `frame` bytes below the entry
`RSP` (amd64; as `MemAmd64.EqPre.of_caller`, with the spill slots allowed). -/
theorem eqPre_at {s S : State} {d frame nargs : Nat} (hg : StackGuardOK s (d + frame))
    (hal : (s.regs 4).toNat % 8 = 0) (hd : d + frame ≤ (s.regs 4).toNat)
    (hb : (s.regs 4).toNat + 8 + 8 * 2 ≤ 2 ^ 48)
    (hacc : s.mem.accessible ((s.regs 4).toNat - (d + frame)) (d + frame + 8 + 8 * 2) true = true)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 (calleeStack s (d + frame) 2))
    (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 2))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg' : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame) : EqPre d nargs S := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have hgo' := hgo
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
    and_true] at hgo'
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, hx, hdf, hra⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg']; omega
  · simp only [regG, stackguard0Offset, hg', hf.accessible]; exact hg2
  · simp only [stackguard0, regG, regSP, stackguard0Offset, hg', hsp]
    rw [hf.readLE _ _ hgo]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hg', hsp]
    omega

/-- `Input` at such a call site of a range readable at the entry and outside the entry's callee
window (amd64). -/
theorem input_at {s S : State} {d frame nargs a n : Nat} {ws : List (Nat × Nat)}
    (hf : MemFrame s.mem S.mem ws)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame)
    (hfd : frame ≤ (s.regs 4).toNat) (hb : a + n ≤ 2 ^ 48) (hacc : s.mem.accessible a n false = true)
    (ho : Outside a n (calleeStack s (d + frame) 2)) : Input S d nargs a n := by
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
    and_true] at ho
  refine ⟨hb, by rw [hf.accessible]; exact hacc, ?_⟩
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
    and_true, hsp]
  omega

/-- A model environment living in `priv` survives changes in the entry's callee window when that
window is outside `priv`. -/
theorem env_at {Env : Janus.Arm64.Memory → W64 → Prop} {priv : List (Nat × Nat)}
    (hl : ∀ m m' g, Env m g → Agrees m m' priv → Env m' g) {s : State} {m : Janus.Arm64.Memory}
    {g : W64} {D : Nat} (he : Env s.mem g) (hout : Outside ((s.regs 4).toNat - D) (D + 8 + 8 * 2) priv)
    (hD : D ≤ (s.regs 4).toNat) (hm : MemFrame s.mem m (calleeStack s D 2)) : Env m g :=
  hl _ _ _ he (Agrees.of_memFrame hm fun a ha => by
    obtain ⟨r, hr, h1, h2⟩ := ha
    have := MemFrame.outside_mem hout hr
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true]
    omega)

/-- The caller's frame then the callee's frame (with the private ranges `P`) is the caller's
frame (amd64). -/
theorem frame_ret {s S : State} {m : Janus.Arm64.Memory} {P : List (Nat × Nat)} {d frame nargs : Nat}
    (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 2))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame)
    (hfd : d + frame ≤ (s.regs 4).toNat)
    (h2 : MemFrame S.mem m (P ++ calleeStack S d nargs)) :
    MemFrame s.mem m (P ++ calleeStack s (d + frame) 2) :=
  hf.trans h2 fun a k h => by
    simp only [outside_append] at h ⊢
    refine ⟨h.2, h.1, ?_⟩
    have h2 := h.2
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hsp] at h2 ⊢
    omega

/-- How a typed-memory proof ends (amd64): as `hRet_intro`, for `TRet`. -/
theorem tRet_intro {M : Janus.Contracts.Mem.MemModel} {d nargs : Nat} {extra : List (Nat × Nat)}
    {s s' : State} {P : Janus.Arm64.Memory → Prop}
    (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64)
    (hf : MemFrame s.mem s'.mem (M.priv ++ calleeStack s d nargs ++ extra))
    (he : M.Env s'.mem (s.regs 14)) (hp : P s'.mem) : TRet M d nargs extra s s' P :=
  ⟨_, _, _, _, _, _, retState_of hsp h5 h14 hx hrip hfs hdf, hmx, hf, he, hp⟩

/-- The caller's frame then the callee's frame (with the private ranges `P` and the extra
ranges `X` of a typed-memory contract) is the caller's frame (amd64). -/
theorem frame_retx {s S : State} {m : Janus.Arm64.Memory} {P X : List (Nat × Nat)} {d frame nargs : Nat}
    (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 2))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame)
    (hfd : d + frame ≤ (s.regs 4).toNat)
    (h2 : MemFrame S.mem m (P ++ calleeStack S d nargs ++ X)) :
    MemFrame s.mem m (P ++ calleeStack s (d + frame) 2 ++ X) :=
  hf.trans h2 fun a k h => by
    simp only [outside_append] at h ⊢
    refine ⟨h.1.2, ⟨h.1.1, ?_⟩, h.2⟩
    have h2 := h.1.2
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hsp] at h2 ⊢
    omega

/-- As `eqPre_at`, for a call site whose memory differs from the entry `s` in any ranges `ws`
the guard word is outside of (amd64; for a second call). -/
theorem eqPre_ws {s S : State} {d frame nargs : Nat} {ws : List (Nat × Nat)}
    (hg : StackGuardOK s (d + frame)) (hal : (s.regs 4).toNat % 8 = 0) (hd : d + frame ≤ (s.regs 4).toNat)
    (hb : (s.regs 4).toNat + 8 + 8 * 2 ≤ 2 ^ 48)
    (hacc : s.mem.accessible ((s.regs 4).toNat - (d + frame)) (d + frame + 8 + 8 * 2) true = true)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 (calleeStack s (d + frame) 2))
    (hgw : Outside ((s.regs 14).toNat + 16) 8 ws) (hf : MemFrame s.mem S.mem ws)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg' : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame) : EqPre d nargs S := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have hgo' := hgo
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
    and_true] at hgo'
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, hx, hdf, hra⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg']; omega
  · simp only [regG, stackguard0Offset, hg', hf.accessible]; exact hg2
  · simp only [stackguard0, regG, regSP, stackguard0Offset, hg', hsp]
    rw [hf.readLE _ _ hgw]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hg', hsp]
    omega

/-- As `frame_retx`, from a frame that already includes the private ranges. -/
theorem frame_retx' {s S : State} {m : Janus.Arm64.Memory} {P X : List (Nat × Nat)} {d frame nargs : Nat}
    (hf : MemFrame s.mem S.mem (P ++ calleeStack s (d + frame) 2 ++ []))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame)
    (hfd : d + frame ≤ (s.regs 4).toNat)
    (h2 : MemFrame S.mem m (P ++ calleeStack S d nargs ++ X)) :
    MemFrame s.mem m (P ++ calleeStack s (d + frame) 2 ++ X) :=
  hf.trans h2 fun a k h => by
    simp only [outside_append, outside_nil, and_true] at h ⊢
    refine ⟨⟨h.1.1, h.1.2⟩, ⟨h.1.1, ?_⟩, h.2⟩
    have h2 := h.1.2
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hsp] at h2 ⊢
    omega

set_option maxHeartbeats 4000000 in
/-- **`runtime.memclrHasPointers` (amd64) meets its contract**, given its callees'. -/
theorem correctness (impl : List Janus.Amd64.Segment) (M : MemModel) (hM : M.Laws) (wb d : Nat)
    (hbb : BulkBarrierOff (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.bulkBarrierPreWrite") M wb d)
    (hclr : MemclrNoHeapPointers (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") M d) :
    MemclrHasPointers (Extracted.program.link impl) Extracted.entry M wb (d + 48) := by
  intro s hpc ⟨⟨he, hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hout, ⟨hw1, hw2, hw3⟩, hwb, hgo, hgp⟩,
    hp8, hn8, ⟨hD1, hD2, hD3, hD4, hD5⟩⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  have hD3' := hD3
  have hgo' := hgo
  have hw3' := hw3
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    at hD3 hw3 hgo hD5
  have hsp48 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hS : ∀ v, MemFrame s.mem ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat + 8) 8 (s.regs 0).toNat).writeLE ((s.regs 4).toNat + 16) 8 (s.regs 3).toNat).writeLE
      ((s.regs 4).toNat - 48) 8 v) (calleeStack s (d + 48) 2) := by
    intro v; simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame
  janus64_run until [Extracted.program.contractAddr "runtime.bulkBarrierPreWrite"]
  refine reach_name ?_
  intro S hSd
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 48 := by
    subst hSd; simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
  obtain ⟨q1, q2, q3⟩ := eqPre_at (S := S) (nargs := 4) (frame := 48) hg hal hd hsp hacc hgo'
    (by subst hSd; exact hS _) hS4 (by subst hSd; rfl) (by subst hSd; exact hx) (by subst hSd; rfl)
    (by rw [hS4]; subst hSd; rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide) (by decide) (by decide)
  subst hSd
  refine ReachesRet.call hbb rfl ⟨⟨env_at hM.env_frame he hout hd (hS _), q1, q2, ?_, ?_, ?_, q3,
    by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; exact hgp⟩, ?_, ?_, ?_⟩ ?_
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
    exact Outside.of_sub hout (by omega) (by omega)
  · refine ⟨hw1, by rw [(hS _).accessible]; exact hw2, ?_⟩
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
    omega
  · simp only [WriteBarrierOff] at hwb ⊢
    rw [(hS _).readLE _ _ hw3']; exact hwb
  · simpa [setRegF] using hp8
  · simp [setRegF]
  · simpa [setRegF] using hn8
  intro s1 hpc1 ⟨r1, x1, y1, fl1, mx1, m1, hs1, hmx1, hfr1, he1, _⟩
  subst hs1
  have hfr1' := hfr1
  have hF1 := frame_retx (nargs := 4) (X := []) (hS _)
    (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]) (by decide) (by omega) hfr1'
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
    Nat.reduceEqDiff, hsp48] at hfr1
  simp only [setRegF, reduceIte, Nat.reduceEqDiff] at he1 hmx1
  have hm1acc : m1.accessible ((s.regs 4).toNat - (d + 48)) (d + 48 + 8 + 8 * 2) true = true := by
    rw [hF1.accessible]; exact hacc
  have hm1acc' := Janus.Arm64.Memory.accessible_read_of_write _ hm1acc
  simp only [retState] at hpc1 ⊢
  janus64_run until [Extracted.program.contractAddr "runtime.memclrNoHeapPointers"]
  have hF1w : ∀ v, MemFrame s.mem (m1.writeLE ((s.regs 4).toNat - 48) 8 v)
      (M.priv ++ calleeStack s (d + 48) 2 ++ []) := fun v =>
    hF1.writeLE v (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..)))
      (by simp; omega) (by simp; omega)
  have hgw : Outside ((s.regs 14).toNat + 16) 8 (M.priv ++ calleeStack s (d + 48) 2 ++ []) := by
    simp only [outside_append, outside_nil, and_true]; exact ⟨hgp, hgo'⟩
  refine ReachesRet.call hclr rfl ⟨?_, eqPre_ws (frame := 48) hg hal hd hsp hacc hgo' hgw (hF1w _)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]) (by rfl)
      (by simp only [Janus.Contracts.MapAmd64.keepX15, reduceIte]; exact hx) (by rfl)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
          rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide) (by decide) (by decide), ?_, ?_⟩ ?_
  · exact hM.env_frame _ _ _ he1 (agrees_writeLE _ _ (Outside.of_sub hout (by omega) (by omega)))
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
    exact Outside.of_sub hout (by omega) (by omega)
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
    refine ⟨hD1, by rw [(hF1w _).accessible]; exact hD2, ?_, hD4, ?_⟩ <;>
      simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
        and_true, setRegF, reduceIte, Nat.reduceEqDiff, hsp48] <;> omega
  intro s2 hpc2 ⟨r, x, y, fl, mx, m2, hs2, hmx, hfr, he2, hz⟩
  subst hs2
  have hfr' := hfr
  have hF := frame_retx' (nargs := 2) (hF1w _)
    (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]) (by decide) (by omega) hfr'
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
    Nat.reduceEqDiff, hsp48] at hfr
  simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hz he2 hmx hF
  have hm2acc : m2.accessible ((s.regs 4).toNat - (d + 48)) (d + 48 + 8 + 8 * 2) true = true := by
    rw [hF.accessible]; exact hacc
  have hm2acc' := Janus.Arm64.Memory.accessible_read_of_write _ hm2acc
  simp only [retState] at hpc2 ⊢
  janus64_run
  exact tRet_intro (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) hdf.symm (by simp only; rw [hmx, hmx1]) hF
    (by simpa [Janus.Contracts.MapAmd64.keepABI, setRegF] using he2) hz

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MemSatAmd64

/-- `runtime.memclrNoHeapPointers` is the model `memclrCode` (`REP STOSB`, at `A0`, behind a jump
at the contract address). -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.memclrNoHeapPointers"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := memclrCode }
/-- `runtime.bulkBarrierPreWrite` is the straight-line model `bulkBarrierCode` (`RET`: the barrier
is off), placed at its contract address. -/
def bAddr : Nat := Extracted.program.contractAddr "runtime.bulkBarrierPreWrite"
def bulkSeg : Janus.Amd64.Segment := { name := "bulk", base := bAddr, bytes := bulkBarrierCode }
def implAt : List Janus.Amd64.Segment := [bulkSeg, tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [bulkSeg, tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model (d : Nat) : MemclrNoHeapPointers (Extracted.program.link implAt) cAddr M0 d := by
  have hA : MemclrNoHeapPointers (Extracted.program.link implAt) A0 M0 d := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (memclrNoHeapPointers_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨e, ⟨⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨e, ⟨⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

theorem modelB (d : Nat) : BulkBarrierOff (Extracted.program.link implAt) bAddr M0 WB d := by
  rw [show Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } from rfl]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, _, _, hgo, _⟩, _, _, _⟩
  janus_eval_nat hC : bAddr
  rw [hC] at hpc
  janus64_run
  exact tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) trivial trivial

/-- The witness call state: `memclrHasPointers(DST, 64)` on `EqHashModel.wmem64` (the flag word
`WB` is zero), goroutine `wg`, `RSP = wsp`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 DST else if i = 3 then 64
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (the callees' bound 64, flag word `WB`). -/
theorem pre : TPre M0 WB (64 + 48) 2 s0 ∧ (s0.regs 0).toNat % 8 = 0 ∧ (s0.regs 3).toNat % 8 = 0 ∧
    Dest M0 s0 (64 + 48) 2 (s0.regs 0).toNat (s0.regs 3).toNat := by
  refine ⟨⟨trivial, ⟨by decide, by decide, by decide⟩, ?_, trivial, ?_, wmem64_wbOff, ?_, trivial⟩,
    by decide, by decide, ?_⟩ <;>
    simp only [CallOK, Input, Dest, M0, calleeStack, Janus.Contracts.MapAmd64.calleeStack,
      outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MemModel) (wb d : Nat) (s : State),
    M.Laws ∧
    BulkBarrierOff (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.bulkBarrierPreWrite") M wb d ∧
    MemclrNoHeapPointers (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") M d ∧
    s.rip = BitVec.ofNat 64 Extracted.entry ∧
    (TPre M wb (d + 48) 2 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 3).toNat % 8 = 0 ∧
      Dest M s (d + 48) 2 (s.regs 0).toNat (s.regs 3).toNat) :=
  ⟨implAt, M0, WB, 64, s0, M0_laws, modelB 64, model 64, rfl, pre⟩

/-- `correctness` at `s0`: the 64 bytes at `DST` are cleared. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (retAddrOf s0) s0
    (fun s' => TRet M0 (64 + 48) 2 [((s0.regs 0).toNat, (s0.regs 0).toNat + (s0.regs 3).toNat)] s0 s'
      fun m => Zeroed m (s0.regs 0).toNat (s0.regs 3).toNat) :=
  correctness implAt M0 M0_laws WB 64 (modelB 64) (model 64) s0 rfl pre

end Witness

end Proof
