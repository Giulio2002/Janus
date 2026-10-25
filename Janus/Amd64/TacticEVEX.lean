import Janus.Amd64.TacticAVX2

/-!
# Proof support for the AVX-512 instructions (WP-G)

Extends the `janus64_exec` / `janus64_post` simp sets so that `janus64_run` steps the
instructions of `Janus.Amd64.ExecEVEX`, and proves the **EVEX zero-upper rule**, its VEX and
legacy-SSE counterparts on the AVX-512 state, and the compatibility of the earlier models with
the extended state. Everything is proved from the model.

* `ExecEVEX.exec` is unfolded per constructor (definitional `rfl` equations, as `exec`), and so
  is its operand plumbing (`getZ`, `rdV`, `rdLow`, `done`, `merge`, `selected`, `kb`); `setZ` gets
  the `setXmmF`/`setZmmF` normal form and `setK` the register-file normal form `setRegF` (the
  opmask registers are 64-bit, like the general ones).
* `setZ_128`, `setZ_256`: an EVEX write at 128 or 256 bits is exactly the VEX write
  `ExecAVX.setV`, so the WP-F lemmas about VEX results apply to EVEX.128/256 results.
* `evex_zero_upper` / `exec_evex_zero_upper`: every vector register an EVEX instruction writes at
  `l < 512` bits has bits 511:`l` zero afterwards (and `l = 128`: bits 255:128 too).
* `vex_zero_zmm` / `exec_avx_zero_zmm`: a VEX instruction zeroes bits 511:256 of what it writes;
  `sse_preserves_avx512`: legacy SSE changes neither `ZMM` bits 511:256 nor the opmask registers;
  `avx_preserves_kreg`: no VEX instruction of WP-F touches the opmask registers.
* `sse_compat`, `avx_compat`: **the earlier semantics are unchanged.** The result of a WP-D or
  WP-F instruction, with its AVX-512 state erased (`strip512`), does not depend on the AVX-512
  state it started from: it is the result from the same state with that state zero, i.e. the
  state of the model before WP-G.
-/

namespace Janus.Amd64

/-- The vector registers an `EvexI` instruction writes, with the width it writes them at. -/
def EvexI.vdsts : EvexI XLoc Loc Addr → List (Nat × Nat)
  | .mov _ l _ (.xmm d) _ _ _ | .op _ _ l d _ _ _ _ _ | .uop _ _ l d _ _ _ _ _ | .blendm _ l d _ _ _ _ _
  | .compress _ l (.xmm d) _ _ _ | .expand _ l d _ _ _ | .insert _ l _ d _ _ _ _ _ | .bcast _ _ l d _ _ _
  | .bcastG _ l d _ _ _ | .pmovx _ _ _ l d _ _ _ | .fp _ _ l d _ _ _ _ _ _ => [(d, l)]
  | .extract _ _ c (.xmm d) _ _ _ _ => [(d, c)]
  | _ => []

/-- A state with its AVX-512 part (`ZMM` bits 511:256, `K0`–`K7`) erased. -/
def State.strip512 (s : State) : State := { s with zmmHi := fun _ => 0, kreg := fun _ => 0 }

end Janus.Amd64

namespace Janus.Amd64.Tactic

open Janus.Amd64 Janus.Arm64 Janus.Tactic

/-! ## Simp set: the executor -/

janus_rfl_eqns ExecEVEX.exec [janus64_exec]

attribute [janus64_exec] ExecEVEX.getZ ExecEVEX.rdV ExecEVEX.rdLow ExecEVEX.done ExecEVEX.merge
  ExecEVEX.selected ExecEVEX.kb ExecEVEX.repl ExecEVEX.evalOp ExecEVEX.evalUop State.zmm
  ExecEVEX.EOp.suppress ExecEVEX.EUOp.suppress ExecEVEX.EOp.count ExecEVEX.pintElementwise ExecEVEX.rdK

/-- The EVEX register write in the normal form of the scalar instructions. -/
@[janus64_exec] theorem ExecEVEX.setZ_eq (s : State) (l n v : Nat) :
    ExecEVEX.setZ s l n v =
      { s with xmm := setXmmF s.xmm n (BitVec.ofNat 128 v),
               ymmHi := setXmmF s.ymmHi n (if l = 128 then 0 else BitVec.ofNat 128 (v / 2 ^ 128)),
               zmmHi := setZmmF s.zmmHi n (if l = 512 then BitVec.ofNat 256 (v / 2 ^ 256) else 0) } := rfl

/-- The opmask write in the register-file normal form. -/
@[janus64_exec] theorem ExecEVEX.setK_eq (s : State) (n v : Nat) :
    ExecEVEX.setK s n v = { s with kreg := setRegF s.kreg n (BitVec.ofNat 64 v) } := rfl

/-! ## Compatibility of EVEX.128/256 with VEX -/

/-- An EVEX write at 128 bits is the VEX.128 write. -/
theorem setZ_128 (s : State) (n v : Nat) : ExecEVEX.setZ s 128 n v = ExecAVX.setV s 128 n v := by
  simp [ExecEVEX.setZ, ExecAVX.setV]

/-- An EVEX write at 256 bits is the VEX.256 write. -/
theorem setZ_256 (s : State) (n v : Nat) : ExecEVEX.setZ s 256 n v = ExecAVX.setV s 256 n v := by
  simp [ExecEVEX.setZ, ExecAVX.setV]

/-- Reading at 128/256 bits is WP-F's `getV`. -/
theorem getZ_eq_getV (s : State) (l n : Nat) (hl : l = 128 ∨ l = 256) :
    ExecEVEX.getZ s l n = ExecAVX.getV s l n := by
  rcases hl with rfl | rfl <;> simp [ExecEVEX.getZ, ExecAVX.getV]

/-- Without a write mask the result is written whole. -/
@[janus64_exec, janus64_post] theorem merge_noMask (s : State) (e l d : Nat) (z : Bool) (r : Nat) :
    ExecEVEX.merge s e l d 0 z r = r := rfl

/-! ## The EVEX zero-upper rule -/

/-- An EVEX write at `l ≤ 256` bits zeroes bits 511:256 of its destination, and at `l = 128` bits
255:128 too. -/
theorem setZ_upper (s : State) (l n v : Nat) (hl : l < 512) :
    (ExecEVEX.setZ s l n v).zmmHi n = 0 ∧ (l = 128 → (ExecEVEX.setZ s l n v).ymmHi n = 0) := by
  simp only [ExecEVEX.setZ]
  exact ⟨by simp [show l ≠ 512 by omega], fun h => by simp [h]⟩

set_option maxHeartbeats 4000000 in
/-- **The EVEX zero-upper rule.** If an AVX-512 instruction completes, every vector register it
writes at `l < 512` bits has bits 511:256 zero afterwards, and bits 255:128 zero for `l = 128`. -/
theorem evex_zero_upper (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat)
    (i : EvexI XLoc Loc Addr) (s' : State) (h : ExecEVEX.exec s next pc ea i = .ok s') :
    ∀ d l, (d, l) ∈ i.vdsts → l < 512 → s'.zmmHi d = 0 ∧ (l = 128 → s'.ymmHi d = 0) := by
  intro d l hd hl
  cases i <;> simp only [EvexI.vdsts, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hd
  all_goals
    first
    | (obtain ⟨rfl, rfl⟩ := hd)
    | (split at hd <;> simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hd <;>
        obtain ⟨rfl, rfl⟩ := hd)
    | skip
  all_goals
    simp only [ExecEVEX.exec, ExecEVEX.done, ExecEVEX.doneFP] at h
    (repeat' split at h) <;> (try cases h) <;>
      simp_all [ExecEVEX.setZ, ExecSSE.raiseMx] <;> omega

/-! ## VEX and legacy SSE on the AVX-512 state -/

/-- A VEX write zeroes bits 511:256 of its destination. -/
theorem setV_zmm (s : State) (l n v : Nat) : (ExecAVX.setV s l n v).zmmHi n = 0 := by
  simp [ExecAVX.setV]

set_option maxHeartbeats 4000000 in
/-- **VEX zeroes bits 511:256** of every register an AVX instruction writes. -/
theorem vex_zero_zmm (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat)
    (i : AvxI XLoc Loc Addr) (s' : State) (h : ExecAVX.exec s next pc ea i = .ok s') :
    ∀ d l, (d, l) ∈ i.vdsts → s'.zmmHi d = 0 := by
  cases i <;> simp only [ExecAVX.exec, ExecAVX.doneV, ExecAVX.doneFPV, ExecAVX.doneS,
    ExecAVX.maskmovExec, ExecAVX.gatherExec] at h <;>
    (repeat' split at h) <;> (try cases h) <;> intro d l hd <;>
    simp only [AvxI.vdsts, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hd <;>
    (try obtain ⟨rfl, hl⟩ := hd) <;> (try rcases hd with ⟨rfl, hl⟩ | ⟨rfl, hl⟩) <;>
    simp_all [ExecAVX.setV, ExecSSE.raiseMx]

set_option maxHeartbeats 4000000 in
/-- No AVX instruction of WP-F touches the opmask registers. -/
theorem avx_preserves_kreg (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat)
    (i : AvxI XLoc Loc Addr) (s' : State) (h : ExecAVX.exec s next pc ea i = .ok s') :
    s'.kreg = s.kreg := by
  cases i <;> simp only [ExecAVX.exec, ExecAVX.doneV, ExecAVX.doneFPV, ExecAVX.doneS,
    ExecAVX.maskmovExec, ExecAVX.gatherExec] at h <;>
    (repeat' split at h) <;> (try cases h) <;> rfl

/-- **Legacy SSE preserves the AVX-512 state**: no WP-D instruction changes bits 511:256 of any
`ZMM` register or any opmask register. -/
theorem sse_preserves_avx512 (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat)
    (i : SseI XLoc Loc Addr) (s' : State) (h : ExecSSE.exec s next pc ea i = .ok s') :
    s'.zmmHi = s.zmmHi ∧ s'.kreg = s.kreg := by
  cases i <;> simp only [ExecSSE.exec, ExecSSE.doneX, ExecSSE.doneFP] at h <;>
    (repeat' split at h) <;> (try cases h) <;> exact ⟨rfl, rfl⟩

/-! ## The earlier semantics are unchanged -/

set_option maxHeartbeats 8000000 in
/-- **WP-D is unchanged**: a legacy-SSE instruction's result, AVX-512 state erased, is the result
from the state with its AVX-512 state erased. -/
theorem sse_compat (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : SseI XLoc Loc Addr) :
    (ExecSSE.exec s next pc ea i).map State.strip512 =
      (ExecSSE.exec s.strip512 next pc ea i).map State.strip512 := by
  cases i <;> simp only [ExecSSE.exec, ExecSSE.doneX, ExecSSE.doneFP, ExecSSE.readN, ExecSSE.readG,
      State.strip512] <;> (repeat' split) <;> (try simp only [*, reduceIte, Bool.false_eq_true]) <;>
    first | rfl | contradiction | simp_all

set_option maxHeartbeats 8000000 in
/-- **WP-F is unchanged**: an AVX instruction's result, AVX-512 state erased, is the result from
the state with its AVX-512 state erased. -/
theorem avx_compat (s : State) (next : W64) (pc : Nat) (ea : Addr → Nat) (i : AvxI XLoc Loc Addr) :
    (ExecAVX.exec s next pc ea i).map State.strip512 =
      (ExecAVX.exec s.strip512 next pc ea i).map State.strip512 := by
  cases i <;> simp only [ExecAVX.exec, ExecAVX.doneV, ExecAVX.doneFPV, ExecAVX.doneS,
    ExecAVX.maskmovExec, ExecAVX.gatherExec, ExecAVX.rd, ExecAVX.getV, ExecSSE.readG, State.ymm,
    State.strip512] <;> (repeat' split) <;> (try simp only [*, reduceIte, Bool.false_eq_true]) <;>
    first | rfl | contradiction | simp_all

/-! ## At the `Instr` level -/

/-- `exec` of an AVX-512 instruction is `ExecEVEX.exec`. -/
theorem exec_evex (i : EvexI XLoc Loc Addr) (len : Nat) (s : State) :
    exec (.evex i) len s = ExecEVEX.exec s (BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64)) s.rip.toNat
      (fun a => (ea s (BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64)) a).toNat) i := rfl

/-- **The EVEX zero-upper rule**, for a decoded AVX-512 instruction. -/
theorem exec_evex_zero_upper (i : EvexI XLoc Loc Addr) (len : Nat) (s s' : State)
    (h : exec (.evex i) len s = .ok s') :
    ∀ d l, (d, l) ∈ i.vdsts → l < 512 → s'.zmmHi d = 0 ∧ (l = 128 → s'.ymmHi d = 0) :=
  evex_zero_upper s _ _ _ i s' (by rw [exec_evex] at h; exact h)

/-- **VEX zeroes bits 511:256**, for a decoded AVX instruction. -/
theorem exec_avx_zero_zmm (i : AvxI XLoc Loc Addr) (len : Nat) (s s' : State)
    (h : exec (.avx i) len s = .ok s') : ∀ d l, (d, l) ∈ i.vdsts → s'.zmmHi d = 0 :=
  vex_zero_zmm s _ _ _ i s' (by rw [exec_avx] at h; exact h)

/-- **Legacy SSE preserves the AVX-512 state**, for a decoded WP-D instruction. -/
theorem exec_sse_preserves_avx512 (i : SseI XLoc Loc Addr) (len : Nat) (s s' : State)
    (h : exec (.sse i) len s = .ok s') : s'.zmmHi = s.zmmHi ∧ s'.kreg = s.kreg :=
  sse_preserves_avx512 s _ _ _ i s' (by rw [exec_sse] at h; exact h)

end Janus.Amd64.Tactic
