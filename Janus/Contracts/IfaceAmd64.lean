import Janus.Contracts.Iface
import Janus.Contracts.MapAmd64

/-!
# Contracts of the Go interface runtime (amd64)

The amd64 counterparts of `Janus.Contracts.Iface` (see that file and docs/RUNTIME-CONTRACTS.md,
"Interfaces"): the same runtime entry points and the same results over the same model
`R : IfaceModel` (`Janus.Spec.Type`), stated with the amd64 ABIInternal. Arguments are in `RAX`,
`RBX`, `RCX` (`regs 0`, `regs 3`, `regs 1`), results in `RAX` and `RBX`; `CALL` pushes the
return address, so the callee starts with `[RSP]` holding it and returns to it with `RSP + 8`;
`RBP`, `R14` (`g`) and `X15` (zero) are preserved, every other general register, `X0`–`X14`, the
upper `YMM` halves and the flags are arbitrary afterwards. A call may write the runtime's memory,
at most `R.depth` bytes below `RSP` (never the return-address slot), the argument spill slots
`[RSP + 8, RSP + 8 + 8·nargs)` and (`typeAssert`, `interfaceSwitch`) the descriptor's `Cache`
word.

The ISA-independent parts (`BoxCopy`, `BoxWords`, `BoxHolds`, `ItabResult`, `efaceEqual`,
`ifaceEqual`, `EqOK`, `EqFrame`) are those of `Janus.Contracts.Iface`.
-/

namespace Janus.Contracts.IfaceAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts.Iface

/-! ## The common shape -/

/-- What every interface runtime call with `nargs` register arguments needs (amd64): the runtime
environment (with the goroutine in `R14`), the stack guard at least `R.depth` bytes below `RSP`,
an 8-aligned `RSP`, the window `[RSP - R.depth, RSP + 8 + 8·nargs)` writable, below `2^48` and
outside the runtime's memory, `X15 = 0`, the direction flag clear, and a canonical return
address (below `2^47`) at `[RSP]`. -/
def RTPre (R : IfaceModel) (nargs : Nat) (s : State) : Prop :=
  R.Env s.mem (s.regs 14) ∧ StackGuardOK s R.depth ∧ (s.regs 4).toNat % 8 = 0 ∧
    R.depth ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 + 8 * nargs ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - R.depth) (R.depth + 8 + 8 * nargs) true = true ∧
    s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    Outside ((s.regs 4).toNat - R.depth) (R.depth + 8 + 8 * nargs) R.priv

/-- What a caller needs to call the interface runtime (amd64), as `MapAmd64.CallerOK`. -/
def CallerOK (R : IfaceModel) (s : State) (frame above : Nat) : Prop :=
  R.Env s.mem (s.regs 14) ∧ StackGuardOK s (R.depth + frame) ∧ (s.regs 4).toNat % 8 = 0 ∧
    R.depth + frame ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - (R.depth + frame)) (R.depth + frame + above) true = true ∧
    Outside ((s.regs 4).toNat - (R.depth + frame)) (R.depth + frame + above) R.priv ∧
    Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - (R.depth + frame))
      (R.depth + frame + above) ∧
    Outside ((s.regs 14).toNat + 16) 8 R.priv

/-- `RTPre` at a call site `S` from the caller's `CallerOK` at its entry `s` (amd64). -/
theorem RTPre.of_parts {R : IfaceModel} {s S : State} {frame above nargs : Nat}
    (hc : CallerOK R s frame above) (henv : R.Env S.mem (s.regs 14))
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (hguard : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : RTPre R nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, -, -⟩ := hc
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  refine ⟨by rw [hg]; exact henv, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hx, hdf, hra, ?_⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hacc]; exact hg2
  · simp only [stackguard0, regG, regSP, stackguard0Offset, hg, hguard, hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hacc]; exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
  · rw [hsp]; exact Outside.of_sub hout (by omega) (by omega)

/-- `RTPre.of_parts` for a first call: the call state's memory differs from the caller's entry
memory only inside the caller's window. -/
theorem RTPre.of_caller {R : IfaceModel} (hl : R.Laws) {s S : State}
    {frame above nargs : Nat} (hc : CallerOK R s frame above)
    (hf : MemFrame s.mem S.mem [((s.regs 4).toNat - (R.depth + frame), (s.regs 4).toNat + above)])
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : RTPre R nargs S := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, -, -⟩, -, -, -, -, hout, hgd, -⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine RTPre.of_parts hc (hl.env_frame _ _ _ henv
    (Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega)))) hf.accessible
    (hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)) hsp hg hx hdf hra hfr hn

/-- The ranges an interface runtime call may write at call state `s` (amd64). -/
def rtWrites (R : IfaceModel) (s : State) (nargs : Nat) : List (Nat × Nat) :=
  R.priv ++ MapAmd64.calleeStack s R.depth nargs

attribute [janus64_exec, janus64_post] rtWrites

/-- The return of an interface runtime call from `s` to `s'` (amd64), with the call-specific
facts `P r m` about the result registers `r` and the new memory `m`. -/
def RTReturn (R : IfaceModel) (nargs : Nat) (extra : List (Nat × Nat)) (s s' : State)
    (P : (Nat → W64) → Janus.Arm64.Memory → Prop) : Prop :=
  ∃ r x y fl m zh kr,
    s' = { s with regs := MapAmd64.keepABI s.regs r, xmm := MapAmd64.keepX15 s.xmm x,
                  ymmHi := y, flags := fl, mem := m, rip := retAddrOf s, zmmHi := zh, kreg := kr } ∧
    MemFrame s.mem m (rtWrites R s nargs ++ extra) ∧ R.Env m (s.regs 14) ∧ P r m

/-- `SETcc r8` into the low byte of a register, read back as the low byte. -/
@[janus64_exec, janus64_post] theorem setcc_low_byte (a : BitVec 64) (b : BitVec 8) :
    ((a &&& 18446744073709551360#64) ||| BitVec.setWidth 64 b).toNat % 256 = b.toNat := by
  have h : ((a &&& 18446744073709551360#64) ||| BitVec.setWidth 64 b).setWidth 8 = b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hm : (18446744073709551360#64).getLsbD i = false := by
      rw [show (18446744073709551360#64) = BitVec.ofNat 64 (2 ^ 64 - 2 ^ 8) from rfl,
        BitVec.getLsbD_ofNat, testBit_two_pow_sub_two_pow 8 i (by decide)]
      simp; omega
    simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, hm, hi,
      show i < 64 by omega]
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth] at this
  exact this

/-! ## Boxing (`RAX = regs 0`, `RBX = regs 3`, `RCX = regs 1`) -/

/-- **`runtime.convT(t, v)`** (`RAX = t`, `RBX = v`): as `Iface.ConvT`. -/
def ConvT (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (H : RtReady) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ R.IsType (s.regs 0).toNat ∧
      (s.regs 3).toNat + tySize s.mem (s.regs 0).toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 3).toNat (tySize s.mem (s.regs 0).toNat) false = true ∧
      Ready64 H R.priv [(s.regs 0).toNat, (s.regs 3).toNat] s)
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      BoxCopy R s.mem m (r 0).toNat (s.regs 3).toNat (tySize s.mem (s.regs 0).toNat))

/-- **`runtime.convTnoptr(t, v)`**: as `Iface.ConvTnoptr`. -/
def ConvTnoptr (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (H : RtReady) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ R.IsType (s.regs 0).toNat ∧ tyPtrBytes s.mem (s.regs 0).toNat = 0 ∧
      (s.regs 3).toNat + tySize s.mem (s.regs 0).toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 3).toNat (tySize s.mem (s.regs 0).toNat) false = true ∧
      Ready64 H R.priv [(s.regs 0).toNat, (s.regs 3).toNat] s)
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      BoxCopy R s.mem m (r 0).toNat (s.regs 3).toNat (tySize s.mem (s.regs 0).toNat))

/-- **`runtime.convT16(v)`** (`RAX = v`): as `Iface.ConvT16`. -/
def ConvT16 (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (H : RtReady) : Prop :=
  Summary p addr (fun s => RTPre R 1 s ∧ Ready64 H R.priv [(s.regs 0).toNat] s)
    (fun s s' => RTReturn R 1 [] s s' fun r m => BoxHolds R m (r 0).toNat 2 ((s.regs 0).toNat % 2 ^ 16))

/-- **`runtime.convT32(v)`**: as `Iface.ConvT32`. -/
def ConvT32 (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (H : RtReady) : Prop :=
  Summary p addr (fun s => RTPre R 1 s ∧ Ready64 H R.priv [(s.regs 0).toNat] s)
    (fun s s' => RTReturn R 1 [] s s' fun r m => BoxHolds R m (r 0).toNat 4 ((s.regs 0).toNat % 2 ^ 32))

/-- **`runtime.convT64(v)`**: as `Iface.ConvT64`. -/
def ConvT64 (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (H : RtReady) : Prop :=
  Summary p addr (fun s => RTPre R 1 s ∧ Ready64 H R.priv [(s.regs 0).toNat] s)
    (fun s s' => RTReturn R 1 [] s s' fun r m => BoxHolds R m (r 0).toNat 8 (s.regs 0).toNat)

/-- **`runtime.convTstring(s)`** (`RAX = ptr`, `RBX = len`): as `Iface.ConvTstring`. -/
def ConvTstring (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (H : RtReady) : Prop :=
  Summary p addr (fun s => RTPre R 2 s ∧ Ready64 H R.priv [(s.regs 0).toNat, (s.regs 3).toNat] s)
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      BoxWords R m (r 0).toNat
        [if (s.regs 3).toNat = 0 then 0 else (s.regs 0).toNat, (s.regs 3).toNat])

/-- **`runtime.convTslice(s)`** (`RAX = ptr`, `RBX = len`, `RCX = cap`): as `Iface.ConvTslice`. -/
def ConvTslice (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (H : RtReady) : Prop :=
  Summary p addr (fun s => RTPre R 3 s ∧ Ready64 H R.priv [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s)
    (fun s s' => RTReturn R 3 [] s s' fun r m =>
      BoxWords R m (r 0).toNat
        (if (s.regs 0).toNat = 0 then [0, 0, 0]
         else [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat]))

/-! ## Assertions and switches -/

/-- **`runtime.assertE2I(inter, t)`** (`RAX = inter`, `RBX = t`): as `Iface.AssertE2I`. -/
def AssertE2I (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ R.IsInter (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
      R.IsType (s.regs 3).toNat ∧ (R.itab (s.regs 0).toNat (s.regs 3).toNat).isSome)
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      ItabResult R m (s.regs 0).toNat (s.regs 3).toNat (r 0).toNat)

/-- **`runtime.assertE2I2(inter, t)`**: as `Iface.AssertE2I2`. -/
def AssertE2I2 (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ R.IsInter (s.regs 0).toNat ∧
      ((s.regs 3).toNat ≠ 0 → R.IsType (s.regs 3).toNat))
    (fun s s' => RTReturn R 2 [] s s' fun r m =>
      ItabResult R m (s.regs 0).toNat (s.regs 3).toNat (r 0).toNat)

/-- **`runtime.typeAssert(desc, t)`** (`RAX = desc`, `RBX = t`): as `Iface.TypeAssert`. -/
def TypeAssert (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (H : RtReady) : Prop :=
  Summary p addr
    (fun s => RTPre R 2 s ∧ TADescOK R s.mem (s.regs 0).toNat ∧
      (s.regs 3).toNat ≠ 0 ∧
      ((s.regs 3).toNat ≠ 0 → R.IsType (s.regs 3).toNat ∧
        (taCanFail s.mem (s.regs 0).toNat = true ∨
          (R.itab (taInter s.mem (s.regs 0).toNat) (s.regs 3).toNat).isSome)) ∧
      Ready64 H R.priv [(s.regs 0).toNat, (s.regs 3).toNat] s)
    (fun s s' => RTReturn R 2 [((s.regs 0).toNat, (s.regs 0).toNat + 8)] s s' fun r m =>
      ItabResult R m (taInter s.mem (s.regs 0).toNat) (s.regs 3).toNat (r 0).toNat ∧
      TADescOK R m (s.regs 0).toNat ∧ taInter m (s.regs 0).toNat = taInter s.mem (s.regs 0).toNat ∧
      taCanFail m (s.regs 0).toNat = taCanFail s.mem (s.regs 0).toNat)

/-- **`runtime.interfaceSwitch(desc, t)`** (`RAX = desc`, `RBX = t`; results `RAX = case`,
`RBX = itab`): as `Iface.InterfaceSwitch`. -/
def InterfaceSwitch (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) (H : RtReady) : Prop :=
  ∀ cs : List Nat, Summary p addr
    (fun s => RTPre R 2 s ∧ ISDescOK R s.mem (s.regs 0).toNat cs ∧ (s.regs 3).toNat ≠ 0 ∧
      R.IsType (s.regs 3).toNat ∧
      Ready64 H R.priv [(s.regs 0).toNat, (s.regs 3).toNat] s)
    (fun s s' => RTReturn R 2 [((s.regs 0).toNat, (s.regs 0).toNat + 8)] s s' fun r m =>
      (r 0).toNat = (switchCase R (s.regs 3).toNat cs).1 ∧
      (r 3).toNat = (switchCase R (s.regs 3).toNat cs).2 ∧
      ((r 3).toNat ≠ 0 → ItabAt R.priv m (r 3).toNat (cs.getD (r 0).toNat 0) (s.regs 3).toNat) ∧
      ISDescOK R m (s.regs 0).toNat cs)

/-! ## Comparison -/

/-- **`runtime.efaceeq(t, x, y)`** (`RAX = t`, `RBX`, `RCX`): `efaceEqual` in `AL`. -/
def Efaceeq (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 3 s ∧ EqOK R s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat)
    (fun s s' => RTReturn R 3 [] s s' fun r _ =>
      (r 0).toNat % 256 =
        (efaceEqual R s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat).toNat)

/-- **`runtime.ifaceeq(tab, x, y)`** (`RAX = tab`, `RBX`, `RCX`): `ifaceEqual` in `AL`. -/
def Ifaceeq (p : Janus.Amd64.Program) (addr : Nat) (R : IfaceModel) : Prop :=
  Summary p addr
    (fun s => RTPre R 3 s ∧ ((s.regs 0).toNat ≠ 0 →
      (s.regs 0).toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 16 false = true ∧
      (s.mem.readLE ((s.regs 0).toNat + 8) 8 ≠ 0) ∧
      EqOK R s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.regs 3).toNat (s.regs 1).toNat))
    (fun s s' => RTReturn R 3 [] s s' fun r _ =>
      (r 0).toNat % 256 =
        (ifaceEqual R s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat).toNat)

end Janus.Contracts.IfaceAmd64
