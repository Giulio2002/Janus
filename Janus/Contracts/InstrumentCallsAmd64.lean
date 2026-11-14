import Janus.Contracts.InstrumentCalls
import Janus.Contracts.MapAmd64

/-!
# Instrumented builds: the `-d=checkptr` runtime checks, and the cgo pointer checks (amd64)

The amd64 versions of `Janus.Contracts.InstrumentCalls` (whose module documentation explains the
contracts): the same conditions (`AlignOK`, `ArithOK`, the model `CheckptrModel`), with the Go
ABIInternal of amd64 (arguments in `RAX, RBX, RCX, RDI`, `g` in `R14`, the return address at
`[RSP]`; `RTPre64`, `RTReturn64`, `CallerOK64` as for the interface contracts).
-/

namespace Janus.Contracts.Instrument

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts

/-- What a runtime call with `nargs` register arguments needs (amd64). -/
def RTPre64 (E : RtEnv) (nargs : Nat) (s : State) : Prop :=
  E.Env s.mem (s.regs 14) ∧ StackGuardOK s E.depth ∧ (s.regs 4).toNat % 8 = 0 ∧
    E.depth ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 + 8 * nargs ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - E.depth) (E.depth + 8 + 8 * nargs) true = true ∧
    s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    Outside ((s.regs 4).toNat - E.depth) (E.depth + 8 + 8 * nargs) E.priv

/-- What a caller needs to call the runtime (amd64). -/
def CallerOK64 (E : RtEnv) (s : State) (frame above : Nat) : Prop :=
  E.Env s.mem (s.regs 14) ∧ StackGuardOK s (E.depth + frame) ∧ (s.regs 4).toNat % 8 = 0 ∧
    E.depth + frame ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + above ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - (E.depth + frame)) (E.depth + frame + above) true = true ∧
    Outside ((s.regs 4).toNat - (E.depth + frame)) (E.depth + frame + above) E.priv ∧
    Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - (E.depth + frame))
      (E.depth + frame + above) ∧
    Outside ((s.regs 14).toNat + 16) 8 E.priv

theorem RTPre64.of_parts {E : RtEnv} {s S : State} {frame above nargs : Nat}
    (hc : CallerOK64 E s frame above) (henv : E.Env S.mem (s.regs 14))
    (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
    (hguard : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : RTPre64 E nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, -⟩ := hc
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

/-- `RTPre64.of_parts` for a first call. -/
theorem RTPre64.of_caller {E : RtEnv} (hl : E.Laws) {s S : State}
    {frame above nargs : Nat} (hc : CallerOK64 E s frame above)
    (hf : MemFrame s.mem S.mem [((s.regs 4).toNat - (E.depth + frame), (s.regs 4).toNat + above)])
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame + above) : RTPre64 E nargs S := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, -, -⟩, -, -, -, -, hout, hgd, -⟩ := hc'
  simp only [regG, stackguard0Offset, Spec.Disjoint] at hg1 hgd
  refine RTPre64.of_parts hc (hl.env_frame _ _ _ henv
    (Agrees.of_window hf (Outside.of_sub hout (by omega) (by omega)))) hf.accessible
    (hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)) hsp hg hx hdf hra hfr hn

/-- The ranges a runtime call may write at call state `s` (amd64). -/
def rtWrites64 (E : RtEnv) (s : State) (nargs : Nat) : List (Nat × Nat) :=
  E.priv ++ MapAmd64.calleeStack s E.depth nargs

attribute [janus64_exec, janus64_post] rtWrites64

/-- The return of a runtime call from `s` to `s'` (amd64). -/
def RTReturn64 (E : RtEnv) (nargs : Nat) (s s' : State) (P : (Nat → W64) → Janus.Arm64.Memory → Prop) : Prop :=
  ∃ r x y fl m zh kr, s' = { s with regs := MapAmd64.keepABI s.regs r, xmm := MapAmd64.keepX15 s.xmm x,
                                    ymmHi := y, flags := fl, mem := m, rip := retAddrOf s, zmmHi := zh, kreg := kr } ∧
    MemFrame s.mem m (rtWrites64 E s nargs) ∧ E.Env m (s.regs 14) ∧ P r m

/-- A model implementation's return as `RTReturn64`. -/
theorem RTReturn64.intro (E : RtEnv) (nargs : Nat) (s s' : State)
    (P : (Nat → W64) → Janus.Arm64.Memory → Prop) (hrip : s'.rip = retAddrOf s)
    (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hmx : s'.mxcsr = s.mxcsr) (hfr : MemFrame s.mem s'.mem (rtWrites64 E s nargs))
    (henv : E.Env s'.mem (s.regs 14)) (hp : P s'.regs s'.mem)
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) : RTReturn64 E nargs s s' P := by
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, s'.zmmHi, s'.kreg, ?_, hfr, henv, hp⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx, x8, fw⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx hx87 hfw ⊢
  subst hrip hfs hdf hmx hx87 hfw
  congr
  · funext i
    simp only [MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-- **`runtime.checkptrAlignment(p, elem, n)`** (amd64; `RAX = p`, `RBX = elem`, `RCX = n`). -/
def CheckptrAlignment64 (p : Janus.Amd64.Program) (addr : Nat) (C : CheckptrModel) : Prop :=
  Summary p addr
    (fun s => RTPre64 C.toRtEnv 3 s ∧
      AlignOK C s.mem (s.regs 14) (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat)
    (fun s s' => RTReturn64 C.toRtEnv 3 s s' fun _ _ => True)

/-- **`runtime.checkptrArithmetic(p, originals)`** (amd64; `RAX = p`, `RBX, RCX, RDI` the slice). -/
def CheckptrArithmetic64 (p : Janus.Amd64.Program) (addr : Nat) (C : CheckptrModel) : Prop :=
  Summary p addr
    (fun s => RTPre64 C.toRtEnv 4 s ∧
      ArithOK C s.mem (s.regs 14) (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat)
    (fun s s' => RTReturn64 C.toRtEnv 4 s s' fun _ _ => True)

/-- **`runtime.cgoCheckPointer(ptr, arg any)`** (amd64; `RAX, RBX = ptr`, `RCX, RDI = arg`). -/
def CgoCheckPointer64 (p : Janus.Amd64.Program) (addr : Nat) (C : CgoCheckModel) : Prop :=
  Summary p addr
    (fun s => RTPre64 C.toRtEnv 4 s ∧
      C.ok s.mem (s.regs 14) (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat (s.regs 7).toNat)
    (fun s s' => RTReturn64 C.toRtEnv 4 s s' fun _ _ => True)

/-- **`runtime.cgoCheckResult(val any)`** (amd64; `RAX, RBX = val`). -/
def CgoCheckResult64 (p : Janus.Amd64.Program) (addr : Nat) (C : CgoCheckModel) : Prop :=
  Summary p addr
    (fun s => RTPre64 C.toRtEnv 2 s ∧ C.resOK s.mem (s.regs 14) (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => RTReturn64 C.toRtEnv 2 s s' fun _ _ => True)

end Janus.Contracts.Instrument
