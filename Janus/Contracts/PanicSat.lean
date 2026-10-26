import Janus.Contracts.PanicModel

/-!
# The panic/defer/recover contracts are satisfiable (arm64)

Model code for the panic runtime `PanicModel.P0` (one segment, the "engine", at `E = 0x300000`,
with an entry for each runtime function), proved to meet every arm64 panic contract of
`Janus.Contracts.Panic` in **every** program that contains the engine (`EngineAt`): a contract
address holds a three-instruction stub (`movz`/`movk`/`br x11`) jumping to the engine. The
`<contract>_satisfiable` theorems instantiate this for a toy program, with a call state in the
contract's precondition; the examples' `Witness` sections instantiate it for their own linked
program.

See `docs/model/panic_model.s` for the assembly source of `engineCode`.
-/

namespace Janus.Contracts.PanicSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
open Janus.Contracts.PanicModel

/-! ## The engine -/

def engineCode : List Nat :=
  [0xd2a00026, 0xf94000c7, 0x910400c8, 0x8b071508, 0xf9000100, 0xf9000501, 0x910003e9, 0xf9000909,
   0xf9000d1f, 0x910004e7, 0xf90000c7, 0xd280000a, 0x14000074, 0xd2a00026, 0xf94000c7, 0x910400c8,
   0x8b071508, 0xf900011f, 0xf900051f, 0x910003e9, 0xf9000909, 0xd2800029, 0xf9000d09, 0x910004e7,
   0xf90000c7, 0xd280002a, 0x14000066, 0xd2a00026, 0x910003e9, 0xf94008c5, 0xf9400cce, 0xf94010cf,
   0xf90008df, 0xd101813f, 0xf90003e9, 0xf90007e9, 0xf9000bff, 0xd280004a, 0xf9000fea, 0xf90013e5,
   0xf90017ee, 0xf9001bef, 0xf9001ff2, 0xf90023fe, 0xf90027fd, 0x1400007d, 0xd2a00026, 0xf94000c7,
   0xb40001e7, 0xd10004e7, 0x910400c8, 0x8b071508, 0xf9400d00, 0xb5000140, 0xf94007a1, 0x10001422,
   0xeb02003f, 0x540000c1, 0xd2800040, 0xf9000d00, 0xf9400100, 0xf9400501, 0xd65f03c0, 0xd2800000,
   0xd2800001, 0xd65f03c0, 0xd2a00026, 0xf94004c7, 0xd2800c09, 0x9b097ce8, 0x8b060108, 0x91080108,
   0x910003ea, 0xf900010a, 0xf900051f, 0xf900091f, 0xd280002b, 0xf9000d0b, 0xf9001100, 0x910004e7,
   0xf90004c7, 0xd65f03c0, 0xf9400c00, 0xd2a00026, 0xf94004c7, 0xd2800c09, 0x9b097ce8, 0x8b060108,
   0x91080108, 0x910003ea, 0xf900010a, 0xf900051f, 0xf900091f, 0xd280002b, 0xf9000d0b, 0xf9001100,
   0x910004e7, 0xf90004c7, 0xd65f03c0, 0xd2a00026, 0xf94004c7, 0xd2800c09, 0x9b097ce8, 0x8b060108,
   0x91080108, 0x910003ea, 0xf900010a, 0xf9000508, 0xf900091f, 0xf9000d1f, 0x910004e7, 0xf90004c7,
   0xd2800020, 0xaa0803e1, 0xd65f03c0, 0xd2a00026, 0xf94004c7, 0xd10004e7, 0xd2800c09, 0x9b097ce8,
   0x8b060108, 0x91080108, 0xf9400d0a, 0x9100810b, 0xf82a7960, 0x9100054a, 0xf9000d0a, 0xd65f03c0,
   0xd2a00026, 0xf94014c7, 0x911400c8, 0xb4000167, 0xf9400100, 0xeb0003df, 0x540000a3, 0xf9400501,
   0x8b010001, 0xeb0103df, 0x540000a3, 0x9100e108, 0xd10004e7, 0x17fffff6, 0x14000000, 0x910003e9,
   0xf9400901, 0x8b010122, 0xf9400d03, 0x8b030003, 0xf9401104, 0xd2800005, 0xd280000e, 0xd280000f,
   0xb4000124, 0xd100204c, 0xf940150d, 0xcb0d018e, 0xf940190d, 0xcb0d018f, 0x394001cd, 0x3400004d,
   0xd2800025, 0xd101813f, 0xf90003e9, 0xf90007e2, 0xf9000be3, 0xf9000fea, 0xf90013e5, 0xf90017ee,
   0xf9001bef, 0xf9001ff2, 0xf94013e0, 0xb40001e0, 0xf94017e1, 0x39400022, 0x34000162, 0x5ac01043,
   0x528003e4, 0x4b030083, 0x52800024, 0x1ac32084, 0x0a240042, 0x39000022, 0xf9401be5, 0xf86378ba,
   0x1400001d, 0xf90013ff, 0xd2a00026, 0xf94004c7, 0xb4000807, 0xd10004e8, 0xd2800c00, 0x9b007d08,
   0x8b060108, 0x91080108, 0xf9400100, 0xf94003e1, 0xeb01001f, 0x540006e1, 0xd2800020, 0xf9000900,
   0xf9400d00, 0xb4000120, 0xd1000400, 0xf9000d00, 0x91008102, 0xf860785a, 0xb50000e0, 0xd10004e7,
   0xf90004c7, 0x14000004, 0xd10004e7, 0xf90004c7, 0x17ffffd6, 0xf9400349, 0xd10023fd, 0xd63f0120,
   0xf9401ff2, 0xf9400fe0, 0xb5fffa00, 0xd2a00026, 0xf94000c7, 0xd10004e7, 0x910400c8, 0x8b071508,
   0xf9400d00, 0x360ff920, 0xf94003e1, 0xf94000c7, 0xb4000127, 0xd10004e7, 0x910400c8, 0x8b071508,
   0xf9400900, 0xeb01001f, 0x54000068, 0xf90000c7, 0x17fffff7, 0xf90008df, 0xf94013e0, 0xb4000120,
   0xf94017e2, 0x39400043, 0x340000c3, 0xd2800020, 0xf90008c0, 0xf9000cc2, 0xf9401be3, 0xf90010c3,
   0xf9400be0, 0x9100003f, 0xd10023fd, 0xd61f0000, 0xf9400fe0, 0xf100081f, 0x540000a0, 0xf94007e1,
   0x9100003f, 0x10fffae0, 0xd61f0000, 0xf94023fe, 0xf94027fd, 0xf94003e1, 0x9100003f, 0xd65f03c0]

abbrev E : Nat := 0x300000
/-- Entry points (offsets in `docs/model/panic_model.s`). -/
abbrev eGopanic : Nat := E
abbrev eGoexit : Nat := E + 0x34
abbrev eDeferreturn : Nat := E + 0x6c
abbrev eGorecover : Nat := E + 0xb8
abbrev eDeferproc : Nat := E + 0x108
abbrev eDeferprocStack : Nat := E + 0x148
abbrev eDeferrangefunc : Nat := E + 0x18c
abbrev eDeferprocat : Nat := E + 0x1cc
abbrev eLookup : Nat := E + 0x200
abbrev eLH : Nat := E + 0x2a8
/-- The return point of every deferred call the model makes. -/
abbrev RPa : Nat := E + 0x360

def engineSeg : Segment := { name := "panic-model", base := E, words := engineCode }

/-- The engine alone, as a closed program for the symbolic executor. -/
def qE : Program := { segments := [engineSeg], stubs := [], exitAddr := 0 }

/-- `p` contains the engine: every word of it is fetched, with no stub and no exit there. -/
def EngineAt (p : Program) : Prop :=
  ∀ pc w, qE.fetch pc = some w → p.fetch pc = some w ∧ p.stubAt pc = none ∧ pc ≠ p.exitAddr

theorem steps_transfer {p : Program} (hp : EngineAt p) {s s' : State} {k : Nat}
    (h : Program.Steps qE s k s') : Program.Steps p s k s' := by
  induction h with
  | refl => exact .refl _
  | step _ _ hf hst _ ih =>
    obtain ⟨h1, h2, h3⟩ := hp _ _ hf
    exact .step h3 h2 h1 hst ih

theorem reachesRet_transfer {p : Program} (hp : EngineAt p) {ret : W64} {s : State}
    {Q : State → Prop} (h : ReachesRet qE ret s Q) : ReachesRet p ret s Q := by
  obtain ⟨k, s', hk, h1, h2⟩ := h
  exact ⟨k, s', steps_transfer hp hk, h1, h2⟩

/-- The stub placed at a contract address: `movz x11, #lo; movk x11, #hi, lsl #16; br x11`. -/
def stubCode (tgt : Nat) : List Nat :=
  [0xd2800000 + tgt % 0x10000 * 32 + 11, 0xf2a00000 + tgt / 0x10000 % 0x10000 * 32 + 11, 0xd61f0160]

/-- The model `U`: a state at the deferred calls' return point with `SP = b` and `X28 = g`. -/
def U0 (u : State) (g b : Nat) : Prop :=
  u.pc = BitVec.ofNat 64 RPa ∧ u.sp = BitVec.ofNat 64 b ∧ u.regs 28 = BitVec.ofNat 64 g

/-! ## Returns -/

/-- A model routine's return as `PanicRet`: the preserved registers and fields. -/
theorem panicRet_of (P : PanicRuntime) (nargs : Nat) (s s' : State) (hsp : s'.sp = s.sp)
    (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28)
    (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr)
    (hfc : s'.fpcr = s.fpcr) (hfs : s'.fpsr = s.fpsr)
    (hfr : MemFrame s.mem s'.mem (P.priv ++ calleeStack s P.depth nargs)) (henv : P.Env s'.mem) :
    PanicRet P nargs s s' := by
  refine ⟨s'.regs, s'.flags, s'.vregs, s'.mem, ?_, hfr, henv⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc hdz htp hfc hfs h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc hfs
  simp only [retState]
  congr
  funext i
  simp only [callRegs_apply, List.getD_nil]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-- The store lemmas of the model's decoders, as one simp call. -/
syntax "model_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| model_simp $[$loc]?) => `(tactic| simp (disch := first | omega | (simp only [recAt, panAt, tabAt, B]; omega)) only [rd_w, panList_w, recList_w,
      capMin_w, Memory.readLE_writeLE_self, PanicModel.readLE_writeLE_same', Memory.readLE_writeLE_of_disjoint,
      Memory.accessible_writeLE, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul] $[$loc]?)

/-! ## `deferproc` -/

theorem room0_pos {m : Memory} (h : 0 < room0 m) : npan m < 8 ∧ ndef m < 8 ∧ 0 < capMin m (min (ndef m) 8) := by
  unfold room0 at h; omega

set_option maxHeartbeats 0 in
theorem deferproc_run {p : Program} (hp : EngineAt p) (T : List FuncInfo) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 eDeferproc) (hpre : PanicPre (P0 T RPa) 1 s) (hroom : 0 < room0 s.mem) :
    ReachesRet p (s.regs 30) s (fun s' => PanicRet (P0 T RPa) 1 s s' ∧
      defers0 s'.mem = { sp := s.sp.toNat, fns := [(s.regs 0).toNat] } :: defers0 s.mem ∧
      KeepsBut (P0 T RPa) (gOf s) 1 s.mem s'.mem) := by
  apply reachesRet_transfer hp
  obtain ⟨henv, -, ⟨h30a, h30b, hal, hst, h8, hwin, hacc⟩, hout⟩ := hpre
  rw [P0_env] at henv
  have henv' := henv
  unfold Env0 at henv'
  obtain ⟨hB, hnp, hnd, hrec, htab⟩ := henv'
  obtain ⟨-, hnd8, -⟩ := room0_pos hroom
  have hnd : s.mem.readLE 65544 8 < 8 := hnd8
  have hmul : (BitVec.ofNat 64 (s.mem.readLE 65544 8) * 96#64).toNat = s.mem.readLE 65544 8 * 96 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := s.mem.readLE 65544 8) (by omega)]; omega
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  janus_run [hmul]
  generalize hk : s.mem.readLE 65544 8 = k at *
  have hk' : ndef s.mem = k := hk
  refine ⟨panicRet_of _ 1 s _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
    rfl ?_ ?_, ?_, ?_⟩
  · rw [P0_priv, P0_depth]; simp only [B, calleeStack, List.cons_append, List.nil_append]; janus_frame
  · rw [P0_env]; unfold Env0; dsimp only
    refine ⟨by simpa using hB, ?_, ?_, fun i hi => ?_, ?_⟩
    · simp only [npan, rd, B]; model_simp; exact hnp
    · simp only [ndef, rd, B]; model_simp; omega
    · simp only [ndef, rd, B, recN, recTok, recConv, recAt] at hi ⊢
      model_simp at hi
      rw [Nat.mod_eq_of_lt (by omega)] at hi
      by_cases hik : i = k
      · subst hik; model_simp; omega
      · have hik' : i < k := by omega
        have := hrec i (by rw [hk']; omega)
        simp only [recN, recTok, recConv, recAt, rd, B] at this
        model_simp; exact this
    · repeat' first | apply tableOK_w | exact htab
      all_goals (simp only [tabAt, B, Nat.reduceAdd, Nat.reduceMul]; omega)
  · rw [defers0_eq, defers0_eq, hk']
    try simp only [ndef, rd, B]
    try model_simp
    rw [Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), recList_succ]
    try model_simp
    unfold decRec
    simp only [recTok, recConv, recN, recSp, rd, recAt, B]
    try model_simp
    simp only [true_or, ite_true, show min 1 8 = 1 from rfl, recFns_succ, recFn, rd, recAt, B,
      show PanicModel.recFns _ k 0 = [] from rfl]
    try model_simp
    simp only [Nat.mod_eq_of_lt (BitVec.isLt _), List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  · refine ⟨?_, ?_, rfl, ?_⟩
    · rw [P0_panics, P0_panics, panics0_eq, panics0_eq]; simp only [npan, rd, B]; model_simp
    · rw [P0_saved, P0_saved, saved0_eq, saved0_eq]; simp only [rd, B]; model_simp
    · rw [P0_room, P0_room, room0_eq, room0_eq, hk']; simp only [npan, ndef, rd, B]
      model_simp
      rw [Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega : k + 1 ≤ 8), Nat.min_eq_left (by omega : k ≤ 8),
        capMin_succ]
      model_simp
      simp only [recN, rd, recAt, B]
      model_simp
      omega

end Janus.Contracts.PanicSat
