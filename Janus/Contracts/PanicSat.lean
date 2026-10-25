import Janus.Contracts.Panic
import Janus.Contracts.IfaceModel

/-!
# The panic/defer/recover contracts are satisfiable (arm64)

For every returning contract of `Janus.Contracts.Panic` (`DeferprocContract`, `DeferreturnContract`,
`GorecoverContract`, …): a model `P0` of the panic runtime whose laws hold (`P0_laws`), a tiny
implementation (a single `RET`) placed at an address `A0` of a program with no other code, a proof
that it meets the contract for `P0`, and a call state (`wstate`) that satisfies the contract's
precondition. So no contract is contradictory (`<contract>_satisfiable`). The model code just
returns; the contract only promises a return with the ABI preserved and memory confined to the
runtime, which a `RET` trivially satisfies.
-/

namespace Janus.Contracts.PanicSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

/-! ## The model -/

/-- A distinct non-zero type word for each runtime-error kind (so `P0.err` is injective with
non-nil type words). -/
def errTyp : ErrKind → Nat
  | .bounds => 0x10008 | .divide => 0x10010 | .shift => 0x10018 | .overflow => 0x10020
  | .float => 0x10028 | .mem => 0x10030 | .simdImm => 0x10038 | .dottype => 0x10040
  | .makeslice => 0x10048 | .unsafeOp => 0x10050 | .wrap => 0x10058 | .rangeState => 0x10060

/-- The model's panic record (in its private memory): type word `+0`, data word `+8`, the
deferred call's return point `+16`, the active flag `+24`, the recovered flag `+32`. -/
def PANREC : Nat := 0x10800

/-- The model of the panic runtime: one metadata range, stack depth 64, every runtime error a
distinct non-nil `error`, its panic record at `PANREC`, no wrappers. -/
def P0 : PanicRuntime where
  err k := ⟨errTyp k, 0⟩
  priv := [(0x10000, 0x11000)]
  depth := 64
  Env m := m.accessible 0x10000 0x1000 true = true
  Panicking m _ v rp := m.readLE (PANREC + 24) 8 = 1 ∧ m.readLE PANREC 8 = v.typ ∧
    m.readLE (PANREC + 8) 8 = v.data ∧ m.readLE (PANREC + 16) 8 = rp
  Calm m _ := m.readLE (PANREC + 24) 8 = 0
  Recovered m _ := m.readLE (PANREC + 32) 8 = 1
  wrapper _ := False

@[simp] theorem P0_priv : P0.priv = [(0x10000, 0x11000)] := rfl
@[simp] theorem P0_depth : P0.depth = 64 := rfl
@[simp] theorem P0_env (m : Memory) : P0.Env m = (m.accessible 0x10000 0x1000 true = true) := rfl

theorem P0_laws : P0.Laws where
  err_typ_ne k := by cases k <;> simp [P0, errTyp]
  err_inj k k' h := by
    have : (P0.err k).typ = (P0.err k').typ := by rw [h]
    cases k <;> cases k' <;> first | rfl | (simp only [P0, errTyp] at this; omega)
  depth_pos := by decide
  env_frame m m' h ha := by
    show m'.accessible 0x10000 0x1000 true = true
    rw [ha.1]; exact h
  panicking_frame m m' g v rp h ha := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hin : ∀ a, 0x10000 ≤ a → a + 8 ≤ 0x11000 → InRanges a 8 P0.priv :=
      fun a ha1 ha2 => ⟨(0x10000, 0x11000), by simp, ha1, ha2⟩
    exact ⟨(ha.readLE (hin _ (by simp [PANREC]) (by simp [PANREC]))).trans h1,
      (ha.readLE (hin _ (by simp [PANREC]) (by simp [PANREC]))).trans h2,
      (ha.readLE (hin _ (by simp [PANREC]) (by simp [PANREC]))).trans h3,
      (ha.readLE (hin _ (by simp [PANREC]) (by simp [PANREC]))).trans h4⟩
  calm_frame m m' g h ha := by
    show m'.readLE (PANREC + 24) 8 = 0
    rw [ha.readLE ⟨(0x10000, 0x11000), by simp, by simp [PANREC], by simp [PANREC]⟩]; exact h
  recovered_frame m m' g h ha := by
    show m'.readLE (PANREC + 32) 8 = 1
    rw [ha.readLE ⟨(0x10000, 0x11000), by simp, by simp [PANREC], by simp [PANREC]⟩]; exact h
  calm_not_panicking m g v rp h hp := by
    have h1 : m.readLE (PANREC + 24) 8 = 0 := h
    rw [hp.1] at h1; exact absurd h1 (by decide)

/-! ## The toy program and the model code (a single `RET`) -/

/-- A program with no code, stubs or data of its own. -/
def toy : Program := { segments := [], stubs := [], exitAddr := 0 }

/-- Where the model `RET` is placed. -/
def A0 : Nat := 0x100000

/-- The model implementation: `ret` at `A0`. -/
def retCode : List Nat := [0xd65f03c0]

def at0 (ws : List Nat) : List Segment := [{ name := "model", base := A0, words := ws }]
def withCode (ws : List Nat) : Program := { segments := at0 ws, stubs := [], exitAddr := 0 }
theorem link_at0 (ws : List Nat) : toy.link (at0 ws) = withCode ws := rfl

/-! ## The witness call state -/

def wg : Nat := 0x50000
def wsp : Nat := 0x48000
def wret : Nat := 0x200000

/-- The witness memory: the runtime metadata `[0x10000, 0x11000)` readable, a stack
`[0x40000, 0x50000)` writable, the goroutine `[0x50000, 0x50100)` readable (its `stackguard0`
at `+16` is `0`, far below `SP`). All bytes zero. -/
def wmem : Memory :=
  ⟨fun _ => 0,
    [⟨0x10000, 0x1000, true⟩, ⟨0x40000, 0x10000, true⟩, ⟨0x50000, 0x100, false⟩]⟩

/-- The witness call state: goroutine in `X28`, return address `wret` in `X30`, stack pointer
`wsp`, the rest zero. -/
def wstate : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret
      else if i = 29 then BitVec.ofNat 64 (wsp - 8) else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := wmem }

theorem wstate_pre (nargs : Nat) (hn : nargs ≤ 2) : PanicPre P0 nargs wstate := by
  have hsp : wstate.sp = BitVec.ofNat 64 wsp := rfl
  have hg28 : wstate.regs 28 = BitVec.ofNat 64 wg := rfl
  have h30 : wstate.regs 30 = BitVec.ofNat 64 wret := rfl
  have hm : wstate.mem = wmem := rfl
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show wstate.mem.accessible 0x10000 0x1000 true = true; rw [hm]; decide
  · simp only [regG, stackguard0Offset, hg28]; decide
  · simp only [regG, stackguard0Offset, hg28, hm]; decide
  · simp only [stackguard0, regG, stackguard0Offset, hg28, hm, hsp, P0_depth]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp, P0_depth]; decide
  · decide
  · simp only [hsp, P0_depth]; rw [BitVec.toNat_ofNat]; simp only [wsp]; omega
  · simp only [hsp, hm, P0_depth]
    refine Memory.accessible_mono _
      (show wmem.accessible (wsp - 64) (64 + 8 + 8 * 2) true = true by decide) ?_ ?_
    · rw [BitVec.toNat_ofNat]; simp [wsp]
    · rw [BitVec.toNat_ofNat]; simp only [wsp]; omega
  · simp only [hsp, P0_priv, P0_depth, outside_cons, outside_nil, and_true]
    rw [BitVec.toNat_ofNat]; simp only [wsp]; omega

/-- The witness for `gopanic`: as `wmem`, plus a pending open-coded defer in the caller's frame
(the `deferBits` byte `1` at `SP + 40`, the slot at `SP + 48` holding the funcval `0x41000`, whose
code word is `0x300000`). -/
def gmem : Memory :=
  ⟨fun a => if a = wsp + 40 then 1 else if a = wsp + 49 then 0x10 else if a = wsp + 50 then 0x04
      else if a = 0x41002 then 0x30 else 0,
    [⟨0x10000, 0x1000, true⟩, ⟨0x40000, 0x10000, true⟩, ⟨0x50000, 0x100, false⟩]⟩

/-- The `gopanic` witness call state: as `wstate`, with the panic value's type word `X0 = 1`. -/
def gstate : State := { wstate with regs := fun i => if i = 0 then 1 else wstate.regs i, mem := gmem }

theorem gstate_pre (nargs : Nat) (hn : nargs ≤ 2) : PanicPre P0 nargs gstate := by
  have hsp : gstate.sp = BitVec.ofNat 64 wsp := rfl
  have hg28 : gstate.regs 28 = BitVec.ofNat 64 wg := rfl
  have h30 : gstate.regs 30 = BitVec.ofNat 64 wret := rfl
  have hm : gstate.mem = gmem := rfl
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show gstate.mem.accessible 0x10000 0x1000 true = true; rw [hm]; decide
  · simp only [regG, stackguard0Offset, hg28]; decide
  · simp only [regG, stackguard0Offset, hg28, hm]; decide
  · simp only [stackguard0, regG, stackguard0Offset, hg28, hm, hsp, P0_depth]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp, P0_depth]; decide
  · decide
  · simp only [hsp, P0_depth]; rw [BitVec.toNat_ofNat]; simp only [wsp]; omega
  · simp only [hsp, hm, P0_depth]
    refine Memory.accessible_mono _
      (show gmem.accessible (wsp - 64) (64 + 8 + 8 * 2) true = true by decide) ?_ ?_
    · rw [BitVec.toNat_ofNat]; simp [wsp]
    · rw [BitVec.toNat_ofNat]; simp only [wsp]; omega
  · simp only [hsp, P0_priv, P0_depth, outside_cons, outside_nil, and_true]
    rw [BitVec.toNat_ofNat]; simp only [wsp]; omega

/-- The model `RET` meets every returning panic contract for `P0`: from any state at `A0` in
`PanicPre`, it returns to `X30` with the ABI preserved and memory unchanged (so confined to
`P0.priv` and the callee stack). -/
theorem ret_summary (n : Nat) :
    Summary (toy.link (at0 retCode)) A0 (PanicPre P0 n) (PanicRet P0 n) := by
  rw [link_at0]
  intro s hpc ⟨henv, hg, ⟨h30a, h30b, hsp, hst, h8, hwin, hacc⟩, hout⟩
  janus_run
  refine ⟨s.regs, s.flags, s.vregs, s.mem, ?_, MemFrame.refl _ _, henv⟩
  show _ = retState s s.regs [] s.flags s.vregs s.mem
  simp only [retState]
  congr 1
  funext i; simp only [callRegs_apply, List.getD_nil]; split <;> rfl

/-- A model implementation's return as `PanicRet`: the preserved registers and fields. -/
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

theorem deferproc_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferprocContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 1 s :=
  ⟨P0, _, P0_laws, ret_summary 1, wstate, rfl, wstate_pre 1 (by decide)⟩

theorem deferprocStack_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferprocStackContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 1 s :=
  ⟨P0, _, P0_laws, ret_summary 1, wstate, rfl, wstate_pre 1 (by decide)⟩

theorem deferprocat_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferprocatContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 2 s :=
  ⟨P0, _, P0_laws, ret_summary 2, wstate, rfl, wstate_pre 2 (by decide)⟩

theorem deferrangefunc_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferrangefuncContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 0 s :=
  ⟨P0, _, P0_laws, ret_summary 0, wstate, rfl, wstate_pre 0 (by decide)⟩

theorem deferreturn_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    DeferreturnContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧ PanicPre P 0 s :=
  ⟨P0, _, P0_laws, ret_summary 0, wstate, rfl, wstate_pre 0 (by decide)⟩

/-- The model `gorecover`: `x14 = PANREC`; if the active flag is clear, or the frame-pointer
chain's saved return address `[x29 + 8]` is not the recorded return point, return `nil`; otherwise
return the recorded value and set the recovered flag. -/
def gorecoverCode : List Nat :=
  [0xd281000e, 0xf2a0002e, 0xf9400dc9, 0xb4000149, 0xf94009ca, 0xf94007ab, 0xeb0b015f, 0x540000c1,
   0xf94001c0, 0xf94005c1, 0xd280002c, 0xf90011cc, 0xd65f03c0, 0xaa1f03e0, 0xaa1f03e1, 0xd65f03c0]

theorem gorecover_impl : GorecoverContract (toy.link (at0 gorecoverCode)) A0 P0 := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨h30a, h30b, hsp, hst, h8, hwin, hacc⟩, hout⟩, hfp, hfp'⟩
  simp only [P0_env] at henv
  have hrd : s.mem.accessible PANREC 0x800 true = true :=
    Memory.accessible_mono _ henv (by simp [PANREC]) (by simp [PANREC])
  have hr : s.mem.accessible PANREC 0x800 false = true := Janus.Contracts.IfaceModel.acc_read_of_write hrd
  simp only [PANREC] at hrd hr
  janus_run
  · -- the active flag is clear: `nil`
    refine ⟨panicRet_of P0 0 s _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (MemFrame.refl _ _) henv, fun h => h, fun v rp hp _ _ => ?_⟩
    have := hp.1; simp only [PANREC, Nat.reduceAdd] at this; omega
  · -- the recorded return point matches `[x29 + 8]`: return the value, set the recovered flag
    refine ⟨panicRet_of P0 0 s _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (by simp only [P0_priv, calleeStack, P0_depth, List.cons_append, List.nil_append]; janus_frame)
      (by simp only [P0_env, Memory.accessible_writeLE]; exact henv), fun hc => ?_,
      fun v rp hp _ _ => ?_⟩
    · have h1 : s.mem.readLE (PANREC + 24) 8 = 0 := hc
      simp only [PANREC, Nat.reduceAdd] at h1; omega
    · obtain ⟨-, h2, h3, -⟩ := hp
      simp only [PANREC, Nat.reduceAdd] at h2 h3
      have hl1 := Memory.readLE_lt s.mem 67584 8
      have hl2 := Memory.readLE_lt s.mem 67592 8
      refine ⟨by first | omega | (simp only [BitVec.toNat_ofNat]; omega) | (simp [setReg]; omega),
        by first | omega | (simp only [BitVec.toNat_ofNat]; omega) | (simp [setReg]; omega), ?_⟩
      · show (s.mem.writeLE (PANREC + 32) 8 1).readLE (PANREC + 32) 8 = 1
        rw [Memory.readLE_writeLE_self]
  · -- the return point does not match: `nil`
    refine ⟨panicRet_of P0 0 s _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (MemFrame.refl _ _) henv, fun hc => ?_, fun v rp hp _ hfp8 => ?_⟩
    · have h1 : s.mem.readLE (PANREC + 24) 8 = 0 := hc
      simp only [PANREC, Nat.reduceAdd] at h1; omega
    · obtain ⟨-, -, -, h4⟩ := hp
      simp only [PANREC, Nat.reduceAdd] at h4
      exact absurd (h4.trans hfp8.symm) (by assumption)

theorem gorecover_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment), P.Laws ∧
    GorecoverContract (toy.link impl) A0 P ∧ ∃ s, s.pc = BitVec.ofNat 64 A0 ∧
      (PanicPre P 0 s ∧ s.mem.accessible ((s.regs 29).toNat + 8) 8 false = true ∧
        (s.regs 29).toNat + 16 ≤ 2 ^ 48) :=
  ⟨P0, _, P0_laws, gorecover_impl, wstate, rfl, wstate_pre 0 (by decide), by decide, by decide⟩

/-- The model `gopanic` (deferBits at `SP + 40`, slot at `SP + 48`, resume address `0x100800`):
load the deferred funcval and its code word, open a 32-byte frame saving the caller's `SP`, clear
the bit, record the panic (value, return point, active flag) at `PANREC`, call the closure; on
its return restore the caller's `SP` and `X29`, clear the active flag and jump to `resume`. -/
def gopanicCode : List Nat :=
  [0x910003e9, 0xf940193a, 0xf940034b, 0xd10083ff, 0xf9000be9, 0x3900a13f, 0xd281000e, 0xf2a0002e,
   0xf90001c0, 0xf90005c1, 0x100000ed, 0xf90009cd, 0xd280002c, 0xf9000dcc, 0xf90011df, 0xd10023fd,
   0xd63f0160, 0xf9400be9, 0x9100013f, 0xd10023fd, 0xd281000e, 0xf2a0002e, 0xf9000ddf, 0xd281000c,
   0xf2a0020c, 0xd61f0180]

theorem gopanic_impl : GopanicRecoverContract (toy.link (at0 gopanicCode)) A0 P0 40 48 0x100800 := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨h30a, h30b, hsp, hst, h8, hwin, hacc⟩, hout⟩, hx0, hbits, hb1, hb2, hb3,
    hs1, hs2, hf1, hf2, hc1, hc2⟩
  simp only [P0_env, P0_depth, P0_priv, outside_cons, outside_nil, and_true] at henv hwin hacc hout hb3 hst
  have hrd : s.mem.accessible PANREC 0x800 true = true :=
    Memory.accessible_mono _ henv (by simp [PANREC]) (by simp [PANREC])
  simp only [PANREC] at hrd
  have hspl := s.sp.isLt
  show ReachesRet _ _ s _
  janus_run
  refine ⟨by omega, (by simp only [P0_depth]; omega), by omega, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [P0, PANREC, Nat.reduceAdd, Memory.readLE_writeLE_of_disjoint,
      Memory.readLE_writeLE_self]
    have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    exact ⟨trivial, by rw [h64]; exact Nat.mod_eq_of_lt (s.regs 0).isLt,
      by rw [h64]; exact Nat.mod_eq_of_lt (s.regs 1).isLt, trivial⟩
  · simp only [P0_env, Memory.accessible_writeLE]; exact henv
  · simp only [P0_priv, P0_depth, List.cons_append, List.nil_append]
    janus_frame
  · intro c' hpc' hsp' h28' h18' hag henv' hrec
    obtain ⟨r', sp', pc', fl', m', dz', vr', tp', fc', fs'⟩ := c'
    simp only at hpc' hsp' h28' h18' hag henv' hrec ⊢
    subst hpc' hsp'
    have hwin' : m'.accessible (s.sp.toNat - 32) 32 true = true := by
      rw [hag.1]; simp only [Memory.accessible_writeLE]
      exact Memory.accessible_mono _ hacc (by omega) (by omega)
    have hpr' : m'.accessible 67584 2048 true = true := by
      rw [hag.1]; simp only [Memory.accessible_writeLE]; exact hrd
    have hv : m'.readLE (s.sp.toNat - 16) 8 = s.sp.toNat := by
      rw [hag.readLE ⟨(s.sp.toNat - 32, s.sp.toNat), by simp, by omega, by omega⟩]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [h64]; exact Nat.mod_eq_of_lt s.sp.isLt
    show ReachesRet _ _ _ _
    janus_run
    have hsp0 : BitVec.ofNat 64 (m'.readLE (s.sp.toNat - 16) 8) = s.sp := by
      rw [hv]; exact BitVec.ofNat_toNat _ _
    refine ⟨hsp0, h28', h18', by rw [hsp0], ?_, ?_, ?_⟩
    · simp only [P0_priv, P0_depth, List.cons_append, List.nil_append]
      janus_frame
    · simp only [P0_env, Memory.accessible_writeLE] at henv' ⊢; exact henv'
    · show (m'.writeLE (PANREC + 24) 8 0).readLE (PANREC + 24) 8 = 0
      rw [Memory.readLE_writeLE_self]


theorem gopanic_satisfiable : ∃ (P : PanicRuntime) (impl : List Segment) (bitsOff slotOff resume : Nat),
    P.Laws ∧ GopanicRecoverContract (toy.link impl) A0 P bitsOff slotOff resume ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ GopanicRecoverPre P bitsOff slotOff s := by
  refine ⟨P0, _, 40, 48, 0x100800, P0_laws, gopanic_impl, gstate, rfl, gstate_pre 2 (by decide),
    by decide, ?_, by decide, ?_, ?_, by decide, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [P0_priv, outside_cons, outside_nil, and_true]) <;> decide

end Janus.Contracts.PanicSat
