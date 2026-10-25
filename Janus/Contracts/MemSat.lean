import Janus.Contracts.EqHashModel
import Janus.Contracts.IfaceSat
import Janus.Tactic.Float

/-!
# The equality and typed-memory contracts are satisfiable (arm64)

For every contract of `Janus.Contracts.Mem`: machine code (A64 assembly, its words below) placed
at the address `A0` of a program with no other code (`IfaceSat.toy`, `IfaceSat.at0`), a proof
by symbolic execution that it satisfies the contract (for every stack bound `d`, since no
implementation uses its stack, every write-barrier address `wb`, and the models `EqHashModel.M0`
and `IfaceModel.R0`, whose laws hold), and a call state over the witness memory
`EqHashModel.wmem` that satisfies the contract's precondition. So no contract is contradictory:
`<contract>_satisfiable` states that a model, an implementation and such a state exist, and the
implementation then reaches the contract's postcondition from that state (`Summary`).

**Loops.** The contracts quantify over every call state, so the implementations are complete:
`memequal`, `strequal`, `memequal_varlen` and the typed-memory functions run byte loops (the
`memmove` loop copies backwards when the destination is above the source, so overlapping ranges
are copied correctly). A loop is a *core*: its words form a segment of their own at
`HEAD = A0 + 4`, proved once as a `Summary` of that segment (by induction on the bytes left,
with the loop head as the invariant point, as in `examples/proofs/Sum.lean`). An implementation
is `[w] ++ core ++ prefix`: the first word falls through into the core (`nop`) or branches to
the prefix, which sets up the core's arguments and branches to `HEAD`. The core's summary moves
into the implementation's program by `EqHashModel.Summary.of_codeIn` (`codeIn_core`) and is
used at `HEAD` like a call whose return is the implementation's return (`ReachesRet.call`).
-/

namespace Janus.Contracts.MemSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Mem Janus.Contracts.IfaceSat Janus.Contracts.EqHashModel
  Janus.Float

/-! ## Witness states and the return -/

/-- The witness call state: the arguments `r`, goroutine `wg`, return address `wret`, stack
pointer `wsp` (all from `IfaceModel`), memory `EqHashModel.wmem`. -/
def wstate (r : Nat → W64) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 IfaceModel.wg
      else if i = 30 then BitVec.ofNat 64 IfaceModel.wret else r i,
    sp := BitVec.ofNat 64 IfaceModel.wsp, pc := BitVec.ofNat 64 A0,
    flags := ⟨false, false, false, false⟩, mem := EqHashModel.wmem }

@[simp] theorem wstate_mem (r : Nat → W64) : (wstate r).mem = EqHashModel.wmem := rfl
@[simp] theorem wstate_sp (r : Nat → W64) : (wstate r).sp = BitVec.ofNat 64 IfaceModel.wsp := rfl
@[simp] theorem wstate_fpcr (r : Nat → W64) : (wstate r).fpcr = 0 := rfl
theorem wstate_regs (r : Nat → W64) (i : Nat) (h28 : i ≠ 28) (h30 : i ≠ 30) :
    (wstate r).regs i = r i := by simp [wstate, h28, h30]

/-- The witness stack window: `[wsp - 64, wsp + 8 + 8·4)` is writable. -/
theorem wmem_window : EqHashModel.wmem.accessible (IfaceModel.wsp - 64) (64 + 8 + 8 * 4) true = true := by
  decide

/-- The witness state satisfies the stack guard and `CallOK` for the stack bound 64 and up to
four arguments. -/
theorem wstate_eqPre (r : Nat → W64) (n : Nat) (hn : n ≤ 4) : EqPre 64 n (wstate r) := by
  have h28 : (wstate r).regs 28 = BitVec.ofNat 64 IfaceModel.wg := rfl
  have h30 : (wstate r).regs 30 = BitVec.ofNat 64 IfaceModel.wret := rfl
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, by decide, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, h28]; decide
  · simp only [regG, stackguard0Offset, h28, wstate_mem]; decide
  · simp only [stackguard0, regG, stackguard0Offset, h28, wstate_mem, wstate_sp]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [wstate_sp]; decide
  · simp only [wstate_sp]; decide
  · simp only [wstate_sp]; simp [IfaceModel.wsp]; omega
  · simp only [wstate_sp, wstate_mem, BitVec.toNat_ofNat]
    exact Memory.accessible_mono _ wmem_window (by simp [IfaceModel.wsp])
      (by simp [IfaceModel.wsp]; omega)
  · simp only [calleeStack, h28, wstate_sp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [IfaceModel.wsp, IfaceModel.wg]; omega

/-- The window of the witness state (stack bound 64) is outside the model runtime range
`[0x10000, 0x11000)`. -/
theorem wstate_outside (r : Nat → W64) (n : Nat) :
    Outside ((wstate r).sp.toNat - 64) (64 + 8 + 8 * n) [(0x10000, 0x11000)] := by
  simp only [wstate_sp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
  simp [IfaceModel.wsp]

/-- The user data `[0x30000, 0x31000)` of the witness memory is writable. -/
theorem wmem_user : EqHashModel.wmem.accessible 0x30000 0x1000 true = true := by decide

/-- `k` bytes of user data at `a` are an input of a call from the witness state. -/
theorem wstate_input (r : Nat → W64) (nargs a k : Nat) (h1 : 0x30000 ≤ a) (h2 : a + k ≤ 0x31000) :
    Input (wstate r) 64 nargs a k := by
  refine ⟨by omega, Memory.accessible_mono _ (IfaceModel.acc_read_of_write wmem_user) h1 h2, ?_⟩
  simp only [calleeStack, wstate_sp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
  simp [IfaceModel.wsp]; omega

/-- The final state of a run that keeps `SP`, `X18`, `X28`, `X29` and the system registers and
returns to `X30` is `s` with the ABI-kept registers, the rest of the registers, the SIMD&FP
registers, the flags, `FPSR` and memory replaced: the common part of `EqRet`, `IfaceRet`,
`TRet` and `Hash.HRet`. -/
theorem ret_eq {s s' : State} (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30)
    (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29)
    (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr) :
    s' = { s with regs := Map.keepABI s.regs s'.regs, vregs := s'.vregs, flags := s'.flags,
                  fpsr := s'.fpsr, mem := s'.mem, pc := s.regs 30 } := by
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc hdz htp hfc h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-- What a run from `S` to `S'` keeps (the ABI-preserved registers and the system registers)
and where it returns (`X30`). -/
structure Keeps (S S' : State) : Prop where
  sp : S'.sp = S.sp
  pc : S'.pc = S.regs 30
  r18 : S'.regs 18 = S.regs 18
  r28 : S'.regs 28 = S.regs 28
  r29 : S'.regs 29 = S.regs 29
  dczid : S'.dczid = S.dczid
  tpidr : S'.tpidr = S.tpidr
  fpcr : S'.fpcr = S.fpcr

theorem Keeps.ret_eq {S S' : State} (h : Keeps S S') :
    S' = { S with regs := Map.keepABI S.regs S'.regs, vregs := S'.vregs, flags := S'.flags,
                  fpsr := S'.fpsr, mem := S'.mem, pc := S.regs 30 } :=
  MemSat.ret_eq h.sp h.pc h.r18 h.r28 h.r29 h.dczid h.tpidr h.fpcr

/-- `Keeps` through a state `T` that agrees with `S` on the kept fields and `X30`. -/
theorem Keeps.trans {S T S' : State} (h : Keeps T S') (hsp : T.sp = S.sp) (h30 : T.regs 30 = S.regs 30)
    (h18 : T.regs 18 = S.regs 18) (h28 : T.regs 28 = S.regs 28) (h29 : T.regs 29 = S.regs 29)
    (hdz : T.dczid = S.dczid) (htp : T.tpidr = S.tpidr) (hfc : T.fpcr = S.fpcr) : Keeps S S' :=
  ⟨h.sp.trans hsp, h.pc.trans h30, h.r18.trans h18, h.r28.trans h28, h.r29.trans h29,
    h.dczid.trans hdz, h.tpidr.trans htp, h.fpcr.trans hfc⟩

/-- `EqRet` from `Keeps`. -/
theorem eqRet_of {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop} (hk : Keeps s s')
    (hf : MemFrame s.mem s'.mem (calleeStack s d nargs)) (hp : P s'.regs) : EqRet d nargs s s' P :=
  ⟨_, _, _, _, _, hk.ret_eq, hf, hp⟩

/-- The return address is admissible. -/
def RetOK (S : State) : Prop := (S.regs 30).toNat % 4 = 0 ∧ (S.regs 30).toNat < 2 ^ 48

/-! ## Cores -/

/-- Where a core starts. -/
def HEAD : Nat := A0 + 4

/-- A core as a program of its own. -/
def coreProg (ws : List Nat) : Program := segProg ⟨"core", HEAD, ws⟩

/-- A segment at `B` whose words are `w :: core ++ rest` has the instructions of `core` at
`B + 4`. -/
theorem codeIn_core_at (B : Nat) (nm nm' : String) (w : Nat) (core rest : List Nat) :
    CodeIn (segProg ⟨nm, B + 4, core⟩)
      { segments := [⟨nm', B, w :: (core ++ rest)⟩], stubs := [], exitAddr := 0 } := by
  intro pc v hf
  obtain ⟨i, hi, rfl⟩ := fetchIn_single_some hf
  simp only at hi
  refine ⟨?_, rfl, by simp only; omega⟩
  have h1 : (segProg ⟨nm, B + 4, core⟩).fetch (B + 4 + 4 * i) = core[i]? := by
    simp only [segProg, Program.fetch, Program.fetchIn]
    rw [ite_eq_left (by omega), show (B + 4 + 4 * i - (B + 4)) / 4 = i by omega]
    cases core[i]? <;> rfl
  have h2 : Program.fetch { segments := [⟨nm', B, w :: (core ++ rest)⟩], stubs := [], exitAddr := 0 }
      (B + 4 + 4 * i) = core[i]? := by
    simp only [Program.fetch, Program.fetchIn]
    rw [ite_eq_left (by omega), show (B + 4 + 4 * i - B) / 4 = i + 1 by omega]
    simp only [List.getElem?_cons_succ, List.getElem?_append_left hi]
    cases core[i]? <;> rfl
  simp only at hf ⊢
  rw [h2, ← h1]; exact hf

/-- `withCode (w :: core ++ rest)` has the instructions of the core at `HEAD`. -/
theorem codeIn_core (w : Nat) (core rest : List Nat) :
    CodeIn (coreProg core) (withCode (w :: (core ++ rest))) :=
  codeIn_core_at A0 "core" "model" w core rest

/-- Weaken the goal of a run. -/
theorem ReachesRet.weaken {p : Program} {r r' : W64} {T : State} {Q Q' : State → Prop}
    (h : ReachesRet p r T Q) (hr : r = r') (hq : ∀ x, Q x → Q' x) : ReachesRet p r' T Q' := by
  obtain ⟨k, s', hs, hpc, hq'⟩ := h
  exact ⟨k, s', hs, hpc.trans hr, hq' |> hq s'⟩

/-! ## The byte-comparison core -/

/-- The byte-comparison core (`X0 = a`, `X1 = b`, `X2 = n`), at `HEAD`:
```
head: cbz x2, 1f
      ldrb w3, [x0], #1
      ldrb w4, [x1], #1
      cmp w3, w4
      b.ne neq
      sub x2, x2, #1
      b head
1:    mov x0, #1
      ret
neq:  mov x0, #0
      ret
``` -/
def eqCore : List Nat :=
  [0xb40000e2, 0x38401403, 0x38401424, 0x6b04007f, 0x540000a1, 0xd1000442, 0x17fffffa,
   0xd2800020, 0xd65f03c0, 0xd2800000, 0xd65f03c0]

/-- What the byte-comparison core needs: an admissible return address and the `n` bytes at `a`
and `b` readable. -/
def EqCorePre (S : State) : Prop :=
  RetOK S ∧ S.mem.accessible (S.regs 0).toNat (S.regs 2).toNat false = true ∧
    S.mem.accessible (S.regs 1).toNat (S.regs 2).toNat false = true

/-- What it returns: memory unchanged, `X0` the comparison. -/
def EqCorePost (S S' : State) : Prop :=
  Keeps S S' ∧ S'.mem = S.mem ∧ BoolRes S'.regs
    (S.mem.readLE (S.regs 0).toNat (S.regs 2).toNat == S.mem.readLE (S.regs 1).toNat (S.regs 2).toNat)

theorem readLE_succ_beq (m : Memory) (a b n : Nat) :
    (m.readLE a (n + 1) == m.readLE b (n + 1)) =
      ((m.bytes a).toNat == (m.bytes b).toNat && (m.readLE (a + 1) n == m.readLE (b + 1) n)) := by
  rw [Memory.readLE_succ, Memory.readLE_succ]
  have ha := (m.bytes a).isLt
  have hb := (m.bytes b).isLt
  generalize (m.bytes a).toNat = x at *
  generalize (m.bytes b).toNat = y at *
  generalize m.readLE (a + 1) n = u
  generalize m.readLE (b + 1) n = v
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq, Bool.and_eq_true]
  omega

/-- A byte loaded by `ldrb` and compared as a 32-bit word. -/
theorem byte_w32 (m : Memory) (a : Nat) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE a 1))).toNat = (m.bytes a).toNat := by
  have := (m.bytes a).isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Memory.readLE_one]
  omega

/-- `x + 1` of an address below `2^48`. -/
theorem toNat_add_one {x : W64} (h : x.toNat + 1 ≤ 2 ^ 48) : (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add]; simp; omega

/-- `x - 1` of a non-zero count. -/
theorem toNat_sub_one {x : W64} {n : Nat} (h : x.toNat = n + 1) : (x - 1#64).toNat = n := by
  rw [BitVec.toNat_sub]; simp; omega

theorem eqCore_sum : Summary (coreProg eqCore) HEAD EqCorePre EqCorePost := by
  intro S hpc hpre
  obtain ⟨⟨h30a, h30b⟩, ha, hb⟩ := hpre
  generalize hn : (S.regs 2).toNat = n at ha hb
  induction n generalizing S with
  | zero =>
    have h2 : S.regs 2 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hn)
    janus_run
    refine ⟨⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩, rfl, ?_⟩
    simp [BoolRes, setReg, hn]
  | succ n ih =>
    have ha1 := Memory.accessible_mono _ ha (Nat.le_refl _)
      (by omega : (S.regs 0).toNat + 1 ≤ (S.regs 0).toNat + (n + 1))
    have hb1 := Memory.accessible_mono _ hb (Nat.le_refl _)
      (by omega : (S.regs 1).toNat + 1 ≤ (S.regs 1).toNat + (n + 1))
    have hab := Memory.accessible_bound _ ha
    have hbb := Memory.accessible_bound _ hb
    have h2 : S.regs 2 ≠ 0#64 := fun h => by simp [h] at hn
    janus_run until [HEAD]
    · rw [byte_w32, byte_w32] at hbr
      have e0 := toNat_add_one (x := S.regs 0) (by omega)
      have e1 := toNat_add_one (x := S.regs 1) (by omega)
      refine ReachesRet.weaken (ih _ rfl (by simpa [setReg] using h30a) (by simpa [setReg] using h30b)
        (by simpa [setReg] using toNat_sub_one hn) ?_ ?_) (by simp [setReg, regLR]) ?_
      · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, e0]
        exact Memory.accessible_mono _ ha (by omega) (by omega)
      · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, e1]
        exact Memory.accessible_mono _ hb (by omega) (by omega)
      · rintro S' ⟨hk, hm, hr⟩
        refine ⟨hk.trans rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
          (by simp [setReg]) rfl rfl rfl, hm, ?_⟩
        simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, e0, e1, toNat_sub_one hn] at hr
        rw [hn, readLE_succ_beq, hbr]
        simpa using hr
    · rename_i _ hne _
      rw [byte_w32, byte_w32] at hne
      refine ⟨⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩, rfl, ?_⟩
      rw [hn, readLE_succ_beq]
      simp [BoolRes, setReg, beq_false_of_ne hne]

/-- Run a core from `HEAD` in an implementation `w :: core ++ rest` whose return is the core's. -/
theorem core_run {core : List Nat} {pre : State → Prop} {post : State → State → Prop}
    (hsum : Summary (coreProg core) HEAD pre post) {code : List Nat} (w : Nat) (rest : List Nat)
    (hcode : code = w :: (core ++ rest)) {T : State} {ret : W64} {Q : State → Prop}
    (hpc : T.pc = BitVec.ofNat 64 HEAD) (hpre : pre T) (hret : T.regs 30 = ret)
    (h : ∀ S', post T S' → Q S') : ReachesRet (withCode code) ret T Q := by
  subst hcode
  exact ReachesRet.call (Summary.of_codeIn (codeIn_core w core rest) hsum) hpc hpre
    fun S' hpc' hq => ReachesRet.done (hpc'.trans hret) (h S' hq)

/-! ## `memequal`, `memequal0/8/16/32/64/128`, `memequal_varlen`, `strequal` -/

/-- `nop`, then the byte-comparison core (`eqCore`). -/
def memequalCode : List Nat := 0xd503201f :: (eqCore ++ [])

theorem memequal_impl (d : Nat) : Memequal (toy.link (at0 memequalCode)) A0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus_run until [HEAD]
  refine core_run eqCore_sum _ _ rfl rfl ⟨⟨hl1, hl2⟩, ha2, hb2⟩ rfl fun S' ⟨hk, hm, hr⟩ => ?_
  exact eqRet_of (hk.trans rfl rfl rfl rfl rfl rfl rfl rfl) (hm ▸ MemFrame.refl _ _) hr

/-- The witness arguments of the comparisons: `X0 = X1 = VAL`, `X2 = 8`. -/
def eqArgs : Nat → W64 := fun i =>
  if i = 0 ∨ i = 1 then BitVec.ofNat 64 IfaceModel.VAL else if i = 2 then 8#64 else 0

/-- `Memequal` is satisfiable. -/
theorem memequal_satisfiable : ∃ (impl : List Segment) (d : Nat),
    Memequal (toy.link impl) A0 d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (EqPre d 0 s ∧ Input s d 0 (s.regs 0).toNat (s.regs 2).toNat ∧
        Input s d 0 (s.regs 1).toNat (s.regs 2).toNat) :=
  ⟨_, 64, memequal_impl 64, wstate eqArgs, rfl, wstate_eqPre _ 0 (by decide),
    wstate_input _ 0 _ _ (by decide) (by decide), wstate_input _ 0 _ _ (by decide) (by decide)⟩

/-- `b pre`, the core, `pre: movz x2, #n; b head`: `memequal` with the size `n < 2^16`. -/
def memequalNCode (n : Nat) : List Nat :=
  0x1400000c :: (eqCore ++ [0xd2800002 + n * 32, 0x17fffff4])

/-- The `MemequalN` proof for a concrete `n` (the size word is executed, so it is concrete). -/
macro "memequalN_tac" : tactic => `(tactic| (
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus_run until [HEAD]
  refine core_run eqCore_sum _ _ rfl rfl ⟨⟨by simpa [setReg] using hl1, by simpa [setReg] using hl2⟩,
    by simpa [setReg] using ha2, by simpa [setReg] using hb2⟩ (by simp [setReg])
    fun S' ⟨hk, hm, hr⟩ => ?_
  exact eqRet_of (hk.trans rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl) (hm ▸ MemFrame.refl _ _) (by simpa [setReg] using hr)))

theorem memequal0_impl (d : Nat) : MemequalN (toy.link (at0 (memequalNCode 0))) A0 d 0 := by
  memequalN_tac
theorem memequal8_impl (d : Nat) : MemequalN (toy.link (at0 (memequalNCode 1))) A0 d 1 := by
  memequalN_tac
theorem memequal16_impl (d : Nat) : MemequalN (toy.link (at0 (memequalNCode 2))) A0 d 2 := by
  memequalN_tac
theorem memequal32_impl (d : Nat) : MemequalN (toy.link (at0 (memequalNCode 4))) A0 d 4 := by
  memequalN_tac
theorem memequal64_impl (d : Nat) : MemequalN (toy.link (at0 (memequalNCode 8))) A0 d 8 := by
  memequalN_tac
theorem memequal128_impl (d : Nat) : MemequalN (toy.link (at0 (memequalNCode 16))) A0 d 16 := by
  memequalN_tac

/-- `MemequalN` is satisfiable for `n = 0, 1, 2, 4, 8, 16`. -/
theorem memequalN_satisfiable (n : Nat) (hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) :
    ∃ (impl : List Segment) (d : Nat), MemequalN (toy.link impl) A0 d n ∧
      ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
        (EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat n ∧ Input s d 2 (s.regs 1).toNat n) := by
  have h0 : ((wstate eqArgs).regs 0).toNat = IfaceModel.VAL := by simp [wstate, eqArgs, IfaceModel.VAL]
  have h1 : ((wstate eqArgs).regs 1).toNat = IfaceModel.VAL := by simp [wstate, eqArgs, IfaceModel.VAL]
  have hv : IfaceModel.VAL + n ≤ 0x31000 := by simp only [IfaceModel.VAL]; omega
  have hs : EqPre 64 2 (wstate eqArgs) ∧ Input (wstate eqArgs) 64 2 ((wstate eqArgs).regs 0).toNat n ∧
      Input (wstate eqArgs) 64 2 ((wstate eqArgs).regs 1).toNat n := by
    rw [h0, h1]
    exact ⟨wstate_eqPre _ 2 (by decide), wstate_input _ 2 _ _ (by decide) hv,
      wstate_input _ 2 _ _ (by decide) hv⟩
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, 64, memequal0_impl 64, _, rfl, hs⟩
  · exact ⟨_, 64, memequal8_impl 64, _, rfl, hs⟩
  · exact ⟨_, 64, memequal16_impl 64, _, rfl, hs⟩
  · exact ⟨_, 64, memequal32_impl 64, _, rfl, hs⟩
  · exact ⟨_, 64, memequal64_impl 64, _, rfl, hs⟩
  · exact ⟨_, 64, memequal128_impl 64, _, rfl, hs⟩

/-- `b pre`, the core, `pre: ldr x2, [x26, #8]; b head`: the closure's size, then `memequal`. -/
def memequalVarlenCode : List Nat := 0x1400000c :: (eqCore ++ [0xf9400742, 0x17fffff4])

theorem memequalVarlen_impl (d : Nat) : MemequalVarlen (toy.link (at0 memequalVarlenCode)) A0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, ⟨hv1, hv2, hv3⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  have hsz : (BitVec.ofNat 64 (varlenSize s)).toNat = varlenSize s :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Memory.readLE_lt _ _ _) (by decide))
  simp only [varlenSize] at hsz ha1 ha2 ha3 hb1 hb2 hb3 ⊢
  janus_run until [HEAD]
  refine core_run eqCore_sum _ _ rfl rfl ⟨⟨by simpa [setReg] using hl1, by simpa [setReg] using hl2⟩,
    by simpa [setReg, hsz] using ha2, by simpa [setReg, hsz] using hb2⟩ (by simp [setReg])
    fun S' ⟨hk, hm, hr⟩ => ?_
  exact eqRet_of (hk.trans rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl) (hm ▸ MemFrame.refl _ _) (by simpa [setReg, hsz] using hr)

/-- `MemequalVarlen` is satisfiable. -/
theorem memequalVarlen_satisfiable : ∃ (impl : List Segment) (d : Nat),
    MemequalVarlen (toy.link impl) A0 d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ Input s d 2 ((s.regs 26).toNat + 8) 8 ∧
        Input s d 2 (s.regs 0).toNat (varlenSize s) ∧ Input s d 2 (s.regs 1).toNat (varlenSize s)) := by
  let r : Nat → W64 := fun i => if i = 26 then BitVec.ofNat 64 VLEN else eqArgs i
  have h0 : ((wstate r).regs 0).toNat = IfaceModel.VAL := by simp [r, wstate, eqArgs, IfaceModel.VAL]
  have h1 : ((wstate r).regs 1).toNat = IfaceModel.VAL := by simp [r, wstate, eqArgs, IfaceModel.VAL]
  have h26 : ((wstate r).regs 26).toNat = VLEN := by simp [r, wstate, VLEN]
  have hsz : varlenSize (wstate r) = 8 := by simp only [varlenSize, h26, wstate_mem]; decide
  refine ⟨_, 64, memequalVarlen_impl 64, wstate r, rfl, wstate_eqPre _ 2 (by decide), ?_, ?_, ?_⟩
  · rw [h26]; exact wstate_input _ 2 _ _ (by decide) (by decide)
  · rw [h0, hsz]; exact wstate_input _ 2 _ _ (by decide) (by decide)
  · rw [h1, hsz]; exact wstate_input _ 2 _ _ (by decide) (by decide)

/-- `b pre`, the core, `pre: ldr x2, [x0, #8]; ldr x3, [x1, #8]; cmp x2, x3; b.ne neq;
ldr x0, [x0]; ldr x1, [x1]; b head`: the lengths, then `memequal` of the data. -/
def strequalCode : List Nat :=
  0x1400000c :: (eqCore ++
    [0xf9400402, 0xf9400423, 0xeb03005f, 0x54ffff61, 0xf9400000, 0xf9400021, 0x17ffffef])

/-- A word read from memory, as a 64-bit register and back. -/
theorem toNat_ofNat_readLE8 (m : Memory) (a : Nat) : (BitVec.ofNat 64 (m.readLE a 8)).toNat = m.readLE a 8 :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Memory.readLE_lt _ _ _) (by decide))

theorem strequal_impl (d : Nat) : Strequal (toy.link (at0 strequalCode)) A0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, ⟨⟨ha1, ha2, ha3⟩, ⟨hpa1, hpa2, hpa3⟩⟩, ⟨⟨hb1, hb2, hb3⟩, ⟨hpb1, hpb2, hpb3⟩⟩⟩
  have ha8 := Memory.accessible_mono _ ha2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 8 ≤ (s.regs 0).toNat + 16)
  have ha8' := Memory.accessible_mono _ ha2 (by omega : (s.regs 0).toNat ≤ (s.regs 0).toNat + 8) (by omega : (s.regs 0).toNat + 8 + 8 ≤ (s.regs 0).toNat + 16)
  have hb8 := Memory.accessible_mono _ hb2 (Nat.le_refl _) (by omega : (s.regs 1).toNat + 8 ≤ (s.regs 1).toNat + 16)
  have hb8' := Memory.accessible_mono _ hb2 (by omega : (s.regs 1).toNat ≤ (s.regs 1).toNat + 8) (by omega : (s.regs 1).toNat + 8 + 8 ≤ (s.regs 1).toNat + 16)
  simp only [strPtr, strLen] at hpa1 hpa2 hpb1 hpb2
  janus_run until [HEAD]
  · refine core_run eqCore_sum _ _ rfl rfl ⟨⟨by simpa [setReg] using hl1, by simpa [setReg] using hl2⟩,
      ?_, ?_⟩ (by simp [setReg]) fun S' ⟨hk, hm, hr⟩ => ?_
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      rw [toNat_ofNat_readLE8, toNat_ofNat_readLE8, ← hbr]; exact hpa2
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      rw [toNat_ofNat_readLE8, toNat_ofNat_readLE8]; exact hpb2
    · refine eqRet_of (hk.trans rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
        (by simp [setReg]) rfl rfl rfl) (hm ▸ MemFrame.refl _ _) ?_
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, toNat_ofNat_readLE8] at hr
      simpa [strEq, strPtr, strLen, hbr] using hr
  · rename_i hne _
    refine eqRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
      (MemFrame.refl _ _) ?_
    simp [BoolRes, setReg, strEq, strLen, beq_false_of_ne hne]

/-- The witness arguments of the string comparison: `X0 = X1 = STR`. -/
def strArgs : Nat → W64 := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 STR else 0

/-- The witness string `STR` is an input. -/
theorem wstate_strInput (r : Nat → W64) (nargs : Nat) : StrInput (wstate r) 64 nargs STR := by
  have hp : strPtr EqHashModel.wmem STR = IfaceModel.VAL := by decide
  have hl : strLen EqHashModel.wmem STR = 8 := by decide
  refine ⟨wstate_input _ _ _ _ (by decide) (by decide), ?_⟩
  rw [wstate_mem, hp, hl]; exact wstate_input _ _ _ _ (by decide) (by decide)

/-- `Strequal` is satisfiable. -/
theorem strequal_satisfiable : ∃ (impl : List Segment) (d : Nat),
    Strequal (toy.link impl) A0 d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ StrInput s d 2 (s.regs 0).toNat ∧ StrInput s d 2 (s.regs 1).toNat) := by
  have h0 : ((wstate strArgs).regs 0).toNat = STR := by simp [wstate, strArgs, STR]
  have h1 : ((wstate strArgs).regs 1).toNat = STR := by simp [wstate, strArgs, STR]
  refine ⟨_, 64, strequal_impl 64, wstate strArgs, rfl, wstate_eqPre _ 2 (by decide), ?_, ?_⟩
  · rw [h0]; exact wstate_strInput _ 2
  · rw [h1]; exact wstate_strInput _ 2

/-! ## Floating-point and complex equality -/

/-- `ldr s0, [x0]; ldr s1, [x1]; fcmp s0, s1; cset x0, eq; ret`. -/
def f32equalCode : List Nat := [0xbd400000, 0xbd400021, 0x1e212000, 0x9a9f17e0, 0xd65f03c0]

/-- `ldr d0, [x0]; ldr d1, [x1]; fcmp d0, d1; cset x0, eq; ret`. -/
def f64equalCode : List Nat := [0xfd400000, 0xfd400021, 0x1e612000, 0x9a9f17e0, 0xd65f03c0]

theorem f32equal_impl (d : Nat) : Fequal (toy.link (at0 f32equalCode)) A0 d binary32 4 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, hf, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  have hx : s.mem.readLE (s.regs 0).toNat 4 < 4294967296 := Memory.readLE_lt _ _ _
  have hy : s.mem.readLE (s.regs 1).toNat 4 < 4294967296 := Memory.readLE_lt _ _ _
  janus_run [hf]
  refine eqRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, hf.symm⟩
    (MemFrame.refl _ _) ?_
  simp only [BoolRes, setReg_apply, reduceIte, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide : 4294967296 < 340282366920938463463374607431768211456)),
    Nat.mod_eq_of_lt (Nat.lt_trans hy (by decide : 4294967296 < 340282366920938463463374607431768211456))]
  cases feq binary32 (s.mem.readLE (s.regs 0).toNat 4) (s.mem.readLE (s.regs 1).toNat 4) <;> rfl

theorem f64equal_impl (d : Nat) : Fequal (toy.link (at0 f64equalCode)) A0 d binary64 8 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, hf, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  have hx : s.mem.readLE (s.regs 0).toNat 8 < 18446744073709551616 := Memory.readLE_lt _ _ _
  have hy : s.mem.readLE (s.regs 1).toNat 8 < 18446744073709551616 := Memory.readLE_lt _ _ _
  janus_run [hf]
  refine eqRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, hf.symm⟩
    (MemFrame.refl _ _) ?_
  simp only [BoolRes, setReg_apply, reduceIte,
    Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide : 18446744073709551616 < 340282366920938463463374607431768211456)),
    Nat.mod_eq_of_lt (Nat.lt_trans hy (by decide : 18446744073709551616 < 340282366920938463463374607431768211456))]
  cases feq binary64 (s.mem.readLE (s.regs 0).toNat 8) (s.mem.readLE (s.regs 1).toNat 8) <;> rfl

/-- `ldr s0, [x0]; ldr s1, [x1]; ldr s2, [x0, #4]; ldr s3, [x1, #4]; fcmp s0, s1; cset w4, eq;
fcmp s2, s3; cset w5, eq; and w0, w4, w5; ret`. -/
def c64equalCode : List Nat :=
  [0xbd400000, 0xbd400021, 0xbd400402, 0xbd400423, 0x1e212000, 0x1a9f17e4, 0x1e232040,
   0x1a9f17e5, 0x0a050080, 0xd65f03c0]

/-- `ldr d0, [x0]; ldr d1, [x1]; ldr d2, [x0, #8]; ldr d3, [x1, #8]; fcmp d0, d1; cset w4, eq;
fcmp d2, d3; cset w5, eq; and w0, w4, w5; ret`. -/
def c128equalCode : List Nat :=
  [0xfd400000, 0xfd400021, 0xfd400402, 0xfd400423, 0x1e612000, 0x1a9f17e4, 0x1e632040,
   0x1a9f17e5, 0x0a050080, 0xd65f03c0]

/-- A 4-byte read as a single-precision register holds it. -/
theorem rd4 (m : Memory) (a : Nat) :
    m.readLE a 4 % 340282366920938463463374607431768211456 % 4294967296 = m.readLE a 4 := by
  have := Memory.readLE_lt m a 4; simp at this; omega

/-- An 8-byte read as a double-precision register holds it. -/
theorem rd8 (m : Memory) (a : Nat) :
    m.readLE a 8 % 340282366920938463463374607431768211456 = m.readLE a 8 := by
  have := Memory.readLE_lt m a 8; simp at this; omega

theorem c64equal_impl (d : Nat) : Cequal (toy.link (at0 c64equalCode)) A0 d binary32 4 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, hf, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  have ha4 := Memory.accessible_mono _ ha2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 4 ≤ (s.regs 0).toNat + 2 * 4)
  have ha4' := Memory.accessible_mono _ ha2 (by omega : (s.regs 0).toNat ≤ (s.regs 0).toNat + 4) (by omega : (s.regs 0).toNat + 4 + 4 ≤ (s.regs 0).toNat + 2 * 4)
  have hb4 := Memory.accessible_mono _ hb2 (Nat.le_refl _) (by omega : (s.regs 1).toNat + 4 ≤ (s.regs 1).toNat + 2 * 4)
  have hb4' := Memory.accessible_mono _ hb2 (by omega : (s.regs 1).toNat ≤ (s.regs 1).toNat + 4) (by omega : (s.regs 1).toNat + 4 + 4 ≤ (s.regs 1).toNat + 2 * 4)
  janus_run [hf]
  refine eqRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, hf.symm⟩
    (MemFrame.refl _ _) ?_
  simp only [BoolRes, setReg_apply, reduceIte, rd4]
  cases feq binary32 (s.mem.readLE (s.regs 0).toNat 4) (s.mem.readLE (s.regs 1).toNat 4) <;>
    cases feq binary32 (s.mem.readLE ((s.regs 0).toNat + 4) 4) (s.mem.readLE ((s.regs 1).toNat + 4) 4) <;>
    rfl

theorem c128equal_impl (d : Nat) : Cequal (toy.link (at0 c128equalCode)) A0 d binary64 8 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩, _⟩, hf, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  have ha4 := Memory.accessible_mono _ ha2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 8 ≤ (s.regs 0).toNat + 2 * 8)
  have ha4' := Memory.accessible_mono _ ha2 (by omega : (s.regs 0).toNat ≤ (s.regs 0).toNat + 8) (by omega : (s.regs 0).toNat + 8 + 8 ≤ (s.regs 0).toNat + 2 * 8)
  have hb4 := Memory.accessible_mono _ hb2 (Nat.le_refl _) (by omega : (s.regs 1).toNat + 8 ≤ (s.regs 1).toNat + 2 * 8)
  have hb4' := Memory.accessible_mono _ hb2 (by omega : (s.regs 1).toNat ≤ (s.regs 1).toNat + 8) (by omega : (s.regs 1).toNat + 8 + 8 ≤ (s.regs 1).toNat + 2 * 8)
  janus_run [hf]
  refine eqRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, hf.symm⟩
    (MemFrame.refl _ _) ?_
  simp only [BoolRes, setReg_apply, reduceIte, Nat.reduceEqDiff, rd8]
  cases feq binary64 (s.mem.readLE (s.regs 0).toNat 8) (s.mem.readLE (s.regs 1).toNat 8) <;>
    cases feq binary64 (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8) <;>
    rfl

/-- `Fequal` is satisfiable for `float32` and `float64`: the witness compares `VAL` with itself
(the bytes at `VAL` are `42` and zeros, a finite float of either format). -/
theorem fequal_satisfiable (f : Fmt) (k : Nat) (hf : (f = binary32 ∧ k = 4) ∨ (f = binary64 ∧ k = 8)) :
    ∃ (impl : List Segment) (d : Nat), Fequal (toy.link impl) A0 d f k ∧
      ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
        (EqPre d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat k ∧ Input s d 2 (s.regs 1).toNat k) := by
  have h0 : ((wstate eqArgs).regs 0).toNat = IfaceModel.VAL := by simp [wstate, eqArgs, IfaceModel.VAL]
  have h1 : ((wstate eqArgs).regs 1).toNat = IfaceModel.VAL := by simp [wstate, eqArgs, IfaceModel.VAL]
  have hs : ∀ k, k ≤ 16 → EqPre 64 2 (wstate eqArgs) ∧ (wstate eqArgs).fpcr = 0 ∧
      Input (wstate eqArgs) 64 2 ((wstate eqArgs).regs 0).toNat k ∧
      Input (wstate eqArgs) 64 2 ((wstate eqArgs).regs 1).toNat k := fun k hk => by
    rw [h0, h1]
    have hv : IfaceModel.VAL + k ≤ 0x31000 := by simp only [IfaceModel.VAL]; omega
    exact ⟨wstate_eqPre _ 2 (by decide), rfl, wstate_input _ 2 _ _ (by decide) hv,
      wstate_input _ 2 _ _ (by decide) hv⟩
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, 64, f32equal_impl 64, _, rfl, hs 4 (by decide)⟩
  · exact ⟨_, 64, f64equal_impl 64, _, rfl, hs 8 (by decide)⟩

/-- `Cequal` is satisfiable for `complex64` and `complex128`. -/
theorem cequal_satisfiable (f : Fmt) (k : Nat) (hf : (f = binary32 ∧ k = 4) ∨ (f = binary64 ∧ k = 8)) :
    ∃ (impl : List Segment) (d : Nat), Cequal (toy.link impl) A0 d f k ∧
      ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
        (EqPre d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat (2 * k) ∧
          Input s d 2 (s.regs 1).toNat (2 * k)) := by
  have h0 : ((wstate eqArgs).regs 0).toNat = IfaceModel.VAL := by simp [wstate, eqArgs, IfaceModel.VAL]
  have h1 : ((wstate eqArgs).regs 1).toNat = IfaceModel.VAL := by simp [wstate, eqArgs, IfaceModel.VAL]
  have hs : ∀ k, k ≤ 16 → EqPre 64 2 (wstate eqArgs) ∧ (wstate eqArgs).fpcr = 0 ∧
      Input (wstate eqArgs) 64 2 ((wstate eqArgs).regs 0).toNat k ∧
      Input (wstate eqArgs) 64 2 ((wstate eqArgs).regs 1).toNat k := fun k hk => by
    rw [h0, h1]
    have hv : IfaceModel.VAL + k ≤ 0x31000 := by simp only [IfaceModel.VAL]; omega
    exact ⟨wstate_eqPre _ 2 (by decide), rfl, wstate_input _ 2 _ _ (by decide) hv,
      wstate_input _ 2 _ _ (by decide) hv⟩
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, 64, c64equal_impl 64, _, rfl, hs 8 (by decide)⟩
  · exact ⟨_, 64, c128equal_impl 64, _, rfl, hs 16 (by decide)⟩

/-! ## Interface comparison -/

/-- `IfaceRet` from `Keeps`. -/
theorem ifaceRet_of {R : IfaceModel} {d : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (hk : Keeps s s') (hf : MemFrame s.mem s'.mem (R.priv ++ calleeStack s d 2))
    (he : R.Env s'.mem (s.regs 28)) (hp : P s'.regs) : IfaceRet R d s s' P :=
  ⟨_, _, _, _, _, hk.ret_eq, hf, he, hp⟩

/-- `ldr x2, [x0]; ldr x3, [x1]; cmp x2, x3; b.ne ne; cbz x2, nil; ldr x2, [x0, #8];
ldr x3, [x1, #8]; ldr x2, [x2]; ldr x3, [x3]; cmp x2, x3; cset x0, eq; ret; nil: mov x0, #1;
ret; ne: mov x0, #0; ret`: equal first words, then (unless nil) the 8-byte values the data words
point to (`R0`'s one comparable type `TD`). The same code serves `interequal`: `R0`'s non-nil
itabs have the type `TD`. -/
def ifaceEqualCode : List Nat :=
  [0xf9400002, 0xf9400023, 0xeb03005f, 0x54000161, 0xb4000102, 0xf9400402, 0xf9400423, 0xf9400042,
   0xf9400063, 0xeb03005f, 0x9a9f17e0, 0xd65f03c0, 0xd2800020, 0xd65f03c0, 0xd2800000, 0xd65f03c0]

theorem nilinterequal_impl (d : Nat) : Nilinterequal (toy.link (at0 ifaceEqualCode)) A0 IfaceModel.R0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hl1, hl2, hc⟩, hout, _⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩, hok⟩
  have ha8 := Memory.accessible_mono _ ha2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 8 ≤ (s.regs 0).toNat + 16)
  have ha8' := Memory.accessible_mono _ ha2 (by omega : (s.regs 0).toNat ≤ (s.regs 0).toNat + 8) (by omega : (s.regs 0).toNat + 8 + 8 ≤ (s.regs 0).toNat + 16)
  have hb8 := Memory.accessible_mono _ hb2 (Nat.le_refl _) (by omega : (s.regs 1).toNat + 8 ≤ (s.regs 1).toNat + 16)
  have hb8' := Memory.accessible_mono _ hb2 (by omega : (s.regs 1).toNat ≤ (s.regs 1).toNat + 8) (by omega : (s.regs 1).toNat + 8 + 8 ≤ (s.regs 1).toNat + 16)
  have hk : ∀ v : W64, Keeps s { s with regs := setReg s.regs 0 v, pc := s.regs 30 } :=
    fun v => ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
  by_cases heq : s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 1).toNat 8
  · by_cases h0 : s.mem.readLE (s.regs 0).toNat 8 = 0
    · janus_run
      refine ifaceRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
        (MemFrame.refl _ _) henv ?_
      simp [BoolRes, setReg, Iface.efaceEqual]
    · obtain ⟨hok1, -⟩ := hok heq
      obtain ⟨-, htd, hx, hy⟩ := hok1 h0
      janus_run
      refine ifaceRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
        (MemFrame.refl _ _) henv ?_
      rw [← heq, htd, efaceEqual_R0 (g := s.regs 28) henv]
      simp only [BoolRes, setReg_apply, reduceIte, Nat.reduceEqDiff]
      split
      · rename_i h; simp [h]
      · rename_i h; simp [beq_false_of_ne h]
  · janus_run
    refine ifaceRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
      (MemFrame.refl _ _) henv ?_
    simp [BoolRes, setReg, beq_false_of_ne heq]

theorem interequal_impl (d : Nat) : Interequal (toy.link (at0 ifaceEqualCode)) A0 IfaceModel.R0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hl1, hl2, hc⟩, hout, _⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩, hok⟩
  have ha8 := Memory.accessible_mono _ ha2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 8 ≤ (s.regs 0).toNat + 16)
  have ha8' := Memory.accessible_mono _ ha2 (by omega : (s.regs 0).toNat ≤ (s.regs 0).toNat + 8) (by omega : (s.regs 0).toNat + 8 + 8 ≤ (s.regs 0).toNat + 16)
  have hb8 := Memory.accessible_mono _ hb2 (Nat.le_refl _) (by omega : (s.regs 1).toNat + 8 ≤ (s.regs 1).toNat + 16)
  have hb8' := Memory.accessible_mono _ hb2 (by omega : (s.regs 1).toNat ≤ (s.regs 1).toNat + 8) (by omega : (s.regs 1).toNat + 8 + 8 ≤ (s.regs 1).toNat + 16)
  by_cases heq : s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 1).toNat 8
  · by_cases h0 : s.mem.readLE (s.regs 0).toNat 8 = 0
    · janus_run
      refine ifaceRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
        (MemFrame.refl _ _) henv ?_
      simp [BoolRes, setReg, Iface.ifaceEqual]
    · obtain ⟨-, ht0, hok1, -⟩ := hok heq h0
      obtain ⟨-, htd, hx, hy⟩ := hok1 ht0
      janus_run
      refine ifaceRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
        (MemFrame.refl _ _) henv ?_
      rw [← heq]
      simp only [Iface.ifaceEqual, htd, beq_false_of_ne h0, Bool.false_or]
      rw [efaceEqual_R0 (g := s.regs 28) henv]
      simp only [BoolRes, setReg_apply, reduceIte, Nat.reduceEqDiff]
      split
      · rename_i h; simp [h]
      · rename_i h; simp [beq_false_of_ne h]
  · janus_run
    refine ifaceRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl⟩
      (MemFrame.refl _ _) henv ?_
    simp [BoolRes, setReg, beq_false_of_ne heq]

/-- The witness state satisfies `IfacePre` for `R0` and the stack bound 64. -/
theorem wstate_ifacePre (r : Nat → W64) : IfacePre IfaceModel.R0 64 (wstate r) :=
  ⟨EqHashModel.wmem_env0 ((wstate r).regs 28), (wstate_eqPre r 2 (by decide)).1,
    (wstate_eqPre r 2 (by decide)).2.1, wstate_outside r 2, (wstate_eqPre r 2 (by decide)).2.2⟩

/-- The witness comparison of two `TD`-values at `VAL` does not depend on the callee's window
(`EqFrame.of_regular`: `TD` is `TFlagRegularMemory`, not direct, and `VAL` and `R0.priv` are
outside the window). -/
theorem wstate_eqFrame (r : Nat → W64) :
    EqFrame IfaceModel.R0 IfaceModel.TD EqHashModel.wmem IfaceModel.VAL IfaceModel.VAL
      (calleeStack (wstate r) 64 2) := by
  have hsz : tySize EqHashModel.wmem IfaceModel.TD = 8 := by decide
  have hout : ∀ a n, a + n ≤ 0x31000 → Outside a n (calleeStack (wstate r) 64 2) := fun a n h => by
    simp only [calleeStack, wstate_sp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [IfaceModel.wsp]; omega
  refine EqFrame.of_regular (g := (wstate r).regs 28) IfaceModel.R0_laws (EqHashModel.wmem_env0 ((wstate r).regs 28)) (Or.inl rfl)
    (by decide) (by decide) (by rw [hsz]; decide) (by rw [hsz]; decide) (by rw [hsz]; exact hout _ _ (by decide))
    (by rw [hsz]; exact hout _ _ (by decide)) fun a n ⟨rg, hr, h1, h2⟩ => hout a n ?_
  simp only [IfaceModel.R0_priv, List.mem_singleton] at hr; subst hr; simp only at h2; omega

/-- The witness values of type `TD` compare (`EqOK`). -/
theorem wmem_eqOK : Iface.EqOK IfaceModel.R0 EqHashModel.wmem IfaceModel.TD IfaceModel.VAL IfaceModel.VAL :=
  fun _ => ⟨Or.inl rfl, rfl, by decide, by decide⟩

/-- `Nilinterequal` is satisfiable: the witness compares the `any` value `EFV = (TD, VAL)` with
itself (equal non-nil types, so the comparison of the values runs). -/
theorem nilinterequal_satisfiable : ∃ (R : IfaceModel) (impl : List Segment) (d : Nat), R.Laws ∧
    Nilinterequal (toy.link impl) A0 R d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (IfacePre R d s ∧ IfaceInput s d (s.regs 0).toNat ∧ IfaceInput s d (s.regs 1).toNat ∧
        (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 1).toNat 8 →
          Iface.EqOK R s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.mem.readLE ((s.regs 0).toNat + 8) 8)
            (s.mem.readLE ((s.regs 1).toNat + 8) 8) ∧
          EqFrame R (s.mem.readLE (s.regs 0).toNat 8) s.mem (s.mem.readLE ((s.regs 0).toNat + 8) 8)
            (s.mem.readLE ((s.regs 1).toNat + 8) 8) (calleeStack s d 2))) := by
  let r : Nat → W64 := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 EFV else 0
  have h0 : ((wstate r).regs 0).toNat = EFV := by simp [r, wstate, EFV]
  have h1 : ((wstate r).regs 1).toNat = EFV := by simp [r, wstate, EFV]
  have ht : EqHashModel.wmem.readLE EFV 8 = IfaceModel.TD := by decide
  have hv : EqHashModel.wmem.readLE (EFV + 8) 8 = IfaceModel.VAL := by decide
  refine ⟨_, _, 64, IfaceModel.R0_laws, nilinterequal_impl 64, wstate r, rfl, wstate_ifacePre r, ?_, ?_, ?_⟩
  · rw [h0]; exact wstate_input _ 2 _ _ (by decide) (by decide)
  · rw [h1]; exact wstate_input _ 2 _ _ (by decide) (by decide)
  · rw [h0, h1, wstate_mem, ht, hv]; exact fun _ => ⟨wmem_eqOK, wstate_eqFrame r⟩

/-- `Interequal` is satisfiable: the witness compares `IFV = (TAB, VAL)` with itself (equal
non-nil itabs of the type `TD`). -/
theorem interequal_satisfiable : ∃ (R : IfaceModel) (impl : List Segment) (d : Nat), R.Laws ∧
    Interequal (toy.link impl) A0 R d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (IfacePre R d s ∧ IfaceInput s d (s.regs 0).toNat ∧ IfaceInput s d (s.regs 1).toNat ∧
      (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 1).toNat 8 →
        s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        Input s d 2 (s.mem.readLE (s.regs 0).toNat 8) 16 ∧
        s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8 ≠ 0 ∧
        Iface.EqOK R s.mem (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8)
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8) ∧
        EqFrame R (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8) s.mem
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 1).toNat + 8) 8)
          (calleeStack s d 2))) := by
  let r : Nat → W64 := fun i => if i = 0 ∨ i = 1 then BitVec.ofNat 64 IFV else 0
  have h0 : ((wstate r).regs 0).toNat = IFV := by simp [r, wstate, IFV]
  have h1 : ((wstate r).regs 1).toNat = IFV := by simp [r, wstate, IFV]
  have ht : EqHashModel.wmem.readLE IFV 8 = IfaceModel.TAB := by decide
  have htt : EqHashModel.wmem.readLE (IfaceModel.TAB + 8) 8 = IfaceModel.TD := by decide
  have hv : EqHashModel.wmem.readLE (IFV + 8) 8 = IfaceModel.VAL := by decide
  have hin : Input (wstate r) 64 2 IfaceModel.TAB 16 := by
    refine ⟨by decide, by decide, ?_⟩
    simp only [calleeStack, wstate_sp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [IfaceModel.wsp, IfaceModel.TAB]
  refine ⟨_, _, 64, IfaceModel.R0_laws, interequal_impl 64, wstate r, rfl, wstate_ifacePre r, ?_, ?_, ?_⟩
  · rw [h0]; exact wstate_input _ 2 _ _ (by decide) (by decide)
  · rw [h1]; exact wstate_input _ 2 _ _ (by decide) (by decide)
  · rw [h0, h1, wstate_mem, ht, htt, hv]
    exact fun _ _ => ⟨hin, by decide, wmem_eqOK, wstate_eqFrame r⟩

/-! ## The clearing core -/

/-- The byte-clearing core (`X0 = p`, `X1 = n`), at `HEAD`:
```
head: cbz x1, 1f
      strb wzr, [x0], #1
      sub x1, x1, #1
      b head
1:    ret
``` -/
def clrCore : List Nat := [0xb4000081, 0x3800141f, 0xd1000421, 0x17fffffd, 0xd65f03c0]

/-- What the clearing core needs: an admissible return address and the `n` bytes at `p`
writable. -/
def ClrPre (S : State) : Prop :=
  RetOK S ∧ S.mem.accessible (S.regs 0).toNat (S.regs 1).toNat true = true

/-- What it returns: memory changed only in `[p, p + n)`, which is zero. -/
def ClrPost (S S' : State) : Prop :=
  Keeps S S' ∧ MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + (S.regs 1).toNat)] ∧
    Zeroed S'.mem (S.regs 0).toNat (S.regs 1).toNat

theorem clr_loop (S : State) (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hacc : S.mem.accessible (S.regs 0).toNat (S.regs 1).toNat true = true) :
    ∀ k (T : State) (i : Nat), i + k = (S.regs 1).toNat → T.pc = BitVec.ofNat 64 HEAD →
      (T.regs 0).toNat = (S.regs 0).toNat + i → (T.regs 1).toNat = k →
      T.sp = S.sp → T.regs 18 = S.regs 18 → T.regs 28 = S.regs 28 → T.regs 29 = S.regs 29 →
      T.regs 30 = S.regs 30 → T.dczid = S.dczid → T.tpidr = S.tpidr → T.fpcr = S.fpcr →
      MemFrame S.mem T.mem [((S.regs 0).toNat, (S.regs 0).toNat + i)] →
      Zeroed T.mem (S.regs 0).toNat i →
      ReachesRet (coreProg clrCore) (S.regs 30) T (ClrPost S) := by
  have hb := Memory.accessible_bound _ hacc
  intro k
  induction k with
  | zero =>
    intro T i hi hpc h0 h1 hsp h18 h28 h29 h30 hdz htp hfc hf hz
    have h1' : T.regs 1 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    have ha : T.regs 30 = S.regs 30 := h30
    rw [← ha] at h30a h30b ⊢
    janus_run
    refine ⟨⟨rfl, rfl, h18, h28, h29, hdz, htp, rfl⟩, ?_, ?_⟩
    · rw [← hi, Nat.add_zero]; exact hf
    · rw [← hi, Nat.add_zero]; exact hz
  | succ k ih =>
    intro T i hi hpc h0 h1 hsp h18 h28 h29 h30 hdz htp hfc hf hz
    have h1' : T.regs 1 ≠ 0#64 := fun h => by simp [h] at h1
    have hw : T.mem.accessible (T.regs 0).toNat 1 true = true := by
      rw [hf.accessible, h0]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
    janus_run until [HEAD]
    have e0 : (T.regs 0 + 1#64).toNat = (S.regs 0).toNat + (i + 1) := by
      rw [toNat_add_one (by omega), h0]; omega
    refine ih _ (i + 1) (by omega) rfl (by simpa [setReg] using e0)
      (by simpa [setReg] using toNat_sub_one h1) rfl (by simpa [setReg] using h18)
      (by simpa [setReg] using h28) (by simpa [setReg] using h29) (by simpa [setReg] using h30)
      hdz htp rfl ?_ ?_
    · rw [h0]
      refine (hf.mono fun a n h => ?_).writeLE 0 (List.mem_singleton_self _) (by simp) (by simp; omega)
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
    · intro j hj
      rw [h0]
      by_cases hji : j = i
      · subst hji; rw [Memory.bytes_writeLE_inside _ (by omega) (by omega), Nat.zero_div]; rfl
      · rw [Memory.bytes_writeLE_outside _ (by omega)]; exact hz j (by omega)

theorem clrCore_sum : Summary (coreProg clrCore) HEAD ClrPre ClrPost := by
  intro S hpc ⟨⟨h30a, h30b⟩, hacc⟩
  exact clr_loop S h30a h30b hacc _ S 0 (by simp) hpc (by simp) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (MemFrame.refl _ _) (fun j hj => absurd hj (Nat.not_lt_zero _))

/-! ## The copying core -/

/-- The byte-copying core (`X0 = dst`, `X1 = src`, `X2 = n`), at `HEAD`: forwards when
`dst ≤ src`, backwards otherwise, so overlapping ranges are copied correctly.
```
      cmp x0, x1
      b.hi bwd
fwd:  cbz x2, done
      ldrb w3, [x1], #1
      strb w3, [x0], #1
      sub x2, x2, #1
      b fwd
bwd:  cbz x2, done
      sub x2, x2, #1
      ldrb w3, [x1, x2]
      strb w3, [x0, x2]
      b bwd
done: ret
``` -/
def moveCore : List Nat :=
  [0xeb01001f, 0x540000c8, 0xb4000142, 0x38401423, 0x38001403, 0xd1000442, 0x17fffffc,
   0xb40000a2, 0xd1000442, 0x38626823, 0x38226803, 0x17fffffc, 0xd65f03c0]

/-- What the copying core needs: an admissible return address, the `n` bytes at `src`
readable and those at `dst` writable. -/
def MovePre (S : State) : Prop :=
  RetOK S ∧ S.mem.accessible (S.regs 1).toNat (S.regs 2).toNat false = true ∧
    S.mem.accessible (S.regs 0).toNat (S.regs 2).toNat true = true

/-- What it returns: memory changed only in `[dst, dst + n)`, which holds the bytes `src` held. -/
def MovePost (S S' : State) : Prop :=
  Keeps S S' ∧ MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + (S.regs 2).toNat)] ∧
    Copied S.mem S'.mem (S.regs 0).toNat (S.regs 1).toNat (S.regs 2).toNat

/-- The forward loop head. -/
def FWD : Nat := HEAD + 8
/-- The backward loop head. -/
def BWD : Nat := HEAD + 28

/-- A byte loaded and stored by `ldrb`/`strb`. -/
theorem byte_copy (m : Memory) (a : Nat) {a' : Nat} :
    BitVec.ofNat 8 (m.readLE a 1 % 18446744073709551616 / 256 ^ (a' - a')) = m.bytes a := by
  have := (m.bytes a).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Memory.readLE_one, Nat.sub_self, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
  omega

theorem fwd_loop (S : State) (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hsrc : S.mem.accessible (S.regs 1).toNat (S.regs 2).toNat false = true)
    (hdst : S.mem.accessible (S.regs 0).toNat (S.regs 2).toNat true = true)
    (hle : (S.regs 0).toNat ≤ (S.regs 1).toNat) :
    ∀ k (T : State) (i : Nat), i + k = (S.regs 2).toNat → T.pc = BitVec.ofNat 64 FWD →
      (T.regs 0).toNat = (S.regs 0).toNat + i → (T.regs 1).toNat = (S.regs 1).toNat + i →
      (T.regs 2).toNat = k →
      T.sp = S.sp → T.regs 18 = S.regs 18 → T.regs 28 = S.regs 28 → T.regs 29 = S.regs 29 →
      T.regs 30 = S.regs 30 → T.dczid = S.dczid → T.tpidr = S.tpidr → T.fpcr = S.fpcr →
      MemFrame S.mem T.mem [((S.regs 0).toNat, (S.regs 0).toNat + i)] →
      Copied S.mem T.mem (S.regs 0).toNat (S.regs 1).toNat i →
      ReachesRet (coreProg moveCore) (S.regs 30) T (MovePost S) := by
  have hbs := Memory.accessible_bound _ hsrc
  have hbd := Memory.accessible_bound _ hdst
  intro k
  induction k with
  | zero =>
    intro T i hi hpc h0 h1 h2 hsp h18 h28 h29 h30 hdz htp hfc hf hc
    have h2' : T.regs 2 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
    have ha : T.regs 30 = S.regs 30 := h30
    rw [← ha] at h30a h30b ⊢
    janus_run
    refine ⟨⟨rfl, rfl, h18, h28, h29, hdz, htp, rfl⟩, ?_, ?_⟩
    · rw [← hi, Nat.add_zero]; exact hf
    · rw [← hi, Nat.add_zero]; exact hc
  | succ k ih =>
    intro T i hi hpc h0 h1 h2 hsp h18 h28 h29 h30 hdz htp hfc hf hc
    have h2' : T.regs 2 ≠ 0#64 := fun h => by simp [h] at h2
    have hr : T.mem.accessible (T.regs 1).toNat 1 false = true := by
      rw [hf.accessible, h1]; exact Memory.accessible_mono _ hsrc (by omega) (by omega)
    have hw : T.mem.accessible (T.regs 0).toNat 1 true = true := by
      rw [hf.accessible, h0]; exact Memory.accessible_mono _ hdst (by omega) (by omega)
    janus_run until [FWD]
    have e0 : (T.regs 0 + 1#64).toNat = (S.regs 0).toNat + (i + 1) := by
      rw [toNat_add_one (by omega), h0]; omega
    have e1 : (T.regs 1 + 1#64).toNat = (S.regs 1).toNat + (i + 1) := by
      rw [toNat_add_one (by omega), h1]; omega
    refine ih _ (i + 1) (by omega) rfl (by simpa [setReg] using e0) (by simpa [setReg] using e1)
      (by simpa [setReg] using toNat_sub_one h2) rfl (by simpa [setReg] using h18)
      (by simpa [setReg] using h28) (by simpa [setReg] using h29) (by simpa [setReg] using h30)
      hdz htp rfl ?_ ?_
    · rw [h0]
      refine (hf.mono fun a n h => ?_).writeLE _ (List.mem_singleton_self _) (by simp) (by simp; omega)
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
    · intro j hj
      rw [h0, h1]
      by_cases hji : j = i
      · subst hji; rw [Memory.bytes_writeLE_inside _ (by omega) (by omega)]; exact byte_copy _ _
      · rw [Memory.bytes_writeLE_outside _ (by omega)]; exact hc j (by omega)

theorem bwd_loop (S : State) (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hsrc : S.mem.accessible (S.regs 1).toNat (S.regs 2).toNat false = true)
    (hdst : S.mem.accessible (S.regs 0).toNat (S.regs 2).toNat true = true)
    (hlt : (S.regs 1).toNat < (S.regs 0).toNat) :
    ∀ k (T : State), k ≤ (S.regs 2).toNat → T.pc = BitVec.ofNat 64 BWD →
      T.regs 0 = S.regs 0 → T.regs 1 = S.regs 1 → (T.regs 2).toNat = k →
      T.sp = S.sp → T.regs 18 = S.regs 18 → T.regs 28 = S.regs 28 → T.regs 29 = S.regs 29 →
      T.regs 30 = S.regs 30 → T.dczid = S.dczid → T.tpidr = S.tpidr → T.fpcr = S.fpcr →
      MemFrame S.mem T.mem [((S.regs 0).toNat + k, (S.regs 0).toNat + (S.regs 2).toNat)] →
      (∀ j, k ≤ j → j < (S.regs 2).toNat → T.mem.bytes ((S.regs 0).toNat + j) = S.mem.bytes ((S.regs 1).toNat + j)) →
      ReachesRet (coreProg moveCore) (S.regs 30) T (MovePost S) := by
  have hbs := Memory.accessible_bound _ hsrc
  have hbd := Memory.accessible_bound _ hdst
  intro k
  induction k with
  | zero =>
    intro T hk hpc h0 h1 h2 hsp h18 h28 h29 h30 hdz htp hfc hf hc
    have h2' : T.regs 2 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
    have ha : T.regs 30 = S.regs 30 := h30
    rw [← ha] at h30a h30b ⊢
    janus_run
    refine ⟨⟨rfl, rfl, h18, h28, h29, hdz, htp, rfl⟩, ?_, ?_⟩
    · simpa using hf
    · intro j hj; exact hc j (Nat.zero_le _) hj
  | succ k ih =>
    intro T hk hpc h0 h1 h2 hsp h18 h28 h29 h30 hdz htp hfc hf hc
    have h2' : T.regs 2 ≠ 0#64 := fun h => by simp [h] at h2
    have e2 := toNat_sub_one h2
    have ea : (T.regs 1 + (T.regs 2 - 1#64)).toNat = (S.regs 1).toNat + k := by
      rw [BitVec.toNat_add, e2, h1]; omega
    have eb : (T.regs 0 + (T.regs 2 - 1#64)).toNat = (S.regs 0).toNat + k := by
      rw [BitVec.toNat_add, e2, h0]; omega
    have hr : T.mem.accessible (T.regs 1 + (T.regs 2 - 1#64)).toNat 1 false = true := by
      rw [hf.accessible, ea]; exact Memory.accessible_mono _ hsrc (by omega) (by omega)
    have hw : T.mem.accessible (T.regs 0 + (T.regs 2 - 1#64)).toNat 1 true = true := by
      rw [hf.accessible, eb]; exact Memory.accessible_mono _ hdst (by omega) (by omega)
    janus_run until [BWD]
    simp only [h2, Nat.add_sub_cancel]
    refine ih _ (by omega) rfl (by simpa [setReg] using h0) (by simpa [setReg] using h1)
      (by simpa [setReg] using e2) rfl (by simpa [setReg] using h18)
      (by simpa [setReg] using h28) (by simpa [setReg] using h29) (by simpa [setReg] using h30)
      hdz htp rfl ?_ ?_
    · refine (hf.mono fun a n h => ?_).writeLE _ (List.mem_singleton_self _) (by simp) (by simp; omega)
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
    · intro j hj1 hj2
      by_cases hji : j = k
      · subst hji; rw [Memory.bytes_writeLE_inside _ (by omega) (by omega)]; exact byte_copy _ _
      · rw [Memory.bytes_writeLE_outside _ (by omega)]; exact hc j (by omega) hj2

theorem moveCore_sum : Summary (coreProg moveCore) HEAD MovePre MovePost := by
  intro S hpc ⟨⟨h30a, h30b⟩, hsrc, hdst⟩
  janus_run until [FWD, BWD]
  · exact bwd_loop S h30a h30b hsrc hdst hbr _ _ (Nat.le_refl _) rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl (MemFrame.refl _ _) (fun j h1 h2 => absurd h2 (by omega))
  · exact fwd_loop S h30a h30b hsrc hdst (by omega) _ _ 0 (by simp) rfl (by simp) (by simp) rfl rfl
      rfl rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) (fun j hj => absurd hj (Nat.not_lt_zero _))

/-! ## `memmove`, `memclrNoHeapPointers` and the typed-memory functions -/

/-- `TRet` from `Keeps`. -/
theorem tRet_of {M : MemModel} {d nargs : Nat} {extra : List (Nat × Nat)} {s s' : State}
    {P : Memory → Prop} (hk : Keeps s s') (hf : MemFrame s.mem s'.mem (M.priv ++ calleeStack s d nargs ++ extra))
    (he : M.Env s'.mem (s.regs 28)) (hp : P s'.mem) : TRet M d nargs extra s s' P :=
  ⟨_, _, _, _, _, hk.ret_eq, hf, he, hp⟩

/-- A frame of one range inside a larger list of ranges. -/
theorem frame_extra {m m' : Memory} {a b : Nat} {rs : List (Nat × Nat)} (h : MemFrame m m' [(a, b)]) :
    MemFrame m m' (rs ++ [(a, b)]) :=
  h.mono fun x n hx => by simp only [outside_append, outside_cons, outside_nil, and_true] at hx ⊢; exact hx.2

/-- `nop`, then the copying core (`moveCore`). -/
def memmoveCode : List Nat := 0xd503201f :: (moveCore ++ [])

theorem memmove_impl (d : Nat) : Memmove (toy.link (at0 memmoveCode)) A0 EqHashModel.M0 d := by
  rw [link_at0]
  intro s hpc ⟨_, ⟨hg, ⟨hl1, hl2, hc⟩, _⟩, _, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4⟩⟩
  janus_run until [HEAD]
  refine core_run moveCore_sum _ _ rfl rfl ⟨⟨hl1, hl2⟩, hs2, hd2⟩ rfl fun S' ⟨hk, hf, hcp⟩ => ?_
  exact tRet_of (hk.trans rfl rfl rfl rfl rfl rfl rfl rfl) (frame_extra hf) trivial hcp

/-- `nop`, then the clearing core (`clrCore`). -/
def memclrCode : List Nat := 0xd503201f :: (clrCore ++ [])

theorem memclrNoHeapPointers_impl (d : Nat) :
    MemclrNoHeapPointers (toy.link (at0 memclrCode)) A0 EqHashModel.M0 d := by
  rw [link_at0]
  intro s hpc ⟨_, ⟨hg, ⟨hl1, hl2, hc⟩, _⟩, _, ⟨hd1, hd2, hd3, hd4⟩⟩
  janus_run until [HEAD]
  refine core_run clrCore_sum _ _ rfl rfl ⟨⟨hl1, hl2⟩, hd2⟩ rfl fun S' ⟨hk, hf, hz⟩ => ?_
  exact tRet_of (hk.trans rfl rfl rfl rfl rfl rfl rfl rfl) (frame_extra hf) trivial hz

theorem memclrHasPointers_impl (wb d : Nat) :
    MemclrHasPointers (toy.link (at0 memclrCode)) A0 EqHashModel.M0 wb d := by
  rw [link_at0]
  intro s hpc ⟨⟨_, hg, ⟨hl1, hl2, hc⟩, _⟩, _, _, ⟨hd1, hd2, hd3, hd4⟩⟩
  janus_run until [HEAD]
  refine core_run clrCore_sum _ _ rfl rfl ⟨⟨hl1, hl2⟩, hd2⟩ rfl fun S' ⟨hk, hf, hz⟩ => ?_
  exact tRet_of (hk.trans rfl rfl rfl rfl rfl rfl rfl rfl) (frame_extra hf) trivial hz

/-- `b pre`, the copying core, `pre: ldr x3, [x0]; mov x0, x1; mov x1, x2; mov x2, x3; b head`:
`memmove(dst, src, typ.Size_)`. -/
def typedmemmoveCode : List Nat :=
  0x1400000e :: (moveCore ++ [0xf9400003, 0xaa0103e0, 0xaa0203e1, 0xaa0303e2, 0x17ffffef])

theorem typedmemmove_impl (wb d : Nat) :
    TypedMemmove (toy.link (at0 typedmemmoveCode)) A0 EqHashModel.M0 wb d := by
  rw [link_at0]
  intro s hpc ⟨⟨_, hg, ⟨hl1, hl2, hc⟩, _⟩, ⟨ht1, ht2⟩, _, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4⟩⟩
  have ht8 := Memory.accessible_mono _ ht2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 8 ≤ (s.regs 0).toNat + 16)
  simp only [typSize] at hs1 hs2 hs3 hd1 hd2 hd3 hd4 ⊢
  janus_run until [HEAD]
  refine core_run moveCore_sum _ _ rfl rfl ⟨⟨by simpa [setReg] using hl1, by simpa [setReg] using hl2⟩,
    ?_, ?_⟩ (by simp [setReg]) fun S' ⟨hk, hf, hcp⟩ => ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; rw [toNat_ofNat_readLE8]; exact hs2
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; rw [toNat_ofNat_readLE8]; exact hd2
  refine tRet_of (hk.trans rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl) (frame_extra ?_) trivial ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hf; rw [toNat_ofNat_readLE8] at hf; exact hf
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hcp; rw [toNat_ofNat_readLE8] at hcp
    exact hcp

/-- `b pre`, the clearing core, `pre: ldr x2, [x0]; mov x0, x1; mov x1, x2; b head`:
`memclrNoHeapPointers(ptr, typ.Size_)`. -/
def typedmemclrCode : List Nat :=
  0x14000006 :: (clrCore ++ [0xf9400002, 0xaa0103e0, 0xaa0203e1, 0x17fffff8])

theorem typedmemclr_impl (wb d : Nat) :
    TypedMemclr (toy.link (at0 typedmemclrCode)) A0 EqHashModel.M0 wb d := by
  rw [link_at0]
  intro s hpc ⟨⟨_, hg, ⟨hl1, hl2, hc⟩, _⟩, ⟨ht1, ht2⟩, _, ⟨hd1, hd2, hd3, hd4⟩⟩
  have ht8 := Memory.accessible_mono _ ht2 (Nat.le_refl _) (by omega : (s.regs 0).toNat + 8 ≤ (s.regs 0).toNat + 16)
  simp only [typSize] at hd1 hd2 hd3 hd4 ⊢
  janus_run until [HEAD]
  refine core_run clrCore_sum _ _ rfl rfl ⟨⟨by simpa [setReg] using hl1, by simpa [setReg] using hl2⟩,
    ?_⟩ (by simp [setReg]) fun S' ⟨hk, hf, hz⟩ => ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; rw [toNat_ofNat_readLE8]; exact hd2
  refine tRet_of (hk.trans rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl) (frame_extra ?_) trivial ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hf; rw [toNat_ofNat_readLE8] at hf; exact hf
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hz; rw [toNat_ofNat_readLE8] at hz
    exact hz

/-- `ret`: with the barrier off, `bulkBarrierPreWrite` does nothing. -/
def bulkBarrierCode : List Nat := [0xd65f03c0]

theorem bulkBarrierOff_impl (wb d : Nat) :
    BulkBarrierOff (toy.link (at0 bulkBarrierCode)) A0 EqHashModel.M0 wb d := by
  rw [link_at0]
  intro s hpc ⟨⟨_, hg, ⟨hl1, hl2, hc⟩, _⟩, _⟩
  janus_run
  exact tRet_of ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (MemFrame.refl _ _) trivial trivial

/-- The witness state satisfies `TPre` for `M0`, the barrier flag `WB` and the stack bound 64. -/
theorem wstate_tPre (r : Nat → W64) (n : Nat) (hn : n ≤ 4) : TPre EqHashModel.M0 WB 64 n (wstate r) :=
  ⟨trivial, (wstate_eqPre r n hn).1, (wstate_eqPre r n hn).2.1, by simp [EqHashModel.M0],
    wstate_input r n WB 4 (by decide) (by decide), EqHashModel.wmem_wbOff, (wstate_eqPre r n hn).2.2,
    by simp [EqHashModel.M0]⟩

/-- `k` bytes of user data at `a` are a destination of a call from the witness state. -/
theorem wstate_dest (r : Nat → W64) (nargs a k : Nat) (h1 : 0x30000 ≤ a) (h2 : a + k ≤ 0x31000) :
    Dest EqHashModel.M0 (wstate r) 64 nargs a k := by
  refine ⟨by omega, Memory.accessible_mono _ wmem_user h1 h2, (wstate_input r nargs a k h1 h2).2.2, ?_⟩
  simp [EqHashModel.M0]

/-- The witness arguments of the copies: `X0 = DST`, `X1 = VAL`, `X2 = 8`. -/
def moveArgs : Nat → W64 := fun i =>
  if i = 0 then BitVec.ofNat 64 DST else if i = 1 then BitVec.ofNat 64 IfaceModel.VAL
  else if i = 2 then 8#64 else 0

/-- `Memmove` is satisfiable. -/
theorem memmove_satisfiable : ∃ (M : MemModel) (impl : List Segment) (d : Nat), M.Laws ∧
    Memmove (toy.link impl) A0 M d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (M.Env s.mem (s.regs 28) ∧ EqPre d 3 s ∧ Outside (s.sp.toNat - d) (d + 8 + 8 * 3) M.priv ∧
        Input s d 3 (s.regs 1).toNat (s.regs 2).toNat ∧ Dest M s d 3 (s.regs 0).toNat (s.regs 2).toNat) := by
  have h0 : ((wstate moveArgs).regs 0).toNat = DST := by simp [wstate, moveArgs, DST]
  have h1 : ((wstate moveArgs).regs 1).toNat = IfaceModel.VAL := by
    simp [wstate, moveArgs, IfaceModel.VAL]
  have h2 : ((wstate moveArgs).regs 2).toNat = 8 := by simp [wstate, moveArgs]
  refine ⟨_, _, 64, EqHashModel.M0_laws, memmove_impl 64, wstate moveArgs, rfl, trivial,
    wstate_eqPre _ 3 (by decide), by simp [EqHashModel.M0], ?_, ?_⟩
  · rw [h1, h2]; exact wstate_input _ 3 _ _ (by decide) (by decide)
  · rw [h0, h2]; exact wstate_dest _ 3 _ _ (by decide) (by decide)

/-- `MemclrNoHeapPointers` is satisfiable. -/
theorem memclrNoHeapPointers_satisfiable : ∃ (M : MemModel) (impl : List Segment) (d : Nat), M.Laws ∧
    MemclrNoHeapPointers (toy.link impl) A0 M d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (M.Env s.mem (s.regs 28) ∧ EqPre d 2 s ∧ Outside (s.sp.toNat - d) (d + 8 + 8 * 2) M.priv ∧
        Dest M s d 2 (s.regs 0).toNat (s.regs 1).toNat) := by
  let r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 DST else if i = 1 then 64#64 else 0
  have h0 : ((wstate r).regs 0).toNat = DST := by simp [r, wstate, DST]
  have h1 : ((wstate r).regs 1).toNat = 64 := by simp [r, wstate]
  refine ⟨_, _, 64, EqHashModel.M0_laws, memclrNoHeapPointers_impl 64, wstate r, rfl, trivial,
    wstate_eqPre _ 2 (by decide), by simp [EqHashModel.M0], ?_⟩
  rw [h0, h1]; exact wstate_dest _ 2 _ _ (by decide) (by decide)

/-- `MemclrHasPointers` is satisfiable. -/
theorem memclrHasPointers_satisfiable : ∃ (M : MemModel) (impl : List Segment) (wb d : Nat), M.Laws ∧
    MemclrHasPointers (toy.link impl) A0 M wb d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (TPre M wb d 2 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 1).toNat % 8 = 0 ∧
        Dest M s d 2 (s.regs 0).toNat (s.regs 1).toNat) := by
  let r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 DST else if i = 1 then 64#64 else 0
  have h0 : ((wstate r).regs 0).toNat = DST := by simp [r, wstate, DST]
  have h1 : ((wstate r).regs 1).toNat = 64 := by simp [r, wstate]
  refine ⟨_, _, WB, 64, EqHashModel.M0_laws, memclrHasPointers_impl WB 64, wstate r, rfl,
    wstate_tPre _ 2 (by decide), by rw [h0]; decide, by rw [h1], ?_⟩
  rw [h0, h1]; exact wstate_dest _ 2 _ _ (by decide) (by decide)

/-- The witness type `TD` (8 bytes) is readable and outside the callee's window. -/
theorem wstate_typ (r : Nat → W64) (nargs : Nat) :
    TypeOK EqHashModel.wmem IfaceModel.TD ∧ Outside IfaceModel.TD 16 (calleeStack (wstate r) 64 nargs) ∧
      typSize EqHashModel.wmem IfaceModel.TD = 8 := by
  refine ⟨⟨by decide, by decide⟩, ?_, by decide⟩
  simp only [calleeStack, wstate_sp, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
  simp [IfaceModel.wsp, IfaceModel.TD]

/-- `TypedMemmove` is satisfiable (the type `TD`, `dst = DST`, `src = VAL`). -/
theorem typedmemmove_satisfiable : ∃ (M : MemModel) (impl : List Segment) (wb d : Nat), M.Laws ∧
    TypedMemmove (toy.link impl) A0 M wb d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (TPre M wb d 3 s ∧ TypeOK s.mem (s.regs 0).toNat ∧
        Outside (s.regs 0).toNat 16 (calleeStack s d 3) ∧
        Input s d 3 (s.regs 2).toNat (typSize s.mem (s.regs 0).toNat) ∧
        Dest M s d 3 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat)) := by
  let r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 IfaceModel.TD else if i = 1 then BitVec.ofNat 64 DST
    else if i = 2 then BitVec.ofNat 64 IfaceModel.VAL else 0
  have h0 : ((wstate r).regs 0).toNat = IfaceModel.TD := by simp [r, wstate, IfaceModel.TD]
  have h1 : ((wstate r).regs 1).toNat = DST := by simp [r, wstate, DST]
  have h2 : ((wstate r).regs 2).toNat = IfaceModel.VAL := by simp [r, wstate, IfaceModel.VAL]
  obtain ⟨ht1, ht2, ht3⟩ := wstate_typ r 3
  refine ⟨_, _, WB, 64, EqHashModel.M0_laws, typedmemmove_impl WB 64, wstate r, rfl,
    wstate_tPre _ 3 (by decide), ?_, ?_, ?_, ?_⟩ <;> simp only [h0, wstate_mem]
  · exact ht1
  · exact ht2
  · rw [h2, ht3]; exact wstate_input _ 3 _ _ (by decide) (by decide)
  · rw [h1, ht3]; exact wstate_dest _ 3 _ _ (by decide) (by decide)

/-- `TypedMemclr` is satisfiable (the type `TD`, `ptr = DST`). -/
theorem typedmemclr_satisfiable : ∃ (M : MemModel) (impl : List Segment) (wb d : Nat), M.Laws ∧
    TypedMemclr (toy.link impl) A0 M wb d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (TPre M wb d 2 s ∧ TypeOK s.mem (s.regs 0).toNat ∧
        Outside (s.regs 0).toNat 16 (calleeStack s d 2) ∧
        Dest M s d 2 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat)) := by
  let r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 IfaceModel.TD else if i = 1 then BitVec.ofNat 64 DST
    else 0
  have h0 : ((wstate r).regs 0).toNat = IfaceModel.TD := by simp [r, wstate, IfaceModel.TD]
  have h1 : ((wstate r).regs 1).toNat = DST := by simp [r, wstate, DST]
  obtain ⟨ht1, ht2, ht3⟩ := wstate_typ r 2
  refine ⟨_, _, WB, 64, EqHashModel.M0_laws, typedmemclr_impl WB 64, wstate r, rfl,
    wstate_tPre _ 2 (by decide), ?_, ?_, ?_⟩ <;> simp only [h0, wstate_mem]
  · exact ht1
  · exact ht2
  · rw [h1, ht3]; exact wstate_dest _ 2 _ _ (by decide) (by decide)

/-- `BulkBarrierOff` is satisfiable (all three arguments `DST`, aligned). -/
theorem bulkBarrierOff_satisfiable : ∃ (M : MemModel) (impl : List Segment) (wb d : Nat), M.Laws ∧
    BulkBarrierOff (toy.link impl) A0 M wb d ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (TPre M wb d 4 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 1).toNat % 8 = 0 ∧
        (s.regs 2).toNat % 8 = 0) :=
  ⟨_, _, WB, 64, EqHashModel.M0_laws, bulkBarrierOff_impl WB 64, wstate fun _ => 0, rfl,
    wstate_tPre _ 4 (by decide), by simp [wstate], by simp [wstate], by simp [wstate]⟩

/-! ## Names for the SAT row (`audit/round9/sat_check.py` looks for `<contract>_satisfiable`) -/

/-- `typedmemmove` under the name of its contract. -/
theorem typedMemmove_satisfiable : type_of% @typedmemmove_satisfiable := @typedmemmove_satisfiable

/-- `typedmemclr` under the name of its contract. -/
theorem typedMemclr_satisfiable : type_of% @typedmemclr_satisfiable := @typedmemclr_satisfiable

end Janus.Contracts.MemSat
