import Janus.Contracts.MemAmd64
import Janus.Contracts.EqHashModel
import Janus.Contracts.IfaceSatAmd64
import Janus.Amd64.TacticFloat

/-!
# The equality and typed-memory contracts are satisfiable (amd64)

As `Janus.Contracts.IfaceSatAmd64` for the contracts of `Janus.Contracts.MemAmd64`: for every
contract x86-64 machine code (its bytes below, from GNU `as`) at the address `A0` of a program with
no other code (`IfaceSatAmd64.toy`), a proof that it satisfies the contract (for every stack bound
and write-barrier address; with `EqHashModel.M0` for the typed-memory contracts and
`IfaceModel.R0` for the interface ones), and a call state over `EqHashModel.wmem` (`wstate`) that
satisfies the precondition.

The comparisons of `n` bytes run a byte loop (`memequal_loop` and its copies, by induction on the
bytes left from the loop head); `memmove` copies with `REP MOVSB`, forwards when `dst ≤ src` and
backwards (`STD`) otherwise, so overlapping ranges are copied correctly (`copyLE_bytes`,
`copyB_bytes`); the clears use `REP STOSB`. The float comparisons use `UCOMISS`/`UCOMISD` with
Go's `MXCSR` (`comis_feq`), whose exception flags they may raise (`mxKeep`).
-/

namespace Janus.Contracts.MemSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.MemAmd64
  Janus.Contracts.IfaceSatAmd64 Janus.Contracts.EqHashModel
open Janus (MemFrame InRanges Outside outside_cons outside_nil)
open Janus.Contracts.Mem (BoolRes MemModel WriteBarrierOff Copied Zeroed feq strEq strPtr strLen)

/-- The witness call state over `EqHashModel.wmem`. -/
def wstate (r : Nat → W64) : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 IfaceModel.wsp else if i = 14 then
      BitVec.ofNat 64 IfaceModel.wg else r i,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := wmem }

theorem wstate_eqPre (r : Nat → W64) (n : Nat) (hn : n ≤ 4) : EqPre 64 n (wstate r) := by
  have hw : wmem.accessible (IfaceModel.wsp - 64) (64 + 8 + 8 * 4) true = true := by decide
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_⟩, ?_⟩
  · show IfaceModel.wg + 16 + 8 ≤ 2 ^ 48; decide
  · show wmem.accessible (IfaceModel.wg + 16) 8 false = true; decide
  · show wmem.readLE (IfaceModel.wg + 16) 8 + 64 < IfaceModel.wsp; decide
  · show IfaceModel.wsp % 8 = 0; decide
  · show 64 ≤ IfaceModel.wsp; decide
  · show IfaceModel.wsp + 8 + 8 * n ≤ 2 ^ 48; simp [IfaceModel.wsp]; omega
  · show wmem.accessible (IfaceModel.wsp - 64) (64 + 8 + 8 * n) true = true
    exact Janus.Arm64.Memory.accessible_mono _ hw (by simp) (by simp; omega)
  · show wmem.readLE IfaceModel.wsp 8 < 2 ^ 47; decide
  · simp only [MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    simp [wstate, IfaceModel.wsp, IfaceModel.wg]; omega

theorem wstate_ifacePre (r : Nat → W64) : IfacePre IfaceModel.R0 64 (wstate r) := by
  obtain ⟨hg, hc, ho⟩ := wstate_eqPre r 2 (by decide)
  refine ⟨wmem_env0 ((wstate r).regs 14), hg, hc, ?_, ho⟩
  simp [wstate, IfaceModel.wsp]

theorem wstate_tPre (r : Nat → W64) (n : Nat) (hn : n ≤ 4) :
    TPre EqHashModel.M0 WB 64 n (wstate r) := by
  obtain ⟨hg, hc, ho⟩ := wstate_eqPre r n hn
  refine ⟨trivial, hg, hc, trivial, ⟨by decide, show wmem.accessible WB 4 false = true by decide,
      ?_⟩,
    wmem_wbOff, ho, trivial⟩
  simp only [MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
  simp [wstate, IfaceModel.wsp, WB]

/-- A state that keeps what every runtime call keeps (amd64) is a `MemAmd64.retState`. -/
theorem retState_of {s s' : State} (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s)
    (hfs : s'.fsBase = s.fsBase) (hdf : s.df = false) (hdf' : s'.df = false)
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) :
    s' = MemAmd64.retState s s'.regs s'.xmm s'.ymmHi s'.flags s'.mxcsr s'.mem := by
  obtain ⟨r, rip, fl, xmm, mem, yh, fsb, df, mx, x8, fw⟩ := s'
  simp only at hsp h5 h14 hx hrip hfs hdf' hx87 hfw ⊢
  subst hrip hfs hdf' hx87 hfw
  simp only [MemAmd64.retState, State.mk.injEq, and_true, true_and, hdf]
  refine ⟨?_, ?_⟩
  · funext i
    simp only [MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact hsp
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-- The return of a model implementation as `IfaceRet`. -/
theorem ifaceRet_of {R : Janus.Spec.Type.IfaceModel} {d : Nat} {s s' : State} {P : (Nat → W64) →
    Prop}
    (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s) (hfs : s'.fsBase = s.fsBase)
    (hdf : s.df = false) (hdf' : s'.df = false) (hmx : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64)
    (hf : MemFrame s.mem s'.mem (R.priv ++ MemAmd64.calleeStack s d 2))
    (he : R.Env s'.mem (s.regs 14)) (hp : P s'.regs)
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) : IfaceRet R d s s' P :=
  ⟨_, _, _, _, _, _, retState_of hsp h5 h14 hx hrip hfs hdf hdf' hx87 hfw, hmx, hf, he, hp⟩

/-- The return of a model implementation as `TRet`. -/
theorem tRet_of {M : MemModel} {d nargs : Nat} {extra : List (Nat × Nat)} {s s' : State}
    {P : Janus.Arm64.Memory → Prop}
    (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s) (hfs : s'.fsBase = s.fsBase)
    (hdf : s.df = false) (hdf' : s'.df = false) (hmx : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64)
    (hf : MemFrame s.mem s'.mem (M.priv ++ MemAmd64.calleeStack s d nargs ++ extra))
    (he : M.Env s'.mem (s.regs 14)) (hp : P s'.mem)
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) : TRet M d nargs extra s s' P :=
  ⟨_, _, _, _, _, _, retState_of hsp h5 h14 hx hrip hfs hdf hdf' hx87 hfw, hmx, hf, he, hp⟩

/-- The return of a model implementation as `EqRet`. -/
theorem eqRet_of {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s) (hfs : s'.fsBase = s.fsBase)
    (hdf : s.df = false) (hdf' : s'.df = false) (hmx : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64)
    (hf : MemFrame s.mem s'.mem (MemAmd64.calleeStack s d nargs)) (hp : P s'.regs)
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) : EqRet d nargs
        s s' P :=
  EqRet.intro hsp h5 h14 hx hrip hfs (hdf'.trans hdf.symm) hmx hf hp hx87 hfw

/-- `SETE` after `CMP x, y` of `w`-bit values, read back: `x == y`. -/
theorem setcc_eq {N x y : Nat} (hx : x < N) (hy : y < N) :
    (if (N - y + x) % N = 0 then 1#8 else 0#8).toNat = (x == y).toNat := by
  by_cases h : x = y
  · subst h; simp [Nat.sub_add_cancel (Nat.le_of_lt hy)]
  · rw [ite_eq_right (by
      intro h'
      rcases Nat.lt_or_ge x y with hl | hl
      · rw [Nat.mod_eq_of_lt (by omega)] at h'; omega
      · rw [show N - y + x = (x - y) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          at h'
        omega)]
    cases hb : (x == y) <;> simp_all

/-- Close the `EqRet` of a straight-line comparison (no stack, memory unchanged). -/
macro "eq_close" hdf:term : tactic => `(tactic| (
  refine eqRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl $hdf rfl rfl (MemFrame.refl _ _) ?_))

/-- `(if c then 1 else 0).toNat` -/
theorem ite_one_zero_toNat (c : Prop) [Decidable c] :
    (if c then 1#8 else 0#8).toNat = (decide c).toNat := by
  by_cases h : c <;> simp [h]

/-- A `CMP` of `w`-bit values that sets `ZF`. -/
theorem dec_sub_eq_zero {w : Nat} (e y : BitVec w) : decide (e - y = 0#w) = (e.toNat == y.toNat) :=
    by
  by_cases h : e = y
  · subst h; simp
  · have : e.toNat ≠ y.toNat := fun h' => h (BitVec.eq_of_toNat_eq h')
    simp only [beq_false_of_ne this, decide_eq_false_iff_not]
    intro h'; exact h (by simpa using BitVec.sub_eq_iff_eq_add.1 h')

/-! ## `memequal0/8/16/32/64/128` -/

/-- `mov $1, %eax; ret`. -/
def memequal0Code : List Nat := [0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]

theorem memequal0_impl (d : Nat) : MemequalN (toy.link (at0 memequal0Code)) A0 d 0 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, _, _⟩
  janus64_run
  eq_close hdf
  simp [BoolRes, setRegF]

/-- `movzbl (%rax), %edx; cmp (%rbx), %dl; sete %al; ret`. -/
def memequal8Code : List Nat := [0x0f, 0xb6, 0x10, 0x3a, 0x13, 0x0f, 0x94, 0xc0, 0xc3]

theorem memequal8_impl (d : Nat) : MemequalN (toy.link (at0 memequal8Code)) A0 d 1 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus64_run
  eq_close hdf
  simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, IfaceAmd64.setcc_low_byte,
    ite_one_zero_toNat, dec_sub_eq_zero]
  have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 1
  have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 1
  simp only [Nat.reducePow] at ha hb
  congr 2 <;> simp <;> omega

/-- `movzwl (%rax), %edx; cmp (%rbx), %dx; sete %al; ret`. -/
def memequal16Code : List Nat := [0x0f, 0xb7, 0x10, 0x66, 0x3b, 0x13, 0x0f, 0x94, 0xc0, 0xc3]

theorem memequal16_impl (d : Nat) : MemequalN (toy.link (at0 memequal16Code)) A0 d 2 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus64_run
  eq_close hdf
  simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, IfaceAmd64.setcc_low_byte,
    ite_one_zero_toNat, dec_sub_eq_zero]
  have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 2
  have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 2
  simp only [Nat.reducePow] at ha hb
  congr 2 <;> simp <;> omega

/-- `mov (%rax), %edx; cmp (%rbx), %edx; sete %al; ret`. -/
def memequal32Code : List Nat := [0x8b, 0x10, 0x3b, 0x13, 0x0f, 0x94, 0xc0, 0xc3]

theorem memequal32_impl (d : Nat) : MemequalN (toy.link (at0 memequal32Code)) A0 d 4 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus64_run
  eq_close hdf
  simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, IfaceAmd64.setcc_low_byte,
    ite_one_zero_toNat, dec_sub_eq_zero]
  have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 4
  have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 4
  simp only [Nat.reducePow] at ha hb
  congr 2 <;> simp <;> omega

/-- `mov (%rax), %rdx; cmp (%rbx), %rdx; sete %al; ret`. -/
def memequal64Code : List Nat := [0x48, 0x8b, 0x10, 0x48, 0x3b, 0x13, 0x0f, 0x94, 0xc0, 0xc3]

theorem memequal64_impl (d : Nat) : MemequalN (toy.link (at0 memequal64Code)) A0 d 8 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus64_run
  eq_close hdf
  have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
  simp only [Nat.reducePow] at ha hb
  simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, IfaceAmd64.setcc_low_byte]
  rw [setcc_eq ha hb]
  
/-- `mov (%rax), %rdx; cmp (%rbx), %rdx; jne 1f; mov 8(%rax), %rdx; cmp 8(%rbx), %rdx;
sete %al; ret; 1: xor %eax, %eax; ret`. -/
def memequal128Code : List Nat :=
  [0x48, 0x8b, 0x10, 0x48, 0x3b, 0x13, 0x75, 0x0c, 0x48, 0x8b, 0x50, 0x08, 0x48, 0x3b, 0x53, 0x08,
   0x0f, 0x94, 0xc0, 0xc3, 0x31, 0xc0, 0xc3]

theorem memequal128_impl (d : Nat) : MemequalN (toy.link (at0 memequal128Code)) A0 d 16 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
  have ha' := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 8) 8
  have hb' := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 3).toNat + 8) 8
  simp only [Nat.reducePow] at ha hb ha' hb'
  simp only [Janus.Arm64.Memory.readLE_sixteen]
  janus64_run
  all_goals eq_close hdf
  all_goals simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, IfaceAmd64.setcc_low_byte]
  · rw [setcc_eq ha' hb']
    have e : Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 =
      Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8 := by omega
    rw [e]
    by_cases h : Janus.Arm64.Memory.readLE s.mem ((s.regs 0).toNat + 8) 8 =
      Janus.Arm64.Memory.readLE s.mem ((s.regs 3).toNat + 8) 8
    · simp [h]
    · simp only [beq_false_of_ne h, Bool.toNat_false]
      rw [beq_false_of_ne (by omega)]; rfl
  · rw [beq_false_of_ne (by omega)]; rfl

/-! ## Floating-point and complex equality -/

/-- Raising exception flags keeps the control bits of `MXCSR`. -/
theorem mxKeep (m : BitVec 32) (x : Nat) :
    (BitVec.ofNat 32 (m.toNat ||| x % 64)).toNat / 64 = m.toNat / 64 := by
  rw [BitVec.toNat_ofNat, Janus.Amd64.Tactic.mx_raise_div, Nat.mod_eq_of_lt m.isLt]

/-- Two raises keep the control bits of `MXCSR`. -/
theorem mxKeep2 (m : BitVec 32) (x y : Nat) :
    (BitVec.ofNat 32 ((m.toNat ||| x % 64) % 4294967296 ||| y % 64)).toNat / 64 = m.toNat / 64 := by
  rw [BitVec.toNat_ofNat, Janus.Amd64.Tactic.mx_raise_div, Nat.mod_mod,
    Janus.Amd64.Tactic.mx_raise_div, Nat.mod_eq_of_lt m.isLt]

/-- `ANDL` of two registers, read back as the low byte. -/
theorem and_low (X Y : BitVec 64) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 X &&& BitVec.setWidth 32 Y)).toNat % 256 =
      (X.toNat % 256) &&& (Y.toNat % 256) := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 64),
    Nat.and_mod_two_pow, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 32),
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 32)]

theorem ite_zero_one_toNat (c : Prop) [Decidable c] :
    (if c then 0#8 else 1#8).toNat = (!decide c).toNat := by
  by_cases h : c <;> simp [h]

theorem bool_and_toNat (a b : Bool) : a.toNat &&& b.toNat = (a && b).toNat := by
  cases a <;> cases b <;> rfl

/-- `movss (%rax), %xmm0; ucomiss (%rbx), %xmm0; sete %al; setnp %cl; and %ecx, %eax; ret`. -/
def f32equalCode : List Nat :=
  [0xf3, 0x0f, 0x10, 0x00, 0x0f, 0x2e, 0x03, 0x0f, 0x94, 0xc0, 0x0f, 0x9b, 0xc1, 0x21, 0xc8, 0xc3]

theorem f32equal_impl (d : Nat) : Fequal (toy.link (at0 f32equalCode)) A0 d Janus.Float.binary32 4
    := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, hm, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2,
      hb3⟩⟩
  janus64_run [Janus.Amd64.Tactic.GoMXCSR.ctl hm, Janus.Amd64.Tactic.GoMXCSR.unmasked hm,
    Janus.Amd64.Tactic.GoMXCSR.mod hm]
  refine eqRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl ?_ (MemFrame.refl _ _) ?_
  · dsimp only; simp only [mxKeep]
  · have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 4
    simp only [Nat.reducePow] at ha
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, and_low, IfaceAmd64.setcc_low_byte,
      ite_one_zero_toNat, ite_zero_one_toNat, bool_and_toNat, comis_feq, Nat.mod_eq_of_lt ha]

/-- `movsd (%rax), %xmm0; ucomisd (%rbx), %xmm0; sete %al; setnp %cl; and %ecx, %eax; ret`. -/
def f64equalCode : List Nat :=
  [0xf2, 0x0f, 0x10, 0x00, 0x66, 0x0f, 0x2e, 0x03, 0x0f, 0x94, 0xc0, 0x0f, 0x9b, 0xc1, 0x21, 0xc8,
   0xc3]

theorem f64equal_impl (d : Nat) : Fequal (toy.link (at0 f64equalCode)) A0 d Janus.Float.binary64 8
    := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, hm, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2,
      hb3⟩⟩
  janus64_run [Janus.Amd64.Tactic.GoMXCSR.ctl hm, Janus.Amd64.Tactic.GoMXCSR.unmasked hm,
    Janus.Amd64.Tactic.GoMXCSR.mod hm]
  refine eqRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl ?_ (MemFrame.refl _ _) ?_
  · dsimp only; simp only [mxKeep]
  · have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
    simp only [Nat.reducePow] at ha
    have ha2 : Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 <
        340282366920938463463374607431768211456 := by omega
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, and_low, IfaceAmd64.setcc_low_byte,
      ite_one_zero_toNat, ite_zero_one_toNat, bool_and_toNat, comis_feq, Nat.mod_eq_of_lt ha2]

/-- `movss (%rax), %xmm0; ucomiss (%rbx), %xmm0; sete %dl; setnp %cl; and %ecx, %edx;
movss 4(%rax), %xmm0; ucomiss 4(%rbx), %xmm0; sete %al; setnp %cl; and %ecx, %eax;
and %edx, %eax; ret`. -/
def c64equalCode : List Nat :=
  [0xf3, 0x0f, 0x10, 0x00, 0x0f, 0x2e, 0x03, 0x0f, 0x94, 0xc2, 0x0f, 0x9b, 0xc1, 0x21, 0xca, 0xf3,
   0x0f, 0x10, 0x40, 0x04, 0x0f, 0x2e, 0x43, 0x04, 0x0f, 0x94, 0xc0, 0x0f, 0x9b, 0xc1, 0x21, 0xc8,
   0x21, 0xd0, 0xc3]

theorem c64equal_impl (d : Nat) : Cequal (toy.link (at0 c64equalCode)) A0 d Janus.Float.binary32 4
    := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, hm, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2,
      hb3⟩⟩
  janus64_run [Janus.Amd64.Tactic.GoMXCSR.ctl hm, Janus.Amd64.Tactic.GoMXCSR.unmasked hm,
    Janus.Amd64.Tactic.GoMXCSR.mod hm]
  refine eqRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl ?_ (MemFrame.refl _ _) ?_
  · dsimp only; rw [mxKeep2]
  · have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 4
    have ha' := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 4) 4
    simp only [Nat.reducePow] at ha ha'
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, and_low, IfaceAmd64.setcc_low_byte,
      ite_one_zero_toNat, ite_zero_one_toNat, bool_and_toNat, comis_feq, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt ha']
    rw [Bool.and_comm]

/-- `movsd (%rax), %xmm0; ucomisd (%rbx), %xmm0; sete %dl; setnp %cl; and %ecx, %edx;
movsd 8(%rax), %xmm0; ucomisd 8(%rbx), %xmm0; sete %al; setnp %cl; and %ecx, %eax;
and %edx, %eax; ret`. -/
def c128equalCode : List Nat :=
  [0xf2, 0x0f, 0x10, 0x00, 0x66, 0x0f, 0x2e, 0x03, 0x0f, 0x94, 0xc2, 0x0f, 0x9b, 0xc1, 0x21, 0xca,
   0xf2, 0x0f, 0x10, 0x40, 0x08, 0x66, 0x0f, 0x2e, 0x43, 0x08, 0x0f, 0x94, 0xc0, 0x0f, 0x9b, 0xc1,
   0x21, 0xc8, 0x21, 0xd0, 0xc3]

theorem c128equal_impl (d : Nat) :
    Cequal (toy.link (at0 c128equalCode)) A0 d Janus.Float.binary64 8 := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, hm, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2,
      hb3⟩⟩
  janus64_run [Janus.Amd64.Tactic.GoMXCSR.ctl hm, Janus.Amd64.Tactic.GoMXCSR.unmasked hm,
    Janus.Amd64.Tactic.GoMXCSR.mod hm]
  refine eqRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl ?_ (MemFrame.refl _ _) ?_
  · dsimp only; rw [mxKeep2]
  · have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
    have ha' := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 8) 8
    simp only [Nat.reducePow] at ha ha'
    have hc : Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 <
      340282366920938463463374607431768211456 := by omega
    have hc' : Janus.Arm64.Memory.readLE s.mem ((s.regs 0).toNat + 8) 8 <
      340282366920938463463374607431768211456 := by omega
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, and_low, IfaceAmd64.setcc_low_byte,
      ite_one_zero_toNat, ite_zero_one_toNat, bool_and_toNat, comis_feq, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt hc']
    rw [Bool.and_comm]

/-! ## Interfaces -/

/-- `mov (%rax), %rdx; cmp (%rbx), %rdx; jne 1f; test %rdx, %rdx; jz 2f; mov 8(%rax), %rax;
mov 8(%rbx), %rbx; mov (%rax), %rdx; cmp (%rbx), %rdx; sete %al; ret; 1: xor %eax, %eax; ret;
2: mov $1, %eax; ret`: equal first words, then (for a non-nil one) the 8-byte values the data
words point to, as `TD`'s equality in `IfaceModel.R0`. -/
def interequalCode : List Nat :=
  [0x48, 0x8b, 0x10, 0x48, 0x3b, 0x13, 0x75, 0x17, 0x48, 0x85, 0xd2, 0x74, 0x15, 0x48, 0x8b, 0x40,
   0x08, 0x48, 0x8b, 0x5b, 0x08, 0x48, 0x8b, 0x10, 0x48, 0x3b, 0x13, 0x0f, 0x94, 0xc0, 0xc3, 0x31,
   0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]

theorem nilinterequal_impl (d : Nat) :
    Nilinterequal (toy.link (at0 interequalCode)) A0 IfaceModel.R0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo⟩, ⟨ha1, ha2, ha3⟩,
    ⟨hb1, hb2, hb3⟩, hok⟩
  have he0 : IfaceModel.Env0 s.mem (s.regs 14) := henv
  have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
  simp only [Nat.reducePow] at ha hb
  by_cases heq : Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 =
      Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8
  · by_cases h0 : Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 = 0
    · janus64_run
      refine ifaceRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
        (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) he0 ?_
      simp [BoolRes, setRegF, Iface.efaceEqual]
    · obtain ⟨hok1, -⟩ := hok heq
      obtain ⟨-, htd, hx, hy⟩ := hok1 h0
      janus64_run
      refine ifaceRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
        (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) he0 ?_
      rw [← heq, htd, IfaceSat.efaceEqual_R0 he0]
      have hx' := Janus.Arm64.Memory.readLE_lt s.mem
        (Janus.Arm64.Memory.readLE s.mem ((s.regs 0).toNat + 8) 8) 8
      have hy' := Janus.Arm64.Memory.readLE_lt s.mem
        (Janus.Arm64.Memory.readLE s.mem ((s.regs 3).toNat + 8) 8) 8
      simp only [Nat.reducePow] at hx' hy'
      simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, IfaceAmd64.setcc_low_byte]
      rw [setcc_eq hx' hy']
  · janus64_run
    refine ifaceRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) he0 ?_
    simp [BoolRes, setRegF, beq_false_of_ne heq]

theorem interequal_impl (d : Nat) :
    Interequal (toy.link (at0 interequalCode)) A0 IfaceModel.R0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo⟩, ⟨ha1, ha2, ha3⟩,
    ⟨hb1, hb2, hb3⟩, hok⟩
  have he0 : IfaceModel.Env0 s.mem (s.regs 14) := henv
  have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
  simp only [Nat.reducePow] at ha hb
  by_cases heq : Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 =
      Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8
  · by_cases h0 : Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 = 0
    · janus64_run
      refine ifaceRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
        (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) he0 ?_
      simp [BoolRes, setRegF, Iface.ifaceEqual]
    · obtain ⟨-, ht0, hok1, -⟩ := hok heq h0
      obtain ⟨-, htd, hx, hy⟩ := hok1 ht0
      janus64_run
      refine ifaceRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
        (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) he0 ?_
      rw [← heq]
      simp only [Iface.ifaceEqual, beq_false_of_ne h0, Bool.false_or]
      rw [htd, IfaceSat.efaceEqual_R0 he0]
      have hx' := Janus.Arm64.Memory.readLE_lt s.mem
        (Janus.Arm64.Memory.readLE s.mem ((s.regs 0).toNat + 8) 8) 8
      have hy' := Janus.Arm64.Memory.readLE_lt s.mem
        (Janus.Arm64.Memory.readLE s.mem ((s.regs 3).toNat + 8) 8) 8
      simp only [Nat.reducePow] at hx' hy'
      simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, IfaceAmd64.setcc_low_byte]
      rw [setcc_eq hx' hy']
  · janus64_run
    refine ifaceRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) he0 ?_
    simp [BoolRes, setRegF, beq_false_of_ne heq]

/-! ## Copying and clearing with `REP MOVSB` / `REP STOSB` -/

section Rep


/-- `REP MOVSB`/`REP STOSB` (`DF = 0`) in a `ReachesRet` goal, as `Reaches.repMovs`. -/
theorem ReachesRet.repMovsb {p : Janus.Amd64.Program} {ret : W64} {t : State} {Q : State → Prop} {c
    len : Nat}
    (hpc : t.rip = BitVec.ofNat 64 c) (hok : stepOKAt p c (.movs true 8) len = true) (a b k : Nat)
    (hdf : t.df = false) (h7 : t.regs 7 = BitVec.ofNat 64 a) (h6 : t.regs 6 = BitVec.ofNat 64 b)
    (h1 : t.regs 1 = BitVec.ofNat 64 k) (hk : k < 2 ^ 64)
    (hacc : t.mem.accessible a k true = true) (hsrc : t.mem.accessible b k false = true)
    (hnw : a + k < 2 ^ 64) (hnw' : b + k < 2 ^ 64)
    (h : ReachesRet p ret
      (((({ t with mem := copyLE t.mem a b 1 k }.setReg 6
        (BitVec.ofNat 64 (b + 1 * k))).setReg 7 (BitVec.ofNat 64 (a + 1 * k))).setReg 1 0).setRip
        (BitVec.ofNat 64 ((t.rip.toNat + len) % 2 ^ 64))) Q) :
    ReachesRet p ret t Q := by
  obtain ⟨bs, hok⟩ := stepOKAt_spec hok
  refine ReachesRet.step hpc hok rfl ?_
  have h1' : (t.regs 1).toNat = k := by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  simp only [exec, ite_true, hdf, Bool.false_eq_true, ite_false, h1',
    movsIter_ok 1 k t a b h7 h6 (by simpa using hacc) (by simpa using hsrc) (by simpa using hnw)
      (by simpa using hnw')]
  rw [hdf] at h; exact h

theorem ReachesRet.repStosb {p : Janus.Amd64.Program} {ret : W64} {t : State} {Q : State → Prop} {c
    len : Nat}
    (hpc : t.rip = BitVec.ofNat 64 c) (hok : stepOKAt p c (.stos true 8) len = true) (a k : Nat)
    (hdf : t.df = false) (h7 : t.regs 7 = BitVec.ofNat 64 a) (h1 : t.regs 1 = BitVec.ofNat 64 k)
    (hk : k < 2 ^ 64) (hacc : t.mem.accessible a k true = true) (hnw : a + k < 2 ^ 64)
    (h : ReachesRet p ret
      ((({ t with mem := fillLE t.mem a 1 (t.getReg 8 0).toNat k }.setReg 7
        (BitVec.ofNat 64 (a + 1 * k))).setReg 1 0).setRip
        (BitVec.ofNat 64 ((t.rip.toNat + len) % 2 ^ 64))) Q) :
    ReachesRet p ret t Q := by
  obtain ⟨bs, hok⟩ := stepOKAt_spec hok
  refine ReachesRet.step hpc hok rfl ?_
  have h1' : (t.regs 1).toNat = k := by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  simp only [exec, ite_true, hdf, Bool.false_eq_true, ite_false, h1',
    stosIter_ok 1 _ k t a h7 (by simpa using hacc) (by simpa using hnw)]
  rw [hdf] at h; exact h

/-- The memory after `k` backward `MOVSB` steps from `b` down to `a` (`DF = 1`). -/
def copyB (M : Janus.Arm64.Memory) (a b : Nat) : Nat → Janus.Arm64.Memory
  | 0 => M
  | k + 1 => copyB (M.writeLE a 1 (M.readLE b 1)) (a - 1) (b - 1) k

theorem regions_copyB (M : Janus.Arm64.Memory) (a b k : Nat) : (copyB M a b k).regions = M.regions
    := by
  induction k generalizing M a b with
  | zero => rfl
  | succ k ih => exact ih _ _ _

theorem accessible_copyB (M : Janus.Arm64.Memory) (a b k c n : Nat) (w : Bool) :
    (copyB M a b k).accessible c n w = M.accessible c n w :=
  Janus.Arm64.Memory.accessible_congr (regions_copyB M a b k) c n w

/-- `k` element steps of `MOVSB` with `DF = 1` from `RSI = b` to `RDI = a`. -/
theorem movsIterB_ok : ∀ (k : Nat) (t : State) (a b : Nat), (t.regs 7).toNat = a →
    (t.regs 6).toNat = b → k ≤ a + 1 → k ≤ b + 1 →
    t.mem.accessible (a + 1 - k) k true = true → t.mem.accessible (b + 1 - k) k false = true →
    movsIterB 1 k t = .ok (({ t with mem := copyB t.mem a b k }.setReg 6
      (t.regs 6 - BitVec.ofNat 64 k)).setReg 7 (t.regs 7 - BitVec.ofNat 64 k))
  | 0, t, a, b, _, _, _, _, _, _ => by
    simp only [movsIterB, copyB, Except.ok.injEq]
    refine State.ext' ?_ rfl rfl rfl rfl
    funext i; simp only [State.setReg]; split <;> (try split) <;> simp_all
  | k + 1, t, a, b, h7, h6, hka, hkb, hacc, hsrc => by
    have hld : load t.mem (t.regs 6).toNat 1 = .ok (t.mem.readLE b 1) := by
      rw [h6]; exact load_ok _ (Janus.Arm64.Memory.accessible_sub _ hsrc (Or.inl rfl) (by omega)
          (by omega))
    have hst : store t.mem (t.regs 7).toNat 1 (t.mem.readLE b 1) =
        .ok (t.mem.writeLE a 1 (t.mem.readLE b 1)) := by
      rw [h7]; exact store_ok _ _ (Janus.Arm64.Memory.accessible_sub _ hacc (Or.inr rfl) (by omega)
          (by omega))
    simp only [movsIterB, hld, hst]
    have ha := (t.regs 7).isLt
    have hb := (t.regs 6).isLt
    rcases k with _ | k
    · simp only [movsIterB, copyB]
    · rw [movsIterB_ok (k + 1) _ (a - 1) (b - 1)
        (by simp only [State.setReg, reduceIte, Nat.reduceEqDiff, BitVec.toNat_sub,
            BitVec.toNat_ofNat]
            omega)
        (by simp only [State.setReg, reduceIte, Nat.reduceEqDiff, BitVec.toNat_sub,
            BitVec.toNat_ofNat]
            omega)
        (by omega) (by omega)
        (by simp only [State.setReg, Janus.Arm64.Memory.accessible_writeLE]
            exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inr rfl) (by omega) (by omega))
        (by simp only [State.setReg, Janus.Arm64.Memory.accessible_writeLE]
            exact Janus.Arm64.Memory.accessible_sub _ hsrc (Or.inl rfl) (by omega) (by omega))]
      congr 1
      refine State.ext' ?_ rfl rfl rfl ?_
      · funext i; simp only [State.setReg]
        split
        · rename_i hi; subst hi; simp only [↓reduceIte]; bv_omega
        · split
          · rename_i hi; subst hi; simp only [↓reduceIte, Nat.reduceEqDiff]; bv_omega
          · rfl
      · simp [State.setReg, copyB]

theorem ReachesRet.repMovsbB {p : Janus.Amd64.Program} {ret : W64} {t : State} {Q : State → Prop}
    {c len : Nat}
    (hpc : t.rip = BitVec.ofNat 64 c) (hok : stepOKAt p c (.movs true 8) len = true) (a b k : Nat)
    (hdf : t.df = true) (h7 : (t.regs 7).toNat = a) (h6 : (t.regs 6).toNat = b)
    (h1 : t.regs 1 = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) (hka : k ≤ a + 1) (hkb : k ≤ b + 1)
    (hacc : t.mem.accessible (a + 1 - k) k true = true)
    (hsrc : t.mem.accessible (b + 1 - k) k false = true)
    (h : ReachesRet p ret
      (((({ t with mem := copyB t.mem a b k }.setReg 6
        (t.regs 6 - BitVec.ofNat 64 k)).setReg 7 (t.regs 7 - BitVec.ofNat 64 k)).setReg 1 0).setRip
        (BitVec.ofNat 64 ((t.rip.toNat + len) % 2 ^ 64))) Q) :
    ReachesRet p ret t Q := by
  obtain ⟨bs, hok⟩ := stepOKAt_spec hok
  refine ReachesRet.step hpc hok rfl ?_
  have h1' : (t.regs 1).toNat = k := by rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  simp only [exec, ite_true, hdf, h1', show (8 : Nat) / 8 = 1 from rfl,
    movsIterB_ok k t a b h7 h6 hka hkb hacc hsrc]
  rw [hdf] at h; exact h

/-! ### What the copies and fills leave in memory -/

theorem copyLE_bytes_out (M : Janus.Arm64.Memory) (a b k x : Nat) (h : x < a ∨ a + k ≤ x) :
    (copyLE M a b 1 k).bytes x = M.bytes x := by
  induction k generalizing M a b with
  | zero => rfl
  | succ k ih =>
    simp only [copyLE]
    rw [ih _ _ _ (by omega), Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]

theorem copyLE_bytes (M : Janus.Arm64.Memory) (a b k : Nat) (hab : a ≤ b) :
    ∀ i, i < k → (copyLE M a b 1 k).bytes (a + i) = M.bytes (b + i) := by
  induction k generalizing M a b with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    simp only [copyLE]
    rcases i with _ | j
    · rw [copyLE_bytes_out _ _ _ _ _ (Or.inl (by omega)), Nat.add_zero, Nat.add_zero,
        Janus.Arm64.Memory.bytes_writeLE_inside _ (by omega) (by omega)]
      simp
    · rw [show a + (j + 1) = a + 1 + j by omega, ih _ _ _ (by omega) j (by omega),
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega), show b + 1 + j = b + (j + 1) by
            omega]

theorem copyB_bytes_out (M : Janus.Arm64.Memory) (a b k x : Nat) (h : a < x ∨ x + k ≤ a) :
    (copyB M a b k).bytes x = M.bytes x := by
  induction k generalizing M a b with
  | zero => rfl
  | succ k ih =>
    simp only [copyB]
    rw [ih _ _ _ (by omega), Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]

theorem copyB_bytes (M : Janus.Arm64.Memory) (a b k : Nat) (hab : b ≤ a) (hk : k ≤ b + 1) :
    ∀ i, i < k → (copyB M a b k).bytes (a - i) = M.bytes (b - i) := by
  induction k generalizing M a b with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    simp only [copyB]
    rcases i with _ | j
    · rcases k with _ | k
      · simp only [copyB, Nat.sub_zero]
        rw [Janus.Arm64.Memory.bytes_writeLE_inside _ (by omega) (by omega)]; simp
      · rw [copyB_bytes_out _ _ _ _ _ (Or.inl (by omega)), Nat.sub_zero, Nat.sub_zero,
          Janus.Arm64.Memory.bytes_writeLE_inside _ (by omega) (by omega)]
        simp
    · rw [show a - (j + 1) = a - 1 - j by omega, ih _ _ _ (by omega) (by omega) j (by omega),
        Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega), show b - 1 - j = b - (j + 1) by
            omega]

/-- A byte-wise frame gives a `MemFrame` with the changed range as an extra range. -/
theorem memFrame_of_bytes {m m' : Janus.Arm64.Memory} {ws : List (Nat × Nat)} {a n : Nat}
    (hr : m'.regions = m.regions) (hb : ∀ x, (x < a ∨ a + n ≤ x) → m'.bytes x = m.bytes x) :
    MemFrame m m' (ws ++ [(a, a + n)]) :=
  ⟨fun b k hout => by
    simp only [Janus.outside_append, outside_cons, outside_nil, and_true] at hout
    exact Janus.Arm64.Memory.readLE_congr fun i hi => hb _ (by omega),
   fun b k w => Janus.Arm64.Memory.accessible_congr hr b k w⟩

end Rep

/-! ## `memmove` and `typedmemmove` -/

/-- `test %rcx, %rcx; jz 1f; mov %rax, %rdi; mov %rbx, %rsi; cmp %rsi, %rdi; ja 2f; rep movsb;
1: ret; 2: lea -1(%rdi,%rcx), %rdi; lea -1(%rsi,%rcx), %rsi; std; rep movsb; cld; ret`: copy
forwards when `dst ≤ src`, backwards otherwise (so overlapping ranges are copied correctly). -/
def memmoveCode : List Nat :=
  [0x48, 0x85, 0xc9, 0x74, 0x0d, 0x48, 0x89, 0xc7, 0x48, 0x89, 0xde, 0x48, 0x39, 0xf7, 0x77, 0x03,
   0xf3, 0xa4, 0xc3, 0x48, 0x8d, 0x7c, 0x0f, 0xff, 0x48, 0x8d, 0x74, 0x0e, 0xff, 0xfd, 0xf3, 0xa4,
   0xfc, 0xc3]

theorem memmove_impl (d : Nat) : Memmove (toy.link (at0 memmoveCode)) A0 EqHashModel.M0 d := by
  rw [link_at0]
  intro s hpc ⟨henv, ⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, hout, ⟨hs1, hs2, hs3⟩,
    ⟨hD1, hD2, hD3, hD4, hD5⟩⟩
  have hn := (s.regs 1).isLt
  simp only [outside_cons, outside_nil, and_true] at hD5
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  janus64_run until [0x100010, 0x10001e]
  · -- `n = 0`
    refine tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) trivial ?_
    intro i hi; omega
  · -- `dst > src`: backwards
    refine ReachesRet.repMovsbB (c := 0x10001e) (len := 2) rfl rfl
      ((s.regs 0).toNat + (s.regs 1).toNat - 1) ((s.regs 3).toNat + (s.regs 1).toNat - 1)
      (s.regs 1).toNat rfl
      (by simp [setRegF, BitVec.toNat_sub, BitVec.toNat_add]; omega)
      (by simp [setRegF, BitVec.toNat_sub, BitVec.toNat_add]; omega)
      (by simp [setRegF]) hn (by omega) (by omega)
      (by rw [show (s.regs 0).toNat + (s.regs 1).toNat - 1 + 1 - (s.regs 1).toNat =
            (s.regs 0).toNat by omega]; exact hD2)
      (by rw [show (s.regs 3).toNat + (s.regs 1).toNat - 1 + 1 - (s.regs 1).toNat =
            (s.regs 3).toNat by omega]; exact hs2) ?_
    have hm1 := accessible_copyB s.mem ((s.regs 0).toNat + (s.regs 1).toNat - 1)
      ((s.regs 3).toNat + (s.regs 1).toNat - 1) (s.regs 1).toNat (s.regs 4).toNat 8 false
    have hm2 : (copyB s.mem ((s.regs 0).toNat + (s.regs 1).toNat - 1)
        ((s.regs 3).toNat + (s.regs 1).toNat - 1) (s.regs 1).toNat).readLE (s.regs 4).toNat 8 =
        s.mem.readLE (s.regs 4).toNat 8 :=
      Janus.Arm64.Memory.readLE_congr fun i hi => copyB_bytes_out _ _ _ _ _ (by omega)
    rw [hsp] at hm1
    janus64_run
    refine tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl ?_ trivial ?_
    · exact memFrame_of_bytes (regions_copyB _ _ _ _) fun x hx => copyB_bytes_out _ _ _ _ _ (by
        omega)
    · intro i hi
      have h := copyB_bytes s.mem ((s.regs 0).toNat + (s.regs 1).toNat - 1)
        ((s.regs 3).toNat + (s.regs 1).toNat - 1) (s.regs 1).toNat (by omega) (by omega)
        ((s.regs 1).toNat - 1 - i) (by omega)
      rw [show (s.regs 0).toNat + (s.regs 1).toNat - 1 - ((s.regs 1).toNat - 1 - i) =
          (s.regs 0).toNat + i by omega,
        show (s.regs 3).toNat + (s.regs 1).toNat - 1 - ((s.regs 1).toNat - 1 - i) =
          (s.regs 3).toNat + i by omega] at h
      exact h
  · -- `dst ≤ src`: forwards
    refine ReachesRet.repMovsb (c := 0x100010) (len := 2) rfl rfl (s.regs 0).toNat (s.regs 3).toNat
      (s.regs 1).toNat rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) hn hD2 hs2
      (by omega) (by omega) ?_
    have hm1 := accessible_copyLE s.mem (s.regs 0).toNat (s.regs 3).toNat 1 (s.regs 1).toNat
      (s.regs 4).toNat 8 false
    have hm2 : (copyLE s.mem (s.regs 0).toNat (s.regs 3).toNat 1 (s.regs 1).toNat).readLE
        (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
      Janus.Arm64.Memory.readLE_congr fun i hi => copyLE_bytes_out _ _ _ _ _ (by omega)
    rw [hsp] at hm1
    janus64_run
    refine tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl ?_ trivial ?_
    · exact memFrame_of_bytes (regions_copyLE _ _ _ _ _) fun x hx => copyLE_bytes_out _ _ _ _ _ hx
    · exact copyLE_bytes _ _ _ _ (by omega)


/-- `mov %rbx, %rdi; mov %rcx, %rsi; mov (%rax), %rcx` (the size `typ.Size_`), then
`memmoveCode`'s copy: `test %rcx, %rcx; jz 1f; cmp %rsi, %rdi; ja 2f; rep movsb; 1: ret;
2: lea -1(%rdi,%rcx), %rdi; lea -1(%rsi,%rcx), %rsi; std; rep movsb; cld; ret`. -/
def typedmemmoveCode : List Nat :=
  [0x48, 0x89, 0xdf, 0x48, 0x89, 0xce, 0x48, 0x8b, 0x08, 0x48, 0x85, 0xc9, 0x74, 0x07, 0x48, 0x39,
   0xf7, 0x77, 0x03, 0xf3, 0xa4, 0xc3, 0x48, 0x8d, 0x7c, 0x0f, 0xff, 0x48, 0x8d, 0x74, 0x0e, 0xff,
   0xfd, 0xf3, 0xa4, 0xfc, 0xc3]

theorem typedmemmove_impl (wb d : Nat) :
    TypedMemmove (toy.link (at0 typedmemmoveCode)) A0 EqHashModel.M0 wb d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, _, _, hgo, _⟩, ⟨ht1, ht2⟩, _,
    ⟨hs1, hs2, hs3⟩, ⟨hD1, hD2, hD3, hD4, hD5⟩⟩
  simp only [Janus.Contracts.typSize] at hs1 hs2 hs3 hD1 hD2 hD3 hD4 hD5 ⊢
  have hn : Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 < 2 ^ 64 := by
    simpa using Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have ht8 : s.mem.accessible (s.regs 0).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ ht2 (Nat.le_refl _) (by omega)
  have hs2' := hs2
  simp only [outside_cons, outside_nil, and_true] at hD5
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  janus64_run until [0x100013, 0x100021]
  all_goals generalize Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 = N at *
  · -- `n = 0`
    refine tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) trivial ?_
    intro i hi; omega
  · -- `dst > src`: backwards
    refine ReachesRet.repMovsbB (c := 0x100021) (len := 2) rfl rfl
      ((s.regs 3).toNat + N - 1) ((s.regs 1).toNat + N - 1)
      N rfl
      (by simp [setRegF, BitVec.toNat_add]; omega)
      (by simp [setRegF, BitVec.toNat_add]; omega)
      (by simp [setRegF]) hn (by omega) (by omega)
      (by rw [show (s.regs 3).toNat + N - 1 + 1 - N =
            (s.regs 3).toNat by omega]; exact hD2)
      (by rw [show (s.regs 1).toNat + N - 1 + 1 - N =
            (s.regs 1).toNat by omega]; exact hs2') ?_
    have hm1 := accessible_copyB s.mem ((s.regs 3).toNat + N - 1)
      ((s.regs 1).toNat + N - 1) N (s.regs 4).toNat 8 false
    have hm2 : (copyB s.mem ((s.regs 3).toNat + N - 1)
        ((s.regs 1).toNat + N - 1) N).readLE (s.regs 4).toNat 8 =
        s.mem.readLE (s.regs 4).toNat 8 :=
      Janus.Arm64.Memory.readLE_congr fun i hi => copyB_bytes_out _ _ _ _ _ (by omega)
    rw [hsp] at hm1
    janus64_run
    refine tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl ?_ trivial ?_
    · exact memFrame_of_bytes (regions_copyB _ _ _ _) fun x hx => copyB_bytes_out _ _ _ _ _ (by
        omega)
    · intro i hi
      have h := copyB_bytes s.mem ((s.regs 3).toNat + N - 1)
        ((s.regs 1).toNat + N - 1) N (by omega) (by omega)
        (N - 1 - i) (by omega)
      rw [show (s.regs 3).toNat + N - 1 - (N - 1 - i) =
          (s.regs 3).toNat + i by omega,
        show (s.regs 1).toNat + N - 1 - (N - 1 - i) =
          (s.regs 1).toNat + i by omega] at h
      exact h
  · -- `dst ≤ src`: forwards
    refine ReachesRet.repMovsb (c := 0x100013) (len := 2) rfl rfl (s.regs 3).toNat (s.regs 1).toNat
      N rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) hn hD2 hs2'
      (by omega) (by omega) ?_
    have hm1 := accessible_copyLE s.mem (s.regs 3).toNat (s.regs 1).toNat 1 N
      (s.regs 4).toNat 8 false
    have hm2 : (copyLE s.mem (s.regs 3).toNat (s.regs 1).toNat 1 N).readLE
        (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
      Janus.Arm64.Memory.readLE_congr fun i hi => copyLE_bytes_out _ _ _ _ _ (by omega)
    rw [hsp] at hm1
    janus64_run
    refine tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl ?_ trivial ?_
    · exact memFrame_of_bytes (regions_copyLE _ _ _ _ _) fun x hx => copyLE_bytes_out _ _ _ _ _ hx
    · exact copyLE_bytes _ _ _ _ (by omega)


/-! ## Clearing -/

theorem fill_frame {m : Janus.Arm64.Memory} {ws : List (Nat × Nat)} {a n : Nat} :
    MemFrame m (fillLE m a 1 0 n) (ws ++ [(a, a + n)]) :=
  memFrame_of_bytes (regions_fillLE _ _ _ _ _) fun x hx => by
    rw [bytes_fillLE_zero, ite_eq_right (by omega)]

theorem fill_zeroed (m : Janus.Arm64.Memory) (a n : Nat) : Zeroed (fillLE m a 1 0 n) a n := by
  intro i hi; rw [bytes_fillLE_zero, ite_eq_left (by omega)]

theorem fill_ret {m : Janus.Arm64.Memory} {a n r : Nat} (h : a + n ≤ r ∨ r + 8 ≤ a) :
    (fillLE m a 1 0 n).readLE r 8 = m.readLE r 8 :=
  Janus.Arm64.Memory.readLE_congr fun i hi => by rw [bytes_fillLE_zero, ite_eq_right (by omega)]

/-- `mov %rax, %rdi; mov %rbx, %rcx; xor %eax, %eax; rep stosb; ret`. -/
def memclrCode : List Nat := [0x48, 0x89, 0xc7, 0x48, 0x89, 0xd9, 0x31, 0xc0, 0xf3, 0xaa, 0xc3]

theorem memclrNoHeapPointers_impl (d : Nat) :
    MemclrNoHeapPointers (toy.link (at0 memclrCode)) A0 EqHashModel.M0 d := by
  rw [link_at0]
  intro s hpc ⟨henv, ⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, hout, ⟨hD1, hD2, hD3, hD4,
      hD5⟩⟩
  simp only [outside_cons, outside_nil, and_true] at hD5
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  have hm2 := fill_ret (m := s.mem) hD5
  have hm1 : (fillLE s.mem (s.regs 0).toNat 1 0 (s.regs 3).toNat).accessible (s.regs 4).toNat 8
      false = true := by rw [accessible_fillLE]; exact hsp
  janus64_run until [0x100008]
  refine ReachesRet.repStosb (c := 0x100008) (len := 2) rfl rfl (s.regs 0).toNat (s.regs 3).toNat
    rfl (by simp [setRegF]) (by simp [setRegF]) (s.regs 3).isLt hD2 (by omega) ?_
  janus64_run
  exact tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl rfl fill_frame trivial (fill_zeroed _ _ _)

theorem memclrHasPointers_impl (wb d : Nat) :
    MemclrHasPointers (toy.link (at0 memclrCode)) A0 EqHashModel.M0 wb d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, _, _, hgo, _⟩, _, _,
    ⟨hD1, hD2, hD3, hD4, hD5⟩⟩
  simp only [outside_cons, outside_nil, and_true] at hD5
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  have hm2 := fill_ret (m := s.mem) hD5
  have hm1 : (fillLE s.mem (s.regs 0).toNat 1 0 (s.regs 3).toNat).accessible (s.regs 4).toNat 8
      false = true := by rw [accessible_fillLE]; exact hsp
  janus64_run until [0x100008]
  refine ReachesRet.repStosb (c := 0x100008) (len := 2) rfl rfl (s.regs 0).toNat (s.regs 3).toNat
    rfl (by simp [setRegF]) (by simp [setRegF]) (s.regs 3).isLt hD2 (by omega) ?_
  janus64_run
  exact tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl rfl fill_frame trivial (fill_zeroed _ _ _)

/-- `mov (%rax), %rcx` (the size `typ.Size_`); `mov %rbx, %rdi; xor %eax, %eax; rep stosb;
ret`. -/
def typedmemclrCode : List Nat := [0x48, 0x8b, 0x08, 0x48, 0x89, 0xdf, 0x31, 0xc0, 0xf3, 0xaa, 0xc3]

theorem typedmemclr_impl (wb d : Nat) :
    TypedMemclr (toy.link (at0 typedmemclrCode)) A0 EqHashModel.M0 wb d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, _, _, hgo, _⟩, ⟨ht1, ht2⟩, _,
    ⟨hD1, hD2, hD3, hD4, hD5⟩⟩
  simp only [Janus.Contracts.typSize] at hD1 hD2 hD3 hD4 hD5 ⊢
  have ht8 : s.mem.accessible (s.regs 0).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ ht2 (Nat.le_refl _) (by omega)
  have hn : Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 < 2 ^ 64 := by
    simpa using Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  simp only [outside_cons, outside_nil, and_true] at hD5
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  janus64_run until [0x100008]
  generalize Janus.Arm64.Memory.readLE s.mem (s.regs 0).toNat 8 = N at *
  have hm2 := fill_ret (m := s.mem) hD5
  have hm1 : (fillLE s.mem (s.regs 3).toNat 1 0 N).accessible (s.regs 4).toNat 8
      false = true := by rw [accessible_fillLE]; exact hsp
  refine ReachesRet.repStosb (c := 0x100008) (len := 2) rfl rfl (s.regs 3).toNat N
    rfl (by simp [setRegF]) (by simp [setRegF]) hn hD2 (by omega) ?_
  janus64_run
  exact tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl rfl fill_frame trivial (fill_zeroed _ _ _)

/-- `ret`: with the barrier off, `bulkBarrierPreWrite` does nothing. -/
def bulkBarrierCode : List Nat := [0xc3]

theorem bulkBarrierOff_impl (wb d : Nat) :
    BulkBarrierOff (toy.link (at0 bulkBarrierCode)) A0 EqHashModel.M0 wb d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, _, _, hgo, _⟩, _, _, _⟩
  janus64_run
  exact tRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) trivial trivial


/-! ## `memequal`, `memequal_varlen`, `strequal`: a byte loop -/

/-- Comparing `k + 1` bytes: the first byte, then the rest. -/
theorem readLE_succ_beq (m : Janus.Arm64.Memory) (a b k : Nat) :
    (m.readLE a (k + 1) == m.readLE b (k + 1)) =
      ((m.bytes a == m.bytes b) && (m.readLE (a + 1) k == m.readLE (b + 1) k)) := by
  rw [Janus.Arm64.Memory.readLE_succ, Janus.Arm64.Memory.readLE_succ]
  have h1 := (m.bytes a).isLt
  have h2 := (m.bytes b).isLt
  by_cases h : m.bytes a = m.bytes b
  · rw [h]
    by_cases hc : m.readLE (a + 1) k = m.readLE (b + 1) k
    · simp [hc]
    · rw [beq_false_of_ne hc, beq_false_of_ne (by omega)]; simp
  · have : (m.bytes a).toNat ≠ (m.bytes b).toNat := fun h' => h (BitVec.eq_of_toNat_eq h')
    rw [beq_false_of_ne h, Bool.false_and, beq_false_of_ne (by omega)]

/-- `0: test %rcx, %rcx; jz 1f; movzbl (%rax), %edx; movzbl (%rbx), %esi; cmp %rsi, %rdx;
jne 2f; inc %rax; inc %rbx; dec %rcx; jmp 0b; 1: mov $1, %eax; ret; 2: xor %eax, %eax; ret`. -/
def memequalCode : List Nat :=
  [0x48, 0x85, 0xc9, 0x74, 0x16, 0x0f, 0xb6, 0x10, 0x0f, 0xb6, 0x33, 0x48, 0x39, 0xf2, 0x75, 0x11,
   0x48, 0xff, 0xc0, 0x48, 0xff, 0xc3, 0x48, 0xff, 0xc9, 0xeb, 0xe5, 0xb8, 0x01, 0x00, 0x00, 0x00,
   0xc3, 0x31, 0xc0, 0xc3]

/-- What the byte loop returns with, from the loop head with `k` bytes left at `a`, `b`. -/
def LoopPost (m : Janus.Arm64.Memory) (R : W64) (t : State) (a b k : Nat) (t' : State) : Prop :=
  t'.rip = BitVec.ofNat 64 (m.readLE R.toNat 8) ∧ t'.regs 4 = R + 8 ∧ t'.regs 5 = t.regs 5 ∧
      t'.regs 14 = t.regs 14 ∧ t'.xmm 15 = t.xmm 15 ∧
    t'.fsBase = t.fsBase ∧ t'.df = false ∧ t'.mxcsr = t.mxcsr ∧ t'.x87 = t.x87 ∧ t'.fpucw = t.fpucw ∧ t'.mem = m ∧
    (t'.regs 0).toNat % 256 = (m.readLE a k == m.readLE b k).toNat

theorem memequal_loop (m : Janus.Arm64.Memory) (R : W64) (hR : m.accessible R.toNat 8 false = true)
    (hra : m.readLE R.toNat 8 < 2 ^ 47) :
    ∀ k (t : State) (a b : Nat), t.rip = BitVec.ofNat 64 A0 → t.regs 0 = BitVec.ofNat 64 a →
      t.regs 3 = BitVec.ofNat 64 b → t.regs 1 = BitVec.ofNat 64 k → t.mem = m → t.regs 4 = R →
      t.df = false → a + k ≤ 2 ^ 48 → b + k ≤ 2 ^ 48 → m.accessible a k false = true →
      m.accessible b k false = true →
      ReachesRet (withCode memequalCode) (BitVec.ofNat 64 (m.readLE R.toNat 8)) t
        (LoopPost m R t a b k) := by
  intro k
  induction k with
  | zero =>
    intro t a b h_rip h0 h3 h1 hmem h4 hdf ha hb hacc hbcc
    janus64_run
    exact ⟨rfl, by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by simp [setRegF]⟩
  | succ k ih =>
    intro t a b h_rip h0 h3 h1 hmem h4 hdf ha hb hacc hbcc
    have hab := (m.bytes a).isLt
    have hbb := (m.bytes b).isLt
    simp only [Nat.reducePow] at hab hbb
    janus64_run until [0x100000]
    · simp only [Janus.Arm64.Memory.readLE_one] at hbr
      have he : m.bytes a = m.bytes b := BitVec.eq_of_toNat_eq (by omega)
      refine ReachesRet.mono (ih _ (a + 1) (b + 1) rfl (by simp [setRegF]) (by simp [setRegF])
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; bv_omega) rfl (by simp [setRegF, h4])
            rfl
        (by omega) (by omega)
        (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
        (Janus.Arm64.Memory.accessible_mono _ hbcc (by omega) (by omega))) ?_
      intro t' ⟨erip, e4, e5, e14, e15, efs, edf, emx, ex87, efw, emem, e0⟩
      refine ⟨erip, e4, by simpa [setRegF] using e5, by simpa [setRegF] using e14, e15, efs, edf,
          emx, ex87, efw, emem,
        ?_⟩
      rw [e0, readLE_succ_beq, he, beq_self_eq_true, Bool.true_and]
    · simp only [Janus.Arm64.Memory.readLE_one] at *
      have he' : (m.bytes a).toNat ≠ (m.bytes b).toNat := by omega
      have he : m.bytes a ≠ m.bytes b := fun h => he' (by rw [h])
      refine ⟨rfl, by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        ?_⟩
      rw [readLE_succ_beq, beq_false_of_ne he]; simp [setRegF]


theorem memequal_impl (d : Nat) : Memequal (toy.link (at0 memequalCode)) A0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  refine ReachesRet.mono (memequal_loop s.mem (s.regs 4) hsp hra (s.regs 1).toNat s (s.regs 0).toNat
    (s.regs 3).toNat hpc (by simp) (by simp) (by simp) rfl rfl hdf ha1 hb1 ha2 hb2) ?_
  intro t' ⟨erip, e4, e5, e14, e15, efs, edf, emx, ex87, efw, emem, e0⟩
  exact eqRet_of e4 e5 e14 e15 erip efs hdf edf (by rw [emx])
    (by rw [emem]; exact MemFrame.refl _ _) e0 ex87 efw


/-- `mov 8(%rdx), %rcx` (the closure's size), then `memequalCode`'s loop. -/
def memequalVarlenCode : List Nat :=
  [0x48, 0x8b, 0x4a, 0x08, 0x48, 0x85, 0xc9, 0x74, 0x16, 0x0f, 0xb6, 0x10, 0x0f, 0xb6, 0x33, 0x48,
   0x39, 0xf2, 0x75, 0x11, 0x48, 0xff, 0xc0, 0x48, 0xff, 0xc3, 0x48, 0xff, 0xc9, 0xeb, 0xe5, 0xb8,
   0x01, 0x00, 0x00, 0x00, 0xc3, 0x31, 0xc0, 0xc3]

theorem memequalVarlen_loop (m : Janus.Arm64.Memory) (R : W64) (hR : m.accessible R.toNat 8 false =
    true)
    (hra : m.readLE R.toNat 8 < 2 ^ 47) :
    ∀ k (t : State) (a b : Nat), t.rip = BitVec.ofNat 64 (A0 + 4) → t.regs 0 = BitVec.ofNat 64 a →
      t.regs 3 = BitVec.ofNat 64 b → t.regs 1 = BitVec.ofNat 64 k → t.mem = m → t.regs 4 = R →
      t.df = false → a + k ≤ 2 ^ 48 → b + k ≤ 2 ^ 48 → m.accessible a k false = true →
      m.accessible b k false = true →
      ReachesRet (withCode memequalVarlenCode) (BitVec.ofNat 64 (m.readLE R.toNat 8)) t
        (LoopPost m R t a b k) := by
  intro k
  induction k with
  | zero =>
    intro t a b h_rip h0 h3 h1 hmem h4 hdf ha hb hacc hbcc
    janus64_run
    exact ⟨rfl, by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by simp [setRegF]⟩
  | succ k ih =>
    intro t a b h_rip h0 h3 h1 hmem h4 hdf ha hb hacc hbcc
    have hab := (m.bytes a).isLt
    have hbb := (m.bytes b).isLt
    simp only [Nat.reducePow] at hab hbb
    janus64_run until [0x100004]
    · simp only [Janus.Arm64.Memory.readLE_one] at hbr
      have he : m.bytes a = m.bytes b := BitVec.eq_of_toNat_eq (by omega)
      refine ReachesRet.mono (ih _ (a + 1) (b + 1) rfl (by simp [setRegF]) (by simp [setRegF])
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; bv_omega) rfl (by simp [setRegF, h4])
            rfl
        (by omega) (by omega)
        (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
        (Janus.Arm64.Memory.accessible_mono _ hbcc (by omega) (by omega))) ?_
      intro t' ⟨erip, e4, e5, e14, e15, efs, edf, emx, ex87, efw, emem, e0⟩
      refine ⟨erip, e4, by simpa [setRegF] using e5, by simpa [setRegF] using e14, e15, efs, edf,
          emx, ex87, efw, emem,
        ?_⟩
      rw [e0, readLE_succ_beq, he, beq_self_eq_true, Bool.true_and]
    · simp only [Janus.Arm64.Memory.readLE_one] at *
      have he' : (m.bytes a).toNat ≠ (m.bytes b).toNat := by omega
      have he : m.bytes a ≠ m.bytes b := fun h => he' (by rw [h])
      refine ⟨rfl, by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        ?_⟩
      rw [readLE_succ_beq, beq_false_of_ne he]; simp [setRegF]


theorem memequalVarlen_impl (d : Nat) : MemequalVarlen (toy.link (at0 memequalVarlenCode)) A0 d :=
    by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, ⟨hv1, hv2, hv3⟩, ⟨ha1, ha2, ha3⟩,
    ⟨hb1, hb2, hb3⟩⟩
  simp only [varlenSize] at ha1 ha2 hb1 hb2 ⊢
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  janus64_run until [0x100004]
  refine ReachesRet.mono (memequalVarlen_loop s.mem (s.regs 4) hsp hra _ _ (s.regs 0).toNat
    (s.regs 3).toNat rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [setRegF]) rfl ha1 hb1 ha2 hb2) ?_
  intro t' ⟨erip, e4, e5, e14, e15, efs, edf, emx, ex87, efw, emem, e0⟩
  exact eqRet_of (by simpa [setRegF] using e4) (by simpa [setRegF] using e5)
    (by simpa [setRegF] using e14) e15 erip efs hdf edf (by rw [emx])
    (by rw [emem]; exact MemFrame.refl _ _) e0 ex87 efw

/-- `mov 8(%rax), %rcx; cmp 8(%rbx), %rcx; jne 2f` (different lengths: `false`); `mov (%rax), %rax;
mov (%rbx), %rbx`, then `memequalCode`'s loop on the data. -/
def strequalCode : List Nat :=
  [0x48, 0x8b, 0x48, 0x08, 0x48, 0x3b, 0x4b, 0x08, 0x75, 0x27, 0x48, 0x8b, 0x00, 0x48, 0x8b, 0x1b,
   0x48, 0x85, 0xc9, 0x74, 0x16, 0x0f, 0xb6, 0x10, 0x0f, 0xb6, 0x33, 0x48, 0x39, 0xf2, 0x75, 0x11,
   0x48, 0xff, 0xc0, 0x48, 0xff, 0xc3, 0x48, 0xff, 0xc9, 0xeb, 0xe5, 0xb8, 0x01, 0x00, 0x00, 0x00,
   0xc3, 0x31, 0xc0, 0xc3]

theorem strequal_loop (m : Janus.Arm64.Memory) (R : W64) (hR : m.accessible R.toNat 8 false = true)
    (hra : m.readLE R.toNat 8 < 2 ^ 47) :
    ∀ k (t : State) (a b : Nat), t.rip = BitVec.ofNat 64 (A0 + 16) → t.regs 0 = BitVec.ofNat 64 a →
      t.regs 3 = BitVec.ofNat 64 b → t.regs 1 = BitVec.ofNat 64 k → t.mem = m → t.regs 4 = R →
      t.df = false → a + k ≤ 2 ^ 48 → b + k ≤ 2 ^ 48 → m.accessible a k false = true →
      m.accessible b k false = true →
      ReachesRet (withCode strequalCode) (BitVec.ofNat 64 (m.readLE R.toNat 8)) t
        (LoopPost m R t a b k) := by
  intro k
  induction k with
  | zero =>
    intro t a b h_rip h0 h3 h1 hmem h4 hdf ha hb hacc hbcc
    janus64_run
    exact ⟨rfl, by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      by simp [setRegF]⟩
  | succ k ih =>
    intro t a b h_rip h0 h3 h1 hmem h4 hdf ha hb hacc hbcc
    have hab := (m.bytes a).isLt
    have hbb := (m.bytes b).isLt
    simp only [Nat.reducePow] at hab hbb
    janus64_run until [0x100010]
    · simp only [Janus.Arm64.Memory.readLE_one] at hbr
      have he : m.bytes a = m.bytes b := BitVec.eq_of_toNat_eq (by omega)
      refine ReachesRet.mono (ih _ (a + 1) (b + 1) rfl (by simp [setRegF]) (by simp [setRegF])
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; bv_omega) rfl (by simp [setRegF, h4])
            rfl
        (by omega) (by omega)
        (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
        (Janus.Arm64.Memory.accessible_mono _ hbcc (by omega) (by omega))) ?_
      intro t' ⟨erip, e4, e5, e14, e15, efs, edf, emx, ex87, efw, emem, e0⟩
      refine ⟨erip, e4, by simpa [setRegF] using e5, by simpa [setRegF] using e14, e15, efs, edf,
          emx, ex87, efw, emem,
        ?_⟩
      rw [e0, readLE_succ_beq, he, beq_self_eq_true, Bool.true_and]
    · simp only [Janus.Arm64.Memory.readLE_one] at *
      have he' : (m.bytes a).toNat ≠ (m.bytes b).toNat := by omega
      have he : m.bytes a ≠ m.bytes b := fun h => he' (by rw [h])
      refine ⟨rfl, by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        ?_⟩
      rw [readLE_succ_beq, beq_false_of_ne he]; simp [setRegF]


theorem strequal_impl (d : Nat) : Strequal (toy.link (at0 strequalCode)) A0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hgo⟩, ⟨⟨ha1, ha2, ha3⟩, ⟨hp1, hp2, hp3⟩⟩,
    ⟨⟨hb1, hb2, hb3⟩, ⟨hq1, hq2, hq3⟩⟩⟩
  simp only [strPtr, strLen] at hp1 hp2 hq1 hq2
  have hsp : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hst (Or.inl rfl) (by omega) (by omega)
  have hla := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 8) 8
  have hlb := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 3).toNat + 8) 8
  simp only [Nat.reducePow] at hla hlb
  janus64_run until [0x100010]
  · have hl : Janus.Arm64.Memory.readLE s.mem ((s.regs 0).toNat + 8) 8 =
        Janus.Arm64.Memory.readLE s.mem ((s.regs 3).toNat + 8) 8 := by omega
    rw [← hl] at hq1 hq2
    refine ReachesRet.mono (strequal_loop s.mem (s.regs 4) hsp hra _ _ _ _ rfl (by simp [setRegF])
      (by simp [setRegF]) (by simp [setRegF]) rfl (by simp [setRegF]) rfl hp1 hq1 hp2 hq2) ?_
    intro t' ⟨erip, e4, e5, e14, e15, efs, edf, emx, ex87, efw, emem, e0⟩
    refine eqRet_of (by simpa [setRegF] using e4) (by simpa [setRegF] using e5)
      (by simpa [setRegF] using e14) e15 erip efs hdf edf (by rw [emx])
      (by rw [emem]; exact MemFrame.refl _ _) ?_ ex87 efw
    simp only [BoolRes, e0, strEq, strLen, strPtr, ← hl, beq_self_eq_true, Bool.true_and]
  · eq_close hdf
    have hne : Janus.Arm64.Memory.readLE s.mem ((s.regs 0).toNat + 8) 8 ≠
        Janus.Arm64.Memory.readLE s.mem ((s.regs 3).toNat + 8) 8 := by omega
    simp [BoolRes, setRegF, strEq, strLen, beq_false_of_ne hne]


/-! ## Satisfiability -/

/-- The witness arguments: `RAX = a`, `RBX = b`, `RCX = c`, `RDX = x`. -/
def args (a b c x : Nat) : Nat → W64 := fun i =>
  if i = 0 then BitVec.ofNat 64 a else if i = 3 then BitVec.ofNat 64 b else
  if i = 1 then BitVec.ofNat 64 c else if i = 2 then BitVec.ofNat 64 x else 0

/-- Decide an `Input`/`StrInput` of a witness state. -/
macro "inp" : tactic => `(tactic| (simp only [MemAmd64.Input, MemAmd64.StrInput,
  MapAmd64.calleeStack, Janus.outside_cons, Janus.outside_nil]; decide))

/-- `Memequal` is satisfiable (amd64). -/
theorem memequal_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    Memequal (toy.link impl) A0 d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 0 s ∧ Input s d 0 (s.regs 0).toNat (s.regs 1).toNat ∧
        Input s d 0 (s.regs 3).toNat (s.regs 1).toNat) :=
  ⟨_, 64, memequal_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 8 0), rfl,
    wstate_eqPre _ 0 (by decide), by inp, by inp⟩

/-- `MemequalN 0` is satisfiable (amd64). -/
theorem memequal0_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    MemequalN (toy.link impl) A0 d 0 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat 0 ∧ Input s d 2 (s.regs 3).toNat 0) :=
  ⟨_, 64, memequal0_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by inp, by inp⟩

/-- `MemequalN 1` is satisfiable (amd64). -/
theorem memequal8_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    MemequalN (toy.link impl) A0 d 1 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat 1 ∧ Input s d 2 (s.regs 3).toNat 1) :=
  ⟨_, 64, memequal8_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by inp, by inp⟩

/-- `MemequalN 2` is satisfiable (amd64). -/
theorem memequal16_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    MemequalN (toy.link impl) A0 d 2 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat 2 ∧ Input s d 2 (s.regs 3).toNat 2) :=
  ⟨_, 64, memequal16_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by inp, by inp⟩

/-- `MemequalN 4` is satisfiable (amd64). -/
theorem memequal32_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    MemequalN (toy.link impl) A0 d 4 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat 4 ∧ Input s d 2 (s.regs 3).toNat 4) :=
  ⟨_, 64, memequal32_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by inp, by inp⟩

/-- `MemequalN 8` is satisfiable (amd64). -/
theorem memequal64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    MemequalN (toy.link impl) A0 d 8 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat 8 ∧ Input s d 2 (s.regs 3).toNat 8) :=
  ⟨_, 64, memequal64_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by inp, by inp⟩

/-- `MemequalN 16` is satisfiable (amd64). -/
theorem memequal128_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    MemequalN (toy.link impl) A0 d 16 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat 16 ∧ Input s d 2 (s.regs 3).toNat 16) :=
  ⟨_, 64, memequal128_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by inp, by inp⟩

/-- `MemequalVarlen` is satisfiable (amd64): the closure `VLEN` (size 8). -/
theorem memequalVarlen_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    MemequalVarlen (toy.link impl) A0 d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ Input s d 2 ((s.regs 2).toNat + 8) 8 ∧
        Input s d 2 (s.regs 0).toNat (varlenSize s) ∧ Input s d 2 (s.regs 3).toNat (varlenSize s))
            :=
  ⟨_, 64, memequalVarlen_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 VLEN), rfl,
    wstate_eqPre _ 2 (by decide), by inp, by inp, by inp⟩

/-- `Fequal binary32 4` and `Fequal binary64 8` are satisfiable (amd64). -/
theorem f32equal_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    Fequal (toy.link impl) A0 d Janus.Float.binary32 4 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ GoMXCSR s ∧ Input s d 2 (s.regs 0).toNat 4 ∧ Input s d 2 (s.regs 3).toNat 4) :=
  ⟨_, 64, f32equal_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by unfold GoMXCSR; decide, by inp, by inp⟩

theorem f64equal_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    Fequal (toy.link impl) A0 d Janus.Float.binary64 8 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ GoMXCSR s ∧ Input s d 2 (s.regs 0).toNat 8 ∧ Input s d 2 (s.regs 3).toNat 8) :=
  ⟨_, 64, f64equal_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by unfold GoMXCSR; decide, by inp, by inp⟩

/-- `Cequal binary32 4` and `Cequal binary64 8` are satisfiable (amd64). -/
theorem c64equal_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    Cequal (toy.link impl) A0 d Janus.Float.binary32 4 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ GoMXCSR s ∧ Input s d 2 (s.regs 0).toNat (2 * 4) ∧
        Input s d 2 (s.regs 3).toNat (2 * 4)) :=
  ⟨_, 64, c64equal_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by unfold GoMXCSR; decide, by inp, by inp⟩

theorem c128equal_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    Cequal (toy.link impl) A0 d Janus.Float.binary64 8 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ GoMXCSR s ∧ Input s d 2 (s.regs 0).toNat (2 * 8) ∧
        Input s d 2 (s.regs 3).toNat (2 * 8)) :=
  ⟨_, 64, c128equal_impl 64, wstate (args IfaceModel.VAL IfaceModel.VAL 0 0), rfl,
    wstate_eqPre _ 2 (by decide), by unfold GoMXCSR; decide, by inp, by inp⟩

/-- `MemequalN` is satisfiable for `n = 0, 1, 2, 4, 8, 16` (amd64): the witnesses per length
above. -/
theorem memequalN_satisfiable (n : Nat) (hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) :
    ∃ (impl : List Janus.Amd64.Segment) (d : Nat), MemequalN (toy.link impl) A0 d n ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
        (EqPre d 2 s ∧ Input s d 2 (s.regs 0).toNat n ∧ Input s d 2 (s.regs 3).toNat n) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact memequal0_satisfiable
    | exact memequal8_satisfiable
    | exact memequal16_satisfiable
    | exact memequal32_satisfiable
    | exact memequal64_satisfiable
    | exact memequal128_satisfiable

/-- `Fequal` is satisfiable for `float32` and `float64` (amd64). -/
theorem fequal_satisfiable (f : Janus.Float.Fmt) (k : Nat)
    (hf : (f = Janus.Float.binary32 ∧ k = 4) ∨ (f = Janus.Float.binary64 ∧ k = 8)) :
    ∃ (impl : List Janus.Amd64.Segment) (d : Nat), Fequal (toy.link impl) A0 d f k ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
        (EqPre d 2 s ∧ GoMXCSR s ∧ Input s d 2 (s.regs 0).toNat k ∧ Input s d 2 (s.regs 3).toNat k) := by
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | exact f32equal_satisfiable
    | exact f64equal_satisfiable

/-- `Cequal` is satisfiable for `complex64` and `complex128` (amd64). -/
theorem cequal_satisfiable (f : Janus.Float.Fmt) (k : Nat)
    (hf : (f = Janus.Float.binary32 ∧ k = 4) ∨ (f = Janus.Float.binary64 ∧ k = 8)) :
    ∃ (impl : List Janus.Amd64.Segment) (d : Nat), Cequal (toy.link impl) A0 d f k ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
        (EqPre d 2 s ∧ GoMXCSR s ∧ Input s d 2 (s.regs 0).toNat (2 * k) ∧
          Input s d 2 (s.regs 3).toNat (2 * k)) := by
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | exact c64equal_satisfiable
    | exact c128equal_satisfiable

/-- `Strequal` is satisfiable (amd64): the string header `STR` twice. -/
theorem strequal_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (d : Nat),
    Strequal (toy.link impl) A0 d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (EqPre d 2 s ∧ StrInput s d 2 (s.regs 0).toNat ∧ StrInput s d 2 (s.regs 3).toNat) :=
  ⟨_, 64, strequal_impl 64, wstate (args STR STR 0 0), rfl, wstate_eqPre _ 2 (by decide),
    ⟨by inp, by inp⟩, ⟨by inp, by inp⟩⟩

/-- `TD`'s values `VAL` compare in `R0`, also under every frame outside its private memory. -/
theorem eqOK_wit : Iface.EqOK IfaceModel.R0 wmem IfaceModel.TD IfaceModel.VAL IfaceModel.VAL :=
  fun _ => ⟨Or.inl rfl, rfl, by decide, by decide⟩

theorem eqFrame_wit (ws : List (Nat × Nat))
    (hws : ∀ a n, InRanges a n IfaceModel.R0.priv → Outside a n ws) (hv : Outside IfaceModel.VAL 8
        ws) :
    Janus.Spec.Type.EqFrame IfaceModel.R0 IfaceModel.TD wmem IfaceModel.VAL IfaceModel.VAL ws := by
  have h8 : Janus.Spec.Type.tySize wmem IfaceModel.TD = 8 := by decide
  exact Janus.Spec.Type.EqFrame.of_regular IfaceModel.R0_laws (g := 0) (wmem_env0 0) (Or.inl rfl)
      (by decide)
    (by decide) (by rw [h8]; decide) (by rw [h8]; decide) (by rw [h8]; exact hv) (by rw [h8]; exact
        hv)
    hws

/-- The private memory of `R0` is outside the witness call's window. -/
theorem priv_outside_window (r : Nat → W64) :
    ∀ a n, InRanges a n IfaceModel.R0.priv → Outside a n (MemAmd64.calleeStack (wstate r) 64 2) :=
        by
  intro a n ⟨q, hq, h1, h2⟩
  simp only [IfaceModel.R0_priv, List.mem_cons, List.not_mem_nil, or_false] at hq
  subst hq
  simp only [MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
  simp [wstate, IfaceModel.wsp] at h1 h2 ⊢; omega

/-- `Nilinterequal` is satisfiable (amd64), for `IfaceModel.R0`: `EFV = (TD, VAL)` compared with
itself (the type words agree, so `TD`'s equality is reached). -/
theorem nilinterequal_satisfiable : ∃ (R : Janus.Spec.Type.IfaceModel)
    (impl : List Janus.Amd64.Segment) (d : Nat), R.Laws ∧
    Nilinterequal (toy.link impl) A0 R d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (IfacePre R d s ∧ Input s d 2 (s.regs 0).toNat 16 ∧ Input s d 2 (s.regs 3).toNat 16 ∧
      (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 3).toNat 8 →
        Iface.EqOK R s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.mem.readLE ((s.regs 0).toNat + 8) 8)
          (s.mem.readLE ((s.regs 3).toNat + 8) 8) ∧
        Janus.Spec.Type.EqFrame R (s.mem.readLE (s.regs 0).toNat 8) s.mem
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8)
          (MemAmd64.calleeStack s d 2))) := by
  refine ⟨_, _, 64, IfaceModel.R0_laws, nilinterequal_impl 64, wstate (args EFV EFV 0 0), rfl,
    wstate_ifacePre _, by inp, by inp, fun _ => ?_⟩
  have e1 : (wstate (args EFV EFV 0 0)).mem.readLE ((wstate (args EFV EFV 0 0)).regs 0).toNat 8 =
    IfaceModel.TD := by decide
  have e2 : (wstate (args EFV EFV 0 0)).mem.readLE
    (((wstate (args EFV EFV 0 0)).regs 0).toNat + 8) 8 = IfaceModel.VAL := by decide
  have e3 : (wstate (args EFV EFV 0 0)).mem.readLE
    (((wstate (args EFV EFV 0 0)).regs 3).toNat + 8) 8 = IfaceModel.VAL := by decide
  rw [e1, e2, e3]
  exact ⟨eqOK_wit, eqFrame_wit _ (priv_outside_window _) (by inp)⟩

/-- `Interequal` is satisfiable (amd64), for `IfaceModel.R0`: `IFV = (TAB, VAL)` compared with
itself (the itab words agree and `TAB.Type = TD`). -/
theorem interequal_satisfiable : ∃ (R : Janus.Spec.Type.IfaceModel)
    (impl : List Janus.Amd64.Segment) (d : Nat), R.Laws ∧
    Interequal (toy.link impl) A0 R d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (IfacePre R d s ∧ Input s d 2 (s.regs 0).toNat 16 ∧ Input s d 2 (s.regs 3).toNat 16 ∧
      (s.mem.readLE (s.regs 0).toNat 8 = s.mem.readLE (s.regs 3).toNat 8 →
        s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        Input s d 2 (s.mem.readLE (s.regs 0).toNat 8) 16 ∧
        s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8 ≠ 0 ∧
        Iface.EqOK R s.mem (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8)
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8) ∧
        Janus.Spec.Type.EqFrame R (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 8) 8) s.mem
          (s.mem.readLE ((s.regs 0).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8)
          (MemAmd64.calleeStack s d 2))) := by
  refine ⟨_, _, 64, IfaceModel.R0_laws, interequal_impl 64, wstate (args IFV IFV 0 0), rfl,
    wstate_ifacePre _, by inp, by inp, fun _ _ => ?_⟩
  have e1 : (wstate (args IFV IFV 0 0)).mem.readLE ((wstate (args IFV IFV 0 0)).regs 0).toNat 8 =
    IfaceModel.TAB := by decide
  have e2 : (wstate (args IFV IFV 0 0)).mem.readLE
    (((wstate (args IFV IFV 0 0)).regs 0).toNat + 8) 8 = IfaceModel.VAL := by decide
  have e3 : (wstate (args IFV IFV 0 0)).mem.readLE
    (((wstate (args IFV IFV 0 0)).regs 3).toNat + 8) 8 = IfaceModel.VAL := by decide
  have e4 : (wstate (args IFV IFV 0 0)).mem.readLE (IfaceModel.TAB + 8) 8 = IfaceModel.TD := by
    decide
  rw [e1, e2, e3, e4]
  exact ⟨by inp, by decide, eqOK_wit, eqFrame_wit _ (priv_outside_window _) (by inp)⟩

/-- Decide a `Dest` of a witness state. -/
macro "dst" : tactic => `(tactic| (simp only [MemAmd64.Dest, MapAmd64.calleeStack,
    Janus.outside_cons,
  Janus.outside_nil, EqHashModel.M0]; decide))

/-- `Memmove` is satisfiable (amd64): 8 bytes from `VAL` to `DST`. -/
theorem memmove_satisfiable : ∃ (M : MemModel) (impl : List Janus.Amd64.Segment) (d : Nat), M.Laws ∧
    Memmove (toy.link impl) A0 M d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (M.Env s.mem (s.regs 14) ∧ EqPre d 3 s ∧
        Outside ((s.regs 4).toNat - d) (d + 8 + 8 * 3) M.priv ∧
        Input s d 3 (s.regs 3).toNat (s.regs 1).toNat ∧ Dest M s d 3 (s.regs 0).toNat (s.regs
            1).toNat) :=
  ⟨_, _, 64, M0_laws, memmove_impl 64, wstate (args DST IfaceModel.VAL 8 0), rfl, trivial,
    wstate_eqPre _ 3 (by decide), trivial, by inp, by dst⟩

/-- `MemclrNoHeapPointers` is satisfiable (amd64): the 64 bytes at `DST`. -/
theorem memclrNoHeapPointers_satisfiable : ∃ (M : MemModel) (impl : List Janus.Amd64.Segment)
    (d : Nat), M.Laws ∧ MemclrNoHeapPointers (toy.link impl) A0 M d ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (M.Env s.mem (s.regs 14) ∧ EqPre d 2 s ∧
        Outside ((s.regs 4).toNat - d) (d + 8 + 8 * 2) M.priv ∧
        Dest M s d 2 (s.regs 0).toNat (s.regs 3).toNat) :=
  ⟨_, _, 64, M0_laws, memclrNoHeapPointers_impl 64, wstate (args DST 64 0 0), rfl, trivial,
    wstate_eqPre _ 2 (by decide), trivial, by dst⟩

/-- `MemclrHasPointers` is satisfiable (amd64): the 64 bytes at `DST`, barrier flag `WB`. -/
theorem memclrHasPointers_satisfiable : ∃ (M : MemModel) (impl : List Janus.Amd64.Segment)
    (wb d : Nat), M.Laws ∧ MemclrHasPointers (toy.link impl) A0 M wb d ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (TPre M wb d 2 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 3).toNat % 8 = 0 ∧
        Dest M s d 2 (s.regs 0).toNat (s.regs 3).toNat) :=
  ⟨_, _, WB, 64, M0_laws, memclrHasPointers_impl WB 64, wstate (args DST 64 0 0), rfl,
    wstate_tPre _ 2 (by decide), by decide, by decide, by dst⟩

/-- `TypedMemmove` is satisfiable (amd64): a `TD` value (8 bytes) from `VAL` to `DST`. -/
theorem typedMemmove_satisfiable : ∃ (M : MemModel) (impl : List Janus.Amd64.Segment)
    (wb d : Nat), M.Laws ∧ TypedMemmove (toy.link impl) A0 M wb d ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (TPre M wb d 3 s ∧ Janus.Contracts.TypeOK s.mem (s.regs 0).toNat ∧
        Outside (s.regs 0).toNat 16 (MemAmd64.calleeStack s d 3) ∧
        Input s d 3 (s.regs 1).toNat (Janus.Contracts.typSize s.mem (s.regs 0).toNat) ∧
        Dest M s d 3 (s.regs 3).toNat (Janus.Contracts.typSize s.mem (s.regs 0).toNat)) :=
  ⟨_, _, WB, 64, M0_laws, typedmemmove_impl WB 64,
    wstate (args IfaceModel.TD DST IfaceModel.VAL 0), rfl, wstate_tPre _ 3 (by decide),
    by unfold Janus.Contracts.TypeOK; decide,
    by simp only [MapAmd64.calleeStack, Janus.outside_cons, Janus.outside_nil]; decide,
    by simp only [Janus.Contracts.typSize]; inp, by simp only [Janus.Contracts.typSize]; dst⟩

/-- `TypedMemclr` is satisfiable (amd64): a `TD` value at `DST`. -/
theorem typedMemclr_satisfiable : ∃ (M : MemModel) (impl : List Janus.Amd64.Segment)
    (wb d : Nat), M.Laws ∧ TypedMemclr (toy.link impl) A0 M wb d ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (TPre M wb d 2 s ∧ Janus.Contracts.TypeOK s.mem (s.regs 0).toNat ∧
        Outside (s.regs 0).toNat 16 (MemAmd64.calleeStack s d 2) ∧
        Dest M s d 2 (s.regs 3).toNat (Janus.Contracts.typSize s.mem (s.regs 0).toNat)) :=
  ⟨_, _, WB, 64, M0_laws, typedmemclr_impl WB 64, wstate (args IfaceModel.TD DST 0 0), rfl,
    wstate_tPre _ 2 (by decide), by unfold Janus.Contracts.TypeOK; decide,
    by simp only [MapAmd64.calleeStack, Janus.outside_cons, Janus.outside_nil]; decide,
    by simp only [Janus.Contracts.typSize]; dst⟩

/-- `BulkBarrierOff` is satisfiable (amd64). -/
theorem bulkBarrierOff_satisfiable : ∃ (M : MemModel) (impl : List Janus.Amd64.Segment)
    (wb d : Nat), M.Laws ∧ BulkBarrierOff (toy.link impl) A0 M wb d ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (TPre M wb d 4 s ∧ (s.regs 0).toNat % 8 = 0 ∧ (s.regs 3).toNat % 8 = 0 ∧
        (s.regs 1).toNat % 8 = 0) :=
  ⟨_, _, WB, 64, M0_laws, bulkBarrierOff_impl WB 64, wstate (args DST IfaceModel.VAL 8 0), rfl,
    wstate_tPre _ 4 (by decide), by decide, by decide, by decide⟩

end Janus.Contracts.MemSatAmd64
