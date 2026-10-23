import Janus.Tactic.Basic

/-!
# Symbolic execution of Advanced SIMD and SIMD&FP loads and stores

* `exec` equations (by `rfl`) for the SIMD constructors of `Instr`, and the unfoldings of the
  executor plumbing (`execVThreeSame`, `memV`, `ldMulti`, ...), registered in `janus_exec`.
  The vector operations themselves (`threeSameOp`, `acrossOp`, `elem`, `ofElems`, ...) are
  **not** unfolded: a symbolic V register holds a term like
  `threeSameOp true 3 17 128 x y d`, and the element lemmas below evaluate what the code
  reads back from it (`UMOV`, a later element-wise operation).
* `setVReg`: the V register file normal form, like `setReg` for the general registers.
* Element lemmas: `elem` of loaded data, of `ofElems`, of the logical and compare operations.

Nothing here is trusted: every lemma is proved from the model (`Janus.Arm64.Vector`, `Exec`).
-/

namespace Janus.Tactic

open Janus Janus.Arm64

/-! ## The V register file -/

/-- V register file `f` with register `r` set to `v`. -/
def setVReg (f : Nat → BitVec 128) (r : Nat) (v : BitVec 128) : Nat → BitVec 128 :=
  fun i => if i = r then v else f i

@[janus_exec, janus_post] theorem setVReg_apply (f : Nat → BitVec 128) (r : Nat) (v : BitVec 128)
    (i : Nat) : setVReg f r v i = if i = r then v else f i := rfl

@[janus_exec, janus_post] theorem setVReg_setVReg_same (f : Nat → BitVec 128) (r : Nat)
    (v w : BitVec 128) : setVReg (setVReg f r v) r w = setVReg f r w := by
  funext i; simp only [setVReg]; split <;> rfl

/-- Sort V register updates by register number (see `setReg_comm` for the `r + 0`). -/
@[janus_exec, janus_post] theorem setVReg_comm (f : Nat → BitVec 128) {r r' : Nat} (v w : BitVec 128)
    (h : r' < r) : setVReg (setVReg f r v) r' w = setVReg (setVReg f r' w) (r + 0) v := by
  funext i; simp only [setVReg, Nat.add_zero]
  by_cases h1 : i = r' <;> by_cases h2 : i = r <;> simp [h1, h2] <;> omega

theorem State.setV_eq (s : State) (d w x : Nat) :
    s.setV d w x = { s with vregs := setVReg s.vregs d (BitVec.ofNat 128 (x % 2 ^ w)) } := rfl

attribute [janus_exec] State.setV_eq State.getV qsize setVHigh lowestSetBit5 highestSetBit4
  multiRegs execVThreeSame execVCopy execVAcross execVTwoMisc execVShiftImm execFmovGen memV
  memVPair ldMulti stMulti execVLdStMulti ldSingle stSingle execVLdStSingle vSingleLayout

/-! ## `exec`, one equation per SIMD constructor -/

section ExecEqns

variable (s : State)

@[janus_exec] theorem exec_mrsTpidr (rt : Nat) :
    exec (.mrsTpidr rt) s = .ok (s.writeZR rt s.tpidr).next := rfl
@[janus_exec] theorem exec_vldstMulti (Q L : Bool) (opcode size : Nat) (post : Bool) (rm rn rt : Nat) :
    exec (.vldstMulti Q L opcode size post rm rn rt) s =
      match execVLdStMulti s Q L opcode post rm rn rt with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_vldstSingle (Q L R : Bool) (opcode : Nat) (S : Bool) (size : Nat) (post : Bool)
    (rm rn rt : Nat) :
    exec (.vldstSingle Q L R opcode S size post rm rn rt) s =
      match execVLdStSingle s Q L R opcode S size post rm rn rt with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_vAes (opcode rn rd : Nat) :
    exec (.vAes opcode rn rd) s = .ok (s.setV rd 128 (aesOp opcode (s.getV rd 128) (s.getV rn 128))).next :=
  rfl
@[janus_exec] theorem exec_vldrLit (opc imm19 rt : Nat) :
    exec (.vldrLit opc imm19 rt) s =
      match memV s true (4 * 2 ^ opc) rt (s.pc + sext64 21 (imm19 * 4)) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_vldstUImm (size opc imm12 rn rt : Nat) :
    exec (.vldstUImm size opc imm12 rn rt) s =
      match memIndexed s rn (BitVec.ofNat 64 (imm12 * 2 ^ (opc / 2 * 4 + size))) false false
          (fun s a => memV s (opc % 2 = 1) (2 ^ (opc / 2 * 4 + size)) rt a) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_vldstImm9 (size opc : Nat) (mode : Imm9Mode) (imm9 rn rt : Nat) :
    exec (.vldstImm9 size opc mode imm9 rn rt) s =
      match memIndexed s rn (sext64 9 imm9) (match mode with | .post => true | _ => false)
          (match mode with | .unscaled => false | _ => true)
          (fun s a => memV s (opc % 2 = 1) (2 ^ (opc / 2 * 4 + size)) rt a) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_vldstReg (size opc rm : Nat) (option : ExtendType) (S : Bool) (rn rt : Nat) :
    exec (.vldstReg size opc rm option S rn rt) s =
      match memIndexed s rn (extendReg 64 (s.readZR rm) option (if S then opc / 2 * 4 + size else 0))
          false false (fun s a => memV s (opc % 2 = 1) (2 ^ (opc / 2 * 4 + size)) rt a) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_vldstPair (opc : Nat) (mode : PairMode) (L : Bool) (imm7 rt2 rn rt : Nat) :
    exec (.vldstPair opc mode L imm7 rt2 rn rt) s =
      match memIndexed s rn ((BitVec.ofNat 7 imm7).signExtend 64 <<< (2 + opc))
          (match mode with | .post => true | _ => false)
          (match mode with | .offset => false | _ => true)
          (fun s a => memVPair s L (4 * 2 ^ opc) rt rt2 a) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_vThreeSame (Q U : Bool) (size rm opcode rn rd : Nat) :
    exec (.vThreeSame Q U size rm opcode rn rd) s =
      .ok (execVThreeSame s Q U size rm opcode rn rd).next := rfl
@[janus_exec] theorem exec_vScalarThreeSame (U : Bool) (size rm opcode rn rd : Nat) :
    exec (.vScalarThreeSame U size rm opcode rn rd) s =
      .ok (s.setV rd 64 (threeSameOp U size opcode 64 (s.getV rn 64) (s.getV rm 64)
        (s.getV rd 64))).next := rfl
@[janus_exec] theorem exec_vCopy (Q op : Bool) (imm5 imm4 rn rd : Nat) :
    exec (.vCopy Q op imm5 imm4 rn rd) s = .ok (execVCopy s Q op imm5 imm4 rn rd).next := rfl
@[janus_exec] theorem exec_vAcross (Q U : Bool) (size opcode rn rd : Nat) :
    exec (.vAcross Q U size opcode rn rd) s = .ok (execVAcross s Q U size opcode rn rd).next := rfl
@[janus_exec] theorem exec_vTwoMisc (Q U : Bool) (size opcode rn rd : Nat) :
    exec (.vTwoMisc Q U size opcode rn rd) s = .ok (execVTwoMisc s Q U size opcode rn rd).next := rfl
@[janus_exec] theorem exec_vShiftImm (Q U : Bool) (immh immb opcode rn rd : Nat) :
    exec (.vShiftImm Q U immh immb opcode rn rd) s =
      .ok (execVShiftImm s Q U immh immb opcode rn rd).next := rfl
@[janus_exec] theorem exec_vModImm (Q op : Bool) (cmode imm8 rd : Nat) :
    exec (.vModImm Q op cmode imm8 rd) s =
      .ok (s.setV rd (qsize Q) (modImmOp op cmode imm8 (qsize Q) (s.getV rd (qsize Q)))).next := rfl
@[janus_exec] theorem exec_vExt (Q : Bool) (rm imm4 rn rd : Nat) :
    exec (.vExt Q rm imm4 rn rd) s =
      .ok (s.setV rd (qsize Q) (extOp (qsize Q) imm4 (s.getV rn (qsize Q)) (s.getV rm (qsize Q)))).next :=
  rfl
@[janus_exec] theorem exec_vTbl (Q : Bool) (rm len : Nat) (op : Bool) (rn rd : Nat) :
    exec (.vTbl Q rm len op rn rd) s =
      .ok (s.setV rd (qsize Q) (tblOp op (len + 1) (qsize Q) (tableOf s.vregs rn (len + 1))
        (s.getV rm (qsize Q)) (s.getV rd (qsize Q)))).next := rfl
@[janus_exec] theorem exec_fmovGen (sf : Bool) (ftype rmode opcode rn rd : Nat) :
    exec (.fmovGen sf ftype rmode opcode rn rd) s =
      .ok (execFmovGen s sf rmode opcode rn rd).next := rfl

end ExecEqns

/-! ## Elements

`elem` of the values the code produces and reads back. The side conditions are closed
literal comparisons (`janus_disch` decides them). -/

theorem elem_lt (x e i : Nat) : elem x e i < 2 ^ e := Nat.mod_lt _ (Nat.two_pow_pos e)

attribute [janus_exec, janus_post] pairElem

@[janus_exec, janus_post] theorem elem_mod_two_pow {x k e i : Nat} (h : e * (i + 1) ≤ k) :
    elem (x % 2 ^ k) e i = elem x e i := by
  unfold elem
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  rw [Nat.mul_add, Nat.mul_one] at h
  by_cases hj : j < e
  · have : j + e * i < k := by omega
    simp [hj, this]
  · simp [hj]

theorem ofElems_lt (e n : Nat) (f : Nat → Nat) : ofElems e n f < 2 ^ (e * n) := by
  induction n with
  | zero => simp [ofElems]
  | succ n ih =>
    simp only [ofElems]
    have h1 : f n % 2 ^ e < 2 ^ e := Nat.mod_lt _ (Nat.two_pow_pos e)
    have h2 : 2 ^ (e * (n + 1)) = 2 ^ (e * n) * 2 ^ e := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    rw [h2]
    have : 2 ^ (e * n) * (f n % 2 ^ e) ≤ 2 ^ (e * n) * (2 ^ e - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : 2 ^ (e * n) * (2 ^ e - 1) + 2 ^ (e * n) = 2 ^ (e * n) * 2 ^ e := by
      have := Nat.two_pow_pos e
      rw [Nat.mul_sub, Nat.mul_one]; have := Nat.le_mul_of_pos_right (2 ^ (e*n)) this; omega
    omega

@[janus_exec, janus_post] theorem elem_ofElems {e n i : Nat} (f : Nat → Nat) (h : i < n) :
    elem (ofElems e n f) e i = f i % 2 ^ e := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [ofElems]
    have hlt := ofElems_lt e n f
    by_cases hi : i < n
    · rw [← elem_mod_two_pow (k := e * n) (by
          have := Nat.mul_le_mul_left e (show i + 1 ≤ n by omega); simpa using this),
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      exact ih hi
    · have : i = n := by omega
      subst this
      unfold elem
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add,
        Nat.mod_mod]

@[janus_exec, janus_post] theorem elem_and (x y e i : Nat) : elem (x &&& y) e i = elem x e i &&& elem y e i := by
  unfold elem; apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and]
  cases decide (j < e) <;> simp

@[janus_exec, janus_post] theorem elem_or (x y e i : Nat) : elem (x ||| y) e i = elem x e i ||| elem y e i := by
  unfold elem; apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_or]
  cases decide (j < e) <;> simp

theorem elem_readLE (m : Memory) {a n k i : Nat} (h : k * (i + 1) ≤ n) :
    elem (m.readLE a n) (8 * k) i = m.readLE (a + k * i) k := by
  unfold elem
  have e1 : 2 ^ (8 * k * i) = 256 ^ (k * i) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, Nat.mul_assoc]
  have e2 : 2 ^ (8 * k) = 256 ^ k := by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
  rw [e1, e2, Memory.readLE_div m a n (k * i) (by rw [Nat.mul_add] at h; omega),
    Memory.readLE_mod m _ _ k (by rw [Nat.mul_add, Nat.mul_one] at h; omega)]

@[janus_exec, janus_post] theorem elem_readLE_64 (m : Memory) {a n i : Nat} (h : 8 * (i + 1) ≤ n) :
    elem (m.readLE a n) 64 i = m.readLE (a + 8 * i) 8 := elem_readLE m (k := 8) h
@[janus_exec, janus_post] theorem elem_readLE_8 (m : Memory) {a n i : Nat} (h : i + 1 ≤ n) :
    elem (m.readLE a n) 8 i = m.readLE (a + i) 1 := by
  have := elem_readLE m (k := 1) (a := a) (n := n) (i := i) (by omega); simpa using this

@[janus_exec, janus_post] theorem elem_cmeq {size ds e i : Nat} (x y d : Nat) (he : 8 * 2 ^ size = e) (hi : i < ds / e) :
    elem (threeSameOp true size 17 ds x y d) e i = if elem x e i = elem y e i then 2 ^ e - 1 else 0 := by
  subst he
  have : threeSameOp true size 17 ds x y d = ofElems (8 * 2 ^ size) (ds / (8 * 2 ^ size)) fun i =>
      if decide (elem x (8 * 2 ^ size) i = elem y (8 * 2 ^ size) i) = true then onesN (8 * 2 ^ size) else 0 := rfl
  rw [this, elem_ofElems _ hi]
  simp only [onesN, decide_eq_true_eq]
  have h1 : (2 ^ (8 * 2 ^ size) - 1) % 2 ^ (8 * 2 ^ size) = 2 ^ (8 * 2 ^ size) - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
  split <;> simp [h1]

@[janus_exec, janus_post] theorem threeSameOp_and (ds x y d : Nat) : threeSameOp false 0 3 ds x y d = x &&& y := rfl
@[janus_exec, janus_post] theorem threeSameOp_orr (ds x y d : Nat) : threeSameOp false 2 3 ds x y d = x ||| y := rfl

@[janus_exec, janus_post] theorem elem_addp {size ds e i : Nat} (x y d : Nat) (he : 8 * 2 ^ size = e) (hi : i < ds / e) :
    elem (threeSameOp false size 23 ds x y d) e i =
      (pairElem x y e (ds / e) (2 * i) + pairElem x y e (ds / e) (2 * i + 1)) % 2 ^ e := by
  subst he
  have : threeSameOp false size 23 ds x y d = ofElems (8 * 2 ^ size) (ds / (8 * 2 ^ size)) fun i =>
      pairElem x y (8 * 2 ^ size) (ds / (8 * 2 ^ size)) (2 * i) +
        pairElem x y (8 * 2 ^ size) (ds / (8 * 2 ^ size)) (2 * i + 1) := rfl
  rw [this, elem_ofElems _ hi]

@[janus_exec, janus_post] theorem ite_land_ite (p q : Prop) [Decidable p] [Decidable q] (a : Nat) :
    ((if p then a else 0) &&& (if q then a else 0)) = if p ∧ q then a else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

end Janus.Tactic

namespace Janus.Tactic

open Janus Janus.Arm64

/-! ### The same, with the literals `simp` normalises `2 ^ 128`, `2 ^ 64`, `2 ^ 8` to -/

@[janus_exec, janus_post] theorem elem_mod_2_128 {x e i : Nat} (h : e * (i + 1) ≤ 128) :
    elem (x % 340282366920938463463374607431768211456) e i = elem x e i :=
  elem_mod_two_pow (k := 128) h
@[janus_exec, janus_post] theorem elem_mod_2_64 {x e i : Nat} (h : e * (i + 1) ≤ 64) :
    elem (x % 18446744073709551616) e i = elem x e i :=
  elem_mod_two_pow (k := 64) h
@[janus_exec, janus_post] theorem elem_64_mod (x i : Nat) :
    elem x 64 i % 18446744073709551616 = elem x 64 i := Nat.mod_eq_of_lt (elem_lt x 64 i)
@[janus_exec, janus_post] theorem elem_8_mod (x i : Nat) : elem x 8 i % 256 = elem x 8 i :=
  Nat.mod_eq_of_lt (elem_lt x 8 i)
@[janus_exec, janus_post] theorem readLE_mod_16 (m : Memory) (a : Nat) :
    m.readLE a 16 % 340282366920938463463374607431768211456 = m.readLE a 16 :=
  Nat.mod_eq_of_lt (Memory.readLE_lt m a 16)

attribute [janus_exec, janus_post] Nat.mod_mod

end Janus.Tactic

namespace Janus.Tactic

/-- Truncation of a selected value (CMEQ masks read back with `UMOV`). -/
@[janus_exec, janus_post] theorem ite_mod_nat (p : Prop) [Decidable p] (a b n : Nat) :
    (if p then a else b) % n = if p then a % n else b % n := by
  by_cases h : p <;> simp [h]

/-- A CMEQ mask is zero iff the comparison failed. -/
@[janus_exec, janus_post] theorem ite_eq_zero_iff_not (p : Prop) [Decidable p] {a : Nat} (ha : a ≠ 0) :
    ((if p then a else 0) = 0) = ¬p := by
  by_cases h : p <;> simp [h, ha]

end Janus.Tactic

namespace Janus.Tactic

open Janus Janus.Arm64

/-! ## Comparing memory word by word (what `memequal` decides) -/

/-- Two reads are equal iff their low and high parts are. -/
theorem readLE_add_eq_iff (m : Memory) (a b n k : Nat) :
    m.readLE a (n + k) = m.readLE b (n + k) ↔
      m.readLE a n = m.readLE b n ∧ m.readLE (a + n) k = m.readLE (b + n) k := by
  rw [Memory.readLE_add, Memory.readLE_add]
  have ha := Memory.readLE_lt m a n
  have hb := Memory.readLE_lt m b n
  have hp : 0 < 256 ^ n := Nat.pow_pos (by decide)
  constructor
  · intro h
    have h1 := congrArg (· % 256 ^ n) h
    have h2 := congrArg (· / 256 ^ n) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
    simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb,
      Nat.zero_add] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]

/-- 64 bytes are equal iff their eight words are. -/
theorem readLE_64_eq_iff (m : Memory) (a b : Nat) :
    m.readLE a 64 = m.readLE b 64 ↔
      m.readLE a 8 = m.readLE b 8 ∧ m.readLE (a + 8) 8 = m.readLE (b + 8) 8 ∧
      m.readLE (a + 16) 8 = m.readLE (b + 16) 8 ∧ m.readLE (a + 24) 8 = m.readLE (b + 24) 8 ∧
      m.readLE (a + 32) 8 = m.readLE (b + 32) 8 ∧ m.readLE (a + 40) 8 = m.readLE (b + 40) 8 ∧
      m.readLE (a + 48) 8 = m.readLE (b + 48) 8 ∧ m.readLE (a + 56) 8 = m.readLE (b + 56) 8 := by
  rw [show 64 = 8 + 56 from rfl, readLE_add_eq_iff, show 56 = 8 + 48 from rfl, readLE_add_eq_iff,
    show 48 = 8 + 40 from rfl, readLE_add_eq_iff, show 40 = 8 + 32 from rfl, readLE_add_eq_iff,
    show 32 = 8 + 24 from rfl, readLE_add_eq_iff, show 24 = 8 + 16 from rfl, readLE_add_eq_iff,
    show 16 = 8 + 8 from rfl, readLE_add_eq_iff]

end Janus.Tactic

namespace Janus.Tactic

open Janus Janus.Arm64

/-! ## Byte-mask arithmetic

What `internal/bytealg` computes from CMEQ masks: a *syndrome* with two bits per byte
(`synd`, whose trailing zeros locate the first match: `ctzN_synd`, read off with RBIT + CLZ:
`clzNat_rbitNat`), and the "any match?" test that adds two vectors of byte masks
(`maskSum_add_mod`). These are proof tools for proofs through the runtime's SIMD code; they
are not used by the executor. -/

/-- `Σ_{i<n} 4^i * [f i]`, lowest element first. -/
def synd (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => (f 0).toNat + 4 * synd (fun i => f (i + 1)) n

/-- The first `i < n` with `f i`, or `n`. -/
def firstTrue (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if f 0 then 0 else firstTrue (fun i => f (i + 1)) n + 1

/-- Trailing zeros of the low `n` bits (`n` when they are all zero). -/
def ctzN : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => if x % 2 = 1 then 0 else ctzN n (x / 2) + 1

theorem rbitNat_lt (n x : Nat) : rbitNat n x < 2 ^ n := by
  induction n generalizing x with
  | zero => simp [rbitNat]
  | succ n ih =>
    simp only [rbitNat]
    have := ih (x / 2)
    have h2 : x % 2 ≤ 1 := by omega
    rw [Nat.pow_succ]
    have : x % 2 * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ h2
    omega

theorem clzNat_rbitNat (n x : Nat) : clzNat n (rbitNat n x) = ctzN n x := by
  induction n generalizing x with
  | zero => simp [clzNat, ctzN]
  | succ n ih =>
    simp only [clzNat, rbitNat, ctzN]
    have hr := rbitNat_lt n (x / 2)
    have hb : (x % 2 * 2 ^ n + rbitNat n (x / 2)).testBit n = decide (x % 2 = 1) := by
      rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hr]
      simp only [Nat.lt_irrefl, ite_false, Nat.sub_self, Nat.testBit_zero]
      have : x % 2 < 2 := Nat.mod_lt _ (by decide)
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with h | h <;> simp [h]
    simp only [hb]
    by_cases h : x % 2 = 1
    · simp [h]
    · have h0 : x % 2 = 0 := by omega
      simp [h0, ih, Nat.add_comm]

theorem synd_lt (f : Nat → Bool) (n : Nat) : synd f n < 4 ^ n := by
  induction n generalizing f with
  | zero => simp [synd]
  | succ n ih =>
    simp only [synd, Nat.pow_succ]
    have := ih (fun i => f (i + 1))
    have : (f 0).toNat ≤ 1 := Bool.toNat_le _
    omega

theorem ctzN_synd (f : Nat → Bool) (n m : Nat) (hm : 2 * n ≤ m) (hf : ∃ i < n, f i = true) :
    ctzN m (synd f n) = 2 * firstTrue f n := by
  induction n generalizing f m with
  | zero => obtain ⟨i, hi, _⟩ := hf; omega
  | succ n ih =>
    simp only [synd, firstTrue]
    cases h0 : f 0
    · obtain ⟨i, hi, hfi⟩ := hf
      have hi0 : i ≠ 0 := by rintro rfl; simp [h0] at hfi
      have hf' : ∃ i < n, (fun i => f (i + 1)) i = true := ⟨i - 1, by omega, by
        show f (i - 1 + 1) = true; rw [show i - 1 + 1 = i by omega]; exact hfi⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      have e1 : ctzN (m' + 2) (4 * synd (fun i => f (i + 1)) n) = ctzN m' (synd (fun i => f (i + 1)) n) + 2 := by
        simp only [ctzN]
        rw [show 4 * synd (fun i => f (i + 1)) n % 2 = 0 by omega,
          show 4 * synd (fun i => f (i + 1)) n / 2 % 2 = 0 by omega,
          show 4 * synd (fun i => f (i + 1)) n / 2 / 2 = synd (fun i => f (i + 1)) n by omega]
        simp
      simp only [Bool.toNat_false, Nat.zero_add, e1, ih _ m' (by omega) hf']
      simp; omega
    · simp only [Bool.toNat_true, ite_true]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [ctzN]
      rw [show (1 + 4 * synd (fun i => f (i + 1)) n) % 2 = 1 by omega]; simp

theorem synd_ne_zero (f : Nat → Bool) (n : Nat) (hf : ∃ i < n, f i = true) : synd f n ≠ 0 := by
  induction n generalizing f with
  | zero => obtain ⟨i, hi, _⟩ := hf; omega
  | succ n ih =>
    simp only [synd]
    cases h0 : f 0
    · obtain ⟨i, hi, hfi⟩ := hf
      have hi0 : i ≠ 0 := by rintro rfl; simp [h0] at hfi
      have := ih (fun i => f (i + 1)) ⟨i - 1, by omega, by show f (i - 1 + 1) = true; rw [show i - 1 + 1 = i by omega]; exact hfi⟩
      simp only [Bool.toNat_false]; omega
    · simp

theorem synd_eq_zero (f : Nat → Bool) (n : Nat) (hf : ∀ i < n, f i = false) : synd f n = 0 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [synd, hf 0 (by omega), Bool.toNat_false, Nat.zero_add]
    rw [ih _ (fun i hi => hf (i + 1) (by omega))]

/-- `Σ_{i<n} 255 * 256^i * [f i]`: a vector of `n` byte masks (`0x00`/`0xFF`). -/
def maskSum (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => 255 * (f 0).toNat + 256 * maskSum (fun i => f (i + 1)) n

/-- The sum of two byte-mask vectors is `0 mod 256^n` only if both are zero. -/
theorem maskSum_add_mod (f g : Nat → Bool) (n : Nat) (h : (maskSum f n + maskSum g n) % 256 ^ n = 0) :
    ∀ i < n, f i = false ∧ g i = false := by
  induction n generalizing f g with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [maskSum] at h
    have h256 : (255 * (f 0).toNat + 255 * (g 0).toNat) % 256 = 0 := by
      have := congrArg (· % 256) h
      rw [Nat.pow_succ, Nat.mod_mul_left_mod] at this
      omega
    have hf0 : f 0 = false ∧ g 0 = false := by
      cases hf : f 0 <;> cases hg : g 0 <;> simp [hf, hg] at h256 ⊢
    have h' : (maskSum (fun i => f (i + 1)) n + maskSum (fun i => g (i + 1)) n) % 256 ^ n = 0 := by
      rw [hf0.1, hf0.2] at h
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.zero_add] at h
      rw [← Nat.mul_add, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mul_mod_mul_left] at h
      omega
    intro i hi
    cases i with
    | zero => exact hf0
    | succ i => exact ih _ _ h' i (by omega)

theorem firstTrue_add (f : Nat → Bool) (a b : Nat) :
    firstTrue f (a + b) =
      if ∃ i < a, f i = true then firstTrue f a else a + firstTrue (fun i => f (a + i)) b := by
  induction a generalizing f with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [firstTrue]
    cases h0 : f 0
    · simp only [Bool.false_eq_true, ite_false]
      rw [ih]
      have e : (∃ i < a + 1, f i = true) ↔ ∃ i < a, f (i + 1) = true := by
        constructor
        · rintro ⟨i, hi, hfi⟩
          cases i with
          | zero => simp [h0] at hfi
          | succ i => exact ⟨i, by omega, hfi⟩
        · rintro ⟨i, hi, hfi⟩; exact ⟨i + 1, by omega, hfi⟩
      by_cases hx : ∃ i < a, f (i + 1) = true
      · simp only [hx, e.mpr hx, ite_true]
      · have hx' : ¬∃ i < a + 1, f i = true := fun h => hx (e.mp h)
        simp only [hx, hx', ite_false]
        have : (fun i => (fun i => f (i + 1)) (a + i)) = (fun i => f (a + 1 + i)) := by
          funext i; show f (a + i + 1) = f (a + 1 + i); rw [show a + i + 1 = a + 1 + i by omega]
        rw [this]
        clear e hx hx' this ih
        omega
    · have : ∃ i < a + 1, f i = true := ⟨0, by omega, h0⟩
      simp only [this, ite_true]


/-- A 64-bit element as its eight bytes. -/
theorem elem_64_bytes (x j : Nat) : elem x 64 j =
    elem x 8 (8 * j) + 256 * elem x 8 (8 * j + 1) + 65536 * elem x 8 (8 * j + 2) +
      16777216 * elem x 8 (8 * j + 3) + 4294967296 * elem x 8 (8 * j + 4) +
      1099511627776 * elem x 8 (8 * j + 5) + 281474976710656 * elem x 8 (8 * j + 6) +
      72057594037927936 * elem x 8 (8 * j + 7) := by
  unfold elem
  generalize hy : x / 2 ^ (64 * j) = y
  have hk : ∀ i, x / 2 ^ (8 * (8 * j + i)) = y / 256 ^ i := by
    intro i
    rw [← hy, Nat.div_div_eq_div_mul, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, ← Nat.pow_add]
    congr 2; omega
  have h0 : x / 2 ^ (8 * (8 * j)) = y := by rw [← hy]; congr 2; omega
  rw [h0, hk 1, hk 2, hk 3, hk 4, hk 5, hk 6, hk 7]
  simp only [Nat.reducePow]
  rw [show (18446744073709551616 : Nat) = 256 * (256 * (256 * (256 * (256 * (256 * (256 * 256)))))) from rfl]
  simp only [Nat.mod_mul, Nat.div_div_eq_div_mul]
  simp only [Nat.reduceMul]
  omega

theorem ite_land_nat (p : Prop) [Decidable p] (a m : Nat) :
    ((if p then a else 0) &&& m) = if p then a &&& m else 0 := by
  by_cases h : p <;> simp [h]

theorem ite_add_ite_mod (p q : Prop) [Decidable p] [Decidable q] {a b n : Nat} (h : a + b < n) :
    ((if p then a else 0) + (if q then b else 0)) % n = (if p then a else 0) + (if q then b else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, ite_true, ite_false] <;>
    exact Nat.mod_eq_of_lt (by omega)

theorem ite4_mod (p q r t : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable t]
    {a b c d n : Nat} (h : a + b + c + d < n) :
    ((if p then a else 0) + (if q then b else 0) + ((if r then c else 0) + (if t then d else 0))) % n =
      (if p then a else 0) + (if q then b else 0) + ((if r then c else 0) + (if t then d else 0)) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases ht : t <;>
    simp only [hp, hq, hr, ht, ite_true, ite_false] <;> exact Nat.mod_eq_of_lt (by omega)

theorem ite_eq_mul_toNat (p : Prop) [Decidable p] (k : Nat) :
    (if p then k else 0) = k * (decide p).toNat := by
  by_cases h : p <;> simp [h]


/-- OR of two masks with the same value. -/
theorem ite_lor_ite (p q : Prop) [Decidable p] [Decidable q] (a : Nat) :
    ((if p then a else 0) ||| (if q then a else 0)) = if p ∨ q then a else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

end Janus.Tactic
