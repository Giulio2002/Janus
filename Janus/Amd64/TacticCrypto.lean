import Janus.Amd64.TacticSSE
import Janus.Spec.AES

/-!
# Proof support for the x86 crypto extensions (WP-E)

Extends the `janus64_exec` / `janus64_post` simp sets so that `janus64_run` steps the
instructions of `Janus.Amd64.ExecCrypto`. Everything is proved from the model.

* `ExecCrypto.exec` is unfolded per constructor (definitional `rfl` equations, as `exec`); its
  operand plumbing is `ExecSSE`'s (`readN`, `readG`, `doneX`, `setReg`), already in the sets.
* The operations themselves (`aesRound`, `clmul`, `sha256rnds2`, ...) are **not** unfolded: a
  symbolic `XMM` register holds a term like `aesRound .enc x k`, which a proof relates to its
  specification (`Janus.Spec.AES.aesenc_eq`, ...). They are made irreducible so that `whnf`
  never expands an AES round on symbolic data; the kernel still evaluates them on literals.
* `aesRound_mod`, `clmul_mod`, ...: every result is a 128-bit value, so the `% 2^128` of
  writing it to an `XMM` register disappears.
-/

namespace Janus.Amd64.Tactic

open Janus.Amd64 Janus.Arm64 Janus.Tactic

janus_rfl_eqns ExecCrypto.exec [janus64_exec]

theorem xor_lt_128 {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) : a ^^^ b < 2 ^ 128 :=
  Nat.xor_lt_two_pow ha hb

theorem aesRound_lt (op : AesOp) (a k : Nat) (hk : k < 2 ^ 128) : ExecCrypto.aesRound op a k < 2 ^ 128 := by
  cases op <;> exact xor_lt_128 (ofElems_lt 8 16 _) hk

theorem xor_mod_two_pow (a b n : Nat) : (a ^^^ b) % 2 ^ n = (a % 2 ^ n) ^^^ (b % 2 ^ n) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  cases decide (j < n) <;> simp

theorem xor_mod_128 {a : Nat} (b : Nat) (ha : a < 2 ^ 128) :
    (a ^^^ b) % 340282366920938463463374607431768211456 = a ^^^ (b % 340282366920938463463374607431768211456) := by
  rw [show (340282366920938463463374607431768211456 : Nat) = 2 ^ 128 by rfl, xor_mod_two_pow,
    Nat.mod_eq_of_lt ha]

/-- `aesRound op a k` modulo `2^128` is the round with the key modulo `2^128`. -/
@[janus64_exec, janus64_post] theorem aesRound_mod (op : AesOp) (a k : Nat) :
    ExecCrypto.aesRound op a k % 340282366920938463463374607431768211456 =
      ExecCrypto.aesRound op a (k % 340282366920938463463374607431768211456) := by
  cases op <;> exact xor_mod_128 k (ofElems_lt 8 16 _)

theorem aesMixColumns_lt (inv : Bool) (x : Nat) : aesMixColumns inv x < 2 ^ 128 := ofElems_lt 8 16 _

@[janus64_exec, janus64_post] theorem aesMixColumns_mod (inv : Bool) (x : Nat) :
    aesMixColumns inv x % 340282366920938463463374607431768211456 = aesMixColumns inv x :=
  Nat.mod_eq_of_lt (aesMixColumns_lt inv x)

theorem keygenAssist_lt (b imm : Nat) : ExecCrypto.keygenAssist b imm < 2 ^ 128 := ofElems_lt 32 4 _

@[janus64_exec, janus64_post] theorem keygenAssist_mod (b imm : Nat) :
    ExecCrypto.keygenAssist b imm % 340282366920938463463374607431768211456 = ExecCrypto.keygenAssist b imm :=
  Nat.mod_eq_of_lt (keygenAssist_lt b imm)

theorem polyMult_lt : ∀ (k a : Nat) {b n : Nat}, b < 2 ^ n → polyMult k a b < 2 ^ (n + k)
  | 0, _, _, _, _ => Nat.two_pow_pos _
  | k + 1, a, b, n, hb => by
    simp only [polyMult]
    have ih := polyMult_lt k a hb
    have h1 : polyMult k a b < 2 ^ (n + (k + 1)) :=
      Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : (if a.testBit k = true then b * 2 ^ k else 0) < 2 ^ (n + (k + 1)) := by
      split
      · rw [Nat.pow_add, Nat.pow_succ]
        exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos k))
          (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by decide : 0 < 2)))
      · exact Nat.two_pow_pos _
    exact Nat.xor_lt_two_pow h1 h2

theorem clmul_lt (a b imm : Nat) : ExecCrypto.clmul a b imm < 2 ^ 128 :=
  polyMult_lt 64 _ (Janus.Tactic.elem_lt b 64 _)

@[janus64_exec, janus64_post] theorem clmul_mod (a b imm : Nat) :
    ExecCrypto.clmul a b imm % 340282366920938463463374607431768211456 = ExecCrypto.clmul a b imm :=
  Nat.mod_eq_of_lt (clmul_lt a b imm)

theorem shaOp_lt (op : ShaOp) (a b k : Nat) : ExecCrypto.shaOp op a b k < 2 ^ 128 := by
  cases op <;> exact ofElems_lt 32 4 _

@[janus64_exec, janus64_post] theorem shaOp_mod (op : ShaOp) (a b k : Nat) :
    ExecCrypto.shaOp op a b k % 340282366920938463463374607431768211456 = ExecCrypto.shaOp op a b k :=
  Nat.mod_eq_of_lt (shaOp_lt op a b k)

@[janus64_exec, janus64_post] theorem sha1rnds4_mod (a b imm : Nat) :
    ExecCrypto.sha1rnds4 a b imm % 340282366920938463463374607431768211456 = ExecCrypto.sha1rnds4 a b imm :=
  Nat.mod_eq_of_lt (ofElems_lt 32 4 _)

set_option allowUnsafeReducibility true in
attribute [irreducible] ExecCrypto.aesRound ExecCrypto.keygenAssist ExecCrypto.clmul ExecCrypto.shaOp
  ExecCrypto.sha1rnds4 aesMixColumns

end Janus.Amd64.Tactic
