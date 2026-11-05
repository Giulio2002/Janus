import Janus

/-! # `janus_carry_simp` and `janus_carry_nf` (S16): borrow chains and relations between carry chains

The `AddMod` fast path (holiman uint256) left goals whose closers needed `omega` over about forty nested
`% 2^64` / `/ 2^64` terms (6-10 minutes, or never). `janus_carry_simp` puts the `SBB`/`CMP` borrow chains in
the vocabulary of `janus_carry`; `janus_carry_nf` rewrites a relation between carry chains to the relation of
their carry normal forms (value level: `(X + 2^256 - M) / 2^256`), kernel-checked. Each test below is RED on the old
engine (the first tactic of each one fails or does not exist: the `fail_if_success` lines pin the old behaviour). -/

namespace JanusTests.CarryNf
open Janus Janus.Amd64 Janus.Tactic

set_option maxRecDepth 100000

/-- A four-limb difference, as `janus64_run` leaves it (`subFlags` limbs, nested borrows) equals `(X + 2^256 - M) % 2^256`.
`janus_carry` alone does not know `subFlags`. -/
example (x0 x1 x2 x3 m0 m1 m2 m3 : Nat) (hx0 : x0 < 18446744073709551616) (hx1 : x1 < 18446744073709551616)
    (hx2 : x2 < 18446744073709551616) (hx3 : x3 < 18446744073709551616) (hm0 : m0 < 18446744073709551616)
    (hm1 : m1 < 18446744073709551616) (hm2 : m2 < 18446744073709551616) (hm3 : m3 < 18446744073709551616) :
    (18446744073709551616 - m0 + x0) % 18446744073709551616
    + 18446744073709551616 * (subFlags (BitVec.ofNat 64 x1) (BitVec.ofNat 64 m1) (decide (x0 < m0))).fst.toNat
    + 340282366920938463463374607431768211456 * (subFlags (BitVec.ofNat 64 x2) (BitVec.ofNat 64 m2)
        (decide (x1 < m1 + (decide (x0 < m0)).toNat))).fst.toNat
    + 6277101735386680763835789423207666416102355444464034512896 * (subFlags (BitVec.ofNat 64 x3) (BitVec.ofNat 64 m3)
        (decide (x2 < m2 + (decide (x1 < m1 + (decide (x0 < m0)).toNat)).toNat))).fst.toNat
    = (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2
        + 6277101735386680763835789423207666416102355444464034512896 * x3
        + 115792089237316195423570985008687907853269984665640564039457584007913129639936
        - (m0 + 18446744073709551616 * m1 + 340282366920938463463374607431768211456 * m2
        + 6277101735386680763835789423207666416102355444464034512896 * m3))
      % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  fail_if_success janus_carry
  janus_carry_simp
  janus_carry

/-- "No borrow out of the four-limb chain" means `M ≤ X`: the hypothesis is the comparison of four nested `decide`s
(`omega` cannot read it); in normal form it is `1 = (X + 2^256 - M) / 2^256`. -/
example (x0 x1 x2 x3 m0 m1 m2 m3 : Nat) (hx0 : x0 < 18446744073709551616) (hx1 : x1 < 18446744073709551616)
    (hx2 : x2 < 18446744073709551616) (hx3 : x3 < 18446744073709551616) (hm0 : m0 < 18446744073709551616)
    (hm1 : m1 < 18446744073709551616) (hm2 : m2 < 18446744073709551616) (hm3 : m3 < 18446744073709551616)
    (h : (decide (x3 < m3 + (decide (x2 < m2 + (decide (x1 < m1 + (decide (x0 < m0)).toNat)).toNat)).toNat)).toNat = 0) :
    m0 + 18446744073709551616 * m1 + 340282366920938463463374607431768211456 * m2
        + 6277101735386680763835789423207666416102355444464034512896 * m3
      ≤ x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2
        + 6277101735386680763835789423207666416102355444464034512896 * x3 := by
  fail_if_success omega
  janus_carry_simp at h
  janus_carry_nf at h
  omega

/-- A carry out of an addition chain (the amd64 `ADC` shape) compared with a bound: the normal form is `(X + Y) / 2^256`. -/
example (x0 x1 x2 x3 y0 y1 y2 y3 : Nat) (hx0 : x0 < 18446744073709551616) (hx1 : x1 < 18446744073709551616)
    (hx2 : x2 < 18446744073709551616) (hx3 : x3 < 18446744073709551616) (hy0 : y0 < 18446744073709551616)
    (hy1 : y1 < 18446744073709551616) (hy2 : y2 < 18446744073709551616) (hy3 : y3 < 18446744073709551616)
    (h : (decide (18446744073709551616 ≤ y3 + x3 + (decide (18446744073709551616 ≤ y2 + x2 +
        (decide (18446744073709551616 ≤ y1 + x1 + (decide (18446744073709551616 ≤ y0 + x0)).toNat)).toNat)).toNat)).toNat = 0) :
    x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2
        + 6277101735386680763835789423207666416102355444464034512896 * x3
      + (y0 + 18446744073709551616 * y1 + 340282366920938463463374607431768211456 * y2
        + 6277101735386680763835789423207666416102355444464034512896 * y3)
      < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  fail_if_success omega
  janus_carry_nf at h
  omega

/-- A relation without a carry term is left alone (the tactic fails, like `simp`, and changes nothing). -/
example (a b : Nat) (h : a + 1 ≤ b) : a < b := by
  fail_if_success janus_carry_nf at h
  omega

/-- A relation whose side has no normal form (a truncated subtraction whose order is unknown) is left as it was. -/
example (a b : Nat) (h : (a - b) % 7 = 3) : (a - b) % 7 < 7 := by
  fail_if_success janus_carry_nf at h
  omega

end JanusTests.CarryNf
