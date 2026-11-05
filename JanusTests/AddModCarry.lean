import Janus

/-! # `AddMod` fast path (holiman uint256, amd64): the closers that took minutes (S16)

Two of the goals `janus64_run` left for the fast path of `(*Int).AddMod`, as FV-F extracted them (the stack stores already
removed by the frame lemmas), with the closer that took 6 minutes (`f0`) and more than 30 minutes (`f2`) with `omega`
(about forty nested `/ 2^64` and `% 2^64` of carries, eight branch hypotheses, thirteen address disjunctions). Here they
close in seconds, kernel-checked:

* `janus_carry_simp`: the `SBB` borrow chains into floors and remainders;
* `janus_carry_nf`: every relation to the relation of the carry normal forms (value level: `Vx + Vy + 2^256 - 2 Vm` over
  `2^256`, the four limbs of a value one atom `readLE m a 32`);
* `janus_omega_values`: the bounds of those quotients, the hypotheses that make `omega` split cleared, `omega`.

Without them the same goal is the 6-minute (`f0`) / unfinished (`f2`) `omega`. -/

namespace JanusTests.AddModCarry
open Janus Janus.Amd64

set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 8000000

theorem readLE8_lt (m : Janus.Arm64.Memory) (a : Nat) : m.readLE a 8 < 18446744073709551616 := by
  simpa using Janus.Arm64.Memory.readLE_lt m a 8

def addmodSpec (x y m : Nat) : Nat := if m = 0 then 0 else (x + y) % m

theorem noov_of (c : Prop) [Decidable c] (h : (if c then (1#64) else (0#64)).toNat = 0) : (decide c).toNat = 0 := by
  by_cases hc : c
  · simp [hc] at h
  · simp [hc]

theorem dec_div (A : Nat) (h : A < 2 * 18446744073709551616) :
    (decide (18446744073709551616 ≤ A)).toNat = A / 18446744073709551616 := by
  by_cases hc : 18446744073709551616 ≤ A
  · simp only [hc, decide_true, Bool.toNat_true]; omega
  · simp only [hc, decide_false, Bool.toNat_false]; omega

theorem f0_AddModReduceX (s : Janus.Amd64.State) (z x y m : BitVec 64) (w_d1 w_d2: Janus.Arm64.Memory)
  (z x y m : BitVec 64)
  (hsp : 896 ≤ BitVec.toNat (s.regs 4))
  (hlow : 840 ≤ BitVec.toNat (s.regs 4))
  (hnw : BitVec.toNat (s.regs 4) + 40 ≤ 2 ^ 48)
  (hzw : z.toNat + 32 ≤ 2 ^ 48)
  (hxw : x.toNat + 32 ≤ 2 ^ 48)
  (hyw : y.toNat + 32 ≤ 2 ^ 48)
  (hmw : m.toNat + 32 ≤ 2 ^ 48)
  (hdz : z.toNat + 32 ≤ BitVec.toNat (s.regs 4) - 840 ∨ BitVec.toNat (s.regs 4) + 40 ≤ z.toNat)
  (hdx : x.toNat + 32 ≤ BitVec.toNat (s.regs 4) - 840 ∨ BitVec.toNat (s.regs 4) + 40 ≤ x.toNat)
  (hdy : y.toNat + 32 ≤ BitVec.toNat (s.regs 4) - 840 ∨ BitVec.toNat (s.regs 4) + 40 ≤ y.toNat)
  (hdm : m.toNat + 32 ≤ BitVec.toNat (s.regs 4) - 840 ∨ BitVec.toNat (s.regs 4) + 40 ≤ m.toNat)
  (hzm : z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat)
  (hzx : z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat)
  (hzy : z = y ∨ z.toNat + 32 ≤ y.toNat ∨ y.toNat + 32 ≤ z.toNat)
  (hdg :
  BitVec.toNat (s.regs 14) + 24 ≤ BitVec.toNat (s.regs 4) - 840 ∨
    BitVec.toNat (s.regs 4) + 40 ≤ BitVec.toNat (s.regs 14) + 16)
  (hdgz : BitVec.toNat (s.regs 14) + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ BitVec.toNat (s.regs 14) + 16)
  (h_ret : Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 4)) 8 = ret)
  (hgl :
  load s.mem (BitVec.toNat (s.regs 14) + 16) 8 = Except.ok (Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 14) + 16) 8))
  (hgb : Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 14) + 16) 8 + 768 < BitVec.toNat (s.regs 4))
  (hnw2 : BitVec.toNat (s.regs 14) + 16 + 8 ≤ 2 ^ 48)
  (h_ddisj0_0 : BitVec.toNat (s.regs 4) - 840 + (840 + 40) ≤ 5184320 ∨ 5184320 + 96 ≤ BitVec.toNat (s.regs 4) - 840)
  (hm3 : Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ≠ 0)
  (hx3 : Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8 ≤ Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8)
  (hy3 : Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8 ≤ Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8)
  (hbr_d6 :
  ¬(BitVec.toNat (s.regs 4) - 232 < Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 14) + 16) 8 ∨
      (18446744073709551616 - (232 + Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 14) + 16) 8) +
            BitVec.toNat (s.regs 4)) %
          18446744073709551616 =
        0))
  (hbr_d5 : ¬Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 = 0)
  (hbr_d4 :
  ¬(¬Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8 < Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ∧
      ¬(18446744073709551616 - Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 +
              Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) %
            18446744073709551616 =
          0))
  (hbr_d3 :
  ¬(¬Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8 < Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ∧
      ¬(18446744073709551616 - Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 +
              Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) %
            18446744073709551616 =
          0))
  (hbr_d2 :
  Janus.Arm64.Memory.readLE s.mem m.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
        340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ≤
    Janus.Arm64.Memory.readLE s.mem x.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 +
        340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8)
  (hbr_d1 :
  Janus.Arm64.Memory.readLE s.mem m.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
        340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ≤
    Janus.Arm64.Memory.readLE s.mem y.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
        340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8)
  (hbr_d :
  (if
          18446744073709551616 ≤
            (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8))
                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                      (decide
                        (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 <
                          Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                            (decide
                                (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat +
                (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8))
                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                      (decide
                        (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 <
                          Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                            (decide
                                (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat +
              (decide
                  (18446744073709551616 ≤
                    (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8))
                              (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                              (decide
                                (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                        (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                              (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                              (decide
                                (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                      (decide
                          (18446744073709551616 ≤
                            (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8))
                                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                      (decide
                                        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                                (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                      (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                              (decide
                                  (18446744073709551616 ≤
                                    (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                          Janus.Arm64.Memory.readLE s.mem y.toNat 8) %
                                        18446744073709551616 +
                                      (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                          Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                        18446744073709551616)).toNat)).toNat)).toNat then
        1#64
      else 0#64).toNat =
    0)
  (hbr :
  ¬Janus.Arm64.Memory.readLE s.mem m.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
          340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
        6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ≤
      ((18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 + Janus.Arm64.Memory.readLE s.mem y.toNat 8) %
                  18446744073709551616 +
                (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 + Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                  18446744073709551616) %
              18446744073709551616 +
            18446744073709551616 *
              (((subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8))
                          (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                          (decide
                            (Janus.Arm64.Memory.readLE s.mem y.toNat 8 < Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                    (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                          (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                          (decide
                            (Janus.Arm64.Memory.readLE s.mem x.toNat 8 < Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                  (decide
                      (18446744073709551616 ≤
                        (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                              Janus.Arm64.Memory.readLE s.mem y.toNat 8) %
                            18446744073709551616 +
                          (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                              Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                            18446744073709551616)).toNat) %
                18446744073709551616) +
          340282366920938463463374607431768211456 *
            (((subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8))
                        (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                        (decide
                          (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 <
                            Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                              (decide
                                  (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                    Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                  (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                        (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                        (decide
                          (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                            Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                              (decide
                                  (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                    Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                (decide
                    (18446744073709551616 ≤
                      (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8))
                                (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                (decide
                                  (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                    Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                          (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                (decide
                                  (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                    Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                        (decide
                            (18446744073709551616 ≤
                              (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                    Janus.Arm64.Memory.readLE s.mem y.toNat 8) %
                                  18446744073709551616 +
                                (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                    Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                  18446744073709551616)).toNat)).toNat) %
              18446744073709551616) +
        6277101735386680763835789423207666416102355444464034512896 *
          (((subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8))
                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                      (decide
                        (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 <
                          Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                            (decide
                                (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat +
                (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8))
                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                      (decide
                        (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 <
                          Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                            (decide
                                (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat +
              (decide
                  (18446744073709551616 ≤
                    (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8))
                              (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                              (decide
                                (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                        (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                              (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                              (decide
                                (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                      (decide
                          (18446744073709551616 ≤
                            (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8))
                                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                      (decide
                                        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                                (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                      (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                              (decide
                                  (18446744073709551616 ≤
                                    (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                          Janus.Arm64.Memory.readLE s.mem y.toNat 8) %
                                        18446744073709551616 +
                                      (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                          Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                        18446744073709551616)).toNat)).toNat)).toNat) %
            18446744073709551616)
) :
  ((18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 + Janus.Arm64.Memory.readLE s.mem y.toNat 8) %
                  18446744073709551616 +
                (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 + Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                  18446744073709551616) %
              18446744073709551616 +
            18446744073709551616 *
              (((subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8))
                          (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                          (decide
                            (Janus.Arm64.Memory.readLE s.mem y.toNat 8 < Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                    (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                          (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                          (decide
                            (Janus.Arm64.Memory.readLE s.mem x.toNat 8 < Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                  ((18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 + Janus.Arm64.Memory.readLE s.mem y.toNat 8) %
                        18446744073709551616 +
                      (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                          Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                        18446744073709551616) /
                    18446744073709551616) %
                18446744073709551616) +
          340282366920938463463374607431768211456 *
            (((subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8))
                        (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                        (decide
                          (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 <
                            Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                              (decide
                                  (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                    Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                  (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                        (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                        (decide
                          (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                            Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                              (decide
                                  (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                    Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                ((subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8))
                            (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                            (decide
                              (Janus.Arm64.Memory.readLE s.mem y.toNat 8 < Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                      (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                            (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                            (decide
                              (Janus.Arm64.Memory.readLE s.mem x.toNat 8 < Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                    ((18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                            Janus.Arm64.Memory.readLE s.mem y.toNat 8) %
                          18446744073709551616 +
                        (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                            Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                          18446744073709551616) /
                      18446744073709551616) /
                  18446744073709551616) %
              18446744073709551616) +
        6277101735386680763835789423207666416102355444464034512896 *
          (((subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8))
                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                      (decide
                        (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 <
                          Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                            (decide
                                (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat +
                (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8))
                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                      (decide
                        (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 <
                          Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                            (decide
                                (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat +
              ((subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8))
                          (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                          (decide
                            (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 <
                              Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                (decide
                                    (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                      Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                    (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                          (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                          (decide
                            (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                              Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                (decide
                                    (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                      Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                  ((subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8))
                              (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                              (decide
                                (Janus.Arm64.Memory.readLE s.mem y.toNat 8 <
                                  Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                        (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                              (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                              (decide
                                (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                  Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                      ((18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                              Janus.Arm64.Memory.readLE s.mem y.toNat 8) %
                            18446744073709551616 +
                          (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                              Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                            18446744073709551616) /
                        18446744073709551616) /
                    18446744073709551616) /
                18446744073709551616) %
            18446744073709551616) =
      addmodSpec
        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 +
            340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8)
        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
            340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8)
        (Janus.Arm64.Memory.readLE s.mem m.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
            340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8) := by
  have bx0 := readLE8_lt s.mem x.toNat
  have bx1 := readLE8_lt s.mem (x.toNat + 8)
  have bx2 := readLE8_lt s.mem (x.toNat + 16)
  have bx3 := readLE8_lt s.mem (x.toNat + 24)
  have by0 := readLE8_lt s.mem y.toNat
  have by1 := readLE8_lt s.mem (y.toNat + 8)
  have by2 := readLE8_lt s.mem (y.toNat + 16)
  have by3 := readLE8_lt s.mem (y.toNat + 24)
  have bm0 := readLE8_lt s.mem m.toNat
  have bm1 := readLE8_lt s.mem (m.toNat + 8)
  have bm2 := readLE8_lt s.mem (m.toNat + 16)
  have bm3 := readLE8_lt s.mem (m.toNat + 24)
  have hc1 := noov_of _ (by assumption)
  simp (disch := omega) only [dec_div] at *
  janus_carry_simp at *
  unfold addmodSpec
  rw [if_neg (by omega)]
  refine (Janus.Carry.mod_cases3 _ _ _ ?_ ?_).symm <;> janus_carry_nf at * <;> janus_omega_values

theorem f2_AddModReduceXY (s : Janus.Amd64.State) (z x y m : BitVec 64) (w_d1 w_d2: Janus.Arm64.Memory)
  (z x y m : BitVec 64)
  (hsp : 896 ≤ BitVec.toNat (s.regs 4))
  (hlow : 840 ≤ BitVec.toNat (s.regs 4))
  (hnw : BitVec.toNat (s.regs 4) + 40 ≤ 2 ^ 48)
  (hzw : z.toNat + 32 ≤ 2 ^ 48)
  (hxw : x.toNat + 32 ≤ 2 ^ 48)
  (hyw : y.toNat + 32 ≤ 2 ^ 48)
  (hmw : m.toNat + 32 ≤ 2 ^ 48)
  (hdz : z.toNat + 32 ≤ BitVec.toNat (s.regs 4) - 840 ∨ BitVec.toNat (s.regs 4) + 40 ≤ z.toNat)
  (hdx : x.toNat + 32 ≤ BitVec.toNat (s.regs 4) - 840 ∨ BitVec.toNat (s.regs 4) + 40 ≤ x.toNat)
  (hdy : y.toNat + 32 ≤ BitVec.toNat (s.regs 4) - 840 ∨ BitVec.toNat (s.regs 4) + 40 ≤ y.toNat)
  (hdm : m.toNat + 32 ≤ BitVec.toNat (s.regs 4) - 840 ∨ BitVec.toNat (s.regs 4) + 40 ≤ m.toNat)
  (hzm : z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat)
  (hzx : z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat)
  (hzy : z = y ∨ z.toNat + 32 ≤ y.toNat ∨ y.toNat + 32 ≤ z.toNat)
  (hdg :
  BitVec.toNat (s.regs 14) + 24 ≤ BitVec.toNat (s.regs 4) - 840 ∨
    BitVec.toNat (s.regs 4) + 40 ≤ BitVec.toNat (s.regs 14) + 16)
  (hdgz : BitVec.toNat (s.regs 14) + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ BitVec.toNat (s.regs 14) + 16)
  (h_ret : Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 4)) 8 = ret)
  (hgl :
  load s.mem (BitVec.toNat (s.regs 14) + 16) 8 = Except.ok (Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 14) + 16) 8))
  (hgb : Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 14) + 16) 8 + 768 < BitVec.toNat (s.regs 4))
  (hnw2 : BitVec.toNat (s.regs 14) + 16 + 8 ≤ 2 ^ 48)
  (h_ddisj0_0 : BitVec.toNat (s.regs 4) - 840 + (840 + 40) ≤ 5184320 ∨ 5184320 + 96 ≤ BitVec.toNat (s.regs 4) - 840)
  (hm3 : Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ≠ 0)
  (hx3 : Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8 ≤ Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8)
  (hy3 : Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8 ≤ Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8)
  (hbr_d6 :
  ¬(BitVec.toNat (s.regs 4) - 232 < Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 14) + 16) 8 ∨
      (18446744073709551616 - (232 + Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 14) + 16) 8) +
            BitVec.toNat (s.regs 4)) %
          18446744073709551616 =
        0))
  (hbr_d5 : ¬Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 = 0)
  (hbr_d4 :
  ¬(¬Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8 < Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ∧
      ¬(18446744073709551616 - Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 +
              Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) %
            18446744073709551616 =
          0))
  (hbr_d3 :
  ¬(¬Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8 < Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ∧
      ¬(18446744073709551616 - Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 +
              Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) %
            18446744073709551616 =
          0))
  (hbr_d2 :
  Janus.Arm64.Memory.readLE s.mem m.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
        340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ≤
    Janus.Arm64.Memory.readLE s.mem x.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 +
        340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8)
  (hbr_d1 :
  ¬Janus.Arm64.Memory.readLE s.mem m.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
          340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
        6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ≤
      Janus.Arm64.Memory.readLE s.mem y.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
          340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
        6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8)
  (hbr_d :
  (if
          18446744073709551616 ≤
            Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8 +
                (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8))
                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                      (decide
                        (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 <
                          Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                            (decide
                                (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat +
              (decide
                  (18446744073709551616 ≤
                    Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
                        (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                              (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                              (decide
                                (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                      (decide
                          (18446744073709551616 ≤
                            Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                                (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                      (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                              (decide
                                  (18446744073709551616 ≤
                                    Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                                      (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                          Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                        18446744073709551616)).toNat)).toNat)).toNat then
        1#64
      else 0#64).toNat =
    0)
  (hbr :
  Janus.Arm64.Memory.readLE s.mem m.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
        340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8 ≤
    (Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
              (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 + Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                18446744073709551616) %
            18446744073709551616 +
          18446744073709551616 *
            ((Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                  (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                        (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                        (decide
                          (Janus.Arm64.Memory.readLE s.mem x.toNat 8 < Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                (decide
                    (18446744073709551616 ≤
                      Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                        (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                            Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                          18446744073709551616)).toNat) %
              18446744073709551616) +
        340282366920938463463374607431768211456 *
          ((Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
                (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                      (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                      (decide
                        (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                          Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                            (decide
                                (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                  Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
              (decide
                  (18446744073709551616 ≤
                    Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                        (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                              (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                              (decide
                                (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                  Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                      (decide
                          (18446744073709551616 ≤
                            Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                              (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                  Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                18446744073709551616)).toNat)).toNat) %
            18446744073709551616) +
      6277101735386680763835789423207666416102355444464034512896 *
        ((Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8 +
              (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8))
                    (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                    (decide
                      (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 <
                        Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                          (decide
                              (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                  (decide
                                      (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                        Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat +
            (decide
                (18446744073709551616 ≤
                  Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
                      (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                            (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                            (decide
                              (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                  (decide
                                      (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                        Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                    (decide
                        (18446744073709551616 ≤
                          Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                              (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                    (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                    (decide
                                      (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                        Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                            (decide
                                (18446744073709551616 ≤
                                  Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                                    (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                        Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                      18446744073709551616)).toNat)).toNat)).toNat) %
          18446744073709551616)
) :
  (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                (Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                    (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 + Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                      18446744073709551616) %
                  18446744073709551616) %
              18446744073709551616 +
            18446744073709551616 *
              (subFlags
                    (BitVec.ofNat 64
                      (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                          (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                (decide
                                  (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                    Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                            (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                              18446744073709551616) /
                          18446744073709551616))
                    (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                    (decide
                      ((Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                            (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                              18446744073709551616) %
                          18446744073709551616 <
                        Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
          340282366920938463463374607431768211456 *
            (subFlags
                  (BitVec.ofNat 64
                    (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
                        (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                              (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                              (decide
                                (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                  Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                    (decide
                                        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                          Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                      (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                            (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                  (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                  (decide
                                    (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                      Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                          (Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                              (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                  Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                18446744073709551616) /
                            18446744073709551616) /
                        18446744073709551616))
                  (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                  (decide
                    ((Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                            (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                  (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                  (decide
                                    (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                      Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                          (Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                              (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                  Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                18446744073709551616) /
                            18446744073709551616) %
                        18446744073709551616 <
                      Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                        (decide
                            ((Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                                  (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                      Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                    18446744073709551616) %
                                18446744073709551616 <
                              Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
        6277101735386680763835789423207666416102355444464034512896 *
          (subFlags
                (BitVec.ofNat 64
                  (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8 +
                      (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8))
                            (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                            (decide
                              (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 <
                                Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                                  (decide
                                      (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                        Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                          (decide
                                              (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                                Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat +
                    (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
                          (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                                (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                                (decide
                                  (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                    Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                      (decide
                                          (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                            Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                        (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                              (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                    (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                    (decide
                                      (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                        Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                            (Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                                (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                    Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                  18446744073709551616) /
                              18446744073709551616) /
                          18446744073709551616) /
                      18446744073709551616))
                (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8))
                (decide
                  ((Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
                          (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8))
                                (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8))
                                (decide
                                  (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 <
                                    Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                                      (decide
                                          (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                            Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat))).fst.toNat +
                        (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                              (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                    (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                    (decide
                                      (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                        Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                            (Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                                (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                    Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                  18446744073709551616) /
                              18446744073709551616) /
                          18446744073709551616) %
                      18446744073709551616 <
                    Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
                      (decide
                          ((Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
                                  (subFlags (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8))
                                        (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8))
                                        (decide
                                          (Janus.Arm64.Memory.readLE s.mem x.toNat 8 <
                                            Janus.Arm64.Memory.readLE s.mem m.toNat 8))).fst.toNat +
                                (Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                                    (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                        Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                      18446744073709551616) /
                                  18446744073709551616) %
                              18446744073709551616 <
                            Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
                              (decide
                                  ((Janus.Arm64.Memory.readLE s.mem y.toNat 8 +
                                        (18446744073709551616 - Janus.Arm64.Memory.readLE s.mem m.toNat 8 +
                                            Janus.Arm64.Memory.readLE s.mem x.toNat 8) %
                                          18446744073709551616) %
                                      18446744073709551616 <
                                    Janus.Arm64.Memory.readLE s.mem m.toNat 8)).toNat)).toNat))).fst.toNat =
      addmodSpec
        (Janus.Arm64.Memory.readLE s.mem x.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8 +
            340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8)
        (Janus.Arm64.Memory.readLE s.mem y.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8 +
            340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8)
        (Janus.Arm64.Memory.readLE s.mem m.toNat 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 8) 8 +
            340282366920938463463374607431768211456 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * Janus.Arm64.Memory.readLE s.mem (m.toNat + 24) 8) := by
  have bx0 := readLE8_lt s.mem x.toNat
  have bx1 := readLE8_lt s.mem (x.toNat + 8)
  have bx2 := readLE8_lt s.mem (x.toNat + 16)
  have bx3 := readLE8_lt s.mem (x.toNat + 24)
  have by0 := readLE8_lt s.mem y.toNat
  have by1 := readLE8_lt s.mem (y.toNat + 8)
  have by2 := readLE8_lt s.mem (y.toNat + 16)
  have by3 := readLE8_lt s.mem (y.toNat + 24)
  have bm0 := readLE8_lt s.mem m.toNat
  have bm1 := readLE8_lt s.mem (m.toNat + 8)
  have bm2 := readLE8_lt s.mem (m.toNat + 16)
  have bm3 := readLE8_lt s.mem (m.toNat + 24)
  have hc1 := noov_of _ (by assumption)
  simp (disch := omega) only [dec_div] at *
  janus_carry_simp at *
  unfold addmodSpec
  rw [if_neg (by omega)]
  refine (Janus.Carry.mod_cases3 _ _ _ ?_ ?_).symm <;> janus_carry_nf at * <;> janus_omega_values

end JanusTests.AddModCarry
