import Janus

/-! # `janus_frame`: the side goals of a callee's frame are tried on the goal's own hypotheses first (S6)

`proveFrame` relates a memory to a `MemFrame` hypothesis of a callee through `∀ a n, Outside a n rs → Outside a n rs ∧
Outside a n rs₁`. The three closers of that side goal are tried with the hypotheses about the goal's own atoms first
(`janus_clear_irrel`), then with the whole context: an `omega` over the whole context of a run (hundreds of facts)
spends seconds per fact (FV-B DivModB: 32 leaves, 1060 s -> 236 s in `janus_frame`). When the goal needs a fact about
other atoms the first attempt fails on its small context and the whole context is used as before. -/

namespace JanusTests.FrameClear

open Janus Janus.Arm64 Janus.Tactic

/-- The facts the side goal needs are about the goal's atoms (`a n p`): the cleared attempt closes it. -/
example (m0 m1 m : Memory) (q p : Nat) (hqp : q ≤ p) (hp : p + 8 ≤ q + 100)
    (hf : MemFrame m1 m [(p, p + 8)]) (hm : MemFrame m0 m1 [(q, q + 100)]) : MemFrame m0 m [(q, q + 100)] := by
  janus_frame

/-- With many unrelated facts in the context (disjunctions about other numbers): the same. -/
example (m0 m1 m : Memory) (q p : Nat) (hqp : q ≤ p) (hp : p + 8 ≤ q + 100)
    (hf : MemFrame m1 m [(p, p + 8)]) (hm : MemFrame m0 m1 [(q, q + 100)]) (v0 w0 : Nat) (h0 : v0 + 3 ≤ w0 ∨ w0 + 5 ≤ v0) (v1 w1 : Nat) (h1 : v1 + 3 ≤ w1 ∨ w1 + 5 ≤ v1) (v2 w2 : Nat) (h2 : v2 + 3 ≤ w2 ∨ w2 + 5 ≤ v2) (v3 w3 : Nat) (h3 : v3 + 3 ≤ w3 ∨ w3 + 5 ≤ v3) (v4 w4 : Nat) (h4 : v4 + 3 ≤ w4 ∨ w4 + 5 ≤ v4) (v5 w5 : Nat) (h5 : v5 + 3 ≤ w5 ∨ w5 + 5 ≤ v5) (v6 w6 : Nat) (h6 : v6 + 3 ≤ w6 ∨ w6 + 5 ≤ v6) (v7 w7 : Nat) (h7 : v7 + 3 ≤ w7 ∨ w7 + 5 ≤ v7) (v8 w8 : Nat) (h8 : v8 + 3 ≤ w8 ∨ w8 + 5 ≤ v8) (v9 w9 : Nat) (h9 : v9 + 3 ≤ w9 ∨ w9 + 5 ≤ v9) (v10 w10 : Nat) (h10 : v10 + 3 ≤ w10 ∨ w10 + 5 ≤ v10) (v11 w11 : Nat) (h11 : v11 + 3 ≤ w11 ∨ w11 + 5 ≤ v11) (v12 w12 : Nat) (h12 : v12 + 3 ≤ w12 ∨ w12 + 5 ≤ v12) (v13 w13 : Nat) (h13 : v13 + 3 ≤ w13 ∨ w13 + 5 ≤ v13) (v14 w14 : Nat) (h14 : v14 + 3 ≤ w14 ∨ w14 + 5 ≤ v14) (v15 w15 : Nat) (h15 : v15 + 3 ≤ w15 ∨ w15 + 5 ≤ v15) (v16 w16 : Nat) (h16 : v16 + 3 ≤ w16 ∨ w16 + 5 ≤ v16) (v17 w17 : Nat) (h17 : v17 + 3 ≤ w17 ∨ w17 + 5 ≤ v17) (v18 w18 : Nat) (h18 : v18 + 3 ≤ w18 ∨ w18 + 5 ≤ v18) (v19 w19 : Nat) (h19 : v19 + 3 ≤ w19 ∨ w19 + 5 ≤ v19) (v20 w20 : Nat) (h20 : v20 + 3 ≤ w20 ∨ w20 + 5 ≤ v20) (v21 w21 : Nat) (h21 : v21 + 3 ≤ w21 ∨ w21 + 5 ≤ v21) (v22 w22 : Nat) (h22 : v22 + 3 ≤ w22 ∨ w22 + 5 ≤ v22) (v23 w23 : Nat) (h23 : v23 + 3 ≤ w23 ∨ w23 + 5 ≤ v23) (v24 w24 : Nat) (h24 : v24 + 3 ≤ w24 ∨ w24 + 5 ≤ v24) (v25 w25 : Nat) (h25 : v25 + 3 ≤ w25 ∨ w25 + 5 ≤ v25) (v26 w26 : Nat) (h26 : v26 + 3 ≤ w26 ∨ w26 + 5 ≤ v26) (v27 w27 : Nat) (h27 : v27 + 3 ≤ w27 ∨ w27 + 5 ≤ v27) (v28 w28 : Nat) (h28 : v28 + 3 ≤ w28 ∨ w28 + 5 ≤ v28) (v29 w29 : Nat) (h29 : v29 + 3 ≤ w29 ∨ w29 + 5 ≤ v29) :
    MemFrame m0 m [(q, q + 100)] := by
  janus_frame

/-- A frame that is not contained is still rejected. -/
example (m0 m1 m : Memory) (q p : Nat) (hf : MemFrame m1 m [(p, p + 8)])
    (hm : MemFrame m0 m1 [(q, q + 100)]) : True := by
  fail_if_success
    have : MemFrame m0 m [(q, q + 100)] := by janus_frame
  trivial

end JanusTests.FrameClear
