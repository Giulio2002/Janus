import Janus

/-! # Facts inside a conjunction hypothesis reach the `Outside` dischargers (regression for CALLS-WB-WB)

After a live call the postcondition of a second write barrier states, about its buffer `buf`, one conjunction
`(ApartAll buf n L ∧ Apart buf n obj k) ∧ Apart buf n obj2 k2` (the live set is `L ++ [obj] ++ [obj2]`). The
side condition `Outside a 8 (L ++ [obj] ++ [obj2])` of the next barrier's precondition (the `view` lemmas of
`janus_live`) needs each piece, and the dischargers looked for `ApartAll`/`Apart` only among the top-level
hypotheses. `Common.exposeConj` now adds the components of such conjunctions to the side goal. -/

namespace JanusTests.ConjApartAll

open Janus Janus.Contracts Janus.Tactic

set_option linter.unusedVariables false

example (L : List (Nat × Nat)) (buf q k w : Nat)
    (h : (ApartAll buf 16 L ∧ Apart buf 16 q k) ∧ Apart buf 16 w 48) :
    Outside buf 8 (L ++ [(q, q + k)] ++ [(w, w + 48)]) := by
  janus64_disch

example (L : List (Nat × Nat)) (buf q k w : Nat)
    (h : (ApartAll buf 16 L ∧ Apart buf 16 q k) ∧ Apart buf 16 w 48) :
    Outside (buf + 8) 8 (L ++ [(q, q + k)] ++ [(w, w + 48)]) := by
  janus64_disch

/-- A piece that is not in the conjunction is still refused. -/
example (L : List (Nat × Nat)) (buf q k w : Nat)
    (h : ApartAll buf 16 L ∧ Apart buf 16 q k) : True := by
  fail_if_success
    (have _ : Outside buf 8 (L ++ [(q, q + k)] ++ [(w, w + 48)]) := by janus64_disch)
  trivial

end JanusTests.ConjApartAll
