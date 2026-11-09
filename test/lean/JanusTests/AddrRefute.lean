import Janus

/-! # Refutation first (S4)

* `janus.addr.refute` (default on): `addrDisch` also proves the NEGATION of an address side condition from the
  offsets (`n ≤ x + c` for a literal `n ≤ c`, plus the lower-bound normalisation of a bounded atom), so that
  `2^64 - 48 + sp < 2^64` given `4248 ≤ sp` fails at once instead of after a failed `omega` through every stage.
  Provable goals are unaffected (the check runs only when the goal itself is not decided).
  Measured: DivModB `janus64_run` (closers sorried) 5m09-5m16 -> 4m31-4m38; the 98 failing `mod64_of_lt` discharges of the
  run become instant. -/

namespace JanusTests.AddrRefute

open Janus Janus.Tactic

/- The wrap check of `sp - 48`: false given `4248 ≤ sp`; fails (and quickly: a tiny heartbeat budget). -/
set_option maxHeartbeats 20000 in
example (sp : Nat) (hlow : 4248 ≤ sp) (hn : sp + 40 ≤ 2 ^ 48) : True := by
  fail_if_success
    have : 18446744073709551568 + sp < 18446744073709551616 := by janus_omega
  trivial

/-- Without the refutation the wrap check of a true wrap goal is still proved (the literal is below the offset). -/
example (sp : Nat) (hlow : 4248 ≤ sp) : 18446744073709551616 ≤ 18446744073709551568 + sp := by
  janus_omega

example (sp : Nat) (hlow : 48 ≤ sp) : sp - 48 + 8 ≤ sp := by
  janus_omega

/- Switching it off restores the earlier behaviour: the goal is still not provable. -/
set_option janus.addr.refute false in
example (sp : Nat) (hlow : 4248 ≤ sp) : True := by
  fail_if_success
    have : 18446744073709551568 + sp < 18446744073709551616 := by janus_omega
  trivial

/-- A false same-base goal is refuted as before. -/
example (x : Nat) : True := by
  fail_if_success
    have : x + 8 ≤ x + 4 := by janus_omega
  trivial

end JanusTests.AddrRefute
