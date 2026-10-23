import Lean

/-!
# Simp sets of the amd64 proof automation

* `janus64_exec`: what `janus64_step` uses to evaluate one instruction on a symbolic state.
* `janus64_post`: clean-up of the goals left after symbolic execution.
* `janus64_arith_norm`: rewrites `janus64_arith` applies before `omega`.

Registered in their own module because a simp attribute cannot be used in the module that
declares it.
-/

register_simp_attr janus64_exec
register_simp_attr janus64_post

/-- Normalisation applied by `janus64_arith` before `omega` (carries as `Nat` divisions). -/
register_simp_attr janus64_arith_norm
