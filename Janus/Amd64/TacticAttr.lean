import Lean

/-!
# Simp sets of the amd64 proof automation

* `janus64_exec`: what `janus64_step` uses to evaluate one instruction on a symbolic state.
* `janus64_post`: clean-up of the goals left after symbolic execution.

Registered in their own module because a simp attribute cannot be used in the module that
declares it.
-/

register_simp_attr janus64_exec
register_simp_attr janus64_post
