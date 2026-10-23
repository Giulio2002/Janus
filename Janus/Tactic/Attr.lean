import Lean

/-!
# Simp sets of the Janus proof automation

* `janus_exec`: everything `janus_step` uses to evaluate one instruction on a symbolic state:
  the per-constructor `exec` equations, the executor helpers, register-file and memory
  read-over-write lemmas, address normalisation and flag/condition lemmas.
* `janus_post`: clean-up used on the goals that remain after symbolic execution (final
  states, postconditions, branch conditions).

They are registered here, in their own module, because a simp attribute cannot be used in the
module that declares it.
-/

register_simp_attr janus_exec
register_simp_attr janus_post

/-- Arithmetic normalisation of side goals inside `janus_disch` (addresses, offsets). -/
register_simp_attr janus_disch_norm

/-- Normalisation applied by `janus_arith` before `omega` (carry re-creation patterns). -/
register_simp_attr janus_arith_norm

/-- Lemmas that reduce `m'.accessible …` for a derived memory `m'` to the caller's memory (used
by the accessibility discharger). Tag frame lemmas of user-defined memory updates with it. -/
register_simp_attr janus_acc
