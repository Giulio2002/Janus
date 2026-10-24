/* Termination measures for the model's recursive functions (docs/X86FORMAL.md). Sail's Lean
 * backend prints each as `termination_by (m).toNat`; the decreasing proofs are discharged by
 * the `decreasing_trivial` extension in JanusX86Extras.lean (simp + omega, no sorry). */
termination_measure logcount_int(x) = if x < 0 then 0 - 2 * x else 2 * x
termination_measure logand_int(i, j) = abs_int(i)
termination_measure get_prefixes(_, _, _, _, cnt) = cnt + 0
