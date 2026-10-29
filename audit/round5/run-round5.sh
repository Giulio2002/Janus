#!/usr/bin/env bash
# Round-5 regression rows (docs/AUDIT-ROUND5.md). Exits 1 if a blocked attack prints Verified, a
# control stops verifying or prints something else, or a model row disagrees with hardware.
# Writes only under audit/round5/work/, audit/round5/bin/ and audit/round5/model/{bin,cases,out-*}.
# Usage: audit/round5/run-round5.sh [-j N]     (SKIP_MODEL=1 skips the oracle rows; -j: blocks at
#        once, default the core count capped by memory, scripts/lib/parallel.sh)
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
export PATH=/usr/local/go/bin:$PATH
# shellcheck source=../../scripts/lib/parallel.sh
. "$root/scripts/lib/parallel.sh"
# shellcheck source=../../scripts/lib/memguard.sh
. "$root/scripts/lib/memguard.sh"
memguard_self "$@"
par_init "$@"
J="$root/audit/round5/bin/janus"; mkdir -p "$(dirname "$J")"
# audit/run-rounds.sh builds janus and the framework once for every lane (JANUS_AUDIT_BIN,
# JANUS_AUDIT_PREBUILT=1).
if [ -n "${JANUS_AUDIT_BIN:-}" ]; then J="$JANUS_AUDIT_BIN"; else go build -o "$J" ./cmd/janus || exit 1; fi
[ "${JANUS_AUDIT_PREBUILT:-}" = 1 ] || memguard_lake build Janus Janus.Tools.Audit >/dev/null || { echo "lake build failed"; exit 1; }
[ -f artifacts/examples-arm64 ] || scripts/build-examples.sh >/dev/null
W=audit/round5/work; rm -rf "$W"; mkdir -p $W
"$J" extract artifacts/examples-arm64 example.com/basic.Add $W/Add >/dev/null || exit 1
broken=()
A=audit/round5/attacks

# row NAME EXPECT [PATTERN] -- verify output in $out. EXPECT is "blocked" (must not print
# Verified) or "Verified" (must print Verified and, if given, contain PATTERN).
row() {
  local name=$1 expect=$2 pat=${3:-} verdict status=""
  verdict="$(grep -m1 -E '^(Verified|Invalid|Error)' <<<"$out" | cut -c1-150)"
  [ -n "$verdict" ] || verdict="(no verdict) $(head -1 <<<"$out" | cut -c1-120)"
  case $expect in
    blocked) case $verdict in Verified*) status=BROKEN ;; esac ;;
    Verified) case $verdict in Verified*) [ -n "$pat" ] && ! grep -qF -- "$pat" <<<"$out" && status=BROKEN ;; *) status=BROKEN ;; esac ;;
  esac
  printf '  %-36s %-8s %s%s\n' "$name" "$expect" "$verdict" "${status:+   <-- BROKEN}"
  [ -n "$status" ] && broken+=("$name")
  return 0
}
v() { out="$("$J" verify --janus-root "$root" --proof "$A/$1.lean" $W/Add 2>&1)"; }

# vrow ATTACK EXPECT [PATTERN]: verify one attack and print its row (one parallel block each).
vrow() { v "$1"; row "$@"; }
e5_row() {
  local a=$1
  v $a; row $a blocked
  case $out in *"binds the instance"*|*"inline instance"*) ;; *) echo "    >>> $a: not rejected for the bound instance"; broken+=("$a-reason") ;; esac
}
r2_row() {
  out="$("$J" verify --janus-root "$root" --proof audit/round3/attacks/R2_inst_binder.lean $W/Add 2>&1)"
  row R2_theorem_level_binder Verified '[inst : HMul (BitVec 64) (BitVec 64) (BitVec 64)]'
}

par_run 'echo "== E1: Decidable instances in decide/if (statement, hypotheses, def bodies)"'
for a in E1a_decide_custom_def E1b_decide_local_instance_hyp E1c_if_custom_hyp E1d_decide_classical \
         E1e_decide_in_def_body E1g_decide_projected; do par_run 'vrow "$a" blocked'; done
par_run "vrow E1f_decide_honest Verified 'Decidable.decide (x = x) = Bool.true'"

par_run 'echo "== E2: reducible/abbrev instances, let/fun/beta, inferInstanceAs, attribute/local/scoped/priority"'
for a in E2a_reducible_inst E2b_abbrev_inst E2c_let_inst E2d_beta_instbinder E2e_inferInstanceAs \
         E2f_attribute_instance_later E2g_local_instance E2h_priority_override E2i_scoped_instance \
         E2j_fun_bound_inst E2k_haveI; do par_run 'vrow "$a" blocked'; done

par_run 'echo "== E3: proof-local structures/inductives, Janus-like field names"'
for a in E3a_local_structure_regs E3b_extends_state E3c_local_inductive_in_def; do par_run 'vrow "$a" blocked'; done
par_run "vrow E3d_field_named_def Verified 'Janus.Arm64.State.result : Janus.Arm64.State → BitVec 64 := fun s => s.regs 0'"

par_run 'echo "== E4: proof-local notation, macro_rules, unexpanders (printed in the clean environment)"'
par_run 'vrow E4a_macro_rules_plus blocked'
par_run "vrow E4b_macro_rules_star Verified \"fun x_1 s' => s'.regs 0 = x + y\""
par_run "vrow E4c_local_infix_shadow Verified \"fun x_1 s' => s'.regs 0 = x + y\""
par_run "vrow E4d_global_notation_unexpander Verified \"s'.regs 0 = x + y ∧ s'.regs 0 = x.add y\""

par_run 'echo "== E5: instances bound inside the statement or a disclosed def (fixed this round)"'
for a in E5a_exists_instbinder_def E5b_exists_instbinder_stmt E5c_exists_default_classbinder \
         E5d_hyp_forall_instbinder E5e_unapplied_inst_param E5f_unapplied_via_alias; do
  par_run 'e5_row "$a"'
done
par_run r2_row

e6_block() {
echo "== E6: D4 residual (match auxiliaries, well-founded recursion, universe polymorphism)"
type tmark >/dev/null 2>&1 && tmark "== E6: D4 residual (match auxiliaries, well-founde"
v E6a_match_wf_disclosure; row E6a_match_wf_disclosure Verified \
  'Proof.sel.match_1 : (motive : Nat → Sort u_1) → (n : Nat) → (Unit → motive (0 : Nat)) → ((n : Nat) → motive n.succ) → motive n := fun (motive : Nat → Sort u_1) (n : Nat) (h_1 : Unit → motive (0 : Nat)) (h_2 : (n : Nat) → motive n.succ) => Nat.casesOn n (h_1 ()) fun (n : Nat) => h_2 n  [not round-tripped: read with care]'
grep -qF 'Proof.countdown._unary._proof_1 : ∀ (n : Nat), ¬n = 0 → InvImage (fun x1 x2 => x1 < x2) (fun x => x) (n - 1) n := <proof>' <<<"$out" ||
  { echo "    >>> E6a: the auxiliary theorem is not disclosed as <proof>"; broken+=(E6a-proof); }
}
# The dependency rows share one fixture: one block.
dep_block() {
echo "== E1h-j/E3e: a pinned git dependency with a custom Decidable instance and a 'regs' structure"
type tmark >/dev/null 2>&1 && tmark "== E1h-j/E3e: a pinned git dependency with a custo"
dep="$(audit/round5/dep/setup.sh "$root/$W/dep" "$root")" || { echo "  dependency fixture failed"; broken+=(dep-setup); }
d() { out="$("$J" verify $W/Add --janus-root "$root" --proof "$dep/R5Proofs/Proofs.lean" --proof-root "$dep" --theorem "R5Proofs.$1" 2>&1)"; }
d decInst;  row E1h_dep_instance_in_decide blocked
d decDef;   row E1i_dep_classvalued_def blocked
d decBody;  row E1j_dep_def_body_uses_inst Verified 'Dependency constants in the statement: DecLib.isZero (def, DecLib)'
d viewRegs; row E3e_dep_structure_regs Verified 'DecLib.View.regs (def, DecLib)'
}
e5_gotest_block() {
echo "== E5 unit row (go test)"
type tmark >/dev/null 2>&1 && tmark "== E5 unit row (go test)"
(cd cmd/janus && memguard_run -n go-test -- go test -timeout 30m -run 'TestBoundInstanceRejected' . >/dev/null 2>&1) || { echo "  >>> TestBoundInstanceRejected failed"; broken+=(E5-gotest); }
}
model_block() {
if [ -z "${SKIP_MODEL:-}" ]; then
  echo "== item 6: model-level targeted oracle rows (audit/round5/model/run-model.sh)"
  audit/round5/model/run-model.sh > $W/model.log 2>&1 || { tail -20 $W/model.log; broken+=(model); }
  grep -E '^(  ok|[0-9]+ cases|\*\*0 MISMATCH|All round-5)' $W/model.log | sed 's/^/  /'
fi
}
par_run e6_block
par_run dep_block
par_run e5_gotest_block
par_run model_block
par_wait

if [ ${#broken[@]} -gt 0 ]; then echo; echo "BROKEN: ${broken[*]}"; exit 1; fi
echo; echo "All round-5 rows as expected."
