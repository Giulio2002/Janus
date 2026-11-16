import Lean
import Janus.Amd64.GoABI
import Janus.Tactic.PreSetRet
import Janus.Tactic.Common

/-!
# `janus64_pre_setRet` (amd64): migrating a precondition to the v0.4.0 `Ensures`

The amd64 twin of `janus_pre_setRet` (see `Janus.Tactic.PreSetRet`). Since v0.4.0 the precondition
of `Ensures` & co. is evaluated on the call state **before** the return address is written at
`[RSP]` (`State.setRet`); an old-shaped proof runs on `s.setRet ret`, so migrating it as

```
Ensures.of_old (by janus64_pre_setRet) (by intro ret hret s hs hpre; …  /- the old proof -/)
```

needs `pre s → pre (s.setRet ret)` (`hinv`). `setRet` changes only the 8 bytes `[RSP, RSP + 8)`, so
`janus64_pre_setRet`

* introduces `s ret hret hp` and unfolds the standard predicates (`StackWritable`, `SPAligned`,
  `Buffer`, `Disjoint`, `Outside`, `Apart`, `StackGuardOK`, …) and the definitions listed in
  `[…]` in `hp` and in the goal;
* splits `hp` into its conjuncts (so `omega` sees every arithmetic fact of the precondition);
* rewrites `s.setRet ret` away: registers, flags, regions, `accessible` unconditionally; a memory
  read `readLE a n` / `bytes a` when `[a, a + n)` is disjoint from `[RSP, RSP + 8)`, the side goal
  being discharged by `omega` from `hp` and `RetAddr`'s `ret < 2^47`; a read of the return
  slot itself (`readLE RSP 8`) becomes `ret`;
* closes the goal from `hp` (assumption / `omega`).

**Discharged automatically:** stack-argument reads at `RSP + k` with `k ≥ 8`; reads below `RSP`
(`[a, a + n) ⊆ [0, RSP]`); a read at a pointer whose range is apart from `[RSP, RSP+8)` by an
arithmetic fact of the precondition (an `Apart`/`Disjoint`/`Outside` conjunct, or `Outside` over a
window list that contains `[RSP, RSP + 8)`); `[RSP] < 2^47`-style bounds on the return slot (from
`RetAddr`). **Needs an explicit extra conjunct:** a read at a pointer that the precondition
only places inside a buffer (`Buffer`, `Ptr`, `accessible`) or outside the callee's *writable*
windows (`calleeStack64` leaves the return slot out): state `Apart ptr n RSP 8` for it. A precondition
that pins the return slot or `X30` (`[RSP] = 0`, `X30 < 2^20`) is not invariant under `setRet`, and
the tactic fails on it, by design.
-/

namespace Janus.Amd64.Tactic

open Lean Elab Tactic

/-- `janus_outside_slot`: prove `Outside a n rs` from a hypothesis `Outside b k rs` of the context whose range contains it
(`Outside.of_sub`, the two bounds closed by `omega`): the return slot `[RSP, RSP + 8)` is outside the runtime-owned ranges
when the precondition says its stack window is. -/
elab "janus_outside_slot" : tactic => do
  let g ← getMainGoal
  let hyps ← g.withContext do
    let mut acc : Array Expr := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``Janus.Outside 3 then acc := acc.push d.toExpr
      else if ty.isAppOfArity `Janus.Contracts.LiveSep 2 then acc := acc.push d.toExpr
    return acc
  for hy in hyps do
    let st ← saveState
    try
      let hs ← g.withContext (Term.exprToSyntax hy)
      let lso := mkIdent `Janus.Contracts.SetRetFramesAmd64.liveSep_outside
      -- `LiveSep [win, …] rt` (a window of the live set that covers the return slot) separates the slot from `rt` too
      Tactic.withoutRecover <| evalTactic (← `(tactic| first
        | exact Janus.Outside.of_sub $hs (by omega) (by omega)
        | exact $lso:ident $hs
            (by first | exact List.mem_singleton_self _ | exact List.mem_cons_self .. | exact List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by omega) (by omega)))
      return
    catch _ => st.restore
  throwError "janus_outside_slot: no hypothesis `Outside` contains the goal"

syntax (name := janus64PreSetRetCore) "janus64_pre_setRet_core " ident ident ident ident ident " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules (kind := janus64PreSetRetCore)
  | `(tactic| janus64_pre_setRet_core $s $ret $hs $hret $hp [$ds,*]) => do
    -- lemmas of modules that are imported after this one: identifiers built with `mkIdent` resolve where the tactic is used
    let v1 := mkIdent `Janus.Contracts.view_setRet
    let v2 := mkIdent `Janus.Contracts.StackAmd64.rtView_setRet
    let c1 := mkIdent `Janus.Amd64.CABI.CStack
    let l1 := mkIdent `Janus.Contracts.LibcAmd64.tlsBlock_setRet_iff
    let l2 := mkIdent `Janus.Contracts.LibcAmd64.cstr_setRet_iff
    let m1 := mkIdent `Janus.Contracts.MapAmd64.laws_env_setRet
    let m2 := mkIdent `Janus.Contracts.MapAmd64.laws_rep_setRet
    let m3 := mkIdent `Janus.Contracts.MapAmd64.laws_isMap_setRet
    let m4 := mkIdent `Janus.Contracts.MapAmd64.laws_iter_setRet
    let f0 := mkIdent `Janus.Contracts.SetRetFramesAmd64.mem_env_setRet
    let f1 := mkIdent `Janus.Contracts.SetRetFramesAmd64.iface_env_setRet
    let f2 := mkIdent `Janus.Contracts.SetRetFramesAmd64.hash_env_setRet
    let f3 := mkIdent `Janus.Contracts.SetRetFramesAmd64.rt_env_setRet
    let f4 := mkIdent `Janus.Contracts.SetRetFramesAmd64.panic_env_setRet
    let f5 := mkIdent `Janus.Contracts.SetRetFramesAmd64.panic_panics_setRet
    let f6 := mkIdent `Janus.Contracts.SetRetFramesAmd64.panic_defers_setRet
    let f7 := mkIdent `Janus.Contracts.SetRetFramesAmd64.panic_saved_setRet
    let f8 := mkIdent `Janus.Contracts.SetRetFramesAmd64.panic_rp_setRet
    let f9 := mkIdent `Janus.Contracts.SetRetFramesAmd64.panic_room_setRet
    let f10 := mkIdent `Janus.Contracts.SetRetFramesAmd64.panic_calm_setRet
    let mf := mkIdent `Janus.Contracts.SetRetFramesAmd64.memFrame_setRet_iff
    -- the definitions the user lists are unfolded one by one: an ambiguous or unknown name fails only its own `simp`
    -- all at once (definitions inside each other unfold to a fixpoint), then one by one twice (what is left when a name is ambiguous)
    let mut us ← `(tactic| try simp only [$ds,*] at $hp:ident ⊢)
    for _ in [0:2] do
      for d in ds.getElems do
        us ← `(tactic| ($us; try simp only [$d] at $hp:ident ⊢))
    -- after the split the conditional setRet laws are tried WITHOUT the user's definitions first (what every framework example
    -- needs: unfolding a user definition here can leave a conjunct in a shape `hp0` no longer closes) and, only if that does
    -- not close the goal, again WITH them (a consumer's conditional setRet law given in the list, e.g. one with an Apart side
    -- condition, fires only after the hypotheses are split)
    let rest ← `(tactic|
       (try simp (disch := omega) only [Janus.Amd64.GoABI.readLE_setRet_sp] at ⊢
        try simp (disch := first | assumption | janus_outside_slot) only [$v1:ident] at ⊢
        try simp (disch := first | assumption | janus_outside_slot) only [$v2:ident] at ⊢
        try simp (disch := first | assumption | janus_disj_omega | omega) only [$l1:ident, $l2:ident] at ⊢
        try simp (disch := first | assumption | janus_outside_slot) only [$m1:ident, $m2:ident, $m3:ident, $m4:ident] at ⊢
        try simp (disch := omega) only [$mf:ident] at ⊢
        try simp (disch := first | assumption | janus_outside_slot) only [$f0:ident, $f1:ident, $f2:ident, $f3:ident, $f4:ident, $f5:ident, $f6:ident, $f7:ident, $f8:ident, $f9:ident, $f10:ident] at ⊢))
    let closeQuiet ← `(tactic|
       (all_goals first
         | with_reducible exact Janus.Tactic.Hide.elim hp0
         | (repeat' (first | with_reducible assumption | with_reducible refine And.intro ?_ ?_)
            all_goals omega)))
    `(tactic|
      (have hu := ($hret).user
       $us
       try simp only [Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.StackWritable, Janus.Amd64.GoABI.SPAligned,
         Janus.Amd64.GoABI.Buffer, Janus.Amd64.GoABI.Disjoint, Janus.Amd64.GoABI.valueAt,
         Janus.Amd64.GoABI.StackWords, Janus.Amd64.GoABI.stackWord, Janus.Amd64.GoABI.stackArgOffset,
         Janus.Amd64.GoABI.stackguard0, Janus.Amd64.GoABI.stackguard0Offset,
         Janus.Amd64.GoABI.ClosureCtx, Janus.Spec.Disjoint, Janus.Apart, Janus.outside_nil,
         Janus.outside_cons] at $hp:ident ⊢
       try simp only [$c1:ident] at $hp:ident ⊢
       all_goals
        (have hp0 : Janus.Tactic.Hide _ := $hp
         janus_split_hyps keep hp0
         janus_have_rsp8 hacc8 : ($s).mem.accessible (($s).regs 4).toNat 8 true = true
         first
          | (try simp (disch := first | assumption | janus_disj_omega | omega)
               only [Janus.Amd64.GoABI.setRet_regs,
                 Janus.Amd64.GoABI.setRet_rip, Janus.Amd64.GoABI.setRet_flags,
                 Janus.Amd64.GoABI.setRet_xmm, Janus.Amd64.GoABI.setRet_ymmHi,
                 Janus.Amd64.GoABI.setRet_zmmHi, Janus.Amd64.GoABI.setRet_kreg,
                 Janus.Amd64.GoABI.setRet_fsBase, Janus.Amd64.GoABI.setRet_df,
                 Janus.Amd64.GoABI.setRet_mxcsr, Janus.Amd64.GoABI.setRet_x87,
                 Janus.Amd64.GoABI.setRet_fpucw, Janus.Amd64.GoABI.setRet_mem_regions,
                 Janus.Amd64.GoABI.setRet_accessible, Janus.Amd64.GoABI.readLE_setRet_of_disjoint,
                 Janus.Amd64.GoABI.bytes_setRet_of_outside, Janus.Amd64.GoABI.dataLoaded_setRet_iff,
                 Janus.Amd64.GoABI.stackGuardOK_setRet, Janus.Amd64.GoABI.tlsG_setRet_iff,
                 Janus.Amd64.GoABI.buffer_setRet, Janus.Amd64.GoABI.ptr_setRet] at ⊢
             $rest
             $closeQuiet)
          | (try simp (disch := first | assumption | janus_disj_omega | omega)
               only [Janus.Amd64.GoABI.setRet_regs,
                 Janus.Amd64.GoABI.setRet_rip, Janus.Amd64.GoABI.setRet_flags,
                 Janus.Amd64.GoABI.setRet_xmm, Janus.Amd64.GoABI.setRet_ymmHi,
                 Janus.Amd64.GoABI.setRet_zmmHi, Janus.Amd64.GoABI.setRet_kreg,
                 Janus.Amd64.GoABI.setRet_fsBase, Janus.Amd64.GoABI.setRet_df,
                 Janus.Amd64.GoABI.setRet_mxcsr, Janus.Amd64.GoABI.setRet_x87,
                 Janus.Amd64.GoABI.setRet_fpucw, Janus.Amd64.GoABI.setRet_mem_regions,
                 Janus.Amd64.GoABI.setRet_accessible, Janus.Amd64.GoABI.readLE_setRet_of_disjoint,
                 Janus.Amd64.GoABI.bytes_setRet_of_outside, Janus.Amd64.GoABI.dataLoaded_setRet_iff,
                 Janus.Amd64.GoABI.stackGuardOK_setRet, Janus.Amd64.GoABI.tlsG_setRet_iff,
                 Janus.Amd64.GoABI.buffer_setRet, Janus.Amd64.GoABI.ptr_setRet, $ds,*] at ⊢
             $rest
             all_goals first
               | with_reducible exact Janus.Tactic.Hide.elim hp0
               | (repeat' (first | with_reducible assumption | with_reducible refine And.intro ?_ ?_)
                  all_goals first | omega | (trace_state; fail "janus_pre_setRet: this conjunct of the precondition is not invariant under setRet (see the goal above; pass the predicate definitions to the tactic, e.g. `janus64_ensures_old [Pre, CallEnv]`, and make a pointer read apart from the return slot)"))))))

syntax (name := janus64PreSetRet) "janus64_pre_setRet" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules (kind := janus64PreSetRet)
  | `(tactic| janus64_pre_setRet) => `(tactic| janus64_pre_setRet [])
  | `(tactic| janus64_pre_setRet [$ds,*]) => `(tactic|
      (intro s ret hs hret hp
       janus64_pre_setRet_core s ret hs hret hp [$ds,*]))

/-- `janus64_pre_setRet_k`: as `janus64_pre_setRet` for a precondition on a state and a kernel state
(`EnsuresK`). -/
syntax (name := janus64PreSetRetK) "janus64_pre_setRet_k" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules (kind := janus64PreSetRetK)
  | `(tactic| janus64_pre_setRet_k) => `(tactic| janus64_pre_setRet_k [])
  | `(tactic| janus64_pre_setRet_k [$ds,*]) => `(tactic|
      (intro s k ret hs hret hp
       janus64_pre_setRet_core s ret hs hret hp [$ds,*]))

/-- `janus64_pre_setRet_c`: as `janus64_pre_setRet` for a precondition with a `caller` hypothesis (`EnsuresGrow`: the goal is
`∀ s ret, RetAddr p ret → pre s → caller (s.setRet ret) → pre (s.setRet ret)`; `hc` is available to the proof). -/
syntax (name := janus64PreSetRetC) "janus64_pre_setRet_c" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules (kind := janus64PreSetRetC)
  | `(tactic| janus64_pre_setRet_c) => `(tactic| janus64_pre_setRet_c [])
  | `(tactic| janus64_pre_setRet_c [$ds,*]) => `(tactic|
      (intro s ret hs hret hp hc
       janus64_pre_setRet_core s ret hs hret hp [$ds,*]))

/-- `janus64_ensures_old [defs]`: the amd64 twin of `janus_ensures_old`. -/
syntax (name := janus64EnsuresOld) "janus64_ensures_old" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

def ensuresOldForms64 : List (Name × Nat) :=
  [(`Janus.Amd64.GoABI.Ensures.of_old, 0), (`Janus.Amd64.GoABI.EnsuresWithin.of_old, 0),
   (`Janus.Amd64.GoABI.EnsuresGoX.of_old, 0), (`Janus.Amd64.GoABI.EnsuresGo.of_old, 0),
   (`Janus.Amd64.GoABI.RunsAtLeastOnCall.of_old, 0), (`Janus.Amd64.GoABI0.Ensures0.of_old, 0),
   (`Janus.Amd64.CABI.CEnsures.of_old, 0), (`Janus.Amd64.CABI.CEnsuresA.of_old, 0),
   (`Janus.Amd64.FFI.EnsuresC.of_old, 0), (`Janus.Amd64.FFI.CEnsuresC.of_old, 0),
   (`Janus.Amd64.Kernel.EnsuresK.of_old, 1), (`Janus.Contracts.StackAmd64.EnsuresGrow64.of_old, 2)]

macro_rules (kind := janus64EnsuresOld)
  | `(tactic| janus64_ensures_old) => `(tactic| janus64_ensures_old [])
  | `(tactic| janus64_ensures_old [$ds,*]) => do
    let mut acc ← `(Lean.Parser.Tactic.tacticSeq| fail "janus64_ensures_old: the goal is not a main-theorem form with an `of_old` bridge")
    let mut heads : Array (Ident × TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[]
    for (n, kind) in ensuresOldForms64.reverse do
      let alt ← if kind == 1 then
          `(Lean.Parser.Tactic.tacticSeq| refine $(mkIdent n) (by janus64_pre_setRet_k [$ds,*]) ?_)
        else if kind == 2 then
          `(Lean.Parser.Tactic.tacticSeq| refine $(mkIdent n) (by janus64_pre_setRet_c [$ds,*]) ?_)
        else `(Lean.Parser.Tactic.tacticSeq| refine $(mkIdent n) (by janus64_pre_setRet [$ds,*]) ?_)
      heads := heads.push (mkIdent n.getPrefix, alt)
      acc ← `(Lean.Parser.Tactic.tacticSeq| first | $alt | $acc)
    let (hn, ha) := (heads.map (·.1), heads.map (·.2))
    `(tactic| janus_head_first $[$hn:ident => ($ha)]* otherwise ($acc))

end Janus.Amd64.Tactic

namespace Janus.Amd64.GoABI

open Janus Janus.Amd64 Janus.Amd64.Tactic

/-- Weaken the precondition and the postcondition, with the pre-v0.4.0 `hpost` (about the state that already holds the
return address in `[RSP]`: `pre' s → post s s' → post' s s'`). The invariance of `pre'` under `setRet` is the new
obligation, proved by default with `janus64_pre_setRet`. (`Ensures.mono_ret` states `hpost` at `s.setRet ret`.) -/
theorem Ensures.mono {p : Program} {entry : Nat} {args : List W64} {pre pre' : State → Prop}
    {post post' : State → State → Prop}
    (h : Ensures p entry args pre post) (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s s', pre' s → post s s' → post' s s')
    (hinv : Ensures.SetRetInv p entry args pre' := by janus64_pre_setRet) :
    Ensures p entry args pre' post' :=
  fun s hs hp ret hret => (h s hs (hpre s hp) ret hret).mono fun _ ⟨ha, hq⟩ =>
    ⟨ha, hpost _ _ (hinv s ret hs hret hp) hq⟩

end Janus.Amd64.GoABI
