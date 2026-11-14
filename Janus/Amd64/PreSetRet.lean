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

syntax "janus64_pre_setRet" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| janus64_pre_setRet) => `(tactic| janus64_pre_setRet [])
  | `(tactic| janus64_pre_setRet [$ds,*]) => `(tactic|
      (intro s ret hret hp
       have hu := hret.user
       try simp only [Janus.Amd64.GoABI.regSP, Janus.Amd64.GoABI.StackWritable, Janus.Amd64.GoABI.SPAligned,
         Janus.Amd64.GoABI.Buffer, Janus.Amd64.GoABI.Disjoint, Janus.Amd64.GoABI.valueAt,
         Janus.Amd64.GoABI.StackWords, Janus.Amd64.GoABI.stackWord, Janus.Amd64.GoABI.stackArgOffset,
         Janus.Amd64.GoABI.StackGuardOK, Janus.Amd64.GoABI.stackguard0, Janus.Amd64.GoABI.stackguard0Offset,
         Janus.Amd64.GoABI.ClosureCtx, Janus.Spec.Disjoint, Janus.Apart, Janus.outside_nil,
         Janus.outside_cons, $ds,*] at hp ⊢
       all_goals
        (have hp0 := hp
         janus_split_hyps keep hp0
         janus_have_rsp8 hacc8 : s.mem.accessible (s.regs 4).toNat 8 true = true
         try simp (disch := first | omega | assumption)
           only [Janus.Amd64.GoABI.setRet_regs,
           Janus.Amd64.GoABI.setRet_rip, Janus.Amd64.GoABI.setRet_flags,
           Janus.Amd64.GoABI.setRet_xmm, Janus.Amd64.GoABI.setRet_ymmHi,
           Janus.Amd64.GoABI.setRet_zmmHi, Janus.Amd64.GoABI.setRet_kreg,
           Janus.Amd64.GoABI.setRet_fsBase, Janus.Amd64.GoABI.setRet_df,
           Janus.Amd64.GoABI.setRet_mxcsr, Janus.Amd64.GoABI.setRet_x87,
           Janus.Amd64.GoABI.setRet_fpucw, Janus.Amd64.GoABI.setRet_mem_regions,
           Janus.Amd64.GoABI.setRet_accessible, Janus.Amd64.GoABI.readLE_setRet_of_disjoint,
           Janus.Amd64.GoABI.bytes_setRet_of_outside, Janus.Amd64.GoABI.dataLoaded_setRet_iff] at ⊢
         try simp (disch := omega) only [Janus.Amd64.GoABI.readLE_setRet_sp] at ⊢
         all_goals first | with_reducible exact hp0 | (and_intros <;> first | with_reducible assumption | omega))))

/-- `janus64_ensures_old [defs]`: the amd64 twin of `janus_ensures_old`. -/
syntax "janus64_ensures_old" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| janus64_ensures_old) => `(tactic| janus64_ensures_old [])
  | `(tactic| janus64_ensures_old [$ds,*]) => `(tactic|
      first
        | refine Janus.Amd64.GoABI.Ensures.of_old (by janus64_pre_setRet [$ds,*]) ?_
        | refine Janus.Amd64.GoABI.EnsuresWithin.of_old (by janus64_pre_setRet [$ds,*]) ?_
        | refine Janus.Amd64.GoABI.EnsuresGoX.of_old (by janus64_pre_setRet [$ds,*]) ?_
        | refine Janus.Amd64.GoABI.EnsuresGo.of_old (by janus64_pre_setRet [$ds,*]) ?_
        | refine Janus.Amd64.GoABI.RunsAtLeastOnCall.of_old (by janus64_pre_setRet [$ds,*]) ?_)

end Janus.Amd64.Tactic
