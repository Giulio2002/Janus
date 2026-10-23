import Lean
import Janus.Tactic.Basic
import Janus.Tactic.Data

/-!
# Symbolic execution tactics

* `janus_run [lemmas] (until [pc, ...])? (steps := n)?` steps a goal of the form
  `Reaches p s Q`, `ReachesRet p ret s Q`, `Returns p s post`, `Panics p s` or `GrowsStack p s`
  instruction by instruction until every branch has reached the exit address, a stub, the
  return address (for `ReachesRet`), a `until` address, or the step budget. Branches split
  the goal (the branch condition becomes a hypothesis `hbr`); infeasible branches are closed
  by `omega` on the branch condition.
* `janus_step [lemmas]` performs exactly one step on the main goal.
* `janus_intro hs` turns a `CallSetup` hypothesis into `h_pc : s.pc = …`, `h_lr : s.regs 30 = …`
  and `h_x<i> : s.regs i = argᵢ`.
* `janus_disch` is the side-condition discharger used inside `simp` (closed goals by `decide`,
  `Memory.accessible` from hypotheses, arithmetic by `omega`).

How one step works (`stepGoal`):
1. The pc of the symbolic state is computed (it is a literal in the normal form; otherwise
   `simp` with the hypotheses computes it).
2. The program's data (exit address, segments, stubs) is evaluated once per program and cached;
   the word at `pc` is looked up and decoded by `Janus.Arm64.decode` at tactic run time.
3. The facts "pc is no exit, no stub, holds word `w`, and `w` decodes to `i`" are one Boolean
   `stepOK p pc w i = true`, proved by `Eq.refl true` in an auxiliary lemma checked by the
   kernel only (as `decide +kernel` does), so huge programs are never unfolded by the elaborator.
4. `exec i s` is simplified with the `janus_exec` simp set plus the hypotheses about the
   initial state (all local equations `x.pc = _`, `x.regs i = _`, `x.sp = _`, `x.flags = _`,
   `x.mem = _` are used automatically) and the user's lemmas; the result must be `.ok s'`, a
   branch `if c then … else …`, or the step reports what it could not evaluate.

A call with a symbolic return address is a goal on `Program.withExit p ret` with
`hret : GoABI.RetAddr p ret` in the context: the program facts are still evaluated on the
closed `p`, `pc ≠ ret` comes from `hret` (no code or stub at `ret`, `Reaches.step_withExit`),
facts about `ret` enter the simp set as rewrite rules (`RetAddr.toNat_ofNat`, …), and the
return is recognised when the pc is `BitVec.ofNat 64 ret` (`Reaches.exit_withExit`).
-/

namespace Janus.Tactic

open Lean Meta Elab Tactic
open Janus Janus.Arm64

deriving instance ToExpr for ShiftType
deriving instance ToExpr for ExtendType
deriving instance ToExpr for LogicOp
deriving instance ToExpr for MoveWideOp
deriving instance ToExpr for BitfieldOp
deriving instance ToExpr for Imm9Mode
deriving instance ToExpr for PairMode
deriving instance ToExpr for AtomicOp
deriving instance ToExpr for Instr
deriving instance ToExpr for StubKind

/-- The side-condition discharger (defined below). -/
syntax "janus_disch" : tactic

initialize registerTraceClass `janus
initialize registerTraceClass `janus.disch

/-! ## Program data, evaluated once per program -/

abbrev ProgData := Nat × List (Nat × List Nat) × List (Nat × String × Bool)

unsafe def evalProgDataImpl (p : Expr) : MetaM ProgData := do
  let e := mkApp (mkConst ``progData) p
  let ty ← inferType e
  evalExpr ProgData ty e

@[implemented_by evalProgDataImpl]
opaque evalProgDataCore (p : Expr) : MetaM ProgData

unsafe def evalNatImpl (e : Expr) : MetaM Nat := evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatImpl]
opaque evalNatCore (e : Expr) : MetaM Nat

initialize progCache : IO.Ref (Std.HashMap Expr ProgData) ← IO.mkRef {}

def getProgData (p : Expr) : MetaM ProgData := do
  let p ← instantiateMVars p
  if let some d := (← progCache.get).get? p then return d
  if p.hasFVar || p.hasMVar then
    throwError "janus: the program must be a closed term (e.g. `Extracted.program`), got{indentExpr p}"
  let d ← try evalProgDataCore p catch e =>
    throwError "janus: cannot evaluate the program{indentExpr p}\n{e.toMessageData}"
  progCache.modify (·.insert p d)
  return d

def fetchWord (segs : List (Nat × List Nat)) (pc : Nat) : Option Nat :=
  match segs with
  | [] => none
  | (base, words) :: rest =>
    if base ≤ pc ∧ (pc - base) % 4 = 0 then
      match words[(pc - base) / 4]? with
      | some w => some w
      | none => fetchWord rest pc
    else fetchWord rest pc

/-- A literal natural number, possibly behind `OfNat.ofNat`, or an evaluable closed term. -/
def evalNat (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  if e.hasFVar || e.hasMVar then return none
  try return some (← evalNatCore e) catch _ => return none

/-- `BitVec.ofNat 64 n` (or the literal `n#64`) with `n` evaluable. -/
def bv64Value? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``BitVec.ofNat, #[w, n]) =>
    if (← evalNat w) == some 64 then evalNat n else return none
  | (``OfNat.ofNat, #[ty, n, _]) =>
    match (← whnfR ty).getAppFnArgs with
    | (``BitVec, #[w]) => if (← evalNat w) == some 64 then evalNat n else return none
    | _ => return none
  | _ => return none

/-! ## Kernel-checked Boolean facts -/

unsafe def evalNatExprImpl (e : Expr) : MetaM Nat := evalExpr Nat (mkConst ``Nat) e

/-- Prove `b = true` for a closed Boolean `b` by kernel evaluation only. -/
def kernelDecide (b : Expr) : MetaM Expr := do
  let ty ← mkEq b (mkConst ``Bool.true)
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let name ← try mkAuxLemma [] ty val catch e =>
    throwError "janus: kernel evaluation of{indentExpr b}\nfailed (it is not `true`):\n{e.toMessageData}"
  return mkConst name

/-- Evaluate `dataReadD p a n` on a closed program and literal `a`, `n`; the equation is checked
by the kernel (an auxiliary `rfl` lemma). -/
simproc_decl reduceDataReadD (dataReadD _ _ _) := fun e => do
  let_expr dataReadD p a n := e | return .continue
  if p.hasFVar || p.hasMVar then return .continue
  let some a' := a.nat? <|> a.rawNatLit? | return .continue
  let some n' := n.nat? <|> n.rawNatLit? | return .continue
  let some v ← evalNat (mkApp3 (mkConst ``dataReadD) p (mkNatLit a') (mkNatLit n')) |
    return .continue
  let ty ← mkEq e (mkNatLit v)
  let name ← try mkAuxLemma [] ty (← mkEqRefl (mkNatLit v)) catch _ => return .continue
  return .done { expr := mkNatLit v, proof? := mkConst name }

/-- Evaluate a closed `Nat` term (by the interpreter) and justify it by a kernel `rfl` lemma. -/
def evalClosedNat (e : Expr) : MetaM (Option Simp.Result) := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  let some v ← evalNat e | return none
  let ty ← mkEq e (mkNatLit v)
  let name ← try mkAuxLemma [] ty (← mkEqRefl (mkNatLit v)) catch _ => return none
  return some { expr := mkNatLit v, proof? := mkConst name }

/-- Bitmask immediates of `and`/`orr`/`eor` (immediate) and bitfield moves:
`((decodeBitMasks N imms immr imm M).getD (0, 0)).1` / `.2` on literals. -/
simproc_decl reduceBitMaskFst (Prod.fst (Option.getD (decodeBitMasks _ _ _ _ _) _)) := fun e => do
  match ← evalClosedNat e with
  | some r => return .done r
  | none => return .continue

simproc_decl reduceBitMaskSnd (Prod.snd (Option.getD (decodeBitMasks _ _ _ _ _) _)) := fun e => do
  match ← evalClosedNat e with
  | some r => return .done r
  | none => return .continue

/-- Bit-counting helpers on literals (`clz`, `rbit`, `rev`). -/
simproc_decl reduceClz (clzNat _ _) := fun e => do
  match ← evalClosedNat e with
  | some r => return .done r
  | none => return .continue

simproc_decl reduceRbit (rbitNat _ _) := fun e => do
  match ← evalClosedNat e with
  | some r => return .done r
  | none => return .continue

simproc_decl reduceRev (revContainersNat _ _ _) := fun e => do
  match ← evalClosedNat e with
  | some r => return .done r
  | none => return .continue

/-! ## The simp context -/

/-- Hypotheses describing the initial state(s): equations whose left-hand side is a state
projection (`s.pc`, `s.sp`, `s.flags`, `s.mem`) or a register `s.regs i`. -/
def stateHyps : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    -- facts about a symbolic return address (`RetAddr p ret`), as rewrite rules
    if ty.isAppOfArity ``GoABI.RetAddr 2 then
      for n in [``GoABI.RetAddr.toNat_ofNat, ``GoABI.RetAddr.mod64, ``GoABI.RetAddr.aligned_eq,
          ``GoABI.RetAddr.untagged_eq] do
        out := out.push (← mkAppM n #[d.toExpr])
      continue
    -- branch conditions introduced by `janus_run`
    if d.userName.eraseMacroScopes == `hbr && (← isProp ty) then
      out := out.push d.toExpr; continue
    -- rewrite rules for memory reads (e.g. from `janus_data`)
    let concl ← forallTelescopeReducing ty fun _ b => pure b
    if let some (_, l, _) := concl.eq? then
      if l.isAppOfArity ``Memory.readLE 3 && ty.isForall then
        out := out.push d.toExpr; continue
    let some (_, lhs, rhs) := ty.eq? | continue
    let isStateProj (e : Expr) : Bool :=
      e.isAppOfArity ``State.pc 1 || e.isAppOfArity ``State.sp 1 ||
      e.isAppOfArity ``State.flags 1 || e.isAppOfArity ``State.mem 1
    if isStateProj lhs || (lhs.isAppOfArity ``State.regs 2) then
      -- `x.pc = BitVec.ofNat 64 e` with `e` closed but not a literal: use the literal value
      if lhs.isAppOfArity ``State.pc 1 then
        if let some c ← bv64Value? rhs then
          let lit := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit c)
          if rhs != lit then
            out := out.push (← mkExpectedTypeHint d.toExpr (← mkEq lhs lit))
            continue
      out := out.push d.toExpr
  return out

structure Cfg where
  /-- Extra simp arguments (syntax). -/
  args : Array Term := #[]
  /-- Stop (without stepping) at these addresses, except at the start. -/
  stops : List Nat := []
  /-- Maximum number of instructions per `janus_run`. -/
  maxSteps : Nat := 100000
  /-- Callee summaries `(entry, proof of Summary p entry pre post)`. -/
  calls : Array (Nat × Expr) := #[]

/-- Build the `janus_exec` simp context (plus state hypotheses and user arguments) and run `k`
with it and its discharger. -/
def withExecSimp (cfg : Cfg) (k : Simp.Context → Simp.SimprocsArray → Option Simp.Discharge →
    TacticM α) (set : Name := `janus_exec) : TacticM α := do
  let hyps ← stateHyps
  let args : Array Term := #[⟨mkIdent set⟩] ++ cfg.args
  let sargs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← args.mapM fun t =>
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  let stx ← `(tactic| simp (disch := janus_disch) only [$sargs,*])
  let r ← mkSimpContext stx (eraseLocal := false)
  -- the state hypotheses are added as proof terms (also inaccessible ones)
  let mut ctx := r.ctx
  let mut thms := ctx.simpTheorems
  for h in hyps, k in [0:hyps.size] do
    if let some t0 := thms[0]? then
      thms := thms.set! 0 (← t0.add (.other (Name.mkNum `janus_state k)) #[] h)
  ctx := ctx.setSimpTheorems thms
  let mut simprocs := r.simprocs.push (← Simp.getSimprocs)
  let mut extra : Simp.Simprocs := {}
  for n in [``reduceDataReadD, ``reduceBitMaskFst, ``reduceBitMaskSnd, ``reduceClz, ``reduceRbit,
      ``reduceRev] do
    extra ← extra.add n (post := true)
  simprocs := simprocs.push extra
  r.dischargeWrapper.with fun d? => k ctx simprocs d?

def simpExpr (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (d? : Option Simp.Discharge)
    (e : Expr) : MetaM Simp.Result := do
  let (r, _) ← simp e ctx simprocs d?
  return r

def resultProof (e : Expr) (r : Simp.Result) : MetaM Expr := do
  match r.proof? with
  | some pf => return pf
  | none => mkEqRefl e

/-! ## One step -/

inductive GoalKind where
  /-- `Reaches p s Q` -/
  | reaches (p s Q : Expr)
  /-- `ExecThen p r Q` -/
  | execThen (p r Q : Expr)
  /-- `ReachesRet p ret s Q` -/
  | reachesRet (p ret s Q : Expr)
  /-- `ExecThenRet p ret r Q` -/
  | execThenRet (p ret r Q : Expr)
  | other

def goalKind (g : MVarId) : MetaM GoalKind := do
  let t ← instantiateMVars (← g.getType)
  let t := t.cleanupAnnotations.headBeta
  match t.getAppFnArgs with
  | (``Reaches, #[p, s, Q]) => return .reaches p s Q
  | (``ExecThen, #[p, r, Q]) => return .execThen p r Q
  | (``ReachesRet, #[p, ret, s, Q]) => return .reachesRet p ret s Q
  | (``ReachesRet.ExecThenRet, #[p, ret, r, Q]) => return .execThenRet p ret r Q
  | _ => return .other

/-- Try to close a goal `False`-like branch: the branch hypothesis is contradictory. -/
def tryPrune (g : MVarId) : TacticM Bool := withoutRecover do
  trace[janus] "branch: {← g.withContext do return (← getLCtx).lastDecl.map (·.type)}"
  let saved ← saveState
  let gs ← try
      Tactic.run g <| withoutRecover (evalTactic (← `(tactic| (exfalso; first
        | omega
        | (simp only [BitVec.toNat_eq, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, BitVec.toNat_zero, ne_eq, Nat.reducePow,
            Nat.zero_mod]
            at *; omega)))))
    catch _ => saved.restore; return false
  if !gs.isEmpty then saved.restore
  return gs.isEmpty

/-- Clean up the goal reached at an exit/stub: `IsReturn post (.returned s)` ↦ `post s` etc. -/
def cleanOutcome (cfg : Cfg) (g : MVarId) : TacticM (List MVarId) := g.withContext do
  setGoals [g]
  withExecSimp cfg (set := `janus_post) fun ctx simprocs d? => do
    match ← simpGoal g ctx simprocs d? with
    | (none, _) => return []
    | (some (_, g'), _) =>
      let t ← instantiateMVars (← g'.getType)
      if t.isConstOf ``True then g'.assign (mkConst ``True.intro); return []
      if !t.hasFVar && !t.hasMVar then
        let saved ← saveState
        try
          let gs ← Tactic.run g' <| withoutRecover (evalTactic (← `(tactic| decide +kernel)))
          if gs.isEmpty then return []
        catch _ => pure ()
        saved.restore
      return [g']

/-- The pc of state `s` as a literal, with a proof of `s.pc = BitVec.ofNat 64 c`; otherwise the
simplified pc with a proof of `s.pc = pc`. -/
def statePC (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (d? : Option Simp.Discharge)
    (s : Expr) : MetaM (Option (Nat × Expr) × Expr × Expr) := do
  let pcE ← mkAppM ``State.pc #[s]
  -- fast path: the normal form `State.mk _ _ pc _ _` with a literal pc
  let sw ← instantiateMVars s
  if sw.isAppOfArity ``Janus.Arm64.State.mk 5 then
    let pc := sw.getArg! 2
    if let some c ← bv64Value? pc then
      let ty ← mkEq pcE (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit c))
      return (some (c, ← mkExpectedTypeHint (← mkEqRefl pcE) ty), pc, ← mkEqRefl pcE)
  let r ← simpExpr ctx simprocs d? pcE
  let pf ← resultProof pcE r
  if let some c ← bv64Value? r.expr then
    let ty ← mkEq pcE (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit c))
    return (some (c, ← mkExpectedTypeHint pf ty), r.expr, pf)
  return (none, r.expr, pf)

/-- A program of the form `Program.withExit p ret` (a call with return address `ret`): `(p, ret)`. -/
def exitMode (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let p := (← instantiateMVars p).consumeMData
  match p.getAppFnArgs with
  | (``Program.withExit, #[base, ret]) => return some (base, ret)
  | _ => return none

/-- The hypothesis `RetAddr p ret` from the local context. -/
def findRetAddr (base ret : Expr) : MetaM Expr := do
  let want ← mkAppM ``GoABI.RetAddr #[base, ret]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``GoABI.RetAddr 2 then
      if ← withReducible (isDefEq ty want) then return d.toExpr
  throwError "janus: the program is{indentExpr (← mkAppM ``Program.withExit #[base, ret])}\nbut there is no hypothesis{indentExpr want}\nin the context (introduce it with `intro ret hret …`)"

/-- `pc` is syntactically `BitVec.ofNat 64 ret`. -/
def isRetPC (pc ret : Expr) : MetaM Bool := do
  let pc ← instantiateMVars pc
  let ret ← instantiateMVars ret
  match pc.getAppFnArgs with
  | (``BitVec.ofNat, #[w, r]) =>
    if (← evalNat w) != some 64 then return false
    if r == ret then return true
    withReducible (isDefEq r ret)
  | _ => return false

structure StepResult where
  goals : List MVarId
  /-- goals that are finished with symbolic execution (outcome reached) -/
  done : List MVarId := []

/-- Split `ExecThen` / `ite` structure after `exec` was simplified. -/
partial def afterExec (g : MVarId) : TacticM (List MVarId) := do
  match ← goalKind g with
  | .execThen _ r _ | .execThenRet _ _ r _ =>
    let isRet := match ← goalKind g with | .execThenRet .. => true | _ => false
    let r := (← instantiateMVars r).consumeMData.headBeta
    match r.getAppFnArgs with
    | (``Except.ok, #[_, _, _]) =>
      let lem := if isRet then ``ReachesRet.ok else ``ExecThen.ok
      let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
      afterExecList gs
    | (``ite, #[_, _, _, _, _]) =>
      let lem := if isRet then ``ReachesRet.ite else ``ExecThen.ite
      let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
      let mut out := []
      for g' in gs do
        if (← g'.isAssigned) then continue
        let t ← g'.getType
        if t.isForall then
          let (_, g'') ← g'.intro `hbr
          if ← tryPrune g'' then continue
          out := out ++ (← afterExec g'')
        else out := out ++ [g']
      return out
    | (``Except.error, _) =>
      throwError "janus: the instruction faults:{indentExpr r}"
    | _ =>
      throwError "janus: could not evaluate the instruction to `.ok s'` or a branch ({r.ctorName} {r.getAppFn}); stuck at{indentExpr r}\n(a memory access whose `accessible` condition could not be proved, an address that could not be normalised, or a read-over-write whose aliasing is unknown)"
  | .reaches _ s _ | .reachesRet _ _ s _ =>
    let s ← instantiateMVars s
    if s.isAppOfArity ``ite 5 then
      let isRet := match ← goalKind g with | .reachesRet .. => true | _ => false
      let lem := if isRet then ``ReachesRet.ite_state else ``Reaches.ite_state
      let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
      let mut out := []
      for g' in gs do
        if (← g'.isAssigned) then continue
        let t ← g'.getType
        if t.isForall then
          let (_, g'') ← g'.intro `hbr
          if ← tryPrune g'' then continue
          out := out ++ (← afterExec g'')
        else out := out ++ [g']
      return out
    return [g]
  | .other => return [g]
where
  afterExecList (gs : List MVarId) : TacticM (List MVarId) := do
    let mut out := []
    for g in gs do
      if ← g.isAssigned then continue
      out := out ++ (← afterExec g)
    return out

/-- Prove a callee precondition `pre s` with the post simp set, `omega` and assumptions. -/
def provePre (cfg : Cfg) (g : MVarId) : TacticM Unit := do
  let t ← instantiateMVars (← g.getType)
  g.setType t.headBeta
  let gs ← cleanOutcome cfg g
  for g in gs do
    let rest ← Tactic.run g <| withoutRecover (evalTactic (← `(tactic|
      (repeat' constructor) <;> first | rfl | assumption | omega | janus_disch)))
    unless rest.isEmpty do
      throwError "janus: cannot prove the callee precondition{indentExpr (← g.getType)}"

/-- Apply a callee summary at a call site: the goal continues from the callee's return state.
A postcondition of the form `s' = e` is substituted; conjunctions are split. -/
def applySummary (cfg : Cfg) (g : MVarId) (p s : Expr) (ret? : Option Expr) (hsum hpc : Expr) :
    TacticM (List MVarId) := g.withContext do
  let sty ← instantiateMVars (← inferType hsum)
  let (``Summary, #[_, entry, pre, post]) := sty.getAppFnArgs |
    throwError "janus: not a `Summary`:{indentExpr sty}"
  let hpc ← mkExpectedTypeHint hpc
    (← mkEq (← mkAppM ``State.pc #[s]) (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) entry))
  let hpreM ← mkFreshExprSyntheticOpaqueMVar (mkApp pre s).headBeta
  let lem := match ← goalKind g, ret? with
    | .reachesRet _ ret _ Q, _ =>
      mkAppN (mkConst ``ReachesRet.call) #[p, entry, pre, post, s, ret, Q, hsum, hpc, hpreM]
    | .reaches _ _ Q, _ =>
      mkAppN (mkConst ``Reaches.call) #[p, entry, pre, post, s, Q, hsum, hpc, hpreM]
    | _, _ => default
  let gs ← g.apply lem
  provePre cfg hpreM.mvarId!
  let mut out := []
  for g' in gs do
    if ← g'.isAssigned then continue
    let (fv, g'') ← g'.introNP 3
    let g'' ← g''.withContext do
      let hpost := fv[2]!
      let t ← instantiateMVars (← hpost.getType)
      let t := t.headBeta
      let g ← g''.replaceLocalDeclDefEq hpost t
      if let some (_, lhs, _) := t.eq? then
        if lhs.isFVar && lhs.fvarId! == fv[0]! then
          let g ← g.clear fv[1]!
          return (← substCore g hpost (symm := false) (tryToSkip := true)).2
      -- split conjunctions into separate hypotheses
      g.casesAnd
    out := out ++ [g'']
  return out

/-- Perform one step on `g` (a `Reaches`/`ReachesRet` goal). Returns the new goals and whether
the goal reached an outcome (exit, stub, return address). -/
def stepGoal (cfg : Cfg) (g : MVarId) (allowStop : Bool) : TacticM (Option (List MVarId)) :=
  g.withContext do
  setGoals [g]
  let t0 ← IO.monoMsNow
  withExecSimp cfg fun ctx simprocs d? => do
    trace[janus] "simp context: {(← IO.monoMsNow) - t0} ms"
    let (p, s, ret?) ← match ← goalKind g with
      | .reaches p s _ => pure (p, s, none)
      | .reachesRet p ret s _ => pure (p, s, some ret)
      | _ => throwError "janus: goal is not `Reaches p s Q`"
    let (pc?, pcE, pcPf) ← statePC ctx simprocs d? s
    trace[janus] "state pc: {pcE}, ret: {ret?}"
    -- a call with a symbolic return address: `p = Program.withExit base retE`
    let mode ← exitMode p
    if mode.isSome && ret?.isSome then
      throwError "janus: `ReachesRet` on a program with a return address (`Program.withExit`) is not supported; prove the callee as a `Summary` of the extracted program"
    let hret? ← match mode with
      | some (base, retE) => pure (some (← findRetAddr base retE))
      | none => pure none
    let progE := match mode with | some (base, _) => base | none => p
    -- return address reached (`ReachesRet`)
    if let some ret := ret? then
      if ← isDefEq pcE ret then
        let pcEq ← mkAppM ``State.pc #[s]
        let r ← simpExpr ctx simprocs d? pcEq
        let hpc ← resultProof pcEq r
        let Q := match ← goalKind g with | .reachesRet _ _ _ Q => Q | _ => default
        let hpc ← mkExpectedTypeHint hpc (← mkEq pcEq ret)
        let gs ← g.apply (mkAppN (mkConst ``ReachesRet.done) #[p, ret, s, Q, hpc])
        return some gs
    -- the return address reached (`Program.withExit`)
    if let (some (base, retE), some hret) := (mode, hret?) then
      let atRet ← match pc? with
        | none => isRetPC pcE retE
        | some (c, _) => pure ((← evalNat retE) == some c)
      if atRet then
        let Q := match ← goalKind g with | .reaches _ _ Q => Q | _ => default
        let hpc ← mkExpectedTypeHint pcPf
          (← mkEq (← mkAppM ``State.pc #[s]) (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) retE))
        let gs ← g.apply (mkAppN (mkConst ``Reaches.exit_withExit) #[base, retE, s, Q, hret, hpc])
        return some gs
    let some (c, hpc) := pc? |
      throwError "janus: the pc of the current state is not a concrete address:{indentExpr pcE}"
    if !allowStop && cfg.stops.contains c then return none
    -- a call to a function with a summary
    if let some (_, hsum) := cfg.calls.find? (·.1 == c) then
      let hsum ← match hret? with
        | some hret => mkAppM ``Summary.withExit #[hsum, hret]
        | none => pure hsum
      return some (← applySummary cfg g p s ret? hsum hpc)
    let (exitA, segs, stubs) ← getProgData progE
    let cE := mkNatLit c
    if mode.isNone && c == exitA then
      if ret?.isSome then throwError "janus: reached the exit address inside a callee"
      let hok ← kernelDecide (mkApp2 (mkConst ``exitOK) p cE)
      let Q := match ← goalKind g with | .reaches _ _ Q => Q | _ => default
      let gs ← g.apply (mkAppN (mkConst ``Reaches.exit) #[p, s, Q, cE, hpc, hok])
      return some gs
    if let some (_, name, isPanic) := stubs.find? (·.1 == c) then
      if ret?.isSome then throwError "janus: reached stub {name} inside a callee"
      let kind := if isPanic then mkConst ``StubKind.panic else mkConst ``StubKind.morestack
      let hok ← kernelDecide (mkApp4 (mkConst ``stubOK) progE cE (toExpr name) kind)
      let Q := match ← goalKind g with | .reaches _ _ Q => Q | _ => default
      let lem := match mode, hret? with
        | some (base, retE), some hret =>
          mkAppN (mkConst ``Reaches.stub_withExit) #[base, retE, s, Q, cE, toExpr name, kind, hret,
            hpc, hok]
        | _, _ => mkAppN (mkConst ``Reaches.stub) #[p, s, Q, cE, toExpr name, kind, hpc, hok]
      let gs ← g.apply lem
      return some gs
    let some w := fetchWord segs c |
      throwError "janus: no code at pc {c} (0x{String.ofList (Nat.toDigits 16 c)})"
    let some i := decode w |
      throwError "janus: undecodable word 0x{String.ofList (Nat.toDigits 16 w)} at pc 0x{String.ofList (Nat.toDigits 16 c)}"
    let iE := toExpr i
    trace[janus] "pc 0x{String.ofList (Nat.toDigits 16 c)}: {repr i}"
    let hok ← kernelDecide (mkApp4 (mkConst ``stepOK) progE cE (mkNatLit w) iE)
    let execE := mkApp2 (mkConst ``exec) iE s
    let t0 ← IO.monoMsNow
    let r ← simpExpr ctx simprocs d? execE
    trace[janus] "simp exec: {(← IO.monoMsNow) - t0} ms"

    let he ← resultProof execE r
    let lemE := match ← goalKind g with
      | .reachesRet _ ret _ Q =>
        mkAppN (mkConst ``ReachesRet.step) #[p, ret, s, Q, cE, mkNatLit w, iE, r.expr, hpc, hok, he]
      | .reaches _ _ Q =>
        match mode, hret? with
        | some (base, retE), some hret =>
          mkAppN (mkConst ``Reaches.step_withExit)
            #[base, retE, s, Q, cE, mkNatLit w, iE, r.expr, hret, hpc, hok, he]
        | _, _ => mkAppN (mkConst ``Reaches.step) #[p, s, Q, cE, mkNatLit w, iE, r.expr, hpc, hok, he]
      | _ => default
    let gs ← g.apply lemE
    let mut out := []
    for g' in gs do
      if ← g'.isAssigned then continue
      out := out ++ (← afterExec g')
    return some out

/-- Turn `Returns`/`Panics`/`GrowsStack` goals into `Reaches`. -/
def prepGoal (g : MVarId) : MetaM MVarId := do
  let t ← instantiateMVars (← g.getType)
  let t ← whnfR t
  let tryApply (n : Name) : MetaM MVarId := do
    let gs ← g.apply (← mkConstWithFreshMVarLevels n)
    match gs with
    | [g'] => return g'
    | _ => throwError "janus: unexpected goals after {n}"
  match t.getAppFn.constName? with
  | some ``GoABI.Returns => tryApply ``returns_of_reaches
  | some ``GoABI.Panics => tryApply ``panics_of_reaches
  | some ``GoABI.GrowsStack => tryApply ``growsStack_of_reaches
  | _ => return g

def isStepGoal (g : MVarId) : MetaM Bool := do
  match ← goalKind g with
  | .reaches .. | .reachesRet .. => return true
  | _ => return false

/-- Run symbolic execution on the main goal. -/
def runJanus (cfg : Cfg) (single : Bool) : TacticM Unit := do
  let g ← getMainGoal
  let g ← prepGoal g
  let mut todo : List (MVarId × Bool) := [(g, true)]
  let mut finished : List MVarId := []
  let mut steps := 0
  while !todo.isEmpty do
    let (g, first) :: rest := todo | break
    todo := rest
    if ← g.isAssigned then continue
    if !(← isStepGoal g) then
      let t0 ← IO.monoMsNow
      finished := finished ++ (← cleanOutcome cfg g)
      trace[janus] "clean-up of a final goal: {(← IO.monoMsNow) - t0} ms"
      continue
    if steps ≥ cfg.maxSteps || (single && !first) then
      finished := finished ++ [g]; continue
    let t0 ← IO.monoMsNow
    let res ← stepGoal cfg g first
    trace[janus] "step total: {(← IO.monoMsNow) - t0} ms"
    match res with
    | none => finished := finished ++ [g]
    | some gs =>
      steps := steps + 1
      todo := gs.map (·, false) ++ todo
  replaceMainGoal finished

/-! ## Discharger -/

theorem accessible_sub {m : Memory} {a n b k : Nat} {w w' : Bool}
    (h : m.accessible b k w' = true) (hw : (w = false ∨ w' = true)) (h1 : b ≤ a)
    (h2 : a + n ≤ b + k) : m.accessible a n w = true :=
  Memory.accessible_sub m h hw h1 h2

/-- Prove `m.accessible a n w = true` from a hypothesis about the same memory. -/
def dischargeAccessible (g : MVarId) : TacticM Bool := withoutRecover <| g.withContext do
  -- strip writes: `accessible_writeLE`
  let gs ← Tactic.run g <| withoutRecover (evalTactic (← `(tactic|
    try simp only [janus_acc, State.mem] )))
  let some g := gs.head? | return true
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := t.eq? | return false
  unless lhs.isAppOfArity ``Memory.accessible 4 do return false
  let m := lhs.getArg! 0
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, _) := ty.eq? | continue
    unless l.isAppOfArity ``Memory.accessible 4 do continue
    unless ← isDefEq (l.getArg! 0) m do continue
    let saved ← saveState
    let ok ← try
        let gs ← Tactic.run g <| withoutRecover do
          let lemE := mkAppN (mkConst ``accessible_sub)
            #[m, lhs.getArg! 1, lhs.getArg! 2, l.getArg! 1, l.getArg! 2, lhs.getArg! 3, l.getArg! 3,
              d.toExpr]
          let gs ← (← getMainGoal).apply lemE
          setGoals gs
          evalTactic (← `(tactic| all_goals first | decide | omega | simp))
        pure gs.isEmpty
      catch _ => pure false
    if ok then return true
    saved.restore
  return false

elab_rules : tactic | `(tactic| janus_disch) => withoutRecover do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if (← isTracingEnabledFor `janus.disch) then
    let hs ← g.withContext do (← getLCtx).foldlM (init := #[]) fun acc d =>
      if d.isImplementationDetail then pure acc else pure (acc.push m!"{d.userName} : {d.type}")
    trace[janus.disch] "goal {t}\n{MessageData.joinSep hs.toList "\n"}"
  if !t.hasFVar && !t.hasMVar then
    let saved ← saveState
    let gs ← try Tactic.run g <| withoutRecover (evalTactic (← `(tactic| decide +kernel))) catch _ => saved.restore; pure [g]
    if gs.isEmpty then return
    -- A closed goal that `decide` refutes must not be proved from (possibly contradictory)
    -- hypotheses: simp enters `if` branches with the branch condition as a hypothesis, and
    -- proving e.g. `29 < 16` there would make the register-sorting lemma loop.
    throwError "janus_disch: closed goal is false:{indentExpr t}"
  if let some (_, lhs, _) := t.eq? then
    if lhs.isAppOfArity ``Memory.accessible 4 then
      if ← dischargeAccessible g then return
      throwError "janus_disch: cannot prove{indentExpr t}"
  -- side conditions that are only meant for literals (`Nat.blt c k = true`, ...) are not
  -- attempted on symbolic terms
  if let some (_, lhs, rhs) := t.eq? then
    if rhs.isConstOf ``Bool.true && (lhs.getAppFn.isConstOf ``Nat.blt ||
        lhs.getAppFn.isConstOf ``Nat.ble || lhs.getAppFn.isConstOf ``and) then
      throwError "janus_disch: literal-only side condition"
  evalTactic (← `(tactic| first
    | omega
    | (simp -failIfUnchanged (disch := omega) only [janus_disch_norm, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub,
        Nat.reduceMul, Nat.reduceMod, Nat.reduceDiv]; omega)))

/-! ## Arithmetic -/

partial def collectReadLE (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``Memory.readLE 3 then acc.push e else
  match e with
  | .app f a => collectReadLE a (collectReadLE f acc)
  | .lam _ t b _ | .forallE _ t b _ => collectReadLE b (collectReadLE t acc)
  | .letE _ t v b _ => collectReadLE b (collectReadLE v (collectReadLE t acc))
  | .mdata _ b => collectReadLE b acc
  | .proj _ _ b => collectReadLE b acc
  | _ => acc

/-- Add `Memory.readLE m a n < 256^n` (as a literal bound) for every `readLE` with a literal
width in the goal and the hypotheses. -/
def addReadLEBounds : TacticM Unit := withMainContext do
  let mut seen : Std.HashSet Expr := {}
  let mut tys := #[← instantiateMVars (← getMainTarget)]
  for d in ← getLCtx do
    if !d.isImplementationDetail then tys := tys.push (← instantiateMVars d.type)
  for t in tys do
    for e in collectReadLE t #[] do
      if seen.contains e then continue
      seen := seen.insert e
      if e.hasLooseBVars then continue
      let some n := (e.getArg! 2).nat? | continue
      let g ← getMainGoal
      let bound := mkNatLit (256 ^ n)
      let ty ← mkAppM ``LT.lt #[e, bound]
      let pf ← mkExpectedTypeHint (← mkAppM ``Memory.readLE_lt #[e.getArg! 0, e.getArg! 1, e.getArg! 2]) ty
      let (_, g') ← (← g.assert `h_rd ty pf).intro1P
      replaceMainGoal [g']

/-- `omega` with the range facts of every memory read (`readLE … < 256^n`). -/
elab "janus_arith" : tactic => do
  if (← getUnsolvedGoals).isEmpty then return
  addReadLEBounds
  evalTactic (← `(tactic| try simp (disch := omega) only [janus_arith_norm]))
  evalTactic (← `(tactic| omega))

/-! ## Syntax -/

syntax janusArgs := (" [" term,* "]")?
syntax janusUntil := (" until " "[" term,* "]")?
syntax janusCalls := (" calls " "[" term,* "]")?

def parseArgs (stx : Syntax) : Array Term :=
  if stx[0].isNone then #[] else stx[0][1].getSepArgs.map (⟨·⟩)

def parseUntil (stx : Syntax) : TacticM (List Nat) := do
  if stx[0].isNone then return []
  let ts := stx[0][2].getSepArgs
  ts.toList.mapM fun t => do
    let e ← Term.elabTerm t (some (mkConst ``Nat))
    let some n ← evalNat e | throwError "janus_run until: not a numeral: {t}"
    return n

def parseCalls (stx : Syntax) : TacticM (Array (Nat × Expr)) := do
  if stx[0].isNone then return #[]
  let ts := stx[0][2].getSepArgs
  ts.mapM fun t => do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← instantiateMVars (← inferType e)
    let (``Summary, #[_, entry, _, _]) := ty.getAppFnArgs |
      throwError "janus_run calls: {t} is not a `Summary`: {ty}"
    let some n ← evalNat entry | throwError "janus_run calls: cannot evaluate the entry of {t}"
    return (n, e)

/-- Symbolically execute until every branch reaches an outcome (see module doc). -/
elab "janus_run" args:janusArgs stops:janusUntil calls:janusCalls : tactic => withMainContext do
  runJanus { args := parseArgs args, stops := ← parseUntil stops, calls := ← parseCalls calls } false

/-- Simplify the goal with the `janus_post` simp set, the state hypotheses and the given lemmas
(arithmetic side conditions by `janus_disch`). Fails if no progress is made. -/
elab "janus_simp" args:janusArgs : tactic => withMainContext do
  let g ← getMainGoal
  let gs ← cleanOutcome { args := parseArgs args } g
  replaceMainGoal gs

/-- One symbolic execution step. -/
elab "janus_step" args:janusArgs : tactic => do
  runJanus { args := parseArgs args } true

/-- From `h : p.DataLoaded m`, add `h_data<k> : m.accessible base len false = true` for every data
segment `k` of `p` (literal bounds), and `h_rodata : ∀ a n, (dataRead p a n).isSome = true →
m.readLE a n = dataReadD p a n`, which `janus_run` uses to evaluate loads from the data. -/
elab "janus_data " h:ident : tactic => withMainContext do
  let hE ← elabTerm h none
  let ty ← instantiateMVars (← inferType hE)
  let (``Program.DataLoaded, #[p, m]) := ty.getAppFnArgs |
    throwError "janus_data: expected a `Program.DataLoaded p m` hypothesis"
  let some k ← evalNat (← mkAppM ``List.length #[← mkAppM ``Program.data #[p]]) |
    throwError "janus_data: cannot evaluate the data segments of the program"
  let mut g ← getMainGoal
  for i in [0:k] do
    g ← g.withContext do
      let dE ← mkAppM ``getElem! #[← mkAppM ``Program.data #[p], mkNatLit i]
      let some base ← evalNat (← mkAppM ``DataSegment.base #[dE]) | throwError "janus_data: base"
      let some len ← evalNat (← mkAppM ``List.length #[← mkAppM ``DataSegment.bytes #[dE]]) |
        throwError "janus_data: length"
      let accTy ← mkEq (mkAppN (mkConst ``Memory.accessible) #[m, mkNatLit base, mkNatLit len,
        mkConst ``Bool.false]) (mkConst ``Bool.true)
      let lenLt ← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[← mkAppM ``Program.data #[p]]]
      let hlt ← mkDecideProof lenLt
      let pf ← mkExpectedTypeHint (mkAppN (mkConst ``accessible_of_dataLoaded) #[p, m, hE, mkNatLit i, hlt]) accTy
      let (_, g') ← (← g.assert (Name.mkSimple s!"h_data{i}") accTy pf).intro1P
      return g'
  g ← g.withContext do
    let pf := mkAppN (mkConst ``readLE_dataReadD) #[p, m, hE]
    let (_, g') ← (← g.assert `h_rodata (← inferType pf) pf).intro1P
    return g'
  replaceMainGoal [g]

/-- `janus_cases h` with `h : k < N` (or `k ≤ N`), `N` a literal: one goal per value of `k`,
with `k` replaced by the literal everywhere (if `k` is a variable; otherwise as a hypothesis
`hk : k = i`). Used for loads at a symbolic index from a small constant table. -/
elab "janus_cases " h:ident : tactic => withMainContext do
  let hE ← elabTerm h none
  let ty ← instantiateMVars (← inferType hE)
  let (k, n) ← match ty.getAppFnArgs with
    | (``LT.lt, #[_, _, k, n]) => pure (k, ← evalNat n)
    | (``LE.le, #[_, _, k, n]) => pure (k, (← evalNat n).map (· + 1))
    | _ => throwError "janus_cases: expected `k < N` or `k ≤ N`"
  let some n := n | throwError "janus_cases: the bound must be a literal"
  if n == 0 then
    evalTactic (← `(tactic| exact absurd $h (by omega)))
    return
  let kStx ← Term.exprToSyntax k
  let alts : List Term ← (List.range n).mapM fun i => `($kStx = $(Syntax.mkNumLit (toString i)))
  let disj ← match alts.reverse with
    | [] => unreachable!
    | a :: rest => rest.foldlM (fun acc t => `($t ∨ $acc)) a
  evalTactic (← `(tactic| rcases (show $disj from by omega) with $(mkIdent `h_case):ident))
  -- split the disjunction
  let mut goals ← getGoals
  let mut out := []
  for _ in [0:n] do
    match goals with
    | [] => break
    | g :: rest =>
      goals := rest
      let gs ← Tactic.run g <| withoutRecover do
        let some d := (← getLCtx).findFromUserName? `h_case | return
        let t ← instantiateMVars d.type
        if t.isAppOfArity ``Or 2 then
          evalTactic (← `(tactic| rcases $(mkIdent `h_case):ident with $(mkIdent `h_case):ident | $(mkIdent `h_case):ident))
      match gs with
      | [g1, g2] => out := out ++ [g1]; goals := g2 :: goals
      | gs => out := out ++ gs
  -- substitute
  let mut res := []
  for g in out do
    let gs ← Tactic.run g <| withoutRecover do
      if k.isFVar then
        evalTactic (← `(tactic| subst $(mkIdent `h_case):ident))
      else
        evalTactic (← `(tactic| try simp only [$(mkIdent `h_case):ident] at *))
    res := res ++ gs
  replaceMainGoal res

/-- From `hs : CallSetup p entry [a₀, …] s`, add `h_pc : s.pc = BitVec.ofNat 64 entry`,
`h_lr : s.regs 30 = BitVec.ofNat 64 p.exitAddr` and `h_x<i> : s.regs i = aᵢ`. For a call with a
symbolic return address (`p = Program.withExit p₀ ret`, with `hret : RetAddr p₀ ret` in the
context) `h_lr` is `s.regs 30 = BitVec.ofNat 64 ret`; `janus_run` uses `hret` itself. -/
elab "janus_intro " h:ident : tactic => withMainContext do
  let hE ← elabTerm h none
  let ty ← whnfR (← instantiateMVars (← inferType hE))
  let (``GoABI.CallSetup, #[_, _, args, s]) := ty.getAppFnArgs |
    throwError "janus_intro: expected a `CallSetup` hypothesis"
  let some (_, elemsL) := (← instantiateMVars args).listLit? |
    throwError "janus_intro: the argument list must be a list literal"
  let elems := elemsL.toArray
  let mut g ← getMainGoal
  let (``GoABI.CallSetup, #[prog, entry, _, _]) := ty.getAppFnArgs | unreachable!
  let some entryN ← evalNat entry | throwError "janus_intro: cannot evaluate the entry address"
  let mode ← exitMode prog
  let bv (n : Nat) : Expr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)
  -- the return address: `ret` for `Program.withExit p ret`, else the literal exit address
  let exitE ← match mode with
    | some (_, retE) => pure retE
    | none =>
      let some exitN ← evalNat (← mkAppM ``Program.exitAddr #[prog]) |
        throwError "janus_intro: cannot evaluate the exit address"
      pure (mkNatLit exitN)
  let pcTy ← mkEq (← mkAppM ``State.pc #[s]) (bv entryN)
  let pcPf ← mkExpectedTypeHint (← mkAppM ``GoABI.CallSetup.pc #[hE]) pcTy
  let (_, g') ← (← g.assert `h_pc pcTy pcPf).intro1P
  g := g'
  g ← g.withContext do
    let lrTy ← mkEq (mkApp (← mkAppM ``State.regs #[s]) (mkNatLit 30))
      (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) exitE)
    let lrPf ← mkExpectedTypeHint (← mkAppM ``GoABI.CallSetup.lr #[hE]) lrTy
    let (_, g') ← (← g.assert `h_lr lrTy lrPf).intro1P
    return g'
  -- a symbolic return address needs its `RetAddr` hypothesis (used by `janus_run`)
  if let some (base, retE) := mode then
    discard <| g.withContext (findRetAddr base retE)
  for i in [0:elems.size] do
    g ← g.withContext do
      let regs ← mkAppM ``State.regs #[s]
      let lhs := mkApp regs (mkNatLit i)
      let tyI ← mkEq lhs elems[i]!
      let lenLt ← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[args]]
      let hlt ← mkDecideProof lenLt
      let pf ← mkAppOptM ``GoABI.CallSetup.reg #[none, none, none, none, hE, mkNatLit i, hlt]
      let pf ← mkExpectedTypeHint pf tyI
      let (_, g') ← (← g.assert (Name.mkSimple s!"h_x{i}") tyI pf).intro1P
      return g'
  replaceMainGoal [g]

end Janus.Tactic
