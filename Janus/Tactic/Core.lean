import Lean
import Janus.Tactic.Basic
import Janus.Tactic.Data
import Janus.Tactic.Common
import Janus.Tactic.Disasm
import Janus.Tactic.Carry

/-!
# Symbolic execution tactics

* `janus_run [lemmas] (until [pc, ...])? (calls [h, ...])? ((budget := N))?` steps a goal of the form
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
open Janus.Tactic.Common (Status StepCache hex)

deriving instance ToExpr for ShiftType
deriving instance ToExpr for ExtendType
deriving instance ToExpr for LogicOp
deriving instance ToExpr for MoveWideOp
deriving instance ToExpr for BitfieldOp
deriving instance ToExpr for Imm9Mode
deriving instance ToExpr for PairMode
deriving instance ToExpr for AtomicOp
deriving instance ToExpr for CryptoInstr
deriving instance ToExpr for Instr
deriving instance ToExpr for StubKind

/-- The side-condition discharger (defined below). -/
syntax "janus_disch" : tactic

initialize registerTraceClass `janus
initialize registerTraceClass `janus.disch

/-! ## Program data, evaluated once per program -/

abbrev ProgData := Nat × List (Nat × List Nat) × List (Nat × String × Nat)

/-- `evalExpr` of `e`, over imported constants when possible (`Common.unfoldLocalDefs`: then it
does not wait for the rest of the file), else of `e` itself. -/
unsafe def evalExprLocalFree (α) (ty e : Expr) : MetaM α := do
  let e' ← Common.unfoldLocalDefs e
  if e' == e then return ← evalExpr α ty e
  try evalExpr α ty e' catch _ => evalExpr α ty e

unsafe def evalProgDataImpl (p : Expr) : MetaM ProgData := do
  let e := mkApp (mkConst ``progData) p
  let ty ← inferType e
  evalExprLocalFree ProgData ty e

@[implemented_by evalProgDataImpl]
opaque evalProgDataCore (p : Expr) : MetaM ProgData

unsafe def evalNatImpl (e : Expr) : MetaM Nat := evalExprLocalFree Nat (mkConst ``Nat) e

@[implemented_by evalNatImpl]
opaque evalNatCore (e : Expr) : MetaM Nat

/-- Segment names and ranges (bytes), for messages. -/
def progSyms (p : Program) : List (String × Nat × Nat) :=
  p.segments.map fun seg => (seg.name, seg.base, 4 * seg.words.length)

unsafe def evalProgSymsImpl (p : Expr) : MetaM (List (String × Nat × Nat)) := do
  let e := mkApp (mkConst ``progSyms) p
  evalExprLocalFree (List (String × Nat × Nat)) (← inferType e) e

@[implemented_by evalProgSymsImpl]
opaque evalProgSymsCore (p : Expr) : MetaM (List (String × Nat × Nat))

initialize progCache : IO.Ref (Std.HashMap Expr (ProgData × List (String × Nat × Nat))) ←
  IO.mkRef {}

def getProgData (p : Expr) : MetaM (ProgData × List (String × Nat × Nat)) := do
  let p ← instantiateMVars p
  if let some d := (← progCache.get).get? p then return d
  if p.hasFVar || p.hasMVar then
    throwError "janus_run: the program must be a closed term (e.g. `Extracted.program`), got{indentExpr p}"
  let d ← try evalProgDataCore p catch e =>
    throwError "janus_run: cannot evaluate the program{indentExpr p}\n{e.toMessageData}"
  let syms ← try evalProgSymsCore p catch _ => pure []
  progCache.modify (·.insert p (d, syms))
  return (d, syms)

/-- The name of the tactic, in messages. -/
def tacName : String := "janus_run"

/-- The checked memory operations of the model (`fn m addr size …`), for diagnostics. -/
def accessFns : List (Name × Bool) := [(``Janus.Arm64.load, false), (``Janus.Arm64.store, true)]

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

/-- Writing back the old value of a register leaves the register file unchanged. -/
theorem setReg_restore (f : Nat → W64) (r : Nat) (v : W64) (h : f r = v) : setReg f r v = f := by
  funext i; simp only [setReg]; split
  · next he => subst he; exact h.symm
  · rfl

/-- `setReg f r (s.regs r)` with `f` a chain over `s.regs` that does not write `r` is `f` (a
callee-saved register restored from the stack). -/
simproc_decl reduceSetRegRestore (setReg _ _ _) := fun e => do
  let some (f, r, v, h) ← Common.restoredReg? ``setReg ``State.regs e | return .continue
  return .done { expr := f, proof? := mkAppN (mkConst ``setReg_restore) #[f, r, v, h] }

/-! ## The simp context -/

/-- Hypotheses describing the initial state(s): equations whose left-hand side is a state
projection (`s.pc`, `s.sp`, `s.flags`, `s.mem`, `s.fpcr`, `s.fpsr`) or a register `s.regs i`. -/
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
    -- callee memory frames: their `readLE`/`accessible` rewrite rules
    if ty.isAppOfArity ``Janus.MemFrame 3 then
      out := out ++ (← Common.frameRules d ty); continue
    -- branch conditions introduced by `janus_run`
    if d.userName.eraseMacroScopes == `hbr && (← isProp ty) then
      out := out.push d.toExpr; continue
    -- rewrite rules for memory reads (e.g. from `janus_data`)
    let concl ← forallTelescopeReducing ty fun _ b => pure b
    if let some (_, l, _) := concl.eq? then
      if l.isAppOfArity ``Memory.readLE 3 && ty.isForall then
        out := out.push d.toExpr; continue
    let some (_, lhs, rhs) := ty.eq? | continue
    -- named memory facts `h_rd… : m.readLE a n = v` (e.g. from `generalize h_rd… : … = v`, to
    -- keep the symbolic state small) and those of the dynamic-call vocabulary, from `janus_dyn`
    -- (`Janus.Tactic.Dynamic`): rewrite rules
    if lhs.isAppOfArity ``Memory.readLE 3 &&
        ("h_dyn".isPrefixOf d.userName.eraseMacroScopes.toString ||
         "h_rd".isPrefixOf d.userName.eraseMacroScopes.toString) then
      out := out.push d.toExpr; continue
    let isStateProj (e : Expr) : Bool :=
      e.isAppOfArity ``State.pc 1 || e.isAppOfArity ``State.sp 1 ||
      e.isAppOfArity ``State.flags 1 || e.isAppOfArity ``State.mem 1 ||
      e.isAppOfArity ``State.fpcr 1 || e.isAppOfArity ``State.fpsr 1
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

/-- What the executor knows about one pc: the word, the decoded instruction and the kernel proof
of `stepOK` (computed once per run). -/
structure FetchFact where
  prog : Expr
  word : Nat
  instr : Instr
  hok : Expr

structure Cfg where
  /-- Extra simp arguments (syntax). -/
  args : Array Term := #[]
  /-- Stop (without stepping) at these addresses, except at the start. -/
  stops : List Nat := []
  /-- Maximum number of instructions per `janus_run`. -/
  maxSteps : Nat := 100000
  /-- Callee summaries `(entry, proof of Summary p entry pre post)`. -/
  calls : Array (Nat × Expr) := #[]
  /-- Heartbeat budget of the run, in thousands (`janus_run (budget := N)`). -/
  budget : Option Nat := none
  status : IO.Ref Status
  cache : IO.Ref StepCache
  facts : IO.Ref (Std.HashMap Nat FetchFact)

def Cfg.new (args : Array Term := #[]) (stops : List Nat := []) (calls : Array (Nat × Expr) := #[])
    (budget : Option Nat := none) : IO Cfg := do
  return { args, stops, calls, budget, status := ← IO.mkRef {}, cache := ← IO.mkRef {},
           facts := ← IO.mkRef {} }

/-- Build the `set` simp context (plus state hypotheses and user arguments) for the current
local context, or reuse the one of an earlier step with the same local context, and run `k`
with it and its discharger. -/
def withExecSimp (cfg : Cfg) (k : Simp.Context → Simp.SimprocsArray → Option Simp.Discharge →
    TacticM α) (set : Name := `janus_exec) : TacticM α := do
  Common.withCachedCtx cfg.cache set (k := k) do
  let hyps ← stateHyps
  let args : Array Term := #[⟨mkIdent set⟩] ++ cfg.args
  let sargs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← args.mapM fun t =>
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  let stx ← `(tactic| simp (config := { maxSteps := 2000000 }) (disch := janus_disch) only [$sargs,*])
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
  for n in [``reduceSetRegRestore, ``reduceDataReadD, ``reduceBitMaskFst, ``reduceBitMaskSnd, ``reduceClz, ``reduceRbit,
      ``reduceRev] do
    extra ← extra.add n (post := true)
  simprocs := simprocs.push extra
  return (ctx, simprocs, r.dischargeWrapper)

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
            at *; omega)
        | (simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_false',
            Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not,
            not_and, not_or, Classical.not_not, ne_eq]
            at *; omega)))))
    catch _ => saved.restore; return false
  if !gs.isEmpty then saved.restore
  return gs.isEmpty

/-- Clean up the goal reached at an exit/stub: `IsReturn post (.returned s)` ↦ `post s` etc. -/
def cleanOutcome (cfg : Cfg) (g : MVarId) : TacticM (List MVarId) := g.withContext do
  setGoals [g]
  withExecSimp cfg (set := `janus_post) fun ctx simprocs d? => do
    -- no progress is not an error here: the goal is returned as it is
    match ← (try simpGoal g ctx simprocs d? catch e => do
        if (← e.toMessageData.toString).contains "made no progress" then pure (some (#[], g), {})
        else throw e) with
    | (none, _) => return []
    | (some (_, g'), _) =>
      let t ← instantiateMVars (← g'.getType)
      if t.isConstOf ``True then g'.assign (mkConst ``True.intro); return []
      if !t.hasFVar && !t.hasMVar then
        if ← Common.decideClosed g' then return []
      return [g']

/-- The pc of state `s` as a literal, with a proof of `s.pc = BitVec.ofNat 64 c`; otherwise the
simplified pc with a proof of `s.pc = pc`. -/
def statePC (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (d? : Option Simp.Discharge)
    (s : Expr) : MetaM (Option (Nat × Expr) × Expr × Expr) := do
  let pcE ← mkAppM ``State.pc #[s]
  -- fast path: a state literal `State.mk … pc …` with a literal pc (robust to the number of
  -- fields of `State`)
  let sw ← instantiateMVars s
  if let some (nf, idx) ← Common.fieldIndex ``Janus.Arm64.State `pc then
    if sw.isAppOfArity ``Janus.Arm64.State.mk nf then
      let pc := sw.getArg! idx
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

/-- A program of the form `Program.link p impl` (the extracted code linked with arbitrary
code for its contracts): `(p, impl)`. The program facts are evaluated on the closed `p` and
lifted with `stepOK_link`/`stubOK_link`/`exitOK_link`. -/
def linkMode (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let p := (← instantiateMVars p).consumeMData
  match p.getAppFnArgs with
  | (``Program.link, #[base, impl]) => return some (base, impl)
  | _ => return none

/-- `h : fact p …` lifted to `fact (p.link impl) …` when the program is linked. -/
def liftLink (impl? : Option Expr) (lem : Name) (h : Expr) : MetaM Expr := do
  match impl? with
  | some impl => mkAppM lem #[impl, h]
  | none => return h

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

/-- What a fault means, and what usually rules it out. -/
def explainFault (f : Expr) : MessageData :=
  match f.getAppFn.constName? with
  | some ``Fault.spMisaligned =>
    m!"the stack pointer is used as a base register while not 16-byte aligned (add \
      `s.sp.toNat % 16 = 0`, part of `StackOK`)"
  | some ``Fault.pcMisaligned =>
    m!"the branch target is not 4-byte aligned (or tagged); for a `RET`, `X30` must hold an \
      admissible return address (`h_lr`, `RetAddr`)"
  | some ``Fault.noCode =>
    m!"the branch target is not code; a register target at or above 2^56 (a tagged pointer, \
      not modelled) also ends here: add a bound on the target register"
  | some ``Fault.outsideAllocation | some ``Fault.readOnly =>
    m!"the access is outside the allocations (or writes read-only memory) according to the \
      hypotheses"
  | _ => m!"the model has no defined result here"

/-- Split `ExecThen` / `ite` structure after `exec` was simplified. -/
partial def afterExec (cfg : Cfg) (g : MVarId) : TacticM (List MVarId) := do
  match ← goalKind g with
  | .execThen _ r _ | .execThenRet _ _ r _ =>
    let isRet := match ← goalKind g with | .execThenRet .. => true | _ => false
    let r := (← instantiateMVars r).consumeMData.headBeta
    match r.getAppFnArgs with
    | (``Except.ok, #[_, _, _]) =>
      let lem := if isRet then ``ReachesRet.ok else ``ExecThen.ok
      let gs ← Common.applyFast g (← mkConstWithFreshMVarLevels lem)
      afterExecList gs
    | (``ite, #[_, _, _, _, _]) =>
      let lem := if isRet then ``ReachesRet.ite else ``ExecThen.ite
      let gs ← Common.applyFast g (← mkConstWithFreshMVarLevels lem)
      branches gs
    | (``Except.error, #[_, _, f]) =>
      let st ← cfg.status.get
      throwError "{tacName}: the instruction {st.where_} faults:{indentExpr f}\n({explainFault f})\
        {← g.withContext Common.branchConds}"
    | _ =>
      let st ← cfg.status.get
      throwError (← g.withContext (Common.explainStuck tacName st accessFns r))
  | .reaches _ s _ | .reachesRet _ _ s _ =>
    let s ← instantiateMVars s
    if s.isAppOfArity ``ite 5 then
      let isRet := match ← goalKind g with | .reachesRet .. => true | _ => false
      let lem := if isRet then ``ReachesRet.ite_state else ``Reaches.ite_state
      let gs ← Common.applyFast g (← mkConstWithFreshMVarLevels lem)
      return ← branches gs
    return [g]
  | .other => return [g]
where
  afterExecList (gs : List MVarId) : TacticM (List MVarId) := do
    let mut out := []
    for g in gs do
      if ← g.isAssigned then continue
      out := out ++ (← afterExec cfg g)
    return out
  branches (gs : List MVarId) : TacticM (List MVarId) := do
    let mut out := []
    for g' in gs do
      if (← g'.isAssigned) then continue
      let t ← g'.getType
      if t.isForall then
        let (_, g'') ← g'.intro `hbr
        Common.setPhase cfg.status "pruning a branch (omega on the branch condition)"
        if ← tryPrune g'' then continue
        out := out ++ (← afterExec cfg g'')
      else out := out ++ [g']
    return out

/-- Prove a callee precondition `pre s` with the post simp set, `omega` and assumptions. -/
def provePre (cfg : Cfg) (g : MVarId) (callee : String) : TacticM Unit := do
  -- reducible transparency only in the closers: unfolding `Memory.accessible`/`readLE` of a
  -- symbolic memory to compare it with a hypothesis can take seconds
  let closer ← `(tactic| first | with_reducible rfl | with_reducible assumption | omega | janus_disch)
  let left ← Common.provePreCore (cleanOutcome cfg) closer g
  unless left.isEmpty do
    let st ← cfg.status.get
    throwError "{tacName}: at pc {(st.pc.map hex).getD "?"}, the entry of {callee}: the \
      precondition of its summary could not be proved. Remaining goals (after simplification):\
      {MessageData.joinSep (left.toList.map indentExpr) "\n"}\nAdd the facts they need to the \
      context, or weaken the summary's precondition."

/-- Apply a callee summary at a call site: the goal continues from the callee's return state.
The postcondition is split into hypotheses (conjunctions, existentials); an equation `s' = e`
is substituted. -/
def applySummary (cfg : Cfg) (g : MVarId) (p s : Expr) (hsum hpc : Expr) (callee : String) :
    TacticM (List MVarId) := g.withContext do
  let sty ← instantiateMVars (← inferType hsum)
  let (``Summary, #[_, entry, pre, post]) := sty.getAppFnArgs |
    throwError "{tacName}: not a `Summary`:{indentExpr sty}"
  let hpc ← mkExpectedTypeHint hpc
    (← mkEq (← mkAppM ``State.pc #[s]) (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) entry))
  let hpreM ← mkFreshExprSyntheticOpaqueMVar (mkApp pre s).headBeta
  let lem ← match ← goalKind g with
    | .reachesRet _ ret _ Q =>
      pure <| mkAppN (mkConst ``ReachesRet.call) #[p, entry, pre, post, s, ret, Q, hsum, hpc, hpreM]
    | .reaches _ _ Q =>
      pure <| mkAppN (mkConst ``Reaches.call) #[p, entry, pre, post, s, Q, hsum, hpc, hpreM]
    | _ => throwError "{tacName}: unexpected goal at a call"
  let gs ← Common.applyFast g lem
  Common.setPhase cfg.status s!"proving the precondition of the summary of {callee}"
  provePre cfg hpreM.mvarId! callee
  let mut out := []
  for g' in gs do
    if ← g'.isAssigned then continue
    let before ← g'.withContext do return (← getLCtx).getFVarIds
    let (fv, g'') ← g'.introNP 3
    let g'' ← Common.destructPost g'' fv[0]! fv[1]! fv[2]!
    out := out ++ [← normFrames cfg g'' before]
  return out
where
  /-- Simplify the callee's `MemFrame` hypotheses and the other propositions its postcondition
  added (their terms mention the call-site state literal), so that `omega` and the
  accessibility discharger see the addresses in normal form. -/
  stateEq (ty : Expr) : Bool :=
    match ty.eq? with
    | some (_, l, _) => l.getAppFn.constName?.any (·.getPrefix == ``Janus.Arm64.State)
    | none => false
  normFrames (cfg : Cfg) (g : MVarId) (before : Array FVarId) : TacticM MVarId := g.withContext do
    let mut ids := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``Janus.MemFrame 3 then ids := ids.push d.fvarId
      -- an equation about a state component (`s'.regs 19 = …`) is a state hypothesis: it is a
      -- rewrite rule of the simp set itself, and simplifying it with that set turns it into `True`
      else if !before.contains d.fvarId && (← isProp ty) && !(stateEq ty) then ids := ids.push d.fvarId
    if ids.isEmpty then return g
    setGoals [g]
    withExecSimp cfg (set := `janus_post) fun ctx simprocs d? => do
      match ← (try simpGoal g ctx simprocs d? (fvarIdsToSimp := ids) (simplifyTarget := false)
          catch _ => pure (some (#[], g), {})) with
      | (some (_, g'), _) => return g'
      | (none, _) => return g

/-- Perform one step on `g` (a `Reaches`/`ReachesRet` goal). `none`: stopped at an `until`
address. -/
def stepGoal (cfg : Cfg) (g : MVarId) (allowStop : Bool) : TacticM (Option (List MVarId)) :=
  g.withContext do
  setGoals [g]
  cfg.status.modify fun st =>
    { st with pc := none, sym := none, instr := none, phase := "computing the pc of the state" }
  let t0 ← IO.monoMsNow
  withExecSimp cfg fun ctx simprocs d? => do
    trace[janus] "simp context: {(← IO.monoMsNow) - t0} ms"
    let (p, s, ret?, Q) ← match ← goalKind g with
      | .reaches p s Q => pure (p, s, none, Q)
      | .reachesRet p ret s Q => pure (p, s, some ret, Q)
      | _ => throwError "{tacName}: the goal is not `Reaches p s Q` or `ReachesRet p ret s Q`:{indentExpr (← g.getType)}"
    let (pc?, pcE, pcPf) ← statePC ctx simprocs d? s
    trace[janus] "state pc: {pcE}, ret: {ret?}"
    -- a call with a symbolic return address: `p = Program.withExit base retE`
    let mode ← exitMode p
    if mode.isSome && ret?.isSome then
      throwError "{tacName}: `ReachesRet` on a program with a return address (`Program.withExit`) is not supported; prove the callee as a `Summary` of the extracted program"
    let hret? ← match mode with
      | some (base, retE) => pure (some (← findRetAddr base retE))
      | none => pure none
    let progE := match mode with | some (base, _) => base | none => p
    -- the return address of a callee (`ReachesRet`): compare with the normal form of `ret`
    if let some ret := ret? then
      let rr ← simpExpr ctx simprocs d? ret
      if pcE == rr.expr || (← withReducible (isDefEq pcE rr.expr)) then
        let hpc ← mkEqTrans pcPf (← mkEqSymm (← resultProof ret rr))
        let hpc ← mkExpectedTypeHint hpc (← mkEq (← mkAppM ``State.pc #[s]) ret)
        return some (← Common.applyFast g (mkAppN (mkConst ``ReachesRet.done) #[p, ret, s, Q, hpc]))
    -- the return address reached (`Program.withExit`)
    if let (some (base, retE), some hret) := (mode, hret?) then
      let atRet ← match pc? with
        | none => isRetPC pcE retE
        | some (c, _) => pure ((← evalNat retE) == some c)
      if atRet then
        let hpc ← mkExpectedTypeHint pcPf
          (← mkEq (← mkAppM ``State.pc #[s]) (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) retE))
        return some (← Common.applyFast g (mkAppN (mkConst ``Reaches.exit_withExit) #[base, retE, s, Q, hret, hpc]))
    let some (c, hpc) := pc? |
      throwError "{tacName}: stuck after {(← cfg.status.get).steps} instructions: the pc of the \
        current state is not a concrete address:{indentExpr pcE}\n\
        This is an indirect branch (`br`, `blr`, `ret`) to an address the hypotheses do not \
        determine. For the return of the function being proved, run `p.withExit ret` with \
        `hret : RetAddr p ret` in the context (`intro ret hret …`) and keep `h_lr`; for a callee, \
        prove it as a `Summary` and pass it with `calls [...]`; otherwise add an equation \
        `… = BitVec.ofNat 64 addr` for the target register."
    let (evalE, impl?) ← match ← linkMode progE with
      | some (b, impl) => pure (b, some impl)
      | none => pure (progE, none)
    let ((exitA, segs, stubs), syms) ← getProgData evalE
    cfg.status.modify fun st => { st with pc := some c, sym := Common.symOf syms c }
    if !allowStop && cfg.stops.contains c then return none
    -- a call to a function with a summary
    if let some (_, hsum) := cfg.calls.find? (·.1 == c) then
      let hsum ← match hret? with
        | some hret => mkAppM ``Summary.withExit #[hsum, hret]
        | none => pure hsum
      let callee := (Common.symOf syms c).getD (hex c)
      cfg.status.modify fun st => { st with instr := some s!"(entry of {callee}, by its summary)" }
      return some (← applySummary cfg g p s hsum hpc callee)
    let cE := mkNatLit c
    if mode.isNone && c == exitA then
      if ret?.isSome then throwError "{tacName}: reached the exit address {hex c} inside a callee"
      let hok ← liftLink impl? ``exitOK_link (← kernelDecide (mkApp2 (mkConst ``exitOK) evalE cE))
      return some (← Common.applyFast g (mkAppN (mkConst ``Reaches.exit) #[p, s, Q, cE, hpc, hok]))
    if let some (_, name, kindCode) := stubs.find? (·.1 == c) then
      if ret?.isSome then
        throwError "{tacName}: the callee reaches the runtime stub {name} at {hex c}; a \
          `Summary` only covers runs that return. Add the precondition that excludes this path \
          (e.g. `GuardOK` for `morestack`, a bound for a panic)."
      let kind := match kindCode with
        | 0 => mkConst ``StubKind.panic
        | 1 => mkConst ``StubKind.morestack
        | _ => mkConst ``StubKind.external
      let hok ← liftLink impl? ``stubOK_link
        (← kernelDecide (mkApp4 (mkConst ``stubOK) evalE cE (toExpr name) kind))
      let lem := match mode, hret? with
        | some (base, retE), some hret =>
          mkAppN (mkConst ``Reaches.stub_withExit) #[base, retE, s, Q, cE, toExpr name, kind, hret,
            hpc, hok]
        | _, _ => mkAppN (mkConst ``Reaches.stub) #[p, s, Q, cE, toExpr name, kind, hpc, hok]
      return some (← Common.applyFast g lem)
    -- the instruction at `c` (decoded and checked once per run)
    let fact ← match (← cfg.facts.get).get? c with
      | some f => if f.prog == progE then pure f else mkFact progE evalE impl? segs syms c
      | none => mkFact progE evalE impl? segs syms c
    let iE := toExpr fact.instr
    let ins := Janus.Arm64.Disasm.disasm (some c) fact.instr
    cfg.status.modify fun st => { st with
      instr := some ins, phase := "evaluating the instruction (simp with the janus_exec set)" }
    trace[janus] "pc {hex c}: {ins}"
    let execE := mkApp2 (mkConst ``exec) iE s
    let t0 ← IO.monoMsNow
    let r ← Common.simpCached cfg.cache ctx simprocs d? execE
    trace[janus] "simp exec: {(← IO.monoMsNow) - t0} ms"
    let he ← resultProof execE r
    Common.noteAliases cfg.status r.expr
    let lemE := match ret? with
      | some ret =>
        mkAppN (mkConst ``ReachesRet.step) #[p, ret, s, Q, cE, mkNatLit fact.word, iE, r.expr, hpc,
          fact.hok, he]
      | none => match mode, hret? with
        | some (base, retE), some hret =>
          mkAppN (mkConst ``Reaches.step_withExit)
            #[base, retE, s, Q, cE, mkNatLit fact.word, iE, r.expr, hret, hpc, fact.hok, he]
        | _, _ => mkAppN (mkConst ``Reaches.step)
            #[p, s, Q, cE, mkNatLit fact.word, iE, r.expr, hpc, fact.hok, he]
    let gs ← Common.applyFast g lemE
    Common.setPhase cfg.status "splitting the result (branches)"
    let mut out := []
    for g' in gs do
      if ← g'.isAssigned then continue
      out := out ++ (← afterExec cfg g')
    return some out
where
  mkFact (progE evalE : Expr) (impl? : Option Expr) (segs : List (Nat × List Nat)) (syms : List (String × Nat × Nat)) (c : Nat) :
      TacticM FetchFact := do
    let some w := fetchWord segs c |
      throwError "{tacName}: stuck after {(← cfg.status.get).steps} instructions: pc {hex c} is \
        not in the extracted code (segments: {MessageData.joinSep (syms.map fun (n, b, sz) =>
          m!"{n} [{hex b}, {hex (b + sz)})") ", "}) and is no known stub.\nIf this is a call, \
        extract the callee too or give its `Summary` with `calls [...]`; if it is the return, `X30` \
        does not hold the return address of `p.withExit ret`."
    let symS := match Common.symOf syms c with | some s => s!" ({s})" | none => ""
    let some i := decode w |
      throwError "{tacName}: stuck at pc {hex c}{symS}: the word {hex w} does not decode to a \
        modelled instruction (see docs/SOUNDNESS.md for the supported subset). No proof can \
        execute past it."
    let hok ← liftLink impl? ``stepOK_link
      (← kernelDecide (mkApp4 (mkConst ``stepOK) evalE (mkNatLit c) (mkNatLit w) (toExpr i)))
    let f : FetchFact := { prog := progE, word := w, instr := i, hok }
    cfg.facts.modify (·.insert c f)
    return f

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

/-- The literal pc of a `Reaches`/`ReachesRet` goal whose state is a `State.mk` literal (path
merging, `Common.pickMerged`). -/
def goalPC (g : MVarId) : MetaM (Option Nat) := do
  let s ← match ← goalKind g with
    | .reaches _ s _ | .reachesRet _ _ s _ => pure s
    | _ => return none
  let s ← instantiateMVars s
  let some (nf, idx) ← Common.fieldIndex ``Janus.Arm64.State `pc | return none
  unless s.isAppOfArity ``Janus.Arm64.State.mk nf do return none
  bv64Value? (s.getArg! idx)

/-- Run symbolic execution on the main goal (`single`: one step only). -/
def runJanus (cfg : Cfg) (single : Bool) : TacticM Unit := Common.withBudget cfg.budget do
  let g ← getMainGoal
  let g ← prepGoal g
  let mut todo : List (MVarId × Bool) := [(g, true)]
  let mut finished : List MVarId := []
  let mut steps := 0
  let merge := Common.janus.merge.get (← getOptions)
  while !todo.isEmpty do
    if merge then todo ← Common.pickMerged { memTypes := [``Janus.Arm64.Memory], regChains := [(``setReg, ``State.regs)], restore := [``reduceSetRegRestore] } goalPC todo
    let (g, first) :: rest := todo | break
    todo := rest
    if ← g.isAssigned then continue
    if !(← isStepGoal g) then
      let t0 ← IO.monoMsNow
      Common.setPhase cfg.status "simplifying a final goal (janus_post)"
      finished := finished ++ (← Common.guardStep tacName cfg.status cfg.budget (cleanOutcome cfg g))
      trace[janus] "clean-up of a final goal: {(← IO.monoMsNow) - t0} ms"
      continue
    if steps ≥ cfg.maxSteps || (single && !first) then
      finished := finished ++ [g]; continue
    cfg.status.modify fun st => { st with steps }
    let t0 ← IO.monoMsNow
    let res ← Common.guardStep tacName cfg.status cfg.budget (stepGoal cfg g first)
    trace[janus] "step total: {(← IO.monoMsNow) - t0} ms"
    match res with
    | none => finished := finished ++ [g]
    | some gs =>
      steps := steps + 1
      todo := gs.map (·, false) ++ todo
  Common.reportAliases tacName cfg.status finished
  replaceMainGoal finished

/-! ## Discharger -/

theorem accessible_sub {m : Memory} {a n b k : Nat} {w w' : Bool}
    (h : m.accessible b k w' = true) (hw : (w = false ∨ w' = true)) (h1 : b ≤ a)
    (h2 : a + n ≤ b + k) : m.accessible a n w = true :=
  Memory.accessible_sub m h hw h1 h2

/-- Prove `m.accessible a n w = true` from a hypothesis about the same memory. -/
def dischargeAccessible (g : MVarId) : TacticM Bool := withoutRecover <| g.withContext do
  -- through stores and callee frames (`MemFrame`)
  let g ← Common.reduceAccessible g
  -- strip writes: `accessible_writeLE`
  let gs ← Tactic.run g <| withoutRecover (evalTactic (← `(tactic|
    try simp only [janus_acc, State.mem] )))
  let some g := gs.head? | return true
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := t.eq? | return false
  unless lhs.isAppOfArity ``Memory.accessible 4 do return false
  let m := lhs.getArg! 0
  for d in ← Common.accessibleOrder lhs do
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
          evalTactic (← `(tactic| all_goals first | decide | janus_omega | simp))
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
    -- literal comparisons: evaluated here (no auxiliary declaration per side condition)
    match ← Common.closeByEval? g with
    | some true => return
    | some false => throwError "janus_disch: closed goal is false:{indentExpr t}"
    | none => pure ()
    if ← Common.decideClosed g then return
    -- A closed goal that `decide` refutes must not be proved from (possibly contradictory)
    -- hypotheses: simp enters `if` branches with the branch condition as a hypothesis, and
    -- proving e.g. `29 < 16` there would make the register-sorting lemma loop.
    throwError "janus_disch: closed goal is false:{indentExpr t}"
  if t.isAppOfArity ``Janus.Outside 3 then
    if ← Common.dischargeOutside g then return
    throwError "janus_disch: cannot prove{indentExpr t}"
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
  -- carry-chain bounds and equations (`x / 2^64 < 2^64` for a carry): by reflection, which
  -- also knows the bounds of products that `omega` does not
  match ← Janus.Carry.dischCarry g with
  | some true => return
  | some false => throwError "janus_disch: carry bound does not hold for all limb values"
  | none => pure ()
  evalTactic (← `(tactic| first
    | janus_apart
    | janus_omega
    | (simp -failIfUnchanged (disch := omega) only [janus_disch_norm, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub,
        Nat.reduceMul, Nat.reduceMod, Nat.reduceDiv]; omega)))

/-! ## Arithmetic -/

/-- The carry-chain procedure `janus_carry` first (equations of limb arithmetic, by
reflection); otherwise `omega` with the range facts of every memory read
(`readLE … < 256^n`) after normalising carry terms. -/
elab "janus_arith" : tactic => do
  if (← getUnsolvedGoals).isEmpty then return
  if ← Janus.Carry.tryCarry then return
  Common.addReadLEBounds
  evalTactic (← `(tactic| try simp (disch := omega) only [janus_arith_norm]))
  evalTactic (← `(tactic| omega))

/-! ## Syntax -/

syntax janusArgs := (" [" term,* "]")?
syntax janusUntil := (" until " "[" term,* "]")?
syntax janusCalls := (" calls " "[" term,* "]")?
syntax janusBudget := (" (" &"budget" " := " num ")")?

def parseArgs (stx : Syntax) : Array Term :=
  if stx[0].isNone then #[] else stx[0][1].getSepArgs.map (⟨·⟩)

def parseUntil (stx : Syntax) : TacticM (List Nat) := do
  if stx[0].isNone then return []
  let ts := stx[0][2].getSepArgs
  ts.toList.mapM fun t => do
    let e ← Term.elabTerm t (some (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let some n ← evalNat e | throwError "janus_run until: not a numeral: {t}"
    return n

def parseCalls (stx : Syntax) : TacticM (Array (Nat × Expr)) := do
  if stx[0].isNone then return #[]
  let ts := stx[0][2].getSepArgs
  ts.mapM fun t => do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty0 ← instantiateMVars (← inferType e)
    -- a named contract (`def NewobjectContract … := Summary …`) is unfolded to its `Summary`
    let mut ty := ty0
    for _ in [0:8] do
      if ty.isAppOf ``Summary then break
      match ← unfoldDefinition? ty with
      | some ty' => ty := ty'.headBeta
      | none => break
    let e ← if ty == ty0 then pure e else mkExpectedTypeHint e ty
    let (``Summary, #[_, entry, _, _]) := ty.getAppFnArgs |
      throwError "janus_run calls: {t} is not a `Summary`: {ty0}"
    let some n ← evalNat entry | throwError "janus_run calls: cannot evaluate the entry of {t}"
    return (n, e)

def parseBudget (stx : Syntax) : Option Nat :=
  if stx[0].isNone then none else stx[0][3].isNatLit?

/-- Symbolically execute until every branch reaches an outcome (see module doc). `calls [h, …]`
uses callee summaries instead of executing the callees; `(budget := N)` limits the run to `N`
thousand heartbeats (a run that exceeds its budget, or `maxHeartbeats`, stops with a message
naming the pc, the instruction and what it was doing). -/
elab "janus_run" bud0:janusBudget args:janusArgs stops:janusUntil cs:janusCalls bud:janusBudget : tactic =>
    withMainContext do
  let cfg ← Cfg.new (parseArgs args) (← parseUntil stops) (← parseCalls cs)
    ((parseBudget bud).orElse fun _ => parseBudget bud0)
  runJanus cfg false

/-- Simplify the goal with the `janus_post` simp set, the state hypotheses and the given lemmas
(arithmetic side conditions by `janus_disch`). Fails if no progress is made. -/
elab "janus_simp" args:janusArgs : tactic => withMainContext do
  let g ← getMainGoal
  let gs ← cleanOutcome (← Cfg.new (parseArgs args)) g
  replaceMainGoal gs

/-- One symbolic execution step. -/
elab "janus_step" args:janusArgs cs:janusCalls bud:janusBudget : tactic => withMainContext do
  runJanus (← Cfg.new (parseArgs args) [] (← parseCalls cs) (parseBudget bud)) true

/-- From `h : p.DataLoaded m`, add `h_data<k> : m.accessible base len false = true` for every data
segment `k` of `p` (literal bounds), and `h_rodata : ∀ a n, (dataRead p a n).isSome = true →
m.readLE a n = dataReadD p a n`, which `janus_run` uses to evaluate loads from the data. 
`janus_data hd [hw₁, …]` additionally, for each `hwᵢ : m.accessible a n true = true` (a
writable range of the same memory), `h_ddisj<i>_<k> : a + n ≤ base ∨ base + len ≤ a` for every data
object `k`: read-only data is disjoint from writable memory (`disjoint_of_dataLoaded`). -/
syntax janusDataWith := (" [" ident,* "]")?

elab "janus_data " h:ident ws:janusDataWith : tactic => withMainContext do
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
  do
    let hws : Array (TSyntax `ident) := (Common.collectIdents ws.raw).map (⟨·⟩)
    for hw in hws, j in [0:hws.size] do
      g ← g.withContext do
        let hwE ← Term.elabTerm hw none
        let hwTy ← instantiateMVars (← inferType hwE)
        let some (_, lhs, _) := hwTy.eq? |
          throwError "janus_data: {hw} is not `m.accessible a n true = true`"
        unless lhs.isAppOfArity ``Memory.accessible 4 do
          throwError "janus_data: {hw} is not `m.accessible a n true = true`"
        let a := lhs.getArg! 1
        let n := lhs.getArg! 2
        let mut g := g
        for i in [0:k] do
          g ← g.withContext do
            let dE ← mkAppM ``getElem! #[← mkAppM ``Program.data #[p], mkNatLit i]
            let some base ← evalNat (← mkAppM ``DataSegment.base #[dE]) | throwError "janus_data: base"
            let some len ← evalNat (← mkAppM ``List.length #[← mkAppM ``DataSegment.bytes #[dE]]) |
              throwError "janus_data: length"
            let lenLt ← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[← mkAppM ``Program.data #[p]]]
            let hlt ← mkDecideProof lenLt
            let ty := mkOr (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[a, n], mkNatLit base])
              (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[mkNatLit base, mkNatLit len], a])
            let pairs ← mkAppM ``Option.map #[
              ← withLocalDeclD `d (mkConst ``DataSegment) fun d => do
                mkLambdaFVars #[d] (← mkAppM ``Prod.mk #[← mkAppM ``DataSegment.base #[d],
                  ← mkAppM ``List.length #[← mkAppM ``DataSegment.bytes #[d]]]),
              ← mkAppM ``GetElem?.getElem? #[← mkAppM ``Program.data #[p], mkNatLit i]]
            let want ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[mkNatLit base, mkNatLit len]]
            let hbl ← kernelDecide (← mkAppM ``BEq.beq #[pairs, want])
            let pf := mkAppN (mkConst ``disjoint_of_dataLoaded')
              #[p, m, hE, mkNatLit i, mkNatLit base, mkNatLit len, hbl, a, n, hwE]
            let (_, g') ← (← g.assert (Name.mkSimple s!"h_ddisj{j}_{i}") ty pf).intro1P
            return g'
        return g
  g ← g.withContext do
    let pf := mkAppN (mkConst ``readLE_dataReadD) #[p, m, hE]
    let (_, g') ← (← g.assert `h_rodata (← inferType pf) pf).intro1P
    return g'
  replaceMainGoal [g]

/-- `janus_cases h` with `h : k < N` (or `k ≤ N`), `N` a literal: one goal per value of `k`,
with `k` replaced by the literal everywhere (if `k` is a variable; otherwise as a hypothesis
`hk : k = i`). Used for loads at a symbolic index from a small constant table. -/
elab "janus_cases " h:ident : tactic => Common.casesBound "janus_cases" h

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
