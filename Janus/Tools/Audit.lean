import Janus
import Lean

/-!
# `janus-audit`: the trusted theorem and statement auditor

`janus verify` runs this compiled executable instead of elaborating an audit `.lean` file, so
**no code from the proof ever runs** (A3, A6 in `docs/AUDIT.md`): it imports the proof's compiled
module with `importModules` and never calls `enableInitializersExecution`, which means the
proof's `initialize` blocks, `#eval`s and macros do not execute here. Importing an `.olean`
only loads declarations.

Given the theorem name, the proof module name and a marker, it

* checks the theorem is a `theorem` declared in the proof module;
* collects its transitive axioms (`collectAxioms`) for the allow-list check in Go;
* checks the imported `Extracted.program`/`entry` are **kernel-defeq** to an independently
  elaborated trusted copy `JanusTrusted` (C1): a planted or shadowed `Extracted` is rejected;
* checks every constant in the theorem's *type* comes from Lean/Std core, `Janus.*`,
  `Extracted.*`, or is a plain proof-local `def`/`theorem` that is not an instance, class value,
  axiom, opaque or unsafe (A1); requires the type to mention `Extracted.program`/`entry`
  (so the statement is about the extracted code), and that the proof declares no name with an
  `Extracted` component (A9, A7);
* accepts constants declared in **dependency modules** (the pinned extra Lake dependencies of a
  consumer package, named by module root on the command line) only when they are plain `def`s
  and theorems, or the inductive types/structures, constructors and recursors they are built
  from — never instances (wherever the `instance` attribute was attached), classes or
  class-valued defs, opaques, axioms or unsafe declarations. Instance and class information is
  read from the imported modules' raw environment-extension entries, so no dependency code runs.
  Dependency constants are not unfolded further: their bodies are the pinned dependency's;
* pretty-prints the statement in a **clean environment** that imports only `Janus` and
  `Extracted` (never the proof), with the allowed proof-local defs re-added, so the proof's
  unexpanders, delaborators, notations and instances cannot change what is printed (A2, A4).
  Dependency constants the statement reaches are added there as type-only declarations taken
  from the dependency modules, so the dependency's own notations and delaborators (which would be
  dependency code running in this trusted process) do not apply either;
* checks the printed statement **means what was checked** (round 2, CRITICAL-1): every
  instance-implicit argument of the statement must be a registered trusted instance or an
  instance binder of the theorem (`checkInstArgs`), and the printed text must parse and
  elaborate back, in the same clean environment, to a type definitionally equal to the checked
  one (`printFaithful`/`roundTrip`); then prints it once more with `pp.explicit`.

Output: one line `<marker>{json}` on stdout (the record), or `<marker>ERROR <message>`.
Everything else on stderr. The marker is an argument, not read from any file.
-/

open Lean

namespace JanusAudit

/-- Is `mod` a module whose declarations are trusted to appear in a statement's type? -/
def trustedModule (mod : Name) : Bool :=
  let root := mod.getRoot
  root == `Init || root == `Std || root == `Lean || root == `Janus
    || root == `Extracted || root == `JanusTrusted

/-- The analysis result, printed as JSON for the Go side. -/
structure Record where
  name        : String
  kind        : String
  module      : String
  axioms      : Array String
  statement   : String
  /-- The statement printed with `pp.explicit true` (instance arguments visible). -/
  statementExplicit : String
  definitions : Array String  -- "<name> : <type> := <value>" for each allowed proof-local def
  modules     : Array String
  external    : Array String  -- "<name> (<kind>, <module>)" for each dependency constant used
  /-- The import graph of every module outside the toolchain core (`Init`, `Std`, `Lean`,
  `Lake`): `[module, direct import, …]`. The Go side kernel-replays each of these modules and
  keys its replay cache on the module's bytes and those of its imports. -/
  imports     : Array (Array String)
  deriving ToJson

/-- A module shipped with the Lean toolchain (trusted, never replayed by `janus verify`). -/
def coreModule (mod : Name) : Bool :=
  let root := mod.getRoot
  root == `Init || root == `Std || root == `Lean || root == `Lake

/-- The direct imports of every non-core module of `env`, for `Record.imports`. -/
def importGraph (env : Environment) : Array (Array String) := Id.run do
  let mut out := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]
    if coreModule m then continue
    let imps := match env.header.moduleData[i]? with
      | some d => d.imports.map (·.module.toString)
      | none => #[]
    out := out.push (#[m.toString] ++ imps)
  return out

/-- Where a module comes from: the trusted framework/core, a declared dependency package, or the
consumer package / proof. -/
inductive Origin where
  | trusted | dependency | consumer
  deriving BEq

/-- What the audit knows about the imported environment besides its constants: which module
roots belong to declared dependencies, and every instance and class name, collected from the
raw extension entries of each imported module (so `importModules (loadExts := false)` suffices
and no imported code runs). -/
structure Ctx where
  env       : Environment
  depRoots  : Std.HashSet Name
  instances : Std.HashSet Name
  classes   : Std.HashSet Name

def Ctx.originOfModule (cx : Ctx) (mod : Name) : Origin :=
  if trustedModule mod then .trusted
  else if cx.depRoots.contains mod.getRoot then .dependency
  else .consumer

/-- The module that declares `c`, if any. -/
def Ctx.moduleOf? (cx : Ctx) (c : Name) : Option Name :=
  (cx.env.getModuleIdxFor? c).map fun idx => cx.env.header.moduleNames[idx.toNat]!

def Ctx.originOf (cx : Ctx) (c : Name) : Origin :=
  match cx.moduleOf? c with
  | some m => cx.originOfModule m
  | none => .consumer

/-- Collect instance and class names from every imported module's extension entries. An
`attribute [instance] foo` in any module counts, as do scoped and local-to-namespace ones. -/
def mkCtx (env : Environment) (depRoots : Array String) : Ctx := Id.run do
  let mut instances : Std.HashSet Name := {}
  let mut classes : Std.HashSet Name := {}
  for i in [0:env.header.moduleNames.size] do
    for e in Meta.instanceExtension.ext.getModuleEntries env i do
      let ie := match e with
        | .global ie => ie
        | .scoped _ ie => ie
      if let some n := ie.globalName? then
        instances := instances.insert n
    for ce in classExtension.getModuleEntries env i do
      classes := classes.insert ce.name
  return { env, instances, classes,
           depRoots := depRoots.foldl (fun s r => s.insert r.toName) {} }

/-- A fatal audit failure with a message for the Go side. -/
structure Failure where
  msg : String

abbrev AuditM := ExceptT Failure IO

def fail {α} (msg : String) : AuditM α := throw { msg }

def mkCoreCtx : Core.Context :=
  { fileName := "<janus-audit>", fileMap := default, maxHeartbeats := 0 }

/-- Run a `CoreM` over `env`, turning any exception into a `Failure`. -/
def runCore (env : Environment) (x : CoreM α) : AuditM α := do
  match ← (Core.CoreM.toIO' x mkCoreCtx { env }).toBaseIO with
  | .ok a => return a
  | .error e => fail e.toString

/-- Kernel-check `decl` against `env`; the environment on success, a message on a kernel error. -/
def kernelAdd (env : Environment) (decl : Declaration) : AuditM Environment := do
  match env.addDeclCore (maxHeartbeats := 0) (maxRecDepth := 10000) decl none (doCheck := true) with
  | .ok env => return env
  | .error ex => fail (← (ex.toMessageData {}).toString)

/-- Turn a `ConstantInfo` back into a `Declaration` for re-adding (defs and theorems only). -/
def ciToDecl : ConstantInfo → Option Declaration
  | .defnInfo v => some (.defnDecl v)
  | .thmInfo v => some (.thmDecl v)
  | _ => none

/-- Strip leading `∀`/`λ` binders and return the head constant of the body, if any. -/
partial def headConst : Expr → Option Name
  | .forallE _ _ b _ => headConst b
  | .lam _ _ b _ => headConst b
  | e => e.getAppFn.constName?

/-- Check the imported `Extracted.c` is definitionally equal to the independently elaborated
trusted copy `JanusTrusted.c`, synchronously (unlike a `theorem`, whose proof the kernel would
check on a background task). A planted or shadowed `Extracted` differs and is rejected (C1). -/
def checkIdentity (env : Environment) (c : Name) : AuditM Unit := do
  let ex := `Extracted ++ c
  let tr := `JanusTrusted ++ c
  let some _ := env.find? ex | fail s!"the imported Extracted does not define {ex}"
  let some _ := env.find? tr | fail s!"the trusted copy does not define {tr}"
  let eq ← runCore env <| Meta.MetaM.run' <|
    Meta.withNewMCtxDepth <| Meta.isDefEq (.const ex []) (.const tr [])
  unless eq do
    fail s!"the imported Extracted.{c} is not the checked one (it is not definitionally equal to the independently elaborated trusted copy)"

/-- Check a dependency constant the statement reaches: a plain def or theorem, or an inductive
type (structure) with its constructors and recursors; never an instance, a class or class-valued
def, an opaque, an axiom, a quotient primitive or anything unsafe. Returns its description. -/
def checkExternal (cx : Ctx) (c : Name) (ci : ConstantInfo) : AuditM String := do
  let mod := (cx.moduleOf? c).getD .anonymous
  let from_ := s!"declared in dependency module {mod}"
  if cx.instances.contains c then
    fail s!"the statement uses {c}, an instance {from_}; instances from dependencies are not allowed in statements (state the operation by name)"
  if ci.isUnsafe then
    fail s!"the statement uses the unsafe/partial {c}, {from_}"
  let classValued := match headConst ci.type with
    | some h => cx.classes.contains h
    | none => false
  let kind ← match ci with
    | .defnInfo _ =>
      if classValued then
        fail s!"the statement uses {c}, {from_}, whose type is a class (a disguised instance)"
      pure "def"
    | .thmInfo _ => pure "theorem"
    | .inductInfo _ =>
      if cx.classes.contains c then
        fail s!"the statement uses the class {c}, {from_}; dependency classes are not allowed in statements"
      pure "inductive"
    | .ctorInfo v =>
      if cx.classes.contains v.induct then
        fail s!"the statement uses {c}, a constructor of the class {v.induct} {from_} (a disguised instance)"
      pure "constructor"
    | .recInfo v =>
      if v.all.any cx.classes.contains then
        fail s!"the statement uses the recursor {c} of a class {from_}"
      pure "recursor"
    | .axiomInfo _ => fail s!"the statement uses {c}, an axiom {from_}, which is not a plain def or theorem"
    | .opaqueInfo _ => fail s!"the statement uses {c}, an opaque {from_}, which is not a plain def or theorem"
    | .quotInfo _ => fail s!"the statement uses {c}, a quotient primitive {from_}, which is not a plain def or theorem"
  return s!"{c} ({kind}, {mod})"

/-- All constants a non-trusted allowed def may reach that are themselves consumer-declared;
collected so the clean environment can re-add them before pretty-printing. Dependency constants
on the way are checked with `checkExternal` and collected separately (not unfolded further). -/
partial def collectLocalDefs (cx : Ctx)
    (seen : Std.HashSet Name) (ext : Std.HashMap Name String) (todo : List Name) :
    AuditM (Array Name × Std.HashMap Name String) := do
  match todo with
  | [] => return (seen.toArray, ext)
  | c :: rest =>
    if seen.contains c || ext.contains c then collectLocalDefs cx seen ext rest else
    match cx.originOf c with
    | .trusted => collectLocalDefs cx seen ext rest
    | .dependency =>
      let some ci := cx.env.find? c | fail s!"missing constant {c}"
      let d ← checkExternal cx c ci
      collectLocalDefs cx seen (ext.insert c d) rest
    | .consumer =>
      let some ci := cx.env.find? c | fail s!"missing constant {c}"
      -- Must be a plain def or theorem, safe, not opaque/axiom, not an instance.
      match ci with
      | .defnInfo _ | .thmInfo _ => pure ()
      | _ => fail s!"the statement uses {c}, which is not a plain def or theorem"
      if ci.isUnsafe then fail s!"the statement uses the unsafe/partial definition {c}"
      if cx.instances.contains c then
        fail s!"the statement uses the proof-local instance {c} (a disguised instance)"
      let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      collectLocalDefs cx (seen.insert c) ext (used.toList ++ rest)

/-- The dependency constants the clean environment needs so the statement and the proof-local
defs can be printed: the external constants themselves and, transitively, the dependency
constants in their types, in dependency order (types only; values are never needed to print). -/
partial def externalStubs (cx : Ctx) (seen : Std.HashSet Name) (acc : Array ConstantInfo)
    (todo : List Name) : AuditM (Std.HashSet Name × Array ConstantInfo) := do
  match todo with
  | [] => return (seen, acc)
  | c :: rest =>
    if seen.contains c || cx.originOf c != .dependency then externalStubs cx seen acc rest else
    let some ci := cx.env.find? c | fail s!"missing constant {c}"
    -- dependencies of the type first, then the constant itself
    let (seen, acc) ← externalStubs cx (seen.insert c) acc ci.type.getUsedConstants.toList
    externalStubs cx seen (acc.push ci) rest

/-- Add `decl` without kernel checking: used only in the print-only clean environment when
dependency constants are present as type-only stubs (soundness comes from `collectAxioms` on the
real environment and the kernel replay, never from this environment). -/
def rawAdd (env : Environment) (decl : Declaration) : AuditM Environment := do
  match env.addDeclCore (maxHeartbeats := 0) (maxRecDepth := 10000) decl none (doCheck := false) with
  | .ok env => return env
  | .error ex => fail (← (ex.toMessageData {}).toString)

/-! ## Statement faithfulness (round 2, CRITICAL-1)

The printed statement is the guarantee, so the auditor must make sure the text means what the
kernel proved. An instance argument written *inline* in the statement
(`@HMul.hMul _ _ _ ⟨fun a b => a + b⟩ x y`) is hidden by the default pretty-printer, which renders
the operation from the head symbol (`x * y`). Two independent checks close this:

* `checkInstArgs` (structural): every argument in an instance-implicit position must be a
  registered instance (applied to arguments that are, recursively, checked the same way) or a
  local instance binder of the theorem, up to unfolding reducible definitions;
* `roundTrip` (semantic): the printed statement is re-parsed and re-elaborated in the same clean
  environment and must be definitionally equal to the checked type. -/

/-- Is `c` a registered instance of the trusted environment? `Meta.isInstance` covers the
global instances of the clean environment (core, `Janus`, `Extracted`); `scoped` instances of
trusted modules (e.g. `Classical.propDecidable`) are taken from the raw extension entries of the
audited environment, keeping only those declared in a trusted module. Dependency instances are
never registered here (dependency instance lists are empty by rule: `checkExternal`). -/
def trustedInstance (cx : Ctx) (c : Name) : MetaM Bool := do
  if ← Meta.isInstance c then return true
  return cx.instances.contains c && (match cx.moduleOf? c with
    | some m => trustedModule m
    | none => false)

/-- An argument in an instance-implicit position is acceptable when, up to unfolding reducible
definitions and `whnfCore` (beta, projections of constructors), its head is a registered trusted
instance, or a local variable bound by an instance-implicit binder (a `[inst : C]` of the
theorem). The head is checked *before* unfolding, since instances are themselves reducible and
unfold to structure literals. Arguments of an accepted instance are checked by the caller's
recursive walk. -/
partial def instArgOk (cx : Ctx) (e : Expr) : MetaM Bool := do
  match e.getAppFn with
  | .const c _ =>
    if ← trustedInstance cx c then return true
    match ← Meta.withReducible (Meta.unfoldDefinition? e) with
    | some e' => instArgOk cx e'
    | none => return false
  | .fvar id =>
    match (← getLCtx).find? id with
    | some d => return !d.isLet && d.binderInfo.isInstImplicit
    | none => return false
  | .mdata _ b => instArgOk cx (mkAppN b e.getAppArgs)
  | _ =>
    let e' ← Meta.whnfCore e
    if e' == e then return false else instArgOk cx e'

/-- Is `ty` a class (possibly behind `∀` binders and reducible definitions)? A local of such a type
is a local instance whatever its binder info. -/
def isClassType (ty : Expr) : MetaM Bool := do
  try return (← Meta.isClass? ty).isSome catch _ => return false

/-- Round 5 (E5e): a term used as a value (not applied further) whose type, up to `whnf`, still
takes a parameter of class type: `@Proof.isProd x y r : [HMul …] → Prop` passed to `Exists`.
Whoever consumes it (`Exists`, `Subtype`, …) supplies that instance, so the operators inside refer
to a quantified instance, not the canonical one, although no binder appears in the statement. -/
def unappliedInstParam (e : Expr) : MetaM (Option String) := do
  let ty ← try Meta.inferType e catch _ => return none
  let bad ← try
      Meta.forallTelescopeReducing ty fun xs _ => xs.anyM fun x => do
        return (← x.fvarId!.getBinderInfo).isInstImplicit || (← isClassType (← Meta.inferType x))
    catch _ => pure false
  if bad then
    return some s!"the statement binds the instance of `{(← Meta.ppExpr e).pretty 10000}` (of type `{(← Meta.ppExpr ty).pretty 10000}`) through whatever consumes it: it is used without its instance argument, so a quantifier (`Exists`, …) chooses the instance and operators inside do not mean the canonical operation. Apply it to its instance, or name the operation"
  return none

/-- Walk `e` and fail on the first instance-implicit argument that is not a registered
instance or a local instance binder (a structure-instance literal, anonymous constructor,
lambda, `let`-bound value, proof-local def, …).

Round 5 (E5): an instance binder (instance-implicit, or of class type: a local of class type is
a local instance whatever its binder info) is accepted only in the *leading* binder telescope of
the checked term (`top`): the theorem's own `[inst : C]` parameters, or a proof-local def's
parameters. An instance-implicit binder anywhere else (`Exists fun [_ : HMul …] => r = x * y`,
a nested `∀ [_ : C], …`, an inner `fun [_ : C] => …`) makes every operator under it refer to
the *bound* instance, so `∃ [_ : HMul …], r = x * y` is true for every `r` while it prints and
round-trips as `… r = x * y`. Such binders are rejected, and so is a term that still takes an
instance parameter but is passed unapplied (`unappliedInstParam`: `Exists (@isProd x y r)`). -/
partial def checkInstArgs (cx : Ctx) (e : Expr) (top : Bool := true) : MetaM (Option String) := do
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let some m ← unappliedInstParam e then return some m
    let finfo ← Meta.getFunInfoNArgs fn args.size
    for h : i in [0:args.size] do
      let a := args[i]
      if let some pi := finfo.paramInfo[i]? then
        if pi.binderInfo.isInstImplicit then
          unless ← instArgOk cx a do
            let fnName := match fn.constName? with
              | some c => s!"{c}"
              | none => "a function"
            return some s!"the statement passes the inline instance `{(← Meta.ppExpr a).pretty 10000}` as the instance argument {i + 1} of {fnName}; instance arguments must be registered instances (an inline instance can make the printed statement say something else: write the operation with its canonical instance, or name the function)"
    -- the head is applied: its own instance parameters are the arguments checked above
    unless fn.isConst || fn.isFVar do
      if let some m ← checkInstArgs cx fn false then return some m
    for a in args do
      if let some m ← checkInstArgs cx a false then return some m
    return none
  | .lam n d b bi | .forallE n d b bi =>
    if !top && (bi.isInstImplicit || (← isClassType d)) then
      return some s!"the statement binds the instance `[{n} : {(← Meta.ppExpr d).pretty 10000}]` inside a term (an `∃`, `∀` or `fun` binder that is instance-implicit or of class type, hence a local instance); operators under it refer to that bound instance, not the canonical one (`∃ [_ : HMul …], r = x * y` holds for every r). Instance binders are allowed only as parameters of the theorem or of a proof-local definition"
    if let some m ← checkInstArgs cx d false then return some m
    Meta.withLocalDecl n bi d fun x => checkInstArgs cx (b.instantiate1 x) top
  | .letE n t v b _ =>
    if let some m ← checkInstArgs cx t false then return some m
    if let some m ← checkInstArgs cx v false then return some m
    Meta.withLetDecl n t v fun x => checkInstArgs cx (b.instantiate1 x) false
  | .mdata _ b => checkInstArgs cx b top
  | .proj _ _ s =>
    if let some m ← unappliedInstParam e then return some m
    checkInstArgs cx s false
  | .const .. | .fvar _ => if top then return none else unappliedInstParam e
  | _ => return none

/-- The shape `ppSignature` prints: the declaration name followed by a `declSig`. -/
def sigParser : Parser.Parser :=
  Parser.node `JanusAudit.sig (Parser.ident >> Parser.Command.declSig)

def parseSig (env : Environment) (input : String) : Except String Syntax :=
  let p := Parser.andthenFn Parser.whitespace sigParser.fn
  let ictx := Parser.mkInputContext input "<printed statement>"
  let s := p.run ictx { env, options := {} } (Parser.getTokenTable env) (Parser.mkParserState input)
  if !s.allErrors.isEmpty then .error (s.toErrorMsg ictx)
  else if ictx.atEnd s.pos then .ok s.stxStack.back
  else .error ((s.mkError "end of input").toErrorMsg ictx)

/-- The options the statement is printed with, and re-elaborated with (`autoImplicit` affects
only elaboration). No `pp.all`: the printed statement is the human-readable one, but it must say
what it means, so

* `pp.fullNames`: names are printed in full and resolve without `open`;
* `pp.coercions.types`: a coercion is printed with its target type, `(↑n : Int)`, since a bare
  `↑n` does not determine what it coerces to (neither for the reader nor for re-elaboration). -/
def printOptions : Options := Options.empty
  |>.setBool `pp.fullNames true
  |>.setBool `pp.coercions.types true
  |>.setBool `autoImplicit false
  |>.setBool `relaxedAutoImplicit false

/-- Heartbeat budget (in thousands, as `maxHeartbeats`) for re-elaborating the statement. -/
def roundTripHeartbeats : Nat := 2000000

/-- Re-parse and re-elaborate the printed signature `sig` in the current (clean) environment and
options, and check the result is definitionally equal to `thmType`. Returns an error message,
or `none` when the statement round-trips.

Elaboration runs with `autoImplicit` off (an unresolved name is an error, not a new variable)
and `errToSorry` off; any error message, remaining metavariable or `sorry` is a failure.
The comparison is first structural; otherwise the elaborator's `isDefEq` at **default**
transparency must succeed **and** the kernel's definitional-equality check must confirm it.
Default transparency is sound for this purpose: definitionally equal propositions are the same
proposition to the kernel (a proof of one is a proof of the other), so whatever the printed
text means when elaborated with the canonical instances is exactly what was proved. A planted
instance makes the canonical re-elaboration (e.g. the real `*`) differ from the checked term
(really `+`), and they are not definitionally equal. -/
def roundTrip (thm : Name) (thmType : Expr) (sig : String) : MetaM (Option String) := do
  let env ← getEnv
  let stx ← match parseSig env sig with
    | .ok s => pure s
    | .error e => return some s!"the printed statement does not parse back ({e}); it does not round-trip"
  let nameStx := stx[0]
  let declSig := stx[1]
  unless nameStx.getId == thm do
    return some s!"the printed statement names {nameStx.getId}, not {thm}; it does not round-trip"
  let binders := declSig[0].getArgs
  let tyStx := declSig[1][1]
  let saved ← Core.getMessageLog
  Core.resetMessageLog
  let res ← try
      -- this elaboration runs on its own heartbeat budget
      let t ← withTheReader Core.Context
          (fun c => { c with maxHeartbeats := roundTripHeartbeats * 1000 }) <| withCurrHeartbeats do
        Elab.Term.TermElabM.run' (ctx := { errToSorry := false }) do
          Elab.Term.elabBinders binders fun xs => do
            let t ← Elab.Term.elabType tyStx
            Elab.Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars (← Meta.mkForallFVars xs t)
      pure (Except.ok t)
    catch ex => pure (Except.error (← ex.toMessageData.toString))
  let log ← Core.getMessageLog
  Core.setMessageLog saved
  let t ← match res with
    | .ok t => pure t
    | .error m => return some s!"the printed statement does not elaborate back ({m}); it does not round-trip"
  if log.hasErrors then
    let msgs ← log.toList.filterMapM fun m =>
      if m.severity == .error then some <$> m.data.toString else pure none
    return some s!"the printed statement does not elaborate back ({String.intercalate "; " msgs}); it does not round-trip"
  if t.hasMVar || t.hasSorry then
    return some "the printed statement elaborates back only partially (metavariables or sorry remain); it does not round-trip"
  if t == thmType then return none
  let metaEq ← try
      withTheReader Core.Context
          (fun c => { c with maxHeartbeats := roundTripHeartbeats * 1000 }) <| withCurrHeartbeats <|
        Meta.withTransparency .default (Meta.isDefEq t thmType)
    catch _ => pure false
  -- the kernel confirms what the elaborator found (only then: it has no heartbeat budget)
  let kernelEq := metaEq && (match Kernel.isDefEq env {} t thmType with
    | .ok b => b
    | .error _ => false)
  unless kernelEq do
    return some s!"the printed statement, read back with the canonical instances, is `{(← Meta.ppExpr t).pretty 10000}`, which is not definitionally equal to the checked statement; it does not round-trip (an instance or notation hides what the statement really says)"
  return none

/-- Print the signature of `thm` (whose type is `thmType`) so that it round-trips: first with the
current options, then, if a numeral's type is what the plain print loses (`5 ≠ 7` at
`BitVec 64` reads back at `Nat`), with `pp.numericTypes` too. The first print that round-trips
is the statement; if none does, the error of the plain print. -/
def printFaithful (thm : Name) (thmType : Expr) : MetaM (Except String String) := do
  let mut firstErr := none
  for numeric in [false, true] do
    let sig ← withOptions (fun o => if numeric then o.setBool `pp.numericTypes true else o)
      (PrettyPrinter.ppSignature thm)
    let sigStr := sig.fmt.pretty 10000
    match ← roundTrip thm thmType sigStr with
    | none => return .ok sigStr
    | some m => if firstErr.isNone then firstErr := some m
  return .error (firstErr.getD "the printed statement does not round-trip")

/-- Round 4 (D1): re-parse a printed term `str` and elaborate it (as a type when `expected` is
`none`, otherwise against `expected`), returning whether the result is kernel-defeq to `target`.
Any parse/elaboration error, metavariable or `sorry` counts as "does not round-trip". -/
def termRoundTrips (str : String) (expected : Option Expr) (target : Expr) : MetaM Bool := do
  let env ← getEnv
  let stx ← match Parser.runParserCategory env `term str "<disclosed definition>" with
    | .ok s => pure s
    | .error _ => return false
  let saved ← Core.getMessageLog
  Core.resetMessageLog
  let res ← try
      let t ← withTheReader Core.Context
          (fun c => { c with maxHeartbeats := roundTripHeartbeats * 1000 }) <| withCurrHeartbeats do
        Elab.Term.TermElabM.run' (ctx := { errToSorry := false }) do
          let t ← match expected with
            | none => Elab.Term.elabType stx
            | some ty => Elab.Term.elabTermEnsuringType stx (some ty)
          Elab.Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars t
      pure (some t)
    catch _ => pure none
  let log ← Core.getMessageLog
  Core.setMessageLog saved
  let some t := res | return false
  if log.hasErrors || t.hasMVar || t.hasSorry then return false
  if t == target then return true
  let metaEq ← try
      withTheReader Core.Context
          (fun c => { c with maxHeartbeats := roundTripHeartbeats * 1000 }) <| withCurrHeartbeats <|
        Meta.withTransparency .default (Meta.isDefEq t target)
    catch _ => pure false
  return metaEq && (match Kernel.isDefEq env {} t target with
    | .ok b => b
    | .error _ => false)

/-- Round 4 (D1): disclose a proof-local def or theorem so the disclosure means what it says.
The plain print is used if its type (and, for a def, its value) re-elaborate to the real ones;
otherwise the same with `pp.numericTypes`/`pp.funBinderTypes` (a numeral such as `256 ≠ 0` at
`BitVec 8` reads back at `Nat` without them). If neither round-trips (compiled recursion,
`match` auxiliaries, universe polymorphism), the annotated print is disclosed and tagged
`[not round-tripped]`, so the report never presents an unconfirmed reading as confirmed. -/
def discloseDef (ci : ConstantInfo) : MetaM String := do
  let annotate := fun (o : Options) => o.setBool `pp.numericTypes true |>.setBool `pp.funBinderTypes true
  let mut lastTy := ""
  let mut lastVal := ""
  for ann in [false, true] do
    let withO {α} (x : MetaM α) : MetaM α := withOptions (fun o => if ann then annotate o else o) x
    let tyStr := (← withO (Meta.ppExpr ci.type)).pretty 10000
    let isThm := ci matches .thmInfo _
    let valStr ← if isThm then pure "<proof>" else match ci.value? with
      | some v => pure ((← withO (Meta.ppExpr v)).pretty 10000)
      | none => pure "<opaque>"
    lastTy := tyStr; lastVal := valStr
    if !ci.levelParams.isEmpty then continue
    unless ← termRoundTrips tyStr none ci.type do continue
    if isThm then return s!"{ci.name} : {tyStr} := {valStr}"
    match ci.value? with
    | some v =>
      if ← termRoundTrips valStr (some ci.type) v then
        return s!"{ci.name} : {tyStr} := {valStr}"
    | none => pure ()
  return s!"{ci.name} : {lastTy} := {lastVal}  [not round-tripped: read with care]"

/-- Build the clean environment: import only `Janus` and `Extracted`, with initializers so pp
works, then add type-only stubs for the dependency constants the statement reaches, re-add the
allowed proof-local defs and an axiom with the theorem's type. Reject a proof-local def whose
type's head is a class (a disguised instance, A1). No proof or dependency module is imported, so
none of their initializers, notations, unexpanders or delaborators exist here. -/
unsafe def cleanEnvAndPrint (cx : Ctx) (thm : Name) (thmType : Expr) (localDefs : Array ConstantInfo)
    (stubs : Array ConstantInfo) : AuditM (String × String × Array String) := do
  enableInitializersExecution
  let env ← importModules (loadExts := true)
    #[{ module := `Extracted }, { module := `Janus }] {}
  let mut env := env
  -- Dependency constants: type-only, unchecked (their types may need dependency definitions'
  -- bodies to check, which a stub does not carry).
  for ci in stubs do
    if (env.find? ci.name).isNone then
      env ← rawAdd env (.axiomDecl { name := ci.name, levelParams := ci.levelParams, type := ci.type, isUnsafe := false })
  let add := fun (env : Environment) (decl : Declaration) =>
    if stubs.isEmpty then kernelAdd env decl else rawAdd env decl
  -- Re-add proof-local defs in dependency order.
  let mut pending := localDefs
  let mut progress := true
  while !pending.isEmpty && progress do
    progress := false
    let mut next := #[]
    for ci in pending do
      let deps := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      let ready := deps.all fun d => (env.find? d).isSome || !localDefs.any (·.name == d)
      if ready && (env.find? ci.name).isNone then
        -- reject class-valued (instance-like) proof-local defs
        if let some headTy := headConst ci.type then
          if isClass env headTy || cx.classes.contains headTy then
            fail s!"the statement uses the proof-local {ci.name}, whose type is the class {headTy} (a disguised instance)"
        let some decl := ciToDecl ci
          | fail s!"the statement uses the proof-local {ci.name}, which is not a def or theorem"
        env ← add env decl
        progress := true
      else if (env.find? ci.name).isNone then
        next := next.push ci
    pending := next
  if !pending.isEmpty then
    fail "cannot order the proof-local definitions of the statement"
  -- Add the theorem's type as an axiom (printing only; soundness is from collectAxioms/replay).
  env ← add env (.axiomDecl { name := thm, levelParams := [], type := thmType, isUnsafe := false })
  -- Pretty-print the signature and each allowed proof-local def in the clean environment.
  -- The same options for printing and for the round-trip re-elaboration (`autoImplicit` only
  -- affects elaboration). No `pp.all`: the printed statement is the human-readable one.
  let opts := printOptions
  let printAll : MetaM (String × String × Array String) := do
    -- (b) instance-implicit arguments must be registered instances or local instance binders
    if let some m ← checkInstArgs cx thmType then throwError m
    -- (a) the printed statement must elaborate back to the checked type
    let sigStr ← match ← printFaithful thm thmType with
      | .ok s => pure s
      | .error m => throwError m
    -- (c) the statement with every implicit and instance argument shown, for human inspection
    let explicit ← withOptions (fun o => o.setBool `pp.explicit true) (PrettyPrinter.ppSignature thm)
    let mut defs := #[]
    for ci in localDefs do
      -- (b'), round 3 R1: the disclosed body is the reader's definition of the constant the
      -- statement names, so it is part of the guarantee. Apply the same instance check to the
      -- def's type and value: an inline non-canonical instance in a body
      -- (`fun a b => @HMul.hMul _ _ _ ⟨fun a b => a + b⟩ a b`) is printed `fun a b => a * b` by
      -- the default printer, so without this check a disclosed body reads as `*` while it adds.
      if let some m ← checkInstArgs cx ci.type then
        throwError s!"the proof-local definition {ci.name} used in the statement {m}"
      if let some v := ci.value? then
        if let some m ← checkInstArgs cx v then
          throwError s!"the proof-local definition {ci.name} used in the statement {m}"
      -- round 4 D1: the disclosure itself must round-trip (numerals, binder types)
      defs := defs.push (← discloseDef ci)
    return (sigStr, explicit.fmt.pretty 10000, defs)
  match ← (Core.CoreM.toIO' (Meta.MetaM.run' printAll) { mkCoreCtx with options := opts } { env }).toBaseIO with
  | .ok a => return a
  | .error e => fail e.toString

unsafe def runImpl (thm proofMod marker trusted : String) (depRoots : Array String) : IO Unit := do
  let result ← (show AuditM Record from do
    let thmN := thm.toName
    let proofModN := proofMod.toName
    let envA ← importModules (loadExts := false)
      #[{ module := `Extracted }, { module := trusted.toName }, { module := proofModN }] {}
    -- 1. kind and module
    let some ci := envA.find? thmN | fail s!"the proof does not define {thm}"
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | _ => "other"
    let modName ← match envA.getModuleIdxFor? thmN with
      | some i => pure (envA.header.moduleNames[i.toNat]!)
      | none => fail s!"{thm} is not declared in an imported module"
    -- the selected declaration must be a theorem declared in the proof module; check this
    -- before anything else so the diagnostic names the real problem
    unless kind == "theorem" do
      fail s!"{thm} is a {kind}, not a theorem"
    unless modName == proofModN do
      fail s!"{thm} is declared in module {modName}, not in the proof module {proofModN}"
    -- 2. axioms (allow-list enforced in Go)
    let axs ← runCore envA (collectAxioms thmN)
    -- 3. Extracted identity vs. the trusted copy
    checkIdentity envA `program
    checkIdentity envA `entry
    let cx := mkCtx envA depRoots
    -- 4. no non-trusted (consumer/proof/dependency) module declares a name with an `Extracted` component
    -- (A7, A9, and the consumer analogue of shadowing Extracted from a shared module)
    for (n, idx) in envA.const2ModIdx.toList do
      if !trustedModule envA.header.moduleNames[idx.toNat]! && n.anyS (· == "Extracted") then
        fail s!"a non-trusted module declares {n}, whose name shadows the Extracted namespace"
    -- 5. type constants: must mention Extracted; every constant is trusted or a non-trusted
    -- plain def collected for the clean-environment print
    let used := ci.type.getUsedConstants
    let mut mentionsExtracted := false
    let mut localSeed := #[]
    for c in used do
      if c == `Extracted.program || c == `Extracted.entry then
        mentionsExtracted := true
      match envA.getModuleIdxFor? c with
      | some idx =>
        if !trustedModule envA.header.moduleNames[idx.toNat]! then
          localSeed := localSeed.push c
      | none =>
        fail s!"the statement depends on {c}, which is in no imported module"
    unless mentionsExtracted do
      fail "the statement does not mention Extracted.program or Extracted.entry, so it says nothing about the extracted code"
    -- close over the consumer defs reachable from the statement; check the dependency
    -- constants on the way
    let (localNames, external) ← collectLocalDefs cx {} {} localSeed.toList
    let localDefs := localNames.filterMap envA.find?
    let externalNames := external.toArray.map (·.1) |>.qsort Name.lt
    let (_, stubs) ← externalStubs cx {} #[] externalNames.toList
    -- 6. clean-environment pretty-print
    let (statement, statementExplicit, defs) ← cleanEnvAndPrint cx thmN ci.type localDefs stubs
    return Record.mk thm kind modName.toString (axs.map (·.toString)) statement statementExplicit defs
      (envA.header.moduleNames.map (·.toString)) (externalNames.filterMap external.get?)
      (importGraph envA)
  ).run
  match result with
  | .ok rec => IO.println (marker ++ (toJson rec).compress)
  | .error f => IO.println (marker ++ "ERROR " ++ f.msg)
  (← IO.getStdout).flush

/-- Audit entry point. Run via a generated, trusted `Audit.lean` that does
`#eval JanusAudit.run "<thm>" "<proof module>" "<marker>" "JanusTrusted" #[<dependency roots>]`
and imports only this
module (never the proof), so the proof's `initialize`/macros never run. `run` itself imports the
proof's compiled module with `importModules (loadExts := false)`, which does not run its
initializers. The `@[implemented_by]` wrapper lets the trusted `#eval` call the `unsafe` logic. -/
@[implemented_by runImpl]
opaque run (thm proofMod marker trusted : String) (depRoots : Array String) : IO Unit

end JanusAudit
