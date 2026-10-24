import Lean

/-!
# `janus-audit`: the trusted theorem and statement auditor

`janus verify` runs this logic as the compiled executable `janus-audit` (root
`Janus.Tools.AuditMain`, built with the framework and pinned like its modules); consumer-package
verification runs it through a trusted `#eval` script (`run`). Either way **no code from the
proof ever runs** (A3, A6 in `docs/AUDIT.md`): it imports the proof's compiled
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

This module imports only `Lean` (it reads `Janus` and `Extracted` as data, through
`importModules`), so the executable links no framework code and its imports are mapped once:
an environment imported by this process shares no file with the process's own image.
-/

open Lean

namespace JanusAudit

/-- Is `mod` a module whose declarations are trusted to appear in a statement's type? `extra` are
further trusted module roots: for the ASL corollary (`runASL`), the pinned JanusASL build
(`JanusASL`, `ArmASL`, `Sail`) and the trusted coverage module `JanusASLWords`. -/
def trustedModule (mod : Name) (extra : Array Name := #[]) : Bool :=
  let root := mod.getRoot
  root == `Init || root == `Std || root == `Lean || root == `Janus
    || root == `Extracted || root == `JanusTrusted || extra.contains root

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
  /-- Round 7 (J1): `<name> : <type> := <value>` for each dependency def the statement reaches,
  printed in the clean environment (dependency notation does not apply). Not round-tripped. -/
  externalDefinitions : Array String
  /-- Round 7 (K1): operations whose standard Lean meaning often reads unexpectedly (truncating
  `Nat` subtraction, `x / 0 = 0`, wrapping `^`, `xs[i]!`, `Int.toNat`), with the subterm. These
  are not errors: the statement means exactly what Lean says. -/
  notes : Array String
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
  let names := env.header.moduleNames
  for h : i in [0:names.size] do
    let m := names[i]
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
  /-- `env.header.moduleNames`, computed once (`EnvironmentHeader.moduleNames` rebuilds the array
  of every module name on each call). -/
  modNames  : Array Name
  depRoots  : Std.HashSet Name
  instances : Std.HashSet Name
  classes   : Std.HashSet Name
  /-- Extra trusted module roots (`trustedModule`); empty except for the ASL corollary. -/
  extra     : Array Name := #[]

def Ctx.trusted (cx : Ctx) (mod : Name) : Bool := trustedModule mod cx.extra

def Ctx.originOfModule (cx : Ctx) (mod : Name) : Origin :=
  if cx.trusted mod then .trusted
  else if cx.depRoots.contains mod.getRoot then .dependency
  else .consumer

/-- The module that declares `c`, if any. -/
def Ctx.moduleOf? (cx : Ctx) (c : Name) : Option Name :=
  (cx.env.getModuleIdxFor? c).map fun idx => cx.modNames[idx.toNat]!

def Ctx.originOf (cx : Ctx) (c : Name) : Origin :=
  match cx.moduleOf? c with
  | some m => cx.originOfModule m
  | none => .consumer

/-- Collect instance and class names from every imported module's extension entries. An
`attribute [instance] foo` in any module counts, as do scoped and local-to-namespace ones. -/
def mkCtx (env : Environment) (depRoots : Array String) (extra : Array Name := #[]) : Ctx := Id.run do
  let mut instances : Std.HashSet Name := {}
  let mut classes : Std.HashSet Name := {}
  let modNames := env.header.moduleNames
  for i in [0:modNames.size] do
    for e in Meta.instanceExtension.ext.getModuleEntries env i do
      let ie := match e with
        | .global ie => ie
        | .scoped _ ie => ie
      if let some n := ie.globalName? then
        instances := instances.insert n
    for ce in classExtension.getModuleEntries env i do
      classes := classes.insert ce.name
  return { env, modNames, instances, classes, extra,
           depRoots := depRoots.foldl (fun s r => s.insert r.toName) {} }

/-- Round 6 (F1): characters allowed in a name component of a non-trusted constant that the
report shows: ASCII identifier characters and the subscript digits/letters Lean accepts. Lean
also accepts Greek, Coptic, letterlike and mathematical-alphanumeric letters, many of which look
exactly like Latin ones (`Ε`, U+0395, prints like `E`), so a proof-local `Εxtracted.program` or
`Janus.GoABI.Εnsures` would print like the trusted constant it imitates. -/
def plainNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' ||
    (0x2080 ≤ c.val && c.val ≤ 0x209c) || (0x1d62 ≤ c.val && c.val ≤ 0x1d6a) || c.val == 0x2c7c

/-- Is every string component of `n` a plain identifier (`plainNameChar`)? Numeric components
(compiler auxiliaries) are fine. -/
def plainName (n : Name) : Bool :=
  n.components.all fun
    | .str _ s => !s.isEmpty && s.all plainNameChar
    | _ => true

/-- Round 6 (F1): the Latin letter a confusable non-ASCII identifier letter looks like, if any
(Greek capitals and small letters, letterlike and mathematical alphanumerics are folded by
their usual look); used only to detect names that imitate `Extracted`/`JanusTrusted`. -/
def latinLookalike (c : Char) : Char :=
  if c.val < 0x80 then c else
  match c.val with
  | 0x391 => 'A' | 0x392 => 'B' | 0x395 => 'E' | 0x396 => 'Z' | 0x397 => 'H' | 0x399 => 'I'
  | 0x39a => 'K' | 0x39c => 'M' | 0x39d => 'N' | 0x39f => 'O' | 0x3a1 => 'P' | 0x3a4 => 'T'
  | 0x3a5 => 'Y' | 0x3a7 => 'X' | 0x3b1 => 'a' | 0x3b9 => 'i' | 0x3ba => 'k' | 0x3bd => 'v'
  | 0x3bf => 'o' | 0x3c1 => 'p' | 0x3c4 => 't' | 0x3c5 => 'u' | 0x3c7 => 'x' | 0x3f2 => 'c'
  | 0x3f3 => 'j' | 0x2107 => 'E' | 0x210e => 'h' | 0x2113 => 'l' | 0x212e => 'e' | 0x212f => 'e'
  | 0x2130 => 'E' | 0x2134 => 'o' | 0x2139 => 'i'
  | v =>
    -- Mathematical alphanumeric symbols: 52-letter alphabets (A–Z, a–z) from U+1D400.
    if 0x1d400 ≤ v && v < 0x1d6a4 then
      let k := (v.toNat - 0x1d400) % 52
      if k < 26 then Char.ofNat ('A'.toNat + k) else Char.ofNat ('a'.toNat + (k - 26))
    else c

/-- Does some component of `n`, split at non-identifier characters and with lookalike letters
folded to Latin, read `Extracted` or `JanusTrusted`? (`«Extracted.program»` is one component,
`Εxtracted` has a Greek capital epsilon; both are caught.) -/
def imitatesExtracted (n : Name) : Bool :=
  n.components.any fun
    | .str _ s =>
      let folded := String.ofList (s.toList.map latinLookalike)
      let pieces := (folded.toList.splitBy fun a b => (a.isAlphanum || a == '_') == (b.isAlphanum || b == '_')).map String.ofList
      pieces.any fun p => p == "Extracted" || p == "JanusTrusted"
    | _ => false

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
    | some m => cx.trusted m
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

/-- Round 6 (F2): the number of values of a fixed-width numeric type, i.e. the bound below which
a numeral of that type means what it reads (for the signed `IntN`, the first literal that wraps
to a negative value). `none` for types without wrapping or of unknown width. -/
def numeralBound (ty : Expr) : MetaM (Option Nat) := do
  if ty.hasLooseBVars then return none
  let ty ← try Meta.whnfR ty catch _ => return none
  let lit? (e : Expr) : MetaM (Option Nat) := do
    if e.hasLooseBVars then return none
    match (← try Meta.whnf e catch _ => pure e) with
    | .lit (.natVal n) => return some n
    | e' => match e'.rawNatLit? with
      | some n => return some n
      | none => (Meta.evalNat e').run
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some ``BitVec, #[w] => return (← lit? w).bind fun w => if w ≤ 4096 then some (2 ^ w) else none
  | some ``Fin, #[n] => lit? n
  | some ``UInt8, _ => return some (2 ^ 8)
  | some ``UInt16, _ => return some (2 ^ 16)
  | some ``UInt32, _ => return some (2 ^ 32)
  | some ``UInt64, _ => return some (2 ^ 64)
  | some ``USize, _ => return some (2 ^ 32)  -- the portable bound
  | some ``Int8, _ => return some (2 ^ 7)
  | some ``Int16, _ => return some (2 ^ 15)
  | some ``Int32, _ => return some (2 ^ 31)
  | some ``Int64, _ => return some (2 ^ 63)
  | some ``ISize, _ => return some (2 ^ 31)
  | _, _ => return none

/-- Round 6 (F2): reject a numeral `(n : T)` whose literal is out of range for a wrapping type
`T`. `OfNat` on `BitVec 64` reduces `18446744073709551616` to `0`, so `y ≠ 18446744073709551616`
reads as a vacuous hypothesis while it is `y ≠ 0`; the text round-trips (Lean reads it the same
way), so only the literal itself shows the problem. Write the value in range. -/
def checkNumerals (e : Expr) : MetaM (Option String) := do
  let bad ← IO.mkRef (none : Option String)
  Meta.forEachExpr e fun sub => do
    if (← bad.get).isSome then return
    if sub.isAppOfArity ``OfNat.ofNat 3 then
      let ty := sub.getArg! 0
      if let some n := (sub.getArg! 1).rawNatLit? then
        if let some b ← numeralBound ty then
          if n ≥ b then
            let tyS := (← try Meta.ppExpr ty catch _ => pure "?").pretty 10000
            bad.set (some s!"writes the out-of-range numeral {n} at type {tyS}, whose values are below {b}: the literal wraps (to {n % b} for an unsigned type) and does not mean what it reads (round 6 F2). Write the value in range")
  bad.get

/-- Round 7 (H1): characters a bound variable's name may contain. Lean identifier letters
(ASCII, Greek, Coptic, letterlike, subscripts) as `isLetterLike` defines them, digits and
`_ ' ! ?`. A `«…»` binder may otherwise contain zero-width spaces, combining marks or
lookalike letters from scripts Lean does not accept as identifiers (Cyrillic `х`). -/
def binderChar (c : Char) : Bool :=
  plainNameChar c || Lean.isLetterLike c

/-- Round 7 (H1): the bound-variable names of `e` (`∀`, `fun`, `let` binders), with macro
scopes erased, in traversal order. -/
partial def binderNames (e : Expr) (acc : Array Name := #[]) : Array Name :=
  match e with
  | .forallE n d b _ | .lam n d b _ => binderNames b (binderNames d (acc.push n.eraseMacroScopes))
  | .letE n t v b _ => binderNames b (binderNames v (binderNames t (acc.push n.eraseMacroScopes)))
  | .app f a => binderNames a (binderNames f acc)
  | .mdata _ b => binderNames b acc
  | .proj _ _ b => binderNames b acc
  | _ => acc

/-- Round 7 (H1): reject bound variables that cannot be told apart. `∀ ο, ο = o` with a Greek
omicron reads as the triviality `∀ o, o = o` while it says every value equals the parameter
`o` (a false, hence vacuous, hypothesis). Two distinct binder names of one term that read the
same once lookalike letters are folded to Latin (`latinLookalike`) are rejected, and so is a
binder name with characters other than Lean identifier letters, digits and `_ ' ! ?`. -/
def checkBinderNames (e : Expr) : Option String := Id.run do
  let names := binderNames e
  let mut seen : Std.HashMap String String := {}
  for n in names do
    if n.isAnonymous then continue
    let str := n.toString (escape := false)
    if !n.components.all (fun | .str _ c => c.all binderChar | _ => true) then
      return some s!"binds a variable whose name has characters other than identifier letters, digits and _ ' ! ? (zero-width, combining or lookalike characters): {String.quote str}; rename it (round 7 H1)"
    let folded := String.ofList (str.toList.map latinLookalike)
    match seen.get? folded with
    | some other =>
      if other != str then
        return some s!"binds two variables whose names look alike, {String.quote other} and {String.quote str} (they read the same once lookalike letters are folded), so the printed statement cannot be read reliably; rename one (round 7 H1)"
    | none => seen := seen.insert folded str
  return none

/-- Round 7 (K1): is `ty` (up to reducible unfolding) one of `Nat`, `Int`, or a wrapping
fixed-width type (`numeralBound`)? Returns a short name for messages. -/
def divType? (ty : Expr) : MetaM (Option String) := do
  let ty ← try Meta.whnfR ty catch _ => return none
  if ty.isConstOf ``Nat then return some "Nat"
  if ty.isConstOf ``Int then return some "Int"
  if (← numeralBound ty).isSome then return some (← Meta.ppExpr ty).pretty
  return none

/-- Round 7 (K1): is `e` syntactically nonzero (so `· / e` cannot divide by 0): a numeral
other than zero, or a power or product of such? -/
partial def nonzeroLit (e : Expr) : Bool :=
  if e.isAppOfArity ``HPow.hPow 6 then nonzeroLit (e.getArg! 4) else
  if e.isAppOfArity ``HMul.hMul 6 then nonzeroLit (e.getArg! 4) && nonzeroLit (e.getArg! 5) else
  match e.nat? with
  | some n => n != 0
  | none => match e.rawNatLit? with
    | some n => n != 0
    | none => (e.isAppOfArity ``OfNat.ofNat 3 && match (e.getArg! 1).rawNatLit? with
        | some n => n != 0
        | none => false)

/-- Round 7 (K1): notes on operations in `e` whose standard Lean meaning often surprises a
reader. Each note names the operation and shows the subterm. They are warnings only. -/
def hazardNotes (e : Expr) : MetaM (Array String) := do
  let acc ← IO.mkRef (#[] : Array String)
  let add (msg : String) (sub : Expr) : MetaM Unit := do
    if sub.hasLooseBVars then
      acc.modify (·.push msg)
    else
      let t := (← try Meta.ppExpr sub catch _ => pure "?").pretty 10000
      acc.modify (·.push s!"{msg}: `{t}`")
  Meta.forEachExpr e fun sub => do
    if sub.isAppOfArity ``HSub.hSub 6 then
      if (← try Meta.whnfR (sub.getArg! 0) catch _ => pure (sub.getArg! 0)).isConstOf ``Nat then
        add "Nat subtraction truncates at 0 (`a - b = 0` whenever `a ≤ b`)" sub
    else if sub.isAppOfArity ``Nat.sub 2 || sub.isAppOfArity ``Nat.pred 1 then
      add "Nat subtraction truncates at 0 (`a - b = 0` whenever `a ≤ b`)" sub
    else if sub.isAppOfArity ``HDiv.hDiv 6 || sub.isAppOfArity ``HMod.hMod 6 then
      if !nonzeroLit (sub.getArg! 5) then
        if let some t ← divType? (sub.getArg! 0) then
          add s!"division by zero is total at {t} (`a / 0 = 0`, `a % 0 = a`)" sub
    else if sub.isAppOfArity ``HPow.hPow 6 then
      if (← numeralBound (sub.getArg! 0)).isSome then
        let tyS := (← try Meta.ppExpr (sub.getArg! 0) catch _ => pure "?").pretty 10000
        add s!"`^` wraps at {tyS} (for example `(2 : BitVec 64) ^ 64 = 0`)" sub
    else if sub.isAppOfArity ``GetElem?.getElem! 8 then
      add "`xs[i]!` is `default` when `i` is out of bounds" sub
    else if sub.isAppOfArity ``Int.toNat 1 then
      add "`Int.toNat` maps every negative integer to 0" sub
  let notes ← acc.get
  -- dedupe, keep order
  let mut out := #[]
  for n in notes do
    unless out.contains n do out := out.push n
  return out

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

/-- The clean environment's imports: only `Extracted` and `Janus`, never the proof. -/
def cleanImports : Array Import := #[{ module := `Extracted }, { module := `Janus }]

/-- Read the module data of the clean environment (`cleanImports`) and of the audited one
(`auditImports`) from disk, returning the two import states. This only reads `.olean` files (as
`importModules` does); no environment is built and nothing runs.

Re-reading a module that this process has already mapped is slow (Lean copies and relocates the
whole file instead of mapping it), and the two environments share every framework and core
module, so the audited state is grown from the clean one: each shared module is read once. That
is exactly a fresh import of `auditImports` when the clean closure is part of the audited
closure, i.e. when `Extracted` imports `Janus` (which the extractor always writes);
`auditEnv` checks this on the result and otherwise imports the audited environment afresh. -/
def readImports (auditImports : Array Import) : IO (ImportState × ImportState) := withImporting do
  let (_, sClean) ← (importModulesCore cleanImports).run
  let (_, sAudit) ← (importModulesCore auditImports).run sClean
  return (sClean, sAudit)

/-- The audited environment (`importModules (loadExts := false) auditImports {}`) and the clean
import state, reading every module once (`readImports`). The shared read is used only if the
imported `Extracted` directly imports `Janus`, so the clean closure adds no module to the audited
one and the result is the environment a fresh import builds (same modules, same order: both are
the same depth-first traversal); otherwise the audited environment is imported separately. -/
def auditEnv (auditImports : Array Import) : IO (Environment × ImportState) := do
  let (sClean, sAudit) ← readImports auditImports
  let env ← withImporting <| finalizeImport sAudit auditImports {} (leakEnv := false) (loadExts := false)
  let extractedImportsJanus := match env.getModuleIdx? `Extracted with
    | some i => match env.header.moduleData[i.toNat]? with
      | some d => d.imports.any (·.module == `Janus)
      | none => false
    | none => false
  if extractedImportsJanus then
    return (env, sClean)
  return (← importModules (loadExts := false) auditImports {}, sClean)

/-- Build the clean environment: import only `Janus` and `Extracted`, with initializers so pp
works, then add type-only stubs for the dependency constants the statement reaches, re-add the
allowed proof-local defs and an axiom with the theorem's type. Reject a proof-local def whose
type's head is a class (a disguised instance, A1). No proof or dependency module is imported, so
none of their initializers, notations, unexpanders or delaborators exist here. -/
unsafe def cleanEnvAndPrint (cx : Ctx) (thm : Name) (thmType : Expr) (localDefs : Array ConstantInfo)
    (stubs : Array ConstantInfo) (extDefs : Array ConstantInfo) (cleanState : ImportState)
    (clean : Array Import := cleanImports) :
    AuditM (String × String × Array String × Array String × Array String) := do
  enableInitializersExecution
  -- `importModules (loadExts := true) cleanImports {}`, with the module data already read
  -- (`readImports`): the same `finalizeImport` over the same import state.
  let env ← (withImporting <| finalizeImport cleanState clean {} (leakEnv := false) (loadExts := true) : IO Environment)
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
  let printAll : MetaM (String × String × Array String × Array String × Array String) := do
    -- (b) instance-implicit arguments must be registered instances or local instance binders
    if let some m ← checkInstArgs cx thmType then throwError m
    if let some m ← checkNumerals thmType then throwError s!"the statement {m}"
    if let some m := checkBinderNames thmType then throwError s!"the statement {m}"
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
      for t in [ci.type] ++ ci.value?.toList do
        if let some m ← checkNumerals t then
          throwError s!"the proof-local definition {ci.name} used in the statement {m}"
        if let some m := checkBinderNames t then
          throwError s!"the proof-local definition {ci.name} used in the statement {m}"
      -- round 4 D1: the disclosure itself must round-trip (numerals, binder types)
      defs := defs.push (← discloseDef ci)
    -- round 7 J1: dependency definitions are disclosed with their bodies too (printed here, in
    -- the clean environment, so dependency notation does not apply), since their names and
    -- docstrings need not say what they mean
    let mut extOut := #[]
    for ci in extDefs do
      let annotate := fun (o : Options) => o.setBool `pp.numericTypes true |>.setBool `pp.funBinderTypes true
      let tyStr := (← withOptions annotate (Meta.ppExpr ci.type)).pretty 10000
      let valStr ← match ci.value? with
        | some v => pure ((← withOptions annotate (Meta.ppExpr v)).pretty 10000)
        | none => pure "<no value>"
      extOut := extOut.push s!"{ci.name} : {tyStr} := {valStr}"
    -- round 7 K1: notes on surprising standard operations (statement and disclosed bodies)
    let mut notes ← hazardNotes thmType
    for ci in localDefs ++ extDefs do
      for t in [ci.type] ++ ci.value?.toList do
        for n in ← hazardNotes t do
          let n := s!"in {ci.name}: {n}"
          unless notes.contains n do notes := notes.push n
    return (sigStr, explicit.fmt.pretty 10000, defs, extOut, notes)
  match ← (Core.CoreM.toIO' (Meta.MetaM.run' printAll) { mkCoreCtx with options := opts } { env }).toBaseIO with
  | .ok a => return a
  | .error e => fail e.toString

unsafe def runImpl (thm proofMod marker trusted : String) (depRoots : Array String) : IO Unit := do
  let result ← (show AuditM Record from do
    let thmN := thm.toName
    let proofModN := proofMod.toName
    let auditImports : Array Import :=
      #[{ module := `Extracted }, { module := trusted.toName }, { module := proofModN }]
    let (envA, cleanState) ← (auditEnv auditImports : IO _)
    -- 1. kind and module
    let some ci := envA.find? thmN | fail s!"the proof does not define {thm}"
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | _ => "other"
    -- the module names, computed once (`moduleNames` rebuilds the array on every call)
    let modNames := envA.header.moduleNames
    let modName ← match envA.getModuleIdxFor? thmN with
      | some i => pure (modNames[i.toNat]!)
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
      if !trustedModule modNames[idx.toNat]! && (n.anyS (· == "Extracted") || imitatesExtracted n) then
        fail s!"a non-trusted module declares {n}, whose name shadows the Extracted namespace (round 6 F1: lookalike letters and «…» components count)"
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
        if !trustedModule modNames[idx.toNat]! then
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
    -- round 6 F1: every non-trusted name the report shows must be a plain identifier, so it
    -- cannot print like a trusted constant (`Janus.GoABI.Εnsures`, Greek capital epsilon)
    for n in localNames ++ externalNames do
      unless plainName n do
        fail s!"the statement uses {n}, whose name has characters other than ASCII letters, digits, _ ' ! ? and subscripts (a name with lookalike letters prints like a different, trusted constant); rename it"
    let (_, stubs) ← externalStubs cx {} #[] externalNames.toList
    -- 6. clean-environment pretty-print
    let extDefs := externalNames.filterMap fun n => match envA.find? n with
      | some ci@(.defnInfo _) => some ci
      | _ => none
    let (statement, statementExplicit, defs, extOut, notes) ←
      cleanEnvAndPrint cx thmN ci.type localDefs stubs extDefs cleanState
    return { name := thm, kind, module := modName.toString, axioms := axs.map (·.toString),
             statement, statementExplicit, definitions := defs,
             modules := modNames.map (·.toString),
             external := externalNames.filterMap external.get?, externalDefinitions := extOut,
             notes, imports := importGraph envA }
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

/-! ## The ASL corollary (`janus verify --asl`, docs/ASL.md#janus-verify---asl)

`janus verify --asl` derives, from the user's verified `Ensures` theorem, the same statement
about Arm's ASL (JanusASL's `Ensures.toASL`). The derivation is `aslCorollary`: it is used both by
the `janus_asl_corollary` command that builds the corollary (JanusASL/JanusASL/Verify.lean) and by
`runASL` here, which audits the result without running any proof code. The JanusASL constants are
named, not imported: the framework does not depend on JanusASL. -/

/-- The JanusASL transfer theorem and the three facts `covered p = true` gives about `p`. -/
def aslToASL : Name := `JanusASL.Proofs.Ensures.toASL
def aslCoveredWords : Name := `JanusASL.Verify.covered_words
def aslCoveredCode : Name := `JanusASL.Verify.covered_code
def aslCoveredStubs : Name := `JanusASL.Verify.covered_stubs

/-- Module roots of the trusted JanusASL build and of the trusted coverage module. -/
def aslTrustedRoots : Array Name := #[`JanusASL, `ArmASL, `Sail, `JanusASLWords]

/-- Open the `∀` binders of `ty`, unfolding the head definition of the body (a consumer's
`Computes p e spec`, `EnsuresResults`, …) until it is `Janus.GoABI.Ensures …`, and call `k` with
all the binders and the body. -/
partial def ensuresTelescope {α} (ty : Expr) (k : Array Expr → Expr → MetaM α) (acc : Array Expr := #[])
    (fuel : Nat := 64) : MetaM α :=
  Meta.forallTelescope ty fun xs body => do
    let acc := acc ++ xs
    if body.isAppOfArity `Janus.GoABI.Ensures 5 || fuel == 0 then k acc body else
    match ← Meta.unfoldDefinition? body with
    | some b => ensuresTelescope b.headBeta k acc (fuel - 1)
    | none => k acc body

/-- **The ASL corollary of `thm`** (its type and proof): for a theorem
`∀ xs, Janus.GoABI.Ensures Extracted.program entry args pre post` (after unfolding the definitions
at the head of its conclusion, `ensuresTelescope`),
`fun xs => Ensures.toASL (thm xs) (covered_words _ words) (covered_code _ words) (covered_stubs _ words)`,
where `words : JanusASL.Classify.covered Extracted.program = true`. The type is the inferred type of
that term, beta-reduced. The program must be the constant `Extracted.program` itself. -/
def aslCorollary (thm words : Name) : MetaM (Expr × Expr) := do
  let some ci := (← getEnv).find? thm | throwError "the proof does not define {thm}"
  unless ci.levelParams.isEmpty do
    throwError "{thm} is universe polymorphic; --asl transfers monomorphic Ensures theorems only"
  ensuresTelescope ci.type fun xs body => do
    unless body.isAppOfArity `Janus.GoABI.Ensures 5 do
      throwError "the conclusion of {thm} (after its ∀ binders) is not `Janus.GoABI.Ensures …` (arm64), also after unfolding its head definitions; --asl transfers arm64 Ensures specifications only"
    let args := body.getAppArgs
    let p := args[0]!
    unless p == .const `Extracted.program [] do
      throwError "{thm} is an Ensures statement about {← Meta.ppExpr p}, not about Extracted.program itself"
    let hc := Expr.const words []
    let t := mkAppN (.const aslToASL []) (args ++ #[mkAppN (.const thm []) xs,
      mkApp2 (.const aslCoveredWords []) p hc, mkApp2 (.const aslCoveredCode []) p hc,
      mkApp2 (.const aslCoveredStubs []) p hc])
    let ty ← Meta.inferType t
    let ty ← instantiateMVars (← Meta.mkForallFVars xs ty)
    let ty ← Core.betaReduce ty
    let val ← instantiateMVars (← Meta.mkLambdaFVars xs t)
    return (ty, val)

/-- Audit the ASL corollary `corThm` (module `corMod`, which imports the proof module `proofMod`
and the trusted coverage module) of the user's `userThm`: a theorem of `corMod` whose type is
exactly `aslCorollary userThm words`, about the identity-checked `Extracted.program`, with no
JanusASL, ArmASL, Sail or `JanusASLWords` name declared by any untrusted module (the proof, the
consumer package, the corollary module itself apart from `corThm`), printed and round-tripped in a
clean environment that imports `Extracted`, `Janus` and `JanusASL.Verify` only. Same record as
`run`. -/
unsafe def runASLImpl (userThm proofMod corThm corMod marker trusted words : String) (depRoots : Array String) :
    IO Unit := do
  let result ← (show AuditM Record from do
    let userN := userThm.toName
    let corN := corThm.toName
    let corModN := corMod.toName
    let proofModN := proofMod.toName
    let envA ← importModules (loadExts := false)
      #[{ module := `Extracted }, { module := trusted.toName }, { module := corModN }] {}
    let aslClean : Array Import := cleanImports.push { module := `JanusASL.Verify }
    let cleanState ← (withImporting do
      let (_, st) ← (importModulesCore aslClean).run
      return st : IO ImportState)
    let moduleOf := fun (n : Name) => (envA.getModuleIdxFor? n).map fun i => envA.header.moduleNames[i.toNat]!
    let some uci := envA.find? userN | fail s!"the proof does not define {userThm}"
    unless uci matches .thmInfo _ do fail s!"{userThm} is not a theorem"
    unless moduleOf userN == some proofModN do
      fail s!"{userThm} is not declared in the proof module {proofMod}"
    let some ci := envA.find? corN | fail s!"the corollary module does not define {corThm}"
    unless ci matches .thmInfo _ do fail s!"{corThm} is not a theorem"
    unless moduleOf corN == some corModN do
      fail s!"{corThm} is declared in {moduleOf corN}, not in the corollary module {corMod}"
    let some _ := envA.find? words.toName | fail s!"the coverage module does not define {words}"
    unless (moduleOf words.toName).map (·.getRoot) == some `JanusASLWords do
      fail s!"{words} is not declared in the trusted coverage module"
    let axs ← runCore envA (collectAxioms corN)
    checkIdentity envA `program
    checkIdentity envA `entry
    let cx := mkCtx envA depRoots aslTrustedRoots
    -- reserved namespaces: only the trusted builds may declare Extracted/JanusASL/ArmASL/Sail/
    -- JanusASLWords names, and the corollary module only the corollary
    for (n, idx) in envA.const2ModIdx.toList do
      let m := envA.header.moduleNames[idx.toNat]!
      if cx.trusted m then continue
      if n.anyS (· == "Extracted") || imitatesExtracted n then
        fail s!"a non-trusted module declares {n}, whose name shadows the Extracted namespace"
      if aslTrustedRoots.contains n.getRoot || n.getRoot == corModN.getRoot then
        unless m == corModN && n == corN do
          fail s!"the non-trusted module {m} declares {n}, in a namespace reserved for JanusASL and the ASL corollary (a forged or shadowed ASL name)"
    -- the type is the derivation from the user's theorem, exactly
    let (expTy, _) ← runCore envA <| Meta.MetaM.run' <| aslCorollary userN words.toName
    unless expTy == ci.type do
      let eq := match Kernel.isDefEq envA {} expTy ci.type with
        | .ok b => b
        | .error _ => false
      unless eq do
        fail s!"the corollary {corThm} is not the ASL corollary of {userThm} (its type is not Ensures.toASL applied to {userThm})"
    let used := ci.type.getUsedConstants
    let mut mentionsExtracted := false
    let mut localSeed := #[]
    for c in used do
      if c == `Extracted.program || c == `Extracted.entry then
        mentionsExtracted := true
      match moduleOf c with
      | some m => if !cx.trusted m then localSeed := localSeed.push c
      | none => fail s!"the corollary depends on {c}, which is in no imported module"
    unless mentionsExtracted do
      fail "the corollary does not mention Extracted.program or Extracted.entry"
    let (localNames, external) ← collectLocalDefs cx {} {} localSeed.toList
    let localDefs := localNames.filterMap envA.find?
    let externalNames := external.toArray.map (·.1) |>.qsort Name.lt
    for n in localNames ++ externalNames do
      unless plainName n do
        fail s!"the corollary uses {n}, whose name has characters other than ASCII letters, digits, _ ' ! ? and subscripts (a name with lookalike letters prints like a different, trusted constant); rename it"
    let (_, stubs) ← externalStubs cx {} #[] externalNames.toList
    let extDefs := externalNames.filterMap fun n => match envA.find? n with
      | some ci@(.defnInfo _) => some ci
      | _ => none
    let (statement, statementExplicit, defs, extOut, notes) ←
      cleanEnvAndPrint cx corN ci.type localDefs stubs extDefs cleanState aslClean
    return { name := corThm, kind := "theorem", module := corMod, axioms := axs.map (·.toString),
             statement, statementExplicit, definitions := defs,
             modules := envA.header.moduleNames.map (·.toString),
             external := externalNames.filterMap external.get?, externalDefinitions := extOut,
             notes, imports := importGraph envA }
  ).run
  match result with
  | .ok rec => IO.println (marker ++ (toJson rec).compress)
  | .error f => IO.println (marker ++ "ERROR " ++ f.msg)
  (← IO.getStdout).flush

/-- ASL corollary audit entry point (see `runASLImpl`), run like `run` from a generated trusted
`Audit.lean` that imports only this module. -/
@[implemented_by runASLImpl]
opaque runASL (userThm proofMod corThm corMod marker trusted words : String) (depRoots : Array String) : IO Unit

end JanusAudit
