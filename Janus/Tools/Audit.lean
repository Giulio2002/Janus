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
  | 0x3b3 => 'y' | 0x3c3 => 'o'
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

/-- Round 9 (H2): the basic Greek letters Lean accepts in identifiers (`α`–`ω` except `λ`,
`Α`–`Ω` except `Π`, `Σ`). Each looks unlike every other accepted letter once `latinLookalike`
has folded the Latin-looking ones. Polytonic Greek (U+1F00–U+1FFE: `ό` U+1F79 renders as `ό`
U+03CC, `ι` U+1FBE as `ι`) and the accented and Coptic letters U+03CA–U+03FB are not. -/
def greekBinderChar (c : Char) : Bool :=
  (0x3b1 ≤ c.val && c.val ≤ 0x3c9 && c.val != 0x3bb) ||
    (0x391 ≤ c.val && c.val ≤ 0x3a9 && c.val != 0x3a0 && c.val != 0x3a3)

/-- Round 9 (H2): the letterlike symbols (U+2100–U+214F) allowed in a bound variable's name: only
those `latinLookalike` folds (`ℓ`, `ℯ`, `ℎ`, …). The others include exact duplicates of letters
(`K` U+212A KELVIN SIGN is `K`, `Å` U+212B is `Å`, `Ω` U+2126 is `Ω`). -/
def letterlikeFolded : List UInt32 :=
  [0x2107, 0x210e, 0x2113, 0x212e, 0x212f, 0x2130, 0x2134, 0x2139]

/-- Round 7 (H1), narrowed in round 9 (H2): characters a bound variable's name may contain. ASCII
letters, subscripts, basic Greek (`greekBinderChar`), the mathematical script, fraktur and
double-struck letters (folded to Latin by `latinLookalike`), the folded letterlike symbols,
digits and
`_ ' ! ?`. A `«…»` binder may otherwise contain zero-width spaces, combining marks or
lookalike letters from scripts Lean does not accept as identifiers (Cyrillic `х`). -/
def binderChar (c : Char) : Bool :=
  plainNameChar c || greekBinderChar c || (0x1d49c ≤ c.val && c.val ≤ 0x1d59f) ||
    letterlikeFolded.contains c.val

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
      return some s!"binds a variable whose name has characters other than identifier letters, digits and _ ' ! ? (zero-width, combining or lookalike characters): {String.quote str}; rename it (round 7 H1, round 9 H2)"
    let folded := String.ofList (str.toList.map latinLookalike)
    match seen.get? folded with
    | some other =>
      if other != str then
        return some s!"binds two variables whose names look alike, {String.quote other} and {String.quote str} (they read the same once lookalike letters are folded), so the printed statement cannot be read reliably; rename one (round 7 H1)"
    | none => seen := seen.insert folded str
  return none

/-! ## Symbol names (round 8 I1)

`ItabIs ds m tab name`, `segAddr p name` and the other name lookups of the framework fall back to
a default (`False`, `0`) when no object of that name exists. A statement whose name is misspelt,
names an object the binary does not have, or imitates a real name with a lookalike letter
(`"go:itab.*example.com/basic.MulHаsher,…"`, Cyrillic `а`) is then vacuous or about address 0
while it reads as a claim about the named object, and it round-trips. So every such name must
be a string literal (after proof-local definitions are expanded) that names an object of the
extracted program, an `ItabIs` name must be a static itab (`go:itab.`), and the program or data
argument must be `Extracted.program` (`.data`) up to definitional equality. -/

/-- The framework functions that look an object up by name or index: the argument that must be
`Extracted.program` (`.prog`) or `Extracted.program.data` (`.data`), the name (or index) argument,
and the lookup it performs. -/
inductive SymArg where
  | data | prog | globals
  deriving BEq

inductive SymKind where
  | dataName | itabName | segName | dataIndex | contractName | globalName | globalNames
  deriving BEq

def symbolFns : List (Name × SymArg × Nat × Nat × SymKind) :=
  [(`Janus.Spec.ItabIs, .data, 0, 3, .itabName),
   (`Janus.Spec.dataNamed, .data, 0, 1, .dataName),
   (`Janus.Spec.dataAddr, .data, 0, 1, .dataName),
   (`Janus.Spec.dataLen, .data, 0, 1, .dataName),
   (`Janus.Spec.dataWord, .data, 0, 1, .dataName),
   (`Janus.Spec.itabFun, .data, 0, 1, .dataName),
   (`Janus.Spec.segWord, .prog, 0, 1, .segName),
   (`Janus.Tactic.segAddr, .prog, 0, 1, .segName),
   (`Janus.Amd64.Tactic.segAddr, .prog, 0, 1, .segName),
   (`Janus.Amd64.Tactic.dataBase, .prog, 0, 1, .dataIndex),
   -- round 9 (I1g): a contract address looked up by a name that is not a recorded contract is 0
   (`Janus.Program.contractAddr, .prog, 0, 1, .contractName),
   (`Janus.Amd64.Program.contractAddr, .prog, 0, 1, .contractName),
   -- writable globals (`janus extract --global`, Janus/Spec/Globals.lean): a name that is not a
   -- recorded global makes `GlobalsInit`/`GlobalIs` false (the statement vacuous) or the
   -- address 0
   (`Janus.Spec.GlobalsInit, .globals, 0, 2, .globalNames),
   (`Janus.Spec.GlobalIs, .globals, 0, 2, .globalName),
   (`Janus.Spec.globalNamed, .globals, 0, 1, .globalName),
   (`Janus.Spec.globalAddr, .globals, 0, 1, .globalName),
   (`Janus.Spec.GlobalBytesIs, .globals, 0, 2, .globalName),
   (`Janus.Spec.globalImage, .globals, 0, 1, .globalName),
   (`Janus.Spec.globalInitVal, .globals, 0, 1, .globalName)]

/-- The elements of a closed list term, by weak-head reduction. -/
partial def listElems (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let e ← Meta.whnfD e
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => listElems t (acc.push h)
  | (``List.nil, _) => return acc
  | _ => throwError "cannot read the list {e}"

/-- The value of a closed `String` term that reduces to a literal. -/
def strLit? (e : Expr) : MetaM (Option String) := do
  if e.hasFVar || e.hasLooseBVars || e.hasMVar then return none
  match e.consumeMData with
  | .lit (.strVal s) => return some s
  | _ =>
    match (← try Meta.whnfD e catch _ => pure e).consumeMData with
    | .lit (.strVal s) => return some s
    | _ => return none

/-- The names of the data objects and code segments of `Extracted.program`, and its program and
data terms. -/
structure SymTable where
  prog : Expr
  data : Expr
  segs : Expr
  dataNames : Array String
  segNames : Array String
  contractNames : Array String
  globals : Expr
  globalNames : Array String

def symTable : MetaM SymTable := do
  let prog := mkConst `Extracted.program
  let data ← Meta.mkProjection prog `data
  let segs ← Meta.mkProjection prog `segments
  let names (l : Expr) : MetaM (Array String) := do
    (← listElems l).mapM fun d => do
      match ← strLit? (← Meta.mkProjection d `name) with
      | some s => pure s
      | none => throwError "an object of Extracted.program has no literal name"
  let contracts ← (← listElems (← Meta.mkProjection prog `contracts)).mapM fun c => do
    match ← strLit? (← Meta.mkProjection c `fst) with
    | some s => pure s
    | none => throwError "a contract of Extracted.program has no literal name"
  let globals ← Meta.mkProjection prog `globals
  return { prog, data, segs, dataNames := ← names data, segNames := ← names segs,
           contractNames := contracts, globals, globalNames := ← names globals }

/-- Expand the proof-local definitions `locals` everywhere in `e` (beta-reducing their
applications), so a name passed through an `abbrev` or a definition's parameter is seen at its
use. -/
def expandLocals (locals : Std.HashSet Name) (e : Expr) : CoreM Expr := do
  let fuel ← IO.mkRef (100000 : Nat)
  Core.transform e (pre := fun sub => do
    let .const c lvls := sub.getAppFn | return .continue
    unless locals.contains c do return .continue
    let some ci := (← getEnv).find? c | return .continue
    let some _ := ci.value? | return .continue
    let n ← fuel.get
    if n == 0 then throwError "the proof-local definitions of the statement expand too far"
    fuel.set (n - 1)
    return .visit ((ci.instantiateValueLevelParams! lvls).beta sub.getAppArgs))

/-- Round 8 (I1): check every name lookup in `e` (see the section comment). -/
partial def checkSymbolRefs (tbl : SymTable) (e : Expr) : MetaM (Option String) := do
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := fn then
      if let some (_, which, ai, ni, kind) := symbolFns.find? (·.1 == c) then
        if args.size ≤ max ai ni then
          return some s!"uses {c} without its name argument (round 8 I1: every object name must be a literal of the extracted program)"
        let target := if which == .data then tbl.data else if which == .globals then tbl.globals else tbl.prog
        let arg := args[ai]!
        let argOk ← try
            if which == .data || which == .globals then Meta.isDefEq arg target
            else Meta.isDefEq (← Meta.mkProjection arg `segments) tbl.segs <&&>
              Meta.isDefEq (← Meta.mkProjection arg `data) tbl.data
          catch _ => pure false
        unless argOk do
          let what := if which == .data then "Extracted.program.data"
            else if which == .globals then "Extracted.program.globals" else "Extracted.program"
          return some s!"passes `{(← Meta.ppExpr arg).pretty 10000}` to {c}, which is not {what}; object names are looked up in the extracted program only (round 8 I1)"
        let nameArg := args[ni]!
        if kind == .globalNames then
          let elems ← try some <$> listElems nameArg catch _ => pure none
          let some elems := elems
            | return some s!"uses {c} with the name list `{(← Meta.ppExpr nameArg).pretty 10000}`, which is not a literal list (round 8 I1: object names must be literals)"
          for el in elems do
            let some s ← strLit? el
              | return some s!"uses {c} with the name `{(← Meta.ppExpr el).pretty 10000}`, which is not a string literal (round 8 I1)"
            unless tbl.globalNames.contains s do
              return some s!"uses {c} with the name {String.quote s}, but the extracted program has no writable global (`janus extract --global`) of that name, so the precondition is unsatisfiable and the statement vacuous (a misspelt or lookalike name, round 8 I1)"
        else if kind == .dataIndex then
          let i? ← (Meta.evalNat (← instantiateMVars nameArg)).run
          match i? with
          | some i =>
            unless i < tbl.dataNames.size do
              return some s!"uses {c} with index {i}, but the extracted program has {tbl.dataNames.size} data objects (the lookup would silently return 0; round 8 I1)"
          | none =>
            return some s!"uses {c} with the index `{(← Meta.ppExpr nameArg).pretty 10000}`, which is not a numeral (round 8 I1)"
        else
          let some s ← strLit? nameArg
            | return some s!"uses {c} with the name `{(← Meta.ppExpr nameArg).pretty 10000}`, which is not a string literal (round 8 I1: object names must be literals, so the report shows exactly which object is meant)"
          let known := if kind == .segName then tbl.segNames
            else if kind == .contractName then tbl.contractNames
            else if kind == .globalName then tbl.globalNames else tbl.dataNames
          unless known.contains s do
            let what := if kind == .segName then "function"
              else if kind == .contractName then "runtime contract (`janus extract --contract`)"
              else if kind == .globalName then "writable global (`janus extract --global`)" else "data object"
            return some s!"uses {c} with the name {String.quote s}, but the extracted program has no {what} of that name, so the lookup silently defaults (`False` or `0`) and the statement is vacuous or about another value while it reads as a claim about that object (a misspelt or lookalike name, round 8 I1)"
          if kind == .itabName && !s.startsWith "go:itab." then
            return some s!"uses {c} with the data object {String.quote s}, which is not a static itab (go:itab.*T,I) (round 8 I1)"
    for a in args do
      if let some m ← checkSymbolRefs tbl a then return some m
    unless fn.isConst || fn.isFVar do
      if let some m ← checkSymbolRefs tbl fn then return some m
    return none
  | .const c _ =>
    if symbolFns.any (·.1 == c) then
      return some s!"uses {c} unapplied (round 8 I1: every object name must be a literal of the extracted program)"
    return none
  | .lam n d b bi | .forallE n d b bi =>
    if let some m ← checkSymbolRefs tbl d then return some m
    Meta.withLocalDecl n bi d fun x => checkSymbolRefs tbl (b.instantiate1 x)
  | .letE n t v b _ =>
    if let some m ← checkSymbolRefs tbl t then return some m
    if let some m ← checkSymbolRefs tbl v then return some m
    Meta.withLetDecl n t v fun x => checkSymbolRefs tbl (b.instantiate1 x)
  | .mdata _ b => checkSymbolRefs tbl b
  | .proj _ _ b => checkSymbolRefs tbl b
  | _ => return none

/-! ## Round 10 V1: a runtime-contract hypothesis quantifies the runtime

A runtime contract (`Janus.Contracts.*`: a definition whose body is a `Summary`) assumed by a
theorem is a claim about the runtime at its address. It is a meaningful assumption only for the
runtime parameters the theorem quantifies over: the code `impl` (`Extracted.program.link impl`),
the runtime-owned ranges `rt`, the readiness predicate `H : RtReady` and the abstract models
`R : IfaceModel`, `M : MapModel K V`. Passing a closed term instead (`H := fun _ _ _ _ => True`,
`rt := []`, a concrete model, `Extracted.program` itself) can make the hypothesis false for every
implementation, and the theorem vacuous while it reads as a stronger, unconditional claim: round
9 C1's unsatisfiable allocation contracts again, now by the statement's choice. So in every
premise of the statement, each runtime argument of a contract must be a variable bound by the
statement, and no other premise may constrain such a variable, except the model laws
(`IfaceModel.Laws R`, `MapModel.Laws M`), which are trusted facts about the runtime's data. -/

def summaryHeads : List Name := [`Janus.Tactic.Summary, `Janus.Amd64.Tactic.Summary]

partial def bodyIsSummary : Expr → Bool
  | .lam _ _ b _ | .forallE _ _ b _ | .mdata _ b => bodyIsSummary b
  | e => summaryHeads.any e.isAppOf

partial def binderDomains : Expr → Array Expr → Array Expr
  | .forallE _ d b _, acc => binderDomains b (acc.push d)
  | .mdata _ b, acc => binderDomains b acc
  | _, acc => acc

/-- Is `c` a runtime contract of the framework? -/
def isRuntimeContract (env : Environment) (c : Name) : Bool :=
  (`Janus.Contracts).isPrefixOf c && match env.find? c with
    | some (.defnInfo d) => bodyIsSummary d.value ||
        -- a contract stated over runs rather than as a `Summary` (agent/panic's
        -- `GopanicRecoverContract`: a call that does not return but resumes elsewhere), named
        -- `…Contract` by convention, about a program
        ((c.getString!.endsWith "Contract") && (binderDomains d.type #[]).any fun t =>
          t.consumeMData.isConstOf `Janus.Program || t.consumeMData.isConstOf `Janus.Amd64.Program)
    | _ => false

/-- Is `ty` a plain scalar data type or a universe (`Nat`, `Int`, `Bool`, `Fin n`, `BitVec n`, `UIntN`)? -/
def isScalarParamType (ty : Expr) : Bool :=
  ty.isSort ||  -- a type argument (`K`, `V` of `MapModel K V`): data, not a runtime object
  ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isConstOf ``Bool || ty.isAppOf ``Fin ||
  ty.isAppOf ``BitVec || ty.isConstOf ``UInt8 || ty.isConstOf ``UInt16 || ty.isConstOf ``UInt32 ||
  ty.isConstOf ``UInt64

/-- The kind of a contract parameter, from its declared type: `some false` the program (which must
be `Extracted.program.link impl`), `none` a scalar (an entry address, a stack size, a count: a
number the statement may fix to a literal, which only specialises the claim), and `some true` a
runtime parameter (`H`, `rt`, a model, an invariant), which must be a variable of the statement.

Round 11: this is DEFAULT-DENY, not a whitelist of known runtime types. Round 10 listed `RtReady`,
`IfaceModel`, `MapModel` and `List (Nat × Nat)`, so every runtime-model type added later
(`MemModel`, `HashModel`, `PanicRuntime`, `CheckptrModel`, `CgoCheckModel`, `RtInv`, `PoolShape`, …)
escaped, and a proof could pin it to a closed model (`inv := True`, `rt := []`), making the contract
unsatisfiable and the claim vacuous. Now every parameter that is neither the program nor a scalar
number is a runtime parameter, whatever its type, so a new contract type is covered with no change
here. -/
def contractParamKind (ty : Expr) : Option Bool :=
  let ty := ty.consumeMData
  if ty.isConstOf `Janus.Program || ty.isConstOf `Janus.Amd64.Program then some false
  else if isScalarParamType ty then none
  else some true


/-- The explicit allow-list of the default-deny rule (round 11): the framework's own descriptions
of WHICH runtime function a contract is about (`RtSpec`: `concatstringSpec 2`) or which float
format (`Fmt`: `binary32`). Such an argument is not a runtime object the theorem quantifies; it is
part of the contract's identity, and the framework proves each listed spec satisfiable
(`Janus.Contracts.RtSat`, `Sat`). The list is NAMED: only these constants (the spec applications
`concatstringSpec k`, `concatbyteSpec k` with a numeral `k`), never "any imported constant of the
right type": `default : Fmt` (`⟨0, 0⟩`) or a structure update of a listed spec is imported or
built from imported parts too, and describes an impossible function or format. A proof-file
`def`/`abbrev` alias is not accepted either (only the constant itself, which a `notation` or
`local notation` expands to at parse time). -/
def frameworkSpecs : List Name :=
  [`concatstringsSpec, `concatbytesSpec, `slicebytetostringSpec, `slicebytetostringtmpSpec,
   `stringtoslicebyteSpec, `stringtosliceruneSpec, `slicerunetostringSpec, `intstringSpec,
   `decoderuneSpec, `countrunesSpec, `gostringSpec, `gostringnSpec, `gobytesSpec, `growsliceSpec,
   `growsliceNoAliasSpec, `growsliceBufSpec, `growsliceBufNoAliasSpec, `makeslicecopySpec,
   `moveSliceSpec, `moveSliceNoScanSpec, `moveSliceNoCapSpec, `moveSliceNoCapNoScanSpec,
   `slicecopySpec, `typedslicecopySpec, `wbZeroSpec, `wbMoveSpec].map (`Janus.Contracts ++ ·)

def frameworkSpecsNat : List Name :=
  [`concatstringSpec, `concatbyteSpec].map (`Janus.Contracts ++ ·)

def frameworkFmts : List Name := [`Janus.Float.binary32, `Janus.Float.binary64]

/-- Which allow-listed type is `ty`: `some true` for `RtSpec`, `some false` for `Fmt`. -/
def frameworkConstParamType (ty : Expr) : Option Bool :=
  let ty := ty.consumeMData
  if ty.isConstOf `Janus.Contracts.RtSpec then some true
  else if ty.isConstOf `Janus.Float.Fmt then some false
  else none

/-- Is `a` one of the named framework constants (see `frameworkSpecs`)? -/
def isFrameworkConstArg (env : Environment) (isSpec : Bool) (a : Expr) : Bool :=
  let a := a.consumeMData
  let imported (c : Name) : Bool := (env.getModuleIdxFor? c).isSome
  if isSpec then
    match a with
    | .const c _ => frameworkSpecs.contains c && imported c
    | .app (.const c _) k =>
        frameworkSpecsNat.contains c && imported c && (k.nat?.isSome || k.rawNatLit?.isSome)
    | _ => false
  else match a with
    | .const c _ => frameworkFmts.contains c && imported c
    | _ => false

/-- Is `a` a constant of the generated module `Extracted` other than the program itself
(`Extracted.funcs`, …)? A proof-file constant, even one named `Extracted.x`, lives in another
module, so it is not accepted. -/
def isExtractedConst (env : Environment) (a : Expr) : Bool :=
  match a.consumeMData with
  | .const c _ =>
      c.getPrefix == `Extracted && c != `Extracted.program &&
      match env.getModuleIdxFor? c with
      | some idx => env.header.moduleNames[idx.toNat]? == some `Extracted
      | none => false
  | _ => false

/-- The runtime-contract applications in `e` (outermost first). With `claims`, the subterms under
an `∃` are skipped: a contract there is claimed (a witness theorem's), not assumed. -/
partial def contractApps (env : Environment) (e : Expr) (acc : Array Expr := #[])
    (claims : Bool := false) : Array Expr :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    if claims && fn.isConstOf ``Exists then acc else
    let acc := match fn with
      | .const c _ => if isRuntimeContract env c then acc.push e else acc
      | _ => contractApps env fn acc claims
    e.getAppArgs.foldl (fun acc a => contractApps env a acc claims) acc
  | .lam _ d b _ | .forallE _ d b _ => contractApps env b (contractApps env d acc claims) claims
  | .letE _ t v b _ => contractApps env b (contractApps env v (contractApps env t acc claims) claims) claims
  | .mdata _ b | .proj _ _ b => contractApps env b acc claims
  | _ => acc

/-- The parts of a conclusion that are checked like premises: the conclusion itself, except that
a conjunction is split and a part that is itself a runtime contract (a claim the theorem proves)
is exempt. -/
partial def conclParts (env : Environment) (e : Expr) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then conclParts env (e.getArg! 0) ++ conclParts env (e.getArg! 1)
  else match e.getAppFn with
    | .const c _ => if isRuntimeContract env c then #[] else #[e]
    | _ => #[e]

/-- A premise that bounds the stack depth of a runtime model (the `depth` field of
`IfaceModel`, `MapModel`, …) and mentions the runtime variables only there: `n ≤ R.depth` /
`n < R.depth` with a closed `n` (a model may always be given a larger stack bound, which only
weakens its contracts), or `R.depth + k ≤ d` / `<` where `d` mentions a variable of the
statement that is not a runtime one and no runtime variable outside `.depth` (satisfiable for
every model by the choice of `d`). Such side conditions cannot pin a contract's runtime argument
(round 10 V1's concern); they read like any numeric precondition. -/
def depthBound (bound : Std.HashSet FVarId) (rtVars : Std.HashSet FVarId) (t : Expr) : Bool :=
  let isDepth (e : Expr) : Bool := match e.consumeMData with
    | .app (.const f _) x => f.getString! == "depth" && x.isFVar && rtVars.contains x.fvarId!
    | .proj _ _ x => x.isFVar && rtVars.contains x.fvarId!
    | _ => false
  -- `e` with every `X.depth` of a runtime variable replaced by a constant
  let strip (e : Expr) : Expr := e.replace fun sub => if isDepth sub then some (mkConst ``Nat.zero) else none
  let hasDepth (e : Expr) : Bool := (e.find? isDepth).isSome
  let rtFree (e : Expr) : Bool := !(strip e).hasAnyFVar (rtVars.contains ·)
  if (t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4) && (t.getArg! 0).isConstOf ``Nat then
    let a := t.getArg! 2; let b := t.getArg! 3
    (hasDepth b && rtFree b && !a.hasFVar && !hasDepth a) ||
      (hasDepth a && rtFree a && !hasDepth b && !b.hasAnyFVar (rtVars.contains ·) &&
        b.hasAnyFVar (fun v => bound.contains v && !rtVars.contains v))
  else false

/-- Round 10 V1: check the contract premises of the statement `ty` (see the section comment). -/
def checkContractHyps (ty : Expr) : MetaM (Option String) := do
  let env ← getEnv
  Meta.forallTelescope ty fun xs body => do
    let bound : Std.HashSet FVarId := xs.foldl (fun s x => s.insert x.fvarId!) {}
    let mut rtVars : Std.HashSet FVarId := {}
    let mut premises : Array (Expr × Expr) := #[]
    for x in xs do
      let t ← Meta.inferType x
      if ← Meta.isProp t then premises := premises.push (x, t)
    let isVar (a : Expr) : Bool := a.isFVar && bound.contains a.fvarId!
    -- a contract assumed inside the conclusion (say, in an `Ensures` precondition) is checked
    -- too; only a conclusion that is itself a contract (a theorem proving one) is exempt
    -- (nor is each conjunct of a conclusion that is a conjunction: a theorem proving several
    -- contracts at once, e.g. `gcWriteBarrier1..8`, assumes none of them)
    let concl := conclParts env body
    let apps := premises.foldl (fun acc (_, t) => contractApps env t acc) #[] ++
      concl.foldl (fun acc t => contractApps env t acc (claims := true)) #[]
    for app in apps do
      let .const c _ := app.getAppFn | continue
      let some ci := env.find? c | continue
      let doms := binderDomains ci.type #[]
      let args := app.getAppArgs
      if args.size < doms.size then
        return some s!"applies the runtime contract {c} partially (round 10 V1)"
      for i in [0:doms.size] do
        let a := args[i]!.consumeMData
        if let some isSpec := frameworkConstParamType doms[i]! then
          unless isFrameworkConstArg env isSpec a do
            return some s!"assumes the runtime contract {c} for the argument `{(← Meta.ppExpr a).pretty 10000}`, which is not one of the framework's named {if isSpec then "runtime-function specs (`concatstringSpec 2`, `growsliceSpec`, …)" else "float formats (`binary32`, `binary64`)"}: the function or format a contract describes cannot be chosen by the statement, not even from imported parts such as `default` (round 11)"
          continue
        -- Round 13: an argument that is EXACTLY a constant generated by `janus extract` into
        -- `Extracted.lean` (`Extracted.funcs`, the function metadata the panic contracts read from
        -- .gopclntab, …) is the extraction's own data: `janus check` regenerates the whole file
        -- from the binary and compares it byte for byte, so the statement cannot choose it.
        -- Syntactically that constant (levels aside) and nothing else: not a projection, a
        -- `List.tail`/`take`/`++`, a `let` or a proof-local alias (those are not this constant).
        if isExtractedConst env a then continue
        match contractParamKind doms[i]! with
        | some true =>
          unless isVar a do
            return some s!"assumes the runtime contract {c} for the runtime argument `{(← Meta.ppExpr a).pretty 10000}`, which is not a variable of the statement: a contract is an assumption about the runtime only when the theorem quantifies its code, runtime-owned memory, readiness predicate and models; a closed choice (such as `fun _ _ _ _ => True`, `[]` or a concrete model) can make it false for every implementation and the theorem vacuous (round 10 V1; round 11: every contract argument that is not the program or a number is a runtime parameter, whatever its type)"
          rtVars := rtVars.insert a.fvarId!
        | some false =>
          let ok := (a.isAppOfArity `Janus.Program.link 2 || a.isAppOfArity `Janus.Amd64.Program.link 2) &&
            (a.getArg! 0).isConstOf `Extracted.program && isVar (a.getArg! 1).consumeMData
          -- the `morestack` contracts are relations over the call state at a `morestack` stub:
          -- there is no implementation code to link (the program is only consulted through
          -- `stubAt`, which `link` does not change), so they may be stated about
          -- `Extracted.program` itself
          let noCode := (c == `Janus.Contracts.Stack.MorestackContract ||
            c == `Janus.Contracts.StackAmd64.MorestackContract64) && a.isConstOf `Extracted.program
          if noCode then continue
          unless ok do
            return some s!"assumes the runtime contract {c} about the program `{(← Meta.ppExpr a).pretty 10000}`, which is not `Extracted.program.link impl` for a variable `impl` of the statement (round 10 V1)"
          rtVars := rtVars.insert (a.getArg! 1).consumeMData.fvarId!
        | none => pure ()
    if rtVars.isEmpty then return none
    -- Round 13: the discipline covers EVERY binder, of any sort. A binder that is not a Prop
    -- (a `Type`/`Sort u` binder: `PLift (H = …)`, `{u : Unit // H = …}`, `ULift (PLift …)`, a
    -- proof-local `def Pin H : Type := …`, a structure bundling a pin) is not inspected as a
    -- premise, yet carries one as soon as its type mentions a runtime variable. The runtime
    -- variables themselves (free binders) and binders that mention none keep their treatment;
    -- everything else is rejected, whatever it wraps. (Occurrence of the variable in the binder's
    -- type, after `instantiateMVars`, is what makes unfolding irrelevant: a definition can only
    -- reach the bound `H` through an argument.)
    for x in xs do
      if rtVars.contains x.fvarId! then continue
      let t ← instantiateMVars (← Meta.inferType x)
      if ← Meta.isProp t then continue
      if t.hasAnyFVar (rtVars.contains ·) then
        return some s!"has the non-Prop binder `{(← x.fvarId!.getUserName)} : {(← Meta.ppExpr t).pretty 10000}` whose type mentions a runtime variable of a contract hypothesis: a binder of any sort (`PLift`, `ULift`, `Subtype`, `Sigma`, a structure, a proof-local `def …: Type`) could carry a constraint on the runtime that only the contracts and the model laws may state; put such a condition in the precondition instead (round 13)"
    for (x, t) in premises do
      unless t.hasAnyFVar (rtVars.contains ·) do continue
      let t' := t.consumeMData
      let isContract := match t'.getAppFn with
        | .const c _ => isRuntimeContract env c
        | _ => false
      -- the laws of a model: `….Laws M` for a framework model (`IfaceModel`, `MapModel`,
      -- `MemModel`, `HashModel`, …) with `M` a variable and no runtime variable elsewhere
      let isLaws := match t'.getAppFn with
        | .const c _ => (`Janus).isPrefixOf c && c.getString! == "Laws" && t'.getAppNumArgs ≥ 1 &&
            isVar t'.appArg!.consumeMData &&
            !t'.getAppArgs.pop.any (·.hasAnyFVar (rtVars.contains ·))
        | _ => false
      unless isContract || isLaws || depthBound bound rtVars t' do
        return some s!"has the premise `{(← Meta.ppExpr t).pretty 10000}` ({(← x.fvarId!.getUserName)}), which constrains a runtime variable of a contract hypothesis; only the contracts and the model laws may mention them (round 10 V1, round 11)"
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
    -- round 8 I1: object names resolve in the extracted program
    let tbl ← symTable
    let localSet : Std.HashSet Name := localDefs.foldl (fun s ci => s.insert ci.name) {}
    let expanded ← expandLocals localSet thmType
    if let some m ← checkSymbolRefs tbl expanded then
      throwError s!"the statement {m}"
    -- round 10 V1: contract hypotheses quantify the runtime
    if let some m ← checkContractHyps expanded then
      throwError s!"the statement {m}"
    for ci in extDefs do
      for t in [ci.type] ++ ci.value?.toList do
        if let some m ← checkSymbolRefs tbl t then
          throwError s!"the dependency definition {ci.name} used in the statement {m}"
        -- round 10 V1: a contract hidden in a dependency definition escapes the premise check
        if !(contractApps (← getEnv) t).isEmpty then
          throwError s!"the dependency definition {ci.name} used in the statement applies a runtime contract; state contract hypotheses in the theorem itself (round 10 V1)"
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
