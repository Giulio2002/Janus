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
  /-- Round 14: what the verified theorem is: `main` (a correctness statement: the runtime is
  quantified), `witness-nonvacuous` or `witness-returns` (a concrete instance showing the main
  theorem's hypotheses are satisfiable / that it fires; NOT a correctness claim). -/
  role : String := "main"
  /-- Round 14: for a witness, the main theorem of the proof module whose hypotheses and
  precondition it instantiates (or whose guarantee it states at a concrete state). -/
  matchedMain : String := ""
  /-- Every main theorem of the proof module the witness is an instance of (`matchedMain` is the first):
  a witness for a precondition several theorems share supports all of them. -/
  matchedMains : Array String := #[]
  /-- The module declaring each of `matchedMains` (a witness may sit in a module of its own, importing the main
  theorem's: `Three/Witness.lean`). -/
  matchedModules : Array String := #[]
  /-- Round 14: the runtime contracts the STATEMENT applies (`NewobjectContract@runtime.newobject`),
  computed from the statement, not from the extraction. A main theorem has them as hypotheses; a
  witness claims them. Empty: the statement assumes nothing about the runtime. -/
  contractHyps : Array String := #[]
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

/-- Is `n` an equation lemma that Lean generated on demand in the proof's module for a constant of the
generated module `Extracted` (`simp only [Extracted.dataSize.«sym»]` realizes `Extracted.dataSize.«sym».eq_1`,
`unfold` realizes `….eq_def`)? Exactly: `n = c.eq_<k>` or `c.eq_def`, `c` declared in the module `Extracted`,
and `n` a theorem of the form `c args = rhs`. Such a lemma is proved by Lean from the definition, so it adds
nothing the definition does not say, and it declares no new `Extracted` definition; every other
`Extracted`-named declaration of a proof module is still rejected. -/
def isGeneratedEqnLemma (env : Environment) (n : Name) : Bool :=
  match n with
  | .str c l =>
    (l == "eq_def" || (l.startsWith "eq_" && (l.drop 3).all Char.isDigit && (l.drop 3).length > 0)) &&
    (match env.getModuleIdxFor? c with
      | some i => env.header.moduleNames[i.toNat]? == some `Extracted
      | none => false) &&
    (match env.find? n with
      | some (.thmInfo ci) =>
        ci.type.isAppOfArity ``Eq 3 && (ci.type.getArg! 1).getAppFn.constName? == some c
      | _ => false)
  | _ => false

/-- Check every named data-symbol constant of the extraction (`Extracted.dataAddr.«sym»`,
`Extracted.dataSize.«sym»`, generated by `janus extract` from the binary's symbol table) against the
independently elaborated trusted copy, exactly like `program` and `entry`: a statement may mention
them, and a planted or shadowed definition of one differs from the trusted copy and is rejected. -/
def checkDataSymIdentities (env : Environment) : AuditM Unit := do
  -- `env.header.moduleNames` rebuilds the array of every module name on EACH call: it is taken once,
  -- and the cheap name test runs first (calling it per constant made the audit ~9 s instead of ~1.5 s)
  let modNames := env.header.moduleNames
  let names := env.const2ModIdx.fold (init := #[]) fun acc n idx =>
    if n.getPrefix.getPrefix == `Extracted && (n.getPrefix == `Extracted.dataAddr || n.getPrefix == `Extracted.dataSize) &&
        modNames[idx.toNat]? == some `Extracted then acc.push n else acc
  for n in names.qsort Name.lt do
    checkIdentity env (n.replacePrefix `Extracted .anonymous)

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

/-! ## The amd64 undefined-value stream is not part of any statement (BSF/BSR of zero)

The amd64 model gives the destination of `BSF`/`BSR` of zero the next element of an undefined-value
stream, `State.undefVal` = `kreg 8` (indices `>= 8` of the opmask file are used for nothing else; `Janus.Amd64.Exec`). A
theorem about such code is sound because it holds for every stream (every initial state). A statement
that PINS the stream (`s.kreg 8 = s.regs 0`, `s.kreg = fun _ => 0`, `s.undefVal = 0`) would instead read
as if the architecturally undefined destination were known, and it would be accepted by the kernel.
The auditor therefore rejects any mention, in the statement (proof-local definitions expanded) or in
a dependency definition it uses, of `State.undefVal`, `State.advanceUndef`, and `State.kreg` at an index
that is not a literal below 8 (the AVX-512 opmask registers `k0`..`k7`), or `State.kreg` whole, except
as a frame equation `a.kreg = b.kreg` between two states (it names no value). It only rejects more.

Round RTU2b: a pin need not name `kreg` at all. The auditor also rejects, in the same places, every way
to take a state apart (`match`, `State.casesOn`/`rec`), the default state, every state-valued term that
is not a variable (`{ s with kreg := _ }`, `setK s 8 5`, `s.strip512`, `retState ..`), a `State.mk`
whose opmask file is not copied from a variable (a fully concrete state, the start of a `Witness`
theorem, is allowed). An equation at a type built from `State` then holds only variables and
framework functions of them (`step s .. = .error ..` stays allowed). -/

/-- A literal opmask index below 8. -/
def opmaskLit? (e : Expr) : Bool :=
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => (n.rawNatLit?.map (fun x => decide (x < 8))).getD false
  | _ => (e.rawNatLit?.map (fun x => decide (x < 8))).getD false

/-- A variable (free or bound), possibly under metadata. -/
def atomVar (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ | .bvar _ => true
  | _ => false

/-- `State.kreg x` for a variable `x`: the opmask file of a state, naming no value (a frame). -/
def kregFrame (e : Expr) : Bool :=
  let e := e.consumeMData
  e.getAppFn.isConstOf `Janus.Amd64.State.kreg && e.getAppNumArgs == 1 && atomVar e.appArg!

/-- The ways to take a `State` apart or to build one from nothing (round RTU2b): a `match` on a
state (its matcher unfolds to `casesOn`), `State.rec`, the default state. They read or choose a
state's `kreg` without naming `State.kreg`. -/
def undefStreamConsts : List Name :=
  [`Janus.Amd64.State.undefVal, `Janus.Amd64.State.advanceUndef, `Janus.Amd64.State.casesOn,
   `Janus.Amd64.State.rec, `Janus.Amd64.State.recOn, `Janus.Amd64.State.brecOn,
   `Janus.Amd64.State.binductionOn, `Janus.Amd64.State.noConfusion,
   `Janus.Amd64.State.noConfusionType, `Janus.Amd64.instInhabitedState]

/-- Does the constant `c` produce a `State` (its type, after the parameters, is `State`)? -/
def returnsState (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci =>
    let rec go : Expr → Bool
      | .forallE _ _ b _ => go b
      | .mdata _ b => go b
      | t => t.isConstOf `Janus.Amd64.State
    go ci.type
  | none => false

/-- The first subterm of `e` that pins or reads the undefined-value stream (see above). -/
partial def findUndefStream (env : Environment) (witness : Bool) (kregIdx : Nat) (e : Expr) : Option Expr :=
  let kregFn : Name := `Janus.Amd64.State.kreg
  let findUndefStream := findUndefStream env witness
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const c _ =>
      if undefStreamConsts.contains c then some e
      else if returnsState env c && c != `Janus.Amd64.State.mk then
        -- any state that is not a variable (`setK t 8 5`, `t.strip512`, `retState ..`): the only
        -- states of a statement are the quantified ones (their opmask file is arbitrary)
        some e
      else if c == kregFn then
        if args.size ≥ 2 then
          if opmaskLit? args[1]! then args.findSome? (findUndefStream kregIdx) else some e
        else some e
      else if c == `Janus.Amd64.State.mk then
        -- a state built from fields: its opmask file must be a copy of a variable's (`{ s with .. }`)
        -- A fully concrete state (no variable anywhere) is the initial state of a `Witness` theorem, a
        -- run of one named state, not a theorem about every state; it is allowed there only (a theorem inside a `Witness` namespace).
        -- Only in a `Witness` theorem (round RTU2c): in the theorem that is the guarantee, a
        -- concrete state pins the stream to the default (`kreg := fun _ => 0`, which `pp` does not
        -- even show) and a model's value for an undefined destination reads as a known result.
        if witness && !e.hasFVar && !e.hasLooseBVars && !e.hasMVar then args.findSome? (findUndefStream kregIdx)
        else if args.size > kregIdx && kregFrame args[kregIdx]! then
          (args.eraseIdx! kregIdx).findSome? (findUndefStream kregIdx)
        else some e
      else if c == ``Eq && args.size == 3 then
        if kregFrame args[1]! && kregFrame args[2]! then none
        else args.findSome? (findUndefStream kregIdx)
      else args.findSome? (findUndefStream kregIdx)
    | _ => (findUndefStream kregIdx fn).orElse fun _ => args.findSome? (findUndefStream kregIdx)
  | .const c _ => if undefStreamConsts.contains c || c == kregFn || c == `Janus.Amd64.State.mk || returnsState env c then some e else none
  | .lam _ t b _ | .forallE _ t b _ => (findUndefStream kregIdx t).orElse fun _ => findUndefStream kregIdx b
  | .letE _ t v b _ => (findUndefStream kregIdx t).orElse fun _ => (findUndefStream kregIdx v).orElse fun _ => findUndefStream kregIdx b
  | .mdata _ b => findUndefStream kregIdx b
  | .proj sn i b => if sn == `Janus.Amd64.State && i == kregIdx then some e else findUndefStream kregIdx b
  | _ => none

/-! The role of a theorem by name (round 14), declared here because the undefined-stream check needs it. -/

inductive Role | main | nonvacuous | returns | auxiliary
  deriving BEq

def Role.label : Role → String
  | .main => "main"
  | .nonvacuous => "witness-nonvacuous"
  | .returns => "witness-returns"
  | .auxiliary => "witness-auxiliary"

def roleOf (n : Name) : Role :=
  let cs := n.components
  if !cs.any (· == `Witness) then .main else
  match cs.reverse with
  | l :: w :: _ =>
      if w == `Witness then
        (if l == `nonvacuous then .nonvacuous else if l == `returns then .returns else .auxiliary)
      else .auxiliary
  | _ => .auxiliary

/-- The role of a theorem from its name AND statement. A theorem of a `Witness` namespace under any
name other than `nonvacuous`/`returns` whose statement is an `∃` is a non-vacuity witness candidate
(`Role.nonvacuous`): `checkWitness` still demands that it instantiate a main theorem's whole
hypotheses (contract hypotheses included), so the semantic match, not the name, decides. -/
def roleOfTy (n : Name) (ty : Expr) : Role :=
  match roleOf n with
  | .auxiliary =>
    if n.components.any (· == `Witness) && ty.consumeMData.isAppOfArity ``Exists 2 then .nonvacuous else .auxiliary
  | r => r

/-- Reject a statement or definition that mentions the undefined-value stream. -/
def checkUndefStream (witness : Bool) (e : Expr) : MetaM (Option String) := do
  let fields := getStructureFields (← getEnv) `Janus.Amd64.State
  let kregIdx := (fields.idxOf? `kreg).getD 1000
  match findUndefStream (← getEnv) witness kregIdx e with
  | none => return none
  | some bad =>
    let s := (← try Meta.ppExpr bad catch _ => pure (toString bad)).pretty 300
    return some s!"mentions the amd64 undefined-value stream (`{s}`): `State.undefVal`, `State.advanceUndef` and `State.kreg` at an index that is not a literal below 8 are the model's source of the architecturally undefined result of BSF/BSR of zero; a statement may not name or constrain them (a pinned stream reads as a known value for an undefined destination). Quantify over every state instead"

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

partial def forallBinderNames : Expr → Array Name → Array Name
  | .forallE n _ b _, acc => forallBinderNames b (acc.push n)
  | .mdata _ b, acc => forallBinderNames b acc
  | _, acc => acc

/-- Round 14: the PINNED runtime-contract predicates, as (defining module, short name). A premise counts as a
runtime contract only if its head constant is DEFINED in the module listed here (looked up in the environment's
constant-to-module map, so a proof or consumer module that declares `namespace Janus.Contracts` and its own
`FakeContract`/`Summary` def, or shadows a real contract's name, is not a contract). Generated from the framework's
contract definitions by `python3 audit/round9/sat_check.py ROOT --emit`; the SAT row of audit/round9 fails if this
list and the tree differ, so a new framework def does not become a contract by accident. -/
def pinnedContracts : Array (String × String) := #[
-- BEGIN pinnedContracts
  ("Janus.Contracts.Alloc", "GrowsliceContract"),
  ("Janus.Contracts.Alloc", "MakesliceContract"),
  ("Janus.Contracts.Alloc", "MallocgcContract"),
  ("Janus.Contracts.Alloc", "NewobjectContract"),
  ("Janus.Contracts.AllocAmd64", "GrowsliceContract64"),
  ("Janus.Contracts.AllocAmd64", "MakesliceContract64"),
  ("Janus.Contracts.AllocAmd64", "MallocgcContract64"),
  ("Janus.Contracts.AllocAmd64", "NewobjectContract64"),
  ("Janus.Contracts.Cmpstring", "CmpstringContract"),
  ("Janus.Contracts.CmpstringAmd64", "CmpstringContract64"),
  ("Janus.Contracts.Errorf", "ErrorfLive"),
  ("Janus.Contracts.ErrorfAmd64", "ErrorfLive"),
  ("Janus.Contracts.Hash", "Chash"),
  ("Janus.Contracts.Hash", "Fhash"),
  ("Janus.Contracts.Hash", "Interhash"),
  ("Janus.Contracts.Hash", "Memhash"),
  ("Janus.Contracts.Hash", "Memhash0"),
  ("Janus.Contracts.Hash", "Memhash32"),
  ("Janus.Contracts.Hash", "Memhash64"),
  ("Janus.Contracts.Hash", "MemhashN"),
  ("Janus.Contracts.Hash", "MemhashVarlen"),
  ("Janus.Contracts.Hash", "Nilinterhash"),
  ("Janus.Contracts.Hash", "Rand"),
  ("Janus.Contracts.Hash", "Strhash"),
  ("Janus.Contracts.Hash", "Typehash"),
  ("Janus.Contracts.HashAmd64", "Chash"),
  ("Janus.Contracts.HashAmd64", "Fhash"),
  ("Janus.Contracts.HashAmd64", "Interhash"),
  ("Janus.Contracts.HashAmd64", "Memhash"),
  ("Janus.Contracts.HashAmd64", "Memhash0"),
  ("Janus.Contracts.HashAmd64", "Memhash32"),
  ("Janus.Contracts.HashAmd64", "Memhash64"),
  ("Janus.Contracts.HashAmd64", "MemhashN"),
  ("Janus.Contracts.HashAmd64", "MemhashVarlen"),
  ("Janus.Contracts.HashAmd64", "Nilinterhash"),
  ("Janus.Contracts.HashAmd64", "Rand"),
  ("Janus.Contracts.HashAmd64", "Strhash"),
  ("Janus.Contracts.HashAmd64", "Typehash"),
  ("Janus.Contracts.ICall", "ICallContract"),
  ("Janus.Contracts.ICallAmd64", "ICallContract64"),
  ("Janus.Contracts.Iface", "AssertE2I"),
  ("Janus.Contracts.Iface", "AssertE2I2"),
  ("Janus.Contracts.Iface", "ConvT"),
  ("Janus.Contracts.Iface", "ConvT16"),
  ("Janus.Contracts.Iface", "ConvT32"),
  ("Janus.Contracts.Iface", "ConvT64"),
  ("Janus.Contracts.Iface", "ConvTnoptr"),
  ("Janus.Contracts.Iface", "ConvTslice"),
  ("Janus.Contracts.Iface", "ConvTstring"),
  ("Janus.Contracts.Iface", "Efaceeq"),
  ("Janus.Contracts.Iface", "Ifaceeq"),
  ("Janus.Contracts.Iface", "InterfaceSwitch"),
  ("Janus.Contracts.Iface", "TypeAssert"),
  ("Janus.Contracts.IfaceAmd64", "AssertE2I"),
  ("Janus.Contracts.IfaceAmd64", "AssertE2I2"),
  ("Janus.Contracts.IfaceAmd64", "ConvT"),
  ("Janus.Contracts.IfaceAmd64", "ConvT16"),
  ("Janus.Contracts.IfaceAmd64", "ConvT32"),
  ("Janus.Contracts.IfaceAmd64", "ConvT64"),
  ("Janus.Contracts.IfaceAmd64", "ConvTnoptr"),
  ("Janus.Contracts.IfaceAmd64", "ConvTslice"),
  ("Janus.Contracts.IfaceAmd64", "ConvTstring"),
  ("Janus.Contracts.IfaceAmd64", "Efaceeq"),
  ("Janus.Contracts.IfaceAmd64", "Ifaceeq"),
  ("Janus.Contracts.IfaceAmd64", "InterfaceSwitch"),
  ("Janus.Contracts.IfaceAmd64", "TypeAssert"),
  ("Janus.Contracts.InstrumentCalls", "CgoCheckPointer"),
  ("Janus.Contracts.InstrumentCalls", "CgoCheckResult"),
  ("Janus.Contracts.InstrumentCalls", "CheckptrAlignment"),
  ("Janus.Contracts.InstrumentCalls", "CheckptrArithmetic"),
  ("Janus.Contracts.InstrumentCallsAmd64", "CgoCheckPointer64"),
  ("Janus.Contracts.InstrumentCallsAmd64", "CgoCheckResult64"),
  ("Janus.Contracts.InstrumentCallsAmd64", "CheckptrAlignment64"),
  ("Janus.Contracts.InstrumentCallsAmd64", "CheckptrArithmetic64"),
  ("Janus.Contracts.Live", "GrowsliceLiveContract"),
  ("Janus.Contracts.Live", "MakesliceLiveContract"),
  ("Janus.Contracts.Live", "MallocgcLiveContract"),
  ("Janus.Contracts.Live", "MallocgcSmallNoScanSCLiveContract"),
  ("Janus.Contracts.Live", "MallocgcSmallScanNoHeaderSCLiveContract"),
  ("Janus.Contracts.Live", "MallocgcTinySizeLiveContract"),
  ("Janus.Contracts.Live", "MemclrHasPointersLive"),
  ("Janus.Contracts.Live", "MemclrNoHeapPointersLive"),
  ("Janus.Contracts.Live", "MemmoveLive"),
  ("Janus.Contracts.Live", "NewobjectLiveContract"),
  ("Janus.Contracts.Live", "RtLiveContract"),
  ("Janus.Contracts.Live", "TypedMemclrLive"),
  ("Janus.Contracts.Live", "TypedMemmoveLive"),
  ("Janus.Contracts.Live", "WbLiveContract"),
  ("Janus.Contracts.LiveAmd64", "GrowsliceLiveContract64"),
  ("Janus.Contracts.LiveAmd64", "MakesliceLiveContract64"),
  ("Janus.Contracts.LiveAmd64", "MallocgcLiveContract64"),
  ("Janus.Contracts.LiveAmd64", "MallocgcSmallNoScanSCLiveContract64"),
  ("Janus.Contracts.LiveAmd64", "MallocgcSmallScanNoHeaderSCLiveContract64"),
  ("Janus.Contracts.LiveAmd64", "MallocgcTinySizeLiveContract64"),
  ("Janus.Contracts.LiveAmd64", "MemclrHasPointersLive64"),
  ("Janus.Contracts.LiveAmd64", "MemclrNoHeapPointersLive64"),
  ("Janus.Contracts.LiveAmd64", "MemmoveLive64"),
  ("Janus.Contracts.LiveAmd64", "NewobjectLiveContract64"),
  ("Janus.Contracts.LiveAmd64", "RtLiveContract64"),
  ("Janus.Contracts.LiveAmd64", "TypedMemclrLive64"),
  ("Janus.Contracts.LiveAmd64", "TypedMemmoveLive64"),
  ("Janus.Contracts.LiveAmd64", "WbLiveContract64"),
  ("Janus.Contracts.MallocSC", "MallocgcSmallNoScanSCContract"),
  ("Janus.Contracts.MallocSC", "MallocgcSmallScanNoHeaderSCContract"),
  ("Janus.Contracts.MallocSC", "MallocgcTinySizeContract"),
  ("Janus.Contracts.MallocSCAmd64", "MallocgcSmallNoScanSCContract64"),
  ("Janus.Contracts.MallocSCAmd64", "MallocgcSmallScanNoHeaderSCContract64"),
  ("Janus.Contracts.MallocSCAmd64", "MallocgcTinySizeContract64"),
  ("Janus.Contracts.Map", "Access1"),
  ("Janus.Contracts.Map", "Access2"),
  ("Janus.Contracts.Map", "Access2Ptr"),
  ("Janus.Contracts.Map", "Assign"),
  ("Janus.Contracts.Map", "Clear"),
  ("Janus.Contracts.Map", "Delete"),
  ("Janus.Contracts.Map", "IterNext"),
  ("Janus.Contracts.Map", "IterStart"),
  ("Janus.Contracts.Map", "MakeSmall"),
  ("Janus.Contracts.MapAmd64", "Access1"),
  ("Janus.Contracts.MapAmd64", "Access2"),
  ("Janus.Contracts.MapAmd64", "Access2Ptr"),
  ("Janus.Contracts.MapAmd64", "Assign"),
  ("Janus.Contracts.MapAmd64", "Clear"),
  ("Janus.Contracts.MapAmd64", "Delete"),
  ("Janus.Contracts.MapAmd64", "IterNext"),
  ("Janus.Contracts.MapAmd64", "IterStart"),
  ("Janus.Contracts.MapAmd64", "MakeSmall"),
  ("Janus.Contracts.MapStr", "Access1Str"),
  ("Janus.Contracts.MapStr", "Access2Str"),
  ("Janus.Contracts.MapStr", "AssignStr"),
  ("Janus.Contracts.MapStr", "DeleteStr"),
  ("Janus.Contracts.MapStrAmd64", "Access1Str64"),
  ("Janus.Contracts.MapStrAmd64", "Access2Str64"),
  ("Janus.Contracts.MapStrAmd64", "AssignStr64"),
  ("Janus.Contracts.MapStrAmd64", "DeleteStr64"),
  ("Janus.Contracts.MapVar", "Access1F32"),
  ("Janus.Contracts.MapVar", "Access1Fat"),
  ("Janus.Contracts.MapVar", "Access1G"),
  ("Janus.Contracts.MapVar", "Access2F32"),
  ("Janus.Contracts.MapVar", "Access2Fat"),
  ("Janus.Contracts.MapVar", "Access2G"),
  ("Janus.Contracts.MapVar", "Assign64Ptr"),
  ("Janus.Contracts.MapVar", "AssignF32"),
  ("Janus.Contracts.MapVar", "AssignG"),
  ("Janus.Contracts.MapVar", "DeleteF32"),
  ("Janus.Contracts.MapVar", "DeleteG"),
  ("Janus.Contracts.MapVar", "MakeMap"),
  ("Janus.Contracts.MapVarAmd64", "Access1F32"),
  ("Janus.Contracts.MapVarAmd64", "Access1Fat"),
  ("Janus.Contracts.MapVarAmd64", "Access1G"),
  ("Janus.Contracts.MapVarAmd64", "Access2F32"),
  ("Janus.Contracts.MapVarAmd64", "Access2Fat"),
  ("Janus.Contracts.MapVarAmd64", "Access2G"),
  ("Janus.Contracts.MapVarAmd64", "Assign64Ptr"),
  ("Janus.Contracts.MapVarAmd64", "AssignF32"),
  ("Janus.Contracts.MapVarAmd64", "AssignG"),
  ("Janus.Contracts.MapVarAmd64", "DeleteF32"),
  ("Janus.Contracts.MapVarAmd64", "DeleteG"),
  ("Janus.Contracts.MapVarAmd64", "MakeMap"),
  ("Janus.Contracts.Mem", "BulkBarrierOff"),
  ("Janus.Contracts.Mem", "Cequal"),
  ("Janus.Contracts.Mem", "Fequal"),
  ("Janus.Contracts.Mem", "Interequal"),
  ("Janus.Contracts.Mem", "MemclrHasPointers"),
  ("Janus.Contracts.Mem", "MemclrNoHeapPointers"),
  ("Janus.Contracts.Mem", "Memequal"),
  ("Janus.Contracts.Mem", "MemequalN"),
  ("Janus.Contracts.Mem", "MemequalVarlen"),
  ("Janus.Contracts.Mem", "Memmove"),
  ("Janus.Contracts.Mem", "Nilinterequal"),
  ("Janus.Contracts.Mem", "Strequal"),
  ("Janus.Contracts.Mem", "TypedMemclr"),
  ("Janus.Contracts.Mem", "TypedMemmove"),
  ("Janus.Contracts.MemAmd64", "BulkBarrierOff"),
  ("Janus.Contracts.MemAmd64", "Cequal"),
  ("Janus.Contracts.MemAmd64", "Fequal"),
  ("Janus.Contracts.MemAmd64", "Interequal"),
  ("Janus.Contracts.MemAmd64", "MemclrHasPointers"),
  ("Janus.Contracts.MemAmd64", "MemclrNoHeapPointers"),
  ("Janus.Contracts.MemAmd64", "Memequal"),
  ("Janus.Contracts.MemAmd64", "MemequalN"),
  ("Janus.Contracts.MemAmd64", "MemequalVarlen"),
  ("Janus.Contracts.MemAmd64", "Memmove"),
  ("Janus.Contracts.MemAmd64", "Nilinterequal"),
  ("Janus.Contracts.MemAmd64", "Strequal"),
  ("Janus.Contracts.MemAmd64", "TypedMemclr"),
  ("Janus.Contracts.MemAmd64", "TypedMemmove"),
  ("Janus.Contracts.Panic", "DeferprocContract"),
  ("Janus.Contracts.Panic", "DeferprocStackContract"),
  ("Janus.Contracts.Panic", "DeferprocatContract"),
  ("Janus.Contracts.Panic", "DeferrangefuncContract"),
  ("Janus.Contracts.Panic", "DeferreturnContract"),
  ("Janus.Contracts.Panic", "GoexitContract"),
  ("Janus.Contracts.Panic", "GopanicContract"),
  ("Janus.Contracts.Panic", "GorecoverContract"),
  ("Janus.Contracts.PanicAmd64", "DeferprocContract"),
  ("Janus.Contracts.PanicAmd64", "DeferprocStackContract"),
  ("Janus.Contracts.PanicAmd64", "DeferprocatContract"),
  ("Janus.Contracts.PanicAmd64", "DeferrangefuncContract"),
  ("Janus.Contracts.PanicAmd64", "DeferreturnContract"),
  ("Janus.Contracts.PanicAmd64", "GoexitContract"),
  ("Janus.Contracts.PanicAmd64", "GopanicContract"),
  ("Janus.Contracts.PanicAmd64", "GorecoverContract"),
  ("Janus.Contracts.Pool", "PoolGetLive"),
  ("Janus.Contracts.Pool", "PoolPutLive"),
  ("Janus.Contracts.PoolAmd64", "PoolGetLive"),
  ("Janus.Contracts.PoolAmd64", "PoolPutLive"),
  ("Janus.Contracts.Print", "Lock2Contract"),
  ("Janus.Contracts.Print", "MemmoveContract"),
  ("Janus.Contracts.Print", "Unlock2Contract"),
  ("Janus.Contracts.PrintAmd64", "Lock2Contract"),
  ("Janus.Contracts.PrintAmd64", "MemmoveContract"),
  ("Janus.Contracts.PrintAmd64", "Unlock2Contract"),
  ("Janus.Contracts.Rt", "RtContract"),
  ("Janus.Contracts.Rt", "RtContract64"),
  ("Janus.Contracts.SoftFloat", "KeepAliveContract"),
  ("Janus.Contracts.SoftFloat", "SoftFaddContract"),
  ("Janus.Contracts.SoftFloat", "SoftFdivContract"),
  ("Janus.Contracts.SoftFloat", "SoftFmulContract"),
  ("Janus.Contracts.SoftFloat", "SoftFsubContract"),
  ("Janus.Contracts.SoftFloatAmd64", "KeepAliveContract64"),
  ("Janus.Contracts.SoftFloatAmd64", "SoftFaddContract64"),
  ("Janus.Contracts.SoftFloatAmd64", "SoftFdivContract64"),
  ("Janus.Contracts.SoftFloatAmd64", "SoftFmulContract64"),
  ("Janus.Contracts.SoftFloatAmd64", "SoftFsubContract64"),
  ("Janus.Contracts.Stack", "MorestackContract"),
  ("Janus.Contracts.StackAmd64", "MorestackContract64"),
  ("Janus.Contracts.Syscall", "ConvT64Contract"),
  ("Janus.Contracts.Syscall", "SchedContract"),
  ("Janus.Contracts.SyscallAmd64", "ConvT64Contract"),
  ("Janus.Contracts.SyscallAmd64", "SchedContract"),
  ("Janus.Contracts.WriteBarrier", "WbContract"),
  ("Janus.Contracts.WriteBarrier", "WbContract64"),
-- END pinnedContracts
  ]

/-- Is `c` a pinned runtime contract: listed, defined in the listed trusted framework module (never a proof or
consumer module), and of the contract shape? -/
def isRuntimeContract (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => false
  | some idx =>
    let mod := env.header.moduleNames[idx.toNat]!
    trustedModule mod && pinnedContracts.contains (mod.toString, c.getString!) &&
    (`Janus).isPrefixOf c && match env.find? c with
    | some (.defnInfo d) => bodyIsSummary d.value ||
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
  [`concatstringsSpec, `concatbytesSpec, `slicebytetostringtmpSpec,
   `stringtoslicebyteSpec, `stringtosliceruneSpec, `slicerunetostringSpec, `intstringSpec,
   `decoderuneSpec, `countrunesSpec, `gostringSpec, `gostringnSpec, `gobytesSpec, `growsliceSpec,
   `growsliceNoAliasSpec, `growsliceBufSpec, `growsliceBufNoAliasSpec, `makeslicecopySpec,
   `moveSliceSpec, `moveSliceNoScanSpec, `moveSliceNoCapSpec, `moveSliceNoCapNoScanSpec,
   `slicecopySpec, `typedslicecopySpec, `wbZeroSpec, `wbMoveSpec,
   -- the live boxing contracts (`Janus.Contracts.IfaceLive`: `convTstring`, `convT64`) and their live data
   `convTstringSpec, `convT64Spec, `convTstringLive, `convT64Live,
   -- the live data of `slicebytetostring` (`RtLiveContract … (slicebytetostringSpec st) slicebytetostringLive`; `st` is
   -- checked as for the plain contract: `frameworkSpecsStatic`)
   `slicebytetostringLive,
   -- the live data of the growslice specs (`LiveSpec`: cost, fresh and kept objects), the second description
   -- argument of `RtLiveContract` (round 15)
   `growsliceLive, `growsliceNoAliasLive, `growsliceBufLive, `growsliceBufNoAliasLive].map (`Janus.Contracts ++ ·)

def frameworkSpecsNat : List Name :=
  [`concatstringSpec, `concatbyteSpec].map (`Janus.Contracts ++ ·)

/-- The address of `runtime.staticuint64s` that `janus extract` names for a `--contract runtime.slicebytetostring`
(`Extracted.dataAddr.«runtime.staticuint64s»`; the extractor checks the object's size and contents, `janus check`
regenerates `Extracted.lean` from the binary). The only argument `slicebytetostringSpec` accepts: another number
(`0`, a variable, an address the statement picks) would say that a one-byte result lives somewhere the runtime never
puts it, and the contract would be one no implementation meets (or, for an address the statement can choose, one
that lets the proof place the result anywhere). -/
def staticuint64sConst : Name := .str `Extracted.dataAddr "runtime.staticuint64s"

/-- Is `k` exactly `Extracted.dataAddr.«runtime.staticuint64s»` (imported from the `Extracted` module)? -/
def isStaticAddr (env : Environment) (k : Expr) : Bool :=
  match k.consumeMData with
  | .const c _ =>
      c == staticuint64sConst &&
      match env.getModuleIdxFor? c with
      | some idx => env.header.moduleNames[idx.toNat]? == some `Extracted
      | none => false
  | _ => false

/-- Is `k` exactly `Extracted.dataAddr.«name»` (imported from the `Extracted` module)? -/
def isExtractedDataAddr (env : Environment) (k : Expr) (name : String) : Bool :=
  match k.consumeMData with
  | .const c _ =>
      c == .str `Extracted.dataAddr name &&
      match env.getModuleIdxFor? c with
      | some idx => env.header.moduleNames[idx.toNat]? == some `Extracted
      | none => false
  | _ => false

/-- The contract `ErrorfLive` (both ISAs): the type descriptors and itabs it names, as the argument positions of
`tErr`, `iErr`, `tInt`, `iWrap` and the `Extracted.dataAddr` constants `janus extract --contract fmt.errorf` generates
for them (the extractor checks the itabs pair `type:error` with the types and finds the descriptor of `int` by
name). Another number would state the result of `fmt.errorf` with an itab or type the binary never uses. -/
def errorfDataArgs : List (Nat × String) :=
  [(4, "type:*errors.errorString"), (5, "go:itab.*errors.errorString,error"), (6, "type:int"),
   (7, "go:itab.*fmt.wrapError,error")]

def isErrorfLive (c : Name) : Bool :=
  c == `Janus.Contracts.Errorf.ErrorfLive || c == `Janus.Contracts.ErrorfAmd64.ErrorfLive

/-- The specs that take the address of `runtime.staticuint64s` (see `isStaticAddr`). -/
def frameworkSpecsStatic : List Name := [`slicebytetostringSpec, `slicebytetostringSpecT].map (`Janus.Contracts ++ ·)

def frameworkFmts : List Name := [`Janus.Float.binary32, `Janus.Float.binary64]

/-- Which allow-listed type is `ty`: `some true` for `RtSpec`, `some false` for `Fmt`. -/
def frameworkConstParamType (ty : Expr) : Option Bool :=
  let ty := ty.consumeMData
  if ty.isConstOf `Janus.Contracts.RtSpec || ty.isConstOf `Janus.Contracts.LiveSpec then some true
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
        (frameworkSpecsNat.contains c && imported c && (k.nat?.isSome || k.rawNatLit?.isSome)) ||
        (frameworkSpecsStatic.contains c && imported c && isStaticAddr env k)
    | _ => false
  else match a with
    | .const c _ => frameworkFmts.contains c && imported c
    | _ => false


/-! ### Spec binding: which runtime function a spec describes

The auditor checks that a spec argument is one of the framework's named constants (above), but not that it
describes the function the contract is stated AT: `RtContract … (contractAddr "runtime.newobject") … growsliceSpec`
verified, and the report said `RtContract@runtime.newobject` (a contract no implementation of `newobject` meets,
labelled as `newobject`'s). The tables below name, for each allow-listed spec, the runtime function(s) whose
contract it is; a contract hypothesis whose address names another function is rejected, and so is a live
contract whose spec and live data are not each other's. -/

/-- The runtime functions each allow-listed `RtSpec` constant (short name, in `Janus.Contracts`) describes. -/
def specRuntimeNames : List (String × List String) :=
  [("concatstringsSpec", ["runtime.concatstrings"]), ("concatbytesSpec", ["runtime.concatbytes"]),
   ("slicebytetostringSpec", ["runtime.slicebytetostring"]), ("slicebytetostringSpecT", ["runtime.slicebytetostring"]),
   ("slicebytetostringtmpSpec", ["runtime.slicebytetostringtmp"]),
   ("stringtoslicebyteSpec", ["runtime.stringtoslicebyte"]), ("stringtosliceruneSpec", ["runtime.stringtoslicerune"]),
   ("slicerunetostringSpec", ["runtime.slicerunetostring"]), ("intstringSpec", ["runtime.intstring"]),
   ("decoderuneSpec", ["runtime.decoderune"]), ("countrunesSpec", ["runtime.countrunes"]),
   ("gostringSpec", ["runtime.gostring"]), ("gostringnSpec", ["runtime.gostringn"]), ("gobytesSpec", ["runtime.gobytes"]),
   ("growsliceSpec", ["runtime.growslice", "runtime.growsliceNoAlias"]),
   ("growsliceNoAliasSpec", ["runtime.growsliceNoAlias", "runtime.growslice"]),
   ("growsliceBufSpec", ["runtime.growsliceBuf", "runtime.growsliceBufNoAlias"]),
   ("growsliceBufNoAliasSpec", ["runtime.growsliceBufNoAlias", "runtime.growsliceBuf"]),
   ("makeslicecopySpec", ["runtime.makeslicecopy"]),
   ("moveSliceSpec", ["runtime.moveSlice"]), ("moveSliceNoScanSpec", ["runtime.moveSliceNoScan"]),
   ("moveSliceNoCapSpec", ["runtime.moveSliceNoCap"]), ("moveSliceNoCapNoScanSpec", ["runtime.moveSliceNoCapNoScan"]),
   ("slicecopySpec", ["runtime.slicecopy"]), ("typedslicecopySpec", ["runtime.typedslicecopy"]),
   ("wbZeroSpec", ["runtime.wbZero"]), ("wbMoveSpec", ["runtime.wbMove"]),
   ("convTstringSpec", ["runtime.convTstring"]), ("convT64Spec", ["runtime.convT64"])]

/-- The allow-listed `LiveSpec` constants and the `RtSpec` each is the live data of. -/
def liveSpecOf : List (String × String) :=
  [("growsliceLive", "growsliceSpec"), ("growsliceNoAliasLive", "growsliceNoAliasSpec"),
   ("growsliceBufLive", "growsliceBufSpec"), ("growsliceBufNoAliasLive", "growsliceBufNoAliasSpec"),
   ("convTstringLive", "convTstringSpec"), ("convT64Live", "convT64Spec"),
   ("slicebytetostringLive", "slicebytetostringSpec"), ("slicebytetostringLive", "slicebytetostringSpecT")]

/-- The short name of a constant of `Janus.Contracts` (`none` for any other). -/
def contractsShort? (c : Name) : Option String :=
  match c with
  | .str p s => if p == `Janus.Contracts then some s else none
  | _ => none

/-- A spec argument (`growsliceSpec`, `concatstringSpec 2`): its printed form and the runtime functions it
describes; `none` when it is not an allow-listed spec. -/
def specInfo? (a : Expr) : Option (String × List String) :=
  match a.consumeMData with
  | .const c _ =>
    match contractsShort? c with
    | some s => (specRuntimeNames.find? (·.1 == s)).map fun (_, ns) => (s, ns)
    | none => none
  | .app (.const c _) k =>
    match contractsShort? c, (k.nat? <|> k.rawNatLit?) with
    | some "concatstringSpec", some n => some (s!"concatstringSpec {n}", [s!"runtime.concatstring{n}"])
    | some "concatbyteSpec", some n => some (s!"concatbyteSpec {n}", [s!"runtime.concatbyte{n}"])
    | _, _ => none
  | _ => none

/-- `slicebytetostringSpec st` (`st` any term): the printed form and the function; the argument itself is
checked by `isFrameworkConstArg`. -/
def specStaticInfo? (a : Expr) : Option (String × List String) :=
  match a.consumeMData with
  | .app (.const c _) _ =>
    match contractsShort? c with
    | some "slicebytetostringSpec" => some ("slicebytetostringSpec", ["runtime.slicebytetostring"])
    | some "slicebytetostringSpecT" => some ("slicebytetostringSpecT", ["runtime.slicebytetostring"])
    | _ => none
  | _ => none

/-- A live-data argument (`growsliceLive`): its short name and the specs it belongs to (`slicebytetostringLive`: the plain spec and
the one with the identity table in its precondition). -/
def liveInfo? (a : Expr) : Option (String × List String) :=
  match a.consumeMData with
  | .const c _ =>
    match contractsShort? c with
    | some s =>
      let owners := (liveSpecOf.filter (·.1 == s)).map (·.2)
      if owners.isEmpty then none else some (s, owners)
    | none => none
  | _ => none

/-- The runtime function a dedicated contract is about, from its name (`NewobjectContract64` → `runtime.newobject`;
`WbContract` → the prefix `runtime.gcWriteBarrier`). The generic `RtContract` and `RtLiveContract` take it from their spec. -/
def contractFunction? (c : Name) : Option (String × Bool) :=
  let s := c.getString!
  let base := (if s.endsWith "64" then s.dropRight 2 else s)
  match base with
  | "NewobjectContract" | "NewobjectLiveContract" => some ("runtime.newobject", false)
  | "MakesliceContract" | "MakesliceLiveContract" => some ("runtime.makeslice", false)
  | "MallocgcContract" | "MallocgcLiveContract" => some ("runtime.mallocgc", false)
  | "GrowsliceContract" | "GrowsliceLiveContract" => some ("runtime.growslice", false)
  | "ErrorfLive" => some ("fmt.errorf", false)
  | "WbContract" | "WbLiveContract" => some ("runtime.gcWriteBarrier", true)
  | _ => none

/-- The string literal of the `contractAddr P "name"` application among the arguments of a contract hypothesis,
with its program argument. -/
def contractAddrOf? (app : Expr) : Option (Expr × String) :=
  let isAddr (x : Expr) : Bool :=
    (x.getAppFn.isConstOf `Janus.Program.contractAddr || x.getAppFn.isConstOf `Janus.Amd64.Program.contractAddr) &&
      x.getAppNumArgs == 2 && (match x.appArg! with | .lit (.strVal _) => true | _ => false)
  match app.find? isAddr with
  | some x => (match x.appArg! with | .lit (.strVal a) => some (x.appFn!.appArg!.consumeMData, a) | _ => none)
  | none => none

/-- The spec and live data a contract application names, as printed in the report (`growsliceSpec`,
`growsliceSpec/growsliceLive`; empty for a contract without them). -/
def specLabel (app : Expr) : String :=
  let parts := app.getAppArgs.filterMap fun a =>
    match specInfo? a <|> specStaticInfo? a with
    | some (l, _) => some l
    | none => (liveInfo? a).map (·.1)
  "/".intercalate parts.toList

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

/-- U-ICALL: exactly `Extracted.program.contractAddr "name"` (either ISA): the address of a `--contract` stub that the
extraction itself lists in `Extracted.contracts` (the existing symbol-reference check requires `name` to be one: an
absent name would make the address `0`). That code is not extracted and not the theorem's own: the weak ABI-only
contract is the honest assumption about it. -/
def isStubAddrLit (e : Expr) : Bool :=
  let e := e.consumeMData
  (e.getAppFn.isConstOf `Janus.Program.contractAddr || e.getAppFn.isConstOf `Janus.Amd64.Program.contractAddr) &&
    e.getAppNumArgs == 2 && (e.getArg! 0).consumeMData.isConstOf `Extracted.program &&
    (match (e.getArg! 1).consumeMData with | .lit (.strVal _) => true | _ => false)

/-- U-ICALL-STACK: the natural number a closed term denotes, after instantiating metavariables, zeta-reducing `let`s, folding
literal arithmetic (`2 ^ 48`, `2 ^ 47 * 2`, `Nat.pow 2 48`) and unfolding definitions (a def-wrapped constant): `none` for a term
that is not a closed natural number (a variable, an application of an unknown function). -/
partial def icallNatValue? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if e.hasLooseBVars then return none
  let e ← Meta.zetaReduce e
  let e := e.consumeMData
  if e.hasFVar then
    -- a `let`-bound local: its value
    if let .fvar v := e then
      if let some val := (← v.getDecl).value? then return ← icallNatValue? val
    return none
  if let some n := e.rawNatLit? then return some n
  if let some n ← (Meta.evalNat e).run then return some n
  let e' ← Meta.withTransparency .all (Meta.whnf e)
  if e'.consumeMData != e then
    if let some n := e'.consumeMData.rawNatLit? then return some n
    if let some n ← (Meta.evalNat e').run then return some n
  return none

/-- The abstract-callee contracts (U-ICALL): `ICallContract`, `ICallContract64`. -/
def isICallContract (c : Name) : Bool :=
  c == `Janus.Contracts.ICall.ICallContract || c == `Janus.Contracts.ICall.ICallContract64

/- U-ICALL: NO premise of the theorem may constrain `rt` through `Outside a n rt` (red team B3-B6): `Outside 0 2^48 rt`, or two such
premises covering the address space, force `rt = []` ("the callee writes nothing"). The caller's own frame is stated in the
`Ensures` precondition (over the entry state), where it is an obligation, not an assumption. -/

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

/-! ## Round 14 (V2): the runtime of a MAIN theorem is quantified, never chosen

Round 10 V1 inspects `link` only inside contract applications. A statement about
`Extracted.program.link impl` for a CONCRETE `impl` (the consumer's own toy allocator, say) with no
contract hypothesis at all was therefore accepted, and the report claimed the runtime contract as
"assumed" although the theorem assumes nothing about the runtime and says nothing about the real
one. The rule: in a main (non-`Witness`) theorem the implementation of the runtime enters the
statement ONLY as `Extracted.program.link impl` for a variable `impl` bound by the statement itself,
and `impl` is constrained only by the pinned contracts and model laws (the V1 premise check, which
now also covers an `impl` that no contract mentions). Witness theorems (`…Witness.nonvacuous`,
`…Witness.returns`) exhibit concrete instances by design and are checked structurally instead
(`checkWitness`). Every check here only rejects. -/

/-- `List Segment` of either ISA. -/
def isSegListType (t : Expr) : Bool :=
  match t.consumeMData with
  | .app (.const ``List _) a =>
      a.consumeMData.isConstOf `Janus.Segment || a.consumeMData.isConstOf `Janus.Amd64.Segment
  | _ => false

def isProgramType (t : Expr) : Bool :=
  t.consumeMData.isConstOf `Janus.Program || t.consumeMData.isConstOf `Janus.Amd64.Program

def isStateType (t : Expr) : Bool :=
  t.consumeMData.isConstOf `Janus.Arm64.State || t.consumeMData.isConstOf `Janus.Amd64.State

def linkNames : List Name := [`Janus.Program.link, `Janus.Amd64.Program.link]

/-- `Program.ofImpl P impl`: the program with no user code, only the runtime's segments. It may be the program of
a runtime contract hypothesis (with the same discipline as `link`), never anything else (round 15, internal
calls): a contract about the runtime's own code transports forward to `link impl` (`….of_codeIn`). -/
def ofImplNames : List Name := [`Janus.Program.ofImpl, `Janus.Amd64.Program.ofImpl]

/-- `ImplApart P impl`: the runtime's code does not overlap the extracted code (round 15). -/
def implApartNames : List Name := [`Janus.ImplApart, `Janus.Amd64.ImplApart]

/-- Is `t` EXACTLY `ImplApart Extracted.program v` for a variable `v` (of the trusted module)? This is the only
premise the auditor allows on a runtime implementation variable besides the pinned contracts and model laws:
"the runtime's code does not overlap the extracted function's code". -/
def isImplApartPremise (env : Environment) (t : Expr) : Bool :=
  let t := t.consumeMData
  match t.getAppFn with
  | .const c _ =>
    implApartNames.contains c && t.getAppNumArgs == 2 &&
      (t.getArg! 0).consumeMData.isConstOf `Extracted.program && (t.getArg! 1).consumeMData.isFVar &&
      (match env.getModuleIdxFor? c with
        | some idx => trustedModule env.header.moduleNames[idx.toNat]!
        | none => false)
  | _ => false

/-- The linking forms through which an implementation variable may occur. -/
def implFormNames : List Name := linkNames ++ ofImplNames

/-- Constants that build a program or a segment by hand: not available to a main theorem. -/
def handBuiltNames : List Name := [`Janus.Program.mk, `Janus.Amd64.Program.mk]

/-- `Extracted.program.segments` / `.stubs`: the extraction's own code and stubs, not an implementation of the
runtime. -/
def isExtractedField (e : Expr) : Bool :=
  match e.consumeMData with
  | .app (.const c _) a => [`Janus.Program.segments, `Janus.Amd64.Program.segments, `Janus.Program.stubs,
        `Janus.Amd64.Program.stubs].contains c && a.consumeMData.isConstOf `Extracted.program
  | .proj s i a => (s == `Janus.Program || s == `Janus.Amd64.Program) && i < 2 &&
      a.consumeMData.isConstOf `Extracted.program
  | _ => false

/-- The programs a main statement may speak about: `Extracted.program`, the program with an exit
address (`withExit`) and the linked program (checked separately). -/
def programHeadOk (c : Name) : Bool :=
  c == `Extracted.program || c == `Janus.Program.withExit || c == `Janus.Amd64.Program.withExit ||
    linkNames.contains c || handBuiltNames.contains c

/-- The variables `impl` of `Extracted.program.link impl` in `e`. -/
partial def linkVars (e : Expr) (acc : Array FVarId := #[]) : Array FVarId :=
  match e with
  | .app .. =>
    let acc := if e.getAppFn.isConst && implFormNames.any e.getAppFn.isConstOf && e.getAppNumArgs == 2 then
        match (e.getArg! 1).consumeMData with
        | .fvar v => acc.push v
        | _ => acc
      else acc
    let acc := linkVars e.getAppFn acc
    e.getAppArgs.foldl (fun acc a => linkVars a acc) acc
  | .lam _ d b _ | .forallE _ d b _ => linkVars b (linkVars d acc)
  | .letE _ t v b _ => linkVars b (linkVars v (linkVars t acc))
  | .mdata _ b | .proj _ _ b => linkVars b acc
  | _ => acc


/-- The variables `impl` of `Extracted.program.link impl` in the statement outside its runtime-contract hypotheses
(spec binding: the implementation the statement runs; a contract must be about the same one). -/
partial def runVars (env : Environment) (e : Expr) (acc : Array FVarId := #[]) : Array FVarId :=
  match e with
  | .app .. =>
    if e.getAppFn.isConst && (match e.getAppFn with | .const c _ => isRuntimeContract env c | _ => false) then acc
    else
      let acc := if e.getAppFn.isConst && linkNames.any e.getAppFn.isConstOf && e.getAppNumArgs == 2 then
          match (e.getArg! 1).consumeMData with
          | .fvar v => acc.push v
          | _ => acc
        else acc
      let acc := runVars env e.getAppFn acc
      e.getAppArgs.foldl (fun acc a => runVars env a acc) acc
  | .lam _ d b _ | .forallE _ d b _ => runVars env b (runVars env d acc)
  | .letE _ t v b _ => runVars env b (runVars env v (runVars env t acc))
  | .mdata _ b | .proj _ _ b => runVars env b acc
  | _ => acc

/-- Round 14 (V2): is the runtime implementation of the statement `e` anything other than a variable
bound by the statement? `outer` are the statement's own binders (as free variables). A term of type
`List Segment` must be one of them; `Program.link` must be `Extracted.program.link <outer
variable>`; programs and segments are not built by hand; every program is `Extracted.program`,
`withExit` of one, or a linked one. -/
partial def concreteRuntime (outer : Std.HashSet FVarId) (e : Expr) : MetaM (Option String) := do
  let show_ (e : Expr) : MetaM String := do pure ((← Meta.ppExpr e).pretty 200)
  let tyOf (e : Expr) : MetaM (Option Expr) := do
    try pure (some (← Meta.whnfR (← Meta.inferType e))) catch _ => pure none
  if isExtractedField e then return none
  match e with
  | .mdata _ b => concreteRuntime outer b
  | .proj _ _ b =>
    if let some t ← tyOf e then
      if isSegListType t then
        return some s!"mentions a runtime implementation (`{← show_ e}`, a `List Segment`) that is not a variable of the statement (round 14)"
    concreteRuntime outer b
  | .fvar v =>
    if let some t ← tyOf e then
      if isSegListType t && !outer.contains v then
        return some s!"quantifies a runtime implementation (`{← show_ e}`, a `List Segment`) inside the statement (an `∃` or a lambda): the implementation must be a variable of the whole statement (round 14)"
    return none
  | .const c _ =>
    if handBuiltNames.contains c || implFormNames.contains c then
      return some s!"uses {c} unapplied: a program is `Extracted.program` or `Extracted.program.link impl` for a variable `impl` of the statement (round 14)"
    if let some t ← tyOf e then
      if isSegListType t then
        return some s!"mentions the concrete runtime implementation `{c}` (a `List Segment`): a main theorem quantifies the implementation (a variable `impl` constrained only by the runtime contracts) instead of choosing one (round 14)"
      if isProgramType t && !programHeadOk c then
        return some s!"mentions the program `{c}`, which is not `Extracted.program` (round 14)"
    return none
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := fn then
      -- Round 15 (internal calls): `Program.ofImpl` (the runtime's code alone, no user code) is the program of a
      -- runtime contract hypothesis, with the same discipline as `link`: `Extracted.program.ofImpl impl`, `impl` a
      -- variable of the statement. It is not the program of a statement about the extracted function.
      if ofImplNames.contains c then
        return some s!"mentions `{← show_ e}`: `Program.ofImpl` (the runtime's code alone) is only the program of a runtime contract hypothesis (`… (Extracted.program.ofImpl impl) …`), never of a statement about the extracted function (round 15)"
      if isRuntimeContract (← getEnv) c then
        for a in args do
          let a' := a.consumeMData
          if a'.getAppFn.isConst && ofImplNames.any a'.getAppFn.isConstOf then
            let ok := a'.getAppNumArgs == 2 && (a'.getArg! 0).consumeMData.isConstOf `Extracted.program &&
              match (a'.getArg! 1).consumeMData with | .fvar v => outer.contains v | _ => false
            unless ok do
              return some s!"mentions `{← show_ a'}`: a runtime contract may be assumed about `Extracted.program.ofImpl impl` only for a variable `impl` of the statement (round 15)"
          else if let some m ← concreteRuntime outer a then return some m
        return none
      if linkNames.contains c then
        let ok := args.size == 2 && (args[0]!.consumeMData).isConstOf `Extracted.program &&
          match (args[1]!).consumeMData with | .fvar v => outer.contains v | _ => false
        unless ok do
          return some s!"mentions `{← show_ e}`: a main theorem may link only a variable of the statement (`Extracted.program.link impl`, `impl` a binder of the theorem constrained by the runtime contracts), never a concrete implementation (round 14)"
        return none
      -- `{ Extracted.program with data := … }` (a precondition about the program's read-only data) keeps the
      -- extraction's segments and stubs; any other `Program.mk` chooses the code
      if handBuiltNames.contains c && !(args.size ≥ 2 && isExtractedField args[0]! && isExtractedField args[1]!) then
        return some s!"builds a program by hand (`{← show_ e}`) with {c}: a main theorem speaks about `Extracted.program` (segments and stubs as extracted) linked with a variable `impl` (round 14)"
    if !e.hasLooseBVars then
      if let some t ← tyOf e then
        if isSegListType t then
          return some s!"mentions a concrete runtime implementation (`{← show_ e}`, a `List Segment`) that is not a variable of the statement: a main theorem quantifies the implementation (a variable `impl` constrained only by the runtime contracts) instead of choosing one (round 14)"
        if isProgramType t then
          match fn with
          | .const c _ => unless programHeadOk c do
              return some s!"mentions the program `{← show_ e}`, which is not `Extracted.program`, `.withExit` or `.link impl` of one (round 14)"
          | _ => return some s!"mentions the program `{← show_ e}`, which is not `Extracted.program`, `.withExit` or `.link impl` of one (round 14)"
    if !fn.isConst then
      if let some m ← concreteRuntime outer fn then return some m
    for a in args do
      if let some m ← concreteRuntime outer a then return some m
    return none
  | .lam n d b bi | .forallE n d b bi =>
    if let some m ← concreteRuntime outer d then return some m
    Meta.withLocalDecl n bi d fun x => concreteRuntime outer (b.instantiate1 x)
  | .letE n t v b _ =>
    -- `{ Extracted.program with data := … }` elaborates to `let src := Extracted.program; { segments := src.segments, … }`
    if v.consumeMData.isConstOf `Extracted.program then return ← concreteRuntime outer (b.instantiate1 v)
    if let some m ← concreteRuntime outer t then return some m
    if let some m ← concreteRuntime outer v then return some m
    Meta.withLetDecl n t v fun x => concreteRuntime outer (b.instantiate1 x)
  | _ => return none

/-- The first variable of `ivs` that occurs in `e` other than as the argument of `Program.link`. -/
partial def strayImpl (ivs : Std.HashSet FVarId) (e : Expr) : Option FVarId :=
  match e with
  | .fvar v => if ivs.contains v then some v else none
  | .app .. =>
    let fn := e.getAppFn
    if fn.isConst && implFormNames.any fn.isConstOf && e.getAppNumArgs == 2 && (e.getArg! 1).consumeMData.isFVar then none
    else e.getAppArgs.foldl (fun r a => r <|> strayImpl ivs a) (strayImpl ivs fn)
  | .lam _ d b _ | .forallE _ d b _ => strayImpl ivs d <|> strayImpl ivs b
  | .letE _ t v b _ => strayImpl ivs t <|> strayImpl ivs v <|> strayImpl ivs b
  | .mdata _ b | .proj _ _ b => strayImpl ivs b
  | _ => none

/-- `e` is a read of the memory word at the entry `RSP` (`Memory.readLE m (… State.regs s 4 …) n`, the saved return
address `[RSP]`), in any form. -/
def isSpRead (e : Expr) : Bool :=
  e.getAppFn.constName? == some `Janus.Arm64.Memory.readLE && e.getAppNumArgs ≥ 3 &&
    ((e.getArg! 1).find? fun x => x.getAppFn.constName? == some `Janus.Amd64.State.regs &&
      x.getAppNumArgs == 2 && ((x.getArg! 1).nat? == some 4 ||
        (x.getArg! 1).constName?.any (·.getString! == "regSP"))).isSome

/-- The framework's standard ABI predicates are opaque to the analysis below (see `abiPredicates`). -/
def abiNames : List Name :=
  [`Janus.Contracts.CallOK64, `Janus.Contracts.StackRoom64,
   `Janus.GoABI.CallSetup, `Janus.GoABI.RetAddr, `Janus.GoABI.StackWritable, `Janus.GoABI.StackGuardOK,
   `Janus.Amd64.GoABI.CallSetup, `Janus.Amd64.GoABI.RetAddr, `Janus.Amd64.GoABI.StackWritable,
   `Janus.Amd64.GoABI.StackGuardOK]

/-- by EXACT full name (a name the framework already declares cannot be redeclared by a proof file), never by a
prefix or a last component: a proof's own `def Janus.Sneak.CallSetup` is not an ABI predicate -/
def isAbiName (n : Name) : Bool := abiNames.contains n

/-- Does the definition `c` read the word at `[RSP]`, directly or through the definitions it uses (transitively)?
Memoised per constant (`cache`), so the cost is one traversal of each definition, not of each use; the ABI predicates
and the core library (`Init`/`Std`/`Lean`) are opaque. A definition under analysis counts as not reading (cycles). -/
partial def constReadsSp (cache : IO.Ref (Std.HashMap Name Bool)) (c : Name) : MetaM Bool := do
  if let some r := (← cache.get)[c]? then return r
  if isAbiName c then return false
  let env ← getEnv
  if let some mi := env.getModuleIdxFor? c then
    let m := env.header.moduleNames[mi.toNat]!
    if m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean then
      cache.modify (·.insert c false); return false
  cache.modify (·.insert c false)
  let some (.defnInfo d) := env.find? c | return false
  let mut r := (d.value.find? isSpRead).isSome
  if !r then
    for u in d.value.getUsedConstants do
      if ← constReadsSp cache u then r := true; break
  cache.modify (·.insert c r)
  return r

/-- Does the conjunct `e` read the word at `[RSP]`: itself (any spelling, under binders, in arithmetic or an existential) or
through a definition it mentions (alias, framework predicate that is not one of the ABI predicates)? Semantic, not
syntactic. -/
def mentionsSpWord (cache : IO.Ref (Std.HashMap Name Bool)) (e : Expr) : MetaM Bool := do
  if (e.find? isSpRead).isSome then return true
  for u in e.getUsedConstants do
    if ← constReadsSp cache u then return true
  return false

/-- `c` is (an application of) one of the framework's standard ABI preconditions: they say `[RSP]` is the return address (a
word below `2^47`), which every consumer legitimately assumes of its caller. A top-level precondition conjunct that is one
of these is allowed without unfolding; every other conjunct must not read the word at `[RSP]`. -/
def isAbiPredicate (c : Expr) : Bool :=
  c.getAppFn.constName?.any isAbiName

/-- the conjuncts of a precondition body (`A ∧ B ∧ …`), under the `fun s =>` binder -/
partial def conjuncts (e : Expr) : List Expr :=
  match e with
  | .mdata _ b => conjuncts b
  | _ => if e.isAppOfArity ``And 2 then conjuncts (e.getArg! 0) ++ conjuncts (e.getArg! 1) else [e]

/-- The precondition argument of every `Ensures p entry args pre post` in `ty`. -/
partial def ensuresPres (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc := if (e.getAppFn.constName?.any fun n => n == `Janus.GoABI.Ensures || n == `Janus.Amd64.GoABI.Ensures) && e.getAppNumArgs == 5 then acc.push (e.getArg! 3) else acc
  match e with
  | .app f a => ensuresPres a (ensuresPres f acc)
  | .lam _ d b _ | .forallE _ d b _ => ensuresPres b (ensuresPres d acc)
  | .letE _ ty v b _ => ensuresPres b (ensuresPres v (ensuresPres ty acc))
  | .mdata _ b | .proj _ _ b => ensuresPres b acc
  | _ => acc

/-- Round 10 V1: check the contract premises of the statement `ty` (see the section comment).
Round 14 (V2): with `main` (the default; every theorem that is not a `Witness.nonvacuous`/`Witness.returns`)
the runtime implementation must also be a variable of the statement (`concreteRuntime`) and every such
`impl` is a runtime variable even when no contract mentions it. -/
def checkContractHyps (ty : Expr) (main : Bool := true) : MetaM (Option String) := do
  let env ← getEnv
  -- a bound on the caller's return address: any top-level precondition that reads the memory word at the entry `RSP`
  -- (`[RSP]`; `ErrorfAmd64.RetLow` is one) weakens the guarantee without the reader seeing it. A consumer proves such facts
  -- inside its proof from the return address its own `call` pushes. Hypotheses (contract statements) are not scanned.
  -- (the statement's binders and `fun s => …` become free variables: no loose bound variable reaches `whnf`)
  let spCache ← IO.mkRef ({} : Std.HashMap Name Bool)
  let spHit ← Meta.forallTelescope ty fun _ stmt => do
    for pre in ensuresPres stmt do
      let bad ← Meta.lambdaTelescope pre fun _ body => do
        for c in conjuncts body do
          unless isAbiPredicate c do
            if ← mentionsSpWord spCache c then return true
        return false
      if bad then return true
    return false
  do
    if spHit then
       return some "the precondition constrains the memory word at the entry `RSP` (the saved return address `[RSP]`, e.g. `ErrorfAmd64.RetLow`, in any form: alias, arithmetic, existential): a theorem must not assume a bound on its caller's return address; a consumer discharges such a fact inside its proof from the return address its own `call` pushes (a code address of the extracted program)"
  Meta.forallTelescope ty fun xs body => do
    let bound : Std.HashSet FVarId := xs.foldl (fun s x => s.insert x.fvarId!) {}
    let mut rtVars : Std.HashSet FVarId := {}
    let mut sizeVars : Array (String × FVarId × Nat) := #[]  -- U-ICALL-STACK: variables used as nargs/stack/above
    let mut icallFns : Array FVarId := #[]  -- U-ICALL: the callee-address variables of the abstract-callee contracts
    let mut icallFree : Array Expr := #[]  -- U-ICALL: the `P` and `keep` arguments, checked once `rtVars` is complete
    -- the implementation variables no recognised contract mentions (round 14)
    let mut implOnly : Std.HashSet FVarId := {}
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
      -- Round 14 (rt-auditv2, F5): only a WITNESS exhibits contracts under an `∃` (its claim); in a main theorem
      -- an `∃`-bound contract in the conclusion (a precondition `∃ H, Contract … [] 4096 H`) is checked like any other
      concl.foldl (fun acc t => contractApps env t acc (claims := !main)) #[]
    -- Spec binding: the implementation variables the statement itself runs (`Extracted.program.link impl`)
    let mut stmtImpls : Array FVarId := runVars env body
    for (_, t) in premises do stmtImpls := runVars env t stmtImpls
    for x in xs do
      let t ← instantiateMVars (← Meta.inferType x)
      unless ← Meta.isProp t do stmtImpls := runVars env t stmtImpls
    for app in apps do
      let .const c _ := app.getAppFn | continue
      let some ci := env.find? c | continue
      let doms := binderDomains ci.type #[]
      let args := app.getAppArgs
      if args.size < doms.size then
        return some s!"applies the runtime contract {c} partially (round 10 V1)"
      -- U-ICALL-STACK (red team B12, B18, B19, V01-V15, F01-F11): contract argument well-formedness. The arguments named
      -- `stack` (`d` in the memequal/memhash/memmove/typed-copy families), `nargs` and `above` (every contract family: ICallContract[64], RtContract[64], RtLiveContract[64],
      -- NewobjectContract[64], NewobjectLiveContract[64], …) gate the satisfiability of the call precondition (`CallOK`: a stack
      -- window `[SP - stack, SP + 8 + 8·nargs)` that fits in the address space; `stack ≥ 8`; the caller frame `above ≥ 8 + 8·nargs`).
      -- Each is EITHER a closed term that evaluates (literals, `^`, `*`, `let`s, unfolded definitions) into the satisfiable range
      -- (8 ≤ stack < 2^47; nargs ≤ 64; 8 + 8·nargs ≤ above < 2^47), OR a variable of the statement that no theorem premise
      -- constrains beyond a numeral lower bound (checked once the premises are known); anything else could make the contract
      -- hold vacuously.
      let bnames := forallBinderNames ci.type #[]
      let mut nargsV : Option Nat := none
      for i in [0:bnames.size] do
        if bnames[i]! == `nargs then nargsV := ← icallNatValue? args[i]!
      for i in [0:bnames.size] do
        let nm := bnames[i]!.toString
        unless nm == "stack" || nm == "d" || nm == "nargs" || nm == "above" do continue
        let a := args[i]!.consumeMData
        let limit := if nm == "nargs" then 64 else 2 ^ 47
        match (← icallNatValue? a) with
        | some n =>
          let low := if nm == "stack" then 8 else if nm == "above" then 8 + 8 * (nargsV.getD 0) else 0
          if n < low || (nm != "nargs" && n ≥ limit) || (nm == "nargs" && n > limit) then
            return some s!"assumes the runtime contract {c} with the {nm} `{(← Meta.ppExpr a).pretty 10000}` = {n}, outside the satisfiable range ({if nm == "nargs" then "at most 64" else if nm == "stack" then "8 ≤ stack < 2^47" else s!"{low} ≤ above < 2^47"}): the call precondition would be unsatisfiable, so the hypothesis would hold vacuously (U-ICALL-STACK)"
        | none =>
          if isVar a then sizeVars := sizeVars.push (nm, a.fvarId!, limit)
          else
            return some s!"assumes the runtime contract {c} with the {nm} `{(← Meta.ppExpr a).pretty 10000}`, which is neither a closed numeral term nor a variable of the statement: its value could make the call precondition unsatisfiable (U-ICALL-STACK)"
      -- Spec binding: the spec (and live data) a contract carries must describe the function it is stated at
      if let some (prog, fn) := contractAddrOf? app then
        unless prog.isConstOf `Extracted.program do
          return some s!"assumes the runtime contract {c} at the address of `{fn}` in the program `{(← Meta.ppExpr prog).pretty 10000}`, which is not `Extracted.program`: a contract is stated at the extraction's own contract address (spec binding)"
        let mut specSeen := false
        for i in [0:doms.size] do
          if doms[i]!.consumeMData.isConstOf `Janus.Contracts.RtSpec then
            if let some (lbl, names) := (specInfo? args[i]! <|> specStaticInfo? args[i]!) then
              specSeen := true
              unless names.contains fn do
                return some s!"assumes the runtime contract {c} at the address of `{fn}` with the spec `{lbl}`, which describes {" / ".intercalate names}: the spec of another runtime function makes the contract one that no implementation of `{fn}` meets, labelled as `{fn}`'s (spec binding)"
        for i in [0:doms.size] do
          if doms[i]!.consumeMData.isConstOf `Janus.Contracts.LiveSpec then
            if let some (live, owner) := liveInfo? args[i]! then
              -- the live data must be those of the spec argument of the same contract
              let mut okPair := false
              for j in [0:doms.size] do
                if doms[j]!.consumeMData.isConstOf `Janus.Contracts.RtSpec then
                  if let some (lbl, _) := (specInfo? args[j]! <|> specStaticInfo? args[j]!) then
                    if owner.contains lbl then okPair := true
              unless okPair do
                return some s!"assumes the runtime contract {c} with the live data `{live}`, which belong to the spec `{" / ".intercalate owner}`, not to the spec of this contract: a spec and live data of different runtime functions describe no real call (spec binding)"
        if !specSeen then
          if let some (want, isPrefix) := contractFunction? c then
            unless (if isPrefix then fn.startsWith want else fn == want) do
              return some s!"assumes the runtime contract {c}, the contract of `{want}`, at the address of `{fn}` (spec binding)"
      if isErrorfLive c then
        for (i, nm) in errorfDataArgs do
          unless isExtractedDataAddr env args[i]! nm do
            return some s!"assumes the runtime contract {c} for the argument `{(← Meta.ppExpr args[i]!).pretty 10000}` where it takes `Extracted.dataAddr.«{nm}»` (the address of that type descriptor or itab in the binary, generated and checked by `janus extract --contract fmt.errorf`): any other number states the result of fmt.errorf with a type or itab the binary does not use"
      for i in [0:doms.size] do
        let a := args[i]!.consumeMData
        if let some isSpec := frameworkConstParamType doms[i]! then
          unless isFrameworkConstArg env isSpec a do
            return some s!"assumes the runtime contract {c} for the argument `{(← Meta.ppExpr a).pretty 10000}`, which is not one of the framework's named {if isSpec then "runtime-function specs (`concatstringSpec 2`, `growsliceSpec`, …)" else "float formats (`binary32`, `binary64`)"}: the function or format a contract describes cannot be chosen by the statement, not even from imported parts such as `default` (round 11)"
          continue
        -- U-ICALL: the call-site property `P` and the kept ranges `keep` of an abstract-callee contract are the
        -- STATEMENT's claims about the call (a precondition the consumer proves at the call, and bytes it asks the
        -- callee to leave alone), not assumptions about the runtime's data: `P := False` only makes the hypothesis
        -- weaker, and every `keep` is met by a callee that writes nothing. They are closed terms by design; the
        -- runtime parameters of the contract (`impl`, `rt`, the result relation `R`) keep the variable rule.
        if isICallContract c then
          -- the target address of the callee is a variable of the statement: a numeral or an expression (the address of
          -- an extracted function, `Extracted.entry`) would make the hypothesis a static contract about code the
          -- statement can choose, false for the real code at that address (U-ICALL red team)
          if i == 1 && !isVar a && !isStubAddrLit a then
            return some s!"assumes the abstract-callee contract {c} at the address `{(← Meta.ppExpr a).pretty 10000}`, which is neither a variable of the statement (a dynamic callee: the address is a parameter of the theorem, linked to the call by the itab word) nor `Extracted.program.contractAddr \"name\"` (a static call to a non-extracted function the extraction lists as a `--contract` stub); an extracted function's address, `Extracted.entry` and a numeral are never accepted (U-ICALL)"
          if i == 1 && isVar a then icallFns := icallFns.push a.fvarId!
          if i == 6 || i == 8 then
            icallFree := icallFree.push a
            continue
          -- U-ICALL-PRESERVES: `preserves` is the callee's disclosed assumption about the runtime it leaves behind. Exactly two
          -- forms: `fun _ _ => True` (nothing assumed, the default), or `RtPreserves R2` (`RtPreserves64 R2` on amd64) for a
          -- VARIABLE `R2` of the statement (then a runtime variable: the usual rules for runtime variables apply to it).
          -- Anything else (a lambda that constrains bytes, values or registers, `False`, a closed model, an eta-expanded
          -- `RtPreserves`, an extra argument) is a post smuggled into the hypothesis and is rejected; a separate premise
          -- of the same shape is rejected by the premise rule below (it mentions a runtime variable and is no contract).
          if i == 9 then
            let isTrue := match a.consumeMData with
              | .lam _ _ (.lam _ _ b _) _ => b.consumeMData.isConstOf ``True
              | _ => false
            let rtp := if c == `Janus.Contracts.ICall.ICallContract then `Janus.Contracts.ICall.RtPreserves
              else `Janus.Contracts.ICall.RtPreserves64
            if isTrue then continue
            if a.isAppOfArity rtp 1 && isVar (a.getArg! 0).consumeMData then
              rtVars := rtVars.insert (a.getArg! 0).consumeMData.fvarId!
              continue
            return some s!"assumes the abstract-callee contract {c} with the `preserves` argument `{(← Meta.ppExpr a).pretty 10000}`, which is neither `fun _ _ => True` (nothing assumed) nor `{rtp.getString!} R2` for a runtime model variable `R2` of the statement: `preserves` may only say that the callee keeps the runtime's invariant, never constrain bytes, values or registers (U-ICALL-PRESERVES)"
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
          let ok := (implFormNames.any fun n => a.isAppOfArity n 2) &&
            (a.getArg! 0).isConstOf `Extracted.program && isVar (a.getArg! 1).consumeMData
          -- the `morestack` contracts are relations over the call state at a `morestack` stub:
          -- there is no implementation code to link (the program is only consulted through
          -- `stubAt`, which `link` does not change), so they may be stated about
          -- `Extracted.program` itself
          let noCode := (c == `Janus.Contracts.Stack.MorestackContract ||
            c == `Janus.Contracts.StackAmd64.MorestackContract64) && a.isConstOf `Extracted.program
          if noCode then continue
          unless ok do
            return some s!"assumes the runtime contract {c} about the program `{(← Meta.ppExpr a).pretty 10000}`, which is not `Extracted.program.link impl` (or `Extracted.program.ofImpl impl`) for a variable `impl` of the statement (round 10 V1, round 15)"
          -- Spec binding: the contract is about the implementation the statement runs, not another variable's
          if main && !stmtImpls.isEmpty && !stmtImpls.contains (a.getArg! 1).consumeMData.fvarId! then
            return some s!"assumes the runtime contract {c} about the runtime implementation `{(← Meta.ppExpr (a.getArg! 1)).pretty 10000}`, but the statement runs `Extracted.program.link {(← Meta.ppExpr (Expr.fvar stmtImpls[0]!)).pretty 10000}`: a contract about another implementation variable says nothing about the runtime the theorem quantifies (spec binding)"
          rtVars := rtVars.insert (a.getArg! 1).consumeMData.fvarId!
        | none => pure ()
    -- Round 14 (V2): a main theorem never chooses the implementation of the runtime
    if main then
      if let some m ← concreteRuntime bound body then return some m
      for x in xs do
        if let some m ← concreteRuntime bound (← instantiateMVars (← Meta.inferType x)) then return some m
      let mut ivs := linkVars body
      for x in xs do
        ivs := linkVars (← instantiateMVars (← Meta.inferType x)) ivs
      -- Round 14 (rt-auditv2, F4): the implementation variable occurs only as the argument of
      -- `Extracted.program.link`: a precondition about it (`impl.length = 0`, `Pin impl`) would pin the
      -- code the theorem quantifies without being a premise
      let ivSet : Std.HashSet FVarId := ivs.foldl (fun st v => if bound.contains v then st.insert v else st) {}
      if !ivSet.isEmpty then
        let mut stray := strayImpl ivSet body
        for x in xs do
          if stray.isNone then
            let tx ← instantiateMVars (← Meta.inferType x)
            -- Round 15: the one premise on `impl` the auditor allows is exactly `ImplApart Extracted.program impl`
            unless isImplApartPremise env tx && (match tx.consumeMData.getArg! 1 |>.consumeMData with
                | .fvar v => bound.contains v | _ => false) do
              stray := strayImpl ivSet tx
        if let some v := stray then
          return some s!"mentions the runtime implementation variable `{(← v.getUserName)}` other than as `Extracted.program.link {(← v.getUserName)}`: a main theorem may constrain the implementation only through the pinned contracts and model laws, not through a premise or precondition about the code (round 14, rt-auditv2)"
      for v in ivs do
        if bound.contains v && !rtVars.contains v then
          rtVars := rtVars.insert v
          implOnly := implOnly.insert v
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
    -- U-ICALL: the call-site property and the kept ranges mention no runtime variable (`impl`, `rt`, `R`, …): they are the
    -- statement's own claims about the call, they must not constrain the runtime's parameters
    for a in icallFree do
      if a.hasAnyFVar (rtVars.contains ·) then
        return some s!"has an abstract-callee contract whose call-site property or kept ranges `{(← Meta.ppExpr a).pretty 10000}` mention a runtime variable of a contract hypothesis: they may mention only the statement's own variables (U-ICALL)"
    -- U-ICALL-STACK: a variable used as a size is constrained by no premise except a numeral lower bound (`c ≤ k`, `c < k`, c ≤ limit)
    let sizeVarIds := sizeVars.map (·.2.1)
    -- A variable `w` that only BOUNDS FROM BELOW: every premise mentioning it has the shape `X ≤ w` / `X < w` (Nat) with `X` free of `w`.
    -- Nothing can pin such a `w` from above, so `v + k ≤ w` (k a numeral) or `v ≤ w` holds for every size `v` by the choice of `w`
    -- (the frame/stack bound `d` of the memhash/memequal/memmove/typed-copy families next to the callee's own bound `d'`; the
    -- same reasoning as `depthBound`). `w` may not itself be a size or a runtime variable.
    let onlyLowerBounded (w : FVarId) : Bool :=
      bound.contains w && !rtVars.contains w && !sizeVarIds.contains w &&
        premises.all fun (_, p) =>
          let p' := p.consumeMData
          !p'.hasAnyFVar (· == w) ||
            ((p'.isAppOfArity ``LE.le 4 || p'.isAppOfArity ``LT.lt 4) && (p'.getArg! 0).isConstOf ``Nat &&
              (p'.getArg! 3).consumeMData == .fvar w && !(p'.getArg! 2).hasAnyFVar (· == w))
    for (what, v, limit) in sizeVars do
      for (x, t) in premises do
        unless t.hasAnyFVar (· == v) do continue
        let t' := t.consumeMData
        let isContractHyp := match t'.getAppFn with
          | .const c _ => isRuntimeContract env c
          | _ => false
        if isContractHyp then continue
        let lowerBound ← do
          if (t'.isAppOfArity ``LE.le 4 || t'.isAppOfArity ``LT.lt 4) && (t'.getArg! 0).isConstOf ``Nat then
            match (t'.getArg! 3).consumeMData with
            | .fvar w =>
              if w == v then
                match (← icallNatValue? (t'.getArg! 2)) with
                | some n => pure (decide (n < limit))
                | none => pure false
              else pure false
            | _ => pure false
          else pure false
        -- `v ≤ w`, `v < w`, `v + k ≤ w`, `v + k < w` with `w` bounded below only (see `onlyLowerBounded`) and `k` a numeral below the limit
        let belowFree ← do
          if (t'.isAppOfArity ``LE.le 4 || t'.isAppOfArity ``LT.lt 4) && (t'.getArg! 0).isConstOf ``Nat then
            match (t'.getArg! 3).consumeMData with
            | .fvar w =>
              if w == v || !onlyLowerBounded w then pure false
              else
                let l := (t'.getArg! 2).consumeMData
                if l == .fvar v then pure true
                else if l.isAppOfArity ``HAdd.hAdd 6 && (l.getArg! 4).consumeMData == .fvar v then
                  match (← icallNatValue? (l.getArg! 5)) with
                  | some k => pure (decide (k < limit))
                  | none => pure false
                else pure false
            | _ => pure false
          else pure false
        unless lowerBound || belowFree do
          return some s!"has the premise `{(← Meta.ppExpr t).pretty 10000}` ({(← x.fvarId!.getUserName)}) about the {what} `{(← v.getUserName)}` of a runtime contract: such a size may be constrained only by a numeral lower bound (`c ≤ {(← v.getUserName)}`) within the satisfiable range; an equality or upper bound can pin it to a value that makes the call precondition unsatisfiable, and the contract would hold vacuously (U-ICALL-STACK)"
    -- U-ICALL red team B1/B2: the callee address `fn` of an abstract-callee contract appears only inside contract
    -- hypotheses (and the statement's own body); any other premise mentioning it (`fn = Extracted.entry`, `fn = 0x100000`,
    -- an inequality, …) would pin the abstract callee to code the statement chooses
    for (x, t) in premises do
      if t.hasAnyFVar (icallFns.contains ·) then
        let isICall := match t.consumeMData.getAppFn with
          | .const c _ => isICallContract c
          | _ => false
        unless isICall do
          return some s!"has the premise `{(← Meta.ppExpr t).pretty 10000}` ({(← x.fvarId!.getUserName)}) about the callee address of an abstract-callee contract: the address may appear only inside the contract hypothesis (it is a parameter of the theorem linked to the call by the itab word, or exactly `Extracted.program.contractAddr \"name\"`); a premise that pins it chooses the callee (U-ICALL)"
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
      -- Round 15: "the runtime's code does not overlap the extracted function's code"
      let isApart := isImplApartPremise env t' &&
        (match t'.getArg! 1 |>.consumeMData with | .fvar v => bound.contains v | _ => false)
      unless isContract || isLaws || isApart || depthBound bound rtVars t' do
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
def readCleanImports : IO ImportState := withImporting do
  let (_, sClean) ← (importModulesCore cleanImports).run
  return sClean

/-- The audited state, grown from the clean one (`readCleanImports`): the modules the audited
closure adds to the clean closure are read, the shared ones are not read again. -/
def readAuditImports (sClean : ImportState) (auditImports : Array Import) : IO ImportState := withImporting do
  let (_, sAudit) ← (importModulesCore auditImports).run sClean
  return sAudit

def readImports (auditImports : Array Import) : IO (ImportState × ImportState) := do
  let sClean ← readCleanImports
  let sAudit ← readAuditImports sClean auditImports
  return (sClean, sAudit)

/-- The audited environment (`importModules (loadExts := false) auditImports {}`) and the clean
import state, reading every module once (`readImports`). The shared read is used only if the
imported `Extracted` directly imports `Janus`, so the clean closure adds no module to the audited
one and the result is the environment a fresh import builds (same modules, same order: both are
the same depth-first traversal); otherwise the audited environment is imported separately. -/
def auditEnv (auditImports : Array Import) (clean? : Option ImportState := none) :
    IO (Environment × ImportState) := do
  let (sClean, sAudit) ← match clean? with
    | some sClean => pure (sClean, ← readAuditImports sClean auditImports)
    | none => readImports auditImports
  let env ← withImporting <| finalizeImport sAudit auditImports {} (leakEnv := false) (loadExts := false)
  let extractedImportsJanus := match env.getModuleIdx? `Extracted with
    | some i => match env.header.moduleData[i.toNat]? with
      | some d => d.imports.any (·.module == `Janus)
      | none => false
    | none => false
  if extractedImportsJanus then
    return (env, sClean)
  return (← importModules (loadExts := false) auditImports {}, sClean)

/-- The clean environment's import state and the environment `cleanEnvAndPrint` builds from it
(`finalizeImport cleanState cleanImports {} (loadExts := true)`, initializers enabled), built
without looking at the proof: `janus-audit --serve` runs this while the proof compiles and
`runImplCore` then continues with it. It reads the framework and `Extracted` modules only. -/
unsafe def prepareClean : IO (ImportState × Environment) := do
  let sClean ← readCleanImports
  enableInitializersExecution
  let env ← (withImporting <| finalizeImport sClean cleanImports {} (leakEnv := false) (loadExts := true) : IO Environment)
  return (sClean, env)

/-- Round 14: the runtime contracts the statement `e` applies, as `Contract@runtime.function` (the
function named by the `contractAddr` literal in the application), each once. -/
def contractNames (apps : Array Expr) : Array String :=
  apps.foldl (init := #[]) fun acc app =>
    let c := app.getAppFn.constName!.toString
    let isAddr (x : Expr) : Bool :=
      (x.getAppFn.isConstOf `Janus.Program.contractAddr || x.getAppFn.isConstOf `Janus.Amd64.Program.contractAddr) &&
        x.getAppNumArgs == 2 && (match x.appArg! with | .lit (.strVal _) => true | _ => false)
    let sp := specLabel app
    let s := match app.find? isAddr with
      | some x => (match x.appArg! with | .lit (.strVal a) => s!"{c}@{a}" | _ => c)
      | none => c
    let s := if sp == "" then s else s!"{s}[{sp}]"
    if acc.contains s then acc else acc.push s

def contractUses (env : Environment) (e : Expr) : Array String :=
  contractNames (contractApps env e)

/-- The runtime contracts a MAIN theorem ASSUMES: those applied in its premises and in the part of
its conclusion that is not itself a contract. A theorem whose conclusion IS a contract (it proves the
contract of the program's own code) assumes nothing by stating it; the non-vacuity policy
(`janus verify`: a main theorem that assumes contracts needs a witness) must not count it. A witness
exhibits its contracts, so for a non-main theorem every application counts. -/
def assumedContracts (ty : Expr) (main : Bool) : MetaM (Array String) := do
  let env ← getEnv
  if !main then return contractUses env ty
  Meta.forallTelescope ty fun xs body => do
    let mut apps : Array Expr := #[]
    for x in xs do
      let t ← Meta.inferType x
      if ← Meta.isProp t then apps := contractApps env t apps
    for t in conclParts env body do apps := contractApps env t apps
    return contractNames apps

/-- Build the clean environment: import only `Janus` and `Extracted`, with initializers so pp
works, then add type-only stubs for the dependency constants the statement reaches, re-add the
allowed proof-local defs and an axiom with the theorem's type. Reject a proof-local def whose
type's head is a class (a disguised instance, A1). No proof or dependency module is imported, so
none of their initializers, notations, unexpanders or delaborators exist here. -/
unsafe def cleanEnvAndPrint (cx : Ctx) (thm : Name) (thmType : Expr) (localDefs : Array ConstantInfo)
    (stubs : Array ConstantInfo) (extDefs : Array ConstantInfo) (cleanState : ImportState)
    (clean : Array Import := cleanImports) (pre? : Option Environment := none) (main : Bool := true) :
    AuditM (String × String × Array String × Array String × Array String × Array String) := do
  -- `importModules (loadExts := true) cleanImports {}`, with the module data already read
  -- (`readImports`): the same `finalizeImport` over the same import state. `pre?` is that very
  -- environment, built earlier by `prepareClean` (the serve mode of `janus-audit`).
  let env ← match pre? with
    | some e => pure e
    | none => do
      enableInitializersExecution
      (withImporting <| finalizeImport cleanState clean {} (leakEnv := false) (loadExts := true) : IO Environment)
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
  let printAll : MetaM (String × String × Array String × Array String × Array String × Array String) := do
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
    if let some m ← checkContractHyps expanded main then
      throwError s!"the statement {m}"
    -- the amd64 undefined-value stream (BSF/BSR of zero) is never pinned by a statement
    -- role-based, never name-prefix based (round 14 reconciliation): only a theorem whose role is exactly
    -- `Witness.nonvacuous` / `Witness.returns` AND that is not the main theorem (`main` is the role verdict
    -- of the caller) gets the concrete-start-state exemption; any theorem of a `Witness` namespace that is
    -- the main theorem, or an auxiliary lemma, never does
    let isWitness := !main && (roleOfTy thm thmType == Role.nonvacuous || roleOfTy thm thmType == Role.returns)
    if let some m ← checkUndefStream isWitness expanded then
      throwError s!"the statement {m}"
    for ci in extDefs do
      for t in [ci.type] ++ ci.value?.toList do
        if let some m ← checkUndefStream isWitness t then
          throwError s!"the dependency definition {ci.name} used in the statement {m}"
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
    return (sigStr, explicit.fmt.pretty 10000, defs, extOut, notes, ← assumedContracts expanded main)
  match ← (Core.CoreM.toIO' (Meta.MetaM.run' printAll) { mkCoreCtx with options := opts } { env }).toBaseIO with
  | .ok a => return a
  | .error e => fail e.toString

/-! ## Round 14 (W2): the role of a theorem, and witnesses checked structurally

The audit used to gate the non-vacuity witnesses (`Proof.Witness.nonvacuous`, `Proof.Witness.returns`)
by their NAME and by "the statement mentions `Extracted.program`", so `Extracted.program =
Extracted.program` in the place of a witness passed. A witness now has a SHAPE, checked here:

* `…Witness.nonvacuous` must be `∃ vars, c₁ ∧ … ∧ cₙ` such that some main theorem `M` of the same
  proof module (`∀ xs, hyps → F program entry args pre post …`) is instantiated: EVERY hypothesis of
  `M` (the runtime contracts, model laws, readiness predicates, numeric side conditions) appears as
  a conjunct, and so does every premise of `M`'s conclusion once its head (`Ensures`, `EnsuresK`, …)
  is unfolded to its `∀ ret, RetAddr … → ∀ s, CallSetup … → pre s → …` form: the return address,
  the call state for the SAME program, entry address and arguments, and each conjunct of the
  precondition. The match is definitional unification of `M`'s variables with the witness's, so a
  witness exhibits a call state satisfying the main theorem's precondition together with an
  instance of its hypotheses; `Extracted.program = Extracted.program` or `True` cannot pass.
* `…Witness.returns` must be a `Returns`-style statement (`Returns`, `GoReturns`, `ReturnsK`,
  `GrownReturns`, `ReachesRet`) that is, for ONE conjunct of the main theorem (an execution runs one entry; non-vacuity of
  the others is `nonvacuous`'s job, which covers every conjunct), up to definitional unification of `M`'s variables, the
  EXACT conclusion of some main theorem `M` (its unfolded `Returns … (fun s' => ABIReturn s s' ∧
  post s s')`) at a concrete start state: an execution of the program that reaches the return with
  the guarantee of the main theorem.
* Any other theorem whose name has a `Witness` component is a lemma of a witness namespace and is
  not a verifiable result.
* Any other theorem is a MAIN theorem (`checkContractHyps`, `concreteRuntime`).

The witness is matched against the theorems of the proof module only; the report names the matched
main theorem (`matchedMain`) so the reader can see which theorem the witness supports. -/

/-- Numeric literal spelling only (round 14): `(BitVec.ofNat n k).toNat` and `(k#n).toNat` with numerals `k < 2^n`
are the numeral `k`; nothing else is rewritten. A witness states `H [42] …` where the main theorem has
`H [(42#64).toNat] …` for the argument `x := 42#64`. -/
def normLits (e : Expr) : MetaM Expr := do
  Core.transform (← instantiateMVars e) (post := fun sub => do
    if sub.isAppOfArity ``BitVec.toNat 2 then
      let v := sub.appArg!
      let lit? : Option (Nat × Nat) :=
        if v.isAppOfArity ``BitVec.ofNat 2 then
          match (v.getArg! 0).nat?, (v.getArg! 1).nat? with
          | some n, some k => some (n, k) | _, _ => none
        else none
      if let some (n, k) := lit? then
        if k < 2 ^ n then return .done (mkNatLit k)
    return .continue)

/-- Definitional equality, tried at reducible transparency first, then at default (the proof's
own `def`s may need unfolding: a `Witness.rt` that is an alias of the allocator's ranges), with a
heartbeat budget; a failure leaves the metavariable context unchanged. -/
def defEqTry (a b : Expr) : MetaM Bool := do
  if ← Meta.checkpointDefEq (Meta.withReducible (Meta.isDefEq a b)) then return true
  -- the same up to numeral spelling
  let a' ← normLits a
  let b' ← normLits b
  if (a' != a || b' != b) && (← Meta.checkpointDefEq (Meta.withReducible (Meta.isDefEq a' b'))) then return true
  -- the default-transparency retry only for the same predicate (`Outside … Witness.rt` vs `Outside … AllocW.rt`):
  -- unfolding two different predicates just to compare them is slow and never what a witness does
  unless a.getAppFn.isConst && a.getAppFn == b.getAppFn do return false
  try
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 300000 * 1000 }) do
      withCurrHeartbeats do
        Meta.checkpointDefEq (Meta.withDefault (Meta.isDefEq a b))
  catch _ => pure false

def findConj (p : Expr) (cs : Array Expr) : MetaM Bool := cs.anyM (defEqTry p ·)

/-- The conjuncts of `e`, through `∧` only. -/
partial def flattenAnd (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then flattenAnd (e.getArg! 1) (flattenAnd (e.getArg! 0) acc)
  else acc.push e

/-- `e` with `mdata` dropped, applied lambdas beta-reduced (`(fun s => P s ∧ Q s) s`) and `let`s instantiated,
repeatedly: the same proposition, so a witness that states the precondition as an applied lambda (copied from
the main theorem's `pre`) is read as the conjunction it is. Definitions are NOT unfolded (a premise
`CallPre n s` of the main theorem stays one conjunct, as it is in the witness). -/
partial def conjHead (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  match e with
  | .letE _ _ v b _ => conjHead (b.instantiate1 v)
  | _ => return e

/-- The conjuncts of `e` with every `∃` binder on the way (leading, or inside a conjunction:
`∃ impl, C ∧ ∃ s, s.pc = … ∧ P`) opened as a local variable, for the continuation `k`. -/
partial def withConjs {α} (e : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let e ← conjHead e
  if e.isAppOfArity ``And 2 then
    withConjs (e.getArg! 0) fun ca => withConjs (e.getArg! 1) fun cb => k (ca ++ cb)
  else if e.isAppOfArity ``Exists 2 then
    match (e.getArg! 1).consumeMData with
    | .lam n d b bi => Meta.withLocalDecl n bi d fun x => withConjs (b.instantiate1 x) k
    | _ => k #[e]
  else k #[e]

/-- `e` with its head definition unfolded (`Ensures`, `EnsuresResults`, `CEnsures`, `EnsuresK`, …)
until it is a `∀`: `∀ ret, RetAddr p ret → ∀ s, CallSetup … → pre s → Returns …`. -/
def unfoldToForall (e : Expr) : MetaM Expr := do
  let mut e := e.consumeMData
  for _ in [0:8] do
    if e.isForall then return e
    match ← Meta.unfoldDefinition? e with
    | some e2 => e := e2.consumeMData
    | none => return e
  return e

/-- Candidate main theorems of the proof module for a witness: theorems of the module that are not
witness lemmas, mention `Extracted.program`, and are not the witness itself; only those named `correctness`
if there are any. -/
def mainCandidates (env : Environment) (proofMod : Name) (self : Name) : Array Name :=
  let modNames := env.header.moduleNames
  -- theorems about `Extracted.program` of a module, `correctness` ones only if there are any
  let inMods (ok : Name → Bool) : Array Name :=
    let all := env.const2ModIdx.fold (init := #[]) fun acc n idx =>
      match modNames[idx.toNat]? with
      | some m =>
        if ok m && n != self && !n.isInternal && roleOf n == .main then
          match env.find? n with
          | some (.thmInfo ci) =>
            let used := ci.type.getUsedConstants
            if used.contains `Extracted.program || used.contains `Extracted.entry then acc.push n else acc
          | _ => acc
        else acc
      | none => acc
    let first := all.filter (·.getString! == "correctness")
    if !first.isEmpty then first.qsort Name.lt else all.qsort Name.lt
  -- The module's main theorem is the one named `correctness` (every example's convention); only when it has
  -- none are all its non-witness theorems candidates (otherwise a helper lemma or a junk theorem with a weak
  -- statement could stand in for the main theorem a witness supports). A proof whose main theorem lives in a
  -- module it imports (`PrintProofs.Arm64.MainX`, a `Three/Main.lean`) falls back to the imported
  -- consumer/proof modules, never the trusted ones.
  let own := inMods (· == proofMod)
  if !own.isEmpty then own else inMods fun m => !trustedModule m && m != proofMod

/-- The statement of `n` with fresh universe metavariables. -/
def freshType (env : Environment) (n : Name) : MetaM (Option Expr) := do
  let some ci := env.find? n | return none
  return some (ci.instantiateTypeLevelParams (← Meta.mkFreshLevelMVars ci.levelParams.length))

/-- A conjunct that says nothing: `True`, or `a = a`. -/
def trivialConj (e : Expr) : Bool :=
  e.isConstOf ``True || (e.isAppOfArity ``Eq 3 && e.getArg! 1 == e.getArg! 2)

/-- `s.pc` (arm64) or `s.rip` (amd64) of a state. -/
def isPcProj (e : Expr) : Bool :=
  let f := e.getAppFn
  (f.isConstOf `Janus.Arm64.State.pc || f.isConstOf `Janus.Amd64.State.rip) && e.getAppNumArgs == 1

/-- A premise about numbers (`8 ≤ db`, `db + 48 ≤ d`): tried after the structural ones, which fix the
variables, because several such conjuncts can unify with it. -/
def arithPremise (e : Expr) : Bool :=
  e.isAppOf ``LE.le || e.isAppOf ``LT.lt || e.isAppOf ``Eq || e.isAppOf ``Ne || e.isAppOf ``GE.ge ||
    e.isAppOf ``GT.gt || e.isAppOf ``Not

/-- Is the closed proposition `t` true by evaluating its natural-number literals (`0 ≤ 8`, `1 ≤ 8`, `2 + 1 < 9`)?
No instance search: the auditor's environment has no instance extension loaded. -/
partial def decideTrue (t : Expr) : MetaM Bool := do
  let t := (← instantiateMVars t).consumeMData
  if t.hasExprMVar then return false
  let nat2 (f : Nat → Nat → Bool) (a b : Expr) : MetaM Bool := do
    match ← Meta.evalNat a, ← Meta.evalNat b with
    | some x, some y => return f x y
    | _, _ => return false
  if t.isConstOf ``True then return true
  else if t.isAppOfArity ``And 2 then return (← decideTrue (t.getArg! 0)) && (← decideTrue (t.getArg! 1))
  else if t.isAppOfArity ``LE.le 4 && (t.getArg! 0).isConstOf ``Nat then nat2 (· ≤ ·) (t.getArg! 2) (t.getArg! 3)
  else if t.isAppOfArity ``LT.lt 4 && (t.getArg! 0).isConstOf ``Nat then nat2 (· < ·) (t.getArg! 2) (t.getArg! 3)
  else if t.isAppOfArity ``GE.ge 4 && (t.getArg! 0).isConstOf ``Nat then nat2 (· ≥ ·) (t.getArg! 2) (t.getArg! 3)
  else if t.isAppOfArity ``GT.gt 4 && (t.getArg! 0).isConstOf ``Nat then nat2 (· > ·) (t.getArg! 2) (t.getArg! 3)
  else if t.isAppOfArity ``Eq 3 && (t.getArg! 0).isConstOf ``Nat then nat2 (· == ·) (t.getArg! 1) (t.getArg! 2)
  else return false

/-- Round 14 (rt-auditv2, F1): the address of a `pc`/`rip` premise that a witness may leave to the proof: the
extraction's entry or a contract address of the program (`s.pc = BitVec.ofNat 64 entry`). -/
partial def entryAddrLike (env : Environment) (fuel : Nat) (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  let x := (if e.isAppOfArity ``BitVec.ofNat 2 then e.getArg! 1 else e).consumeMData
  if x.isConstOf `Extracted.entry then return true
  match x.getAppFn with
  | .const c _ =>
    let isTrusted := match env.getModuleIdxFor? c with
      | some i => trustedModule env.header.moduleNames[i.toNat]!
      | none => false
    if isTrusted then
      return (c.getString! == "contractAddr" || c.getString! == "segAddr") && x.getAppNumArgs == 2
    -- a proof-local definition (`def wb1 := segAddr Extracted.program "runtime.gcWriteBarrier1"`): its body must be one
    if fuel == 0 then return false
    match ← Meta.unfoldDefinition? x with
    | some x' => entryAddrLike env (fuel - 1) x'
    | none => return false
  | _ => return false

/-- Round 14 (rt-auditv2, F2): does a binder of type `t` (an unassigned variable of the main theorem) have an
element by construction? Numbers, lists and the like, a `Fin` of a positive or free size, a function into a
proposition or such a type, a type of a trusted module (the framework's states, memories, segments). Not a
`Subtype`, `PLift`, `Sigma`, `Empty`, or a type of the proof or a dependency. -/
partial def inhabSafe (env : Environment) (t : Expr) : MetaM Bool := do
  let t ← instantiateMVars t
  let t ← try Meta.whnfR t catch _ => pure t
  match t with
  | .sort _ => return true
  | .forallE n d b bi => Meta.withLocalDecl n bi d fun x => inhabSafe env (b.instantiate1 x)
  | _ =>
    let some c := t.getAppFn.constName? | return false
    let args := t.getAppArgs
    if c == ``Fin then
      let n ← instantiateMVars args[0]!
      return match n.nat? with | some k => decide (0 < k) | none => n.isMVar
    if [``Nat, ``Int, ``Bool, ``String, ``Char, ``Unit, ``PUnit, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize,
        ``BitVec, ``List, ``Array, ``Option, ``Float].contains c then return true
    if c == ``Prod then return (← args.allM (inhabSafe env ·))
    if [``Subtype, ``Sigma, ``PSigma, ``PLift, ``ULift, ``Empty, ``PEmpty, ``Exists, ``False, ``Nonempty,
        ``Squash, ``Quot, ``Quotient, ``Eq, ``HEq].contains c then return false
    match env.getModuleIdxFor? c with
    | some idx => return trustedModule env.header.moduleNames[idx.toNat]!
    | none => return false

/-- Does the witness conjunct `c` give the premise `p`? Either `c` unifies with `p`, or `c` is a
universal statement `∀ n, n ≤ 8 → A n ∧ B n` (`WriteBarrier`: the witness covers every slot count) one of
whose instances unifies with `p` and whose side conditions at that instance are decidably true. -/
def conjGives (p c : Expr) : MetaM Bool := do
  if ← defEqTry p c then return true
  let c := c.consumeMData
  if !c.isForall then return false
  let st ← Meta.saveState
  let (vs, _, b) ← Meta.forallMetaTelescope c
  for bc in flattenAnd b do
    let st2 ← Meta.saveState
    if ← defEqTry p bc then
      let mut ok := true
      -- a variable that `p` does not mention (`n` of `CallOK s 232 0` in `∀ n, n ≤ 8 → CallOK s 232 0 ∧ Ready … [n] s`)
      -- is taken to be `0` (a natural number)
      for v in vs do
        let t ← instantiateMVars (← Meta.inferType v)
        if !(← Meta.isProp t) && !(← v.mvarId!.isAssigned) && t.isConstOf ``Nat then
          discard <| Meta.isDefEq v (toExpr (0 : Nat))
      for v in vs do
        let t ← instantiateMVars (← Meta.inferType v)
        if ← Meta.isProp t then
          unless ← decideTrue t do ok := false
        else unless ← v.mvarId!.isAssigned do ok := false
      if ok then return true
    st2.restore
  st.restore
  return false

/-- Match every premise of `ps` to a conjunct of `cs`, assigning the metavariables, with backtracking
(a premise can unify with several conjuncts). `none` on success, else the premise that could not be
placed. -/
partial def matchPremises (ps : List Expr) (cs : Array Expr) : MetaM (Option String) := do
  match ps with
  | [] => return none
  | p :: rest =>
    let mut last : Option String := none
    for c in cs do
      let st ← Meta.saveState
      if ← conjGives p c then
        match ← matchPremises rest cs with
        | none => return none
        | some w => last := some w
      st.restore
    return last <|> some s!"`{(← Meta.ppExpr p).pretty 300}` is not among the conjuncts of the witness (conjuncts are matched after beta-reduction)"

/-- The Prop-typed metavariables of a telescope, as non-trivial conjuncts, structural ones first. -/
def premisesOf (ms : Array Expr) : MetaM (List Expr) := do
  let mut ps := #[]
  for m in ms do
    let t := (← instantiateMVars (← Meta.inferType m)).headBeta
    unless ← Meta.isProp t do continue
    for p in flattenAnd t do
      let p := (← instantiateMVars p).headBeta
      unless trivialConj p do ps := ps.push p
  return (ps.filter (!arithPremise ·)).toList ++ (ps.filter arithPremise).toList

/-- Is the witness body `wconjs` an instance of the main statement `mty`? `none` when it is, else
the reason. Every hypothesis of `mty` must be a conjunct of the witness; and, for EVERY conjunct of the
conclusion (a main theorem may state several guarantees, `IsEven ∧ IsOdd`, `wb1 ∧ … ∧ wb8`; a witness for one
of them would leave the others possibly vacuous), every premise of that conjunct's unfolded form (return
address, call state, precondition conjuncts) must be a conjunct of the witness too. -/
def matchNonvacuous (mty : Expr) (wconjs : Array Expr) : MetaM (Option String) := do
  let (ms, _, concl) ← Meta.forallMetaTelescope mty
  let hyps ← premisesOf ms
  let concls := flattenAnd (← instantiateMVars concl)
  for (c, idx) in concls.toList.zip (List.range concls.size) do
    let st ← Meta.saveState
    let body ← unfoldToForall c
    let (ms2, _, _) ← Meta.forallMetaTelescope body
    let which := if concls.size > 1 then s!" (conjunct {idx + 1} of {concls.size})" else ""
    if ms2.isEmpty then
      return some s!"the conclusion of the main theorem{which} does not unfold to a `∀ ret, … → ∀ s, CallSetup … → pre s → …` statement"
    let calls ← premisesOf ms2
    -- the premise `s.pc = entry` / `s.rip = entry` of a `Summary`-style contract is the call setup; a witness
    -- that exhibits a state satisfying the rest of the precondition (`CallOK s …`, `Ready H rt [n] s`) for
    -- `s` may leave the entry address to the proof (`WriteBarrier`: one state for every `gcWriteBarrierN`)
    let all := hyps ++ calls
    let pcPrem := fun (e : Expr) => e.isAppOfArity ``Eq 3 && isPcProj (e.getArg! 1)
    let core := all.filter (!pcPrem ·)
    let ps := core.filter (!arithPremise ·) ++ core.filter arithPremise
    match ← matchPremises ps wconjs with
    | none =>
      -- Round 14 (rt-auditv2, F2): a binder of the main theorem that is not a proposition and that the
      -- matched premises did not fix (`(i : Fin 0)`, `{n : Nat // n < 0}`, `PLift (0 = 1)`) is exhibited
      -- by nothing in the witness; it must be of a type that has an element by construction
      let env ← getEnv
      for m in ms ++ ms2 do
        let t ← instantiateMVars (← Meta.inferType m)
        if ← Meta.isProp t then continue
        if (← instantiateMVars m) != m then continue
        unless ← inhabSafe env t do
          return some s!"the main theorem{which} has a binder of type `{(← Meta.ppExpr t).pretty 200}`, which no conjunct of the witness exhibits and which is not a type with an element by construction (an empty type makes the main theorem vacuous): state the witness's value for it in the premises (round 14, rt-auditv2)"
      -- the pc premises: matched if the witness states them, else they must be about a state the other
      -- premises fixed
      for q in all.filter pcPrem do
        let q ← instantiateMVars q
        unless ← findConj q wconjs do
          if q.hasExprMVar then
            return some s!"the entry-address premise of the main theorem{which} concerns no state of the witness"
          -- Round 14 (rt-auditv2, F1): ... and then the address must be the program's entry or a contract address
          -- (`WriteBarrier`: one state for every `gcWriteBarrierN`); `s.pc = 7` (an unsatisfiable precondition)
          -- is a premise the witness has to state
          unless ← entryAddrLike (← getEnv) 8 (q.getArg! 2) do
            return some s!"the premise `{(← Meta.ppExpr q).pretty 300}` of the main theorem{which} fixes the program counter to an address that is neither the entry nor a contract address, and the witness does not state it"
    | some w => return some s!"the premise {w}{which}"
    st.restore
  if concls.isEmpty then return some "the main theorem has no conclusion"
  return none

/-- Is `e` an application of a `Returns`-style predicate? -/
def returnsHead (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ =>
      let s := c.getString!
      (s.startsWith "Returns" || s.startsWith "GoReturns" || s.startsWith "GrownReturns" || s == "ReachesRet")
  | _ => false

/-- The `Returns`-style application inside `e` (through `∧`, `→`, `↔`, `∀`), if any. -/
partial def findReturns (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  if returnsHead e then return some e
  match e with
  | .forallE n d b bi => Meta.withLocalDecl n bi d fun x => findReturns (b.instantiate1 x)
  | .app .. => do
    for a in e.getAppArgs do
      if let some r ← findReturns a then return some r
    return none
  | _ => return none

/-- The `Returns`-style conclusions that the unfolded conjuncts of the main statement `mty` end in, with
`M`'s variables as metavariables. -/
def mainReturns (mty : Expr) : MetaM (Array Expr) := do
  let (_, _, concl) ← Meta.forallMetaTelescope mty
  let mut out := #[]
  for c in flattenAnd concl do
    let body ← unfoldToForall c
    let (_, _, last) ← Meta.forallMetaTelescope body
    if returnsHead last.consumeMData then out := out.push last.consumeMData
  return out

/-- Does the `Returns`-style statement `r` (of a `returns` witness) state the guarantee `mr` of the main
theorem at a start state? Strictly: they unify. Or, since a witness usually states the guarantee
SPECIALISED to its concrete inputs (`ABIReturn s0 s' ∧ s'.regs 0 = 0`, derived from the general
postcondition with `Returns.mono`): the same predicate with the same program, start state and
auxiliary arguments, whose postcondition keeps the first conjunct of the main theorem's (the ABI
obligation `ABIReturn s s'` / `CReturn s s'`) and adds at least one further conjunct, i.e. says
something about the result. A trivial postcondition, or the ABI obligation alone, is rejected. -/
def returnsMatches (mr r : Expr) : MetaM Bool := do
  if ← defEqTry mr r then return true
  unless mr.getAppFn == r.getAppFn && mr.getAppNumArgs == r.getAppNumArgs do return false
  let ma := mr.getAppArgs
  let ra := r.getAppArgs
  let mut lamSeen := false
  for i in [0:ma.size] do
    let m := (← instantiateMVars ma[i]!).consumeMData.headBeta
    let x := (← instantiateMVars ra[i]!).consumeMData.headBeta
    if m.isLambda && x.isLambda then
      lamSeen := true
      let ok ← Meta.lambdaTelescope m fun ys bm => do
        let bx := (x.beta ys).headBeta
        let cm := flattenAnd (← instantiateMVars bm).headBeta
        -- Round 14 (rt-auditv2, F3): a conjunct of the witness's result statement counts only if it says something
        -- about the result state (`1 + 1 = 2`, `decide True = true` do not); a lambda whose main body does not
        -- speak about its arguments at all (the fault continuation `fun _ _ => False` of `ReturnsK`) is unchanged
        let mentions := fun (c : Expr) => ys.any fun y => c.containsFVar y.fvarId!
        let cx0 := (flattenAnd bx).filter (!trivialConj ·)
        let cx := cx0.filter mentions
        if cx0.isEmpty || cm.isEmpty then return false
        -- the main postcondition's first conjunct is the ABI obligation (`ABIReturn s s'`) when it has
        -- several: keep it and add a statement about the result; a single conjunct (`GrownReturns`,
        -- `EnsuresGrow`: no ABI obligation) is specialised to the concrete result, which must say something
        if cm.size ≥ 2 then
          if cx.size < 2 then return false
          findConj cm[0]! cx
        else return !(cm.any mentions) || !cx.isEmpty
      unless ok do return false
    else
      unless ← defEqTry m x do return false
  return lamSeen

/-- Main theorems of the proof module (not witnesses, not `self`) about `Extracted.program` whose statement
mentions a runtime contract: they assume the runtime, so each is owed a non-vacuity witness. -/
def contractMains (env : Environment) (proofMod : Name) (self : Name) : Array Name :=
  let modNames := env.header.moduleNames
  let all := env.const2ModIdx.fold (init := #[]) fun acc n idx =>
    match modNames[idx.toNat]? with
    | some m =>
      if m == proofMod && n != self && !n.isInternal && roleOf n == .main then
        match env.find? n with
        | some (.thmInfo ci) =>
          let used := ci.type.getUsedConstants
          if (used.contains `Extracted.program || used.contains `Extracted.entry) &&
              used.any (isRuntimeContract env) then acc.push n else acc
        | _ => acc
      else acc
    | none => acc
  all.qsort Name.lt

/-- Round 14 (W2): check the shape of a witness theorem (see the section comment); the matched main
theorem on success. -/
def checkWitness (env : Environment) (proofMod thm : Name) (role : Role) (thmType : Expr) :
    MetaM (Except String (Name × Array Name)) := do
  let cands0 := mainCandidates env proofMod thm
  -- further main theorems of the module that assume runtime contracts (`full_write` next to `correctness`):
  -- each needs its own witness, and one witness may serve several of them
  let extra := contractMains env proofMod thm
  let cands := cands0 ++ extra.filter (!cands0.contains ·)
  if cands.isEmpty then
    return .error "the proof module has no main theorem about Extracted.program for this witness to support"
  match role with
  | .nonvacuous =>
    unless (thmType.consumeMData.isAppOfArity ``Exists 2) do
      return .error "is not of the form `∃ …, …` (a state and runtime exhibiting the main theorem's hypotheses)"
    withConjs thmType fun wconjs => do
      let mut whys : Array String := #[]
      let mut ok : Array Name := #[]
      for c in cands do
        let some mty ← freshType env c | continue
        let st ← Meta.saveState
        match ← matchNonvacuous mty wconjs with
        | none => ok := ok.push c
        | some w => whys := whys.push s!"{c}: {w}"
        st.restore
      if let some c := ok[0]? then return .ok (c, ok)
      return .error s!"does not instantiate any main theorem of the proof module ({"; ".intercalate whys.toList})"
  | .returns =>
    Meta.forallTelescope thmType fun _ body => do
      let mut whys : Array String := #[]
      let some r ← findReturns body
        | return .error "is not a `Returns`-style statement (`Returns`, `GoReturns`, `ReturnsK`, `GrownReturns`, `ReachesRet`)"
      unless (r.find? (·.isConstOf `Extracted.program)).isSome do
        return .error "its program is not built from Extracted.program"
      let mut ok : Array Name := #[]
      for c in cands do
        let some mty ← freshType env c | continue
        let mrs ← mainReturns mty
        if mrs.isEmpty then whys := whys.push s!"{c}: its conclusion does not unfold to a Returns-style statement"; continue
        let mut hit := false
        for mr in mrs do
          let st ← Meta.saveState
          if ← returnsMatches mr r then hit := true
          else whys := whys.push s!"{c}: the statement is not its guarantee `{(← Meta.ppExpr mr).pretty 200}`"
          st.restore
          if hit then break
        if hit then ok := ok.push c
      if let some c := ok[0]? then return .ok (c, ok)
      return .error s!"is not the guarantee of any main theorem of the proof module at a start state ({"; ".intercalate whys.toList})"
  | _ => return .error "is a lemma of a Witness namespace, not a verifiable result: only a `∃ …` non-vacuity witness (any name; `Witness.nonvacuous` by convention) and `Witness.returns` are"

unsafe def runImplCore (thm proofMod marker trusted : String) (depRoots : Array String)
    (pre? : Option (ImportState × Environment)) : IO Unit := do
  let result ← (show AuditM Record from do
    let thmN := thm.toName
    let proofModN := proofMod.toName
    let auditImports : Array Import :=
      #[{ module := `Extracted }, { module := trusted.toName }, { module := proofModN }]
    let (envA, cleanState) ← (auditEnv auditImports (pre?.map (·.1)) : IO _)
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
    checkDataSymIdentities envA
    let cx := mkCtx envA depRoots
    -- 4. no non-trusted (consumer/proof/dependency) module declares a name with an `Extracted` component
    -- (A7, A9, and the consumer analogue of shadowing Extracted from a shared module)
    -- (the module of each constant is looked up in a table of the modules' trust, computed once;
    -- the offender reported is the one the first match of `const2ModIdx.toList` would be)
    let trustedMods : Array Bool := modNames.map (trustedModule ·)
    let offender? := envA.const2ModIdx.fold (init := (none : Option Name)) fun acc n idx =>
      if !trustedMods[idx.toNat]! && (n.anyS (· == "Extracted") || imitatesExtracted n) && !isGeneratedEqnLemma envA n then some n else acc
    if let some n := offender? then
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
    -- Round 14: the role of the theorem. A witness (`Witness.nonvacuous`/`Witness.returns`) is
    -- checked structurally against a main theorem of the module; every other theorem is a main
    -- theorem, whose runtime is quantified (`checkContractHyps … main`).
    let role := roleOfTy thmN ci.type
    let (matchedMain, matchedMains, matchedModules) ← match role with
      | .main => pure ("", #[], #[])
      | _ => do
        match ← runCore envA (Meta.MetaM.run' (checkWitness envA proofModN thmN role ci.type)) with
        | .ok (c, cs) =>
          let modOf := fun (n : Name) => match envA.getModuleIdxFor? n with
            | some i => modNames[i.toNat]!.toString
            | none => ""
          pure (c.toString, cs.map (·.toString), cs.map modOf)
        | .error m => fail s!"{thm} {m} (round 14, W2)"
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
    let (statement, statementExplicit, defs, extOut, notes, contractHyps) ←
      cleanEnvAndPrint cx thmN ci.type localDefs stubs extDefs cleanState (pre? := pre?.map (·.2))
        (main := role == .main)
    return { name := thm, kind, module := modName.toString, axioms := axs.map (·.toString),
             statement, statementExplicit, definitions := defs,
             modules := modNames.map (·.toString),
             external := externalNames.filterMap external.get?, externalDefinitions := extOut,
             notes, role := role.label, matchedMain, matchedMains, matchedModules, contractHyps, imports := importGraph envA }
  ).run
  match result with
  | .ok rec => IO.println (marker ++ (toJson rec).compress)
  | .error f => IO.println (marker ++ "ERROR " ++ f.msg)
  (← IO.getStdout).flush

unsafe def runImpl (thm proofMod marker trusted : String) (depRoots : Array String) : IO Unit :=
  runImplCore thm proofMod marker trusted depRoots none

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
    checkDataSymIdentities envA
    let cx := mkCtx envA depRoots aslTrustedRoots
    -- reserved namespaces: only the trusted builds may declare Extracted/JanusASL/ArmASL/Sail/
    -- JanusASLWords names, and the corollary module only the corollary
    let modNamesA := envA.header.moduleNames -- once: the projection rebuilds the array on every call
    for (n, idx) in envA.const2ModIdx.toList do
      let m := modNamesA[idx.toNat]!
      if cx.trusted m then continue
      if (n.anyS (· == "Extracted") || imitatesExtracted n) && !isGeneratedEqnLemma envA n then
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
    let (statement, statementExplicit, defs, extOut, notes, _) ←
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
