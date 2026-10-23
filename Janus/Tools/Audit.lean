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
  dependency code running in this trusted process) do not apply either.

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

/-- Build the clean environment: import only `Janus` and `Extracted`, with initializers so pp
works, then add type-only stubs for the dependency constants the statement reaches, re-add the
allowed proof-local defs and an axiom with the theorem's type. Reject a proof-local def whose
type's head is a class (a disguised instance, A1). No proof or dependency module is imported, so
none of their initializers, notations, unexpanders or delaborators exist here. -/
unsafe def cleanEnvAndPrint (cx : Ctx) (thm : Name) (thmType : Expr) (localDefs : Array ConstantInfo)
    (stubs : Array ConstantInfo) : AuditM (String × Array String) := do
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
  let opts := (Options.empty.setBool `pp.fullNames true)
  let ctx := { mkCoreCtx with options := opts }
  let printAll : MetaM (String × Array String) := do
    let sig ← PrettyPrinter.ppSignature thm
    let mut defs := #[]
    for ci in localDefs do
      let tyFmt ← Meta.ppExpr ci.type
      let valFmt ← match ci.value? with
        | some v => Meta.ppExpr v
        | none => pure (Std.Format.text "<opaque>")
      defs := defs.push s!"{ci.name} : {tyFmt.pretty 10000} := {valFmt.pretty 10000}"
    return (sig.fmt.pretty 10000, defs)
  runCore env (Meta.MetaM.run' printAll)

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
    let (statement, defs) ← cleanEnvAndPrint cx thmN ci.type localDefs stubs
    return Record.mk thm kind modName.toString (axs.map (·.toString)) statement defs
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
