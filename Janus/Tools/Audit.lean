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
* pretty-prints the statement in a **clean environment** that imports only `Janus` and
  `Extracted` (never the proof), with the allowed proof-local defs re-added, so the proof's
  unexpanders, delaborators, notations and instances cannot change what is printed (A2, A4).

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
  deriving ToJson

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

/-- Is `c` declared in a non-trusted (consumer/proof) module of `env`? -/
def isLocal (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx => !trustedModule env.header.moduleNames[idx.toNat]!
  | none => false

/-- All constants a non-trusted allowed def may reach that are themselves non-trusted; collected
so the clean environment can re-add them before pretty-printing. -/
partial def collectLocalDefs (env : Environment)
    (seen : Std.HashSet Name) (todo : List Name) : AuditM (Array Name) := do
  match todo with
  | [] => return seen.toArray
  | c :: rest =>
    if seen.contains c || !isLocal env c then collectLocalDefs env seen rest else
    let some ci := env.find? c | fail s!"missing constant {c}"
    -- Must be a plain def or theorem, safe, not opaque/axiom.
    match ci with
    | .defnInfo _ | .thmInfo _ => pure ()
    | _ => fail s!"the statement uses {c}, which is not a plain def or theorem"
    if ci.isUnsafe then fail s!"the statement uses the unsafe/partial definition {c}"
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    collectLocalDefs env (seen.insert c) (used.toList ++ rest)

/-- Build the clean environment: import only `Janus` and `Extracted`, with initializers so pp
works, then re-add the allowed proof-local defs and an axiom with the theorem's type. Reject a
proof-local def whose type's head is a class (a disguised instance, A1). -/
unsafe def cleanEnvAndPrint (thm : Name) (thmType : Expr) (localDefs : Array ConstantInfo)
    (envA : Environment) : AuditM (String × Array String) := do
  enableInitializersExecution
  let env ← importModules (loadExts := true)
    #[{ module := `Extracted }, { module := `Janus }] {}
  -- Re-add proof-local defs in dependency order.
  let mut env := env
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
          if isClass env headTy then
            fail s!"the statement uses the proof-local {ci.name}, whose type is the class {headTy} (a disguised instance)"
        let some decl := ciToDecl ci
          | fail s!"the statement uses the proof-local {ci.name}, which is not a def or theorem"
        env ← kernelAdd env decl
        progress := true
      else if (env.find? ci.name).isNone then
        next := next.push ci
    pending := next
  if !pending.isEmpty then
    fail "cannot order the proof-local definitions of the statement"
  -- Add the theorem's type as an axiom (printing only; soundness is from collectAxioms/replay).
  env ← kernelAdd env (.axiomDecl { name := thm, levelParams := [], type := thmType, isUnsafe := false })
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

unsafe def runImpl (thm proofMod marker trusted : String) : IO Unit := do
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
    -- 4. no non-trusted (consumer/proof) module declares a name with an `Extracted` component
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
    -- close over the non-trusted defs reachable from the statement
    let localNames ← collectLocalDefs envA {} localSeed.toList
    let localDefs := localNames.filterMap envA.find?
    -- 6. clean-environment pretty-print
    let (statement, defs) ← cleanEnvAndPrint thmN ci.type localDefs envA
    return Record.mk thm kind modName.toString (axs.map (·.toString)) statement defs
      (envA.header.moduleNames.map (·.toString))
  ).run
  match result with
  | .ok rec => IO.println (marker ++ (toJson rec).compress)
  | .error f => IO.println (marker ++ "ERROR " ++ f.msg)
  (← IO.getStdout).flush

/-- Audit entry point. Run via a generated, trusted `Audit.lean` that does
`#eval JanusAudit.run "<thm>" "<proof module>" "<marker>" "JanusTrusted"` and imports only this
module (never the proof), so the proof's `initialize`/macros never run. `run` itself imports the
proof's compiled module with `importModules (loadExts := false)`, which does not run its
initializers. The `@[implemented_by]` wrapper lets the trusted `#eval` call the `unsafe` logic. -/
@[implemented_by runImpl]
opaque run (thm proofMod marker trusted : String) : IO Unit

end JanusAudit
