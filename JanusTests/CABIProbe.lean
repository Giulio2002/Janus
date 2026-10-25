import Janus.CABI.AAPCS64
import Janus.CABI.SysV

/-!
# The C ABI probe: Janus's classification, printed for the differential test

`scripts/cabi-probe.sh` (the Go program `scripts/cabiprobe`) runs this file with
`lake env lean --run JanusTests/CABIProbe.lean` and feeds it one prototype per line:

```
<id> <ret | v> <named | -> <arg type> ...
```

with the types written `i1 i2 i4 i8 i16` (signed integers), `u1 … u16`, `p` (pointer), `h f d ld`
(`_Float16`, `float`, `double`, `long double`), `cf cd cld` (`_Complex`), `v8 v16` (vectors),
`s(t,…)`, `u(t,…)` (struct, union) and `a<n>(t)` (array). For every prototype it prints, for
both ABIs, the layout of each type (size, alignment, the byte ranges of its scalars), where
each argument and the result go (`Sig.passing`, `Sig.resultPassing`), the stacked-argument
size, `AL` (System V) and, for a variadic prototype, the `va_list` fields after `va_start` and
after each `va_arg`. The Go side compiles callers and callees of each prototype with gcc and
clang and compares what the code does with these lines; nothing here is trusted by a proof.
-/

open Janus.C

namespace Janus.C.Probe

/-- Parse a type from a character list; returns the type and the rest. -/
partial def parseType : List Char → Option (CType × List Char)
  | 'i' :: cs => parseInt true cs
  | 'u' :: '(' :: cs => (parseList cs).map fun (ts, r) => (.union ts, r)
  | 'u' :: cs => parseInt false cs
  | 'p' :: cs => some (.ptr, cs)
  | 'h' :: cs => some (.half, cs)
  | 'f' :: cs => some (.float, cs)
  | 'l' :: 'd' :: cs => some (.ldouble, cs)
  | 'd' :: cs => some (.double, cs)
  | 'c' :: 'l' :: 'd' :: cs => some (.complex .ldouble, cs)
  | 'c' :: 'f' :: cs => some (.complex .float, cs)
  | 'c' :: 'd' :: cs => some (.complex .double, cs)
  | 'v' :: cs => (parseNat cs).map fun (n, r) => (.vec n, r)
  | 's' :: '(' :: cs => (parseList cs).map fun (ts, r) => (.struct ts, r)
  | 'a' :: cs => do
    let (n, r) ← parseNat cs
    match r with
    | '(' :: r => do
      let (t, r) ← parseType r
      match r with
      | ')' :: r => some (.array t n, r)
      | _ => none
    | _ => none
  | _ => none
where
  parseNat (cs : List Char) : Option (Nat × List Char) :=
    let ds := cs.takeWhile Char.isDigit
    if ds.isEmpty then none else some (String.toNat! (String.ofList ds), cs.drop ds.length)
  parseInt (signed : Bool) (cs : List Char) : Option (CType × List Char) :=
    (parseNat cs).map fun (n, r) => (.int n signed, r)
  parseList (cs : List Char) : Option (List CType × List Char) := do
    let (t, r) ← parseType cs
    match r with
    | ',' :: r => let (ts, r) ← parseList r; some (t :: ts, r)
    | ')' :: r => some ([t], r)
    | _ => none

def parse (s : String) : Option CType :=
  match parseType s.toList with
  | some (t, []) => some t
  | _ => none

def leafLen : CType.Leaf → Nat
  | .int n => n
  | .sse n => n
  | .vec16 => 16
  | .x87 => 10

def showLoc : Loc → String
  | .gpr r => s!"x{r}"
  | .vec r o => s!"v{r}.{o}"
  | .stack o => s!"s{o}"
  | .x87 i => s!"st{i}"

def showPiece (p : Piece) : String := s!"{showLoc p.loc}:{p.src}+{p.len}"

def showPassing : Passing → String
  | .direct ps => "direct " ++ " ".intercalate (ps.map showPiece)
  | .indirect l => "indirect " ++ showLoc l

def leafKind : CType.Leaf → String
  | .int _ => "i"
  | .sse _ => "s"
  | .vec16 => "v"
  | .x87 => "x"

def showType (k : String) (t : CType) : String :=
  let ls := (CType.leaves 0 t).map fun (o, l) => s!"{o}:{leafLen l}:{leafKind l}"
  s!"type {k} size {CType.size t} align {CType.align t} leaves {",".intercalate ls}"

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

def parseHex : List Char → List Nat
  | a :: b :: cs => (16 * hexVal a + hexVal b) :: parseHex cs
  | _ => []

def toHex (v n : Nat) : String :=
  String.join ((List.range n).map fun i =>
    let b := v / 256 ^ i % 256
    String.ofList [Nat.digitChar (b / 16), Nat.digitChar (b % 16)])

/-- A memory snapshot: regions `base:hex`. -/
def readMem (regions : List (Nat × Array Nat)) (a n : Nat) : Nat :=
  (List.range n).foldr (fun i acc =>
    let b := (regions.find? fun (base, bs) => base ≤ a + i ∧ a + i < base + bs.size).map
      (fun (base, bs) => bs[a + i - base]!) |>.getD 0
    b + 256 * acc) 0

def parseRegions (ws : List String) : List (Nat × Array Nat) :=
  ws.filterMap fun w => match w.splitOn ":" with
    | [b, h] => b.toNat?.map fun base => (base, (parseHex h.toList).toArray)
    | _ => none

/-- `vaeval <a64|sysv> <id> <va_list fields> <types> mem <regions>`: Janus's `va_arg` sequence on
a memory snapshot of the compiled callee (its `va_list` right after `va_start`, its save areas,
the stacked arguments). -/
def vaeval (abi id : String) (rest : List String) : List String :=
  let (pre, post) := rest.span (· ≠ "mem")
  let regions := parseRegions (post.drop 1)
  let rd := readMem regions
  let nf := if abi = "a64" then 5 else 4
  let fields := pre.take nf
  match (pre.drop nf).mapM parse with
  | none => [s!"error {id} vaeval types"]
  | some ts =>
    let vals : Option (List Nat) :=
      if abi = "a64" then
        match fields with
        | [st, gt, vt, go, vo] => do
          let l : AAPCS64.VaList := ⟨← st.toNat?, ← gt.toNat?, ← vt.toNat?, ← go.toInt?, ← vo.toInt?⟩
          some (AAPCS64.vaArgs rd l ts).1
        | _ => none
      else
        match fields with
        | [gp, fp, ov, rs] => do
          let l : SysV.VaList := ⟨← gp.toNat?, ← fp.toNat?, ← ov.toNat?, ← rs.toNat?⟩
          some (SysV.vaArgs rd l ts).1
        | _ => none
    match vals with
    | none => [s!"error {id} vaeval fields"]
    | some vs => (vs.zip ts).zipIdx.map fun ((v, t), i) => s!"vaval {id} {i + 1} {toHex v (CType.size t)}"

def run (line : String) : List String :=
  match line.splitOn " " |>.filter (· ≠ "") with
  | "vaeval" :: abi :: id :: rest => vaeval abi id rest
  | id :: ret :: named :: args =>
    let ret? := if ret = "v" then some none else (parse ret).map some
    let args? := args.mapM parse
    let named? : Option (Option Nat) := if named = "-" then some none else
      (named.toNat?).map some
    match ret?, args?, named? with
    | some ret, some args, some named =>
      let types := (args.zipIdx.map fun (t, i) => showType (toString i) t) ++
        (match ret with | some t => [showType "r" t] | none => [])
      let a64 : AAPCS64.Sig := ⟨ret, args, named⟩
      let sv : SysV.Sig := ⟨ret, args, named⟩
      let showRet (r : Option Passing) : String :=
        match r with | some p => "ret " ++ showPassing p | none => "ret void"
      let a64va : List String := match named with
        | none => []
        | some k =>
          let st := (AAPCS64.assignAll {} (args.take k)).2
          let l0 := AAPCS64.vaStart st 0 0 0
          let showL (l : AAPCS64.VaList) := s!"{l.stack} {l.grOffs} {l.vrOffs}"
          let rec go (l : AAPCS64.VaList) (i : Nat) : List CType → List String
            | [] => []
            | t :: ts => let l' := (AAPCS64.vaArg (fun _ _ => 0) l t).2
                         s!"va {i} {showL l'}" :: go l' (i + 1) ts
          s!"va 0 {showL l0}" :: go l0 1 (args.drop k)
      let svva : List String := match named with
        | none => []
        | some k =>
          let st := (SysV.assignAll sv.start (args.take k)).2
          let l0 := SysV.vaStart st 0 0
          let showL (l : SysV.VaList) := s!"{l.gpOffset} {l.fpOffset} {l.overflow}"
          let rec go2 (l : SysV.VaList) (i : Nat) : List CType → List String
            | [] => []
            | t :: ts => let l' := (SysV.vaArg (fun _ _ => 0) l t).2
                         s!"va {i} {showL l'}" :: go2 l' (i + 1) ts
          s!"va 0 {showL l0}" :: go2 l0 1 (args.drop k)
      [s!"sig {id} aapcs64"] ++ types ++
        (a64.passing.zipIdx.map fun (p, i) => s!"arg {i} {showPassing p}") ++
        [showRet a64.resultPassing, s!"stack {a64.stackSize}"] ++ a64va ++
      [s!"sig {id} sysv"] ++ types ++
        (sv.passing.zipIdx.map fun (p, i) => s!"arg {i} {showPassing p}") ++
        [showRet sv.resultPassing, s!"stack {sv.stackSize}", s!"vecregs {sv.vecRegs}"] ++ svva ++
      ["end"]
    | _, _, _ => [s!"error {id} cannot parse"]
  | _ => if line.trimAscii.isEmpty then [] else [s!"error cannot parse: {line}"]

end Janus.C.Probe

partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return
    for l in Janus.C.Probe.run line.trimAscii.toString do
      stdout.putStrLn l
    loop
  loop
