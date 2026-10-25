import Janus.Amd64.Instr

/-!
# A small x86-64 disassembler for diagnostics

`Instr.disasm pc len i` renders a decoded `Janus.Amd64.Instr` in Intel syntax (as
`objdump -M intel` does), with branch and RIP-relative targets resolved against the address of
the next instruction `pc + len`. It is only used in messages of the proof automation
(`janus64_run` stuck diagnostics and traces).

Constructors that are not handled fall back to their `Repr`.
-/

namespace Janus.Amd64.Disasm

open Janus.Amd64

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Signed value of a 64-bit field. -/
def sval (v : Nat) : Int := if v < 2 ^ 63 then v else (v : Int) - 2 ^ 64

def reg64 : Nat → String
  | 0 => "rax" | 1 => "rcx" | 2 => "rdx" | 3 => "rbx" | 4 => "rsp" | 5 => "rbp" | 6 => "rsi"
  | 7 => "rdi" | n => s!"r{n}"

def regW (w r : Nat) : String :=
  match w with
  | 64 => reg64 r
  | 32 => match r with
    | 0 => "eax" | 1 => "ecx" | 2 => "edx" | 3 => "ebx" | 4 => "esp" | 5 => "ebp" | 6 => "esi"
    | 7 => "edi" | n => s!"r{n}d"
  | 16 => match r with
    | 0 => "ax" | 1 => "cx" | 2 => "dx" | 3 => "bx" | 4 => "sp" | 5 => "bp" | 6 => "si"
    | 7 => "di" | n => s!"r{n}w"
  | _ => match r with
    | 0 => "al" | 1 => "cl" | 2 => "dl" | 3 => "bl" | 4 => "spl" | 5 => "bpl" | 6 => "sil"
    | 7 => "dil" | n => s!"r{n}b"

def highName : Nat → String
  | 0 => "ah" | 1 => "ch" | 2 => "dh" | _ => "bh"

def ptrName : Nat → String
  | 8 => "byte ptr " | 16 => "word ptr " | 32 => "dword ptr " | 64 => "qword ptr "
  | 128 => "xmmword ptr " | _ => ""

/-- `[base + index*scale + disp]`; RIP-relative operands are resolved when `next` is known. -/
def addrOff (next : Option Nat) (a : Addr) : String :=
  if a.rip then
    match next with
    | some n => s!"[rip {if sval a.disp < 0 then "-" else "+"} {hex (sval a.disp).natAbs}] ; {hex ((((n : Int) + sval a.disp) % 2 ^ 64).toNat)}"
    | none => s!"[rip {if sval a.disp < 0 then "-" else "+"} {hex (sval a.disp).natAbs}]"
  else
    let parts : List String :=
      (match a.base with | some b => [reg64 b] | none => []) ++
      (match a.index with
        | some i => [if a.scale = 0 then reg64 i else s!"{reg64 i}*{2 ^ a.scale}"]
        | none => [])
    let d := sval a.disp
    let body := " + ".intercalate parts
    let dispS := if d = 0 then (if parts.isEmpty then "0" else "")
      else if parts.isEmpty then (if d < 0 then "-" else "") ++ hex d.natAbs
      else if d < 0 then s!" - {hex d.natAbs}" else s!" + {hex d.toNat}"
    s!"[{body}{dispS}]"

/-- An address with its `fs:` segment prefix, if any. -/
def addr (next : Option Nat) (a : Addr) : String :=
  (if a.fs then "fs:" else "") ++ addrOff next a

def ymmName (l n : Nat) : String := if l = 256 then s!"ymm{n}" else s!"xmm{n}"

def sseName : SseOp → String
  | .xor => "pxor" | .and => "pand" | .or => "por" | .pcmpeqb => "pcmpeqb"
  | .punpcklbw => "punpcklbw" | .pshufb => "pshufb" | .psignb => "psignb"

def loc (next : Option Nat) (w : Nat) : Loc → String
  | .reg r => regW w r
  | .high r => highName r
  | .mem a => ptrName w ++ addr next a

def src (next : Option Nat) (w : Nat) : Src → String
  | .loc l => loc next w l
  | .imm v => hex v

def xloc (next : Option Nat) : XLoc → String
  | .xmm n => s!"xmm{n}"
  | .mem a => "xmmword ptr " ++ addr next a

def ccName (cc : Nat) : String :=
  match cc % 16 with
  | 0 => "o" | 1 => "no" | 2 => "b" | 3 => "ae" | 4 => "e" | 5 => "ne" | 6 => "be" | 7 => "a"
  | 8 => "s" | 9 => "ns" | 10 => "p" | 11 => "np" | 12 => "l" | 13 => "ge" | 14 => "le"
  | _ => "g"

def aluName : AluOp → String
  | .add => "add" | .or => "or" | .adc => "adc" | .sbb => "sbb" | .and => "and" | .sub => "sub"
  | .xor => "xor" | .cmp => "cmp"

def target (next : Option Nat) (rel : Nat) : String :=
  match next with
  | some n => hex ((n + rel) % 2 ^ 64)
  | none => s!"rip{if sval rel < 0 then "-" else "+"}{hex (sval rel).natAbs}"

/-- `disasm` without the `LOCK` wrapper. -/
def disasm0 (pc : Option Nat) (len : Nat) (i : Instr) : String :=
  let next := pc.map (· + len)
  match (some i : Option Instr) with
  | some (.alu op w dst s) => s!"{aluName op} {loc next w dst}, {src next w s}"
  | some (.test w a b) => s!"test {loc next w a}, {src next w b}"
  | some (.mov w dst s) => s!"mov {loc next w dst}, {src next w s}"
  | some (.movx signed dw sw dst s) =>
    let m := if signed then (if sw = 32 then "movsxd" else "movsx") else "movzx"
    s!"{m} {regW dw dst}, {loc next sw s}"
  | some (.lea w dst a) => s!"lea {regW w dst}, {addr next a}"
  | some (.unary op w dst) =>
    let m := match op with | .inc => "inc" | .dec => "dec" | .not => "not" | .neg => "neg"
    s!"{m} {loc next w dst}"
  | some (.mul1 signed w s) => s!"{if signed then "imul" else "mul"} {loc next w s}"
  | some (.imul w dst a b) =>
    match b with
    | .loc l => if a == .reg dst then s!"imul {regW w dst}, {loc next w l}"
      else s!"imul {regW w dst}, {loc next w a}, {loc next w l}"
    | .imm v => s!"imul {regW w dst}, {loc next w a}, {hex v}"
  | some (.div signed w s) => s!"{if signed then "idiv" else "div"} {loc next w s}"
  | some (.shift op w dst c) =>
    let m := match op with | .rol => "rol" | .ror => "ror" | .shl => "shl" | .shr => "shr" | .sar => "sar"
    s!"{m} {loc next w dst}, {match c with | .imm v => toString v | .loc _ => "cl"}"
  | some (.shd left w dst s c) =>
    s!"{if left then "shld" else "shrd"} {loc next w dst}, {regW w s}, {match c with | .imm v => toString v | .loc _ => "cl"}"
  | some (.bit op w dst off) =>
    let m := match op with | .bt => "bt" | .bts => "bts" | .btr => "btr" | .btc => "btc"
    s!"{m} {loc next w dst}, {src next w off}"
  | some (.count op w dst s) =>
    let m := match op with
      | .bsf => "bsf" | .bsr => "bsr" | .tzcnt => "tzcnt" | .lzcnt => "lzcnt" | .popcnt => "popcnt"
    s!"{m} {regW w dst}, {loc next w s}"
  | some (.bswap w r) => s!"bswap {regW w r}"
  | some (.setcc cc dst) => s!"set{ccName cc} {loc next 8 dst}"
  | some (.cmov cc w dst s) => s!"cmov{ccName cc} {regW w dst}, {loc next w s}"
  | some (.jcc cc rel) => s!"j{ccName cc} {target next rel}"
  | some (.jmp rel) => s!"jmp {target next rel}"
  | some (.jmpInd s) => s!"jmp {loc next 64 s}"
  | some (.call rel) => s!"call {target next rel}"
  | some (.callInd s) => s!"call {loc next 64 s}"
  | some (.ret n) => if n = 0 then "ret" else s!"ret {hex n}"
  | some (.push s) => s!"push {src next 64 s}"
  | some (.pop r) => s!"pop {reg64 r}"
  | some .leave => "leave"
  | some .nop => "nop"
  | some (.xchg w a b) => s!"xchg {loc next w a}, {loc next w b}"
  | some (.cbw w) => match w with | 16 => "cbw" | 32 => "cwde" | _ => "cdqe"
  | some (.cwd w) => match w with | 16 => "cwd" | 32 => "cdq" | _ => "cqo"
  | some (.flagOp op) => match op with | .clc => "clc" | .stc => "stc" | .cmc => "cmc"
  | some (.sseMov aligned d s) =>
    s!"{if aligned then "movaps" else "movups"} {xloc next d}, {xloc next s}"
  | some (.sseOp op d s) => s!"{sseName op} xmm{d}, {xloc next s}"
  | some (.vop op l d s1 s2) =>
    let s2' := match s2 with | .xmm n => ymmName l n | .mem a => addr next a
    s!"v{sseName op} {ymmName l d}, {ymmName l s1}, {s2'}"
  | some (.vmov al l d s) =>
    let f : XLoc → String := fun | .xmm n => ymmName l n | .mem a => addr next a
    s!"{if al then "vmovdqa" else "vmovdqu"} {f d}, {f s}"
  | some (.pmovmskb l d s) => s!"{if l = 256 then "vpmovmskb" else "pmovmskb"} {reg64 d}, {ymmName l s}"
  | some .vzeroupper => "vzeroupper"
  | some (.setDF b) => if b then "std" else "cld"
  | some (.rcx left w dst c) =>
    s!"{if left then "rcl" else "rcr"} {loc next w dst}, {match c with | .imm v => toString v | .loc _ => "cl"}"
  | some (.movdq w toX x g) =>
    let m := if w = 64 then "movq" else "movd"
    if toX then s!"{m} xmm{x}, {loc next w g}" else s!"{m} {loc next w g}, xmm{x}"
  | some (.movq d s) =>
    let f : XLoc → String := fun | .xmm n => s!"xmm{n}" | .mem a => "qword ptr " ++ addr next a
    s!"movq {f d}, {f s}"
  | some (.andn w d s1 s2) => s!"andn {regW w d}, {regW w s1}, {loc next w s2}"
  | some (.blsx op w d s) =>
    s!"{if op = 1 then "blsr" else if op = 2 then "blsmsk" else "blsi"} {regW w d}, {loc next w s}"
  | some (.bextr w d s c) => s!"bextr {regW w d}, {loc next w s}, {regW w c}"
  | some (.bzhi w d s c) => s!"bzhi {regW w d}, {loc next w s}, {regW w c}"
  | some (.shiftx op w d s c) =>
    let m := match op with | .shl => "shlx" | .sar => "sarx" | _ => "shrx"
    s!"{m} {regW w d}, {loc next w s}, {regW w c}"
  | some (.rorx w d s i) => s!"rorx {regW w d}, {loc next w s}, {i}"
  | some (.mulx w h l s) => s!"mulx {regW w h}, {regW w l}, {loc next w s}"
  | some (.pdep w d s m) => s!"pdep {regW w d}, {regW w s}, {loc next w m}"
  | some (.pext w d s m) => s!"pext {regW w d}, {regW w s}, {loc next w m}"
  | some (.movbe w d s) => s!"movbe {loc next w d}, {loc next w s}"
  | some (.vfmas w form negP negC d s2 s3) =>
    let m := (if negP then "vfnm" else "vfm") ++ (if negC then "sub" else "add") ++ toString form ++
      (if w = 64 then "sd" else "ss")
    let s3' := match s3 with | .xmm n => s!"xmm{n}" | .mem a => ptrName w ++ addr next a
    s!"{m} xmm{d}, xmm{s2}, {s3'}"
  | _ => toString (repr i)

/-- Disassemble `i` at `pc` with length `len` (both optional). -/
def disasm (pc : Option Nat) (len : Nat) (i : Instr) : String :=
  match i with
  | .locked j _ _ => "lock " ++ disasm0 pc len j
  | _ => disasm0 pc len i

end Janus.Amd64.Disasm
