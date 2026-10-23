import Janus.Arm64.Instr
import Janus.Arm64.Bits

/-!
# A small AArch64 disassembler for diagnostics

`Instr.disasm pc i` renders a decoded `Janus.Arm64.Instr` in (roughly) GNU assembler syntax,
with the common aliases (`mov`, `cmp`, `lsl`, `mul`, `cset`, …) and branch targets resolved
against `pc`. It is only used in messages of the proof automation (`janus_run` stuck
diagnostics and traces); nothing depends on it logically.

Constructors that are not handled (for example ones added to `Instr` later) fall back to their
`Repr`, so the printer never has to be updated in lockstep with the ISA.
-/

namespace Janus.Arm64.Disasm

open Janus.Arm64

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- Signed value of a `w`-bit two's complement field. -/
def sval (w v : Nat) : Int := if v < 2 ^ (w - 1) then v else (v : Int) - 2 ^ w

def simm (i : Int) : String := if i < 0 then s!"#-{hex i.natAbs}" else s!"#{hex i.toNat}"

def imm (n : Nat) : String := if n < 10 then s!"#{n}" else s!"#{hex n}"

/-- Register `r` of the `X` (`sf`) or `W` file; `31` is `xzr`/`wzr` or `sp`/`wsp`. -/
def reg (sf : Bool) (r : Nat) (sp : Bool := false) : String :=
  if r = 31 then (if sp then (if sf then "sp" else "wsp") else (if sf then "xzr" else "wzr"))
  else (if sf then "x" else "w") ++ toString r

def xr (r : Nat) (sp := false) := reg true r sp

def condName (c : Nat) : String :=
  match c % 16 with
  | 0 => "eq" | 1 => "ne" | 2 => "hs" | 3 => "lo" | 4 => "mi" | 5 => "pl" | 6 => "vs"
  | 7 => "vc" | 8 => "hi" | 9 => "ls" | 10 => "ge" | 11 => "lt" | 12 => "gt" | 13 => "le"
  | 14 => "al" | _ => "nv"

def shiftName : ShiftType → String
  | .lsl => "lsl" | .lsr => "lsr" | .asr => "asr" | .ror => "ror"

def extName : ExtendType → String
  | .uxtb => "uxtb" | .uxth => "uxth" | .uxtw => "uxtw" | .uxtx => "uxtx"
  | .sxtb => "sxtb" | .sxth => "sxth" | .sxtw => "sxtw" | .sxtx => "sxtx"

def target (pc : Option Nat) (off : Int) : String :=
  match pc with
  | some p => hex ((((p : Int) + off) % 2 ^ 64).toNat)
  | none => s!"pc{if off < 0 then "-" else "+"}{hex off.natAbs}"

def shifted (shift : ShiftType) (amt : Nat) : String :=
  if amt = 0 && shift == .lsl then "" else s!", {shiftName shift} #{amt}"

/-- Mnemonic of a single-register load/store from `size` and `opc`. -/
def ldstName (size opc : Nat) (unscaled : Bool) : String × Bool :=
  -- (mnemonic, register is 64-bit)
  let u := if unscaled then "ur" else "r"
  let sfx := match size with | 0 => "b" | 1 => "h" | _ => ""
  match opc with
  | 0 => (s!"st{u}{sfx}", size == 3)
  | 1 => (s!"ld{u}{sfx}", size == 3)
  | 2 => (s!"ld{u}s{if size == 2 then "w" else sfx}", true)
  | _ => (s!"ld{u}s{sfx}", false)

/-- Disassemble `i` (at `pc`, if known, to resolve branch targets). -/
def disasm (pc : Option Nat) (i : Instr) : String :=
  match (some i : Option Instr) with
  | some (.adr op immlo immhi rd) =>
    let v := immhi * 4 + immlo
    if op then
      let off := sval 21 v * 4096
      let tgt := match pc with
        | some p => hex (((((p / 4096) * 4096 : Nat) : Int) + off).toNat)
        | none => simm off
      s!"adrp {xr rd}, {tgt}"
    else s!"adr {xr rd}, {target pc (sval 21 v)}"
  | some (.addSubImm sf op S sh imm12 rn rd) =>
    let im := imm imm12 ++ (if sh then ", lsl #12" else "")
    if !op && !S && imm12 = 0 && !sh && (rn = 31 || rd = 31) then
      s!"mov {reg sf rd true}, {reg sf rn true}"
    else if S && rd = 31 then s!"{if op then "cmp" else "cmn"} {reg sf rn true}, {im}"
    else
      let m := (if op then "sub" else "add") ++ (if S then "s" else "")
      s!"{m} {reg sf rd (!S)}, {reg sf rn true}, {im}"
  | some (.logicalImm sf opc N immr imms rn rd) =>
    let w := if sf then 64 else 32
    let v := ((decodeBitMasks N imms immr true w).getD (0, 0)).1
    let m := match opc with | .and => "and" | .orr => "orr" | .eor => "eor" | .ands => "ands"
    if opc == .ands && rd = 31 then s!"tst {reg sf rn}, #{hex v}"
    else if opc == .orr && rn = 31 then s!"mov {reg sf rd true}, #{hex v}"
    else s!"{m} {reg sf rd (opc != .ands)}, {reg sf rn}, #{hex v}"
  | some (.moveWide sf opc hw imm16 rd) =>
    let m := match opc with | .movn => "movn" | .movz => "movz" | .movk => "movk"
    let sh := if hw = 0 then "" else s!", lsl #{16 * hw}"
    if opc == .movz then s!"mov {reg sf rd}, #{hex (imm16 * 2 ^ (16 * hw))}"
    else s!"{m} {reg sf rd}, {imm imm16}{sh}"
  | some (.bitfield sf opc _ immr imms rn rd) =>
    let w := if sf then 64 else 32
    match opc with
    | .ubfm =>
      if imms + 1 = immr then s!"lsl {reg sf rd}, {reg sf rn}, #{w - immr}"
      else if imms = w - 1 then s!"lsr {reg sf rd}, {reg sf rn}, #{immr}"
      else if immr = 0 && imms = 7 then s!"uxtb {reg sf rd}, {reg false rn}"
      else if immr = 0 && imms = 15 then s!"uxth {reg sf rd}, {reg false rn}"
      else if imms < immr then s!"ubfiz {reg sf rd}, {reg sf rn}, #{w - immr}, #{imms + 1}"
      else s!"ubfx {reg sf rd}, {reg sf rn}, #{immr}, #{imms + 1 - immr}"
    | .sbfm =>
      if imms = w - 1 then s!"asr {reg sf rd}, {reg sf rn}, #{immr}"
      else if immr = 0 && imms = 31 then s!"sxtw {reg sf rd}, {reg false rn}"
      else if immr = 0 && imms = 7 then s!"sxtb {reg sf rd}, {reg false rn}"
      else if immr = 0 && imms = 15 then s!"sxth {reg sf rd}, {reg false rn}"
      else s!"sbfx {reg sf rd}, {reg sf rn}, #{immr}, #{imms + 1 - immr}"
    | .bfm => s!"bfm {reg sf rd}, {reg sf rn}, #{immr}, #{imms}"
  | some (.extr sf _ rm imms rn rd) =>
    if rn = rm then s!"ror {reg sf rd}, {reg sf rn}, #{imms}"
    else s!"extr {reg sf rd}, {reg sf rn}, {reg sf rm}, #{imms}"
  | some (.b op imm26) => s!"{if op then "bl" else "b"} {target pc (sval 28 (imm26 * 4))}"
  | some (.bcond imm19 cond) => s!"b.{condName cond} {target pc (sval 21 (imm19 * 4))}"
  | some (.cb sf op imm19 rt) =>
    s!"{if op then "cbnz" else "cbz"} {reg sf rt}, {target pc (sval 21 (imm19 * 4))}"
  | some (.tb b5 op b40 imm14 rt) =>
    let bitPos := (if b5 then 32 else 0) + b40
    s!"{if op then "tbnz" else "tbz"} {reg b5 rt}, #{bitPos}, {target pc (sval 16 (imm14 * 4))}"
  | some (.br rn) => s!"br {xr rn}"
  | some (.blr rn) => s!"blr {xr rn}"
  | some (.ret rn) => if rn = 30 then "ret" else s!"ret {xr rn}"
  | some (.hint crm op2) =>
    match crm, op2 with
    | 0, 0 => "nop" | 0, 1 => "yield" | 0, 2 => "wfe" | 0, 3 => "wfi" | 0, 4 => "sev"
    | _, _ => s!"hint #{crm * 8 + op2}"
  | some (.barrier crm op2) =>
    let m := match op2 with | 4 => "dsb" | 5 => "dmb" | 6 => "isb" | _ => "barrier"
    let opt := match crm with
      | 15 => "sy" | 14 => "st" | 13 => "ld" | 11 => "ish" | 10 => "ishst" | 9 => "ishld"
      | 7 => "nsh" | 3 => "osh" | k => s!"#{k}"
    if op2 = 6 && crm = 15 then "isb" else s!"{m} {opt}"
  | some (.ldrLit opc imm19 rt) =>
    let (m, sf) := match opc with | 0 => ("ldr", false) | 1 => ("ldr", true) | _ => ("ldrsw", true)
    s!"{m} {reg sf rt}, {target pc (sval 21 (imm19 * 4))}"
  | some (.ldstUImm size opc imm12 rn rt) =>
    let (m, sf) := ldstName size opc false
    let off := imm12 * 2 ^ size
    s!"{m} {reg sf rt}, [{xr rn true}{if off = 0 then "" else s!", {imm off}"}]"
  | some (.ldstImm9 size opc mode imm9 rn rt) =>
    let off := sval 9 imm9
    match mode with
    | .unscaled =>
      let (m, sf) := ldstName size opc true
      s!"{m} {reg sf rt}, [{xr rn true}{if off = 0 then "" else s!", {simm off}"}]"
    | .post =>
      let (m, sf) := ldstName size opc false
      s!"{m} {reg sf rt}, [{xr rn true}], {simm off}"
    | .pre =>
      let (m, sf) := ldstName size opc false
      s!"{m} {reg sf rt}, [{xr rn true}, {simm off}]!"
  | some (.ldstReg size opc rm option S rn rt) =>
    let (m, sf) := ldstName size opc false
    let amt := if S then size else 0
    let idx := match option with
      | .uxtx => s!"{xr rm}{if S then s!", lsl #{amt}" else ""}"
      | .sxtx => s!"{xr rm}, sxtx{if S then s!" #{amt}" else ""}"
      | e => s!"{reg false rm}, {extName e}{if S then s!" #{amt}" else ""}"
    s!"{m} {reg sf rt}, [{xr rn true}, {idx}]"
  | some (.ldstPair opc mode L imm7 rt2 rn rt) =>
    let sf := opc ≠ 0
    let m := if opc = 1 then "ldpsw" else if L then "ldp" else "stp"
    let off := sval 7 imm7 * 2 ^ (2 + opc / 2)
    let regs := s!"{reg sf rt}, {reg sf rt2}"
    match mode with
    | .offset => s!"{m} {regs}, [{xr rn true}{if off = 0 then "" else s!", {simm off}"}]"
    | .post => s!"{m} {regs}, [{xr rn true}], {simm off}"
    | .pre => s!"{m} {regs}, [{xr rn true}, {simm off}]!"
  | some (.logicalShifted sf opc shift N rm imm6 rn rd) =>
    let base := match opc with | .and => "and" | .orr => "orr" | .eor => "eor" | .ands => "ands"
    let m := if N then (match opc with
      | .and => "bic" | .orr => "orn" | .eor => "eon" | .ands => "bics") else base
    let sh := shifted shift imm6
    if opc == .orr && !N && rn = 31 && imm6 = 0 then s!"mov {reg sf rd}, {reg sf rm}"
    else if opc == .orr && N && rn = 31 then s!"mvn {reg sf rd}, {reg sf rm}{sh}"
    else if opc == .ands && !N && rd = 31 then s!"tst {reg sf rn}, {reg sf rm}{sh}"
    else s!"{m} {reg sf rd}, {reg sf rn}, {reg sf rm}{sh}"
  | some (.addSubShifted sf op S shift rm imm6 rn rd) =>
    let sh := shifted shift imm6
    if S && rd = 31 then s!"{if op then "cmp" else "cmn"} {reg sf rn}, {reg sf rm}{sh}"
    else if op && rn = 31 then s!"neg{if S then "s" else ""} {reg sf rd}, {reg sf rm}{sh}"
    else
      let m := (if op then "sub" else "add") ++ (if S then "s" else "")
      s!"{m} {reg sf rd}, {reg sf rn}, {reg sf rm}{sh}"
  | some (.addSubExt sf op S rm option imm3 rn rd) =>
    let m := (if op then "sub" else "add") ++ (if S then "s" else "")
    let rmS := match option with
      | .uxtx | .sxtx => reg true rm
      | _ => reg false rm
    let ext := if (option == .uxtx || option == .uxtw && !sf) && imm3 = 0 then ""
      else s!", {extName option}{if imm3 = 0 then "" else s!" #{imm3}"}"
    if S && rd = 31 then s!"{if op then "cmp" else "cmn"} {reg sf rn true}, {rmS}{ext}"
    else s!"{m} {reg sf rd (!S)}, {reg sf rn true}, {rmS}{ext}"
  | some (.addSubCarry sf op S rm rn rd) =>
    let m := (if op then "sbc" else "adc") ++ (if S then "s" else "")
    if op && rn = 31 then s!"ngc{if S then "s" else ""} {reg sf rd}, {reg sf rm}"
    else s!"{m} {reg sf rd}, {reg sf rn}, {reg sf rm}"
  | some (.condCmpReg sf op rm cond rn nzcv) =>
    s!"{if op then "ccmp" else "ccmn"} {reg sf rn}, {reg sf rm}, #{nzcv}, {condName cond}"
  | some (.condCmpImm sf op imm5 cond rn nzcv) =>
    s!"{if op then "ccmp" else "ccmn"} {reg sf rn}, #{imm5}, #{nzcv}, {condName cond}"
  | some (.condSel sf op rm cond o2 rn rd) =>
    let inv := condName (cond ^^^ 1)
    match op, o2 with
    | false, false => s!"csel {reg sf rd}, {reg sf rn}, {reg sf rm}, {condName cond}"
    | false, true =>
      if rn = 31 && rm = 31 then s!"cset {reg sf rd}, {inv}"
      else if rn = rm then s!"cinc {reg sf rd}, {reg sf rn}, {inv}"
      else s!"csinc {reg sf rd}, {reg sf rn}, {reg sf rm}, {condName cond}"
    | true, false =>
      if rn = 31 && rm = 31 then s!"csetm {reg sf rd}, {inv}"
      else s!"csinv {reg sf rd}, {reg sf rn}, {reg sf rm}, {condName cond}"
    | true, true =>
      if rn = rm then s!"cneg {reg sf rd}, {reg sf rn}, {inv}"
      else s!"csneg {reg sf rd}, {reg sf rn}, {reg sf rm}, {condName cond}"
  | some (.madd sf o0 rm ra rn rd) =>
    if ra = 31 then s!"{if o0 then "mneg" else "mul"} {reg sf rd}, {reg sf rn}, {reg sf rm}"
    else s!"{if o0 then "msub" else "madd"} {reg sf rd}, {reg sf rn}, {reg sf rm}, {reg sf ra}"
  | some (.maddl U o0 rm ra rn rd) =>
    let p := if U then "u" else "s"
    if ra = 31 && !o0 then s!"{p}mull {xr rd}, {reg false rn}, {reg false rm}"
    else s!"{p}{if o0 then "msubl" else "maddl"} {xr rd}, {reg false rn}, {reg false rm}, {xr ra}"
  | some (.mulh U rm rn rd) => s!"{if U then "umulh" else "smulh"} {xr rd}, {xr rn}, {xr rm}"
  | some (.div sf o1 rm rn rd) =>
    s!"{if o1 then "sdiv" else "udiv"} {reg sf rd}, {reg sf rn}, {reg sf rm}"
  | some (.shiftV sf op2 rm rn rd) => s!"{shiftName op2} {reg sf rd}, {reg sf rn}, {reg sf rm}"
  | some (.rbit sf rn rd) => s!"rbit {reg sf rd}, {reg sf rn}"
  | some (.rev sf opc rn rd) =>
    let m := match opc, sf with | 1, _ => "rev16" | 2, true => "rev32" | _, _ => "rev"
    s!"{m} {reg sf rd}, {reg sf rn}"
  | some (.clz sf rn rd) => s!"clz {reg sf rd}, {reg sf rn}"
  | some (.cls sf rn rd) => s!"cls {reg sf rd}, {reg sf rn}"
  | _ => toString (repr i)

end Janus.Arm64.Disasm
