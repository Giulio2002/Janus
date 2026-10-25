import Janus.Amd64.State
import Janus.Amd64.Instr

/-!
# Executing the x87 instructions (trusted)

`X87.exec` runs one decoded x87 instruction (`Instr.x87`) on `State`; `Janus.Amd64.exec`
delegates to it with the linear address of the memory operand (if any) and the `RFLAGS`
condition evaluator (for `FCMOVcc`). The operations are those of `Janus.Amd64.X87`. Every case
follows the SDM's `Operation` section; faults:

* **`#MF` (`fpuException`)**: a *waiting* instruction (every supported one except `FNSTCW`,
  `FNSTSW`, `FNCLEX`, `FNINIT`) faults when an exception is pending (`St.pending`); an
  instruction that raises an exception unmasked in the control word faults before writing
  anything (see `Janus.Amd64.X87` on why this is conservative); `FLDCW` faults when the new
  control word unmasks a raised flag.
* **stack fault (`fpuStack`)**: reading an empty register (underflow) or pushing onto an in-use
  `ST(7)` (overflow). The hardware's masked response (`IE` + `SF`, the indefinite) is not
  modelled.
* `undefinedResult` for an arithmetic instruction under the reserved precision control `01`,
  `undefinedFlag` for `FNSTSW` while a condition code is undefined and for `FCMOVcc` reading an
  undefined status flag.

Condition codes follow "FPU Flags Affected": `C1` is the rounded-up bit of a rounding
instruction, 0 after loads, exchanges, sign operations and comparisons, the sign for `FXAM`;
`C0 C2 C3` are set by the comparisons and `FXAM`, kept by `FCOMI`/`FUCOMI`, and undefined
otherwise (as is every condition code after `FLDCW`, `FNSTCW`, `FNSTSW`, `FNCLEX`, `FWAIT`,
`FNOP`, `FCMOVcc`).
-/

namespace Janus.Amd64.X87

open Janus.Float

/-- The memory operand's linear address (the decoder always supplies one for a memory form). -/
def memAddr (pc : Nat) : Option Nat → Except Fault Nat
  | some a => .ok a
  | none => .error (.undefinedResult pc)

/-- `ST(i)`, or a stack-underflow fault. -/
def getST (t : St) (pc i : Nat) : Except Fault Nat :=
  match t.get i with
  | some v => .ok v
  | none => .error (.fpuStack pc)

/-- An arithmetic or comparison operand as double-extended, with whether it was a denormal
binary32/64 memory operand (`DE`). Integers convert exactly; a signalling NaN is not quieted
here (the operation's NaN rules see it). -/
def operand (t : St) (m : Memory) (pc : Nat) (addr : Option Nat) : Src → Except Fault (Nat × Bool)
  | .st i =>
    match getST t pc i with
    | .ok v => .ok (v, false)
    | .error e => .error e
  | .mem k =>
    match memAddr pc addr with
    | .error e => .error e
    | .ok a =>
      match Janus.Amd64.load m a k.size with
      | .error e => .error e
      | .ok v =>
        match k with
        | .f32 => .ok (extend binary32 v)
        | .f64 => .ok (extend binary64 v)
        | .f80 => .ok (v, false)
        | .i16 => .ok (ofInt 16 v, false)
        | .i32 => .ok (ofInt 32 v, false)
        | .i64 => .ok (ofInt 64 v, false)

/-- `dst op src` at precision `p` (`subr`/`divr` reverse the operands). -/
def arithOp (op : Arith) (p : Nat) (rm : RM) (d s : Nat) (sDen : Bool) : XR :=
  match op with
  | .add => binop .add p rm d s sDen
  | .mul => binop .mul p rm d s sDen
  | .sub => binop .sub p rm d s sDen
  | .subr => binop .sub p rm s d sDen
  | .div => binop .div p rm d s sDen
  | .divr => binop .div p rm s d sDen

/-- The integer width of an integer memory format. -/
def MemFmt.intWidth : MemFmt → Nat
  | .i16 => 16 | .i32 => 32 | _ => 64

/-- Finish: the new x87 state `t'` and `RIP` advanced. -/
def fin (s : State) (next : W64) (t' : St) : Except Fault State := .ok { s with x87 := t', rip := next }

/-- Pop when `b`. -/
def St.popIf (t : St) (b : Bool) : St := if b then t.pop else t

/-- The condition codes `C3 C2 C0` from the 3-bit code `c` (bits 2, 1, 0), with `C1 = c1`. -/
def St.setCC (t : St) (c : Nat) (c1 : Option Bool) : St :=
  { t with c0 := some (c % 2 = 1), c1 := c1, c2 := some (c / 2 % 2 = 1), c3 := some (c / 4 % 2 = 1) }

/-- Execute a waiting instruction (no exception pending). `t = s.x87`. -/
def execWaiting (s : State) (pc : Nat) (next : W64) (op : Op) (addr : Option Nat)
    (cond : Nat → Option Bool) : Except Fault State :=
  let t := s.x87
  let cw := s.fpucw.toNat
  let rm := rounding cw
  let trap (o : XR) : Bool := o.traps &&& unmasked cw != 0
  match op with
  | .arith aop src =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok d =>
      match operand t s.mem pc addr src with
      | .error e => .error e
      | .ok (v, den) =>
        match precision cw with
        | none => .error (.undefinedResult pc)
        | some p =>
          let o := arithOp aop p rm d v den
          if trap o then .error (.fpuException pc)
          else fin s next (((t.set 0 o.res).raise o.flags).ccC1 (some o.c1))
  | .arithTo aop i pop =>
    match getST t pc i with
    | .error e => .error e
    | .ok d =>
      match getST t pc 0 with
      | .error e => .error e
      | .ok v =>
        match precision cw with
        | none => .error (.undefinedResult pc)
        | some p =>
          let o := arithOp aop p rm d v false
          if trap o then .error (.fpuException pc)
          else fin s next ((((t.set i o.res).raise o.flags).popIf pop).ccC1 (some o.c1))
  | .com unordered src pops =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a =>
      match operand t s.mem pc addr src with
      | .error e => .error e
      | .ok (b, den) =>
        let (rel, fl) := compare (!unordered) a b den
        if fl &&& unmasked cw != 0 then .error (.fpuException pc)
        else
          let t1 := (t.raise fl).setCC (relBits rel) (some false)
          fin s next (if pops = 0 then t1 else if pops = 1 then t1.pop else t1.pop.pop)
  | .comi unordered i pop =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a =>
      match getST t pc i with
      | .error e => .error e
      | .ok b =>
        let (rel, fl) := compare (!unordered) a b
        if fl &&& unmasked cw != 0 then .error (.fpuException pc)
        else
          let c := relBits rel
          let t1 := { t.raise fl with c1 := none }
          .ok { s with x87 := t1.popIf pop, rip := next,
                       flags := ⟨some (c % 2 = 1), some (c / 2 % 2 = 1), some false,
                         some (c / 4 % 2 = 1), some false, some false⟩ }
  | .tst =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a =>
      let (rel, fl) := compare true a (zero80 false)
      if fl &&& unmasked cw != 0 then .error (.fpuException pc)
      else fin s next ((t.raise fl).setCC (relBits rel) (some false))
  | .xam =>
    match t.get 0 with
    | none => fin s next (t.setCC 0b101 none)
    | some a => fin s next (t.setCC (xamCode a) (some (signOf80 a)))
  | .ld src =>
    let r : Except Fault XR :=
      match src with
      | .st i =>
        match getST t pc i with
        | .ok v => .ok (done v 0)
        | .error e => .error e
      | .mem k =>
        match memAddr pc addr with
        | .error e => .error e
        | .ok a =>
          match Janus.Amd64.load s.mem a k.size with
          | .error e => .error e
          | .ok v =>
            match k with
            | .f32 => .ok (fromFmt binary32 v)
            | .f64 => .ok (fromFmt binary64 v)
            | .f80 => .ok (done v 0)
            | k => .ok (done (ofInt k.intWidth v) 0)
    match r with
    | .error e => .error e
    | .ok o =>
      if trap o then .error (.fpuException pc) else
      match t.push o.res with
      | none => .error (.fpuStack pc)
      | some t1 => fin s next ((t1.raise o.flags).ccC1 (some false))
  | .ldConst v =>
    match t.push v with
    | none => .error (.fpuStack pc)
    | some t1 => fin s next (t1.ccC1 (some false))
  | .st dst pop =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a =>
      match dst with
      | .st i => fin s next (((t.set i a).popIf pop).ccC1 (some false))
      | .mem k =>
        match memAddr pc addr with
        | .error e => .error e
        | .ok ad =>
          let o : XR := match k with
            | .f32 => toFmt binary32 rm a
            | .f64 => toFmt binary64 rm a
            | _ => done a 0
          if trap o then .error (.fpuException pc) else
          match k with
          | .f32 | .f64 | .f80 =>
            match Janus.Amd64.store s.mem ad k.size o.res with
            | .error e => .error e
            | .ok m => .ok { s with mem := m, rip := next,
                                    x87 := ((t.raise o.flags).popIf pop).ccC1 (some o.c1) }
          | _ => .error (.undefinedResult pc)
  | .ist k trunc pop =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a =>
      match memAddr pc addr with
      | .error e => .error e
      | .ok ad =>
        let o := toInt k.intWidth (if trunc then .rz else rm) a
        if trap o then .error (.fpuException pc) else
        match Janus.Amd64.store s.mem ad k.size o.res with
        | .error e => .error e
        | .ok m => .ok { s with mem := m, rip := next,
                                x87 := ((t.raise o.flags).popIf pop).ccC1 (some o.c1) }
  | .xch i =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a =>
      match getST t pc i with
      | .error e => .error e
      | .ok b => fin s next (((t.set 0 b).set i a).ccC1 (some false))
  | .chs =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a =>
      fin s next ((t.set 0 (if signOf80 a then a - 2 ^ 79 else a + 2 ^ 79)).ccC1 (some false))
  | .abs =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a => fin s next ((t.set 0 (a % 2 ^ 79)).ccC1 (some false))
  | .sqrt =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a =>
      match precision cw with
      | none => .error (.undefinedResult pc)
      | some p =>
        let o := sqrt p rm a
        if trap o then .error (.fpuException pc)
        else fin s next (((t.set 0 o.res).raise o.flags).ccC1 (some o.c1))
  | .cmov cc i =>
    match getST t pc 0 with
    | .error e => .error e
    | .ok a =>
      match getST t pc i with
      | .error e => .error e
      | .ok b =>
        match cond cc with
        | none => .error (.undefinedFlag pc)
        | some c => fin s next ((t.set 0 (if c then b else a)).ccC1 none)
  | .ldcw =>
    match memAddr pc addr with
    | .error e => .error e
    | .ok ad =>
      match Janus.Amd64.load s.mem ad 2 with
      | .error e => .error e
      | .ok v =>
        let t1 := t.ccC1 none
        if t1.pending (normCW v) then .error (.fpuException pc)
        else .ok { s with x87 := t1, fpucw := BitVec.ofNat 16 (normCW v), rip := next }
  | .wait | .nop => fin s next (t.ccC1 none)
  -- the non-waiting instructions are handled by `exec`
  | _ => .error (.undefinedResult pc)

/-- Execute the x87 instruction `op` at `pc` (`next` = the address after it) with the linear
address `addr` of its memory operand; `cond cc` evaluates the `Jcc` condition `cc` on `RFLAGS`
(`none` if it reads an undefined flag). -/
def exec (s : State) (pc : Nat) (next : W64) (op : Op) (addr : Option Nat)
    (cond : Nat → Option Bool) : Except Fault State :=
  let t := s.x87
  match op with
  | .nstcw =>
    match memAddr pc addr with
    | .error e => .error e
    | .ok ad =>
      match Janus.Amd64.store s.mem ad 2 s.fpucw.toNat with
      | .error e => .error e
      | .ok m => .ok { s with mem := m, rip := next, x87 := t.ccC1 none }
  | .nstsw ax =>
    match t.statusWord with
    | none => .error (.undefinedFlag pc)
    | some w =>
      if ax then
        .ok { s with x87 := t.ccC1 none, rip := next,
                     regs := fun r => if r = 0 then (s.regs 0 &&& ~~~0xFFFF#64) ||| BitVec.ofNat 64 w
                       else s.regs r }
      else
        match memAddr pc addr with
        | .error e => .error e
        | .ok ad =>
          match Janus.Amd64.store s.mem ad 2 w with
          | .error e => .error e
          | .ok m => .ok { s with mem := m, rip := next, x87 := t.ccC1 none }
  | .nclex => fin s next (({ t with sw := 0 } : St).ccC1 none)
  | .ninit => .ok { s with x87 := { regs := t.regs }, fpucw := 0x37F, rip := next }
  | _ => if t.pending s.fpucw.toNat then .error (.fpuException pc) else execWaiting s pc next op addr cond

end Janus.Amd64.X87
