import Lean
import Janus.Amd64.GoABI
import Janus.Amd64.TacticAttr

/-!
# Symbolic execution for amd64 programs

The amd64 analogue of `Janus.Tactic` (arm64). Nothing in the logical layer is trusted: every
step is a lemma proved from the model, and the facts about the concrete program (no exit, no
stub, the bytes at `pc`, their decoding) are one Boolean `stepOK` closed by kernel evaluation.

* `Reaches p s Q`: from `s`, the run ends (with enough fuel) in an outcome satisfying `Q`.
  `GoABI.Returns`/`Panics`/`GrowsStack` reduce to it.
* `janus64_run [lemmas]` steps a goal `Reaches p s Q` (or `Returns`, `Panics`, `GrowsStack`)
  instruction by instruction until every branch reaches the exit address or a stub.
  Conditional branches split the goal (the condition becomes a hypothesis `hbr`); infeasible
  branches are closed by `omega`. `janus64_step` performs one step.
* `janus64_intro hs` turns `hs : GoABI.CallSetup p entry [a₀, …] s` into equations
  `h_rip : s.rip = …`, `h_ret : s.mem.readLE (s.regs 4).toNat 8 = exitAddr`,
  `h_x15 : s.xmm 15 = 0` and `h_a<i> : s.regs (argReg i) = aᵢ` (with the register number
  evaluated).

One step (`stepGoal`): compute the literal `rip` of the symbolic state; evaluate the program
data once (cached); look up the bytes at `rip` and decode them with `Janus.Amd64.decode` at
tactic run time; prove `stepOK p pc bytes i len = true` by `Eq.refl true` checked by the kernel;
simplify `exec i len s` with the `janus64_exec` set, the local equations about the initial state
and the user's lemmas, to `.ok s'` or an `if`.
-/

namespace Janus.Amd64.Tactic

open Janus Janus.Amd64 Janus.Amd64.GoABI

/-! ## `Reaches` -/

def Reaches (p : Program) (s : State) (Q : Outcome → Prop) : Prop :=
  ∃ n o, p.run n s = .ok o ∧ Q o

def ExecThen (p : Program) (r : Except Fault State) (Q : Outcome → Prop) : Prop :=
  match r with
  | .ok s' => Reaches p s' Q
  | .error _ => False

def IsReturn (post : State → Prop) : Outcome → Prop
  | .returned s => post s
  | .stub _ _ _ => False

def IsPanic : Outcome → Prop
  | .stub _ .panic _ => True
  | _ => False

def IsMorestack : Outcome → Prop
  | .stub _ .morestack _ => True
  | _ => False

@[simp, janus64_post] theorem isReturn_returned (post : State → Prop) (s : State) :
    IsReturn post (.returned s) = post s := rfl
@[simp, janus64_post] theorem isReturn_stub (post : State → Prop) (n : String) (k : StubKind)
    (s : State) : IsReturn post (.stub n k s) = False := rfl
@[simp, janus64_post] theorem isPanic_returned (s : State) : IsPanic (.returned s) = False := rfl
@[simp, janus64_post] theorem isPanic_panic (n : String) (s : State) :
    IsPanic (.stub n .panic s) = True := rfl
@[simp, janus64_post] theorem isPanic_morestack (n : String) (s : State) :
    IsPanic (.stub n .morestack s) = False := rfl
@[simp, janus64_post] theorem isMorestack_returned (s : State) :
    IsMorestack (.returned s) = False := rfl
@[simp, janus64_post] theorem isMorestack_panic (n : String) (s : State) :
    IsMorestack (.stub n .panic s) = False := rfl
@[simp, janus64_post] theorem isMorestack_morestack (n : String) (s : State) :
    IsMorestack (.stub n .morestack s) = True := rfl

/-- `pc` is an ordinary instruction: not the exit address, not a stub, inside the code with
bytes `bs`, which decode to `i` of length `len`. Closed by kernel evaluation. -/
def stepOK (p : Program) (pc : Nat) (bs : List Nat) (i : Instr) (len : Nat) : Bool :=
  decide (pc < 2 ^ 64) && !(pc == p.exitAddr) && (p.stubAt pc).isNone &&
    (p.fetch pc == some bs) && (decode bs == some (i, len))

def exitOK (p : Program) (pc : Nat) : Bool := decide (pc < 2 ^ 64) && pc == p.exitAddr

def stubOK (p : Program) (pc : Nat) (name : String) (kind : StubKind) : Bool :=
  decide (pc < 2 ^ 64) && !(pc == p.exitAddr) &&
    match p.stubAt pc with
    | some st => st.name == name && st.kind == kind
    | none => false

/-- The data the tactic reads off a program (re-checked by the kernel on every use). -/
def progData (p : Program) : Nat × List (Nat × List Nat) × List (Nat × String × Bool) :=
  (p.exitAddr, p.segments.map (fun seg => (seg.base, seg.bytes)),
    p.stubs.map (fun st => (st.addr, st.name, st.kind == .panic)))

private theorem rip_toNat_of {s : State} {c : Nat} (hpc : s.rip = BitVec.ofNat 64 c)
    (hc : c < 2 ^ 64) : s.rip.toNat = c := by
  rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

namespace Reaches

variable {p : Program} {s : State} {Q : Outcome → Prop}

theorem mono {Q' : Outcome → Prop} (h : Reaches p s Q) (hQ : ∀ o, Q o → Q' o) :
    Reaches p s Q' := by
  obtain ⟨n, o, h, hq⟩ := h; exact ⟨n, o, h, hQ o hq⟩

theorem step {c len : Nat} {bs : List Nat} {i : Instr} {r : Except Fault State}
    (hpc : s.rip = BitVec.ofNat 64 c) (hok : stepOK p c bs i len = true) (he : exec i len s = r)
    (h : ExecThen p r Q) : Reaches p s Q := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    Option.isNone_iff_eq_none, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hc, hx⟩, hs⟩, hf⟩, hd⟩ := hok
  have hpc' := rip_toNat_of hpc hc
  cases r with
  | error e => exact h.elim
  | ok s' =>
    obtain ⟨n, o, hr, hq⟩ := h
    refine ⟨n + 1, o, ?_, hq⟩
    rw [Program.run_succ_step (s' := s') (by rw [hpc']; exact hx) (by rw [hpc']; exact hs)
      (by rw [hpc']; exact hf) (by rw [step_of_decode hd]; exact he)]
    exact hr

theorem exit {c : Nat} (hpc : s.rip = BitVec.ofNat 64 c) (hok : exitOK p c = true)
    (hq : Q (.returned s)) : Reaches p s Q := by
  simp only [exitOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  exact ⟨1, _, Program.run_succ_exit (by rw [rip_toNat_of hpc hok.1]; exact hok.2), hq⟩

theorem stub {c : Nat} {name : String} {kind : StubKind} (hpc : s.rip = BitVec.ofNat 64 c)
    (hok : stubOK p c name kind = true) (hq : Q (.stub name kind s)) : Reaches p s Q := by
  unfold stubOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hok
  obtain ⟨⟨hc, hx⟩, hst⟩ := hok
  have hpc' := rip_toNat_of hpc hc
  cases hfind : p.stubAt c with
  | none => rw [hfind] at hst; cases hst
  | some st =>
    rw [hfind] at hst
    simp only [Bool.and_eq_true, beq_iff_eq] at hst
    obtain ⟨h1, h2⟩ := hst
    refine ⟨1, _, Program.run_succ_stub (by rw [hpc']; exact hx) (by rw [hpc']; exact hfind), ?_⟩
    rw [h1, h2]; exact hq

theorem of_steps {k : Nat} {s' : State} (hs : Program.Steps p s k s') (h : Reaches p s' Q) :
    Reaches p s Q := by
  obtain ⟨n, o, hr, hq⟩ := h
  exact ⟨k + n, o, by rw [Program.run_steps hs, hr], hq⟩

theorem ite_state {c : Prop} [Decidable c] {s₁ s₂ : State} (h₁ : c → Reaches p s₁ Q)
    (h₂ : ¬c → Reaches p s₂ Q) : Reaches p (if c then s₁ else s₂) Q := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc]; exact h₂ hc

end Reaches

/-! ### Calls with a symbolic return address (`p.withExit ret`, `RetAddr p ret`)

The program facts are still evaluated by the kernel on the closed `p`; `rip ≠ ret` follows from
`RetAddr` (no code and no stub at `ret`). The rewrite rules below are installed by the executor
for every `RetAddr` hypothesis, so that `RET` to `ret` evaluates without arithmetic hypotheses. -/

theorem _root_.Janus.Amd64.GoABI.RetAddr.toNat_ofNat {p : Program} {ret : Nat} (hret : GoABI.RetAddr p ret) :
    (BitVec.ofNat 64 ret).toNat = ret := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hret.lt64]
theorem _root_.Janus.Amd64.GoABI.RetAddr.mod64 {p : Program} {ret : Nat} (hret : GoABI.RetAddr p ret) :
    ret % 18446744073709551616 = ret := Nat.mod_eq_of_lt hret.lt64
theorem _root_.Janus.Amd64.GoABI.RetAddr.user_eq {p : Program} {ret : Nat} (hret : GoABI.RetAddr p ret) :
    (ret < 140737488355328) = True := eq_true hret.user

namespace Reaches

variable {p : Program} {ret : Nat} {s : State} {Q : Outcome → Prop}

theorem step_withExit {c len : Nat} {bs : List Nat} {i : Instr} {r : Except Fault State}
    (hret : GoABI.RetAddr p ret) (hpc : s.rip = BitVec.ofNat 64 c)
    (hok : stepOK p c bs i len = true) (he : exec i len s = r)
    (h : ExecThen (p.withExit ret) r Q) : Reaches (p.withExit ret) s Q := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    Option.isNone_iff_eq_none, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hc, _⟩, hs⟩, hf⟩, hd⟩ := hok
  have hpc' := rip_toNat_of hpc hc
  cases r with
  | error e => exact h.elim
  | ok s' =>
    obtain ⟨n, o, hr, hq⟩ := h
    refine ⟨n + 1, o, ?_, hq⟩
    rw [Program.run_succ_step (p := p.withExit ret) (s' := s')
      (by rw [hpc']; exact hret.ne_of_fetch hf) (by rw [hpc']; exact hs) (by rw [hpc']; exact hf)
      (by rw [step_of_decode hd]; exact he)]
    exact hr

theorem exit_withExit (hret : GoABI.RetAddr p ret) (hpc : s.rip = BitVec.ofNat 64 ret)
    (hq : Q (.returned s)) : Reaches (p.withExit ret) s Q :=
  ⟨1, _, Program.run_succ_exit (by rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hret.lt64]; rfl),
    hq⟩

theorem stub_withExit {c : Nat} {name : String} {kind : StubKind} (hret : GoABI.RetAddr p ret)
    (hpc : s.rip = BitVec.ofNat 64 c) (hok : stubOK p c name kind = true)
    (hq : Q (.stub name kind s)) : Reaches (p.withExit ret) s Q := by
  unfold stubOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hok
  obtain ⟨⟨hc, _⟩, hst⟩ := hok
  have hpc' := rip_toNat_of hpc hc
  cases hfind : p.stubAt c with
  | none => rw [hfind] at hst; cases hst
  | some st =>
    rw [hfind] at hst
    simp only [Bool.and_eq_true, beq_iff_eq] at hst
    obtain ⟨h1, h2⟩ := hst
    refine ⟨1, _, Program.run_succ_stub (p := p.withExit ret)
      (by rw [hpc']; exact hret.ne_of_stubAt hfind) (by rw [hpc']; exact hfind), ?_⟩
    rw [h1, h2]; exact hq

end Reaches

namespace ExecThen

variable {p : Program} {Q : Outcome → Prop}

theorem ok {s : State} (h : Reaches p s Q) : ExecThen p (.ok s) Q := h

theorem ite {c : Prop} [Decidable c] {r₁ r₂ : Except Fault State} (h₁ : c → ExecThen p r₁ Q)
    (h₂ : ¬c → ExecThen p r₂ Q) : ExecThen p (if c then r₁ else r₂) Q := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc]; exact h₂ hc

end ExecThen

theorem returns_of_reaches {p : Program} {s : State} {post : State → Prop}
    (h : Reaches p s (IsReturn post)) : Returns p s post := by
  obtain ⟨n, o, hr, hq⟩ := h
  cases o with
  | returned s' => exact ⟨n, s', hr, hq⟩
  | stub _ _ _ => exact hq.elim

theorem panics_of_reaches {p : Program} {s : State} (h : Reaches p s IsPanic) : Panics p s := by
  obtain ⟨n, o, hr, hq⟩ := h
  cases o with
  | returned s' => exact hq.elim
  | stub name kind s' =>
    cases kind with
    | panic => exact ⟨n, name, s', hr⟩
    | morestack => exact hq.elim

theorem growsStack_of_reaches {p : Program} {s : State} (h : Reaches p s IsMorestack) :
    GrowsStack p s := by
  obtain ⟨n, o, hr, hq⟩ := h
  cases o with
  | returned s' => exact hq.elim
  | stub name kind s' =>
    cases kind with
    | panic => exact hq.elim
    | morestack => exact ⟨n, name, s', hr⟩

/-! ## The `janus64_exec` simp set

### Instruction families and operands -/

attribute [janus64_exec] exec execAlu execUnary execMul1 execImul execDiv execShift execShd
  execBit execCount readLoc readLocRW readSrc writeLoc readX writeX ea push64 branchTo
  BitVec.and_self BitVec.or_self BitVec.xor_self State.getReg State.getHigh State.putReg State.putHigh State.setFlags State.setRip logicFlags

/-! ### Register-file normal form

The registers of a symbolic state are a chain `setRegF (setRegF s.regs 0 v₀) 3 v₃` with
increasing register numbers, each written once (as in the arm64 tactic). -/

def setRegF (f : Nat → W64) (r : Nat) (v : W64) : Nat → W64 := fun i => if i = r then v else f i
def setXmmF (f : Nat → W128) (r : Nat) (v : W128) : Nat → W128 := fun i => if i = r then v else f i

@[janus64_exec] theorem State.setReg_eq (s : State) (r : Nat) (v : W64) :
    s.setReg r v = { s with regs := setRegF s.regs r v } := rfl
@[janus64_exec] theorem State.setXmm_eq (s : State) (r : Nat) (v : W128) :
    s.setXmm r v = { s with xmm := setXmmF s.xmm r v } := rfl

@[janus64_exec, janus64_post] theorem setRegF_apply (f : Nat → W64) (r : Nat) (v : W64) (i : Nat) :
    setRegF f r v i = if i = r then v else f i := rfl
@[janus64_exec, janus64_post] theorem setXmmF_apply (f : Nat → W128) (r : Nat) (v : W128) (i : Nat) :
    setXmmF f r v i = if i = r then v else f i := rfl

@[janus64_exec, janus64_post] theorem setRegF_same (f : Nat → W64) (r : Nat) (v w : W64) :
    setRegF (setRegF f r v) r w = setRegF f r w := by
  funext i; simp only [setRegF]; split <;> rfl

@[janus64_exec, janus64_post] theorem setRegF_comm (f : Nat → W64) {r r' : Nat} (v w : W64)
    (h : r' < r) : setRegF (setRegF f r v) r' w = setRegF (setRegF f r' w) (r + 0) v := by
  funext i; simp only [setRegF, Nat.add_zero]
  by_cases h1 : i = r' <;> by_cases h2 : i = r <;> simp [h1, h2] <;> omega

@[janus64_exec, janus64_post] theorem setXmmF_same (f : Nat → W128) (r : Nat) (v w : W128) :
    setXmmF (setXmmF f r v) r w = setXmmF f r w := by
  funext i; simp only [setXmmF]; split <;> rfl

@[janus64_exec, janus64_post] theorem setXmmF_comm (f : Nat → W128) {r r' : Nat} (v w : W128)
    (h : r' < r) : setXmmF (setXmmF f r v) r' w = setXmmF (setXmmF f r' w) (r + 0) v := by
  funext i; simp only [setXmmF, Nat.add_zero]
  by_cases h1 : i = r' <;> by_cases h2 : i = r <;> simp [h1, h2] <;> omega

/-! ### Flags of `ADD`/`SUB` (kept folded; fields by `rfl`) -/

section FlagFields
variable {w : Nat} (x y : BitVec w) (c : Bool)

@[janus64_exec, janus64_post] theorem addFlags_cf :
    (addFlags x y c).2.cf = some (decide (x.toNat + y.toNat + c.toNat ≥ 2 ^ w)) := rfl
@[janus64_exec, janus64_post] theorem addFlags_zf :
    (addFlags x y c).2.zf = some (decide ((addFlags x y c).1 = 0)) := rfl
@[janus64_exec, janus64_post] theorem addFlags_sf :
    (addFlags x y c).2.sf = some (addFlags x y c).1.msb := rfl
@[janus64_exec, janus64_post] theorem addFlags_ovf :
    (addFlags x y c).2.ovf =
      some (decide ((addFlags x y c).1.toInt ≠ x.toInt + y.toInt + (c.toNat : Int))) := rfl
@[janus64_exec, janus64_post] theorem addFlags_pf :
    (addFlags x y c).2.pf = some (parity (addFlags x y c).1.toNat) := rfl
@[janus64_exec, janus64_post] theorem addFlags_af :
    (addFlags x y c).2.af = some (auxCarry x y (addFlags x y c).1) := rfl
@[janus64_exec, janus64_post] theorem subFlags_cf :
    (subFlags x y c).2.cf = some (decide (x.toNat < y.toNat + c.toNat)) := rfl
@[janus64_exec, janus64_post] theorem subFlags_zf :
    (subFlags x y c).2.zf = some (decide ((subFlags x y c).1 = 0)) := rfl
@[janus64_exec, janus64_post] theorem subFlags_sf :
    (subFlags x y c).2.sf = some (subFlags x y c).1.msb := rfl
@[janus64_exec, janus64_post] theorem subFlags_ovf :
    (subFlags x y c).2.ovf =
      some (decide ((subFlags x y c).1.toInt ≠ x.toInt - y.toInt - (c.toNat : Int))) := rfl
@[janus64_exec, janus64_post] theorem subFlags_pf :
    (subFlags x y c).2.pf = some (parity (subFlags x y c).1.toNat) := rfl
@[janus64_exec, janus64_post] theorem subFlags_af :
    (subFlags x y c).2.af = some (auxCarry x y (subFlags x y c).1) := rfl

end FlagFields

attribute [janus64_exec, janus64_post] addFlags_false_fst subFlags_false_fst

@[janus64_exec, janus64_post] theorem addFlags_true_fst {w : Nat} (x y : BitVec w) :
    (addFlags x y true).1 = x + y + 1 := by
  rw [addFlags_fst]; rfl

/-- `ADC` with a symbolic carry: `x + y + c` as a `Nat` sum modulo `2^w`. -/
@[janus64_exec, janus64_post] theorem addFlags_fst_decide {w : Nat} (x y : BitVec w) (P : Prop)
    [Decidable P] : (addFlags x y (decide P)).1 = BitVec.ofNat w (x.toNat + y.toNat + (decide P).toNat) := rfl

/-! ### Conditions, one equation per condition code -/

section Conditions
variable (f : Flags)
@[janus64_exec, janus64_post] theorem condition_0 : condition 0 f = f.ovf := rfl
@[janus64_exec, janus64_post] theorem condition_1 : condition 1 f = f.ovf.map (!·) := rfl
@[janus64_exec, janus64_post] theorem condition_2 : condition 2 f = f.cf := rfl
@[janus64_exec, janus64_post] theorem condition_3 : condition 3 f = f.cf.map (!·) := rfl
@[janus64_exec, janus64_post] theorem condition_4 : condition 4 f = f.zf := rfl
@[janus64_exec, janus64_post] theorem condition_5 : condition 5 f = f.zf.map (!·) := rfl
@[janus64_exec, janus64_post] theorem condition_6 :
    condition 6 f = (match f.cf, f.zf with | some c, some z => some (c || z) | _, _ => none) := rfl
@[janus64_exec, janus64_post] theorem condition_7 :
    condition 7 f = (match f.cf, f.zf with | some c, some z => some (c || z) | _, _ => none).map (!·) := rfl
@[janus64_exec, janus64_post] theorem condition_8 : condition 8 f = f.sf := rfl
@[janus64_exec, janus64_post] theorem condition_9 : condition 9 f = f.sf.map (!·) := rfl
@[janus64_exec, janus64_post] theorem condition_10 : condition 10 f = f.pf := rfl
@[janus64_exec, janus64_post] theorem condition_11 : condition 11 f = f.pf.map (!·) := rfl
@[janus64_exec, janus64_post] theorem condition_12 :
    condition 12 f = (match f.sf, f.ovf with | some a, some b => some (a != b) | _, _ => none) := rfl
@[janus64_exec, janus64_post] theorem condition_13 :
    condition 13 f = (match f.sf, f.ovf with | some a, some b => some (a != b) | _, _ => none).map (!·) := rfl
@[janus64_exec, janus64_post] theorem condition_14 :
    condition 14 f = (match f.zf, f.sf, f.ovf with
      | some z, some a, some b => some (z || (a != b)) | _, _, _ => none) := rfl
@[janus64_exec, janus64_post] theorem condition_15 :
    condition 15 f = (match f.zf, f.sf, f.ovf with
      | some z, some a, some b => some (z || (a != b)) | _, _, _ => none).map (!·) := rfl
end Conditions

/-! ### Signed comparisons after `CMP x, y` (64-bit)

`JL/JGE/JLE/JG` (and `SETcc`/`CMOVcc`) read `SF != OF` of `x - y`, which is
`x.toInt < y.toInt`. These equations are applied before the generic condition equations. -/

theorem toInt64_cond (x : BitVec 64) :
    x.toInt = if x.toNat < 9223372036854775808 then (x.toNat : Int)
      else (x.toNat : Int) - 18446744073709551616 := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : x.toNat < 9223372036854775808
  · simp [h]; omega
  · simp [h]; omega

theorem sub_lt_signed (x y : BitVec 64) :
    ((x - y).msb != decide ((x - y).toInt ≠ x.toInt - y.toInt)) = decide (x.toInt < y.toInt) := by
  rw [BitVec.msb_eq_toInt, BitVec.toInt_sub, Int.bmod_def]
  have h1 := @BitVec.toInt_lt 64 x; have h2 := @BitVec.le_toInt 64 x
  have h3 := @BitVec.toInt_lt 64 y; have h4 := @BitVec.le_toInt 64 y
  simp only [Nat.reduceSub, Nat.reducePow, Int.reducePow, Int.reduceNeg] at *
  generalize x.toInt = a at *
  generalize y.toInt = b at *
  have hc : ((18446744073709551616 : Nat) : Int) = 18446744073709551616 := rfl
  simp only [hc] at *
  generalize hr : (a - b) % 18446744073709551616 = r at *
  have hr0 : 0 ≤ r := by rw [← hr]; omega
  have hr1 : r < 18446744073709551616 := by rw [← hr]; omega
  have hq : ∃ q, a - b = r + 18446744073709551616 * q := ⟨(a - b) / 18446744073709551616, by rw [← hr]; omega⟩
  obtain ⟨q, hq⟩ := hq
  split <;> rename_i hc <;>
  (by_cases p1 : r < 0 <;> by_cases p1' : r - 18446744073709551616 < 0 <;>
   by_cases p2 : r = a - b <;> by_cases p2' : r - 18446744073709551616 = a - b <;>
   by_cases p3 : a < b <;> simp [p1, p1', p2, p2', p3] <;> omega)

@[janus64_exec high, janus64_post high] theorem cond_sub_l (x y : BitVec 64) :
    condition 12 (subFlags x y false).2 = some (decide (x.toInt < y.toInt)) := by
  simp only [condition_12, subFlags_sf, subFlags_ovf, subFlags_false_fst, Bool.toNat_false,
    Int.natCast_zero, Int.sub_zero, sub_lt_signed]
@[janus64_exec high, janus64_post high] theorem cond_sub_ge (x y : BitVec 64) :
    condition 13 (subFlags x y false).2 = some (decide (y.toInt ≤ x.toInt)) := by
  simp only [condition_13, subFlags_sf, subFlags_ovf, subFlags_false_fst, Bool.toNat_false,
    Int.natCast_zero, Int.sub_zero, sub_lt_signed, Option.map_some]
  by_cases h : x.toInt < y.toInt <;> simp [h] <;> omega

theorem sub_eq_zero_iff' (x y : BitVec 64) : (x - y = 0) ↔ x.toInt = y.toInt := by
  rw [BitVec.toInt_inj, ← BitVec.toNat_inj, ← BitVec.toNat_inj, BitVec.toNat_sub]
  have := x.isLt; have := y.isLt
  rw [show (0 : BitVec 64).toNat = 0 from rfl]
  omega

@[janus64_exec high, janus64_post high] theorem cond_sub_le (x y : BitVec 64) :
    condition 14 (subFlags x y false).2 = some (decide (x.toInt ≤ y.toInt)) := by
  simp only [condition_14, subFlags_zf, subFlags_sf, subFlags_ovf, subFlags_false_fst,
    Bool.toNat_false, Int.natCast_zero, Int.sub_zero, sub_lt_signed]
  congr 1
  by_cases h : x.toInt = y.toInt
  · rw [decide_eq_true ((sub_eq_zero_iff' x y).mpr h)]; simp; omega
  · rw [decide_eq_false (fun h' => h ((sub_eq_zero_iff' x y).mp h'))]
    by_cases h' : x.toInt < y.toInt
    · rw [decide_eq_true h']; simp; omega
    · rw [decide_eq_false h']; simp; omega
@[janus64_exec high, janus64_post high] theorem cond_sub_g (x y : BitVec 64) :
    condition 15 (subFlags x y false).2 = some (decide (y.toInt < x.toInt)) := by
  simp only [condition_15, subFlags_zf, subFlags_sf, subFlags_ovf, subFlags_false_fst,
    Bool.toNat_false, Int.natCast_zero, Int.sub_zero, sub_lt_signed, Option.map_some]
  congr 1
  by_cases h : x.toInt = y.toInt
  · rw [decide_eq_true ((sub_eq_zero_iff' x y).mpr h)]; simp; omega
  · rw [decide_eq_false (fun h' => h ((sub_eq_zero_iff' x y).mp h'))]
    by_cases h' : x.toInt < y.toInt
    · rw [decide_eq_true h']; simp; omega
    · rw [decide_eq_false h']; simp; omega

/-- Small non-negative values: `toInt = toNat` (side condition by `omega`). -/
@[janus64_exec, janus64_post] theorem toInt64_of_lt (x : BitVec 64) (h : x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) := by
  rw [toInt64_cond, ite_eq_left h]

@[janus64_exec, janus64_post] theorem toInt64_ofNat_of_lt (k : Nat) (h : k < 9223372036854775808) :
    (BitVec.ofNat 64 k).toInt = (k : Int) := by
  rw [toInt64_of_lt _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

@[janus64_exec, janus64_post] theorem bv_ofNat_add_one (k : Nat) :
    BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
  rw [← BitVec.ofNat_add]

attribute [janus64_exec, janus64_post] Option.map_some Option.map_none

/-! ### Memory -/

@[janus64_exec] theorem load_ok (m : Memory) {a n : Nat} (h : m.accessible a n false = true) :
    load m a n = .ok (m.readLE a n) := by simp [load, h]

@[janus64_exec] theorem loadRW_ok (m : Memory) {a n : Nat} (h : m.accessible a n true = true) :
    loadRW m a n = .ok (m.readLE a n) := by
  simp [loadRW, h, Janus.Arm64.Memory.accessible_read_of_write m h]

@[janus64_exec] theorem store_ok (m : Memory) {a n : Nat} (v : Nat) (h : m.accessible a n true = true) :
    store m a n v = .ok (m.writeLE a n v) := by
  simp [store, h, Janus.Arm64.Memory.accessible_read_of_write m h]

attribute [janus64_exec, janus64_post] Janus.Arm64.Memory.accessible_writeLE
  Janus.Arm64.Memory.regions_writeLE

@[janus64_exec, janus64_post] theorem readLE_writeLE_disjoint (m : Memory) {a n b k : Nat} (v : Nat)
    (h : b + k ≤ a ∨ a + n ≤ b) : (m.writeLE a n v).readLE b k = m.readLE b k :=
  Janus.Arm64.Memory.readLE_writeLE_of_disjoint m v h

@[janus64_exec, janus64_post] theorem readLE_writeLE_same (m : Memory) {a b : Nat} (n v : Nat)
    (h : a = b) : (m.writeLE a n v).readLE b n = v % 256 ^ n := by
  subst h; exact Janus.Arm64.Memory.readLE_writeLE_self m a n v

/-- A read entirely inside an earlier write (e.g. one word of a 16-byte `MOVUPS` store). -/
@[janus64_exec, janus64_post] theorem readLE_writeLE_inside (m : Memory) {a n b k : Nat} (v : Nat)
    (h1 : a ≤ b) (h2 : b + k ≤ a + n) (h3 : k < n) :
    (m.writeLE a n v).readLE b k = v / 256 ^ (b - a) % 256 ^ k :=
  Janus.Arm64.Memory.readLE_writeLE_inside m v h1 h2

@[janus64_exec, janus64_post] theorem readLE_mod_8 (m : Memory) (a : Nat) :
    m.readLE a 8 % 18446744073709551616 = m.readLE a 8 :=
  Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt m a 8)

@[janus64_exec, janus64_post] theorem readLE_mod_16 (m : Memory) (a : Nat) :
    m.readLE a 16 % 340282366920938463463374607431768211456 = m.readLE a 16 :=
  Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt m a 16)

@[janus64_exec, janus64_post] theorem readLE_mod_1 (m : Memory) (a : Nat) :
    m.readLE a 1 % 256 = m.readLE a 1 :=
  Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt m a 1)

@[janus64_exec, janus64_post] theorem writeLE_mod_16 (m : Memory) (a v : Nat) :
    m.writeLE a 16 (v % 340282366920938463463374607431768211456) = m.writeLE a 16 v :=
  Janus.Arm64.Memory.writeLE_mod m a 16 v

@[janus64_exec, janus64_post] theorem writeLE_mod_8 (m : Memory) (a v : Nat) :
    m.writeLE a 8 (v % 18446744073709551616) = m.writeLE a 8 v :=
  Janus.Arm64.Memory.writeLE_mod m a 8 v

@[janus64_exec, janus64_post] theorem toNat_ofNat_readLE_8 (m : Memory) (a : Nat) :
    (BitVec.ofNat 64 (m.readLE a 8)).toNat = m.readLE a 8 := by
  rw [BitVec.toNat_ofNat]; exact readLE_mod_8 m a

/-! ### Arithmetic normalisation -/

attribute [janus64_exec, janus64_post] BitVec.toNat_add BitVec.toNat_sub BitVec.toNat_ofNat
  BitVec.setWidth_eq BitVec.shiftLeft_zero BitVec.ushiftRight_zero Nat.shiftLeft_eq
  BitVec.toNat_shiftLeft BitVec.add_zero BitVec.zero_add BitVec.sub_zero

@[janus64_exec, janus64_post] theorem mod64_of_lt {a : Nat} (h : a < 18446744073709551616) :
    a % 18446744073709551616 = a := Nat.mod_eq_of_lt h

/-- `x + (2^64 - k)` wraps to `x - k`. -/
@[janus64_exec, janus64_post] theorem mod64_add_wrap {n c : Nat}
    (hc : Nat.blt c 18446744073709551616 = true)
    (h : 18446744073709551616 - c ≤ n) (hn : n < 18446744073709551616) :
    (n + c) % 18446744073709551616 = n - (18446744073709551616 - c) := by
  have := Nat.blt_eq.mp hc
  rw [show n + c = (n - (18446744073709551616 - c)) + 18446744073709551616 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The literal on the left (`(2^64 - k) + x`, as `BitVec.toNat_add` produces for `x - k`). -/
@[janus64_exec, janus64_post] theorem mod64_add_wrap' {n c : Nat}
    (hc : Nat.blt c 18446744073709551616 = true)
    (h : 18446744073709551616 - c ≤ n) (hn : n < 18446744073709551616) :
    (c + n) % 18446744073709551616 = n - (18446744073709551616 - c) := by
  rw [Nat.add_comm]; exact mod64_add_wrap hc h hn

/-! ### Masked indices (`ANDL $(2^k-1), AX` then an indexed access) -/

attribute [janus64_exec, janus64_post] BitVec.toNat_setWidth BitVec.toNat_and

/-- `n AND (2^k - 1) = n mod 2^k`, for a literal mask (the side condition is decided). -/
@[janus64_exec, janus64_post] theorem land_mask_eq_mod (n m : Nat) (h : ((m + 1) &&& m) = 0) :
    n &&& m = n % (m + 1) := by
  have hm : m + 1 ≠ 0 := by omega
  have hp : ∃ k, m + 1 = 2 ^ k := by
    refine ⟨Nat.log2 (m + 1), ?_⟩
    exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).mp (by simpa using h) |>.elim
      (fun k hk => by rw [hk, Nat.log2_two_pow])
  obtain ⟨k, hk⟩ := hp
  rw [show m = 2 ^ k - 1 by omega, Nat.and_two_pow_sub_one_eq_mod, Nat.sub_add_cancel Nat.one_le_two_pow]

@[janus64_exec, janus64_post] theorem mod_mod_of_dvd' (a b c : Nat) (h : b % c = 0) :
    a % b % c = a % c := Nat.mod_mod_of_dvd a (Nat.dvd_of_mod_eq_zero h)

/-- `DIV` of a 64-bit dividend never overflows the 64-bit quotient. -/
@[janus64_exec, janus64_post] theorem div_toNat_ge_false (x : BitVec 64) (b : Nat) :
    (18446744073709551616 ≤ x.toNat / b) = False :=
  eq_false (Nat.not_le.mpr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt))

@[janus64_exec, janus64_post] theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by simp)

@[janus64_exec, janus64_post] theorem bv64_eq_zero_prop (x : BitVec 64) :
    (x = 0#64) = (x.toNat = 0) := by
  apply propext; constructor
  · intro h; simp [h]
  · intro h; exact BitVec.eq_of_toNat_eq (by simpa using h)

@[janus64_exec, janus64_post] theorem bv64_eq_zero_prop' (x : BitVec 64) : (x = 0) = (x.toNat = 0) :=
  bv64_eq_zero_prop x

@[janus64_exec, janus64_post] theorem bv_add_add (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- `x + (2^64 - k)` as `x - k` for the stack pointer arithmetic of `SUB RSP, k` / `PUSH`. -/
@[janus64_exec, janus64_post] theorem bv_sub_add_le (x : BitVec 64) {a b : Nat} (hc : Nat.ble b a = true) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a - b) := by
  have h := Nat.ble_eq.mp hc
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

@[janus64_exec, janus64_post] theorem bv_sub_add_gt (x : BitVec 64) {a b : Nat} (hc : Nat.blt a b = true) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (b - a) := by
  have h := Nat.blt_eq.mp hc
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

@[janus64_exec, janus64_post] theorem bv_sub_sub (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

@[janus64_exec, janus64_post] theorem bv_add_ofNat_zero (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := by
  simp

@[janus64_exec, janus64_post] theorem bv_sub_add_cancel (x : BitVec 64) (a : Nat) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 a = x := BitVec.sub_add_cancel x _

/-! ### Basic logic -/

attribute [janus64_exec, janus64_post] ge_iff_le gt_iff_lt ite_true ite_false ite_self
  Bool.true_and Bool.and_true Bool.false_and Bool.and_false Bool.not_true Bool.not_false
  Bool.true_or Bool.or_true Bool.false_or Bool.or_false Bool.not_not decide_eq_true_eq
  decide_eq_false_iff_not decide_true decide_false decide_not Bool.true_eq_false
  Bool.false_eq_true ne_eq not_false_eq_true not_true_eq_false eq_self_iff_true and_true true_and
  and_false false_and or_true true_or or_false false_or Bool.bne_true Bool.bne_false
  Bool.not_eq_true Bool.not_eq_false beq_self_eq_true bne_self_eq_false Bool.toNat_true
  Bool.toNat_false Nat.add_zero Nat.zero_add Nat.mul_one Nat.one_mul Nat.mul_zero Nat.zero_mul
  Nat.zero_mod Nat.mod_self ite_not dite_eq_ite if_true_left if_false_left if_true_right
  if_false_right Bool.not_eq_eq_eq_not Bool.or_eq_true Bool.and_eq_true

theorem abiReturn_iff (s₀ s₁ : State) :
    ABIReturn s₀ s₁ ↔ s₁.regs 4 = s₀.regs 4 + 8 ∧ s₁.regs 5 = s₀.regs 5 ∧
      s₁.regs 14 = s₀.regs 14 ∧ s₁.xmm 15 = s₀.xmm 15 :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

attribute [janus64_post] abiReturn_iff results argReg intArgRegs List.take List.map

/-! ### Carry materialisation

`SBBQ R, R` yields `-CF`; `NEGQ`/`NEGL` turn it back into `CF` (Go's `bits.Add64` carry loops).
These keep such carries as `if P then 1 else 0` on the flag condition `P` and fold them back to
`decide P`. -/

@[janus64_exec, janus64_post] theorem subFlags_self_fst64 (x : BitVec 64) (c : Bool) :
    (subFlags x x c).1 = if c then BitVec.allOnes 64 else 0 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  cases c <;> simp [subFlags] <;> omega

@[janus64_exec, janus64_post] theorem zero_sub_ite64 (c : Bool) :
    (0#64 - if c then BitVec.allOnes 64 else 0) = if c then 1 else 0 := by cases c <;> decide

@[janus64_exec, janus64_post] theorem zero_sub_ite_one64 (c : Bool) :
    (0#64 - if c then (1 : BitVec 64) else 0) = if c then BitVec.allOnes 64 else 0 := by
  cases c <;> decide

@[janus64_exec, janus64_post] theorem setWidth32_ite (c : Bool) (a b : BitVec 64) :
    BitVec.setWidth 32 (if c then a else b) = if c then a.setWidth 32 else b.setWidth 32 := by
  cases c <;> rfl

@[janus64_exec, janus64_post] theorem setWidth64_ite32 (c : Bool) (a b : BitVec 32) :
    BitVec.setWidth 64 (if c then a else b) = if c then a.setWidth 64 else b.setWidth 64 := by
  cases c <;> rfl

@[janus64_exec, janus64_post] theorem zero32_sub_ite (c : Bool) (a b : BitVec 32) :
    (0#32 - if c then a else b) = if c then 0#32 - a else 0#32 - b := by cases c <;> rfl

@[janus64_exec, janus64_post] theorem toNat_ite {w : Nat} (c : Bool) (a b : BitVec w) :
    (if c then a else b).toNat = if c then a.toNat else b.toNat := by cases c <;> rfl

@[janus64_exec, janus64_post] theorem decide_ite_eq {w : Nat} (c : Bool) (a b d : BitVec w) :
    decide ((if c then a else b) = d) = if c then decide (a = d) else decide (b = d) := by
  cases c <;> rfl

@[janus64_exec, janus64_post] theorem decide_lt_ite (c : Bool) (n a b : Nat) :
    decide (n < if c then a else b) = if c then decide (n < a) else decide (n < b) := by
  cases c <;> rfl

@[janus64_exec, janus64_post] theorem ite_bool_true_false (c : Bool) : (if c then true else false) = c := by cases c <;> rfl
@[janus64_exec, janus64_post] theorem ite_bool_false_true (c : Bool) : (if c then false else true) = !c := by cases c <;> rfl
@[janus64_exec, janus64_post] theorem ite_toNat_one_zero (c : Bool) : (if c then 1 else 0) = c.toNat := by cases c <;> rfl

@[janus64_exec, janus64_post] theorem zero_sub_iteP (P : Prop) [Decidable P] :
    (0#64 - if P then 18446744073709551615#64 else 0#64) = if P then 1#64 else 0#64 := by
  by_cases h : P <;> simp [h]
@[janus64_exec, janus64_post] theorem setWidth32_iteP (P : Prop) [Decidable P] (a b : BitVec 64) :
    BitVec.setWidth 32 (if P then a else b) = if P then a.setWidth 32 else b.setWidth 32 := by
  by_cases h : P <;> simp [h]
@[janus64_exec, janus64_post] theorem decide_iteP_eq {w : Nat} (P : Prop) [Decidable P] (a b d : BitVec w) :
    decide ((if P then a else b) = d) = if P then decide (a = d) else decide (b = d) := by
  by_cases h : P <;> simp [h]
@[janus64_exec, janus64_post] theorem ite_false_true_P (P : Prop) [Decidable P] : (if P then false else true) = !decide P := by
  by_cases h : P <;> simp [h]

/-! ### Carry chains as `Nat` arithmetic (`janus64_post`) -/

@[janus64_post] theorem addFlags_fst_toNat (x y : BitVec 64) (c : Bool) :
    (addFlags x y c).1.toNat = (x.toNat + y.toNat + c.toNat) % 18446744073709551616 := by
  simp [addFlags]

@[janus64_post] theorem decide_carry_toNat (a : Nat) (h : a < 2 * 18446744073709551616) :
    (decide (a ≥ 18446744073709551616)).toNat = a / 18446744073709551616 := by
  by_cases h' : a ≥ 18446744073709551616
  · simp [h']; omega
  · simp [h']; omega

/-! ## The stepping engine -/

open Lean Meta Elab Tactic

deriving instance ToExpr for Addr
deriving instance ToExpr for Loc
deriving instance ToExpr for Src
deriving instance ToExpr for XLoc
deriving instance ToExpr for AluOp
deriving instance ToExpr for UnOp
deriving instance ToExpr for ShOp
deriving instance ToExpr for BitOp
deriving instance ToExpr for CntOp
deriving instance ToExpr for FlagOp
deriving instance ToExpr for SseOp
deriving instance ToExpr for Instr
deriving instance ToExpr for StubKind

syntax "janus64_disch" : tactic

abbrev ProgData := Nat × List (Nat × List Nat) × List (Nat × String × Bool)

unsafe def evalProgDataImpl (p : Expr) : MetaM ProgData := do
  let e := mkApp (mkConst ``progData) p
  let ty ← inferType e
  evalExpr ProgData ty e

@[implemented_by evalProgDataImpl]
opaque evalProgDataCore (p : Expr) : MetaM ProgData

unsafe def evalNatImpl (e : Expr) : MetaM Nat := evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatImpl]
opaque evalNatCore (e : Expr) : MetaM Nat

initialize progCache : IO.Ref (Std.HashMap Expr ProgData) ← IO.mkRef {}

def getProgData (p : Expr) : MetaM ProgData := do
  let p ← instantiateMVars p
  if let some d := (← progCache.get).get? p then return d
  if p.hasFVar || p.hasMVar then
    throwError "janus64: the program must be a closed term (e.g. `Extracted.program`), got{indentExpr p}"
  let d ← try evalProgDataCore p catch e =>
    throwError "janus64: cannot evaluate the program{indentExpr p}\n{e.toMessageData}"
  progCache.modify (·.insert p d)
  return d

def fetchBytes (segs : List (Nat × List Nat)) (pc : Nat) : Option (List Nat) :=
  match segs with
  | [] => none
  | (base, bytes) :: rest =>
    if base ≤ pc ∧ pc < base + bytes.length then some ((bytes.drop (pc - base)).take 15)
    else fetchBytes rest pc

def evalNat (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  if e.hasFVar || e.hasMVar then return none
  try return some (← evalNatCore e) catch _ => return none

def bv64Value? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``BitVec.ofNat, #[w, n]) =>
    if (← evalNat w) == some 64 then evalNat n else return none
  | (``OfNat.ofNat, #[ty, n, _]) =>
    match (← whnfR ty).getAppFnArgs with
    | (``BitVec, #[w]) => if (← evalNat w) == some 64 then evalNat n else return none
    | _ => return none
  | _ => return none

/-- Prove `b = true` for a closed Boolean `b` by kernel evaluation only. -/
def kernelDecide (b : Expr) : MetaM Expr := do
  let ty ← mkEq b (mkConst ``Bool.true)
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let name ← try mkAuxLemma [] ty val catch e =>
    throwError "janus64: kernel evaluation of{indentExpr b}\nfailed (it is not `true`):\n{e.toMessageData}"
  return mkConst name

/-- Local equations about states: `x.rip = _`, `x.flags = _`, `x.mem = _`, `x.regs i = _`,
`x.xmm i = _`, and memory facts `m.readLE a n = _`. -/
def stateHyps : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, _) := ty.eq? | continue
    if lhs.isAppOfArity ``State.rip 1 || lhs.isAppOfArity ``State.flags 1 ||
        lhs.isAppOfArity ``State.mem 1 || lhs.isAppOfArity ``State.regs 2 ||
        lhs.isAppOfArity ``State.xmm 2 || lhs.isAppOfArity ``State.df 1 ||
        lhs.isAppOfArity ``Janus.Arm64.Memory.readLE 3 then
      out := out.push d.toExpr
  return out

/-- Rewrite rules derived from `RetAddr p ret` hypotheses (see `RetAddr.toNat_ofNat`). -/
def retHyps : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``GoABI.RetAddr 2 then
      for n in [``GoABI.RetAddr.toNat_ofNat, ``GoABI.RetAddr.mod64, ``GoABI.RetAddr.user_eq] do
        out := out.push (← mkAppM n #[d.toExpr])
  return out

/-- A program of the form `Program.withExit p ret`: `(p, ret)`. -/
def exitMode (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let p := (← instantiateMVars p).consumeMData
  match p.getAppFnArgs with
  | (``Program.withExit, #[base, ret]) => return some (base, ret)
  | _ => return none

/-- The hypothesis `RetAddr p ret` from the local context. -/
def findRetAddr (base ret : Expr) : MetaM Expr := do
  let want ← mkAppM ``GoABI.RetAddr #[base, ret]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``GoABI.RetAddr 2 then
      if ← withReducible (isDefEq ty want) then return d.toExpr
  throwError "janus64: the program is{indentExpr (← mkAppM ``Program.withExit #[base, ret])}\nbut there is no hypothesis{indentExpr want}\nin the context (introduce it with `intro ret hret …`)"

structure Cfg where
  args : Array Term := #[]
  stops : List Nat := []
  maxSteps : Nat := 100000

def withExecSimp (cfg : Cfg) (k : Simp.Context → Simp.SimprocsArray → Option Simp.Discharge →
    TacticM α) (set : Name := `janus64_exec) : TacticM α := do
  let hyps ← stateHyps
  let hypStx ← hyps.mapM fun h => do
    let h ← instantiateMVars h
    match h with
    | .fvar id => return (⟨mkIdent (← id.getUserName)⟩ : Term)
    | _ => throwError "unexpected hypothesis"
  let args : Array Term := #[⟨mkIdent set⟩] ++ cfg.args ++
    (hypStx.filter fun t => !(t.raw.getId.isInaccessibleUserName || t.raw.getId.hasMacroScopes))
  let sargs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← args.mapM fun t =>
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  let stx ← `(tactic| simp (disch := janus64_disch) only [$sargs,*])
  let r ← mkSimpContext stx (eraseLocal := false)
  let mut ctx := r.ctx
  let mut thms := ctx.simpTheorems
  for h in hyps do
    let n ← match h with | .fvar id => id.getUserName | _ => pure Name.anonymous
    if n.isInaccessibleUserName || n.hasMacroScopes then
      if let some t0 := thms[0]? then
        thms := thms.set! 0 (← t0.add (.fvar h.fvarId!) #[] h)
  for h in ← retHyps, k in [0:100] do
    if let some t0 := thms[0]? then
      thms := thms.set! 0 (← t0.add (.other (Name.mkNum `janus64_ret k)) #[] h)
  ctx := ctx.setSimpTheorems thms
  let simprocs := r.simprocs.push (← Simp.getSimprocs)
  r.dischargeWrapper.with fun d? => k ctx simprocs d?

def simpExpr (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (d? : Option Simp.Discharge)
    (e : Expr) : MetaM Simp.Result := do
  let (r, _) ← simp e ctx simprocs d?
  return r

def resultProof (e : Expr) (r : Simp.Result) : MetaM Expr := do
  match r.proof? with
  | some pf => return pf
  | none => mkEqRefl e

inductive GoalKind where
  | reaches (p s Q : Expr)
  | execThen (p r Q : Expr)
  | other

def goalKind (g : MVarId) : MetaM GoalKind := do
  let t ← instantiateMVars (← g.getType)
  -- goals produced by `induction`/`intro` may carry metadata or a beta-redex head
  let t ← whnfR t.cleanupAnnotations.headBeta
  match t.getAppFnArgs with
  | (``Reaches, #[p, s, Q]) => return .reaches p s Q
  | (``ExecThen, #[p, r, Q]) => return .execThen p r Q
  | _ => return .other

def tryPrune (g : MVarId) : TacticM Bool := do
  let gs ← try
      Tactic.run g (evalTactic (← `(tactic| (exfalso; omega))))
    catch _ => return false
  return gs.isEmpty

def cleanOutcome (cfg : Cfg) (g : MVarId) : TacticM (List MVarId) := g.withContext do
  setGoals [g]
  withExecSimp cfg (set := `janus64_post) fun ctx simprocs d? => do
    match ← simpGoal g ctx simprocs d? with
    | (none, _) => return []
    | (some (_, g'), _) =>
      let t ← instantiateMVars (← g'.getType)
      if t.isConstOf ``True then g'.assign (mkConst ``True.intro); return []
      return [g']

def statePC (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (d? : Option Simp.Discharge)
    (s : Expr) : MetaM (Option (Nat × Expr) × Expr × Expr) := do
  let pcE ← mkAppM ``State.rip #[s]
  let sw ← instantiateMVars s
  if sw.isAppOfArity ``State.mk 8 then
    let pc := sw.getArg! 1
    if let some c ← bv64Value? pc then
      let ty ← mkEq pcE (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit c))
      return (some (c, ← mkExpectedTypeHint (← mkEqRefl pcE) ty), pc, ← mkEqRefl pcE)
  let r ← simpExpr ctx simprocs d? pcE
  let pf ← resultProof pcE r
  if let some c ← bv64Value? r.expr then
    let ty ← mkEq pcE (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit c))
    return (some (c, ← mkExpectedTypeHint pf ty), r.expr, pf)
  return (none, r.expr, pf)

/-- `pc` is syntactically `BitVec.ofNat 64 ret`. -/
def isRetPC (pc ret : Expr) : MetaM Bool := do
  let pc ← instantiateMVars pc
  let ret ← instantiateMVars ret
  match pc.getAppFnArgs with
  | (``BitVec.ofNat, #[w, r]) =>
    if (← evalNat w) != some 64 then return false
    if r == ret then return true
    withReducible (isDefEq r ret)
  | _ => return false

partial def afterExec (g : MVarId) : TacticM (List MVarId) := do
  match ← goalKind g with
  | .execThen _ r _ =>
    let r ← instantiateMVars r
    match r.getAppFnArgs with
    | (``Except.ok, #[_, _, _]) =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``ExecThen.ok)
      let mut out := []
      for g' in gs do
        if ← g'.isAssigned then continue
        out := out ++ (← afterExec g')
      return out
    | (``ite, #[_, _, _, _, _]) =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``ExecThen.ite)
      let mut out := []
      for g' in gs do
        if (← g'.isAssigned) then continue
        let t ← g'.getType
        if t.isForall then
          let (_, g'') ← g'.intro `hbr
          if ← tryPrune g'' then continue
          out := out ++ (← afterExec g'')
        else out := out ++ [g']
      return out
    | (``Except.error, _) =>
      throwError "janus64: the instruction faults:{indentExpr r}"
    | _ =>
      throwError "janus64: could not evaluate the instruction to `.ok s'` or a branch; stuck at{indentExpr r}\n(a memory access whose `accessible` condition could not be proved, an address that could not be normalised, a flag that is undefined, or a read-over-write whose aliasing is unknown)"
  | .reaches _ s _ =>
    let s ← instantiateMVars s
    if s.isAppOfArity ``ite 5 then
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``Reaches.ite_state)
      let mut out := []
      for g' in gs do
        if (← g'.isAssigned) then continue
        let t ← g'.getType
        if t.isForall then
          let (_, g'') ← g'.intro `hbr
          if ← tryPrune g'' then continue
          out := out ++ (← afterExec g'')
        else out := out ++ [g']
      return out
    return [g]
  | .other => return [g]

def stepGoal (cfg : Cfg) (g : MVarId) (allowStop : Bool) : TacticM (Option (List MVarId)) :=
  g.withContext do
  setGoals [g]
  withExecSimp cfg fun ctx simprocs d? => do
    let .reaches p s Q ← goalKind g | throwError "janus64: goal is not `Reaches p s Q`"
    let (pc?, pcE, pcPf) ← statePC ctx simprocs d? s
    -- a call with a symbolic return address: `p = Program.withExit base retE`
    let mode ← exitMode p
    let hret? ← match mode with
      | some (base, retE) => pure (some (← findRetAddr base retE))
      | none => pure none
    let progE := match mode with | some (base, _) => base | none => p
    if let (some (base, retE), some hret) := (mode, hret?) then
      let atRet ← match pc? with
        | none => isRetPC pcE retE
        | some (c, _) => pure ((← evalNat retE) == some c)
      if atRet then
        let hpc ← mkExpectedTypeHint pcPf
          (← mkEq (← mkAppM ``State.rip #[s]) (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) retE))
        return some (← g.apply (mkAppN (mkConst ``Reaches.exit_withExit) #[base, retE, s, Q, hret, hpc]))
    let some (c, hpc) := pc? |
      throwError "janus64: the rip of the current state is not a concrete address:{indentExpr pcE}"
    if !allowStop && cfg.stops.contains c then return none
    let (exitA, segs, stubs) ← getProgData progE
    let cE := mkNatLit c
    if mode.isNone && c == exitA then
      let hok ← kernelDecide (mkApp2 (mkConst ``exitOK) p cE)
      return some (← g.apply (mkAppN (mkConst ``Reaches.exit) #[p, s, Q, cE, hpc, hok]))
    if let some (_, name, isPanic) := stubs.find? (·.1 == c) then
      let kind := if isPanic then mkConst ``StubKind.panic else mkConst ``StubKind.morestack
      let hok ← kernelDecide (mkApp4 (mkConst ``stubOK) progE cE (toExpr name) kind)
      let lem := match mode, hret? with
        | some (base, retE), some hret =>
          mkAppN (mkConst ``Reaches.stub_withExit) #[base, retE, s, Q, cE, toExpr name, kind, hret,
            hpc, hok]
        | _, _ => mkAppN (mkConst ``Reaches.stub) #[p, s, Q, cE, toExpr name, kind, hpc, hok]
      return some (← g.apply lem)
    let some bs := fetchBytes segs c |
      throwError "janus64: no code at rip 0x{String.ofList (Nat.toDigits 16 c)}"
    let some (i, len) := decode bs |
      throwError "janus64: undecodable bytes {bs} at rip 0x{String.ofList (Nat.toDigits 16 c)}"
    let iE := toExpr i
    let bsE := toExpr bs
    let hok ← kernelDecide (mkAppN (mkConst ``stepOK) #[progE, cE, bsE, iE, mkNatLit len])
    let execE := mkApp3 (mkConst ``exec) iE (mkNatLit len) s
    let r ← simpExpr ctx simprocs d? execE
    let he ← resultProof execE r
    let lemE := match mode, hret? with
      | some (base, retE), some hret =>
        mkAppN (mkConst ``Reaches.step_withExit)
          #[base, retE, s, Q, cE, mkNatLit len, bsE, iE, r.expr, hret, hpc, hok, he]
      | _, _ => mkAppN (mkConst ``Reaches.step)
          #[p, s, Q, cE, mkNatLit len, bsE, iE, r.expr, hpc, hok, he]
    let gs ← g.apply lemE
    let mut out := []
    for g' in gs do
      if ← g'.isAssigned then continue
      out := out ++ (← afterExec g')
    return some out

def prepGoal (g : MVarId) : MetaM MVarId := do
  let t ← instantiateMVars (← g.getType)
  let t ← whnfR t
  let tryApply (n : Name) : MetaM MVarId := do
    let gs ← g.apply (← mkConstWithFreshMVarLevels n)
    match gs with
    | [g'] => return g'
    | _ => throwError "janus64: unexpected goals after {n}"
  match t.getAppFn.constName? with
  | some ``GoABI.Returns => tryApply ``returns_of_reaches
  | some ``GoABI.Panics => tryApply ``panics_of_reaches
  | some ``GoABI.GrowsStack => tryApply ``growsStack_of_reaches
  | _ => return g

def isStepGoal (g : MVarId) : MetaM Bool := do
  match ← goalKind g with
  | .reaches .. => return true
  | _ => return false

def runJanus (cfg : Cfg) (single : Bool) : TacticM Unit := do
  let g ← getMainGoal
  let g ← prepGoal g
  let mut todo : List (MVarId × Bool) := [(g, true)]
  let mut finished : List MVarId := []
  let mut steps := 0
  while !todo.isEmpty do
    let (g, first) :: rest := todo | break
    todo := rest
    if ← g.isAssigned then continue
    if !(← isStepGoal g) then
      finished := finished ++ (← cleanOutcome cfg g); continue
    if steps ≥ cfg.maxSteps || (single && !first) then
      finished := finished ++ [g]; continue
    match ← stepGoal cfg g first with
    | none => finished := finished ++ [g]
    | some gs =>
      steps := steps + 1
      todo := gs.map (·, false) ++ todo
  replaceMainGoal finished

/-! ## Discharger -/

theorem accessible_sub {m : Memory} {a n b k : Nat} {w w' : Bool}
    (h : m.accessible b k w' = true) (hw : (w = false ∨ w' = true)) (h1 : b ≤ a)
    (h2 : a + n ≤ b + k) : m.accessible a n w = true :=
  Janus.Arm64.Memory.accessible_sub m h hw h1 h2

def dischargeAccessible (g : MVarId) : TacticM Bool := g.withContext do
  let gs ← Tactic.run g (evalTactic (← `(tactic|
    try simp only [Janus.Arm64.Memory.accessible_writeLE, State.mem] )))
  let some g := gs.head? | return true
  let t ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := t.eq? | return false
  unless lhs.isAppOfArity ``Janus.Arm64.Memory.accessible 4 do return false
  let m := lhs.getArg! 0
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, _) := ty.eq? | continue
    unless l.isAppOfArity ``Janus.Arm64.Memory.accessible 4 do continue
    unless ← isDefEq (l.getArg! 0) m do continue
    let ok ← try
        let gs ← Tactic.run g do
          let f ← mkConstWithFreshMVarLevels ``accessible_sub
          let (ms, _, _) ← forallMetaTelescopeReducing (← inferType f) (some 8)
          unless ← isDefEq ms[7]! d.toExpr do throwError "janus64_disch: no match"
          let gs ← (← getMainGoal).apply (mkAppN f ms)
          for g' in gs do
            if ← g'.isAssigned then continue
            let rest ← withoutRecover <| Tactic.run g' (evalTactic (← `(tactic| first | decide | omega)))
            unless rest.isEmpty do throwError "janus64_disch: side goal"
          setGoals []
        pure gs.isEmpty
      catch _ => pure false
    if ok then return true
  return false

elab_rules : tactic | `(tactic| janus64_disch) => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if !t.hasFVar && !t.hasMVar then
    -- A closed side condition is decided, never proved from (possibly contradictory) context.
    let gs ← try Tactic.run g (evalTactic (← `(tactic| decide))) catch _ => pure [g]
    if gs.isEmpty then return
    throwError "janus64_disch: closed condition is false{indentExpr t}"
  if let some (_, lhs, _) := t.eq? then
    if lhs.isAppOfArity ``Janus.Arm64.Memory.accessible 4 then
      if ← dischargeAccessible g then return
      throwError "janus64_disch: cannot prove{indentExpr t}"
  evalTactic (← `(tactic| omega))

/-! ## Syntax -/

syntax janus64Args := (" [" term,* "]")?
syntax janus64Until := (" until " "[" term,* "]")?

def parseArgs (stx : Syntax) : Array Term :=
  if stx[0].isNone then #[] else stx[0][1].getSepArgs.map (⟨·⟩)

def parseUntil (stx : Syntax) : TacticM (List Nat) := do
  if stx[0].isNone then return []
  let ts := stx[0][2].getSepArgs
  ts.toList.mapM fun t => do
    let e ← Term.elabTerm t (some (mkConst ``Nat))
    let some n ← evalNat e | throwError "janus64_run until: not a numeral: {t}"
    return n

elab "janus64_run" args:janus64Args stops:janus64Until : tactic => do
  runJanus { args := parseArgs args, stops := ← parseUntil stops } false

elab "janus64_step" args:janus64Args : tactic => do
  runJanus { args := parseArgs args } true

/-- From `hs : CallSetup p entry [a₀, …] s` add `h_rip`, `h_ret`, `h_x15`, `h_df` and `h_a<i>`. For
`p = Program.withExit p₀ ret` (with `hret : RetAddr p₀ ret` in the context) `h_ret` is
`s.mem.readLE (s.regs 4).toNat 8 = ret`. -/
elab "janus64_intro " h:ident : tactic => withMainContext do
  let hE ← elabTerm h none
  let ty ← whnfR (← instantiateMVars (← inferType hE))
  let (``GoABI.CallSetup, #[prog, entry, args, s]) := ty.getAppFnArgs |
    throwError "janus64_intro: expected a `CallSetup` hypothesis"
  let some (_, elemsL) := (← instantiateMVars args).listLit? |
    throwError "janus64_intro: the argument list must be a list literal"
  let elems := elemsL.toArray
  let some entryN ← evalNat entry | throwError "janus64_intro: cannot evaluate the entry address"
  let mode ← exitMode prog
  let exitE ← match mode with
    | some (base, retE) => discard <| findRetAddr base retE; pure retE
    | none =>
      let some exitN ← evalNat (← mkAppM ``Program.exitAddr #[prog]) |
        throwError "janus64_intro: cannot evaluate the exit address"
      pure (mkNatLit exitN)
  let bv (n : Nat) : Expr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)
  let mut g ← getMainGoal
  let ripTy ← mkEq (← mkAppM ``State.rip #[s]) (bv entryN)
  let ripPf ← mkExpectedTypeHint (← mkAppM ``GoABI.CallSetup.rip #[hE]) ripTy
  let (_, g') ← (← g.assert `h_rip ripTy ripPf).intro1P
  g := g'
  g ← g.withContext do
    let rsp := mkApp (← mkAppM ``State.regs #[s]) (mkNatLit 4)
    let lhs ← mkAppM ``Janus.Arm64.Memory.readLE
      #[← mkAppM ``State.mem #[s], ← mkAppM ``BitVec.toNat #[rsp], mkNatLit 8]
    let retTy ← mkEq lhs exitE
    let retPf ← mkExpectedTypeHint (← mkAppM ``GoABI.CallSetup.ret #[hE]) retTy
    let (_, g') ← (← g.assert `h_ret retTy retPf).intro1P
    return g'
  g ← g.withContext do
    let lhs := mkApp (← mkAppM ``State.xmm #[s]) (mkNatLit 15)
    let zTy ← mkEq lhs (← mkAppOptM ``OfNat.ofNat #[mkApp (mkConst ``BitVec) (mkNatLit 128), mkNatLit 0, none])
    let zPf ← mkExpectedTypeHint (← mkAppM ``GoABI.CallSetup.zero #[hE]) zTy
    let (_, g') ← (← g.assert `h_x15 zTy zPf).intro1P
    return g'
  g ← g.withContext do
    let dfTy ← mkEq (← mkAppM ``State.df #[s]) (mkConst ``Bool.false)
    let dfPf ← mkExpectedTypeHint (← mkAppM ``GoABI.CallSetup.df #[hE]) dfTy
    let (_, g') ← (← g.assert `h_df dfTy dfPf).intro1P
    return g'
  for i in [0:elems.size] do
    g ← g.withContext do
      let r := GoABI.argReg i
      let lhs := mkApp (← mkAppM ``State.regs #[s]) (mkNatLit r)
      let tyI ← mkEq lhs elems[i]!
      let lenLt ← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[args]]
      let hlt ← mkDecideProof lenLt
      let pf ← mkAppOptM ``GoABI.CallSetup.reg #[none, none, none, none, hE, mkNatLit i, hlt]
      let pf ← mkExpectedTypeHint pf tyI
      let (_, g') ← (← g.assert (Name.mkSimple s!"h_a{i}") tyI pf).intro1P
      return g'
  replaceMainGoal [g]

end Janus.Amd64.Tactic
