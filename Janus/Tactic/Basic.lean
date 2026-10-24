import Janus.GoABI
import Janus.Tactic.Attr

/-!
# Symbolic execution: the logical layer

This module contains everything the `janus_step` / `janus_run` tactics (`Janus.Tactic.Core`)
produce proofs with. Nothing here is trusted: it is all proved from the model.

* `Reaches p s Q`: from `s`, the run ends (with enough fuel) in an outcome satisfying `Q`.
  It is the goal the tactics work on; `Returns`, `Panics`, `Ensures` reduce to it.
* One-step lemmas `Reaches.step` / `Reaches.exit` / `Reaches.stub`, whose side conditions
  about the program (`stepOK`, `exitOK`, `stubOK`) are Booleans closed by kernel evaluation.
* `setReg`: the register-file update used by the symbolic state normal form, with sorting
  and shadowing lemmas, so that the registers of a symbolic state are a canonical chain
  `setReg (setReg s.regs 1 v₁) 3 v₃` (increasing register numbers, each written once).
* The `janus_exec` simp set: per-constructor `exec` equations (stated by `rfl`, so they need not
  be generated per proof file), helper unfoldings, memory read-over-write lemmas, address
  normalisation (with side conditions discharged by `omega`) and flag/condition lemmas that turn
  `cmp`+`b.cond` into `x.toNat ≤ y.toNat`, `x.toInt < y.toInt`, ...
-/

namespace Janus.Tactic

open Janus Janus.Arm64 Janus.GoABI

/-! ## `Reaches` -/

/-- From `s`, the program ends in an outcome satisfying `Q`, for some finite fuel. -/
def Reaches (p : Program) (s : State) (Q : Outcome → Prop) : Prop :=
  ∃ n o, p.run n s = .ok o ∧ Q o

/-- Continue with `Q` after an instruction that either faulted or produced a state. -/
def ExecThen (p : Program) (r : Except Fault State) (Q : Outcome → Prop) : Prop :=
  match r with
  | .ok s' => Reaches p s' Q
  | .error _ => False

/-- The outcome is a return whose final state satisfies `post`. -/
def IsReturn (post : State → Prop) : Outcome → Prop
  | .returned s => post s
  | .stub _ _ _ => False

/-- The outcome is a Go panic stub. -/
def IsPanic : Outcome → Prop
  | .stub _ .panic _ => True
  | _ => False

/-- The outcome is a `morestack` stub. -/
def IsMorestack : Outcome → Prop
  | .stub _ .morestack _ => True
  | _ => False

@[simp, janus_post] theorem isReturn_returned (post : State → Prop) (s : State) :
    IsReturn post (.returned s) = post s := rfl
@[simp, janus_post] theorem isReturn_stub (post : State → Prop) (n : String) (k : StubKind)
    (s : State) : IsReturn post (.stub n k s) = False := rfl
@[simp, janus_post] theorem isPanic_returned (s : State) : IsPanic (.returned s) = False := rfl
@[simp, janus_post] theorem isPanic_panic (n : String) (s : State) :
    IsPanic (.stub n .panic s) = True := rfl
@[simp, janus_post] theorem isPanic_morestack (n : String) (s : State) :
    IsPanic (.stub n .morestack s) = False := rfl
@[simp, janus_post] theorem isMorestack_returned (s : State) :
    IsMorestack (.returned s) = False := rfl
@[simp, janus_post] theorem isMorestack_panic (n : String) (s : State) :
    IsMorestack (.stub n .panic s) = False := rfl
@[simp, janus_post] theorem isMorestack_morestack (n : String) (s : State) :
    IsMorestack (.stub n .morestack s) = True := rfl
@[simp, janus_post] theorem isPanic_external (n : String) (s : State) :
    IsPanic (.stub n .external s) = False := rfl
@[simp, janus_post] theorem isMorestack_external (n : String) (s : State) :
    IsMorestack (.stub n .external s) = False := rfl

/-- The address `pc` is an ordinary instruction `w`, decoding to `i`: not the exit address, not
a stub, inside the code. Evaluated by the kernel (`decide +kernel`). -/
def stepOK (p : Program) (pc w : Nat) (i : Instr) : Bool :=
  decide (pc < 2 ^ 64) && !(pc == p.exitAddr) && (p.stubAt pc).isNone &&
    (p.fetch pc == some w) && (decode w == some i)

/-- `pc` is the exit address. -/
def exitOK (p : Program) (pc : Nat) : Bool := decide (pc < 2 ^ 64) && pc == p.exitAddr

/-- `pc` is the stub `name` of kind `kind` (and not the exit address). -/
def stubOK (p : Program) (pc : Nat) (name : String) (kind : StubKind) : Bool :=
  decide (pc < 2 ^ 64) && !(pc == p.exitAddr) &&
    match p.stubAt pc with
    | some st => st.name == name && st.kind == kind
    | none => false

/-- The data the tactic reads off a program (evaluated at tactic run time; every use is
re-checked by the kernel through `stepOK`/`exitOK`/`stubOK`): exit address, segments
`(base, words)` and stubs `(addr, name, StubKind.code)`. -/
def progData (p : Program) : Nat × List (Nat × List Nat) × List (Nat × String × Nat) :=
  (p.exitAddr, p.segments.map (fun seg => (seg.base, seg.words)),
    p.stubs.map (fun st => (st.addr, st.name, st.kind.code)))

private theorem pc_toNat_of {s : State} {c : Nat} (hpc : s.pc = BitVec.ofNat 64 c)
    (hc : c < 2 ^ 64) : s.pc.toNat = c := by
  rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

namespace Reaches

variable {p : Program} {s : State} {Q : Outcome → Prop}

theorem intro {n : Nat} {o : Outcome} (h : p.run n s = .ok o) (hq : Q o) : Reaches p s Q :=
  ⟨n, o, h, hq⟩

theorem mono {Q' : Outcome → Prop} (h : Reaches p s Q) (hQ : ∀ o, Q o → Q' o) :
    Reaches p s Q' := by
  obtain ⟨n, o, h, hq⟩ := h; exact ⟨n, o, h, hQ o hq⟩

/-- One ordinary instruction. -/
theorem step {c w : Nat} {i : Instr} {r : Except Fault State}
    (hpc : s.pc = BitVec.ofNat 64 c) (hok : stepOK p c w i = true) (he : exec i s = r)
    (h : ExecThen p r Q) : Reaches p s Q := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    Option.isNone_iff_eq_none, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hc, hx⟩, hs⟩, hf⟩, hd⟩ := hok
  have hpc' := pc_toNat_of hpc hc
  cases r with
  | error e => exact h.elim
  | ok s' =>
    obtain ⟨n, o, hr, hq⟩ := h
    refine ⟨n + 1, o, ?_, hq⟩
    rw [Program.run_succ_step (s' := s') (by rw [hpc']; exact hx) (by rw [hpc']; exact hs)
      (by rw [hpc']; exact hf) (by rw [step_of_decode hd]; exact he)]
    exact hr

/-- The exit address: the call has returned. -/
theorem exit {c : Nat} (hpc : s.pc = BitVec.ofNat 64 c) (hok : exitOK p c = true)
    (hq : Q (.returned s)) : Reaches p s Q := by
  simp only [exitOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  exact ⟨1, _, Program.run_succ_exit (by rw [pc_toNat_of hpc hok.1]; exact hok.2), hq⟩

/-- A stub. -/
theorem stub {c : Nat} {name : String} {kind : StubKind} (hpc : s.pc = BitVec.ofNat 64 c)
    (hok : stubOK p c name kind = true) (hq : Q (.stub name kind s)) : Reaches p s Q := by
  unfold stubOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hok
  obtain ⟨⟨hc, hx⟩, hst⟩ := hok
  have hpc' := pc_toNat_of hpc hc
  cases hfind : p.stubAt c with
  | none => rw [hfind] at hst; cases hst
  | some st =>
    rw [hfind] at hst
    simp only [Bool.and_eq_true, beq_iff_eq] at hst
    obtain ⟨h1, h2⟩ := hst
    refine ⟨1, _, Program.run_succ_stub (by rw [hpc']; exact hx) (by rw [hpc']; exact hfind), ?_⟩
    rw [h1, h2]; exact hq

/-- Prefix of ordinary steps (e.g. a callee summary). -/
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

/-! ### Calls with a symbolic return address

Specifications run `p.withExit ret` for a universally quantified `ret` with `RetAddr p ret`.
The program facts (`stepOK`, `stubOK`) are still evaluated by the kernel on the closed program
`p`; that `pc ≠ ret` follows from `RetAddr` (there is no code and no stub at `ret`), and the
return itself is recognised when the symbolic `pc` is `BitVec.ofNat 64 ret`. -/

namespace Reaches

variable {p : Program} {ret : Nat} {s : State} {Q : Outcome → Prop}

/-! Rewrite rules about `ret` that the executor installs for every `RetAddr` hypothesis (instead
of arithmetic hypotheses, which would slow down every `omega` call): they evaluate the checks of
`RET`/`BR` (`branchReg`: no tag, 4-aligned) on the target `BitVec.ofNat 64 ret`. -/

theorem _root_.Janus.GoABI.RetAddr.toNat_ofNat (hret : RetAddr p ret) :
    (BitVec.ofNat 64 ret).toNat = ret := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hret.lt64]
theorem _root_.Janus.GoABI.RetAddr.mod64 (hret : RetAddr p ret) :
    ret % 18446744073709551616 = ret := Nat.mod_eq_of_lt hret.lt64
theorem _root_.Janus.GoABI.RetAddr.aligned_eq (hret : RetAddr p ret) : (ret % 4 = 0) = True :=
  eq_true hret.aligned
theorem _root_.Janus.GoABI.RetAddr.untagged_eq (hret : RetAddr p ret) :
    (72057594037927936 ≤ ret) = False := eq_false (by have := hret.user; omega)

/-- One ordinary instruction of `p.withExit ret`. -/
theorem step_withExit {c w : Nat} {i : Instr} {r : Except Fault State} (hret : RetAddr p ret)
    (hpc : s.pc = BitVec.ofNat 64 c) (hok : stepOK p c w i = true) (he : exec i s = r)
    (h : ExecThen (p.withExit ret) r Q) : Reaches (p.withExit ret) s Q := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    Option.isNone_iff_eq_none, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hc, _⟩, hs⟩, hf⟩, hd⟩ := hok
  have hpc' := pc_toNat_of hpc hc
  cases r with
  | error e => exact h.elim
  | ok s' =>
    obtain ⟨n, o, hr, hq⟩ := h
    refine ⟨n + 1, o, ?_, hq⟩
    rw [Program.run_succ_step (s' := s') (by rw [hpc']; exact hret.ne_of_fetch hf)
      (by rw [hpc']; exact hs) (by rw [hpc']; exact hf) (by rw [step_of_decode hd]; exact he)]
    exact hr

/-- `pc` is the return address: the call has returned. -/
theorem exit_withExit (hret : RetAddr p ret) (hpc : s.pc = BitVec.ofNat 64 ret)
    (hq : Q (.returned s)) : Reaches (p.withExit ret) s Q :=
  ⟨1, _, Program.run_succ_exit (by rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hret.lt64]; rfl),
    hq⟩

/-- A stub of `p.withExit ret`. -/
theorem stub_withExit {c : Nat} {name : String} {kind : StubKind} (hret : RetAddr p ret)
    (hpc : s.pc = BitVec.ofNat 64 c) (hok : stubOK p c name kind = true)
    (hq : Q (.stub name kind s)) : Reaches (p.withExit ret) s Q := by
  unfold stubOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hok
  obtain ⟨⟨hc, _⟩, hst⟩ := hok
  have hpc' := pc_toNat_of hpc hc
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

/-! ## Specifications in terms of `Reaches` -/

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
    | external => exact hq.elim

theorem growsStack_of_reaches {p : Program} {s : State} (h : Reaches p s IsMorestack) :
    GrowsStack p s := by
  obtain ⟨n, o, hr, hq⟩ := h
  cases o with
  | returned s' => exact hq.elim
  | stub name kind s' =>
    cases kind with
    | panic => exact hq.elim
    | morestack => exact ⟨n, name, s', hr⟩
    | external => exact hq.elim

theorem reaches_of_returns {p : Program} {s : State} {post : State → Prop}
    (h : Returns p s post) : Reaches p s (IsReturn post) := by
  obtain ⟨n, s', hr, hp⟩ := h; exact ⟨n, _, hr, hp⟩

/-! ## Callee summaries

A `Summary p entry pre post` says: from any state at `entry` satisfying `pre`, ordinary steps
(never through the exit address or a stub) reach a state at the return address `X30` that
satisfies `post`. It is what a call (`BL`) needs about the callee, and it is proved by symbolic
execution of the callee alone (`Summary.intro`). -/

/-- Like `Reaches`, but ending when `pc` reaches `ret` (the return address), with ordinary
steps only. -/
def ReachesRet (p : Program) (ret : W64) (s : State) (Q : State → Prop) : Prop :=
  ∃ k s', Program.Steps p s k s' ∧ s'.pc = ret ∧ Q s'

def Summary (p : Program) (entry : Nat) (pre : State → Prop) (post : State → State → Prop) :
    Prop :=
  ∀ s, s.pc = BitVec.ofNat 64 entry → pre s → ReachesRet p (s.regs GoABI.regLR) s (post s)

namespace ReachesRet

variable {p : Program} {ret : W64} {s : State} {Q : State → Prop}

def ExecThenRet (p : Program) (ret : W64) (r : Except Fault State) (Q : State → Prop) : Prop :=
  match r with
  | .ok s' => ReachesRet p ret s' Q
  | .error _ => False

theorem done (hpc : s.pc = ret) (hq : Q s) : ReachesRet p ret s Q :=
  ⟨0, s, .refl s, hpc, hq⟩

theorem step {c w : Nat} {i : Instr} {r : Except Fault State}
    (hpc : s.pc = BitVec.ofNat 64 c) (hok : stepOK p c w i = true) (he : exec i s = r)
    (h : ExecThenRet p ret r Q) : ReachesRet p ret s Q := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    Option.isNone_iff_eq_none, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨hc, hx⟩, hs⟩, hf⟩, hd⟩ := hok
  have hpc' := pc_toNat_of hpc hc
  cases r with
  | error e => exact h.elim
  | ok s' =>
    obtain ⟨k, s'', hst, hr, hq⟩ := h
    exact ⟨k + 1, s'', .step (by rw [hpc']; exact hx) (by rw [hpc']; exact hs)
      (by rw [hpc']; exact hf) (by rw [step_of_decode hd]; exact he) hst, hr, hq⟩

theorem ok {s : State} (h : ReachesRet p ret s Q) : ExecThenRet p ret (.ok s) Q := h

theorem ite {c : Prop} [Decidable c] {r₁ r₂ : Except Fault State}
    (h₁ : c → ExecThenRet p ret r₁ Q) (h₂ : ¬c → ExecThenRet p ret r₂ Q) :
    ExecThenRet p ret (if c then r₁ else r₂) Q := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc]; exact h₂ hc

theorem ite_state {c : Prop} [Decidable c] {s₁ s₂ : State} (h₁ : c → ReachesRet p ret s₁ Q)
    (h₂ : ¬c → ReachesRet p ret s₂ Q) : ReachesRet p ret (if c then s₁ else s₂) Q := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc]; exact h₂ hc

end ReachesRet

/-- Use a callee summary at a call site: `s` is at the callee's entry (after `BL`), `pre s`
holds, and every state the callee may return in (at `s.regs 30`, satisfying `post s`)
continues to `Q`. -/
theorem Reaches.call {p : Program} {entry : Nat} {pre : State → Prop}
    {post : State → State → Prop} {s : State} {Q : Outcome → Prop}
    (hsum : Summary p entry pre post) (hpc : s.pc = BitVec.ofNat 64 entry) (hpre : pre s)
    (h : ∀ s', s'.pc = s.regs GoABI.regLR → post s s' → Reaches p s' Q) : Reaches p s Q := by
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hpc hpre
  exact Reaches.of_steps hst (h s' hr hq)

/-- `ReachesRet` through a nested call. -/
theorem ReachesRet.call {p : Program} {entry : Nat} {pre : State → Prop}
    {post : State → State → Prop} {s : State} {ret : W64} {Q : State → Prop}
    (hsum : Summary p entry pre post) (hpc : s.pc = BitVec.ofNat 64 entry) (hpre : pre s)
    (h : ∀ s', s'.pc = s.regs GoABI.regLR → post s s' → ReachesRet p ret s' Q) :
    ReachesRet p ret s Q := by
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hpc hpre
  obtain ⟨k', s'', hst', hr', hq'⟩ := h s' hr hq
  exact ⟨k + k', s'', hst.trans hst', hr', hq'⟩

/-- A summary of `p` holds in `p.withExit ret` when there is no code at `ret`. -/
theorem Summary.withExit {p : Program} {entry ret : Nat} {pre : State → Prop}
    {post : State → State → Prop} (hsum : Summary p entry pre post) (hret : RetAddr p ret) :
    Summary (p.withExit ret) entry pre post := by
  intro s hpc hpre
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hpc hpre
  exact ⟨k, s', hst.withExit hret.fetch_none, hr, hq⟩

/-! ## Register file normal form -/

/-- Register file `f` with register `r` set to `v`. -/
def setReg (f : Nat → W64) (r : Nat) (v : W64) : Nat → W64 := fun i => if i = r then v else f i

@[janus_exec, janus_post] theorem setReg_apply (f : Nat → W64) (r : Nat) (v : W64) (i : Nat) :
    setReg f r v i = if i = r then v else f i := rfl

@[janus_exec, janus_post] theorem setReg_setReg_same (f : Nat → W64) (r : Nat) (v w : W64) :
    setReg (setReg f r v) r w = setReg f r w := by
  funext i; simp only [setReg]; split <;> rfl

/-- Sort register updates by register number (smaller numbers innermost). The `r + 0` on the
right (folded back by simp's literal arithmetic) keeps simp from treating this as a permutation
lemma, whose term-ordering check is exponential on the DAG-shared values of a symbolic state. -/
@[janus_exec, janus_post] theorem setReg_comm (f : Nat → W64) {r r' : Nat} (v w : W64)
    (h : r' < r) : setReg (setReg f r v) r' w = setReg (setReg f r' w) (r + 0) v := by
  funext i; simp only [setReg, Nat.add_zero]
  by_cases h1 : i = r' <;> by_cases h2 : i = r <;> simp [h1, h2] <;> omega

theorem State.writeZR_eq (s : State) (r : Nat) (v : W64) :
    s.writeZR r v = if r = 31 then s else { s with regs := setReg s.regs r v } := rfl

theorem State.writeSP_eq (s : State) (r : Nat) (v : W64) :
    s.writeSP r v = if r = 31 then { s with sp := v } else { s with regs := setReg s.regs r v } :=
  rfl

attribute [janus_exec] State.writeZR_eq State.writeSP_eq State.readZR State.readSP State.getX
  State.getXSP State.setX State.setXSP State.next State.setFlags

/-! ## `exec`, one equation per constructor -/

section ExecEqns

variable (s : State)

theorem exec_adr_raw (op : Bool) (immlo immhi rd : Nat) :
    exec (.adr op immlo immhi rd) s =
      if op then
        .ok (s.writeZR rd ((s.pc &&& ~~~(0xFFF : W64)) + sext64 33 ((immhi * 4 + immlo) * 2 ^ 12))).next
      else .ok (s.writeZR rd (s.pc + sext64 21 (immhi * 4 + immlo))).next := rfl
@[janus_exec] theorem exec_addSubImm (sf op S sh : Bool) (imm12 rn rd : Nat) :
    exec (.addSubImm sf op S sh imm12 rn rd) s =
      .ok (if sf then execAddSubImm 64 s op S sh imm12 rn rd
           else execAddSubImm 32 s op S sh imm12 rn rd).next := rfl
@[janus_exec] theorem exec_logicalImm (sf : Bool) (opc : LogicOp) (N : Bool) (immr imms rn rd : Nat) :
    exec (.logicalImm sf opc N immr imms rn rd) s =
      .ok (if sf then execLogicalImm 64 s opc N immr imms rn rd
           else execLogicalImm 32 s opc N immr imms rn rd).next := rfl
@[janus_exec] theorem exec_moveWide (sf : Bool) (opc : MoveWideOp) (hw imm16 rd : Nat) :
    exec (.moveWide sf opc hw imm16 rd) s =
      .ok (if sf then execMoveWide 64 s opc hw imm16 rd
           else execMoveWide 32 s opc hw imm16 rd).next := rfl
@[janus_exec] theorem exec_bitfield (sf : Bool) (opc : BitfieldOp) (N : Bool) (immr imms rn rd : Nat) :
    exec (.bitfield sf opc N immr imms rn rd) s =
      .ok (if sf then execBitfield 64 s opc N immr imms rn rd
           else execBitfield 32 s opc N immr imms rn rd).next := rfl
@[janus_exec] theorem exec_extr (sf N : Bool) (rm imms rn rd : Nat) :
    exec (.extr sf N rm imms rn rd) s =
      .ok (if sf then execExtr 64 s rm imms rn rd else execExtr 32 s rm imms rn rd).next := rfl
@[janus_exec] theorem exec_b (op : Bool) (imm26 : Nat) :
    exec (.b op imm26) s =
      .ok { (if op then s.writeZR 30 (s.pc + 4) else s) with
              pc := s.pc + sext64 28 (imm26 * 4) } := by
  cases op <;> rfl
@[janus_exec] theorem exec_bcond (imm19 cond : Nat) :
    exec (.bcond imm19 cond) s =
      if conditionHolds cond s.flags then .ok { s with pc := s.pc + sext64 21 (imm19 * 4) }
      else .ok s.next := rfl
@[janus_exec] theorem exec_cb (sf op : Bool) (imm19 rt : Nat) :
    exec (.cb sf op imm19 rt) s =
      if ((if sf then decide (s.getX 64 rt = 0) else decide (s.getX 32 rt = 0)) != op) = true
      then .ok { s with pc := s.pc + sext64 21 (imm19 * 4) }
      else .ok s.next := rfl
@[janus_exec] theorem exec_tb (b5 op : Bool) (b40 imm14 rt : Nat) :
    exec (.tb b5 op b40 imm14 rt) s =
      if ((s.readZR rt).getLsbD (b5.toNat * 32 + b40) == op) = true
      then .ok { s with pc := s.pc + sext64 16 (imm14 * 4) }
      else .ok s.next := rfl
@[janus_exec] theorem exec_br (rn : Nat) : exec (.br rn) s = branchReg s (s.readZR rn) := rfl
@[janus_exec] theorem exec_blr (rn : Nat) :
    exec (.blr rn) s = branchReg (s.writeZR 30 (s.pc + 4)) (s.readZR rn) := rfl
@[janus_exec] theorem exec_ret (rn : Nat) : exec (.ret rn) s = branchReg s (s.readZR rn) := rfl
@[janus_exec] theorem exec_hint (crm op2 : Nat) : exec (.hint crm op2) s = .ok s.next := rfl
@[janus_exec] theorem exec_barrier (crm op2 : Nat) : exec (.barrier crm op2) s = .ok s.next := rfl
@[janus_exec] theorem exec_ldrLit (opc imm19 rt : Nat) :
    exec (.ldrLit opc imm19 rt) s =
      match (if opc = 0 then memSingle s 2 1 rt (s.pc + sext64 21 (imm19 * 4))
             else if opc = 1 then memSingle s 3 1 rt (s.pc + sext64 21 (imm19 * 4))
             else memSingle s 2 2 rt (s.pc + sext64 21 (imm19 * 4))) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_ldstUImm (size opc imm12 rn rt : Nat) :
    exec (.ldstUImm size opc imm12 rn rt) s =
      match memIndexed s rn (BitVec.ofNat 64 (imm12 * 2 ^ size)) false false
          (fun s a => memSingle s size opc rt a) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_ldstImm9 (size opc : Nat) (mode : Imm9Mode) (imm9 rn rt : Nat) :
    exec (.ldstImm9 size opc mode imm9 rn rt) s =
      match memIndexed s rn (sext64 9 imm9) (match mode with | .post => true | _ => false)
          (match mode with | .unscaled => false | _ => true)
          (fun s a => memSingle s size opc rt a) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_ldstReg (size opc rm : Nat) (option : ExtendType) (S : Bool) (rn rt : Nat) :
    exec (.ldstReg size opc rm option S rn rt) s =
      match memIndexed s rn (extendReg 64 (s.readZR rm) option (if S then size else 0)) false false
          (fun s a => memSingle s size opc rt a) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_ldstPair (opc : Nat) (mode : PairMode) (L : Bool) (imm7 rt2 rn rt : Nat) :
    exec (.ldstPair opc mode L imm7 rt2 rn rt) s =
      match memIndexed s rn ((BitVec.ofNat 7 imm7).signExtend 64 <<< (2 + opc / 2))
          (match mode with | .post => true | _ => false)
          (match mode with | .offset => false | _ => true)
          (fun s a => memPair s opc L rt rt2 a) with
      | .error e => .error e
      | .ok s' => .ok s'.next := rfl
@[janus_exec] theorem exec_logicalShifted (sf : Bool) (opc : LogicOp) (shift : ShiftType) (N : Bool)
    (rm imm6 rn rd : Nat) :
    exec (.logicalShifted sf opc shift N rm imm6 rn rd) s =
      .ok (if sf then execLogicalShifted 64 s opc shift N rm imm6 rn rd
           else execLogicalShifted 32 s opc shift N rm imm6 rn rd).next := rfl
@[janus_exec] theorem exec_addSubShifted (sf op S : Bool) (shift : ShiftType) (rm imm6 rn rd : Nat) :
    exec (.addSubShifted sf op S shift rm imm6 rn rd) s =
      .ok (if sf then execAddSubShifted 64 s op S shift rm imm6 rn rd
           else execAddSubShifted 32 s op S shift rm imm6 rn rd).next := rfl
@[janus_exec] theorem exec_addSubExt (sf op S : Bool) (rm : Nat) (option : ExtendType) (imm3 rn rd : Nat) :
    exec (.addSubExt sf op S rm option imm3 rn rd) s =
      .ok (if sf then execAddSubExt 64 s op S rm option imm3 rn rd
           else execAddSubExt 32 s op S rm option imm3 rn rd).next := rfl
@[janus_exec] theorem exec_addSubCarry (sf op S : Bool) (rm rn rd : Nat) :
    exec (.addSubCarry sf op S rm rn rd) s =
      .ok (if sf then execAddSubCarry 64 s op S rm rn rd
           else execAddSubCarry 32 s op S rm rn rd).next := rfl
@[janus_exec] theorem exec_condCmpReg (sf op : Bool) (rm cond rn nzcv : Nat) :
    exec (.condCmpReg sf op rm cond rn nzcv) s =
      .ok (if sf then execCondCmp s op (s.getX 64 rn) (s.getX 64 rm) cond nzcv
           else execCondCmp s op (s.getX 32 rn) (s.getX 32 rm) cond nzcv).next := rfl
@[janus_exec] theorem exec_condCmpImm (sf op : Bool) (imm5 cond rn nzcv : Nat) :
    exec (.condCmpImm sf op imm5 cond rn nzcv) s =
      .ok (if sf then execCondCmp s op (s.getX 64 rn) (BitVec.ofNat 64 imm5) cond nzcv
           else execCondCmp s op (s.getX 32 rn) (BitVec.ofNat 32 imm5) cond nzcv).next := rfl
@[janus_exec] theorem exec_condSel (sf op : Bool) (rm cond : Nat) (o2 : Bool) (rn rd : Nat) :
    exec (.condSel sf op rm cond o2 rn rd) s =
      .ok (if sf then execCondSel 64 s op rm cond o2 rn rd
           else execCondSel 32 s op rm cond o2 rn rd).next := rfl
@[janus_exec] theorem exec_madd (sf o0 : Bool) (rm ra rn rd : Nat) :
    exec (.madd sf o0 rm ra rn rd) s =
      .ok (if sf then execMadd 64 s o0 rm ra rn rd else execMadd 32 s o0 rm ra rn rd).next := rfl
@[janus_exec] theorem exec_maddl (U o0 : Bool) (rm ra rn rd : Nat) :
    exec (.maddl U o0 rm ra rn rd) s = .ok (execMaddl s U o0 rm ra rn rd).next := rfl
@[janus_exec] theorem exec_mulh (U : Bool) (rm rn rd : Nat) :
    exec (.mulh U rm rn rd) s = .ok (execMulh s U rm rn rd).next := rfl
@[janus_exec] theorem exec_div (sf o1 : Bool) (rm rn rd : Nat) :
    exec (.div sf o1 rm rn rd) s =
      .ok (if sf then execDiv 64 s o1 rm rn rd else execDiv 32 s o1 rm rn rd).next := rfl
@[janus_exec] theorem exec_shiftV (sf : Bool) (t : ShiftType) (rm rn rd : Nat) :
    exec (.shiftV sf t rm rn rd) s =
      .ok (if sf then execShiftV 64 s t rm rn rd else execShiftV 32 s t rm rn rd).next := rfl
@[janus_exec] theorem exec_rbit (sf : Bool) (rn rd : Nat) :
    exec (.rbit sf rn rd) s = .ok (if sf then execRbit 64 s rn rd else execRbit 32 s rn rd).next :=
  rfl
@[janus_exec] theorem exec_rev (sf : Bool) (opc rn rd : Nat) :
    exec (.rev sf opc rn rd) s =
      .ok (if sf then execRev 64 s opc rn rd else execRev 32 s opc rn rd).next := rfl
@[janus_exec] theorem exec_clz (sf : Bool) (rn rd : Nat) :
    exec (.clz sf rn rd) s = .ok (if sf then execClz 64 s rn rd else execClz 32 s rn rd).next :=
  rfl
@[janus_exec] theorem exec_cls (sf : Bool) (rn rd : Nat) :
    exec (.cls sf rn rd) s = .ok (if sf then execCls 64 s rn rd else execCls 32 s rn rd).next :=
  rfl

end ExecEqns

attribute [janus_exec] execAddSubImm execAddSubShifted execAddSubExt execAddSubCarry logicOp
  execLogicalImm execLogicalShifted execMoveWide execBitfield execExtr execCondSel execCondCmp
  execMadd execMaddl execMulh execDiv execShiftV execRbit execRev execClz execCls branchReg
  memSingle memPair memIndexed shiftReg extendReg logicFlags signExtendLoad addSub_fst
  addWithCarry_false_fst addWithCarry_not_true_fst

/-- `baseAddr` for a general register. -/
@[janus_exec] theorem baseAddr_reg (s : State) {rn : Nat} (h : rn ≠ 31) :
    baseAddr s rn = .ok (s.regs rn) := by simp [baseAddr, h]

/-- `baseAddr` for `SP`, when the alignment check passes. -/
@[janus_exec] theorem baseAddr_sp (s : State) (h : s.sp.toNat % 16 = 0) :
    baseAddr s 31 = .ok s.sp := by simp [baseAddr, h]

/-! ## Memory -/

@[janus_exec] theorem load_ok (m : Memory) {a n : Nat} (h : m.accessible a n false = true) :
    load m a n = .ok (m.readLE a n) := load_eq_ok m h

@[janus_exec] theorem store_ok (m : Memory) {a n : Nat} (v : Nat) (h : m.accessible a n true = true) :
    store m a n v = .ok (m.writeLE a n v) := store_eq_ok m v h

attribute [janus_exec, janus_post, janus_acc] Memory.accessible_writeLE Memory.regions_writeLE

@[janus_exec, janus_post] theorem readLE_writeLE_disjoint (m : Memory) {a n b k : Nat} (v : Nat)
    (h : b + k ≤ a ∨ a + n ≤ b) : (m.writeLE a n v).readLE b k = m.readLE b k :=
  Memory.readLE_writeLE_of_disjoint m v h

@[janus_exec, janus_post] theorem readLE_writeLE_same (m : Memory) {a b : Nat} (n v : Nat)
    (h : a = b) : (m.writeLE a n v).readLE b n = v % 256 ^ n := by
  subst h; exact Memory.readLE_writeLE_self m a n v

theorem readLE_writeLE_inside (m : Memory) {a n b k : Nat} (v : Nat) (h1 : a ≤ b)
    (h2 : b + k ≤ a + n) : (m.writeLE a n v).readLE b k = v / 256 ^ (b - a) % 256 ^ k :=
  Memory.readLE_writeLE_inside m v h1 h2

@[janus_exec, janus_post] theorem readLE_mod_8 (m : Memory) (a : Nat) :
    m.readLE a 8 % 18446744073709551616 = m.readLE a 8 :=
  Nat.mod_eq_of_lt (Memory.readLE_lt m a 8)
@[janus_exec, janus_post] theorem readLE_mod_4 (m : Memory) (a : Nat) :
    m.readLE a 4 % 4294967296 = m.readLE a 4 :=
  Nat.mod_eq_of_lt (Memory.readLE_lt m a 4)
@[janus_exec, janus_post] theorem readLE_mod_2 (m : Memory) (a : Nat) :
    m.readLE a 2 % 65536 = m.readLE a 2 :=
  Nat.mod_eq_of_lt (Memory.readLE_lt m a 2)
@[janus_exec, janus_post] theorem readLE_mod_1 (m : Memory) (a : Nat) :
    m.readLE a 1 % 256 = m.readLE a 1 :=
  Nat.mod_eq_of_lt (Memory.readLE_lt m a 1)

@[janus_exec, janus_post] theorem writeLE_mod_8 (m : Memory) (a v : Nat) :
    m.writeLE a 8 (v % 18446744073709551616) = m.writeLE a 8 v := Memory.writeLE_mod m a 8 v
@[janus_exec, janus_post] theorem writeLE_mod_4 (m : Memory) (a v : Nat) :
    m.writeLE a 4 (v % 4294967296) = m.writeLE a 4 v := Memory.writeLE_mod m a 4 v
@[janus_exec, janus_post] theorem writeLE_mod_1 (m : Memory) (a v : Nat) :
    m.writeLE a 1 (v % 256) = m.writeLE a 1 v := Memory.writeLE_mod m a 1 v

/-! ## Arithmetic normalisation (addresses and values) -/

/-- `2^64` as the literal simp normalises it to. -/
abbrev M64 : Nat := 18446744073709551616

attribute [janus_exec, janus_post] BitVec.toNat_add BitVec.toNat_sub BitVec.toNat_ofNat
  BitVec.setWidth_eq BitVec.shiftLeft_zero BitVec.ushiftRight_zero

@[janus_exec, janus_post] theorem mod64_of_lt {a : Nat} (h : a < 18446744073709551616) :
    a % 18446744073709551616 = a := Nat.mod_eq_of_lt h

/-- `x + (2^64 - k)` wraps to `x - k` (negative offsets, `SUB` by immediate). -/
@[janus_exec, janus_post] theorem mod64_add_wrap {n c : Nat}
    (hc : Nat.blt c 18446744073709551616 = true)
    (h : 18446744073709551616 - c ≤ n) (hn : n < 18446744073709551616) :
    (n + c) % 18446744073709551616 = n - (18446744073709551616 - c) := by
  have := Nat.blt_eq.mp hc
  rw [show n + c = (n - (18446744073709551616 - c)) + 18446744073709551616 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The literal `c` must be on the left (the `Nat.blt` condition only closes on literals). -/
@[janus_exec, janus_post] theorem mod64_add_wrap' {n c : Nat}
    (hc : Nat.blt c 18446744073709551616 = true)
    (h : 18446744073709551616 - c ≤ n) (hn : n < 18446744073709551616) :
    (c + n) % 18446744073709551616 = n - (18446744073709551616 - c) := by
  rw [Nat.add_comm]; exact mod64_add_wrap hc h hn

/-- The SP alignment check, discharged arithmetically. -/
@[janus_exec] theorem aligned16_true {n : Nat} (h : n % 16 = 0) : (n % 16 = 0) = True :=
  eq_true h

@[janus_exec, janus_post] theorem toNat_ofNat_readLE_8 (m : Memory) (a : Nat) :
    (BitVec.ofNat 64 (m.readLE a 8)).toNat = m.readLE a 8 := by
  rw [BitVec.toNat_ofNat]; exact readLE_mod_8 m a

/-! ## Flags and conditions

After `cmp x, y` (`subs xzr, x, y`) the flags are `(addSub x y true).2`. The lemmas below turn
`conditionHolds cond` of these flags into arithmetic on `toNat` / `toInt`; they are applied
before the generic unfolding of `conditionHolds` (higher priority). -/

section Flags

variable (x y : BitVec 64)

theorem toInt64_cond (x : BitVec 64) : x.toInt = if x.toNat < 9223372036854775808 then (x.toNat : Int) else (x.toNat : Int) - 18446744073709551616 := by
  rw [BitVec.toInt_eq_toNat_cond]; by_cases h : x.toNat < 9223372036854775808
  · rw [ite_eq_left_iff.mpr (fun h' => absurd (by omega) h'), ite_eq_left_iff.mpr (fun h' => absurd h h')]
  · rw [ite_eq_right (by omega), ite_eq_right h]; rfl

private theorem subRes : (BitVec.ofNat 64 (x.toNat + (~~~y).toNat + true.toNat)).toNat = (x.toNat + 18446744073709551616 - y.toNat) % 18446744073709551616 := by
  simp only [BitVec.toNat_ofNat, BitVec.toNat_not, Bool.toNat_true]
  have := y.isLt; congr 1; omega

theorem sub_flags_c : (addSub x y true).2.c = decide (y.toNat ≤ x.toNat) := by
  simp only [addSub, addWithCarry, ite_true, subRes]
  simp only [BitVec.toNat_not, Bool.toNat_true]
  have := x.isLt; have := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · rw [show x.toNat + 18446744073709551616 - y.toNat = (x.toNat - y.toNat) + 18446744073709551616 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [h]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; simp [h]; omega

theorem sub_flags_z : (addSub x y true).2.z = decide (x.toNat = y.toNat) := by
  simp only [addSub, addWithCarry, ite_true]
  have hr := subRes x y
  have := x.isLt; have := y.isLt
  by_cases h : x.toNat = y.toNat
  · have : BitVec.ofNat 64 (x.toNat + (~~~y).toNat + true.toNat) = 0 := by
      apply BitVec.eq_of_toNat_eq; rw [hr]
      rw [show x.toNat + 18446744073709551616 - y.toNat = 18446744073709551616 by omega]; rfl
    rw [decide_eq_true this, decide_eq_true h]
  · have : BitVec.ofNat 64 (x.toNat + (~~~y).toNat + true.toNat) ≠ 0 := by
      intro h'; have h'' := congrArg BitVec.toNat h'; rw [hr] at h''; change _ = 0 at h''
      by_cases hle : y.toNat ≤ x.toNat
      · rw [show x.toNat + 18446744073709551616 - y.toNat = (x.toNat - y.toNat) + 18446744073709551616 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h''; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at h''; omega
    rw [decide_eq_false this, decide_eq_false h]

private theorem decide_beq_decide (A B : Prop) [Decidable A] [Decidable B] :
    (decide A == decide B) = decide (A ↔ B) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

theorem sub_flags_nv :
    ((addSub x y true).2.n == (addSub x y true).2.v) = decide (y.toInt ≤ x.toInt) := by
  simp only [addSub, addWithCarry, ite_true, BitVec.msb_eq_decide]
  rw [toInt64_cond (BitVec.ofNat 64 _), subRes, toInt64_cond (~~~y), toInt64_cond x, toInt64_cond y]
  have := x.isLt; have := y.isLt
  simp only [Bool.toNat_true, BitVec.toNat_not, Nat.reducePow, Nat.reduceSub,
    decide_not]
  rw [← decide_not, decide_beq_decide]
  apply decide_eq_decide.mpr
  by_cases h : y.toNat ≤ x.toNat
  · rw [show x.toNat + 18446744073709551616 - y.toNat = (x.toNat - y.toNat) + 18446744073709551616 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    split <;> split <;> split <;> split <;> omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    split <;> split <;> split <;> split <;> omega

@[janus_exec high, janus_post high] theorem cond_sub_eq :
    conditionHolds 0 (addSub x y true).2 = decide (x.toNat = y.toNat) := by
  simp [conditionHolds, sub_flags_z]
@[janus_exec high, janus_post high] theorem cond_sub_ne :
    conditionHolds 1 (addSub x y true).2 = decide (x.toNat ≠ y.toNat) := by
  simp [conditionHolds, sub_flags_z]
@[janus_exec high, janus_post high] theorem cond_sub_hs :
    conditionHolds 2 (addSub x y true).2 = decide (y.toNat ≤ x.toNat) := by
  simp [conditionHolds, sub_flags_c]
@[janus_exec high, janus_post high] theorem cond_sub_lo :
    conditionHolds 3 (addSub x y true).2 = decide (x.toNat < y.toNat) := by
  simp only [conditionHolds, sub_flags_c]
  by_cases h : y.toNat ≤ x.toNat
  · simp [h]
  · simp [h]; omega
@[janus_exec high, janus_post high] theorem cond_sub_hi :
    conditionHolds 8 (addSub x y true).2 = decide (y.toNat < x.toNat) := by
  simp only [conditionHolds, sub_flags_c, sub_flags_z]
  by_cases h : y.toNat < x.toNat
  · simp [h, show y.toNat ≤ x.toNat by omega, show x.toNat ≠ y.toNat by omega]
  · simp [h]; omega
@[janus_exec high, janus_post high] theorem cond_sub_ls :
    conditionHolds 9 (addSub x y true).2 = decide (x.toNat ≤ y.toNat) := by
  simp only [conditionHolds, sub_flags_c, sub_flags_z]
  by_cases h : x.toNat ≤ y.toNat
  · simp [h]; omega
  · simp [h, show y.toNat ≤ x.toNat by omega, show x.toNat ≠ y.toNat by omega]
@[janus_exec high, janus_post high] theorem cond_sub_ge :
    conditionHolds 10 (addSub x y true).2 = decide (y.toInt ≤ x.toInt) := by
  simp only [conditionHolds, sub_flags_nv]; rfl
@[janus_exec high, janus_post high] theorem cond_sub_lt :
    conditionHolds 11 (addSub x y true).2 = decide (x.toInt < y.toInt) := by
  simp only [conditionHolds, sub_flags_nv]
  by_cases h : y.toInt ≤ x.toInt
  · simp [h]
  · simp [h]; omega
@[janus_exec high, janus_post high] theorem cond_sub_gt :
    conditionHolds 12 (addSub x y true).2 = decide (y.toInt < x.toInt) := by
  simp only [conditionHolds, sub_flags_nv, sub_flags_z]
  have hz : x.toNat = y.toNat ↔ x.toInt = y.toInt := BitVec.toNat_inj.trans BitVec.toInt_inj.symm
  by_cases h : y.toInt < x.toInt
  · simp [h, show y.toInt ≤ x.toInt by omega, hz, show x.toInt ≠ y.toInt by omega]
  · by_cases h' : y.toInt ≤ x.toInt
    · simp [hz, show x.toInt = y.toInt by omega]
    · simp [h, h']
@[janus_exec high, janus_post high] theorem cond_sub_le :
    conditionHolds 13 (addSub x y true).2 = decide (x.toInt ≤ y.toInt) := by
  simp only [conditionHolds, sub_flags_nv, sub_flags_z]
  have hz : x.toNat = y.toNat ↔ x.toInt = y.toInt := BitVec.toNat_inj.trans BitVec.toInt_inj.symm
  by_cases h : y.toInt < x.toInt
  · simp [h, show y.toInt ≤ x.toInt by omega, hz, show x.toInt ≠ y.toInt by omega]
  · by_cases h' : y.toInt ≤ x.toInt
    · simp [hz, show x.toInt = y.toInt by omega]
    · simp [h']; omega

end Flags

/-- Generic evaluation of `conditionHolds` on a literal condition code (used when the flags
do not come from a subtraction). -/
@[janus_exec, janus_post] theorem conditionHolds_eq (cond : Nat) (f : Flags) :
    conditionHolds cond f =
      let base :=
        match cond / 2 with
        | 0 => f.z | 1 => f.c | 2 => f.n | 3 => f.v | 4 => f.c && !f.z | 5 => f.n == f.v
        | 6 => f.n == f.v && !f.z | _ => true
      if cond % 2 = 1 && cond ≠ 15 then !base else base := rfl

/-- `cbz`/`cbnz` on a 64-bit register: compare its value with zero. -/
@[janus_exec, janus_post] theorem bv64_eq_zero (x : BitVec 64) :
    decide (x = 0#64) = decide (x.toNat = 0) := by
  apply decide_eq_decide.mpr
  exact ⟨fun h => by simp [h], fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩

end Janus.Tactic

namespace Janus.Tactic
open Janus Janus.Arm64 Janus.GoABI

/-! ## Basic logic for the simp sets -/

attribute [janus_exec, janus_post] ge_iff_le gt_iff_lt ite_true ite_false ite_self
  Bool.true_and Bool.and_true Bool.false_and Bool.and_false Bool.not_true Bool.not_false
  Bool.true_or Bool.or_true Bool.false_or Bool.or_false Bool.not_not decide_eq_true_eq
  decide_eq_false_iff_not decide_true decide_false decide_not Bool.true_eq_false Bool.false_eq_true
  ne_eq not_false_eq_true not_true_eq_false eq_self_iff_true and_true true_and and_false false_and
  or_true true_or or_false false_or Bool.bne_true Bool.bne_false Bool.not_eq_true Bool.not_eq_false
  beq_self_eq_true bne_self_eq_false Bool.toNat_true Bool.toNat_false
  Nat.add_zero Nat.zero_add Nat.mul_one Nat.one_mul Nat.mul_zero Nat.zero_mul Nat.zero_mod
  Nat.mod_self BitVec.add_zero BitVec.zero_add BitVec.sub_zero ite_not dite_eq_ite
  if_true_left if_false_left if_true_right if_false_right

theorem abiReturn_iff (s₀ s₁ : State) :
    ABIReturn s₀ s₁ ↔ s₁.sp = s₀.sp ∧ s₁.regs 28 = s₀.regs 28 ∧ s₁.regs 29 = s₀.regs 29 ∧
      s₁.regs 18 = s₀.regs 18 :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

attribute [janus_post] abiReturn_iff State.writeZR_eq

end Janus.Tactic

namespace Janus.Tactic
open Janus Janus.Arm64

/-! ## Carry chains as `Nat` arithmetic (`janus_post`)

`adds`/`adcs` leave `(addWithCarry x y c).1` (the sum) and `.2.c` (the carry out). For the
final arithmetic these become `(x + y + c) % 2^64` and `(x + y + c) / 2^64`, which `omega`
handles directly. -/

@[janus_post] theorem awc_fst_toNat (x y : BitVec 64) (c : Bool) :
    (addWithCarry x y c).1.toNat = (x.toNat + y.toNat + c.toNat) % 18446744073709551616 := by
  simp [addWithCarry]

@[janus_post] theorem awc_c_toNat (x y : BitVec 64) (c : Bool) :
    (addWithCarry x y c).2.c.toNat = (x.toNat + y.toNat + c.toNat) / 18446744073709551616 := by
  simp only [addWithCarry, BitVec.toNat_ofNat]
  have := x.isLt; have := y.isLt; have : c.toNat ≤ 1 := Bool.toNat_le c
  by_cases h : x.toNat + y.toNat + c.toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt (by omega)]; simp
  · rw [show x.toNat + y.toNat + c.toNat = (x.toNat + y.toNat + c.toNat - 2 ^ 64) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [show (x.toNat + y.toNat + c.toNat - 2 ^ 64 + 2 ^ 64) / 18446744073709551616 = 1 by omega]
    simp

@[janus_exec, janus_post] theorem addSub_false_snd {N : Nat} (x y : BitVec N) :
    (addSub x y false).2 = (addWithCarry x y false).2 := rfl

/-- `(x + y).toNat` as an addition modulo `2^64` (used by `janus_post`). -/
@[janus_post] theorem toNat_awc_carry_bound (x y : BitVec 64) (c : Bool) :
    (addWithCarry x y c).2.c.toNat ≤ 1 := Bool.toNat_le _

end Janus.Tactic

namespace Janus.Tactic
open Janus Janus.Arm64

/-! ## Logical and multiply aliases -/

attribute [janus_exec, janus_post] BitVec.zero_or BitVec.or_zero BitVec.zero_and BitVec.and_zero
  BitVec.xor_zero BitVec.zero_xor BitVec.or_self BitVec.and_self

attribute [janus_post] BitVec.toNat_mul BitVec.toNat_udiv
attribute [janus_exec, janus_post, janus_disch_norm] BitVec.toNat_or BitVec.toNat_and
  BitVec.toNat_xor

/-- `umulh`: the high 64 bits of the 128-bit product. -/
@[janus_exec, janus_post] theorem umulh_toNat (x y : BitVec 64) :
    (BitVec.extractLsb' 64 64 (x.setWidth 128 * y.setWidth 128)).toNat =
      x.toNat * y.toNat / 18446744073709551616 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (a := x.toNat) (by have := x.isLt; omega),
    Nat.mod_eq_of_lt (a := y.toNat) (by have := y.isLt; omega)]
  have hx := x.isLt; have hy := y.isLt
  have hp : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 :=
          Nat.mul_lt_mul_of_lt_of_lt hx hy
      _ = 2 ^ 128 := by rw [← Nat.pow_add]
  rw [Nat.mod_eq_of_lt hp, Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  apply Nat.div_lt_of_lt_mul
  calc x.toNat * y.toNat < 2 ^ 128 := hp
    _ = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]

end Janus.Tactic

namespace Janus.Tactic
open Janus Janus.Arm64

/-! ## Constant offsets on 64-bit values (stack pointer arithmetic)

Normal form: `x + k#64` or `x - k#64` with `0 < k < 2^63`; negative immediates
(`sp + 0xfff…f0`) become subtractions and chains of constant offsets are folded. -/

@[janus_exec, janus_post] theorem bv_add_neg (x : BitVec 64) {c : Nat}
    (hc : (Nat.ble 9223372036854775808 c && Nat.blt c 18446744073709551616) = true) :
    x + BitVec.ofNat 64 c = x - BitVec.ofNat 64 (18446744073709551616 - c) := by
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
  obtain ⟨h, h2⟩ := hc
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := c) (by omega),
    Nat.mod_eq_of_lt (a := 18446744073709551616 - c) (by omega)]
  have := x.isLt
  congr 1; omega

@[janus_exec, janus_post] theorem bv_add_add (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

@[janus_exec, janus_post] theorem bv_sub_sub (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

@[janus_exec, janus_post] theorem bv_sub_add_le (x : BitVec 64) {a b : Nat} (hc : Nat.ble b a = true) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a - b) := by
  have h := Nat.ble_eq.mp hc
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

@[janus_exec, janus_post] theorem bv_sub_add_gt (x : BitVec 64) {a b : Nat} (hc : Nat.blt a b = true) :
    x - BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (b - a) := by
  have h := Nat.blt_eq.mp hc
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

@[janus_exec, janus_post] theorem bv_sub_zero' (x : BitVec 64) : x - BitVec.ofNat 64 0 = x := by
  simp

@[janus_exec, janus_post] theorem bv_add_zero' (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := by
  simp

end Janus.Tactic

namespace Janus.Tactic
attribute [janus_disch_norm] BitVec.toNat_add BitVec.toNat_sub BitVec.toNat_ofNat mod64_of_lt
  mod64_add_wrap mod64_add_wrap' toNat_ofNat_readLE_8
  readLE_mod_8 bv_add_neg bv_add_add bv_sub_sub bv_sub_add_le bv_sub_add_gt bv_sub_zero'
  bv_add_zero'
end Janus.Tactic

namespace Janus.Tactic
open Janus Janus.Arm64

@[janus_exec, janus_post] theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by simp)

/-- Zero tests on 64-bit values become `toNat` tests (for `omega`). -/
@[janus_exec, janus_post] theorem bv64_eq_zero_prop (x : BitVec 64) : (x = 0#64) = (x.toNat = 0) := by
  apply propext; constructor
  · intro h; simp [h]
  · intro h; exact BitVec.eq_of_toNat_eq (by simpa using h)

end Janus.Tactic

namespace Janus.Tactic
@[janus_exec, janus_post] theorem bv64_eq_zero_prop' (x : BitVec 64) : (x = 0) = (x.toNat = 0) :=
  bv64_eq_zero_prop x
attribute [janus_exec, janus_post] BitVec.toNat_zero BitVec.ofNat_eq_ofNat
end Janus.Tactic

namespace Janus.Tactic

/-! ## Deciding arithmetic conditions during stepping

Branch and check conditions (`if a ≤ b then …`) that follow from the hypotheses are decided by
the discharger (`omega`), so infeasible paths are never explored. -/

theorem nat_le_true {a b : Nat} (h : a ≤ b) : (a ≤ b) = True := eq_true h
theorem nat_le_false {a b : Nat} (h : b < a) : (a ≤ b) = False :=
  eq_false (Nat.not_le.mpr h)
theorem nat_lt_true {a b : Nat} (h : a < b) : (a < b) = True := eq_true h
theorem nat_lt_false {a b : Nat} (h : b ≤ a) : (a < b) = False :=
  eq_false (Nat.not_lt.mpr h)
theorem nat_eq_true {a b : Nat} (h : a = b) : (a = b) = True := eq_true h
theorem nat_eq_false {a b : Nat} (h : a ≠ b) : (a = b) = False := eq_false h
theorem int_le_true {a b : Int} (h : a ≤ b) : (a ≤ b) = True := eq_true h
theorem int_le_false {a b : Int} (h : b < a) : (a ≤ b) = False :=
  eq_false (Int.not_le.mpr h)
theorem int_lt_true {a b : Int} (h : a < b) : (a < b) = True := eq_true h
theorem int_lt_false {a b : Int} (h : b ≤ a) : (a < b) = False :=
  eq_false (Int.not_lt.mpr h)

end Janus.Tactic

namespace Janus.Tactic
/-- `LSL` by a constant (scaled register offsets `[x0, x3, lsl #3]`), as a product with the
power of two on the left. -/
theorem bv_toNat_shiftLeft (x : BitVec 64) (n : Nat) :
    (x <<< n).toNat = 2 ^ n * x.toNat % 18446744073709551616 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
attribute [janus_exec, janus_post, janus_disch_norm] bv_toNat_shiftLeft
end Janus.Tactic

namespace Janus.Tactic
/-- Signed comparisons of values known to be below `2^63` (lengths, indices) are unsigned. -/
@[janus_exec, janus_post] theorem toInt_of_lt (x : BitVec 64) (h : x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) := by
  rw [toInt64_cond, ite_eq_left h]
end Janus.Tactic

namespace Janus.Tactic
open Janus

/-- The address of the extracted function `name` (the base of its segment; `0` if absent).
Use it instead of literal callee addresses, e.g. `segAddr Extracted.program "example.com/basic.Add"`. -/
def segAddr (p : Program) (name : String) : Nat :=
  match p.segments.find? (·.name == name) with
  | some seg => seg.base
  | none => 0

end Janus.Tactic

namespace Janus.Tactic
/-- A quotient of a 64-bit value fits in 64 bits (`udiv` results). -/
@[janus_exec, janus_post] theorem toNat_div_mod64 (x : BitVec 64) (k : Nat) :
    x.toNat / k % 18446744073709551616 = x.toNat / k :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)
end Janus.Tactic

namespace Janus.Tactic
open Janus Janus.Arm64

/-! ## Sign-extended immediates as `Nat` arithmetic

Branch offsets, `adrp` pages and load/store offsets are sign-extended immediates. Evaluating
`BitVec.signExtend` by definitional unfolding is deep for the kernel, so these lemmas turn them
into `BitVec.ofNat 64 n` with `n` computed by `Nat` arithmetic (which the kernel evaluates with
GMP). The side conditions on the width are closed by `decide`. -/

theorem signExtend_ofNat_eq (w imm : Nat) (hc : (Nat.blt 0 w && Nat.ble w 64) = true) :
    (BitVec.ofNat w imm).signExtend 64 =
      BitVec.ofNat 64 (if imm % 2 ^ w < 2 ^ (w - 1) then imm % 2 ^ w
        else imm % 2 ^ w + (18446744073709551616 - 2 ^ w)) := by
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
  obtain ⟨h0, h64⟩ := hc
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat]
  have hw : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h64
  have hm : imm % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have hh : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  generalize imm % 2 ^ w = r at *
  generalize 2 ^ w = W at *
  generalize 2 ^ (w - 1) = H at *
  simp only [Nat.reducePow] at *
  split <;> split <;> simp_all <;> omega

@[janus_exec, janus_disch_norm] theorem sext64_eq (w imm : Nat)
    (hc : (Nat.blt 0 w && Nat.ble w 64) = true) :
    sext64 w imm = BitVec.ofNat 64 (if imm % 2 ^ w < 2 ^ (w - 1) then imm % 2 ^ w
        else imm % 2 ^ w + (18446744073709551616 - 2 ^ w)) :=
  signExtend_ofNat_eq w imm hc

attribute [janus_exec] signExtend_ofNat_eq

@[janus_exec] theorem ofNat_shiftLeft_64 (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- The `adrp` page base. -/
@[janus_exec] theorem and_not_fff (x : BitVec 64) :
    x &&& ~~~(4095#64) = BitVec.ofNat 64 (x.toNat / 4096 * 4096) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (a := x.toNat / 4096 * 4096) (by omega)]
  rw [show (2 : Nat) ^ 64 - 1 - 4095 % 2 ^ 64 = 2 ^ 64 - 2 ^ 12 by decide]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show x.toNat / 4096 * 4096 = x.toNat >>> 12 <<< 12 by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow], Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    show (2 : Nat) ^ 64 - 2 ^ 12 = (2 ^ 52 - 1) * 2 ^ 12 by decide, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 12
  · simp [show ¬ (12 ≤ i) by omega]
  · by_cases hi2 : i < 64
    · simp [show 12 ≤ i by omega, show 12 + (i - 12) = i by omega]; intro; omega
    · have : x.toNat.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt
        (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this, show 12 ≤ i by omega, show 12 + (i - 12) = i by omega]

end Janus.Tactic

namespace Janus.Tactic
open Janus Janus.Arm64

/-- `ADR`/`ADRP` with the page base computed in `Nat` (`adrp`: `(pc / 4096) * 4096 + imm`). -/
@[janus_exec] theorem exec_adr (s : State) (op : Bool) (immlo immhi rd : Nat) :
    exec (.adr op immlo immhi rd) s =
      if op then
        .ok (s.writeZR rd (BitVec.ofNat 64 (s.pc.toNat / 4096 * 4096) +
          sext64 33 ((immhi * 4 + immlo) * 2 ^ 12))).next
      else .ok (s.writeZR rd (s.pc + sext64 21 (immhi * 4 + immlo))).next := by
  rw [exec_adr_raw, ← and_not_fff]; rfl

end Janus.Tactic

namespace Janus.Tactic
/-- Masking with `2^k - 1` (`and x0, x0, #0xf`) is a remainder. The side condition (that `m + 1`
is a power of two) is evaluated on literals. -/
@[janus_exec, janus_post, janus_disch_norm] theorem land_mask (x m : Nat)
    (h : (m + 1 == 2 ^ Nat.log2 (m + 1)) = true) : x &&& m = x % (m + 1) := by
  have h' : m + 1 = 2 ^ Nat.log2 (m + 1) := by simpa using h
  have : m = 2 ^ Nat.log2 (m + 1) - 1 := by omega
  rw [this, Nat.and_two_pow_sub_one_eq_mod, ← this]
  congr 1; omega
end Janus.Tactic

namespace Janus.Tactic
/-! ## Carry normalisation for `janus_arith` -/

/-- A carry (`a / 2^64` of a sum `a < 2^65`) is already below `2^64`. -/
@[janus_arith_norm] theorem carry_mod {a : Nat} (h : a < 36893488147419103232) :
    a / 18446744073709551616 % 18446744073709551616 = a / 18446744073709551616 :=
  Nat.mod_eq_of_lt (by omega)

/-- `adds xd, xc, #-1` re-creates the carry flag from a saved carry `c ∈ {0, 1}`. -/
@[janus_arith_norm] theorem carry_restore {c : Nat} (h : c ≤ 1) :
    (c + 18446744073709551615) / 18446744073709551616 = c := by omega
end Janus.Tactic

namespace Janus.Tactic
/-! ## Collapsing nested `% 2^64`

`toNat` of a chain of 64-bit additions is a chain of `% 2^64`; collapsing it keeps one modulus,
which keeps the `omega` problems (and the failed attempts of `mod64_of_lt`) small. -/
attribute [janus_exec, janus_post] Nat.mod_add_mod Nat.add_mod_mod Nat.mod_mul_mod Nat.mul_mod_mod
  Nat.mod_mod
end Janus.Tactic

namespace Janus.Tactic
@[janus_post] theorem toNat_div_lt64 (x : BitVec 64) (k : Nat) :
    (x.toNat / k < 18446744073709551616) = True :=
  eq_true (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)
end Janus.Tactic

namespace Janus.Tactic
attribute [janus_exec, janus_post] Bool.not_eq_eq_eq_not Bool.not_eq_true' Bool.not_true
  Bool.not_false decide_not
end Janus.Tactic
