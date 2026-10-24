import JanusASL.Proofs.Run
import Janus

/-! # Transferring shipped example theorems to the ASL

`Ensures.toASL` turns a Janus `Ensures` specification of a program whose words are all in the
proved subset into the same statement about the ASL run (`aslRun`), for every ASL state related to
the call state under `LinuxEL0Config`. Applied to two shipped examples: `Add` and `Max`
(programs from `artifacts/{Add,Max}/Extracted.lean`, proofs from `examples/proofs/{Add,Max}.lean`,
both copied verbatim). -/

namespace JanusASL.Proofs
open Janus Janus.Arm64 Janus.GoABI

theorem fetchIn_some {segs : List Segment} {pc w : Nat} (h : Program.fetchIn segs pc = some w) :
    ∃ seg ∈ segs, pc < seg.base + 4 * seg.words.length ∧ w ∈ seg.words := by
  induction segs with
  | nil => simp [Program.fetchIn] at h
  | cons seg rest ih =>
    simp only [Program.fetchIn] at h
    split at h
    · next hb =>
      split at h
      · next w' hw =>
        cases h
        refine ⟨seg, List.mem_cons_self .., ?_, List.mem_of_getElem? hw⟩
        have := (List.getElem?_eq_some_iff.mp hw).1
        omega
      · obtain ⟨sg, hm, h1, h2⟩ := ih h
        exact ⟨sg, List.mem_cons_of_mem _ hm, h1, h2⟩
    · obtain ⟨sg, hm, h1, h2⟩ := ih h
      exact ⟨sg, List.mem_cons_of_mem _ hm, h1, h2⟩

/-- **A Janus specification holds of the ASL.** If every word of `p` is in the proved subset,
its code is untagged and it has no stubs below the tag boundary issue (`hu`), then every Janus
`Ensures` theorem about `p` gives: from any ASL state related to a call state (under
`LinuxEL0Config`), the ASL run returns to the caller in a state related to one satisfying the
postcondition. -/
theorem Ensures.toASL {p : Program} {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (hE : Ensures p entry args pre post)
    (hp : ∀ w ∈ p.segments.flatMap (·.words), StepOK w)
    (hcode : ∀ seg ∈ p.segments, seg.base + 4 * seg.words.length < 2 ^ 56)
    (hstub : ∀ st ∈ p.stubs, st.addr < 2 ^ 56)
    {ret : Nat} (hret : RetAddr p ret) {js : State} (hs : CallSetup (p.withExit ret) entry args js) (hpre : pre js)
    {s : SState} (h : Rel js s) (hc : LinuxEL0Config s) :
    ∃ fuel s' js', aslRun (p.withExit ret) fuel s = .returned s' ∧ Rel js' s' ∧ LinuxEL0Config s' ∧
      ABIReturn js js' ∧ post js js' := by
  obtain ⟨fuel, js', hrun, hpost⟩ := hE ret hret js hs hpre
  have hp' : ∀ pc w, (p.withExit ret).fetch pc = some w → StepOK w := by
    intro pc w hf
    obtain ⟨seg, hm, _, hw⟩ := fetchIn_some hf
    exact hp w (List.mem_flatMap.mpr ⟨seg, hm, hw⟩)
  have hu : Untagged (p.withExit ret) := by
    refine ⟨by show ret < 2 ^ 56; have := hret.user; omega, fun pc w hf => ?_, fun pc st hst => ?_⟩
    · obtain ⟨seg, hm, hlt, _⟩ := fetchIn_some hf
      have := hcode seg hm; omega
    · have hm := List.mem_of_find?_eq_some hst
      have := List.find?_some hst
      simp only [decide_eq_true_eq] at this
      rw [← this]; exact hstub st hm
  have := run_agree (p.withExit ret) hp' hu fuel js s _ h hc hrun
  revert this
  cases hr : aslRun (p.withExit ret) fuel s with
  | returned s' => intro ⟨hrel, hcf⟩; exact ⟨fuel, s', js', hr, hrel, hcf, hpost⟩
  | stub _ _ _ => intro hf; cases hf
  | other => intro hf; cases hf

end JanusASL.Proofs

/-! ## `Add(x, y uint64) uint64` (artifacts/Add/Extracted.lean, examples/proofs/Add.lean) -/

namespace JanusASL.Examples.Add
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic JanusASL.Proofs

def segments : List Segment := [
  { name := "example.com/basic.Add", base := 0x930c0, words := [0x8b010000, 0xd65f03c0] } ]
def stubs : List Stub := []
def exitAddr : Nat := 0
def program : Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }
def entry : Nat := 0x930c0

/-- The shipped theorem, with its shipped proof. -/
theorem correctness (x y : BitVec 64) :
    Ensures program entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

theorem words_ok : ∀ w ∈ program.segments.flatMap (·.words), StepOK w := by
  simp only [program, segments, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro w (rfl | rfl)
  · exact stepOK_addSubShifted (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact stepOK_ret (by decide) (by decide) (by decide)

/-- **`Add` under Arm's ASL**: from any ASL state related to a Go call of `Add` with `x`, `y` in
`X0`, `X1` (under `LinuxEL0Config`), the ASL run returns to the caller with `x + y` in `X0`. -/
theorem correctness_asl (x y : BitVec 64) {ret : Nat} (hret : RetAddr program ret) {js : State}
    (hs : CallSetup (program.withExit ret) entry [x, y] js) {s : SState} (h : Rel js s) (hc : LinuxEL0Config s) :
    ∃ fuel s' js', aslRun (program.withExit ret) fuel s = .returned s' ∧ Rel js' s' ∧ LinuxEL0Config s' ∧
      ABIReturn js js' ∧ (js'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64 :=
  Ensures.toASL (correctness x y) words_ok (by simp [program, segments]) (by simp [program, stubs]) hret hs
    trivial h hc

end JanusASL.Examples.Add

/-! ## `Max(x, y uint64) uint64` (artifacts/Max/Extracted.lean, examples/proofs/Max.lean) -/

namespace JanusASL.Examples.Max
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic JanusASL.Proofs

def segments : List Segment := [
  { name := "example.com/basic.Max", base := 0x930d0, words := [0xeb00003f, 0x54000042, 0xd65f03c0, 0xaa0103e0, 0xd65f03c0] } ]
def stubs : List Stub := []
def exitAddr : Nat := 0
def program : Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }
def entry : Nat := 0x930d0

/-- The shipped theorem, with its shipped proof. -/
theorem correctness (x y : BitVec 64) :
    Ensures program entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = if y.toNat < x.toNat then x else y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals split <;> first | rfl | omega

theorem words_ok : ∀ w ∈ program.segments.flatMap (·.words), StepOK w := by
  simp only [program, segments, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro w (rfl | rfl | rfl | rfl | rfl)
  · exact stepOK_addSubShifted (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact stepOK_bcond (by decide) (by decide) (by decide)
  · exact stepOK_ret (by decide) (by decide) (by decide)
  · exact stepOK_logicalShifted (by decide) (by decide) (by decide)
  · exact stepOK_ret (by decide) (by decide) (by decide)

/-- **`Max` under Arm's ASL**: both sides of the compiled branch. -/
theorem correctness_asl (x y : BitVec 64) {ret : Nat} (hret : RetAddr program ret) {js : State}
    (hs : CallSetup (program.withExit ret) entry [x, y] js) {s : SState} (h : Rel js s) (hc : LinuxEL0Config s) :
    ∃ fuel s' js', aslRun (program.withExit ret) fuel s = .returned s' ∧ Rel js' s' ∧ LinuxEL0Config s' ∧
      ABIReturn js js' ∧ js'.regs 0 = if y.toNat < x.toNat then x else y :=
  Ensures.toASL (correctness x y) words_ok (by simp [program, segments]) (by simp [program, stubs]) hret hs
    trivial h hc

end JanusASL.Examples.Max

/-! ## `Mul64(x, y uint64) (hi, lo uint64)` (artifacts/Mul64/Extracted.lean, examples/proofs/Mul64.lean) -/

namespace JanusASL.Examples.Mul64
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic JanusASL.Proofs

def segments : List Segment := [
  { name := "example.com/basic.Mul64", base := 0x93100, words := [0x9b017c02, 0x9bc17c00, 0xaa0203e1, 0xd65f03c0] } ]
def stubs : List Stub := []
def exitAddr : Nat := 0
def program : Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }
def entry : Nat := 0x93100

/-- The shipped theorem, with its shipped proof. -/
theorem correctness (x y : BitVec 64) :
    Ensures program entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat * 2 ^ 64 + (s'.regs 1).toNat = x.toNat * y.toNat) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  janus_arith

theorem words_ok : ∀ w ∈ program.segments.flatMap (·.words), StepOK w := by
  simp only [program, segments, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro w (rfl | rfl | rfl | rfl)
  · exact stepOK_madd (by decide) (by decide)
  · exact stepOK_mulh (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact stepOK_logicalShifted (by decide) (by decide) (by decide)
  · exact stepOK_ret (by decide) (by decide) (by decide)

/-- **`Mul64` under Arm's ASL** (MUL, UMULH, MOV, RET): the 128-bit product. -/
theorem correctness_asl (x y : BitVec 64) {ret : Nat} (hret : RetAddr program ret) {js : State}
    (hs : CallSetup (program.withExit ret) entry [x, y] js) {s : SState} (h : Rel js s) (hc : LinuxEL0Config s) :
    ∃ fuel s' js', aslRun (program.withExit ret) fuel s = .returned s' ∧ Rel js' s' ∧ LinuxEL0Config s' ∧
      ABIReturn js js' ∧ (js'.regs 0).toNat * 2 ^ 64 + (js'.regs 1).toNat = x.toNat * y.toNat :=
  Ensures.toASL (correctness x y) words_ok (by simp [program, segments]) (by simp [program, stubs]) hret hs
    trivial h hc

end JanusASL.Examples.Mul64

/-! ## `Add128` (artifacts/Add128/Extracted.lean, examples/proofs/Add128.lean) -/

namespace JanusASL.Examples.Add128
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic JanusASL.Proofs

def segments : List Segment := [
  { name := "example.com/basic.Add128", base := 0x930f0, words := [0xab010061, 0xba000040, 0xd65f03c0] } ]
def stubs : List Stub := []
def exitAddr : Nat := 0
def program : Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }
def entry : Nat := 0x930f0

/-- The shipped theorem, with its shipped proof. -/
theorem correctness (xh xl yh yl : BitVec 64) :
    Ensures program entry [xh, xl, yh, yl] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat * 2 ^ 64 + (s'.regs 1).toNat =
        ((xh.toNat * 2 ^ 64 + xl.toNat) + (yh.toNat * 2 ^ 64 + yl.toNat)) % 2 ^ 128) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  janus_arith

theorem words_ok : ∀ w ∈ program.segments.flatMap (·.words), StepOK w := by
  simp only [program, segments, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro w (rfl | rfl | rfl)
  · exact stepOK_addSubShifted (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact stepOK_addSubCarry (by decide) (by decide) (by decide)
  · exact stepOK_ret (by decide) (by decide) (by decide)

/-- **`Add128` under Arm's ASL** (ADDS, ADC, RET): the carry chain. -/
theorem correctness_asl (xh xl yh yl : BitVec 64) {ret : Nat} (hret : RetAddr program ret) {js : State}
    (hs : CallSetup (program.withExit ret) entry [xh, xl, yh, yl] js) {s : SState} (h : Rel js s)
    (hc : LinuxEL0Config s) :
    ∃ fuel s' js', aslRun (program.withExit ret) fuel s = .returned s' ∧ Rel js' s' ∧ LinuxEL0Config s' ∧
      ABIReturn js js' ∧ (js'.regs 0).toNat * 2 ^ 64 + (js'.regs 1).toNat =
        ((xh.toNat * 2 ^ 64 + xl.toNat) + (yh.toNat * 2 ^ 64 + yl.toNat)) % 2 ^ 128 :=
  Ensures.toASL (correctness xh xl yh yl) words_ok (by simp [program, segments]) (by simp [program, stubs]) hret hs
    trivial h hc

end JanusASL.Examples.Add128
