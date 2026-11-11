import Janus.Amd64.Bridge
import Janus.Contracts.InternalCall
import Janus.Contracts.LiveAmd64
import Janus.Contracts.AllocAmd64
import Janus.Contracts.Rt

/-!
# Internal calls (amd64)

The amd64 twin of `InternalCall.lean`: `Program.onlySegments`, `Program.ofImpl`, `codeIn_restrict64`,
`codeIn_ofImpl64`, `Ensures.toSummaryIn` (the call state's return address `[RSP]` need only be
admissible for the callee's own program) and the contract transports `….of_codeIn` for
`…Contract64`.
-/

namespace Janus.Amd64

open Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.EqHashModel

namespace Program

def onlySegments (P : Program) (names : List String) : Program :=
  { P with segments := P.segments.filter fun seg => names.contains seg.name }

def ofImpl (P : Program) (impl : List Segment) : Program := { P with segments := impl }

end Program

/-- The code ranges of two segments do not overlap. -/
def Segment.Apart (a b : Segment) : Prop :=
  a.base + a.bytes.length ≤ b.base ∨ b.base + b.bytes.length ≤ a.base

instance : DecidableRel Segment.Apart := fun a b => by unfold Segment.Apart; infer_instance

namespace Program

theorem fetchIn_index {pc : Nat} {w : List Nat} :
    ∀ {segs : List Segment}, fetchIn segs pc = some w →
      ∃ seg ∈ segs, seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length
  | [], h => by simp [fetchIn] at h
  | seg :: rest, h => by
    simp only [fetchIn] at h
    by_cases hc : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length
    · exact ⟨seg, List.mem_cons_self .., hc⟩
    · rw [if_neg hc] at h
      obtain ⟨x, hx, r⟩ := fetchIn_index h
      exact ⟨x, List.mem_cons_of_mem _ hx, r⟩

theorem fetchIn_filter_append (f : Segment → Bool) (tail : List Segment) {pc : Nat} {w : List Nat} :
    ∀ {segs : List Segment}, (segs ++ tail).Pairwise Segment.Apart →
      fetchIn (segs.filter f ++ tail) pc = some w → fetchIn (segs ++ tail) pc = some w
  | [], _, h => by simpa using h
  | seg :: rest, hp, h => by
    have hp' := List.pairwise_cons.1 (show (seg :: (rest ++ tail)).Pairwise Segment.Apart from hp)
    cases hf : f seg
    · rw [List.filter_cons_of_neg (by simp [hf])] at h
      have ih := fetchIn_filter_append f tail hp'.2 h
      obtain ⟨x, hx, h1, h2⟩ := fetchIn_index ih
      have ha := hp'.1 x hx
      unfold Segment.Apart at ha
      rw [List.cons_append]
      simp only [fetchIn]
      rw [if_neg (by omega)]
      exact ih
    · rw [List.filter_cons_of_pos (by simp [hf]), List.cons_append] at h
      rw [List.cons_append]
      simp only [fetchIn] at h ⊢
      by_cases hc : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length
      · rw [if_pos hc] at h ⊢; exact h
      · rw [if_neg hc] at h ⊢; exact fetchIn_filter_append f tail hp'.2 h

end Program

theorem codeIn_restrict64 (P : Program) (names : List String) (impl : List Segment)
    (hd : (P.segments ++ impl).Pairwise Segment.Apart)
    (hs : ∀ seg ∈ P.segments ++ impl, ∀ i < seg.bytes.length,
      P.stubAt (seg.base + i) = none ∧ seg.base + i ≠ P.exitAddr) :
    CodeIn64 ((P.onlySegments names).link impl) (P.link impl) := by
  intro pc w hf
  have hf' : Program.fetchIn ((P.onlySegments names).link impl).segments pc = some w := hf
  have hbig : Program.fetchIn (P.segments ++ impl) pc = some w :=
    Program.fetchIn_filter_append (fun seg => names.contains seg.name) impl hd hf'
  obtain ⟨seg, hmem, h1, h2⟩ := Program.fetchIn_index hbig
  obtain ⟨h3, h4⟩ := hs seg hmem (pc - seg.base) (by omega)
  rw [show seg.base + (pc - seg.base) = pc by omega] at h3 h4
  exact ⟨hbig, h3, h4⟩

theorem codeIn_ofImpl64 (P Q : Program) (impl : List Segment)
    (hq : Q.stubs = P.stubs ∧ Q.exitAddr = P.exitAddr)
    (h : ∀ seg ∈ impl, ∀ i < seg.bytes.length, Q.fetch (seg.base + i) = none ∧
      P.stubAt (seg.base + i) = none ∧ seg.base + i ≠ P.exitAddr) :
    CodeIn64 (P.ofImpl impl) (Q.link impl) := by
  intro pc w hf
  have hf' : Program.fetchIn impl pc = some w := hf
  obtain ⟨seg, hmem, h1, h2⟩ := Program.fetchIn_index hf'
  obtain ⟨g1, g2, g3⟩ := h seg hmem (pc - seg.base) (by omega)
  rw [show seg.base + (pc - seg.base) = pc by omega] at g1 g2 g3
  refine ⟨?_, ?_, ?_⟩
  · show Program.fetchIn (Q.segments ++ impl) _ = _
    rw [fetchIn_append_none64 impl g1]; exact hf'
  · show Q.stubAt _ = none
    have : Q.stubAt pc = P.stubAt pc := by simp only [Program.stubAt, hq.1]
    rw [this]; exact g2
  · show pc ≠ Q.exitAddr
    rw [hq.2]; exact g3

/-- **The runtime's code does not overlap the extracted code** (amd64; the one premise on `impl` the
auditor allows, as `ImplApart Extracted.program impl`): see `Janus.ImplApart`. -/
def ImplApart (P : Program) (impl : List Segment) : Prop :=
  (P.segments ++ impl).Pairwise Segment.Apart ∧
    ∀ seg ∈ P.segments ++ impl, ∀ i < seg.bytes.length,
      P.stubAt (seg.base + i) = none ∧ seg.base + i ≠ P.exitAddr

instance (P : Program) (impl : List Segment) : Decidable (ImplApart P impl) := by
  unfold ImplApart; infer_instance

theorem Program.fetchIn_none_of_apart {segs : List Segment} {seg : Segment}
    (h : ∀ x ∈ segs, Segment.Apart x seg) {i : Nat} (hi : i < seg.bytes.length) :
    Program.fetchIn segs (seg.base + i) = none := by
  cases hf : Program.fetchIn segs (seg.base + i) with
  | none => rfl
  | some w =>
    obtain ⟨x, hx, h1, h2⟩ := Program.fetchIn_index hf
    have := h x hx
    unfold Segment.Apart at this
    omega

theorem codeIn_restrict_of_apart64 {P : Program} {impl : List Segment} (h : ImplApart P impl)
    (names : List String) : CodeIn64 ((P.onlySegments names).link impl) (P.link impl) :=
  codeIn_restrict64 P names impl h.1 h.2

theorem codeIn_ofImpl_of_apart64 {P : Program} {impl : List Segment} (h : ImplApart P impl) :
    CodeIn64 (P.ofImpl impl) (P.link impl) := by
  refine codeIn_ofImpl64 P P impl ⟨rfl, rfl⟩ fun seg hseg i hi => ?_
  obtain ⟨h1, h2⟩ := h.2 seg (List.mem_append_right _ hseg) i hi
  exact ⟨Program.fetchIn_none_of_apart (seg := seg)
    (fun x hx => (List.pairwise_append.1 h.1).2.2 x hx seg hseg) hi, h1, h2⟩

theorem codeIn_ofImpl_restrict_of_apart64 {P : Program} {impl : List Segment} (h : ImplApart P impl)
    (names : List String) : CodeIn64 (P.ofImpl impl) ((P.onlySegments names).link impl) := by
  refine codeIn_ofImpl64 P (P.onlySegments names) impl ⟨rfl, rfl⟩ fun seg hseg i hi => ?_
  obtain ⟨h1, h2⟩ := h.2 seg (List.mem_append_right _ hseg) i hi
  exact ⟨Program.fetchIn_none_of_apart (seg := seg)
    (fun x hx => (List.pairwise_append.1 h.1).2.2 x (List.mem_filter.1 hx).1 seg hseg) hi, h1, h2⟩

/-- The argument registers `argReg k, argReg (k+1), …` hold `args` (recursive form of `CallSetup.args`). -/
def ArgsFrom64 (s : State) (k : Nat) : List W64 → Prop
  | [] => True
  | a :: l => s.regs (argReg k) = a ∧ ArgsFrom64 s (k + 1) l

attribute [simp, janus64_exec, janus64_post] ArgsFrom64

attribute [simp, janus64_exec] numIntRegs

@[simp] theorem argReg_0 : argReg 0 = 0 := rfl
@[simp] theorem argReg_1 : argReg 1 = 3 := rfl
@[simp] theorem argReg_2 : argReg 2 = 1 := rfl
@[simp] theorem argReg_3 : argReg 3 = 7 := rfl
@[simp] theorem argReg_4 : argReg 4 = 6 := rfl

theorem ArgsFrom64.index {s : State} : ∀ {args : List W64} {k : Nat}, ArgsFrom64 s k args →
    ∀ i (hi : i < args.length), s.regs (argReg (k + i)) = args[i]
  | [], _, _, i, hi => absurd hi (by simp)
  | a :: l, k, h, 0, _ => by simpa using h.1
  | a :: l, k, h, i + 1, hi => by
    have := ArgsFrom64.index h.2 i (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- **An `Ensures` theorem about the callee's own code is a summary in the whole program** (amd64). -/
theorem Ensures.toSummaryIn {p0 P : Program} {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (h : Ensures p0 entry args pre post)
    (hx : p0.fetch p0.exitAddr = none) (hlen : args.length ≤ numIntRegs) (hc : CodeIn64 p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.mem.readLE (s.regs regSP).toNat 8) ∧ s.xmm xmmZero = 0 ∧
        ArgsFrom64 s 0 args ∧
        s.df = false ∧ pre s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧
        s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧ post s s') := by
  intro s hpc ⟨hret, hzero, hargs, hdf, hpre⟩
  have hsu : CallSetup (p0.withExit (s.mem.readLE (s.regs regSP).toNat 8)) entry args s :=
    ⟨hpc, rfl, hzero, hlen, fun i hi => by simpa using hargs.index i hi, hdf⟩
  obtain ⟨n, s1, hr, hp⟩ := h _ hret s hsu hpre
  have h2 := (show Reaches (p0.withExit (s.mem.readLE (s.regs regSP).toNat 8)) s
    (IsReturn fun s' => ABIReturn s s' ∧ post s s') from ⟨n, _, hr, hp⟩).toReachesRet hret hx
  rw [retAddrOf_eq]
  obtain ⟨k, s', hst, hr', hq⟩ := h2
  exact ⟨k, s', Steps.of_codeIn64 hc hst, hr', ⟨hq.1.sp, hq.1.fp, hq.1.g, hq.1.zero⟩, hq.2⟩

end Janus.Amd64

namespace Janus.Contracts

open Janus.Amd64 Janus.Contracts.EqHashModel

variable {p P : Janus.Amd64.Program}

theorem NewobjectLiveContract64.of_codeIn (hc : CodeIn64 p P) {a st : Nat} {R : RtInv}
    (h : NewobjectLiveContract64 p a st R) : NewobjectLiveContract64 P a st R :=
  fun L b => Summary.of_codeIn64 hc (h L b)
theorem MakesliceLiveContract64.of_codeIn (hc : CodeIn64 p P) {a st : Nat} {R : RtInv}
    (h : MakesliceLiveContract64 p a st R) : MakesliceLiveContract64 P a st R :=
  fun L b => Summary.of_codeIn64 hc (h L b)
theorem MallocgcLiveContract64.of_codeIn (hc : CodeIn64 p P) {a st : Nat} {R : RtInv}
    (h : MallocgcLiveContract64 p a st R) : MallocgcLiveContract64 P a st R :=
  fun L b => Summary.of_codeIn64 hc (h L b)
theorem WbLiveContract64.of_codeIn (hc : CodeIn64 p P) {a st n : Nat} {R : RtInv}
    (h : WbLiveContract64 p a st R n) : WbLiveContract64 P a st R n :=
  fun L b => Summary.of_codeIn64 hc (h L b)
theorem RtLiveContract64.of_codeIn (hc : CodeIn64 p P) {a st : Nat} {R : RtInv} {sp : RtSpec}
    {ls : LiveSpec} (h : RtLiveContract64 p a st R sp ls) : RtLiveContract64 P a st R sp ls :=
  fun L b => Summary.of_codeIn64 hc (h L b)
theorem MemmoveLive64.of_codeIn (hc : CodeIn64 p P) {a d : Nat} {R : RtInv}
    (h : MemmoveLive64 p a d R) : MemmoveLive64 P a d R :=
  fun L b => Summary.of_codeIn64 hc (h L b)
theorem MemmoveZeroLive64.of_codeIn (hc : CodeIn64 p P) {a d : Nat} {R : RtInv}
    (h : MemmoveZeroLive64 p a d R) : MemmoveZeroLive64 P a d R :=
  fun L b => Summary.of_codeIn64 hc (h L b)
theorem MemclrNoHeapPointersLive64.of_codeIn (hc : CodeIn64 p P) {a d : Nat} {R : RtInv}
    (h : MemclrNoHeapPointersLive64 p a d R) : MemclrNoHeapPointersLive64 P a d R :=
  fun L b => Summary.of_codeIn64 hc (h L b)

theorem NewobjectContract64.of_codeIn (hc : CodeIn64 p P) {a st : Nat} {rt : List (Nat × Nat)}
    {H : RtReady} (h : NewobjectContract64 p a rt st H) : NewobjectContract64 P a rt st H :=
  Summary.of_codeIn64 hc h
theorem MallocgcContract64.of_codeIn (hc : CodeIn64 p P) {a st : Nat} {rt : List (Nat × Nat)}
    {H : RtReady} (h : MallocgcContract64 p a rt st H) : MallocgcContract64 P a rt st H :=
  Summary.of_codeIn64 hc h
theorem MakesliceContract64.of_codeIn (hc : CodeIn64 p P) {a st : Nat} {rt : List (Nat × Nat)}
    {H : RtReady} (h : MakesliceContract64 p a rt st H) : MakesliceContract64 P a rt st H :=
  Summary.of_codeIn64 hc h
theorem RtContract64.of_codeIn (hc : CodeIn64 p P) {a st : Nat} {rt : List (Nat × Nat)} {H : RtReady}
    {sp : RtSpec} (h : RtContract64 p a rt st H sp) : RtContract64 P a rt st H sp :=
  Summary.of_codeIn64 hc h

end Janus.Contracts
