import Janus.Tactic.Bridge
import Janus.Contracts.EqHashModel
import Janus.Contracts.Live
import Janus.Contracts.Alloc

/-!
# Internal calls: a callee proved on its own code, used inside the whole extraction (arm64)

`Ensures p entry args pre post` quantifies over return addresses `ret` with `RetAddr p ret`, which
includes `notCode`: `ret` is outside **every** segment of `p`. A call from one function of an
extraction to another returns to an address *inside* the extraction, so `Ensures.toSummary` cannot
serve it. What the proof of the callee actually needs is weaker: the run of the callee must never
reach `pc = ret` before it returns, i.e. `ret` is outside the code the callee *executes* (its own
segments and the runtime code the contracts stand for). So prove the callee about **its own code**:

* `P.onlySegments names` keeps the named segments of `P` (stubs, data, contracts unchanged);
  `(P.onlySegments ["callee"]).link impl` is the callee's program with the runtime stand-in `impl`;
* `Ensures ((P.onlySegments ["callee"]).link impl) entry …` is then a statement whose `RetAddr`
  holds for the caller's return site (outside the callee's segments);
* `Ensures.toSummaryIn` moves it to the whole program `P.link impl` as a `Summary` with the
  precondition `RetAddr p0 (X30) ∧ arguments ∧ pre`, for `janus_run … calls [S]` in the caller
  (`codeIn_restrict` discharges the side condition by `decide` on a concrete extraction);
* the runtime contracts are then hypotheses about a program with **no user code**,
  `Program.ofImpl P impl = {P with segments := impl}`: `codeIn_ofImpl` and the `….of_codeIn`
  lemmas move them to `(P.onlySegments names).link impl` (and to `P.link impl`). Moving them the other
  way would need that the contract code's runs stay inside `impl` (an arbitrary `impl` may jump into
  the extraction's code), which a plain `Summary` does not record: state the contract hypotheses
  of both theorems over `ofImpl` and transport them up.
-/

namespace Janus

open Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Contracts.EqHashModel

namespace Program

/-- `P` with only the named code segments (stubs, data, contracts, globals and the exit address are
`P`'s). -/
def onlySegments (P : Program) (names : List String) : Program :=
  { P with segments := P.segments.filter fun seg => names.contains seg.name }

/-- `P` with no user code, only the segments `impl` (the program a runtime contract is about). -/
def ofImpl (P : Program) (impl : List Segment) : Program := { P with segments := impl }

end Program

/-- The code ranges of two segments do not overlap. -/
def Segment.Apart (a b : Segment) : Prop :=
  a.base + 4 * a.words.length ≤ b.base ∨ b.base + 4 * b.words.length ≤ a.base

instance : DecidableRel Segment.Apart := fun a b => by unfold Segment.Apart; infer_instance

namespace Program

theorem fetchIn_index {pc w : Nat} :
    ∀ {segs : List Segment}, fetchIn segs pc = some w →
      ∃ seg ∈ segs, ∃ i, i < seg.words.length ∧ pc = seg.base + 4 * i
  | [], h => by simp at h
  | seg :: rest, h => by
    rw [fetchIn_cons] at h
    by_cases hc : seg.base ≤ pc ∧ (pc - seg.base) % 4 = 0
    · rw [if_pos hc] at h
      cases hw : seg.words[(pc - seg.base) / 4]? with
      | some w' =>
        refine ⟨seg, List.mem_cons_self .., (pc - seg.base) / 4,
          (List.getElem?_eq_some_iff.1 hw).1, by omega⟩
      | none =>
        rw [hw] at h
        obtain ⟨x, hx, r⟩ := fetchIn_index (show fetchIn rest pc = some w from h)
        exact ⟨x, List.mem_cons_of_mem _ hx, r⟩
    · rw [if_neg hc] at h
      obtain ⟨x, hx, r⟩ := fetchIn_index h
      exact ⟨x, List.mem_cons_of_mem _ hx, r⟩

theorem fetchIn_cons_congr {seg : Segment} {A B : List Segment} {pc w : Nat}
    (h : fetchIn (seg :: A) pc = some w) (hAB : fetchIn A pc = some w → fetchIn B pc = some w) :
    fetchIn (seg :: B) pc = some w := by
  rw [fetchIn_cons] at h ⊢
  by_cases hc : seg.base ≤ pc ∧ (pc - seg.base) % 4 = 0
  · rw [if_pos hc] at h ⊢
    cases hw : seg.words[(pc - seg.base) / 4]? with
    | some w' => rw [hw] at h; exact h
    | none => rw [hw] at h; exact hAB h
  · rw [if_neg hc] at h ⊢; exact hAB h

/-- Dropping segments from a disjoint code layout does not change what the kept ones fetch. -/
theorem fetchIn_filter_append (f : Segment → Bool) (tail : List Segment) {pc w : Nat} :
    ∀ {segs : List Segment}, (segs ++ tail).Pairwise Segment.Apart →
      fetchIn (segs.filter f ++ tail) pc = some w → fetchIn (segs ++ tail) pc = some w
  | [], _, h => by simpa using h
  | seg :: rest, hp, h => by
    have hp' := List.pairwise_cons.1 (show (seg :: (rest ++ tail)).Pairwise Segment.Apart from hp)
    cases hf : f seg
    · rw [List.filter_cons_of_neg (by simp [hf])] at h
      have ih := fetchIn_filter_append f tail hp'.2 h
      obtain ⟨x, hx, i, hi, hpc⟩ := fetchIn_index ih
      have ha := hp'.1 x hx
      unfold Segment.Apart at ha
      rw [List.cons_append, fetchIn_cons_miss (by omega)]
      exact ih
    · rw [List.filter_cons_of_pos (by simp [hf]), List.cons_append] at h
      rw [List.cons_append]
      exact fetchIn_cons_congr h (fetchIn_filter_append f tail hp'.2)

end Program

/-- **The callee's own code is the whole program's code**: `(P.onlySegments names).link impl` fetches
what `P.link impl` fetches wherever it has code, and `P.link impl` has no stub and not its exit address
there. The side conditions are decidable on a concrete extraction. -/
theorem codeIn_restrict (P : Program) (names : List String) (impl : List Segment)
    (hd : (P.segments ++ impl).Pairwise Segment.Apart)
    (hs : ∀ seg ∈ P.segments ++ impl, ∀ i < seg.words.length,
      P.stubAt (seg.base + 4 * i) = none ∧ seg.base + 4 * i ≠ P.exitAddr) :
    CodeIn ((P.onlySegments names).link impl) (P.link impl) := by
  intro pc w hf
  have hf' : Program.fetchIn ((P.onlySegments names).link impl).segments pc = some w := hf
  have hbig : Program.fetchIn (P.segments ++ impl) pc = some w :=
    Program.fetchIn_filter_append (fun seg => names.contains seg.name) impl hd hf'
  obtain ⟨seg, hmem, i, hi, rfl⟩ := Program.fetchIn_index hbig
  obtain ⟨h1, h2⟩ := hs seg hmem i hi
  exact ⟨hbig, h1, h2⟩

/-- **The runtime's own code is in every program that links it**: `Program.ofImpl P impl` fetches what
`Q.link impl` fetches, when `Q` has no code, stub or exit address at `impl`'s words. -/
theorem codeIn_ofImpl (P Q : Program) (impl : List Segment)
    (hq : Q.stubs = P.stubs ∧ Q.exitAddr = P.exitAddr)
    (h : ∀ seg ∈ impl, ∀ i < seg.words.length, Q.fetch (seg.base + 4 * i) = none ∧
      P.stubAt (seg.base + 4 * i) = none ∧ seg.base + 4 * i ≠ P.exitAddr) :
    CodeIn (P.ofImpl impl) (Q.link impl) := by
  intro pc w hf
  have hf' : Program.fetchIn impl pc = some w := hf
  obtain ⟨seg, hmem, i, hi, rfl⟩ := Program.fetchIn_index hf'
  obtain ⟨h1, h2, h3⟩ := h seg hmem i hi
  refine ⟨?_, ?_, ?_⟩
  · show Program.fetchIn (Q.segments ++ impl) _ = _
    rw [fetchIn_append_none impl h1]; exact hf'
  · show Q.stubAt _ = none
    have : Q.stubAt (seg.base + 4 * i) = P.stubAt (seg.base + 4 * i) := by
      simp only [Program.stubAt_eq, hq.1]
    rw [this]; exact h2
  · show seg.base + 4 * i ≠ Q.exitAddr
    rw [hq.2]; exact h3

/-- The argument registers `X(k), X(k+1), …` hold `args` (a recursive form of `CallSetup.args` that
`simp` evaluates on a literal list). -/
def ArgsFrom (s : State) (k : Nat) : List W64 → Prop
  | [] => True
  | a :: l => s.regs k = a ∧ ArgsFrom s (k + 1) l

attribute [simp, janus_exec, janus_post] ArgsFrom

theorem ArgsFrom.index {s : State} : ∀ {args : List W64} {k : Nat}, ArgsFrom s k args →
    ∀ i (hi : i < args.length), s.regs (k + i) = args[i]
  | [], _, _, i, hi => absurd hi (by simp)
  | a :: l, k, h, 0, _ => by simpa using h.1
  | a :: l, k, h, i + 1, hi => by
    have := ArgsFrom.index h.2 i (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- **An `Ensures` theorem about the callee's own code is a summary in the whole program.**
`p0` is the callee's program (`(P.onlySegments names).link impl`), `P` the whole one with the same
code (`hc : CodeIn p0 P`, `codeIn_restrict`). The precondition is for a call from inside `P`: the
return address in `X30` need only be admissible for `p0` (outside the callee's code, aligned, below
`2^48`, no stub), not for `P`. -/
theorem Ensures.toSummaryIn {p0 P : Program} {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (h : Ensures p0 entry args pre post)
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.regs regLR).toNat ∧ ArgsFrom s 0 args ∧ pre s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 18 = s.regs 18) ∧ post s s') := by
  intro s hpc ⟨hret, hargs, hpre⟩
  have hlr : ∀ x : W64, BitVec.ofNat 64 x.toNat = x := fun x => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt
  have hsu : CallSetup (p0.withExit (s.regs regLR).toNat) entry args s :=
    ⟨hpc, by simp only [Program.exitAddr_withExit]; exact (hlr _).symm,
      fun i hi => by simpa using hargs.index i hi⟩
  have h2 := (reaches_of_returns (h _ hret s hsu hpre)).toReachesRet hret hx
  rw [hlr] at h2
  obtain ⟨k, s', hst, hr, hq⟩ := h2
  exact ⟨k, s', Steps.of_codeIn hc hst, hr, ⟨hq.1.sp, hq.1.g, hq.1.fp, hq.1.platform⟩, hq.2⟩


end Janus

/-! ### Runtime contracts move to every program that contains the same code

A contract is a `Summary` (or `∀ L b, Summary`) about the runtime function's code at its address;
`Summary.of_codeIn` moves it to any program that has that code (`CodeIn`). -/

namespace Janus.Contracts

open Janus.Arm64 Janus.Tactic Janus.Contracts.EqHashModel

variable {p P : Program}

theorem NewobjectLiveContract.of_codeIn (hc : CodeIn p P) {a st : Nat} {R : RtInv}
    (h : NewobjectLiveContract p a st R) : NewobjectLiveContract P a st R :=
  fun L b => Summary.of_codeIn hc (h L b)
theorem MakesliceLiveContract.of_codeIn (hc : CodeIn p P) {a st : Nat} {R : RtInv}
    (h : MakesliceLiveContract p a st R) : MakesliceLiveContract P a st R :=
  fun L b => Summary.of_codeIn hc (h L b)
theorem MallocgcLiveContract.of_codeIn (hc : CodeIn p P) {a st : Nat} {R : RtInv}
    (h : MallocgcLiveContract p a st R) : MallocgcLiveContract P a st R :=
  fun L b => Summary.of_codeIn hc (h L b)
theorem WbLiveContract.of_codeIn (hc : CodeIn p P) {a st n : Nat} {R : RtInv}
    (h : WbLiveContract p a st R n) : WbLiveContract P a st R n :=
  fun L b => Summary.of_codeIn hc (h L b)
theorem RtLiveContract.of_codeIn (hc : CodeIn p P) {a st : Nat} {R : RtInv} {sp : RtSpec} {ls : LiveSpec}
    (h : RtLiveContract p a st R sp ls) : RtLiveContract P a st R sp ls :=
  fun L b => Summary.of_codeIn hc (h L b)
theorem MemmoveLive.of_codeIn (hc : CodeIn p P) {a d : Nat} {R : RtInv}
    (h : MemmoveLive p a d R) : MemmoveLive P a d R :=
  fun L b => Summary.of_codeIn hc (h L b)
theorem MemclrNoHeapPointersLive.of_codeIn (hc : CodeIn p P) {a d : Nat} {R : RtInv}
    (h : MemclrNoHeapPointersLive p a d R) : MemclrNoHeapPointersLive P a d R :=
  fun L b => Summary.of_codeIn hc (h L b)
theorem MemclrHasPointersLive.of_codeIn (hc : CodeIn p P) {a d : Nat} {R : RtInv}
    (h : MemclrHasPointersLive p a d R) : MemclrHasPointersLive P a d R :=
  fun L b => Summary.of_codeIn hc (h L b)
theorem TypedMemmoveLive.of_codeIn (hc : CodeIn p P) {a d : Nat} {R : RtInv}
    (h : TypedMemmoveLive p a d R) : TypedMemmoveLive P a d R :=
  fun L b => Summary.of_codeIn hc (h L b)
theorem TypedMemclrLive.of_codeIn (hc : CodeIn p P) {a d : Nat} {R : RtInv}
    (h : TypedMemclrLive p a d R) : TypedMemclrLive P a d R :=
  fun L b => Summary.of_codeIn hc (h L b)

theorem NewobjectContract.of_codeIn (hc : CodeIn p P) {a st : Nat} {rt : List (Nat × Nat)} {H : RtReady}
    (h : NewobjectContract p a rt st H) : NewobjectContract P a rt st H := Summary.of_codeIn hc h
theorem MallocgcContract.of_codeIn (hc : CodeIn p P) {a st : Nat} {rt : List (Nat × Nat)} {H : RtReady}
    (h : MallocgcContract p a rt st H) : MallocgcContract P a rt st H := Summary.of_codeIn hc h
theorem MakesliceContract.of_codeIn (hc : CodeIn p P) {a st : Nat} {rt : List (Nat × Nat)} {H : RtReady}
    (h : MakesliceContract p a rt st H) : MakesliceContract P a rt st H := Summary.of_codeIn hc h
theorem GrowsliceContract.of_codeIn (hc : CodeIn p P) {a st : Nat} {rt : List (Nat × Nat)} {H : RtReady}
    (h : GrowsliceContract p a rt st H) : GrowsliceContract P a rt st H := Summary.of_codeIn hc h
theorem RtContract.of_codeIn (hc : CodeIn p P) {a st : Nat} {rt : List (Nat × Nat)} {H : RtReady}
    {sp : RtSpec} (h : RtContract p a rt st H sp) : RtContract P a rt st H sp := Summary.of_codeIn hc h

end Janus.Contracts
