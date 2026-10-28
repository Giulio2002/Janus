import Janus

/-!
# Programs with the same code in a different order (arm64)

The print examples' proofs run the runtime's print functions from one program, `PrintCode.program`
(`PrintProofs.Arm64.Code`): the code of every function the four examples call, as the extractor
copies it from the binary. Each example's own `Extracted.program` holds the same functions (it is
extracted with the other examples' entry points as `--targets`), only in the order its entry point
reaches them. Code is found by address, so the order is immaterial when the segments do not
overlap: this module proves that, and what follows for the specifications the proofs use
(`Summary`, `ReturnsK`, `RetAddr`, `DataLoaded`), so that a theorem proved about `PrintCode.program`
transports to `Extracted.program`.

Nothing here is trusted: the lemmas are about the framework's definitions, checked by the kernel
like any proof.
-/

deriving instance DecidableEq for Janus.Segment
deriving instance DecidableEq for Janus.Stub
deriving instance DecidableEq for Janus.DataSegment

namespace Janus.Program

open Janus.Tactic Janus.Arm64 Janus.Kernel

/-- Two segments do not overlap. -/
def SegDisj (a b : Segment) : Prop :=
  a.base + 4 * a.words.length ≤ b.base ∨ b.base + 4 * b.words.length ≤ a.base

instance (a b : Segment) : Decidable (SegDisj a b) := by unfold SegDisj; infer_instance

theorem fetchIn_single {seg : Segment} {pc w : Nat} (h : fetchIn [seg] pc = some w) :
    seg.base ≤ pc ∧ pc < seg.base + 4 * seg.words.length := by
  unfold fetchIn at h
  split at h
  · rename_i hc
    split at h
    · rename_i w' hw
      have := (List.getElem?_eq_some_iff.mp hw).1
      omega
    · simp [fetchIn] at h
  · simp [fetchIn] at h

theorem fetchIn_cons' (seg : Segment) (rest : List Segment) (pc : Nat) :
    fetchIn (seg :: rest) pc = match fetchIn [seg] pc with
      | some w => some w
      | none => fetchIn rest pc := by
  by_cases hc : seg.base ≤ pc ∧ (pc - seg.base) % 4 = 0
  · cases hw : seg.words[(pc - seg.base) / 4]? with
    | some w => simp [fetchIn, hc, hw]
    | none => simp [fetchIn, hc, hw]
  · simp [fetchIn, hc]

theorem fetchIn_some {l : List Segment} {pc w : Nat} (h : fetchIn l pc = some w) :
    ∃ seg ∈ l, fetchIn [seg] pc = some w := by
  induction l with
  | nil => simp [fetchIn] at h
  | cons seg rest ih =>
    rw [fetchIn_cons'] at h
    split at h
    · rename_i w' hw; cases h; exact ⟨seg, by simp, hw⟩
    · obtain ⟨s, hs, h'⟩ := ih h; exact ⟨s, by simp [hs], h'⟩

theorem fetchIn_none {l : List Segment} {pc : Nat} :
    fetchIn l pc = none ↔ ∀ seg ∈ l, fetchIn [seg] pc = none := by
  induction l with
  | nil => simp [fetchIn]
  | cons seg rest ih =>
    rw [fetchIn_cons']
    constructor
    · intro h seg' hs'
      cases hh : fetchIn [seg] pc with
      | some w => rw [hh] at h; simp at h
      | none =>
        rw [hh] at h
        simp only at h
        rcases List.mem_cons.mp hs' with rfl | hr
        · exact hh
        · exact ih.mp h seg' hr
    · intro h
      have h1 := h seg (by simp)
      rw [h1]
      exact ih.mpr fun s hs => h s (by simp [hs])

theorem pairwise_mem_ne {R : α → α → Prop} {l : List α} (h : l.Pairwise R) {a b : α} (ha : a ∈ l)
    (hb : b ∈ l) (hne : a ≠ b) : R a b ∨ R b a := by
  induction h with
  | nil => simp at ha
  | cons hx _ ih =>
    rename_i x xs
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact Or.inl (hx _ hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (hx _ ha')
      · exact ih ha' hb'

/-- The word found is the same in any order of non-overlapping segments. -/
theorem fetchIn_perm {l l' : List Segment} (hp : l.Perm l') (hd : l.Pairwise SegDisj) (pc : Nat) :
    fetchIn l pc = fetchIn l' pc := by
  have key : ∀ {l l' : List Segment}, l.Perm l' → l.Pairwise SegDisj → ∀ {w : Nat},
      fetchIn l pc = some w → fetchIn l' pc = some w := by
    intro l l' hp hd w h
    obtain ⟨seg, hs, h1⟩ := fetchIn_some h
    have hs' : seg ∈ l' := hp.mem_iff.mp hs
    cases h' : fetchIn l' pc with
    | none => exact absurd (fetchIn_none.mp h' seg hs') (by rw [h1]; simp)
    | some w' =>
      obtain ⟨seg', hs2, h2⟩ := fetchIn_some h'
      have hs2' : seg' ∈ l := hp.symm.mem_iff.mp hs2
      by_cases he : seg = seg'
      · subst he; rw [h1] at h2; cases h2; rfl
      · have a1 := fetchIn_single h1
        have a2 := fetchIn_single h2
        rcases pairwise_mem_ne hd hs hs2' he with hh | hh <;> (unfold SegDisj at hh; omega)
  cases h : fetchIn l pc with
  | some w => exact (key hp hd h).symm
  | none =>
    cases h' : fetchIn l' pc with
    | none => rfl
    | some w =>
      have := key hp.symm (hp.pairwise_iff (fun {a b} h => by unfold SegDisj at *; omega) |>.mp hd) h'
      rw [h] at this; cases this

theorem fetchIn_append_eq (l₁ l₂ : List Segment) (pc : Nat) :
    fetchIn (l₁ ++ l₂) pc = match fetchIn l₁ pc with
      | some w => some w
      | none => fetchIn l₂ pc := by
  induction l₁ with
  | nil => simp [fetchIn]
  | cons seg rest ih =>
    rw [List.cons_append, fetchIn_cons' seg (rest ++ l₂) pc, fetchIn_cons' seg rest pc]
    cases fetchIn [seg] pc with
    | some w => rfl
    | none => exact ih

/-! ## Programs that behave alike -/

/-- `p` and `q` fetch, stub and exit alike: every run, summary and kernel run of one is one of the
other. -/
structure Sim (p q : Program) : Prop where
  fetch : ∀ pc, p.fetch pc = q.fetch pc
  stub : ∀ pc, p.stubAt pc = q.stubAt pc
  exit : p.exitAddr = q.exitAddr

theorem Sim.symm {p q : Program} (h : Sim p q) : Sim q p :=
  ⟨fun pc => (h.fetch pc).symm, fun pc => (h.stub pc).symm, h.exit.symm⟩

theorem Sim.withExit {p q : Program} (h : Sim p q) (ret : Nat) : Sim (p.withExit ret) (q.withExit ret) :=
  ⟨h.fetch, h.stub, rfl⟩

theorem Sim.steps {p q : Program} (h : Sim p q) {s s' : State} {n : Nat}
    (hs : Program.Steps p s n s') : Program.Steps q s n s' := by
  induction hs with
  | refl => exact .refl _
  | step hx hst hf he _ ih =>
    exact .step (by rw [← h.exit]; exact hx) (by rw [← h.stub]; exact hst) (by rw [← h.fetch]; exact hf) he ih

theorem Sim.reachesRet {p q : Program} (h : Sim p q) {ret : W64} {s : State} {Q : State → Prop}
    (hr : ReachesRet p ret s Q) : ReachesRet q ret s Q := by
  obtain ⟨k, s', hs, hp, hq⟩ := hr
  exact ⟨k, s', h.steps hs, hp, hq⟩

theorem Sim.summary {p q : Program} (h : Sim p q) {a : Nat} {pre : State → Prop}
    {post : State → State → Prop} (hs : Summary p a pre post) : Summary q a pre post :=
  fun s hpc hpre => h.reachesRet (hs s hpc hpre)

theorem Sim.returnsK {p q : Program} (h : Sim p q) {E : KEnv} {post : State → Kern → Prop}
    {onExit : Nat → Kern → Prop} {s : State} {k : Kern} (hr : ReturnsK p E post onExit s k) :
    ReturnsK q E post onExit s k := by
  induction hr with
  | exit hx hp => exact .exit (by rw [← h.exit]; exact hx) hp
  | step hx hs hf hst _ ih =>
    exact .step (by rw [← h.exit]; exact hx) (by rw [← h.stub]; exact hs) (by rw [← h.fetch]; exact hf) hst ih
  | sys hx hs hk hsite hsafe _ ih =>
    refine .sys (by rw [← h.exit]; exact hx) (by rw [← h.stub]; exact hs) hk ?_ hsafe ih
    simpa only [siteOf, h.fetch] using hsite
  | halt hx hs hk hsite he hp =>
    refine .halt (by rw [← h.exit]; exact hx) (by rw [← h.stub]; exact hs) hk ?_ he hp
    simpa only [siteOf, h.fetch] using hsite

/-! ## Equal code in a different order -/

/-- Same code (the segments, up to order, with no two overlapping), stubs, exit address, data and
contracts. -/
structure Equiv (p q : Program) : Prop where
  segs : p.segments.Perm q.segments
  disj : p.segments.Pairwise SegDisj
  stubs : p.stubs = q.stubs
  exit : p.exitAddr = q.exitAddr
  data : p.data = q.data
  contracts : p.contracts = q.contracts

theorem Equiv.symm {p q : Program} (h : Equiv p q) : Equiv q p where
  segs := h.segs.symm
  disj := h.segs.pairwise_iff (fun {a b} hab => by unfold SegDisj at *; omega) |>.mp h.disj
  stubs := h.stubs.symm
  exit := h.exit.symm
  data := h.data.symm
  contracts := h.contracts.symm

/-- With any further code linked in, `p` and `q` behave alike. -/
theorem Equiv.sim {p q : Program} (h : Equiv p q) (impl : List Segment) : Sim (p.link impl) (q.link impl) where
  fetch pc := by
    show fetchIn (p.segments ++ impl) pc = fetchIn (q.segments ++ impl) pc
    rw [fetchIn_append_eq, fetchIn_append_eq, fetchIn_perm h.segs h.disj]
  stub pc := by show p.stubAt pc = q.stubAt pc; simp only [stubAt, h.stubs]
  exit := h.exit

theorem Equiv.contractAddr {p q : Program} (h : Equiv p q) (name : String) :
    p.contractAddr name = q.contractAddr name := by
  simp only [Program.contractAddr, h.contracts]

theorem Equiv.retAddr {p q : Program} (h : Equiv p q) (impl : List Segment) {ret : Nat}
    (hr : GoABI.RetAddr (p.link impl) ret) : GoABI.RetAddr (q.link impl) ret where
  aligned := hr.aligned
  user := hr.user
  notCode seg hs := by
    have : seg ∈ p.segments ++ impl := by
      have hs' : seg ∈ q.segments ++ impl := hs
      rw [List.mem_append] at hs' ⊢
      rcases hs' with hs' | hs'
      · exact Or.inl (h.segs.symm.mem_iff.mp hs')
      · exact Or.inr hs'
    exact hr.notCode seg this
  notStub st hs := hr.notStub st (by rw [stubs_link, h.stubs]; exact hs)

theorem Equiv.dataLoaded {p q : Program} (h : Equiv p q) {m : Memory} (hd : p.DataLoaded m) :
    q.DataLoaded m := by unfold Program.DataLoaded at *; rw [← h.data]; exact hd

end Janus.Program

namespace Janus.Kernel

open Janus Janus.Program

/-- A function contract of `q` (linked with `impl`) is one of `p` when `p` and `q` have the same
code, under a stronger precondition and a weaker postcondition. -/
theorem EnsuresK.of_equiv {p q : Program} (h : Equiv p q) (impl : List Segment) {E : KEnv}
    {entry : Nat} {args : List Arm64.W64} {pre pre' : Arm64.State → Kern → Prop}
    {post post' : Arm64.State → Kern → Arm64.State → Kern → Prop}
    (hq : EnsuresK (q.link impl) E entry args pre post)
    (hpre : ∀ s k, pre' s k → pre s k) (hpost : ∀ s k s' k', post s k s' k' → post' s k s' k') :
    EnsuresK (p.link impl) E entry args pre' post' := by
  intro ret hret s k hs hp
  have hsim := (h.sim impl).withExit ret
  have hs' : GoABI.CallSetup ((q.link impl).withExit ret) entry args s := ⟨hs.pc, hs.lr, hs.args⟩
  have := hsim.symm.returnsK ((hq ret (h.retAddr impl hret) s k hs' (hpre s k hp)))
  exact this.mono (fun s' k' ⟨a, b⟩ => ⟨a, hpost _ _ _ _ b⟩) (fun _ _ x => x)

end Janus.Kernel

namespace Janus.Print

open Janus Janus.Program

/-- The runtime contracts of `q` are those of `p`, for equivalent programs (linked with the same
code, at the same contract addresses). -/
theorem Lock2Contract.of_equiv {p q : Program} (h : Equiv p q) (impl : List Segment)
    (rt : List (Nat × Nat)) (stack : Nat)
    (hl : Lock2Contract (p.link impl) (p.contractAddr "runtime.lock2") rt stack) :
    Lock2Contract (q.link impl) (q.contractAddr "runtime.lock2") rt stack := by
  rw [← h.contractAddr]; exact (h.sim impl).summary hl

theorem Unlock2Contract.of_equiv {p q : Program} (h : Equiv p q) (impl : List Segment)
    (rt : List (Nat × Nat)) (stack : Nat)
    (hl : Unlock2Contract (p.link impl) (p.contractAddr "runtime.unlock2") rt stack) :
    Unlock2Contract (q.link impl) (q.contractAddr "runtime.unlock2") rt stack := by
  rw [← h.contractAddr]; exact (h.sim impl).summary hl

theorem MemmoveContract.of_equiv {p q : Program} (h : Equiv p q) (impl : List Segment)
    (hl : MemmoveContract (p.link impl) (p.contractAddr "runtime.memmove")) :
    MemmoveContract (q.link impl) (q.contractAddr "runtime.memmove") := by
  rw [← h.contractAddr]; exact (h.sim impl).summary hl

theorem DataOutside.of_equiv {p q : Program} (h : Equiv p q) {rt : List (Nat × Nat)}
    (hd : DataOutside p rt) : DataOutside q rt := by
  unfold DataOutside at *; rw [← h.data]; exact hd

end Janus.Print
