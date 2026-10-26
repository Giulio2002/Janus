import Janus.FFI

/-!
# The trusted contracts of `Janus.FFI` are satisfiable (arm64)

A contract whose `next` is empty for an allowed call makes every theorem about a run reaching
that call vacuous there. For each contract of `Janus/FFI.lean` this module shows that `next` is
non-empty (audit/round9 SAT row, which scans `Janus/FFI.lean` too):

* `topOfStack_satisfiable`, `cgoSpec_satisfiable`, `callbackSpec_satisfiable`: total;
* `cgoCall_satisfiable`: every allowed `cgocall` has a result, given what every real cgo call
  has: an admissible return address inside `asmcgocall`, and a system stack (`cgoCStack` bytes
  below a 16-aligned `SP`) disjoint from the Go memory;
* `cgoCallback_satisfiable`: `CgoCallback p Cin (fun _ => True)` is total when `Cin` is and an
  admissible return address exists.
-/

namespace Janus.FFI

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.CABI

/-- `TopOfStack T` is total. -/
theorem topOfStack_satisfiable (T : W64) : (TopOfStack T).Total := fun f s ⟨hf, _⟩ =>
  ⟨_, hf, s.flags, s.mem, rfl, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩


theorem cgoSpec_satisfiable (fn : Nat) (G : State → Prop) (E : State → Memory) :
    (CgoSpec fn G E).Total := fun f s ⟨hf, _⟩ =>
  ⟨_, hf, E s, ⟨s.regs, s.flags, s.vregs, s.tpidr, s.fpsr, rfl, rfl, rfl⟩,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

theorem callbackSpec_satisfiable (fn : Nat) (G : State → Prop) (E : State → Memory) :
    (CallbackSpec fn G E).Total := fun f s ⟨hf, _⟩ =>
  ⟨_, hf, E s, ⟨s.regs, s.flags, s.vregs, s.fpsr, rfl⟩, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

/-- The C call state `asmcgocall` makes from `s` on the system stack at `sp` (a new region). -/
def cgoEntryState (s : State) (ret sp : Nat) : State :=
  { s with pc := s.regs 0, regs := setReg (setReg s.regs 0 (s.regs 1)) 30 (BitVec.ofNat 64 ret),
           sp := BitVec.ofNat 64 sp,
           mem := { s.mem with regions := s.mem.regions ++ [⟨sp - cgoCStack, cgoCStack, true⟩] } }

theorem accessible_append_writable' {m : Memory} {rs : List Region} (hw : ∀ r ∈ rs, r.writable = true)
    {a k : Nat} {w : Bool} (h : m.accessible a k w = true) :
    ({ m with regions := m.regions ++ rs } : Memory).accessible a k w = true := by
  simp only [Memory.accessible, Bool.and_eq_true, List.any_append, List.all_append, Bool.or_eq_true,
    Bool.not_eq_true'] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨.inl h1, ?_⟩
  rcases h2 with h2 | h2
  · exact .inl h2
  · right; refine ⟨h2, ?_⟩
    simp only [List.all_eq_true]
    intro r hr; simp [hw r hr]

theorem cgoEntry_cgoEntryState {p : Program} {s : State} {ret sp : Nat} (hret : RetAddr p ret)
    (h16 : sp % 16 = 0) (hlo : cgoCStack ≤ sp) (hhi : sp ≤ 2 ^ 48)
    (hfree : ∀ r ∈ s.mem.regions, r.base + r.size ≤ sp - cgoCStack ∨ sp ≤ r.base) :
    CgoEntry p s (cgoEntryState s ret sp) ret where
  pc := rfl
  arg := by simp [cgoEntryState, setReg]
  lr := by simp [cgoEntryState, setReg, GoABI.regLR]
  retAddr := hret
  stack := by
    have hsp : (BitVec.ofNat 64 sp).toNat = sp := by simp; omega
    refine ⟨by simp [cgoEntryState, hsp, h16], by simp [cgoEntryState, hsp, hlo], by simp [cgoEntryState, hsp]; omega, ?_⟩
    simp only [cgoEntryState, hsp, Nat.add_zero, Memory.accessible, Bool.and_eq_true, List.any_append,
      List.all_append, List.any_cons, List.any_nil, List.all_cons, List.all_nil, Bool.or_eq_true,
      Bool.not_eq_true', Bool.and_true, Bool.or_false]
    refine ⟨.inr (by simp; omega), .inr ⟨?_, by simp⟩⟩
    simp only [List.all_eq_true]
    intro r hr
    rcases hfree r hr with h | h <;> simp <;> omega
  stackSep a n w h := by
    have hsp : (BitVec.ofNat 64 sp).toNat = sp := by simp; omega
    obtain ⟨⟨r, hr, h1, h2, -, -⟩, -⟩ := (Memory.accessible_iff s.mem a n w).1 h
    simp only [cgoEntryState, hsp, outside_cons, outside_nil, and_true]
    rcases hfree r hr with h3 | h3 <;> omega
  kept a n _ := Memory.readLE_congr fun _ _ => rfl
  keptAcc a n w h := accessible_append_writable' (by simp) h.1
  tpidr := rfl
  dczid := rfl
  fpcr := rfl

/-- The resumed Go state of a final C state `t'`. -/
def cgoResumeState (s t' : State) : State :=
  { s with pc := s.regs GoABI.regLR,
           mem := { bytes := fun a => if s.mem.accessible a 1 false then t'.mem.bytes a else s.mem.bytes a,
                    regions := s.mem.regions } }

theorem cgoResumed_cgoResumeState (s t' : State) : CgoResumed s t' (cgoResumeState s t') :=
  ⟨_, ⟨s.regs, s.flags, s.vregs, s.tpidr, s.fpsr, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl⟩

/-- Every allowed `cgocall` has a result, on a system stack disjoint from the Go memory. -/
theorem cgoCall_satisfiable {p : Program} {s : State} {ret sp : Nat} (hret : RetAddr p ret)
    (h16 : sp % 16 = 0) (hlo : cgoCStack ≤ sp) (hhi : sp ≤ 2 ^ 48)
    (hfree : ∀ r ∈ s.mem.regions, r.base + r.size ≤ sp - cgoCStack ∨ sp ≤ r.base)
    (hs : (CgoCall p).safe "runtime.cgocall" s) : ∃ s', (CgoCall p).next "runtime.cgocall" s s' := by
  obtain ⟨-, hrun⟩ := hs
  have he := cgoEntry_cgoEntryState (s := s) hret h16 hlo hhi hfree
  obtain ⟨t', hr, hc⟩ := (hrun _ ret 0 he).exists_runsTo (topOfStack_satisfiable 0)
  exact ⟨_, rfl, _, ret, 0, t', he, hr, hc, cgoResumed_cgoResumeState s t'⟩

/-! ## `cgocallback` -/


/-- A Go call state `cgocallback` may make from every C state: on a goroutine stack at `2^50`,
far from every C region (below `2^48`), with the C state's memory. -/
def cbState (s : State) (ret : Nat) : State :=
  { s with pc := BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 8) 8),
           regs := setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 16) 8)))
             30 (BitVec.ofNat 64 ret),
           sp := BitVec.ofNat 64 (2 ^ 50) }

theorem callbackEntry_cbState {p : Program} {ret : Nat} (s : State) (hret : RetAddr p ret) :
    CallbackEntry p s (cbState s ret) ret where
  pc := rfl
  arg := by simp [cbState, setReg]
  lr := by simp [cbState, setReg]
  retAddr := hret
  stackSep a n w h := by
    have := Memory.accessible_bound s.mem h
    simp only [outside_cons, outside_nil, and_true, cbState, cbGoStack]
    left; simp only [BitVec.toNat_ofNat]; omega
  kept a n _ := Memory.readLE_congr fun _ _ => rfl
  keptAcc _ _ _ h := h.1
  tpidr := rfl
  dczid := rfl
  fpcr := rfl

/-- The resumed C state of a final Go state `u'`. -/
def cbResumeState (s u' : State) : State :=
  { s with pc := s.regs GoABI.regLR,
           mem := { bytes := fun a => if s.mem.accessible a 1 false then u'.mem.bytes a else s.mem.bytes a,
                    regions := s.mem.regions } }

theorem cbResumed_cbResumeState (s u' : State) : CbResumed s u' (cbResumeState s u') :=
  ⟨_, ⟨s.regs, s.flags, s.vregs, s.fpsr, rfl⟩, rfl, fun _ _ => rfl⟩

theorem cgoCallback_satisfiable {p : Program} {Cin : Contract} {ret : Nat} (hC : Cin.Total)
    (hret : RetAddr p ret) : (CgoCallback p Cin (fun _ => True)).Total := by
  rintro f s ⟨hf, -, hgo⟩
  obtain ⟨u', hr, hab⟩ := (hgo _ ret (callbackEntry_cbState s hret) trivial).exists_runsTo hC
  exact ⟨_, hf, _, ret, u', callbackEntry_cbState s hret, trivial, hr, hab,
    cbResumed_cbResumeState s u'⟩


end Janus.FFI
