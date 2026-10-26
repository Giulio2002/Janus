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
* `cgoCallback_satisfiable`: every allowed call of `CgoCallback t p Cin (fun _ => True) k` has a
  result when `Cin` is total, an admissible return address exists and there is room for the
  goroutine stack (`k.size` bytes) and the `g` struct outside the C memory (`CbRoom`), for every
  stack size and readiness `k`; `cgoCallback_satisfiable_of` for a readiness `R` of the Go call
  state that holds at the witness entry.
-/

namespace Janus.FFI

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.CABI

/-- `TopOfStack T` is total. -/
theorem topOfStack_satisfiable (T : W64) : (TopOfStack T).Total := fun f s ⟨hf, _⟩ =>
  ⟨_, hf, s.flags, s.mem, rfl, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩


theorem cgoSpec_satisfiable (fn : Nat) (G : State → Prop) (E : State → Memory) :
    (CgoSpec fn G E).Total := fun f s ⟨hf, _⟩ =>
  ⟨_, hf, E s, ⟨s.regs, s.flags, s.vregs, s.tpidr, s.fpsr, s.excl, rfl, rfl, rfl⟩,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

theorem callbackSpec_satisfiable (t : TLSImage) (fn : Nat) (G : State → Prop) (E : State → Memory) :
    (CallbackSpec t fn G E).Total := fun f s ⟨hf, _⟩ =>
  ⟨_, hf, E s, ⟨s.regs, s.flags, s.vregs, s.fpsr, s.excl, rfl⟩, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

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
  ⟨_, ⟨s.regs, s.flags, s.vregs, s.tpidr, s.fpsr, s.excl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl⟩

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

/-- A Go call state `cgocallback` may make from the C state `s`, with `k` bytes of goroutine
stack below `SP = gsp` and the goroutine's `g` at `gp`: two new regions (the stack, writable;
the `g` struct, read-only), `stackguard0 = 0`, the TLS `g` slot pointing at `gp`. -/
def cbState (t : TLSImage) (k : Nat) (s : State) (ret gsp gp : Nat) : State :=
  { s with pc := BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 8) 8),
           regs := setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 16) 8)))
             30 (BitVec.ofNat 64 ret)) 28 (BitVec.ofNat 64 gp),
           sp := BitVec.ofNat 64 gsp,
           mem := { ((s.mem.writeLE (gp + 16) 8 0).writeLE (tlsGSlot t s.tpidr) 8 gp) with
             regions := s.mem.regions ++ [⟨gsp - k, k + 16, true⟩, ⟨gp, gStructSize, false⟩] } }

/-- What every real callback has: room for the goroutine stack and the `g` struct outside the C
memory, and a TLS `g` slot apart from the `g` struct's `stackguard0` word. -/
structure CbRoom (t : TLSImage) (k : Nat) (s : State) (gsp gp : Nat) : Prop where
  sp16 : gsp % 16 = 0
  lo : k ≤ gsp
  hi : gsp + 16 ≤ 2 ^ 48
  ghi : gp + gStructSize ≤ 2 ^ 48
  free : ∀ r ∈ s.mem.regions, (r.base + r.size ≤ gsp - k ∨ gsp + 16 ≤ r.base) ∧
    (r.base + r.size ≤ gp ∨ gp + gStructSize ≤ r.base)
  gapart : gp + gStructSize ≤ gsp - k ∨ gsp + 16 ≤ gp
  slot : tlsGSlot t s.tpidr + 8 ≤ gp + 16 ∨ gp + 24 ≤ tlsGSlot t s.tpidr

theorem readLE_cbState (t : TLSImage) (k : Nat) (s : State) (ret gsp gp a n : Nat) :
    (cbState t k s ret gsp gp).mem.readLE a n =
      ((s.mem.writeLE (gp + 16) 8 0).writeLE (tlsGSlot t s.tpidr) 8 gp).readLE a n :=
  readLE_congr fun _ _ => rfl

theorem callbackEntry_cbState {t : TLSImage} {p : Program} {k ret gsp gp : Nat} (s : State)
    (hret : RetAddr p ret) (h : CbRoom t k s gsp gp) :
    CallbackEntry t p k s (cbState t k s ret gsp gp) ret := by
  obtain ⟨h16, hlo, hhi, hghi, hfree, hgap, hslot⟩ := h
  have hsp : (BitVec.ofNat 64 gsp).toNat = gsp := by simp; omega
  have hgp : (BitVec.ofNat 64 gp).toNat = gp := by simp; unfold gStructSize at hghi; omega
  have h28 : (cbState t k s ret gsp gp).regs 28 = BitVec.ofNat 64 gp := by simp [cbState, setReg]
  have hspu : (cbState t k s ret gsp gp).sp = BitVec.ofNat 64 gsp := rfl
  -- a C-accessible range is apart from both new regions
  have hsep : ∀ a n w, s.mem.accessible a n w = true →
      (a + n ≤ gsp - k ∨ gsp + 16 ≤ a) ∧ (a + n ≤ gp ∨ gp + gStructSize ≤ a) := by
    intro a n w hacc
    obtain ⟨⟨r, hr, h1, h2, -, -⟩, -⟩ := (Memory.accessible_iff s.mem a n w).1 hacc
    obtain ⟨hf1, hf2⟩ := hfree r hr
    omega
  exact {
    pc := rfl
    arg := by simp [cbState, setReg]
    lr := by simp [cbState, setReg, GoABI.regLR]
    retAddr := hret
    gReg := by
      rw [h28, hgp]
      refine ⟨hghi, (Memory.accessible_iff _ _ _ _).2 ⟨⟨⟨gp, gStructSize, false⟩, ?_, by simp,
        by simp, by simpa using hghi, Or.inl rfl⟩, fun h => by cases h⟩⟩
      simp [cbState]
    gSep := fun a n w hacc => by
      rw [h28, hgp]; simp only [outside_cons, outside_nil, and_true]; exact (hsep a n w hacc).2
    tlsG := by
      rw [h28, hgp]
      rw [show (cbState t k s ret gsp gp).tpidr = s.tpidr from rfl, readLE_cbState,
        Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by unfold gStructSize at hghi; omega)
    goStack := by
      rw [hspu, hsp]
      refine ⟨h16, hlo, hhi, (Memory.accessible_iff _ _ _ _).2 ⟨⟨⟨gsp - k, k + 16, true⟩, ?_, by simp,
        by dsimp only; omega, by dsimp only; omega, Or.inr rfl⟩, fun _ r hr => ?_⟩⟩
      · simp [cbState]
      · simp only [cbState, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with hr | rfl | rfl
        · right; have := (hfree r hr).1; omega
        · left; rfl
        · right; simp only; unfold gStructSize at hgap ⊢; omega
    stackSep := fun a n w hacc => by
      rw [hspu, hsp]; simp only [outside_cons, outside_nil, and_true]; exact (hsep a n w hacc).1
    gOff := by
      rw [h28, hgp, hspu, hsp]; simp only [outside_cons, outside_nil, and_true]; exact hgap
    guard := by
      rw [h28, hgp, hspu, hsp]
      rw [readLE_cbState, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
      omega
    kept := fun a n ⟨hacc, hout⟩ => by
      rw [readLE_cbState]
      simp only [cbClobber, outside_cons, outside_nil, and_true] at hout
      have := (hsep a n false hacc).2
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by unfold gStructSize at this; omega)]
    keptAcc := fun a n w ⟨hacc, _⟩ => by
      obtain ⟨⟨r, hr, h1, h2, h3, h4⟩, hall⟩ := (Memory.accessible_iff s.mem a n w).1 hacc
      refine (Memory.accessible_iff _ _ _ _).2 ⟨⟨r, ?_, h1, h2, h3, h4⟩, fun hw r' hr' => ?_⟩
      · simp [cbState, hr]
      · simp only [cbState, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with hr' | rfl | rfl
        · exact hall hw r' hr'
        · left; rfl
        · right; have := (hsep a n w hacc).2; simp only; omega
    tpidr := rfl
    dczid := rfl
    fpcr := rfl }

/-- The resumed C state of a final Go state `u'`. -/
def cbResumeState (s u' : State) : State :=
  { s with pc := s.regs GoABI.regLR,
           mem := { bytes := fun a => if s.mem.accessible a 1 false then u'.mem.bytes a else s.mem.bytes a,
                    regions := s.mem.regions } }

theorem cbResumed_cbResumeState (t : TLSImage) (s u' : State) : CbResumed t s u' (cbResumeState s u') :=
  ⟨_, ⟨s.regs, s.flags, s.vregs, s.fpsr, s.excl, rfl⟩, rfl, fun _ _ => rfl⟩

/-- Every allowed `cgocallback` has a result (`CgoCallback t p Cin (fun _ => True) k`, for every
goroutine stack size and readiness `k`), when `Cin` is total, an admissible return address
exists and there is room for the goroutine stack and the `g` struct outside the C memory
(`CbRoom`; for `k.size ≤ 2^40` and C memory below `2^47`, `gsp = 2^47 + 2^41`, `gp = 2^47`
gives one). -/
theorem cgoCallback_satisfiable {t : TLSImage} {p : Program} {Cin : Contract} {k : CbStack}
    {ret gsp gp : Nat} {s : State} (hC : Cin.Total) (hret : RetAddr p ret)
    (hroom : CbRoom t k.size s gsp gp)
    (hs : (CgoCallback t p Cin (fun _ => True) k).safe "runtime.cgocallback.abi0" s) :
    ∃ s', (CgoCallback t p Cin (fun _ => True) k).next "runtime.cgocallback.abi0" s s' := by
  obtain ⟨hf, -, -, hgo⟩ := hs
  have he := callbackEntry_cbState (p := p) s hret hroom
  obtain ⟨u', hr, hab⟩ := (hgo _ ret he trivial).exists_runsTo hC
  exact ⟨_, hf, _, ret, u', he, trivial, hr, hab, cbResumed_cbResumeState t s u'⟩

/-- The same for a readiness predicate `R` of the Go call state that holds at the witness entry
(`cbState`): `CgoCallback t p Cin R k` has a result. -/
theorem cgoCallback_satisfiable_of {t : TLSImage} {p : Program} {Cin : Contract} {R : State → Prop}
    {k : CbStack} {ret gsp gp : Nat} {s : State} (hC : Cin.Total) (hret : RetAddr p ret)
    (hroom : CbRoom t k.size s gsp gp) (hR : R (cbState t k.size s ret gsp gp))
    (hs : (CgoCallback t p Cin R k).safe "runtime.cgocallback.abi0" s) :
    ∃ s', (CgoCallback t p Cin R k).next "runtime.cgocallback.abi0" s s' := by
  obtain ⟨hf, -, -, hgo⟩ := hs
  have he := callbackEntry_cbState (p := p) s hret hroom
  obtain ⟨u', hr, hab⟩ := (hgo _ ret he hR).exists_runsTo hC
  exact ⟨_, hf, _, ret, u', he, hR, hr, hab, cbResumed_cbResumeState t s u'⟩

end Janus.FFI
