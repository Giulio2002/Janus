import Janus.Amd64.FFI
import Janus.FFISat

/-!
# The trusted contracts of `Janus.Amd64.FFI` are satisfiable (amd64)

As `Janus.FFISat`: `topOfStack_satisfiable`, `cgoSpec_satisfiable`, `callbackSpec_satisfiable`
(total), `cgoCall_satisfiable` (every allowed `cgocall` has a result, given an admissible return
address, a system stack disjoint from the Go memory, and the Go state's TLS `g` slot, `TlsG`, as
every real cgo call has), `cgoCallback_satisfiable` (given a goroutine stack disjoint from the C
memory).
-/

namespace Janus.Amd64.FFI

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Amd64.CABI

theorem topOfStack_satisfiable (T : W64) : (TopOfStack T).Total := fun f s ⟨hf, _⟩ =>
  ⟨_, hf, s.flags, rfl⟩


/-- The resumed Go state: `GoResume` with memory `m` and `g` stored back in the TLS slot. -/
def goResumeState (s : State) (m : Memory) : State :=
  { s with regs := fun i => if i = 4 then s.regs 4 + 8 else s.regs i, rip := retAddrOf s,
           xmm := fun i => if i = 15 then 0 else s.xmm i, df := false,
           mem := m.writeLE (s.fsBase.toNat - 8) 8 (s.regs regG).toNat }

theorem goResume_goResumeState {s : State} {m : Memory} (ht : TlsG s)
    (hreg : m.regions = s.mem.regions) :
    GoResume s (goResumeState s m) (m.writeLE (s.fsBase.toNat - 8) 8 (s.regs regG).toNat) := by
  refine ⟨_, s.flags, _, s.ymmHi, s.fsBase, s.mxcsr, rfl, by simp, by simp [GoABI.regFP], by simp [regG],
    by simp [xmmZero], ⟨ht.base, ?_, ?_⟩, rfl⟩
  · simp only [goResumeState, Janus.Arm64.Memory.accessible_writeLE]
    rw [Janus.Arm64.Memory.accessible_congr hreg]; exact ht.readable
  · simp only [goResumeState]
    rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (s.regs regG).isLt]
    simp [regG]

theorem frame_tlsWrite {s : State} {m : Memory} (v : Nat) (h8 : 8 ≤ s.fsBase.toNat) :
    MemFrame m (m.writeLE (s.fsBase.toNat - 8) 8 v) (cgoClobber s) := by
  refine ⟨fun a n ho => ?_, fun _ _ _ => rfl⟩
  simp only [cgoClobber, outside_cons, outside_nil, and_true] at ho
  exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := m) v (by omega)

/-- `CgoSpec` has a result for every allowed call from a state with the TLS `g` slot, when the
assumed memory `E s` has the regions of `s` (as every use of it states). -/
theorem cgoSpec_satisfiable (fn : Nat) (G : State → Prop) (E : State → Memory)
    (hE : ∀ s, (E s).regions = s.mem.regions) {s : State} (ht : TlsG s)
    (hs : (CgoSpec fn G E).safe "runtime.cgocall" s) : ∃ s', (CgoSpec fn G E).next "runtime.cgocall" s s' :=
  ⟨_, hs.1, _, goResume_goResumeState ht (hE s), frame_tlsWrite _ ht.base.1⟩


/-- The C call state `asmcgocall` makes from `s` on the system stack at `sp` (`RSP`, `≡ 8 mod 16`,
the return address at `[RSP]`, a new region `[sp − cgoCStack, sp + 8)`). -/
def cgoEntryState (s : State) (ret sp : Nat) : State :=
  { s with rip := s.regs 0,
           regs := fun i => if i = 7 then s.regs 3 else if i = 4 then BitVec.ofNat 64 sp else s.regs i,
           mem := { bytes := (s.mem.writeLE sp 8 ret).bytes,
                    regions := s.mem.regions ++ [⟨sp - cgoCStack, cgoCStack + 8, true⟩] },
           df := false }

theorem cgoEntry_cgoEntryState {p : Program} {s : State} {ret sp : Nat} (hret : RetAddr p ret)
    (h16 : sp % 16 = 8) (hlo : cgoCStack ≤ sp) (hhi : sp + 8 ≤ 2 ^ 48)
    (hfree : ∀ r ∈ s.mem.regions, r.base + r.size ≤ sp - cgoCStack ∨ sp + 8 ≤ r.base) :
    CgoEntry p s (cgoEntryState s ret sp) ret where
  rip := rfl
  arg := by simp [cgoEntryState]
  retSlot := by
    have hsp : (BitVec.ofNat 64 sp).toNat = sp := by simp; omega
    simp only [cgoEntryState, if_neg (show (4 : Nat) ≠ 7 by decide), if_true, GoABI.regSP, hsp]
    change (s.mem.writeLE sp 8 ret).readLE sp 8 = ret
    rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := hret.user; omega)]
  retAddr := hret
  stack := by
    have hsp : (BitVec.ofNat 64 sp).toNat = sp := by simp; omega
    refine ⟨by simp [cgoEntryState, CABI.regSP, hsp, h16], by simp [cgoEntryState, CABI.regSP, hsp, hlo],
      by simp [cgoEntryState, CABI.regSP, hsp]; omega, ?_⟩
    simp only [cgoEntryState, CABI.regSP, if_neg (show (4 : Nat) ≠ 7 by decide), if_true, hsp,
      Janus.Arm64.Memory.accessible, Bool.and_eq_true, List.any_append, List.all_append, List.any_cons,
      List.any_nil, List.all_cons, List.all_nil, Bool.or_eq_true, Bool.not_eq_true', Bool.and_true,
      Bool.or_false]
    refine ⟨.inr (by simp; omega), .inr ⟨?_, by simp⟩⟩
    simp only [List.all_eq_true]
    intro r hr
    rcases hfree r hr with h | h <;> simp <;> omega
  stackSep a n w h := by
    have hsp : (BitVec.ofNat 64 sp).toNat = sp := by simp; omega
    obtain ⟨⟨r, hr, h1, h2, -, -⟩, -⟩ := (Janus.Arm64.Memory.accessible_iff s.mem a n w).1 h
    simp only [cgoEntryState, GoABI.regSP, if_neg (show (4 : Nat) ≠ 7 by decide), if_true, hsp,
      outside_cons, outside_nil, and_true]
    rcases hfree r hr with h3 | h3 <;> omega
  kept a n hk := by
    obtain ⟨⟨r, hr, h1, h2, -, -⟩, -⟩ := (Janus.Arm64.Memory.accessible_iff s.mem a n false).1 hk.1
    refine (Janus.Arm64.Memory.readLE_of_bytes_eq (m := (cgoEntryState s ret sp).mem)
      (m' := s.mem.writeLE sp 8 ret) rfl a n).trans ?_
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := s.mem) ret (by rcases hfree r hr with h3 | h3 <;> omega)
  keptAcc a n w h := by
    have := Janus.FFI.accessible_append_writable' (m := s.mem) (rs := [⟨sp - cgoCStack, cgoCStack + 8, true⟩])
      (by simp) h.1
    simpa [cgoEntryState, Janus.Arm64.Memory.accessible] using this
  df := rfl
  fs := rfl
  mxcsr := rfl
  fpucw := rfl

def cgoResumeState (s t' : State) : State :=
  goResumeState s { bytes := fun a => if s.mem.accessible a 1 false then t'.mem.bytes a else s.mem.bytes a,
                    regions := s.mem.regions }

theorem cgoResumed_cgoResumeState {s : State} (t' : State) (ht : TlsG s) :
    CgoResumed s t' (cgoResumeState s t') := by
  refine ⟨_, goResume_goResumeState ht rfl, rfl, fun a ho => ?_⟩
  simp only [cgoClobber, outside_cons, outside_nil, and_true] at ho
  obtain ⟨-, -, -, h4⟩ := ho
  have h8 := ht.base.1
  have hx : a < s.fsBase.toNat - 8 ∨ s.fsBase.toNat - 8 + 8 ≤ a := by omega
  exact Janus.Arm64.Memory.bytes_writeLE_outside _ hx

/-- Every allowed `cgocall` has a result, given an admissible return address, a system stack
disjoint from the Go memory and the TLS `g` slot (`TlsG`). -/
theorem cgoCall_satisfiable {p : Program} {s : State} {ret sp : Nat} (hret : RetAddr p ret)
    (h16 : sp % 16 = 8) (hlo : cgoCStack ≤ sp) (hhi : sp + 8 ≤ 2 ^ 48)
    (hfree : ∀ r ∈ s.mem.regions, r.base + r.size ≤ sp - cgoCStack ∨ sp + 8 ≤ r.base) (ht : TlsG s)
    (hs : (CgoCall p).safe "runtime.cgocall" s) : ∃ s', (CgoCall p).next "runtime.cgocall" s s' := by
  obtain ⟨-, hrun⟩ := hs
  have he := cgoEntry_cgoEntryState (s := s) hret h16 hlo hhi hfree
  obtain ⟨t', hr, hc⟩ := (hrun _ ret 0 he).exists_runsTo (topOfStack_satisfiable 0)
  exact ⟨_, rfl, _, ret, 0, t', he, hr, hc, cgoResumed_cgoResumeState t' ht⟩

theorem callbackSpec_satisfiable (t : TLSImage) (fn : Nat) (G : State → Prop) (E : State → Memory) :
    (CallbackSpec t fn G E).Total := fun f s ⟨hf, _⟩ =>
  ⟨_, hf, E s, ⟨fun i => if i = 4 then s.regs 4 + 8 else s.regs i, s.flags, s.xmm, s.ymmHi, s.mxcsr, rfl,
    by simp, rfl⟩, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

/-! ## `cgocallback` -/

/-- A Go call state from every C state: on a goroutine stack at `sp` (a new region
`[sp − cbGoStack, sp + 8)` disjoint from the C memory) holding the return address. -/
def cbState (s : State) (ret sp : Nat) : State :=
  { s with rip := BitVec.ofNat 64 (s.mem.readLE ((s.regs 4).toNat + 8) 8),
           regs := fun i => if i = 0 then BitVec.ofNat 64 (s.mem.readLE ((s.regs 4).toNat + 16) 8)
             else if i = 4 then BitVec.ofNat 64 sp else s.regs i,
           xmm := fun i => if i = 15 then 0 else s.xmm i, df := false,
           mem := { bytes := (s.mem.writeLE sp 8 ret).bytes,
                    regions := s.mem.regions ++ [⟨sp - cbGoStack, cbGoStack + 8, true⟩] } }

theorem callbackEntry_cbState {t : TLSImage} {p : Janus.Amd64.Program} {ret sp : Nat} (s : State)
    (hret : RetAddr p ret) (hlo : cbGoStack ≤ sp) (hhi : sp + 8 ≤ 2 ^ 48)
    (hfree : ∀ r ∈ s.mem.regions, r.base + r.size ≤ sp - cbGoStack ∨ sp + 8 ≤ r.base) :
    CallbackEntry t p s (cbState s ret sp) ret where
  rip := rfl
  arg := by simp [cbState]
  retSlot := by
    have hsp : (BitVec.ofNat 64 sp).toNat = sp := by simp; omega
    simp only [cbState, if_neg (show (4 : Nat) ≠ 0 by decide), if_true, hsp]
    change (s.mem.writeLE sp 8 ret).readLE sp 8 = ret
    rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := hret.user; omega)]
  retAddr := hret
  zero := by simp [cbState, xmmZero]
  df := rfl
  goStack := by
    have hsp : (BitVec.ofNat 64 sp).toNat = sp := by simp; omega
    refine ⟨by simp [cbState, hsp, hlo], by simp [cbState, hsp]; omega, ?_⟩
    simp only [cbState, if_neg (show (4 : Nat) ≠ 0 by decide), if_true, hsp,
      Janus.Arm64.Memory.accessible, Bool.and_eq_true, List.any_append, List.all_append, List.any_cons,
      List.any_nil, List.all_cons, List.all_nil, Bool.or_eq_true, Bool.not_eq_true', Bool.and_true,
      Bool.or_false]
    refine ⟨.inr (by simp; omega), .inr ⟨?_, by simp⟩⟩
    simp only [List.all_eq_true]
    intro r hr
    rcases hfree r hr with h | h <;> simp <;> omega
  stackSep a n w h := by
    have hsp : (BitVec.ofNat 64 sp).toNat = sp := by simp; omega
    obtain ⟨⟨r, hr, h1, h2, -, -⟩, -⟩ := (Janus.Arm64.Memory.accessible_iff s.mem a n w).1 h
    simp only [cbState, if_neg (show (4 : Nat) ≠ 0 by decide), if_true, hsp,
      outside_cons, outside_nil, and_true]
    rcases hfree r hr with h3 | h3 <;> omega
  kept a n hk := by
    obtain ⟨⟨r, hr, h1, h2, -, -⟩, -⟩ := (Janus.Arm64.Memory.accessible_iff s.mem a n false).1 hk.1
    refine (Janus.Arm64.Memory.readLE_of_bytes_eq (m := (cbState s ret sp).mem)
      (m' := s.mem.writeLE sp 8 ret) rfl a n).trans ?_
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := s.mem) ret (by rcases hfree r hr with h3 | h3 <;> omega)
  keptAcc a n w h := by
    have := Janus.FFI.accessible_append_writable' (m := s.mem) (rs := [⟨sp - cbGoStack, cbGoStack + 8, true⟩])
      (by simp) h.1
    simpa [cbState, Janus.Arm64.Memory.accessible] using this
  fs := rfl
  mxcsr := rfl
  fpucw := rfl

def cbResumeState (s u' : State) : State :=
  { s with rip := retAddrOf s, df := false,
           regs := fun i => if i = 4 then s.regs 4 + 8 else s.regs i,
           mem := { bytes := fun a => if s.mem.accessible a 1 false then u'.mem.bytes a else s.mem.bytes a,
                    regions := s.mem.regions } }

theorem cbResumed_cbResumeState (t : TLSImage) (s u' : State) : CbResumed t s u' (cbResumeState s u') :=
  ⟨_, ⟨_, s.flags, s.xmm, s.ymmHi, s.mxcsr, rfl, by simp, rfl⟩, rfl, fun _ _ => rfl⟩

/-- Every allowed `cgocallback` has a result, for a total inner contract, an admissible return
address and a goroutine stack at `sp` disjoint from the C memory (as every real callback has). -/
theorem cgoCallback_satisfiable {t : TLSImage} {p : Janus.Amd64.Program} {Cin : Contract} {ret sp : Nat}
    (hC : Cin.Total) (hret : RetAddr p ret) {f : String} {s : State} (hlo : cbGoStack ≤ sp)
    (hhi : sp + 8 ≤ 2 ^ 48)
    (hfree : ∀ r ∈ s.mem.regions, r.base + r.size ≤ sp - cbGoStack ∨ sp + 8 ≤ r.base)
    (hs : (CgoCallback t p Cin (fun _ => True)).safe f s) :
    ∃ s', (CgoCallback t p Cin (fun _ => True)).next f s s' := by
  obtain ⟨hf, -, hgo⟩ := hs
  have he := callbackEntry_cbState (t := t) s hret hlo hhi hfree
  obtain ⟨u', hr, hab⟩ := (hgo _ ret he trivial).exists_runsTo hC
  exact ⟨_, hf, _, ret, u', he, trivial, hr, hab, cbResumed_cbResumeState t s u'⟩




end Janus.Amd64.FFI
