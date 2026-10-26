import Janus.Contracts.PanicSatRun

/-!
# Witnessing the panic contracts for a linked program (arm64)

The model engine (`PanicSat`) meets every panic/defer/recover contract at its own entry points.
A program's contract addresses (`Program.contractAddr`) hold a single branch to the entry:
`panicImpl` is the code to link (`Program.link`), `EngineAt` and `StubAt` are checked for a concrete
program by `decide`, and the `*_at` theorems turn the engine's contracts into the contracts at the
program's addresses. The examples' `Witness` sections use them.
-/

set_option linter.constructorNameAsVariable false

namespace Janus.Contracts.PanicSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
open Janus.Contracts.PanicModel Janus.Spec.Map

/-! ## The contracts at the engine's entry points -/

theorem deferproc_contract {p : Program} (hp : EngineAt p) (T : List FuncInfo) :
    DeferprocContract p eDeferproc (P0 T RPa) :=
  fun s hpc hpre => deferproc_run hp T s hpc hpre.1 hpre.2

theorem deferrangefunc_contract {p : Program} (hp : EngineAt p) (T : List FuncInfo) :
    DeferrangefuncContract p eDeferrangefunc (P0 T RPa) :=
  fun s hpc hpre => deferrangefunc_run hp T s hpc hpre.1 hpre.2

theorem PanicRet.toW {P : PanicRuntime} {n : Nat} {s s' : State} (extra : List (Nat × Nat))
    (h : PanicRet P n s s') : PanicRetW P n extra s s' := by
  obtain ⟨junk, f, v, m, hs, hf, he⟩ := h
  exact ⟨junk, f, v, m, hs, hf.mono fun a k ho => by
    simp only [outside_append] at ho ⊢; exact ho.1, he⟩

theorem deferprocStack_contract {p : Program} (hp : EngineAt p) (T : List FuncInfo) :
    DeferprocStackContract p eDeferprocStack (P0 T RPa) := fun s hpc hpre =>
  reachesRet_mono (deferprocStack_run hp T s hpc hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2)
    fun s' h => ⟨PanicRet.toW _ h.1, h.2.1, h.2.2⟩

theorem deferprocat_contract {p : Program} (hp : EngineAt p) (T : List FuncInfo) :
    DeferprocatContract p eDeferprocat (P0 T RPa) :=
  fun s hpc hpre => deferprocat_run hp T s hpc hpre.1 hpre.2.1 hpre.2.2

/-! ## A branch to the entry point at a contract address -/

theorem PanicPre.pc {P : PanicRuntime} {n : Nat} {s : State} (q : W64) (h : PanicPre P n s) :
    PanicPre P n { s with pc := q } := by
  obtain ⟨a, ⟨b, c, d⟩, e, f⟩ := h
  exact ⟨a, ⟨b, c, d⟩, e, f⟩


/-- The instruction at `A` is a branch that takes control to `E`, changing nothing else. -/
def StubAt (p : Program) (A E : Nat) : Prop :=
  ∀ s : State, s.pc = BitVec.ofNat 64 A → Program.Steps p s 1 { s with pc := BitVec.ofNat 64 E }

/-- A branch word `b E` for the address `A` (`A ≤ E`, within 128 MB). -/
def stubWord (A E : Nat) : Nat := 0x14000000 + (E - A) / 4

theorem StubAt.of_decode {p : Program} {A E w imm : Nat} (hf : p.fetch A = some w) (hs : p.stubAt A = none)
    (hx : A ≠ p.exitAddr) (hA : A < 2 ^ 64) (hd : decodeAll w = some (.b false imm))
    (hoff : BitVec.ofNat 64 A + sext64 28 (imm * 4) = BitVec.ofNat 64 E) : StubAt p A E := by
  intro s hpc
  have hpc' : s.pc.toNat = A := by rw [hpc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hA
  refine Program.Steps.single (by rw [hpc']; exact hx) (by rw [hpc']; exact hs) (by rw [hpc']; exact hf) ?_
  rw [step_of_decodeAll hd]
  have h1 : s.pc + sext64 28 (imm * 4) = BitVec.ofNat 64 E := by rw [hpc]; exact hoff
  simp only [exec, Bool.false_eq_true, if_false, h1]

theorem GopanicPre.pc {P : PanicRuntime} {fi : FuncInfo} {s : State} (q : W64) (h : GopanicPre P fi s) :
    GopanicPre P fi { s with pc := q } := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨PanicPre.pc q a, b, c, d, e⟩

theorem GoexitPre.pc {P : PanicRuntime} {fi : FuncInfo} {s : State} (q : W64) (h : GoexitPre P fi s) :
    GoexitPre P fi { s with pc := q } := by
  obtain ⟨a, b, c, d⟩ := h
  exact ⟨PanicPre.pc q a, b, c, d⟩

theorem DeferreturnPre.pc {P : PanicRuntime} {s : State} (q : W64) (h : DeferreturnPre P s) :
    DeferreturnPre P { s with pc := q } := by
  obtain ⟨a, b⟩ := h
  exact ⟨PanicPre.pc q a, b⟩

theorem summary_of_stub {p : Program} {A E : Nat} {pre : State → Prop} {post : State → State → Prop}
    (hs : StubAt p A E) (h : Summary p E pre post)
    (hpre : ∀ s q, pre s → pre { s with pc := q })
    (hpost : ∀ s q s', post { s with pc := q } s' → post s s') : Summary p A pre post := by
  intro s hpc hp
  obtain ⟨k, s2, hk, hr, hq⟩ := h { s with pc := BitVec.ofNat 64 E } rfl (hpre s _ hp)
  exact ⟨1 + k, s2, (hs s hpc).trans hk, hr, hpost s _ s2 hq⟩

theorem deferproc_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferproc)
    (h : DeferprocContract p eDeferproc (P0 T RPa)) : DeferprocContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.pc q h.1, h.2⟩) (fun _ _ _ h => h)

theorem deferprocStack_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferprocStack)
    (h : DeferprocStackContract p eDeferprocStack (P0 T RPa)) : DeferprocStackContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.pc q h.1, h.2⟩) (fun _ _ _ h => h)

theorem deferrangefunc_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferrangefunc)
    (h : DeferrangefuncContract p eDeferrangefunc (P0 T RPa)) : DeferrangefuncContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.pc q h.1, h.2⟩) (fun _ _ _ h => h)

theorem deferprocat_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferprocat)
    (h : DeferprocatContract p eDeferprocat (P0 T RPa)) : DeferprocatContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.pc q h.1, h.2⟩) (fun _ _ _ h => h)

theorem gorecover_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eGorecover)
    (h : GorecoverContract p eGorecover (P0 T RPa)) : GorecoverContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.pc q h.1, h.2⟩) (fun _ _ _ h => h)

theorem gopanic_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eGopanic)
    (h : GopanicContract p eGopanic (P0 T RPa) U0 T) : GopanicContract p A (P0 T RPa) U0 T := by
  intro s fi hpc hfind hpre
  exact Engine.of_prefix (c := s) (c' := { s with pc := BitVec.ofNat 64 eGopanic })
    (fun ch rm d hf => LeftFrame.prefix (MemFrame.refl _ _) hf) (hs s hpc)
    (MemFrame.refl _ _) rfl rfl (h { s with pc := BitVec.ofNat 64 eGopanic } fi rfl hfind (GopanicPre.pc _ hpre))

theorem goexit_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eGoexit)
    (h : GoexitContract p eGoexit (P0 T RPa) U0 T) : GoexitContract p A (P0 T RPa) U0 T := by
  intro s fi hpc hfind hpre
  exact Engine.of_prefix (c := s) (c' := { s with pc := BitVec.ofNat 64 eGoexit })
    (fun ch rm d hf => LeftFrame.prefix (MemFrame.refl _ _) hf) (hs s hpc)
    (MemFrame.refl _ _) rfl rfl (h { s with pc := BitVec.ofNat 64 eGoexit } fi rfl hfind (GoexitPre.pc _ hpre))

theorem deferreturn_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferreturn)
    (h : DeferreturnContract p eDeferreturn (P0 T RPa) U0) : DeferreturnContract p A (P0 T RPa) U0 := by
  intro s hpc hpre
  exact Engine.of_prefix_ret (c := s) (c' := { s with pc := BitVec.ofNat 64 eDeferreturn })
    (fun ch rm d hf => RetFin.prefix (MemFrame.refl _ _) hf) (hs s hpc)
    (MemFrame.refl _ _) rfl (h { s with pc := BitVec.ofNat 64 eDeferreturn } rfl (DeferreturnPre.pc _ hpre))

end Janus.Contracts.PanicSat
