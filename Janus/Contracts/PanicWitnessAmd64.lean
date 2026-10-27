import Janus.Contracts.PanicWitness
import Janus.Contracts.PanicSatAmd64Run


/-!
# Witnessing the panic contracts for a linked program (amd64)

The model engine (`PanicSatAmd64`) meets every panic/defer/recover contract at its own entry points.
A program's contract addresses (`Program.contractAddr`) hold a single `jmp rel32` to the entry:
`panicImpl` is the code to link (`Program.link`), `EngineAt` and `StubAt` are checked for a concrete
program by `decide`, and the `*_at` theorems turn the engine's contracts into the contracts at the
program's addresses. The examples' `Witness` sections use them.
-/

namespace Janus.Contracts.PanicSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.PanicAmd64 Janus.Contracts.PanicModel

/-- The instruction at `A` is a branch that takes control to `E`, changing nothing else. -/
def StubAt (p : Program) (A E : Nat) : Prop :=
  ∀ s : State, s.rip = BitVec.ofNat 64 A → Janus.Amd64.Program.Steps p s 1 { s with rip := BitVec.ofNat 64 E }

theorem StubAt.of_jmp {p : Program} {A E rel len : Nat} {bs : List Nat} (hf : p.fetch A = some bs)
    (hs : p.stubAt A = none) (hx : A ≠ p.exitAddr) (hA : A + len < 2 ^ 64)
    (hd : decode bs = some (.jmp rel, len)) (hoff : (A + len + rel) % 2 ^ 64 = E) (hE : E < 2 ^ 47) :
    StubAt p A E := by
  intro s hpc
  have hpc' : s.rip.toNat = A := by rw [hpc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine Janus.Amd64.Program.Steps.single (by rw [hpc']; exact hx) (by rw [hpc']; exact hs)
    (by rw [hpc']; exact hf) ?_
  rw [step_of_decode hd]
  have hn : (BitVec.ofNat 64 ((A + len) % 2 ^ 64)).toNat = A + len := by
    simp only [BitVec.toNat_ofNat]; omega
  simp only [exec, hpc', branchTo, hn, hoff]
  rw [if_pos (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hE)]
  rfl

/-! ## The contracts at the engine's entry points -/

theorem deferproc_contract {p : Program} (hp : EngineAt p) (T : List FuncInfo) :
    DeferprocContract p eDeferproc (P0 T RPa) :=
  fun s hpc hpre => deferproc_run hp T s hpc hpre.1 hpre.2

theorem deferrangefunc_contract {p : Program} (hp : EngineAt p) (T : List FuncInfo) :
    DeferrangefuncContract p eDeferrangefunc (P0 T RPa) :=
  fun s hpc hpre => deferrangefunc_run hp T s hpc hpre.1 hpre.2

theorem PanicRet.toW {P : PanicRuntime} {n : Nat} {s s' : State} (extra : List (Nat × Nat))
    (h : PanicRet P n s s') : PanicRetW P n extra s s' := by
  obtain ⟨r, x, y, fl, m, hs, hf, he⟩ := h
  exact ⟨r, x, y, fl, m, hs, hf.mono fun a k ho => by
    simp only [outside_append] at ho ⊢; exact ho.1, he⟩

theorem deferprocStack_contract {p : Program} (hp : EngineAt p) (T : List FuncInfo) :
    DeferprocStackContract p eDeferprocStack (P0 T RPa) := fun s hpc hpre =>
  reachesRet_mono (deferprocStack_run hp T s hpc hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2)
    fun s' h => ⟨PanicRet.toW _ h.1, h.2.1, h.2.2⟩

theorem deferprocat_contract {p : Program} (hp : EngineAt p) (T : List FuncInfo) :
    DeferprocatContract p eDeferprocat (P0 T RPa) :=
  fun s hpc hpre => deferprocat_run hp T s hpc hpre.1 hpre.2.1 hpre.2.2

/-! ## A branch to the entry point at a contract address -/

theorem PanicPre.rip {P : PanicRuntime} {n : Nat} {s : State} (q : W64) (h : PanicPre P n s) :
    PanicPre P n { s with rip := q } := by
  obtain ⟨a, ⟨b1, b2, b3⟩, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, ⟨b1, b2, b3⟩, c, d, e, f, g, h, i, j⟩

theorem GopanicPre.rip {P : PanicRuntime} {fi : FuncInfo} {s : State} (q : W64) (h : GopanicPre P fi s) :
    GopanicPre P fi { s with rip := q } := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨PanicPre.rip q a, b, c, d, e⟩

theorem GoexitPre.rip {P : PanicRuntime} {fi : FuncInfo} {s : State} (q : W64) (h : GoexitPre P fi s) :
    GoexitPre P fi { s with rip := q } := by
  obtain ⟨a, b, c, d⟩ := h
  exact ⟨PanicPre.rip q a, b, c, d⟩

theorem DeferreturnPre.rip {P : PanicRuntime} {s : State} (q : W64) (h : DeferreturnPre P s) :
    DeferreturnPre P { s with rip := q } := by
  obtain ⟨a, b⟩ := h
  exact ⟨PanicPre.rip q a, b⟩

theorem summary_of_stub {p : Program} {A E : Nat} {pre : State → Prop} {post : State → State → Prop}
    (hs : StubAt p A E) (h : Summary p E pre post)
    (hpre : ∀ s q, pre s → pre { s with rip := q })
    (hpost : ∀ s q s', post { s with rip := q } s' → post s s') : Summary p A pre post := by
  intro s hpc hp
  obtain ⟨k, s2, hk, hr, hq⟩ := h { s with rip := BitVec.ofNat 64 E } rfl (hpre s _ hp)
  exact ⟨1 + k, s2, (hs s hpc).trans hk, hr, hpost s _ s2 hq⟩

theorem deferproc_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferproc)
    (h : DeferprocContract p eDeferproc (P0 T RPa)) : DeferprocContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.rip q h.1, h.2⟩) (fun _ _ _ h => h)

theorem deferprocStack_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferprocStack)
    (h : DeferprocStackContract p eDeferprocStack (P0 T RPa)) : DeferprocStackContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.rip q h.1, h.2⟩) (fun _ _ _ h => h)

theorem deferrangefunc_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferrangefunc)
    (h : DeferrangefuncContract p eDeferrangefunc (P0 T RPa)) : DeferrangefuncContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.rip q h.1, h.2⟩) (fun _ _ _ h => h)

theorem deferprocat_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferprocat)
    (h : DeferprocatContract p eDeferprocat (P0 T RPa)) : DeferprocatContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.rip q h.1, h.2⟩) (fun _ _ _ h => h)

theorem gorecover_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eGorecover)
    (h : GorecoverContract p eGorecover (P0 T RPa)) : GorecoverContract p A (P0 T RPa) :=
  summary_of_stub hs h (fun _ q h => ⟨PanicPre.rip q h.1, h.2⟩) (fun _ _ _ h => h)

theorem gopanic_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eGopanic)
    (h : GopanicContract p eGopanic (P0 T RPa) U1 T) : GopanicContract p A (P0 T RPa) U1 T := by
  intro s fi hpc hfind hpre
  exact Engine.of_prefix (c := s) (c' := { s with rip := BitVec.ofNat 64 eGopanic })
    (fun ch rm d hf => LeftFrame.prefix (MemFrame.refl _ _) rfl hf) (hs s hpc)
    (MemFrame.refl _ _) rfl rfl (h { s with rip := BitVec.ofNat 64 eGopanic } fi rfl hfind (GopanicPre.rip _ hpre))

theorem goexit_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eGoexit)
    (h : GoexitContract p eGoexit (P0 T RPa) U1 T) : GoexitContract p A (P0 T RPa) U1 T := by
  intro s fi hpc hfind hpre
  exact Engine.of_prefix (c := s) (c' := { s with rip := BitVec.ofNat 64 eGoexit })
    (fun ch rm d hf => LeftFrame.prefix (MemFrame.refl _ _) rfl hf) (hs s hpc)
    (MemFrame.refl _ _) rfl rfl (h { s with rip := BitVec.ofNat 64 eGoexit } fi rfl hfind (GoexitPre.rip _ hpre))

theorem deferreturn_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferreturn)
    (h : DeferreturnContract p eDeferreturn (P0 T RPa) U1) : DeferreturnContract p A (P0 T RPa) U1 := by
  intro s hpc hpre
  exact Engine.of_prefix_ret (c := s) (c' := { s with rip := BitVec.ofNat 64 eDeferreturn })
    (fun ch rm d hf => RetFin.prefix (MemFrame.refl _ _) hf) (hs s hpc)
    (MemFrame.refl _ _) rfl (h { s with rip := BitVec.ofNat 64 eDeferreturn } rfl (DeferreturnPre.rip _ hpre))

/-! ## Linking the engine into a program -/

theorem fetchIn_append_skip : ∀ (l₁ l₂ : List Janus.Amd64.Segment) {pc : Nat},
    (∀ seg ∈ l₁, ¬ (seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length)) →
    Janus.Amd64.Program.fetchIn (l₁ ++ l₂) pc = Janus.Amd64.Program.fetchIn l₂ pc
  | [], _, _, _ => rfl
  | seg :: rest, l₂, pc, h => by
    simp only [List.cons_append, Janus.Amd64.Program.fetchIn]
    rw [if_neg (h seg List.mem_cons_self)]
    exact fetchIn_append_skip rest l₂ fun sg hsg => h sg (List.mem_cons_of_mem _ hsg)

theorem fetchIn_hit {seg : Janus.Amd64.Segment} {rest : List Janus.Amd64.Segment} {pc : Nat}
    (h : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length) :
    Janus.Amd64.Program.fetchIn (seg :: rest) pc = some ((seg.bytes.drop (pc - seg.base)).take 15) := by
  simp only [Janus.Amd64.Program.fetchIn]
  rw [if_pos h]

theorem fetchIn_single {seg : Janus.Amd64.Segment} {pc : Nat} {w : List Nat}
    (h : Janus.Amd64.Program.fetchIn [seg] pc = some w) :
    (seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length) ∧ w = (seg.bytes.drop (pc - seg.base)).take 15 := by
  simp only [Janus.Amd64.Program.fetchIn] at h
  by_cases hc : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length
  · rw [if_pos hc] at h
    exact ⟨hc, (Option.some.inj h).symm⟩
  · rw [if_neg hc] at h
    exact absurd h (by simp [Janus.Amd64.Program.fetchIn])

theorem engineSeg_base : engineSeg.base = E := rfl
theorem engineSeg_len : engineSeg.bytes.length = engineCode.length := rfl

/-- The engine is part of `base.link (engineSeg :: rest)` when `base` has nothing where the engine
is (its segments, stubs and exit address lie outside the engine's code). -/
theorem EngineAt.of_link {base : Program} {rest : List Janus.Amd64.Segment}
    (hseg : ∀ seg ∈ base.segments, seg.base + seg.bytes.length ≤ E ∨ E + engineCode.length ≤ seg.base)
    (hstub : ∀ st ∈ base.stubs, st.addr < E ∨ E + engineCode.length ≤ st.addr)
    (hexit : base.exitAddr < E ∨ E + engineCode.length ≤ base.exitAddr) :
    EngineAt (base.link (engineSeg :: rest)) := by
  intro pc w hq
  obtain ⟨hc, hw⟩ := fetchIn_single (seg := engineSeg) (pc := pc) (w := w) hq
  rw [engineSeg_base, engineSeg_len] at hc
  refine ⟨?_, ?_, ?_⟩
  · show Janus.Amd64.Program.fetchIn (base.segments ++ engineSeg :: rest) pc = some w
    rw [fetchIn_append_skip]
    · rw [hw]; exact fetchIn_hit (by rw [engineSeg_base, engineSeg_len]; exact hc)
    · intro seg hseg' ⟨a, b⟩
      rcases hseg seg hseg' with h | h <;> omega
  · show base.stubs.find? (·.addr = pc) = none
    rw [List.find?_eq_none]
    intro st hst
    simp only [decide_eq_true_eq]
    intro heq
    rcases hstub st hst with h | h <;> omega
  · show pc ≠ base.exitAddr
    intro heq
    rcases hexit with h | h <;> omega

/-- The branch segment for the contract `name` of `prog`, to the entry `tgt`. -/
def stubSeg (prog : Program) (name : String) (tgt : Nat) : Janus.Amd64.Segment :=
  { name := name, base := prog.contractAddr name, bytes := stubCode (prog.contractAddr name) tgt }

/-- The code to link into a program: the engine, and a branch to its entry at each of the named
contract addresses. -/
def panicImpl (prog : Program) (cs : List (String × Nat)) : List Janus.Amd64.Segment :=
  engineSeg :: cs.map (fun c => stubSeg prog c.1 c.2)

/-- The goroutine and the stack pointer of the witness states. -/
def wg : Nat := 0x50000
def wsp : Nat := 0x4ff00

/-! ## Read-only data -/

/-- A data object of the program is readable (the amd64 twin of `Janus.Tactic.accessible_of_dataRead`). -/
theorem accessible_of_dataRead {p : Program} {m : Memory} (h : p.DataLoaded m) {a n : Nat}
    (hv : (dataRead p a n).isSome = true) : m.accessible a n false = true := by
  unfold dataRead at hv
  cases hd : dataSegAt p a n with
  | none => rw [hd] at hv; cases hv
  | some d =>
    unfold dataSegAt at hd
    have hmem := List.mem_of_find?_eq_some hd
    have hp := List.find?_some hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hreg, _⟩ := h d hmem
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hreg
    obtain ⟨r, hr, ⟨⟨⟨hb, he⟩, hw⟩, _⟩⟩ := hreg
    exact Janus.Arm64.Memory.accessible_of_mem m hr (by omega) (by omega) hw

end Janus.Contracts.PanicSatAmd64
