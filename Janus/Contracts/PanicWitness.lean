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
    (fun ch rm d hf => LeftFrame.prefix (MemFrame.refl _ _) rfl hf) (hs s hpc)
    (MemFrame.refl _ _) rfl rfl (h { s with pc := BitVec.ofNat 64 eGopanic } fi rfl hfind (GopanicPre.pc _ hpre))

theorem goexit_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eGoexit)
    (h : GoexitContract p eGoexit (P0 T RPa) U0 T) : GoexitContract p A (P0 T RPa) U0 T := by
  intro s fi hpc hfind hpre
  exact Engine.of_prefix (c := s) (c' := { s with pc := BitVec.ofNat 64 eGoexit })
    (fun ch rm d hf => LeftFrame.prefix (MemFrame.refl _ _) rfl hf) (hs s hpc)
    (MemFrame.refl _ _) rfl rfl (h { s with pc := BitVec.ofNat 64 eGoexit } fi rfl hfind (GoexitPre.pc _ hpre))

theorem deferreturn_at {p : Program} {A : Nat} {T : List FuncInfo} (hs : StubAt p A eDeferreturn)
    (h : DeferreturnContract p eDeferreturn (P0 T RPa) U0) : DeferreturnContract p A (P0 T RPa) U0 := by
  intro s hpc hpre
  exact Engine.of_prefix_ret (c := s) (c' := { s with pc := BitVec.ofNat 64 eDeferreturn })
    (fun ch rm d hf => RetFin.prefix (MemFrame.refl _ _) hf) (hs s hpc)
    (MemFrame.refl _ _) rfl (h { s with pc := BitVec.ofNat 64 eDeferreturn } rfl (DeferreturnPre.pc _ hpre))

/-! ## Linking the engine into a program -/

theorem fetchIn_skip {l : List Segment} {pc : Nat}
    (h : ∀ seg ∈ l, ¬ (seg.base ≤ pc ∧ (pc - seg.base) % 4 = 0 ∧ (pc - seg.base) / 4 < seg.words.length)) :
    Program.fetchIn l pc = none := by
  induction l with
  | nil => rfl
  | cons seg rest ih =>
    simp only [Program.fetchIn]
    have h1 := h seg (List.mem_cons_self)
    have hrest : Program.fetchIn rest pc = none := ih fun sg hsg => h sg (List.mem_cons_of_mem _ hsg)
    split
    · rename_i hc
      split
      · rename_i w hw
        exfalso; apply h1
        refine ⟨hc.1, hc.2, ?_⟩
        rcases Nat.lt_or_ge ((pc - seg.base) / 4) seg.words.length with hlt | hge
        · exact hlt
        · have : seg.words[(pc - seg.base) / 4]? = none := List.getElem?_eq_none hge
          rw [this] at hw; cases hw
      · exact hrest
    · exact hrest

theorem fetchIn_append_skip {l₁ : List Segment} (l₂ : List Segment) {pc : Nat}
    (h : ∀ seg ∈ l₁, ¬ (seg.base ≤ pc ∧ (pc - seg.base) % 4 = 0 ∧ (pc - seg.base) / 4 < seg.words.length)) :
    Program.fetchIn (l₁ ++ l₂) pc = Program.fetchIn l₂ pc := by
  induction l₁ with
  | nil => rfl
  | cons seg rest ih =>
    simp only [List.cons_append, Program.fetchIn]
    have h1 := h seg (List.mem_cons_self)
    split
    · rename_i hc
      split
      · rename_i w hw
        exfalso; apply h1
        refine ⟨hc.1, hc.2, ?_⟩
        rcases Nat.lt_or_ge ((pc - seg.base) / 4) seg.words.length with hlt | hge
        · exact hlt
        · have : seg.words[(pc - seg.base) / 4]? = none := List.getElem?_eq_none hge
          rw [this] at hw; cases hw
      · exact ih fun sg hsg => h sg (List.mem_cons_of_mem _ hsg)
    · exact ih fun sg hsg => h sg (List.mem_cons_of_mem _ hsg)

theorem fetchIn_hit {seg : Segment} {rest : List Segment} {pc w : Nat} (h1 : seg.base ≤ pc)
    (h2 : (pc - seg.base) % 4 = 0) (h3 : seg.words[(pc - seg.base) / 4]? = some w) :
    Program.fetchIn (seg :: rest) pc = some w := by
  simp only [Program.fetchIn, h3]
  rw [if_pos ⟨h1, h2⟩]

theorem fetchIn_hit_only {seg : Segment} {pc w : Nat} (h : Program.fetchIn [seg] pc = some w) :
    seg.base ≤ pc ∧ (pc - seg.base) % 4 = 0 ∧ seg.words[(pc - seg.base) / 4]? = some w := by
  simp only [Program.fetchIn] at h
  split at h
  · rename_i hc
    split at h
    · rename_i w' hw'
      cases h
      exact ⟨hc.1, hc.2, hw'⟩
    · simp [Program.fetchIn] at h
  · simp [Program.fetchIn] at h

/-- The engine is part of `base.link (engineSeg :: rest)` when `base` has nothing where the engine
is (its segments, stubs and exit address lie outside the engine's code). -/
theorem EngineAt.of_link {base : Program} {rest : List Segment}
    (hseg : ∀ seg ∈ base.segments, seg.base + 4 * seg.words.length ≤ E ∨ E + 4 * engineCode.length ≤ seg.base)
    (hstub : ∀ st ∈ base.stubs, st.addr < E ∨ E + 4 * engineCode.length ≤ st.addr)
    (hexit : base.exitAddr < E ∨ E + 4 * engineCode.length ≤ base.exitAddr) :
    EngineAt (base.link (engineSeg :: rest)) := by
  intro pc w hq
  have hq' : E ≤ pc ∧ (pc - E) % 4 = 0 ∧ engineCode[(pc - E) / 4]? = some w :=
    fetchIn_hit_only (seg := engineSeg) hq
  obtain ⟨h1, h2, h3⟩ := hq'
  have hlt : (pc - E) / 4 < engineCode.length := by
    rcases Nat.lt_or_ge ((pc - E) / 4) engineCode.length with hh | hh
    · exact hh
    · have := List.getElem?_eq_none (l := engineCode) hh
      rw [this] at h3; cases h3
  refine ⟨?_, ?_, ?_⟩
  · show Program.fetchIn (base.segments ++ engineSeg :: rest) pc = some w
    rw [fetchIn_append_skip]
    · exact fetchIn_hit (seg := engineSeg) h1 h2 h3
    · intro seg hseg' ⟨a, b, c⟩
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
def stubSeg (prog : Program) (name : String) (tgt : Nat) : Segment :=
  { name := name, base := prog.contractAddr name, words := [stubWord (prog.contractAddr name) tgt] }

/-- The code to link into a program: the engine, and a branch to its entry at each of the named
contract addresses. -/
def panicImpl (prog : Program) (cs : List (String × Nat)) : List Segment :=
  engineSeg :: cs.map (fun c => stubSeg prog c.1 c.2)

/-! ## A witness memory: the model's table for `T` -/

instance (m : Memory) (i : Nat) (f : FuncInfo) : Decidable (TabEntry m i f) := by
  unfold TabEntry; infer_instance


/-- The 64-bit words `(address, value)` of the model's private memory for the function table `T`
(everything else is zero). -/
def tabWords (T : List FuncInfo) : List (Nat × Nat) :=
  (B + 0x28, T.length) :: (List.range T.length).flatMap fun i =>
    match T[i]? with
    | none => []
    | some f => [(tabAt i, f.entry), (tabAt i + 8, f.size), (tabAt i + 16, f.frame),
        (tabAt i + 24, f.deferreturn), (tabAt i + 32, if f.openDefer.isSome then 1 else 0),
        (tabAt i + 40, (f.openDefer.map (·.1)).getD 0), (tabAt i + 48, (f.openDefer.map (·.2)).getD 0)]

/-- The byte at `a` of the memory holding the 64-bit words `ws`. -/
def wordByte (ws : List (Nat × Nat)) (a : Nat) : BitVec 8 :=
  match ws.find? (fun w => decide (w.1 ≤ a ∧ a < w.1 + 8)) with
  | some w => BitVec.ofNat 8 (w.2 / 2 ^ (8 * (a - w.1)))
  | none => 0

/-- The witnesses' return address: a code address outside every region of `witMem`, so that the
program's `ret` instruction leaves the extracted code (`RetAddr`). -/
def witRet : Nat := 0x200000

/-- The witnesses' stack pointer at the call (arm64): inside the witness stack. -/
def witSP : Nat := 0x48000

/-- The witnesses' goroutine address (arm64): the start of the read-only goroutine region. -/
def witG : Nat := 0x50000

/-- An address inside the witnesses' stack (a pointer argument a witness points at). -/
def witArg : Nat := 0x41000

/-- The witness memory: the model's private memory `[0x10000, 0x11000)` (writable), a stack
`[0x40000, 0x50000)` (writable), the goroutine `[0x50000, 0x50100)` (read-only); the bytes are
zero except the words `ws`. -/
def witMem (ws : List (Nat × Nat)) : Memory :=
  ⟨wordByte ws, [⟨0x10000, 0x1000, true⟩, ⟨0x40000, 0x10000, true⟩, ⟨0x50000, 0x100, false⟩]⟩


/-- `witMem` with the program's read-only data in place: each data segment is a read-only region
holding its bytes. -/
def witMemD (ws : List (Nat × Nat)) (ds : List DataSegment) : Memory :=
  ⟨fun a => match ds.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
      | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
      | none => wordByte ws a,
    [⟨0x10000, 0x1000, true⟩, ⟨0x40000, 0x10000, true⟩, ⟨0x50000, 0x100, false⟩] ++
      ds.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

/-! ## The engine contracts are satisfiable

`gopanic`, `Goexit` and `deferreturn` of a function that has no deferred calls pending: the engine
alone as the program, the model's function table `gT` (one function covering the return address),
and a call state in the contract's precondition. (The examples show the contracts with deferred
calls pending: their `Witness` sections.) -/

/-- A one-function table: the function containing the return address `sret`. -/
def gT : List FuncInfo :=
  [{ name := "f", entry := 0x200000, size := 0x100, frame := 0x20, deferreturn := 0x40, openDefer := none }]

theorem gT_tok : TOK gT := by
  unfold TOK gT
  decide

def gmem : Memory := witMem (tabWords gT)

theorem env_g : Env0 gT gmem := by
  unfold Env0
  have hnd : ndef gmem = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem room_g : 0 < room0 gmem := by rw [room0_eq]; decide

theorem defers_g : defers0 gmem = [] := by
  have hnd : ndef gmem = 0 := by decide
  rw [defers0_eq, hnd]; rfl

theorem saved_g : saved0 gmem = none := by rw [saved0_eq]; decide

theorem pre_g (nargs : Nat) (hn : nargs ≤ 2) (pc x0 x1 : Nat) : PanicPre (P0 gT RPa) nargs (sstate pc gmem x0 x1) :=
  sstate_pre nargs hn pc x0 x1 env_g (by decide) (by decide) (by decide)

theorem gopanic_satisfiable : ∃ (P : PanicRuntime) (p : Program) (A : Nat) (U : State → Nat → Nat → Prop)
    (T : List FuncInfo), P.Laws ∧ GopanicContract p A P U T ∧ ∃ s fi, s.pc = BitVec.ofNat 64 A ∧
      FuncInfo.find T (s.regs 30).toNat = some fi ∧ GopanicPre P fi s := by
  refine ⟨P0 gT RPa, qE, eGopanic, U0, gT, P0_laws gT RPa, gopanic_run engineAt_qE gT gT_tok,
    sstate eGopanic gmem 1 0, FuncInfo.named gT "f", rfl, by decide, ?_⟩
  refine ⟨pre_g 2 (by decide) _ 1 0, by decide, room_g, fun h => absurd h (by decide), ?_⟩
  show FrameOK (P0 gT RPa) gmem _ _
  simp [frameOf, frameItems, recItems, FuncInfo.named, gT, P0_defers, sstate, defers_g, FrameOK]

theorem goexit_satisfiable : ∃ (P : PanicRuntime) (p : Program) (A : Nat) (U : State → Nat → Nat → Prop)
    (T : List FuncInfo), P.Laws ∧ GoexitContract p A P U T ∧ ∃ s fi, s.pc = BitVec.ofNat 64 A ∧
      FuncInfo.find T (s.regs 30).toNat = some fi ∧ GoexitPre P fi s := by
  refine ⟨P0 gT RPa, qE, eGoexit, U0, gT, P0_laws gT RPa, goexit_run engineAt_qE gT gT_tok,
    sstate eGoexit gmem 0 0, FuncInfo.named gT "f", rfl, by decide, ?_⟩
  refine ⟨pre_g 0 (by decide) _ 0 0, room_g, fun h => absurd h (by decide), ?_⟩
  show FrameOK (P0 gT RPa) gmem _ _
  simp [frameOf, frameItems, recItems, FuncInfo.named, gT, P0_defers, sstate, defers_g, FrameOK]

theorem deferreturn_satisfiable : ∃ (P : PanicRuntime) (p : Program) (A : Nat) (U : State → Nat → Nat → Prop),
    P.Laws ∧ DeferreturnContract p A P U ∧ ∃ s, s.pc = BitVec.ofNat 64 A ∧ DeferreturnPre P s := by
  refine ⟨P0 gT RPa, qE, eDeferreturn, U0, P0_laws gT RPa, deferreturn_run engineAt_qE,
    sstate eDeferreturn gmem 0 0, rfl, pre_g 0 (by decide) _ 0 0, ?_⟩
  show FrameOK (P0 gT RPa) gmem _ _
  simp [retFrame, frameItems, recItems, P0_defers, P0_saved, sstate, defers_g, saved_g, gOf, FrameOK]

end Janus.Contracts.PanicSat
