import Janus.Contracts.WriteBarrier

/-!
# The runtime contracts are satisfiable (arm64)

A contract is a `Summary` over every state that meets its precondition; if no code could meet
it, every theorem assuming it would be vacuous (round 9 C1). For each arm64 contract of
`Janus.Contracts.Alloc`, `Janus.Contracts.String`, `Janus.Contracts.Slice` and
`Janus.Contracts.WriteBarrier` this file proves `<contract>_satisfiable`: there are runtime-owned
ranges `rt`, a readiness predicate `H`, an implementation `impl` (A64 machine code at the address
`A0` of a program with no other code) that **meets** the contract (proved by running it), and a
call state that satisfies the contract's precondition, `H` included. So no precondition is
contradictory and no contract asks for more than code can do.

**The model.** The witness memory `wmem` has a stack (`[wsp - 0x2000, wsp + 0x100)`, writable), a
readable `g` whose `stackguard0` is 0, a writable runtime area `[TYP, TYP + 0x100)` holding a type
descriptor (`Size_ = 8`, `PtrBytes = 0`) and a writable, zero heap `[HEAP, HEAP + 0x10000)`; `rtW`
is the last two. Each `H` fixes the call's arguments and states what the toy implementation
needs of the runtime's memory (as `rtView` shows it: the descriptor's words, a writable zero
heap). The implementations return constants (`constCode`: `MOVZ`/`MOVK` into `X0`–`X2`, `RET`):
the allocation contracts hand out the heap's first block, the others answer calls whose
operands are empty. These are models of the contracts, not of the Go runtime; that the runtime
meets them is what `examples/proofs/Decoderune.lean`, `Countrunes.lean`, `WriteBarrier.lean`
(proved from the binary's code) and the probes of `audit/` address. `decoderune` and `countrunes`
have no `H` (their contracts hold for every input), so their witness is the runtime's own code
proved in those examples.
-/

namespace Janus.Contracts.Sat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- A program with no code, stubs or data of its own. -/
def toy : Program := { segments := [], stubs := [], exitAddr := 0 }

/-- Where the model implementations are placed. -/
def A0 : Nat := 0x100000

/-- An implementation: the words `ws` at `A0`. -/
def at0 (ws : List Nat) : List Segment := [{ name := "model", base := A0, words := ws }]

/-- `toy` with the implementation `ws`, as a program of its own. -/
def withCode (ws : List Nat) : Program := { segments := at0 ws, stubs := [], exitAddr := 0 }

theorem link_at0 (ws : List Nat) : toy.link (at0 ws) = withCode ws := rfl

/-! ## Machine code -/

/-- `MOVZ Xd, #imm, LSL #(16·hw)`. -/
def movz (d imm hw : Nat) : Nat := 0xD2800000 + hw * 2 ^ 21 + imm * 32 + d
/-- `MOVK Xd, #imm, LSL #(16·hw)`. -/
def movk (d imm hw : Nat) : Nat := 0xF2800000 + hw * 2 ^ 21 + imm * 32 + d
/-- `Xd = c` for `c < 2^32`. -/
def movc (d c : Nat) : List Nat := [movz d (c % 65536) 0, movk d (c / 65536 % 65536) 1]
/-- `RET`. -/
def retW : Nat := 0xd65f03c0
/-- `X0 = c0; X1 = c1; X2 = c2; RET`. -/
def constCode (c0 c1 c2 : Nat) : List Nat := movc 0 c0 ++ movc 1 c1 ++ movc 2 c2 ++ [retW]

/-! ## The witness memory and call state -/

/-- The type descriptor (`Size_ = 8`, `PtrBytes = 0`). -/
def TYP : Nat := 0x30000
/-- The heap. -/
def HEAP : Nat := 0x40000
/-- The witness stack pointer. -/
def wsp : Nat := 0x20000
/-- The witness goroutine (its `stackguard0`, at `+16`, is 0). -/
def wg : Nat := 0x50000
/-- The witness return address. -/
def wret : Nat := 0x200000

/-- The runtime-owned ranges of the witnesses: the type descriptor's area and the heap. -/
def rtW : List (Nat × Nat) := [(TYP, TYP + 0x100), (HEAP, HEAP + 0x10000)]

/-- The witness memory: zero except `Size_ = 8` of the descriptor. -/
def wmem : Memory :=
  ⟨fun a => if a = TYP then 8 else 0,
    [⟨wsp - 0x2000, 0x2100, true⟩, ⟨TYP, 0x100, true⟩, ⟨HEAP, 0x10000, true⟩, ⟨wg, 0x100, false⟩]⟩

/-- The witness call state: arguments `r`, `g = wg`, return address `wret`, `SP = wsp`. -/
def wstate (r : Nat → W64) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else r i,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := wmem }

/-- The stack window of every witness contract. -/
abbrev wstack : Nat := 64

theorem wstate_callOK (r : Nat → W64) (n : Nat) (hn : n ≤ 16) : CallOK (wstate r) wstack n := by
  have hw : wmem.accessible (wsp - 0x2000) 0x2100 true = true := by decide
  simp only [CallOK, wstate, wstack, wret, wsp, BitVec.toNat_ofNat, ite_true, ite_false, Nat.reduceEqDiff]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by omega, ?_⟩
  exact Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)

/-- `wstate r` with all argument registers given by the list `l`. -/
def args (l : List Nat) : Nat → W64 := fun i => BitVec.ofNat 64 (l.getD i 0)

theorem argWords_args (l : List Nat) (n : Nat) (hn : n ≤ 16) (hl : ∀ x ∈ l, x < 2 ^ 64) :
    argWords (wstate (args l)) n = (List.range n).map fun i => l.getD i 0 := by
  unfold argWords
  suffices h : ∀ n k, k + n ≤ 28 → wordsFrom (fun i => ((wstate (args l)).regs i).toNat) k n =
      (List.range' k n).map fun i => l.getD i 0 by
    rw [h n 0 (by omega), List.range_eq_range']
  intro n
  induction n with
  | zero => intro k _; rfl
  | succ n ih =>
    intro k hk
    rw [wordsFrom_succ, ih (k + 1) (by omega), List.range'_succ, List.map_cons]
    congr 1
    simp only [wstate, args, show k ≠ 28 by omega, show k ≠ 30 by omega, ite_false, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    cases h : l[k]? with
    | none => simp [List.getD_eq_getElem?_getD, h]
    | some x => simp only [List.getD_eq_getElem?_getD, h, Option.getD_some]; exact hl x (List.mem_of_getElem? h)

/-! ## Constant implementations -/

/-- The return of a constant implementation as `RtPost`. -/
theorem rtPost_const {rt : List (Nat × Nat)} {sp : RtSpec} {s s' : State}
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18)
    (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid)
    (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr) (hfs : s'.fpsr = s.fpsr)
    (hm : s'.mem = s.mem)
    (hq : sp.post rt (argWords s sp.nargs) s.mem (s'.regs 0).toNat (s'.regs 1).toNat (s'.regs 2).toNat s.mem) :
    RtPost rt wstack sp s s' :=
  RtPost.intro hsp hpc h18 h28 h29 hdz htp hfc hfs (hm ▸ MemFrame.refl _ _) (hm ▸ hq)

/-- The readiness of the zero-operand witnesses: every argument word is 0. -/
def H0 : RtReady := fun a _ _ _ => ∀ j, arg a j = 0

theorem args_zero (n j : Nat) (hn : n ≤ 16) : arg (argWords (wstate (args [])) n) j = 0 := by
  rw [argWords_args [] n hn (by simp)]
  simp only [arg, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (List.range n)[j]? <;> rfl

theorem strPairs_zero (a : List Nat) (ha : ∀ j, arg a j = 0) (m : Memory) :
    ∀ k i, catBytes m (strPairs a i k) = [] := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih => intro i; simp only [strPairs, catBytes_cons, ha, ih, strBytes, List.range_zero, List.map_nil, List.nil_append]

theorem mem_strPairs_zero (a : List Nat) (ha : ∀ j, arg a j = 0) :
    ∀ k i x, x ∈ strPairs a i k → x = (0, 0) := by
  intro k
  induction k with
  | zero => intro i x hx; simp [strPairs] at hx
  | succ k ih =>
    intro i x hx
    simp only [strPairs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Prod.ext (ha i) (ha (i + 1))
    · exact ih _ _ hx

theorem outside_zero (rs : List (Nat × Nat)) : Outside 0 0 rs := by
  induction rs with
  | nil => trivial
  | cons r rs ih => obtain ⟨lo, hi⟩ := r; exact ⟨Or.inl (Nat.zero_le _), ih⟩

/-- **A contract is satisfiable**: runtime-owned ranges, a readiness predicate and an
implementation meeting it, and a call state meeting its precondition. -/
def Satisfiable (sp : RtSpec) : Prop :=
  ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Segment),
    RtContract (toy.link impl) A0 rt wstack H sp ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ RtPre rt wstack H sp s

/-! ## Concatenation -/

theorem concatstring_impl (k : Nat) :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 (concatstringSpec k) := by
  rw [link_at0]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, -, -, hH⟩
  have ha := ready_of rfl hH
  janus_run
  apply rtPost_const <;> (try rfl) <;> (try simp [setReg])
  rw [strPairs_zero _ (by simpa [concatstringSpec, Ready, H0] using ha)]
  simp [strBytes]

theorem concatstring_satisfiable (k : Nat) (hk : k ≤ 7) : Satisfiable (concatstringSpec k) := by
  have ha := fun j => args_zero (1 + 2 * k) j (by omega)
  refine ⟨rtW, H0, _, concatstring_impl k, wstate (args []), rfl,
    wstate_callOK _ _ (by simp [concatstringSpec]; omega), ⟨Or.inl (ha 0), ?_⟩, ?_,
    trivial, ready_intro rfl ha⟩
  · intro x hx
    rw [mem_strPairs_zero _ ha _ _ _ hx]
    exact ⟨⟨by decide, by simp⟩, fun h => absurd (ha 0) h⟩
  · intro r hr
    rw [mem_strPairs_zero _ ha _ _ _ hr]
    exact outside_zero _

/-- The zero-operand witness of a spec with `n` argument words: `H0`, `constCode 0 0 0`,
`wstate (args [])`, from the facts the spec needs. -/
theorem sat_zero (sp : RtSpec) (hn : sp.nargs ≤ 16)
    (himpl : RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 sp)
    (hpre : sp.pre (argWords (wstate (args [])) sp.nargs) wmem)
    (hreads : ∀ r ∈ sp.reads (argWords (wstate (args [])) sp.nargs) wmem,
      Outside r.1 r.2 (calleeStack (wstate (args [])) wstack sp.nargs))
    (hg : sp.guard = none) (hr : sp.ready = true) : Satisfiable sp :=
  ⟨rtW, H0, _, himpl, wstate (args []), rfl, wstate_callOK _ _ hn, hpre, hreads,
    by rw [hg]; trivial, ready_intro hr fun j => args_zero _ j hn⟩

set_option hygiene false in
/-- The tactic of every zero-operand implementation proof: run the code, then the spec's
postcondition with all operands 0 (`ha`). -/
macro "zero_impl" : tactic => `(tactic| (
  rw [link_at0]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, H0, arg, List.getD_eq_getElem?_getD] at ha
  janus_run
  apply rtPost_const <;> (try rfl) <;> (try simp [setReg])))

theorem concatstrings_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 concatstringsSpec := by
  zero_impl
  simp only [concatstringsSpec] at ha ⊢
  rw [ha 2]
  simp [strHdrs, catBytes, strBytes]

theorem concatstrings_satisfiable : Satisfiable concatstringsSpec := by
  have ha := fun j => args_zero 4 j (by decide)
  refine sat_zero _ (by decide) concatstrings_impl ?_ ?_ rfl rfl
  · simp only [concatstringsSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    refine ⟨Or.inl rfl, by decide, by simp, by simp [StrsIn, strHdrs], by simp [Disjoint]⟩
  · simp only [concatstringsSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [strHdrs, outside_zero]

theorem concatbyte_impl (k : Nat) :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 (concatbyteSpec k) := by
  zero_impl
  simp only [concatbyteSpec] at ha ⊢
  rw [strPairs_zero _ ha]
  simp [CatBytesOut]

theorem concatbyte_satisfiable (k : Nat) (hk : k ≤ 7) : Satisfiable (concatbyteSpec k) := by
  have ha := fun j => args_zero (1 + 2 * k) j (by omega)
  refine sat_zero _ (by simp [concatbyteSpec]; omega) (concatbyte_impl k) ⟨Or.inl (ha 0), ?_⟩ ?_ rfl rfl
  · intro x hx
    rw [mem_strPairs_zero _ ha _ _ _ hx]
    exact ⟨⟨by decide, by simp⟩, fun h => absurd (ha 0) h⟩
  · intro r hr
    rw [mem_strPairs_zero _ ha _ _ _ hr]
    exact outside_zero _

theorem concatbytes_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 concatbytesSpec := by
  zero_impl
  simp only [concatbytesSpec] at ha ⊢
  rw [ha 0, ha 2]
  simp [strHdrs, catBytes, CatBytesOut]

theorem concatbytes_satisfiable : Satisfiable concatbytesSpec := by
  have ha := fun j => args_zero 4 j (by decide)
  refine sat_zero _ (by decide) concatbytes_impl ?_ ?_ rfl rfl
  · simp only [concatbytesSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    refine ⟨Or.inl rfl, by decide, by simp, by simp [StrsIn, strHdrs], by simp [Disjoint]⟩
  · simp only [concatbytesSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [strHdrs, outside_zero]

/-! ## Conversions -/

theorem slicebytetostring_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 slicebytetostringSpec := by
  zero_impl
  simp only [slicebytetostringSpec] at ha ⊢
  rw [ha 2]
  simp [strBytes]

theorem slicebytetostring_satisfiable : Satisfiable slicebytetostringSpec := by
  have ha := fun j => args_zero 3 j (by decide)
  refine sat_zero _ (by decide) slicebytetostring_impl ?_ ?_ rfl rfl
  · simp only [slicebytetostringSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    exact ⟨Or.inl rfl, ⟨by decide, by simp⟩, fun h => absurd rfl h⟩
  · simp only [slicebytetostringSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [outside_zero]

theorem slicebytetostringtmp_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 slicebytetostringtmpSpec := by
  zero_impl
  simp only [slicebytetostringtmpSpec] at ha ⊢
  rw [ha 0, ha 1]
  simp [strBytes]

theorem slicebytetostringtmp_satisfiable : Satisfiable slicebytetostringtmpSpec := by
  have ha := fun j => args_zero 2 j (by decide)
  refine sat_zero _ (by decide) slicebytetostringtmp_impl ?_ ?_ rfl rfl
  · simp only [slicebytetostringtmpSpec] at ha ⊢
    rw [ha 0, ha 1]
    exact ⟨by decide, by simp⟩
  · simp only [slicebytetostringtmpSpec] at ha ⊢
    rw [ha 0, ha 1]
    simp [outside_zero]

theorem roundupsize_zero (b : Bool) : roundupsize 0 b = 0 := by
  cases b <;> rfl

theorem stringtoslicebyte_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 stringtoslicebyteSpec := by
  zero_impl
  simp only [stringtoslicebyteSpec] at ha ⊢
  rw [ha 0, ha 2]
  simp [ToBytesOut, strBytes, roundupsize_zero]

theorem stringtoslicebyte_satisfiable : Satisfiable stringtoslicebyteSpec := by
  have ha := fun j => args_zero 3 j (by decide)
  refine sat_zero _ (by decide) stringtoslicebyte_impl ?_ ?_ rfl rfl
  · simp only [stringtoslicebyteSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    exact ⟨Or.inl rfl, ⟨by decide, by simp⟩, fun h => absurd rfl h⟩
  · simp only [stringtoslicebyteSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [outside_zero]

theorem stringtoslicerune_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 stringtosliceruneSpec := by
  zero_impl
  simp only [stringtosliceruneSpec] at ha ⊢
  rw [ha 0, ha 2]
  simp [strBytes, runes, runesFrom, runesGo, roundupsize_zero]

theorem stringtoslicerune_satisfiable : Satisfiable stringtosliceruneSpec := by
  have ha := fun j => args_zero 3 j (by decide)
  refine sat_zero _ (by decide) stringtoslicerune_impl ?_ ?_ rfl rfl
  · simp only [stringtosliceruneSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    exact ⟨Or.inl rfl, ⟨by decide, by simp⟩, by decide, fun h => absurd rfl h⟩
  · simp only [stringtosliceruneSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [outside_zero]

theorem slicerunetostring_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 slicerunetostringSpec := by
  zero_impl
  simp only [slicerunetostringSpec] at ha ⊢
  rw [ha 2]
  simp [strBytes, runeWords, encodeRunes]

theorem slicerunetostring_satisfiable : Satisfiable slicerunetostringSpec := by
  have ha := fun j => args_zero 4 j (by decide)
  refine sat_zero _ (by decide) slicerunetostring_impl ?_ ?_ rfl rfl
  · simp only [slicerunetostringSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    exact ⟨Or.inl rfl, ⟨by decide, by simp⟩, fun h => absurd rfl h⟩
  · simp only [slicerunetostringSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [outside_zero]

theorem gostringn_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 gostringnSpec := by
  zero_impl
  simp only [gostringnSpec] at ha ⊢
  rw [ha 1]
  simp [strBytes]

theorem gostringn_satisfiable : Satisfiable gostringnSpec := by
  have ha := fun j => args_zero 2 j (by decide)
  refine sat_zero _ (by decide) gostringn_impl ?_ ?_ rfl rfl
  · simp only [gostringnSpec] at ha ⊢
    rw [ha 0, ha 1]
    exact ⟨by decide, by simp⟩
  · simp only [gostringnSpec] at ha ⊢
    rw [ha 0, ha 1]
    simp [outside_zero]

theorem gobytes_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 gobytesSpec := by
  zero_impl
  simp only [gobytesSpec] at ha ⊢
  rw [ha 1]
  simp

theorem gobytes_satisfiable : Satisfiable gobytesSpec := by
  have ha := fun j => args_zero 2 j (by decide)
  refine sat_zero _ (by decide) gobytes_impl ?_ ?_ rfl rfl
  · simp only [gobytesSpec] at ha ⊢
    rw [ha 0, ha 1]
    exact ⟨⟨by decide, by simp⟩, by decide⟩
  · simp only [gobytesSpec] at ha ⊢
    rw [ha 0, ha 1]
    simp [outside_zero]

/-! ## Slices with empty operands -/

theorem moveSliceNoScan_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 moveSliceNoScanSpec := by
  zero_impl
  simp only [moveSliceNoScanSpec] at ha ⊢
  rw [ha 3]
  simp

theorem moveSliceNoScan_satisfiable : Satisfiable moveSliceNoScanSpec := by
  have ha := fun j => args_zero 4 j (by decide)
  refine sat_zero _ (by decide) moveSliceNoScan_impl ?_ ?_ rfl rfl
  · simp only [moveSliceNoScanSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2, ha 3]
    exact ⟨by decide, by decide, by decide, by simp⟩
  · simp only [moveSliceNoScanSpec] at ha ⊢
    rw [ha 0, ha 1, ha 3]
    simp [outside_zero]

theorem slicecopy_impl :
    RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack H0 slicecopySpec := by
  zero_impl
  simp only [slicecopySpec] at ha ⊢
  rw [ha 1, ha 3, ha 4]
  simp [Copied]

theorem slicecopy_satisfiable : Satisfiable slicecopySpec := by
  have ha := fun j => args_zero 5 j (by decide)
  refine sat_zero _ (by decide) slicecopy_impl ?_ ?_ rfl rfl
  · simp only [slicecopySpec] at ha ⊢
    rw [ha 0, ha 1, ha 2, ha 3, ha 4]
    exact ⟨by decide, by decide, by decide, by simp, by decide, by simp⟩
  · simp only [slicecopySpec] at ha ⊢
    rw [ha 1, ha 2, ha 3, ha 4]
    simp [outside_zero]

/-! ## Fixed operands -/

/-- The readiness of a fixed-operand witness: the argument words are `L`, and the runtime's
memory satisfies `P`. -/
def HL (L : List Nat) (P : Memory → Prop) : RtReady := fun a _ _ v => a = L ∧ P v

theorem argWords_fixed (L : List Nat) (hn : L.length ≤ 16) (hl : ∀ x ∈ L, x < 2 ^ 64) :
    argWords (wstate (args L)) L.length = L := by
  rw [argWords_args L _ hn hl]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem sat_fixed (sp : RtSpec) (L : List Nat) (P : Memory → Prop) (code : List Nat)
    (himpl : RtContract (toy.link (at0 code)) A0 rtW wstack (HL L P) sp)
    (hlen : L.length = sp.nargs) (hn : sp.nargs ≤ 16) (hl : ∀ x ∈ L, x < 2 ^ 64)
    (hpre : sp.pre L wmem)
    (hreads : ∀ r ∈ sp.reads L wmem, Outside r.1 r.2 (calleeStack (wstate (args L)) wstack sp.nargs))
    (hg : sp.guard = none) (hr : sp.ready = true) (hP : P (rtView rtW wmem)) : Satisfiable sp := by
  have ha : argWords (wstate (args L)) sp.nargs = L := by
    rw [← hlen]; exact argWords_fixed L (by omega) hl
  refine ⟨rtW, HL L P, _, himpl, wstate (args L), rfl, wstate_callOK _ _ hn, ?_, ?_,
    by rw [hg]; trivial, ready_intro hr ⟨ha, hP⟩⟩
  · rw [ha]; exact hpre
  · rw [ha]; exact hreads

set_option hygiene false in
/-- The tactic of every fixed-operand implementation proof. -/
macro "fixed_impl" : tactic => `(tactic| (
  rw [link_at0]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, -, -, hH⟩
  obtain ⟨ha, hP⟩ := ready_of rfl hH
  janus_run
  apply rtPost_const <;> (try rfl) <;> (try simp [setReg])))

theorem typ_inRanges : InRanges TYP 16 rtW := ⟨(TYP, TYP + 0x100), by simp [rtW], Nat.le_refl _, by decide⟩
theorem heap_inRanges (n : Nat) (h : n ≤ 0x10000) : InRanges HEAP n rtW :=
  ⟨(HEAP, HEAP + 0x10000), by simp [rtW], Nat.le_refl _, by simp [HEAP]; omega⟩

theorem typSize_of (m : Memory) (h : (rtView rtW m).readLE TYP 8 = 8) : typSize m TYP = 8 := by
  rw [← h, readLE_rtView (typ_inRanges.sub (Nat.le_refl _) (by decide))]; rfl
theorem typPtrBytes_of (m : Memory) (h : (rtView rtW m).readLE (TYP + 8) 8 = 0) : typPtrBytes m TYP = 0 := by
  rw [← h, readLE_rtView (typ_inRanges.sub (by decide) (by decide))]; rfl

theorem elemOK_w : ElemOK wmem TYP := ⟨⟨by decide, by decide⟩, by decide, by decide⟩

theorem moveSlice_impl : RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack
    (HL [TYP, 0, 0, 0] fun _ => True) moveSliceSpec := by
  fixed_impl
  simp only [moveSliceSpec] at ha ⊢
  rw [ha]
  simp [arg]

theorem moveSlice_satisfiable : Satisfiable moveSliceSpec :=
  sat_fixed _ _ _ _ moveSlice_impl rfl (by decide) (by decide)
    ⟨elemOK_w, by decide, by decide, by decide, by simp⟩
    (by simp [moveSliceSpec, arg, calleeStack, wstate, TYP, wsp, outside_zero]) rfl rfl trivial

theorem moveSliceNoCap_impl : RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack
    (HL [TYP, 0, 0] fun _ => True) moveSliceNoCapSpec := by
  fixed_impl
  simp only [moveSliceNoCapSpec] at ha ⊢
  rw [ha]
  simp [arg]

theorem moveSliceNoCap_satisfiable : Satisfiable moveSliceNoCapSpec :=
  sat_fixed _ _ _ _ moveSliceNoCap_impl rfl (by decide) (by decide)
    ⟨elemOK_w, by decide, by decide, by simp⟩
    (by simp [moveSliceNoCapSpec, arg, calleeStack, wstate, TYP, wsp, outside_zero]) rfl rfl trivial

theorem moveSliceNoCapNoScan_impl : RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack
    (HL [8, 0, 0] fun _ => True) moveSliceNoCapNoScanSpec := by
  fixed_impl
  simp only [moveSliceNoCapNoScanSpec] at ha ⊢
  rw [ha]
  simp [arg]

theorem moveSliceNoCapNoScan_satisfiable : Satisfiable moveSliceNoCapNoScanSpec :=
  sat_fixed _ _ _ _ moveSliceNoCapNoScan_impl rfl (by decide) (by decide)
    ⟨by decide, by decide, by decide, by simp⟩
    (by simp [moveSliceNoCapNoScanSpec, arg, outside_zero]) rfl rfl trivial

theorem typedslicecopy_impl : RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack
    (HL [TYP, 0, 0, 0, 0] fun _ => True) typedslicecopySpec := by
  fixed_impl
  simp only [typedslicecopySpec] at ha ⊢
  rw [ha]
  simp [arg, Copied]

theorem typedslicecopy_satisfiable : Satisfiable typedslicecopySpec :=
  sat_fixed _ _ _ _ typedslicecopy_impl rfl (by decide) (by decide)
    ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, by simp, by decide, by simp⟩
    (by simp [typedslicecopySpec, arg, calleeStack, wstate, TYP, wsp, outside_zero]) rfl rfl trivial

theorem makeslicecopy_impl : RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack
    (HL [TYP, 0, 0, 0] fun _ => True) makeslicecopySpec := by
  fixed_impl
  simp only [makeslicecopySpec] at ha ⊢
  rw [ha]
  simp [arg]

theorem makeslicecopy_satisfiable : Satisfiable makeslicecopySpec :=
  sat_fixed _ _ _ _ makeslicecopy_impl rfl (by decide) (by decide)
    ⟨elemOK_w, by decide, by decide, by decide, by decide, by simp⟩
    (by simp [makeslicecopySpec, arg, calleeStack, wstate, TYP, wsp, outside_zero]) rfl rfl trivial

theorem wbZero_impl : RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack
    (HL [TYP, HEAP] fun _ => True) wbZeroSpec := by
  fixed_impl

theorem wbZero_satisfiable : Satisfiable wbZeroSpec :=
  sat_fixed _ _ _ _ wbZero_impl rfl (by decide) (by decide)
    ⟨⟨by decide, by decide⟩, by decide, fun _ => by decide⟩
    (by simp [wbZeroSpec, arg, calleeStack, wstate, TYP, HEAP, wsp]) rfl rfl trivial

theorem wbMove_impl : RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack
    (HL [TYP, HEAP, HEAP] fun _ => True) wbMoveSpec := by
  fixed_impl

theorem wbMove_satisfiable : Satisfiable wbMoveSpec :=
  sat_fixed _ _ _ _ wbMove_impl rfl (by decide) (by decide)
    ⟨⟨by decide, by decide⟩, ⟨by decide, fun _ => by decide⟩, ⟨by decide, fun _ => by decide⟩⟩
    (by simp [wbMoveSpec, arg, calleeStack, wstate, TYP, HEAP, wsp]) rfl rfl trivial

/-! ## A rune, a C string -/

theorem intstring_impl : RtContract (toy.link (at0 (constCode HEAP 1 0))) A0 rtW wstack
    (HL [0, 0] fun v => v.accessible HEAP 1 false = true ∧ v.bytes HEAP = 0) intstringSpec := by
  fixed_impl
  simp only [intstringSpec] at ha ⊢
  rw [ha]
  rw [rtView_accessible] at hP
  have hb := hP.2
  rw [rtView_bytes (heap_inRanges 1 (by decide))] at hb
  have he : encodeRune (intRune (BitVec.ofNat 64 0)) = [0] := by decide
  simp only [show ([0, 0] : List Nat)[1]?.getD 0 = 0 from rfl, he]
  simp only [HEAP] at hP hb
  refine ⟨rfl, hP.1, ?_⟩
  simp [strBytes, hb]

theorem intstring_satisfiable : Satisfiable intstringSpec :=
  sat_fixed _ _ _ _ intstring_impl rfl (by decide) (by decide) (Or.inl rfl)
    (by simp [intstringSpec]) rfl rfl ⟨by decide, by decide⟩

theorem gostring_impl : RtContract (toy.link (at0 (constCode 0 0 0))) A0 rtW wstack
    (HL [HEAP] fun v => (v.bytes HEAP).toNat = 0) gostringSpec := by
  fixed_impl
  simp only [gostringSpec] at ha ⊢
  rw [ha]
  have hb := hP
  rw [rtView_bytes (heap_inRanges 1 (by decide))] at hb
  intro l hl
  have hl0 : l = 0 := by
    rcases Nat.eq_zero_or_pos l with h | h
    · exact h
    · exact absurd (by simpa using hb) (hl.2.2.1 0 h)
  subst hl0
  simp [StrOut, strBytes]

theorem gostring_satisfiable : Satisfiable gostringSpec :=
  sat_fixed _ _ _ _ gostring_impl rfl (by decide) (by decide)
    ⟨0, by decide, by decide, fun i h => absurd h (Nat.not_lt_zero i), by decide⟩
    (by simp [gostringSpec, arg, calleeStack, wstate, HEAP, wsp]) rfl rfl (by decide)

/-! ## Growing a slice (a fresh array) -/

/-- What the growth witnesses need of the runtime: the descriptor's `Size_ = 8`, `PtrBytes = 0`,
and 8 writable heap bytes. -/
def PGrow (v : Memory) : Prop :=
  v.readLE TYP 8 = 8 ∧ v.readLE (TYP + 8) 8 = 0 ∧ v.accessible HEAP 8 true = true

theorem growCap_w : growCap 8 true 1 0 = 1 := by decide

theorem grown_w (m : Memory) (hP : PGrow (rtView rtW m)) :
    GrownArray rtW m m 0 0 1 (typSize m TYP) (typNoscan m TYP) HEAP 1 := by
  obtain ⟨h1, h2, h3⟩ := hP
  rw [typSize_of m h1]
  rw [rtView_accessible] at h3
  exact ⟨heap_inRanges _ (by decide), by decide, h3, fun i h => absurd h (by omega), fun i h => absurd h (by omega),
    fun h => by simp [typNoscan, typPtrBytes_of m h2] at h⟩

theorem growslice_impl : RtContract (toy.link (at0 (constCode HEAP 1 1))) A0 rtW wstack
    (HL [0, 1, 0, 1, TYP] PGrow) growsliceSpec := by
  fixed_impl
  simp only [growsliceSpec] at ha ⊢
  rw [ha]
  have hg := grown_w s.mem hP
  have h1 := typSize_of s.mem hP.1
  have h2 := typPtrBytes_of s.mem hP.2.1
  simp only [typSize, typPtrBytes, typNoscan] at h1 h2 hg
  simp only [show ([0, 1, 0, 1, TYP] : List Nat)[4]?.getD 0 = TYP from rfl,
    show ([0, 1, 0, 1, TYP] : List Nat)[1]?.getD 0 = 1 from rfl,
    show ([0, 1, 0, 1, TYP] : List Nat)[2]?.getD 0 = 0 from rfl,
    show ([0, 1, 0, 1, TYP] : List Nat)[3]?.getD 0 = 1 from rfl,
    show ([0, 1, 0, 1, TYP] : List Nat)[0]?.getD 0 = 0 from rfl, h1, h2] at hg ⊢
  exact ⟨trivial, growCap_w.symm, hg⟩

theorem growslice_pre_w : growsliceSpec.pre [0, 1, 0, 1, TYP] wmem :=
  ⟨elemOK_w, by decide, by decide, by decide, by decide, by simp [Readable]⟩

theorem pgrow_w : PGrow (rtView rtW wmem) := ⟨by decide, by decide, by decide⟩

theorem growslice_satisfiable : Satisfiable growsliceSpec :=
  sat_fixed _ _ _ _ growslice_impl rfl (by decide) (by decide) growslice_pre_w
    (by simp [growsliceSpec, arg, calleeStack, wstate, TYP, wsp, outside_zero]) rfl rfl pgrow_w

theorem growsliceNoAlias_satisfiable : Satisfiable growsliceNoAliasSpec := growslice_satisfiable

theorem growsliceBuf_impl : RtContract (toy.link (at0 (constCode HEAP 1 1))) A0 rtW wstack
    (HL [0, 1, 0, 1, TYP, 0, 0] PGrow) growsliceBufSpec := by
  fixed_impl
  simp only [growsliceBufSpec, growsliceSpec] at ha ⊢
  rw [ha]
  have hg := grown_w s.mem hP
  have h1 := typSize_of s.mem hP.1
  have h2 := typPtrBytes_of s.mem hP.2.1
  simp only [typSize, typPtrBytes, typNoscan] at h1 h2 hg
  simp only [show ([0, 1, 0, 1, TYP, 0, 0] : List Nat)[4]?.getD 0 = TYP from rfl,
    show ([0, 1, 0, 1, TYP, 0, 0] : List Nat)[1]?.getD 0 = 1 from rfl,
    show ([0, 1, 0, 1, TYP, 0, 0] : List Nat)[2]?.getD 0 = 0 from rfl,
    show ([0, 1, 0, 1, TYP, 0, 0] : List Nat)[3]?.getD 0 = 1 from rfl,
    show ([0, 1, 0, 1, TYP, 0, 0] : List Nat)[6]?.getD 0 = 0 from rfl,
    show ([0, 1, 0, 1, TYP, 0, 0] : List Nat)[0]?.getD 0 = 0 from rfl, h1, h2] at hg ⊢
  exact ⟨fun _ => ⟨trivial, growCap_w.symm, hg⟩, fun h => absurd h (by decide)⟩

theorem growsliceBuf_satisfiable : Satisfiable growsliceBufSpec :=
  sat_fixed _ _ _ _ growsliceBuf_impl rfl (by decide) (by decide)
    ⟨growslice_pre_w, fun h => absurd h (by decide)⟩
    (by simp [growsliceBufSpec, arg, calleeStack, wstate, TYP, wsp, outside_zero]) rfl rfl pgrow_w

theorem growsliceBufNoAlias_satisfiable : Satisfiable growsliceBufNoAliasSpec := growsliceBuf_satisfiable

/-! ## Allocation (`Janus.Contracts.Alloc`) -/

/-- The return of a constant implementation as `AllocRet`, with `ptr` the returned `X0`. -/
theorem allocRet_const {rt : List (Nat × Nat)} {stack nargs : Nat} {res : W64 → List W64}
    {s s' : State} {Q : Memory → Nat → Prop}
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18)
    (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid)
    (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr) (hfs : s'.fpsr = s.fpsr)
    (hm : s'.mem = s.mem)
    (hres : ∀ i, i < (res (s'.regs 0)).length → (res (s'.regs 0)).getD i 0 = s'.regs i)
    (hq : Q s.mem (s'.regs 0).toNat) : AllocRet rt stack nargs res s s' Q := by
  refine ⟨s'.regs 0, s'.regs, s'.flags, s'.vregs, s.mem, ?_, MemFrame.refl _ _, hq⟩
  obtain ⟨r, sp', pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc h18 h28 h29 hdz htp hfc hfs hm hres hq ⊢
  subst hsp hpc hdz htp hfc hfs hm
  simp only [retState, State.mk.injEq, and_true]
  funext i
  simp only [callRegs]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · by_cases hl : i < (res (r 0)).length
    · rw [← hres i hl]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- What the allocation witnesses need of the runtime: the descriptor (`Size_ = 8`,
`PtrBytes = 0`) and `n` writable zero heap bytes. -/
def PHeap (n : Nat) (v : Memory) : Prop :=
  v.readLE TYP 8 = 8 ∧ v.readLE (TYP + 8) 8 = 0 ∧ v.accessible HEAP n true = true ∧ ZeroBytes v HEAP n

theorem pheap_w (n : Nat) (hn : n ≤ 16) : PHeap n (rtView rtW wmem) := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · rw [rtView_accessible]; exact Memory.accessible_mono _ (show wmem.accessible HEAP 0x10000 true = true by decide)
      (Nat.le_refl _) (by simp [HEAP]; omega)
  · intro i hi
    rw [rtView_bytes (heap_inRanges 16 (by decide) |>.sub (by simp [HEAP]) (by simp [HEAP]; omega))]
    simp only [wmem]
    split
    · rename_i h; simp only [HEAP, TYP] at h; omega
    · rfl

/-- The heap block a witness allocator returns: `n` writable zero bytes at `HEAP`, 16-aligned. -/
theorem fresh_w (m : Memory) (n round : Nat) (hn : n ≤ round) (hr : round ≤ 16) (z hdr : Bool)
    (hP : PHeap round (rtView rtW m)) : Fresh rtW m HEAP n round z hdr := by
  obtain ⟨-, -, hacc, hz⟩ := hP
  rw [rtView_accessible] at hacc
  refine ⟨heap_inRanges _ (by omega), by simp [HEAP]; omega, hacc, fun _ => by decide, fun _ _ => by decide,
    fun _ => ?_, hn⟩
  intro i hi
  have := ZeroBytes.of_rtView hz (heap_inRanges _ (by omega))
  exact this i (by omega)

/-- The arguments of an arm64 call (`X0, X1, …`) of the witness state: `args`. -/
theorem wregs (L : List Nat) (i : Nat) (hi : i ≠ 28 ∧ i ≠ 30) :
    (wstate (args L)).regs i = BitVec.ofNat 64 (L.getD i 0) := by
  simp [wstate, args, hi.1, hi.2]

/-- `CallOK`, the frame and the ABI facts are those of `wstate`. -/
theorem mallocgc_impl : MallocgcContract (toy.link (at0 (constCode HEAP 0 0))) A0 rtW wstack
    (fun a _ _ v => a = [16, 0, 1] ∧ PHeap 16 v) := by
  rw [link_at0]
  rintro s hpc ⟨⟨⟨h30a, h30b, -⟩, -⟩, ha, hP⟩
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨h0, h1, h2⟩ := ha
  janus_run
  apply allocRet_const <;> (try rfl) <;> (try simp [setReg])
  intro _
  have hb : blockSize 16 true = 16 := by decide
  simp only [mallocgcObj, h0, h1, h2]
  simpa [hb, mallocHdr, HEAP] using fresh_w s.mem 16 16 (by decide) (by decide) true false hP

theorem mallocgc_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Segment),
    MallocgcContract (toy.link impl) A0 rt wstack H ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      MallocgcPre wstack s ∧ Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s :=
  ⟨rtW, _, _, mallocgc_impl, wstate (args [16, 0, 1]), rfl,
    ⟨wstate_callOK _ 3 (by decide), by simp [wstate, args, TYP, maxAlloc], Or.inl (by simp [wstate, args, TYP, maxAlloc])⟩,
    ⟨by simp [wstate, args, TYP, maxAlloc], pheap_w 16 (by decide)⟩⟩

theorem newobject_impl : NewobjectContract (toy.link (at0 (constCode HEAP 0 0))) A0 rtW wstack
    (fun a _ _ v => a = [TYP] ∧ PHeap 8 v) := by
  rw [link_at0]
  rintro s hpc ⟨⟨⟨h30a, h30b, -⟩, -⟩, ha, hP⟩
  simp only [List.cons.injEq, and_true] at ha
  janus_run
  apply allocRet_const <;> (try rfl) <;> (try simp [setReg])
  intro _
  have h1 := typSize_of s.mem hP.1
  have h2 := typPtrBytes_of s.mem hP.2.1
  have hb : blockSize 8 true = 8 := by decide
  simp only [newobjectObj, ha, h1, typNoscan, typPtrBytes] at h2 ⊢
  simpa [hb, h2, mallocHdr, HEAP] using fresh_w s.mem 8 8 (by decide) (by decide) true false hP

theorem newobject_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Segment),
    NewobjectContract (toy.link impl) A0 rt wstack H ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      NewobjectPre wstack s ∧ Ready H rt [(s.regs 0).toNat] s :=
  ⟨rtW, _, _, newobject_impl, wstate (args [TYP]), rfl,
    ⟨wstate_callOK _ 1 (by decide), by simp [wstate, args, TYP, maxAlloc]; exact ⟨by decide, by decide⟩,
      by simp [wstate, args, TYP, maxAlloc]; decide⟩,
    ⟨by simp [wstate, args, TYP, maxAlloc], pheap_w 8 (by decide)⟩⟩

theorem makeslice_impl : MakesliceContract (toy.link (at0 (constCode HEAP 0 0))) A0 rtW wstack
    (fun a _ _ v => a = [TYP, 1, 1] ∧ PHeap 8 v) := by
  rw [link_at0]
  rintro s hpc ⟨⟨⟨h30a, h30b, -⟩, -⟩, ha, hP⟩
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨h0, h1, h2⟩ := ha
  janus_run
  apply allocRet_const <;> (try rfl) <;> (try simp [setReg])
  intro _
  have ht := typSize_of s.mem hP.1
  have hpb := typPtrBytes_of s.mem hP.2.1
  have hb : blockSize 8 true = 8 := by decide
  simp only [makesliceObj, h0, h2, ht, typNoscan, typPtrBytes] at hpb ⊢
  simpa [hb, hpb, mallocHdr, HEAP] using fresh_w s.mem 8 8 (by decide) (by decide) true false hP

theorem makeslice_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Segment),
    MakesliceContract (toy.link impl) A0 rt wstack H ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      MakeslicePre wstack s ∧ Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s :=
  ⟨rtW, _, _, makeslice_impl, wstate (args [TYP, 1, 1]), rfl,
    ⟨wstate_callOK _ 3 (by decide), by simp [wstate, args, TYP, maxAlloc]; exact ⟨by decide, by decide⟩,
      by simp [wstate, args, TYP, maxAlloc], by simp [wstate, args, TYP, maxAlloc], by simp [wstate, args, TYP, maxAlloc]; decide⟩,
    ⟨by simp [wstate, args, TYP, maxAlloc], pheap_w 8 (by decide)⟩⟩

theorem growslice8_impl : GrowsliceContract (toy.link (at0 (constCode HEAP 1 1))) A0 rtW wstack
    (fun a _ _ v => a = [0, 1, 0, 1, TYP] ∧ PHeap 8 v) := by
  rw [link_at0]
  rintro s hpc ⟨⟨⟨⟨h30a, h30b, -⟩, -⟩, -⟩, ha, hP⟩
  simp only [growsliceArgs, List.cons.injEq, and_true] at ha
  obtain ⟨h0, h1, h2, h3, h4⟩ := ha
  janus_run
  apply allocRet_const <;> (try rfl) <;> (try simp [setReg])
  · intro i hi
    try simp only [List.length_cons, List.length_nil] at hi
    have h1' : s.regs 1 = 1#64 := by apply BitVec.eq_of_toNat_eq; simp [h1]
    have h2' : s.regs 2 = 0#64 := by apply BitVec.eq_of_toNat_eq; simp [h2]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> simp [h1', h2'] <;> decide
  · simp only [growsliceObj, h0, h1, h2, h3]
    have hg : growCap8 1 0 = 1 := by decide
    refine ⟨by simpa [hg, HEAP] using fresh_w s.mem 8 8 (by decide) (by decide) false false hP,
      fun i h => absurd h (by omega), fun i h => absurd h (by simp [hg])⟩

theorem growslice8_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Segment),
    GrowsliceContract (toy.link impl) A0 rt wstack H ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      GrowslicePre wstack s ∧ Ready H rt (growsliceArgs s) s :=
  ⟨rtW, _, _, growslice8_impl, wstate (args [0, 1, 0, 1, TYP]), rfl,
    ⟨⟨wstate_callOK _ 5 (by decide), by simp [wstate, args, TYP, maxAlloc]; exact ⟨by decide, by decide⟩,
      by simp [wstate, args, TYP, maxAlloc]; decide, by simp [wstate, args, TYP, maxAlloc]; decide, by simp [wstate, args, TYP, maxAlloc],
      by simp [wstate, args, TYP, maxAlloc], by simp [wstate, args, TYP, maxAlloc], by simp [wstate, args, TYP, maxAlloc]⟩,
      fun h => absurd h (by simp [wstate, args, TYP, maxAlloc])⟩,
    ⟨by simp [wstate, args, TYP, maxAlloc], pheap_w 8 (by decide)⟩⟩

/-! ## The write barrier (`gcWriteBarrierN`) -/

/-- `X25 = HEAP; RET`. -/
def wbCode : List Nat := movc 25 HEAP ++ [retW]

theorem wb_impl (n : Nat) (hn : n ≤ 8) : WbContract (toy.link (at0 wbCode)) A0 rtW wstack
    (fun a _ _ v => a = [n] ∧ v.accessible HEAP (8 * n) true = true) n := by
  rw [link_at0]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, hP⟩
  janus_run
  refine ⟨BitVec.ofNat 64 HEAP, s.regs, s.flags, s.vregs, s.mem, ?_, MemFrame.refl _ _, ?_⟩
  · simp only [State.mk.injEq, and_true]
    funext i
    simp only [setReg, wbRegs]
    split
    · rfl
    · split <;> rfl
  · rw [rtView_accessible] at hP
    exact ⟨heap_inRanges _ (by omega), by simp [HEAP]; omega, by simpa [HEAP] using hP, by decide⟩

theorem wb_heap_w (n : Nat) (hn : n ≤ 8) : (rtView rtW wmem).accessible HEAP (8 * n) true = true := by
  rw [rtView_accessible]
  have h : wmem.accessible HEAP 0x10000 true = true := by decide
  exact Memory.accessible_mono _ h (Nat.le_refl _) (by simp [HEAP]; omega)

theorem wb_satisfiable (n : Nat) (hn : n ≤ 8) : ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Segment),
    WbContract (toy.link impl) A0 rt wstack H n ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      CallOK s wstack 0 ∧ Ready H rt [n] s :=
  ⟨rtW, _, _, wb_impl n hn, wstate (args []), rfl, wstate_callOK _ 0 (by decide), rfl,
    wb_heap_w n hn⟩

end Janus.Contracts.Sat
