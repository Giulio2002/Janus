import Janus.Contracts.Sat

/-!
# The runtime contracts are satisfiable (amd64)

As `Janus.Contracts.Sat` for the amd64 contracts (`RtContract64`, `MallocgcContract64`,
`NewobjectContract64`, `MakesliceContract64`, `GrowsliceContract64`, `WbContract64`): the same
model (`rtW`, `wmem`, the readiness predicates), x86-64 implementations at `A0`
(`constCode64`: `MOV EAX/EBX/ECX, imm32; RET`, `wbCode64`: `MOV R11D, imm32; RET`) proved by
running them, and a call state (`wstate64`) meeting each precondition.
-/

namespace Janus.Contracts.SatAmd64

open Janus.Amd64 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus (MemFrame InRanges Outside outside_cons outside_nil)
open Janus.Contracts.Sat (TYP HEAP wsp wg rtW wmem H0 HL strPairs_zero mem_strPairs_zero outside_zero
  roundupsize_zero PGrow PHeap typSize_of typPtrBytes_of typ_inRanges heap_inRanges elemOK_w growCap_w grown_w
  pheap_w fresh_w growslice_pre_w pgrow_w)

/-- A program with no code, stubs or data of its own. -/
def toy : Janus.Amd64.Program := { segments := [], stubs := [], exitAddr := 0 }

/-- Where the model implementations are placed. -/
def A0 : Nat := 0x100000

/-- An implementation: the bytes `bs` at `A0`. -/
def at0 (bs : List Nat) : List Janus.Amd64.Segment := [{ name := "model", base := A0, bytes := bs }]

/-- `toy` with the implementation `bs`, as a program of its own. -/
def withCode (bs : List Nat) : Janus.Amd64.Program := { segments := at0 bs, stubs := [], exitAddr := 0 }

theorem link_at0 (bs : List Nat) : toy.link (at0 bs) = withCode bs := rfl

/-- The 4 little-endian bytes of `c`. -/
def le32 (c : Nat) : List Nat := [c % 256, c / 256 % 256, c / 65536 % 256, c / 16777216 % 256]
/-- `MOV EAX, c0; MOV EBX, c1; MOV ECX, c2; RET` (the 32-bit moves zero the upper halves). -/
def constCode64 (c0 c1 c2 : Nat) : List Nat :=
  [0xB8] ++ le32 c0 ++ [0xBB] ++ le32 c1 ++ [0xB9] ++ le32 c2 ++ [0xC3]

/-- The register of argument word `i` (`argReg`), inverted: the argument index of register `r`
(9 for a register that carries none). -/
def argIdx (r : Nat) : Nat :=
  if r = 0 then 0 else if r = 3 then 1 else if r = 1 then 2 else if r = 7 then 3 else if r = 6 then 4
  else if r = 8 then 5 else if r = 9 then 6 else if r = 10 then 7 else if r = 11 then 8 else 9

/-- Argument registers holding the words `L`. -/
def args (L : List Nat) : Nat → W64 := fun r => BitVec.ofNat 64 (L.getD (argIdx r) 0)

/-- The witness call state: `RSP = wsp` (its word, the return address, is `0`), `R14 = wg`,
arguments `r`, memory `wmem`. -/
def wstate (r : Nat → W64) : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else r i,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := wmem }

/-- The stack window of every witness contract. -/
abbrev wstack : Nat := 64

theorem wstate_callOK (r : Nat → W64) (n : Nat) (hn : n ≤ 16) : CallOK64 (wstate r) wstack n := by
  have hw : wmem.accessible (wsp - 0x2000) 0x2100 true = true := by decide
  simp only [CallOK64, wstate, wstack, wsp, BitVec.toNat_ofNat, ite_true, ite_false, Nat.reduceEqDiff]
  refine ⟨by decide, by decide, by decide, by omega, ?_⟩
  exact Janus.Arm64.Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)

theorem reg_args (L : List Nat) (j : Nat) (hj : j < 9) (hl : ∀ x ∈ L, x < 2 ^ 64) :
    ((wstate (args L)).regs (GoABI.argReg j)).toNat = L.getD j 0 := by
  have hb : ∀ k, (L.getD k 0) < 2 ^ 64 := by
    intro k
    cases h : L[k]? with
    | none => simp [List.getD_eq_getElem?_getD, h]
    | some x => simp only [List.getD_eq_getElem?_getD, h, Option.getD_some]; exact hl x (List.mem_of_getElem? h)
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [wstate, args, GoABI.argReg, GoABI.intArgRegs, argIdx, List.getD_cons_zero, List.getD_cons_succ]
    simp only [Nat.reduceEqDiff, ite_true, ite_false, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (hb _)

theorem argWords_args (L : List Nat) (n : Nat) (hn : n ≤ 9) (hl : ∀ x ∈ L, x < 2 ^ 64) :
    argWords64 (wstate (args L)) n = (List.range n).map fun i => L.getD i 0 := by
  unfold argWords64
  suffices h : ∀ n k, k + n ≤ 9 → wordsFrom (fun i => if i < 9 then ((wstate (args L)).regs (GoABI.argReg i)).toNat
      else (wstate (args L)).mem.readLE (((wstate (args L)).regs 4).toNat + 8 + 8 * (i - 9)) 8) k n =
      (List.range' k n).map fun i => L.getD i 0 by
    rw [h n 0 (by omega), List.range_eq_range']
  intro n
  induction n with
  | zero => intro k _; rfl
  | succ n ih =>
    intro k hk
    rw [wordsFrom_succ, ih (k + 1) (by omega), List.range'_succ, List.map_cons, if_pos (by omega),
      reg_args L k (by omega) hl]

theorem readLE_zero_of (m : Janus.Arm64.Memory) (a n : Nat) (h : ∀ i, i < n → m.bytes (a + i) = 0) :
    m.readLE a n = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have h0 : m.bytes a = 0 := by simpa using h 0 (by omega)
    rw [Janus.Arm64.Memory.readLE_succ, h0, ih (a + 1) (fun i hi => by
      rw [show a + 1 + i = a + (i + 1) by omega]; exact h _ (by omega))]
    rfl

theorem readLE_wmem_zero (a n : Nat) (h : a + n ≤ TYP ∨ TYP + 1 ≤ a) : wmem.readLE a n = 0 :=
  readLE_zero_of _ _ _ fun i hi => by
    simp only [wmem]
    split
    · rename_i h'; omega
    · rfl

/-- The zero-operand witness's argument words (also the stack words, which `wmem` holds as 0). -/
theorem args_zero (n j : Nat) (hn : n ≤ 16) : arg (argWords64 (wstate (args [])) n) j = 0 := by
  unfold argWords64
  suffices h : ∀ n k, k + n ≤ 16 → ∀ x ∈ wordsFrom (fun i => if i < 9 then ((wstate (args [])).regs (GoABI.argReg i)).toNat
      else (wstate (args [])).mem.readLE (((wstate (args [])).regs 4).toNat + 8 + 8 * (i - 9)) 8) k n, x = 0 by
    simp only [arg, List.getD_eq_getElem?_getD]
    cases hx : (wordsFrom _ 0 n)[j]? with
    | none => rfl
    | some x => exact h n 0 (by omega) x (List.mem_of_getElem? hx)
  intro n
  induction n with
  | zero => intro k _ x hx; simp [wordsFrom] at hx
  | succ n ih =>
    intro k hk x hx
    rw [wordsFrom_succ, List.mem_cons] at hx
    rcases hx with rfl | hx
    · split
      · rename_i hk'
        have := reg_args [] k hk' (by simp)
        simpa using this
      · simp only [wstate, wsp, BitVec.toNat_ofNat]
        exact readLE_wmem_zero _ _ (by simp [TYP]; omega)
    · exact ih _ (by omega) _ hx

/-- The return of a constant implementation as `RtPost64`. -/
theorem rtPost_const {rt : List (Nat × Nat)} {sp : RtSpec} {s s' : State}
    (hrip : s'.rip = retAddrOf s) (h4 : s'.regs 4 = s.regs 4 + 8#64) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr = s.mxcsr) (hm : s'.mem = s.mem)
    (hq : sp.post rt (argWords64 s sp.nargs) s.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat s.mem) :
    RtPost64 rt wstack sp s s' :=
  RtPost64.intro hrip h4 h5 h14 hx hfs hdf hmx (hm ▸ MemFrame.refl _ _) (hm ▸ hq)

/-- **A contract is satisfiable** (amd64). -/
def Satisfiable (sp : RtSpec) : Prop :=
  ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Janus.Amd64.Segment),
    RtContract64 (toy.link impl) A0 rt wstack H sp ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ RtPre64 rt wstack H sp s

/-! ## Concatenation -/

theorem concatstring_impl (k : Nat) :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 (concatstringSpec k) := by
  rw [link_at0]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, -, -, -, hH⟩
  have ha := hH rfl
  janus64_run
  apply rtPost_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  rw [strPairs_zero _ (by simpa [concatstringSpec, Ready64, H0] using ha)]
  simp [strBytes]

theorem concatstring_satisfiable (k : Nat) (hk : k ≤ 7) : Satisfiable (concatstringSpec k) := by
  have ha := fun j => args_zero (1 + 2 * k) j (by omega)
  refine ⟨rtW, H0, _, concatstring_impl k, wstate (args []), rfl,
    wstate_callOK _ _ (by simp [concatstringSpec]; omega), ⟨Or.inl (ha 0), ?_⟩, ?_,
    by simp [concatstringSpec], fun _ => ha⟩
  · intro x hx
    rw [mem_strPairs_zero _ ha _ _ _ hx]
    exact ⟨⟨by decide, by simp⟩, fun h => absurd (ha 0) h⟩
  · intro r hr
    rw [mem_strPairs_zero _ ha _ _ _ hr]
    exact outside_zero _

/-- The zero-operand witness of a spec with `n` argument words: `H0`, `constCode64 0 0 0`,
`wstate (args [])`, from the facts the spec needs. -/
theorem sat_zero (sp : RtSpec) (hn : sp.nargs ≤ 16)
    (himpl : RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 sp)
    (hpre : sp.pre (argWords64 (wstate (args [])) sp.nargs) wmem)
    (hreads : ∀ r ∈ sp.reads (argWords64 (wstate (args [])) sp.nargs) wmem,
      Outside r.1 r.2 (calleeStack64 (wstate (args [])) wstack sp.nargs))
    (hg : sp.guard = none) : Satisfiable sp :=
  ⟨rtW, H0, _, himpl, wstate (args []), rfl, wstate_callOK _ _ hn, hpre, hreads,
    by simp [hg], fun _ j => args_zero _ j hn⟩

set_option hygiene false in
/-- The tactic of every zero-operand implementation proof: run the code, then the spec's
postcondition with all operands 0 (`ha`). -/
macro "zero_impl" : tactic => `(tactic| (
  rw [link_at0]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, -, -, -, hH⟩
  have ha := hH rfl
  simp only [Ready64, H0, arg, List.getD_eq_getElem?_getD] at ha
  janus64_run
  apply rtPost_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])))

theorem concatstrings_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 concatstringsSpec := by
  zero_impl
  simp only [concatstringsSpec] at ha ⊢
  rw [ha 2]
  simp [strHdrs, catBytes, strBytes]

theorem concatstrings_satisfiable : Satisfiable concatstringsSpec := by
  have ha := fun j => args_zero 4 j (by decide)
  refine sat_zero _ (by decide) concatstrings_impl ?_ ?_ rfl
  · simp only [concatstringsSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    refine ⟨Or.inl rfl, by decide, by simp, by simp [StrsIn, strHdrs], by simp [Disjoint]⟩
  · simp only [concatstringsSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [strHdrs, outside_zero]

theorem concatbyte_impl (k : Nat) :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 (concatbyteSpec k) := by
  zero_impl
  simp only [concatbyteSpec] at ha ⊢
  rw [strPairs_zero _ ha]
  simp [CatBytesOut]

theorem concatbyte_satisfiable (k : Nat) (hk : k ≤ 7) : Satisfiable (concatbyteSpec k) := by
  have ha := fun j => args_zero (1 + 2 * k) j (by omega)
  refine sat_zero _ (by simp [concatbyteSpec]; omega) (concatbyte_impl k) ⟨Or.inl (ha 0), ?_⟩ ?_ rfl
  · intro x hx
    rw [mem_strPairs_zero _ ha _ _ _ hx]
    exact ⟨⟨by decide, by simp⟩, fun h => absurd (ha 0) h⟩
  · intro r hr
    rw [mem_strPairs_zero _ ha _ _ _ hr]
    exact outside_zero _

theorem concatbytes_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 concatbytesSpec := by
  zero_impl
  simp only [concatbytesSpec] at ha ⊢
  rw [ha 0, ha 2]
  simp [strHdrs, catBytes, CatBytesOut]

theorem concatbytes_satisfiable : Satisfiable concatbytesSpec := by
  have ha := fun j => args_zero 4 j (by decide)
  refine sat_zero _ (by decide) concatbytes_impl ?_ ?_ rfl
  · simp only [concatbytesSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    refine ⟨Or.inl rfl, by decide, by simp, by simp [StrsIn, strHdrs], by simp [Disjoint]⟩
  · simp only [concatbytesSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [strHdrs, outside_zero]

/-! ## Conversions -/

theorem slicebytetostring_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 slicebytetostringSpec := by
  zero_impl
  simp only [slicebytetostringSpec] at ha ⊢
  rw [ha 2]
  simp [strBytes]

theorem slicebytetostring_satisfiable : Satisfiable slicebytetostringSpec := by
  have ha := fun j => args_zero 3 j (by decide)
  refine sat_zero _ (by decide) slicebytetostring_impl ?_ ?_ rfl
  · simp only [slicebytetostringSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    exact ⟨Or.inl rfl, ⟨by decide, by simp⟩, fun h => absurd rfl h⟩
  · simp only [slicebytetostringSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [outside_zero]

theorem slicebytetostringtmp_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 slicebytetostringtmpSpec := by
  zero_impl
  simp only [slicebytetostringtmpSpec] at ha ⊢
  rw [ha 0, ha 1]
  simp [strBytes]

theorem slicebytetostringtmp_satisfiable : Satisfiable slicebytetostringtmpSpec := by
  have ha := fun j => args_zero 2 j (by decide)
  refine sat_zero _ (by decide) slicebytetostringtmp_impl ?_ ?_ rfl
  · simp only [slicebytetostringtmpSpec] at ha ⊢
    rw [ha 0, ha 1]
    exact ⟨by decide, by simp⟩
  · simp only [slicebytetostringtmpSpec] at ha ⊢
    rw [ha 0, ha 1]
    simp [outside_zero]

theorem stringtoslicebyte_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 stringtoslicebyteSpec := by
  zero_impl
  simp only [stringtoslicebyteSpec] at ha ⊢
  rw [ha 0, ha 2]
  simp [ToBytesOut, strBytes, roundupsize_zero]

theorem stringtoslicebyte_satisfiable : Satisfiable stringtoslicebyteSpec := by
  have ha := fun j => args_zero 3 j (by decide)
  refine sat_zero _ (by decide) stringtoslicebyte_impl ?_ ?_ rfl
  · simp only [stringtoslicebyteSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    exact ⟨Or.inl rfl, ⟨by decide, by simp⟩, fun h => absurd rfl h⟩
  · simp only [stringtoslicebyteSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [outside_zero]

theorem stringtoslicerune_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 stringtosliceruneSpec := by
  zero_impl
  simp only [stringtosliceruneSpec] at ha ⊢
  rw [ha 0, ha 2]
  simp [strBytes, runes, runesFrom, runesGo, roundupsize_zero]

theorem stringtoslicerune_satisfiable : Satisfiable stringtosliceruneSpec := by
  have ha := fun j => args_zero 3 j (by decide)
  refine sat_zero _ (by decide) stringtoslicerune_impl ?_ ?_ rfl
  · simp only [stringtosliceruneSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    exact ⟨Or.inl rfl, ⟨by decide, by simp⟩, by decide, fun h => absurd rfl h⟩
  · simp only [stringtosliceruneSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [outside_zero]

theorem slicerunetostring_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 slicerunetostringSpec := by
  zero_impl
  simp only [slicerunetostringSpec] at ha ⊢
  rw [ha 2]
  simp [strBytes, runeWords, encodeRunes]

theorem slicerunetostring_satisfiable : Satisfiable slicerunetostringSpec := by
  have ha := fun j => args_zero 4 j (by decide)
  refine sat_zero _ (by decide) slicerunetostring_impl ?_ ?_ rfl
  · simp only [slicerunetostringSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2]
    exact ⟨Or.inl rfl, ⟨by decide, by simp⟩, fun h => absurd rfl h⟩
  · simp only [slicerunetostringSpec] at ha ⊢
    rw [ha 1, ha 2]
    simp [outside_zero]

theorem gostringn_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 gostringnSpec := by
  zero_impl
  simp only [gostringnSpec] at ha ⊢
  rw [ha 1]
  simp [strBytes]

theorem gostringn_satisfiable : Satisfiable gostringnSpec := by
  have ha := fun j => args_zero 2 j (by decide)
  refine sat_zero _ (by decide) gostringn_impl ?_ ?_ rfl
  · simp only [gostringnSpec] at ha ⊢
    rw [ha 0, ha 1]
    exact ⟨by decide, by simp⟩
  · simp only [gostringnSpec] at ha ⊢
    rw [ha 0, ha 1]
    simp [outside_zero]

theorem gobytes_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 gobytesSpec := by
  zero_impl
  simp only [gobytesSpec] at ha ⊢
  rw [ha 1]
  simp

theorem gobytes_satisfiable : Satisfiable gobytesSpec := by
  have ha := fun j => args_zero 2 j (by decide)
  refine sat_zero _ (by decide) gobytes_impl ?_ ?_ rfl
  · simp only [gobytesSpec] at ha ⊢
    rw [ha 0, ha 1]
    exact ⟨⟨by decide, by simp⟩, by decide⟩
  · simp only [gobytesSpec] at ha ⊢
    rw [ha 0, ha 1]
    simp [outside_zero]

/-! ## Slices with empty operands -/

theorem moveSliceNoScan_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 moveSliceNoScanSpec := by
  zero_impl
  simp only [moveSliceNoScanSpec] at ha ⊢
  rw [ha 3]
  simp

theorem moveSliceNoScan_satisfiable : Satisfiable moveSliceNoScanSpec := by
  have ha := fun j => args_zero 4 j (by decide)
  refine sat_zero _ (by decide) moveSliceNoScan_impl ?_ ?_ rfl
  · simp only [moveSliceNoScanSpec] at ha ⊢
    rw [ha 0, ha 1, ha 2, ha 3]
    exact ⟨by decide, by decide, by decide, by simp⟩
  · simp only [moveSliceNoScanSpec] at ha ⊢
    rw [ha 0, ha 1, ha 3]
    simp [outside_zero]

theorem slicecopy_impl :
    RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack H0 slicecopySpec := by
  zero_impl
  simp only [slicecopySpec] at ha ⊢
  rw [ha 1, ha 3, ha 4]
  simp [Copied]

theorem slicecopy_satisfiable : Satisfiable slicecopySpec := by
  have ha := fun j => args_zero 5 j (by decide)
  refine sat_zero _ (by decide) slicecopy_impl ?_ ?_ rfl
  · simp only [slicecopySpec] at ha ⊢
    rw [ha 0, ha 1, ha 2, ha 3, ha 4]
    exact ⟨by decide, by decide, by decide, by simp, by decide, by simp⟩
  · simp only [slicecopySpec] at ha ⊢
    rw [ha 1, ha 2, ha 3, ha 4]
    simp [outside_zero]

/-! ## Fixed operands -/

theorem argWords_fixed (L : List Nat) (hn : L.length ≤ 9) (hl : ∀ x ∈ L, x < 2 ^ 64) :
    argWords64 (wstate (args L)) L.length = L := by
  rw [argWords_args L _ hn hl]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem sat_fixed (sp : RtSpec) (L : List Nat) (P : Memory → Prop) (code : List Nat)
    (himpl : RtContract64 (toy.link (at0 code)) A0 rtW wstack (HL L P) sp)
    (hlen : L.length = sp.nargs) (hn : sp.nargs ≤ 9) (hl : ∀ x ∈ L, x < 2 ^ 64)
    (hpre : sp.pre L wmem)
    (hreads : ∀ r ∈ sp.reads L wmem, Outside r.1 r.2 (calleeStack64 (wstate (args L)) wstack sp.nargs))
    (hg : sp.guard = none) (hP : P (rtView rtW wmem)) : Satisfiable sp := by
  have ha : argWords64 (wstate (args L)) sp.nargs = L := by
    rw [← hlen]; exact argWords_fixed L (by omega) hl
  refine ⟨rtW, HL L P, _, himpl, wstate (args L), rfl, wstate_callOK _ _ (by omega), ?_, ?_,
    by simp [hg], fun _ => ⟨ha, hP⟩⟩
  · rw [ha]; exact hpre
  · rw [ha]; exact hreads

set_option hygiene false in
/-- The tactic of every fixed-operand implementation proof. -/
macro "fixed_impl" : tactic => `(tactic| (
  rw [link_at0]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, -, -, -, hH⟩
  obtain ⟨ha, hP⟩ := hH rfl
  janus64_run
  apply rtPost_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])))

theorem moveSlice_impl : RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack
    (HL [TYP, 0, 0, 0] fun _ => True) moveSliceSpec := by
  fixed_impl
  simp only [moveSliceSpec] at ha ⊢
  rw [ha]
  simp [arg]

theorem moveSlice_satisfiable : Satisfiable moveSliceSpec :=
  sat_fixed _ _ _ _ moveSlice_impl rfl (by decide) (by decide)
    ⟨elemOK_w, by decide, by decide, by decide, by simp⟩
    (by simp [moveSliceSpec, arg, calleeStack64, wstate, TYP, wsp, outside_zero]) rfl trivial

theorem moveSliceNoCap_impl : RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack
    (HL [TYP, 0, 0] fun _ => True) moveSliceNoCapSpec := by
  fixed_impl
  simp only [moveSliceNoCapSpec] at ha ⊢
  rw [ha]
  simp [arg]

theorem moveSliceNoCap_satisfiable : Satisfiable moveSliceNoCapSpec :=
  sat_fixed _ _ _ _ moveSliceNoCap_impl rfl (by decide) (by decide)
    ⟨elemOK_w, by decide, by decide, by simp⟩
    (by simp [moveSliceNoCapSpec, arg, calleeStack64, wstate, TYP, wsp, outside_zero]) rfl trivial

theorem moveSliceNoCapNoScan_impl : RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack
    (HL [8, 0, 0] fun _ => True) moveSliceNoCapNoScanSpec := by
  fixed_impl
  simp only [moveSliceNoCapNoScanSpec] at ha ⊢
  rw [ha]
  simp [arg]

theorem moveSliceNoCapNoScan_satisfiable : Satisfiable moveSliceNoCapNoScanSpec :=
  sat_fixed _ _ _ _ moveSliceNoCapNoScan_impl rfl (by decide) (by decide)
    ⟨by decide, by decide, by decide, by simp⟩
    (by simp [moveSliceNoCapNoScanSpec, arg, outside_zero]) rfl trivial

theorem typedslicecopy_impl : RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack
    (HL [TYP, 0, 0, 0, 0] fun _ => True) typedslicecopySpec := by
  fixed_impl
  simp only [typedslicecopySpec] at ha ⊢
  rw [ha]
  simp [arg, Copied]

theorem typedslicecopy_satisfiable : Satisfiable typedslicecopySpec :=
  sat_fixed _ _ _ _ typedslicecopy_impl rfl (by decide) (by decide)
    ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, by simp, by decide, by simp⟩
    (by simp [typedslicecopySpec, arg, calleeStack64, wstate, TYP, wsp, outside_zero]) rfl trivial

theorem makeslicecopy_impl : RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack
    (HL [TYP, 0, 0, 0] fun _ => True) makeslicecopySpec := by
  fixed_impl
  simp only [makeslicecopySpec] at ha ⊢
  rw [ha]
  simp [arg]

theorem makeslicecopy_satisfiable : Satisfiable makeslicecopySpec :=
  sat_fixed _ _ _ _ makeslicecopy_impl rfl (by decide) (by decide)
    ⟨elemOK_w, by decide, by decide, by decide, by decide, by simp⟩
    (by simp [makeslicecopySpec, arg, calleeStack64, wstate, TYP, wsp, outside_zero]) rfl trivial

theorem wbZero_impl : RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack
    (HL [TYP, HEAP] fun _ => True) wbZeroSpec := by
  fixed_impl

theorem wbZero_satisfiable : Satisfiable wbZeroSpec :=
  sat_fixed _ _ _ _ wbZero_impl rfl (by decide) (by decide)
    ⟨⟨by decide, by decide⟩, by decide, fun _ => by decide⟩
    (by simp [wbZeroSpec, arg, calleeStack64, wstate, TYP, HEAP, wsp]) rfl trivial

theorem wbMove_impl : RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack
    (HL [TYP, HEAP, HEAP] fun _ => True) wbMoveSpec := by
  fixed_impl

theorem wbMove_satisfiable : Satisfiable wbMoveSpec :=
  sat_fixed _ _ _ _ wbMove_impl rfl (by decide) (by decide)
    ⟨⟨by decide, by decide⟩, ⟨by decide, fun _ => by decide⟩, ⟨by decide, fun _ => by decide⟩⟩
    (by simp [wbMoveSpec, arg, calleeStack64, wstate, TYP, HEAP, wsp]) rfl trivial

/-! ## A rune, a C string -/

theorem intstring_impl : RtContract64 (toy.link (at0 (constCode64 HEAP 1 0))) A0 rtW wstack
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
    (by simp [intstringSpec]) rfl ⟨by decide, by decide⟩

theorem gostring_impl : RtContract64 (toy.link (at0 (constCode64 0 0 0))) A0 rtW wstack
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
    (by simp [gostringSpec, arg, calleeStack64, wstate, HEAP, wsp]) rfl (by decide)

/-! ## Growing a slice (a fresh array) -/

theorem growslice_impl : RtContract64 (toy.link (at0 (constCode64 HEAP 1 1))) A0 rtW wstack
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

theorem growslice_satisfiable : Satisfiable growsliceSpec :=
  sat_fixed _ _ _ _ growslice_impl rfl (by decide) (by decide) growslice_pre_w
    (by simp [growsliceSpec, arg, calleeStack64, wstate, TYP, wsp, outside_zero]) rfl pgrow_w

theorem growsliceNoAlias_satisfiable : Satisfiable growsliceNoAliasSpec := growslice_satisfiable

theorem growsliceBuf_impl : RtContract64 (toy.link (at0 (constCode64 HEAP 1 1))) A0 rtW wstack
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
    (by simp [growsliceBufSpec, arg, calleeStack64, wstate, TYP, wsp, outside_zero]) rfl pgrow_w

theorem growsliceBufNoAlias_satisfiable : Satisfiable growsliceBufNoAliasSpec := growsliceBuf_satisfiable

/-! ## Allocation (`Janus.Contracts.AllocAmd64`) -/

/-- The return of a constant implementation as `AllocRet64`, with `ptr` the returned `RAX`;
the result words go to `RAX`, `RBX`, `RCX`. -/
theorem allocRet_const {rt : List (Nat × Nat)} {stack nargs : Nat} {res : W64 → List W64}
    {s s' : State} {Q : Memory → Nat → Prop}
    (hrip : s'.rip = retAddrOf s) (h4 : s'.regs 4 = s.regs 4 + 8#64) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr = s.mxcsr) (hm : s'.mem = s.mem)
    (hres : ∀ j, j < (res (s'.regs 0)).length → (res (s'.regs 0)).getD j 0 = s'.regs ([0, 3, 1].getD j 0))
    (hq : Q s.mem (s'.regs 0).toNat) : AllocRet64 rt stack nargs res s s' Q := by
  refine ⟨s'.regs 0, s'.regs, s'.flags, s'.xmm, s'.ymmHi, s.mem, ?_, MemFrame.refl _ _, hq⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx hm hres hq ⊢
  subst hrip hfs hdf hmx hm
  simp only [retState64, State.mk.injEq, and_true, true_and]
  have hg : ∀ j, (res (r 0)).getD j (r ([0, 3, 1].getD j 0)) = r ([0, 3, 1].getD j 0) := by
    intro j
    by_cases hl : j < (res (r 0)).length
    · rw [← hres j hl]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  constructor
  · funext i
    simp only [callRegs64]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · split
        · rename_i hi; subst hi; exact (hg 0).symm
        · split
          · rename_i hi; subst hi; exact (hg 1).symm
          · split
            · rename_i hi; subst hi; exact (hg 2).symm
            · rfl
  · funext i
    split
    · rename_i hi; subst hi; exact hx
    · rfl

set_option hygiene false in
/-- The run of a constant allocator (amd64). -/
macro "alloc_impl" : tactic => `(tactic| (
  rw [link_at0]
  rintro s hpc ⟨⟨⟨hra, hal, hsb, hsa, hacc⟩, -⟩, ha, hP⟩
  simp only [List.cons.injEq, and_true] at ha
  janus64_run
  apply allocRet_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])))

theorem mallocgc_impl : MallocgcContract64 (toy.link (at0 (constCode64 HEAP 0 0))) A0 rtW wstack
    (fun a _ _ v => a = [16, 0, 1] ∧ PHeap 16 v) := by
  alloc_impl
  obtain ⟨h0, h1, h2⟩ := ha
  intro _
  have hb : blockSize 16 true = 16 := by decide
  simp only [mallocgcObj64, h0, h1, h2]
  simpa [hb, mallocHdr, HEAP] using fresh_w s.mem 16 16 (by decide) (by decide) true false hP

theorem mallocgc_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Janus.Amd64.Segment),
    MallocgcContract64 (toy.link impl) A0 rt wstack H ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      MallocgcPre64 wstack s ∧ Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s :=
  ⟨rtW, _, _, mallocgc_impl, wstate (args [16, 0, 1]), rfl,
    ⟨wstate_callOK _ 3 (by decide), by simp [wstate, args, argIdx, maxAlloc],
      Or.inl (by simp [wstate, args, argIdx])⟩,
    ⟨by simp [wstate, args, argIdx], pheap_w 16 (by decide)⟩⟩

theorem newobject_impl : NewobjectContract64 (toy.link (at0 (constCode64 HEAP 0 0))) A0 rtW wstack
    (fun a _ _ v => a = [TYP] ∧ PHeap 8 v) := by
  alloc_impl
  intro _
  have h1 := typSize_of s.mem hP.1
  have h2 := typPtrBytes_of s.mem hP.2.1
  have hb : blockSize 8 true = 8 := by decide
  simp only [newobjectObj64, ha, h1, typNoscan, typPtrBytes] at h2 ⊢
  simpa [hb, h2, mallocHdr, HEAP] using fresh_w s.mem 8 8 (by decide) (by decide) true false hP

theorem newobject_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Janus.Amd64.Segment),
    NewobjectContract64 (toy.link impl) A0 rt wstack H ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      NewobjectPre64 wstack s ∧ Ready64 H rt [(s.regs 0).toNat] s :=
  ⟨rtW, _, _, newobject_impl, wstate (args [TYP]), rfl,
    ⟨wstate_callOK _ 1 (by decide), by simp [wstate, args, argIdx, TYP]; exact ⟨by decide, by decide⟩,
      by simp [wstate, args, argIdx, TYP, maxAlloc]; decide⟩,
    ⟨by simp [wstate, args, argIdx, TYP], pheap_w 8 (by decide)⟩⟩

theorem makeslice_impl : MakesliceContract64 (toy.link (at0 (constCode64 HEAP 0 0))) A0 rtW wstack
    (fun a _ _ v => a = [TYP, 1, 1] ∧ PHeap 8 v) := by
  alloc_impl
  obtain ⟨h0, h1, h2⟩ := ha
  intro _
  have ht := typSize_of s.mem hP.1
  have hpb := typPtrBytes_of s.mem hP.2.1
  have hb : blockSize 8 true = 8 := by decide
  simp only [makesliceObj64, h0, h2, ht, typNoscan, typPtrBytes] at hpb ⊢
  simpa [hb, hpb, mallocHdr, HEAP] using fresh_w s.mem 8 8 (by decide) (by decide) true false hP

theorem makeslice_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Janus.Amd64.Segment),
    MakesliceContract64 (toy.link impl) A0 rt wstack H ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      MakeslicePre64 wstack s ∧ Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s :=
  ⟨rtW, _, _, makeslice_impl, wstate (args [TYP, 1, 1]), rfl,
    ⟨wstate_callOK _ 3 (by decide), by simp [wstate, args, argIdx, TYP]; exact ⟨by decide, by decide⟩,
      by simp [wstate, args, argIdx], by simp [wstate, args, argIdx],
      by simp [wstate, args, argIdx, TYP, maxAlloc]; decide⟩,
    ⟨by simp [wstate, args, argIdx, TYP], pheap_w 8 (by decide)⟩⟩

theorem growslice8_impl : GrowsliceContract64 (toy.link (at0 (constCode64 HEAP 1 1))) A0 rtW wstack
    (fun a _ _ v => a = [0, 1, 0, 1, TYP] ∧ PHeap 8 v) := by
  rw [link_at0]
  rintro s hpc ⟨⟨⟨⟨hra, hal, hsb, hsa, hacc⟩, -⟩, -⟩, ha, hP⟩
  simp only [growsliceArgs64, List.cons.injEq, and_true] at ha
  obtain ⟨h0, h1, h2, h3, h4⟩ := ha
  janus64_run
  apply allocRet_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  · intro j hj
    try simp only [List.length_cons, List.length_nil] at hj
    have h1' : s.regs 3 = 1#64 := by apply BitVec.eq_of_toNat_eq; simp [h1]
    have h2' : s.regs 1 = 0#64 := by apply BitVec.eq_of_toNat_eq; simp [h2]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> simp [h1', h2'] <;> decide
  · simp only [growsliceObj64, h0, h1, h2, h3]
    have hg : growCap8 1 0 = 1 := by decide
    refine ⟨by simpa [hg, HEAP] using fresh_w s.mem 8 8 (by decide) (by decide) false false hP,
      fun i h => absurd h (by omega), fun i h => absurd h (by simp [hg])⟩

theorem growslice8_satisfiable : ∃ (rt : List (Nat × Nat)) (H : RtReady) (impl : List Janus.Amd64.Segment),
    GrowsliceContract64 (toy.link impl) A0 rt wstack H ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      GrowslicePre64 wstack s ∧ Ready64 H rt (growsliceArgs64 s) s :=
  ⟨rtW, _, _, growslice8_impl, wstate (args [0, 1, 0, 1, TYP]), rfl,
    ⟨⟨wstate_callOK _ 5 (by decide), by simp [wstate, args, argIdx, TYP]; exact ⟨by decide, by decide⟩,
      by simp [wstate, args, argIdx, TYP]; decide, by simp [wstate, args, argIdx, TYP]; decide,
      by simp [wstate, args, argIdx], by simp [wstate, args, argIdx], by simp [wstate, args, argIdx],
      by simp [wstate, args, argIdx]⟩,
      fun h => absurd h (by simp [wstate, args, argIdx])⟩,
    ⟨by simp [wstate, args, argIdx, TYP], pheap_w 8 (by decide)⟩⟩

/-! ## The write barrier (`gcWriteBarrierN`) -/

/-- `MOV R11D, HEAP; RET`. -/
def wbCode : List Nat := [0x41, 0xBB] ++ le32 HEAP ++ [0xC3]

theorem wb_impl (n : Nat) (hn : n ≤ 8) : WbContract64 (toy.link (at0 wbCode)) A0 rtW wstack
    (fun a _ _ v => a = [n] ∧ v.accessible HEAP (8 * n) true = true) n := by
  rw [link_at0]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, -, hP⟩
  janus64_run
  refine ⟨BitVec.ofNat 64 HEAP, s.flags, s.xmm, s.ymmHi, s.mem, ?_, MemFrame.refl _ _, ?_⟩
  · simp only [State.mk.injEq, and_true, true_and]
    constructor
    · funext i
      simp only [setRegF]
      by_cases h11 : i = 11
      · subst h11; simp [HEAP]
      · by_cases h4 : i = 4
        · subst h4; simp
        · simp [h11, h4]
    · funext i
      by_cases h : i = 15
      · subst h; rfl
      · simp [h]
  · rw [rtView_accessible] at hP
    exact ⟨heap_inRanges _ (by omega), by simp [HEAP]; omega, by simpa [HEAP] using hP, by decide⟩

theorem wb_satisfiable (n : Nat) (hn : n ≤ 8) : ∃ (rt : List (Nat × Nat)) (H : RtReady)
    (impl : List Janus.Amd64.Segment), WbContract64 (toy.link impl) A0 rt wstack H n ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ CallOK64 s wstack 0 ∧ Ready64 H rt [n] s :=
  ⟨rtW, _, _, wb_impl n hn, wstate (args []), rfl, wstate_callOK _ 0 (by decide), rfl,
    Janus.Contracts.Sat.wb_heap_w n hn⟩

end Janus.Contracts.SatAmd64
