import Janus.Contracts.Errorf
import Janus.Contracts.PoolSat

/-!
# The `fmt.errorf` live contract is satisfiable (arm64)

For `ErrorfLive` of `Janus.Contracts.Errorf`: machine code at the address `A0` of a program with no
other code, a proof by symbolic execution that it satisfies the contract for the toy bump-allocator
runtime `toyR` of `Janus.Contracts.LiveToy`, and a call state that satisfies the whole
precondition (`errorfLive_satisfiable`).

**The instance.** The witness is for the format `%w` alone (no `%d`) and the message bound
`B = 0`: the `%w` operand is an errorString with the empty text, so the message is empty. The
stub allocates the 32-byte `wrapError` from the toy's bump pointer and fills it in: an empty message,
the itab of the `err` field, and the `%w` operand's data word (loaded from the slice). The contract
for the `%d` verbs and for a message with bytes is not witnessed here: it needs a decimal and a
copy loop (see docs/RUNTIME-CONTRACTS.md, "fmt.Errorf").
-/

namespace Janus.Contracts.ErrorfSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Errorf Janus.Contracts.Toy Janus.Contracts.LiveSat
open Janus.Contracts.AllocSat (toy A0 at0 link_at0 withCode)

def tErr : Nat := 0x1111
def iErr : Nat := 0x2222
def tInt : Nat := 0x3333
def iWrap : Nat := 0x4444

/-- `movz x9, #BUMP>>16; ldr x1, [x9]; add x10, x1, #32; str x10, [x9]; str xzr, [x1]; str xzr, [x1, #8];
movz x11, #iErr; str x11, [x1, #16]; ldr x12, [x2, #8]; str x12, [x1, #24]; movz x0, #iWrap; ret`. -/
def code : List Nat :=
  [0xd2a00809, 0xf940044c, 0xf9400121, 0x9100802a, 0xf900012a, 0xf900003f, 0xf900043f, 0xd284444b,
   0xf900082b, 0xf9000c2c, 0xd2888880, 0xd65f03c0]

/-- The state `code` returns in. -/
def errFinal (s : State) : State :=
  { s with
    regs :=
      setReg
        (setReg
          (setReg
            (setReg (setReg (setReg s.regs 0 17476#64) 1 (BitVec.ofNat 64 (s.mem.readLE 4194304 8))) 9 4194304#64)
            10 (BitVec.ofNat 64 (s.mem.readLE 4194304 8) + 32#64))
          11 8738#64)
        12 (BitVec.ofNat 64 (s.mem.readLE (BitVec.toNat (s.regs 2) + 8) 8)),
    pc := s.regs 30,
    mem :=
      ((((s.mem.writeLE 4194304 8 (s.mem.readLE 4194304 8 + 32)).writeLE (s.mem.readLE 4194304 8) 8 0).writeLE
                (s.mem.readLE 4194304 8 + 8) 8 0).writeLE
            (s.mem.readLE 4194304 8 + 16) 8 8738).writeLE
        (s.mem.readLE 4194304 8 + 24) 8 (s.mem.readLE (BitVec.toNat (s.regs 2) + 8) 8) }

set_option maxRecDepth 20000 in
theorem code_run (s : State) (hpc : s.pc = BitVec.ofNat 64 A0) (h30 : (s.regs 30).toNat < 2 ^ 48)
    (h30' : (s.regs 30).toNat % 4 = 0) (hacB : s.mem.accessible BUMP 8 true = true)
    (hH : s.mem.accessible HEAP HSIZE true = true) (hp1 : 268435456 ≤ s.mem.readLE 4194304 8)
    (hp2 : s.mem.readLE 4194304 8 + 32 ≤ 536870912)
    (hS : s.mem.accessible ((s.regs 2).toNat + 8) 8 false = true) (hS2 : (s.regs 2).toNat + 16 ≤ 2 ^ 48) :
    ReachesRet (withCode code) (s.regs regLR) s (fun s' => s' = errFinal s) := by
  janus_run
  rfl

theorem errFinal_ret (s : State) :
    errFinal s = { s with regs := Map.keepABI s.regs (errFinal s).regs, mem := (errFinal s).mem, pc := s.regs 30 } := by
  simp only [errFinal]
  congr 1
  funext i
  simp only [Map.keepABI, setReg]
  by_cases h : i = 18 ∨ i = 28 ∨ i = 29
  · rw [if_pos h]; rcases h with rfl | rfl | rfl <;> simp
  · rw [if_neg h]

/-- The four stores into the new `wrapError` object. -/
def wr4 (m : Memory) (d v0 v1 v2 v3 : Nat) : Memory :=
  (((m.writeLE d 8 v0).writeLE (d + 8) 8 v1).writeLE (d + 16) 8 v2).writeLE (d + 24) 8 v3

theorem wr4_frame (m : Memory) {rs : List (Nat × Nat)} {d : Nat} (hin : InRanges d 32 rs) (v0 v1 v2 v3 : Nat) :
    MemFrame m (wr4 m d v0 v1 v2 v3) rs := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  exact ((((MemFrame.refl m rs).writeLE v0 hr (a := d) (k := 8) h1 (by omega)).writeLE v1 hr
    (a := d + 8) (k := 8) (by omega) (by omega)).writeLE v2 hr (a := d + 16) (k := 8) (by omega) (by omega)).writeLE
    v3 hr (a := d + 24) (k := 8) (by omega) (by omega)

theorem wr4_live {m m' : Memory} {L : List (Nat × Nat)} (h : LiveFrame m m' L []) {d : Nat}
    (hout : ∀ a, d ≤ a → Outside a 8 L) (v0 v1 v2 v3 : Nat) : LiveFrame m (wr4 m' d v0 v1 v2 v3) L [] :=
  (((h.writeLE v0 (hout d (Nat.le_refl _))).writeLE v1 (hout (d + 8) (by omega))).writeLE v2
    (hout (d + 16) (by omega))).writeLE v3 (hout (d + 24) (by omega))

theorem wr4_view (rt L : List (Nat × Nat)) (m : Memory) {d : Nat} (hin : InRanges d 32 L) (v0 v1 v2 v3 : Nat) :
    view rt L (wr4 m d v0 v1 v2 v3) = view rt L m := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  unfold wr4
  rw [view_writeLE_live ⟨r, hr, by omega, by omega⟩, view_writeLE_live ⟨r, hr, by omega, by omega⟩,
    view_writeLE_live ⟨r, hr, by omega, by omega⟩, view_writeLE_live ⟨r, hr, by omega, by omega⟩]

theorem wr4_acc (m : Memory) (d v0 v1 v2 v3 a n : Nat) (w : Bool) :
    (wr4 m d v0 v1 v2 v3).accessible a n w = m.accessible a n w := by
  simp [wr4]

theorem wr4_r0 (m : Memory) (d v0 v1 v2 v3 : Nat) : (wr4 m d v0 v1 v2 v3).readLE d 8 = v0 % 256 ^ 8 := by
  unfold wr4
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]

theorem wr4_r1 (m : Memory) (d v0 v1 v2 v3 : Nat) : (wr4 m d v0 v1 v2 v3).readLE (d + 8) 8 = v1 % 256 ^ 8 := by
  unfold wr4
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Memory.readLE_writeLE_self]

theorem wr4_r2 (m : Memory) (d v0 v1 v2 v3 : Nat) : (wr4 m d v0 v1 v2 v3).readLE (d + 16) 8 = v2 % 256 ^ 8 := by
  unfold wr4
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]

theorem wr4_r3 (m : Memory) (d v0 v1 v2 v3 : Nat) : (wr4 m d v0 v1 v2 v3).readLE (d + 24) 8 = v3 % 256 ^ 8 := by
  unfold wr4
  rw [Memory.readLE_writeLE_self]

set_option maxRecDepth 20000 in
theorem errorf_impl (ok : Nat → List Nat → Prop) :
    ErrorfLive (toy.link (at0 code)) A0 4096 (toyR tys0 ok) tErr iErr tInt iWrap 2 0x7725 0 := by
  rw [link_at0]
  intro L b s hpc ⟨⟨h30a, h30b, hsp16, hst1, hst2, hst3, hacc⟩, hguard, hargs, hreads, hsafe, hok, hinv, hcost, hLs, hWs⟩
  obtain ⟨hFl, hFm, hsome, hsl, hsc, hF, hSl, hT0, hD0, hE, hTxt, hints, hlen, hB⟩ := hargs
  have hlen0 : (msgOf s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat).length = 0 := by omega
  have hcost32 : errorfCost s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat = 32 := by
    simp [errorfCost, hlen0, wrapBytes]
  rw [hcost32] at hcost
  have hinvT : toyInv tys0 b L (s.regs 28).toNat (view (toyRt tys0) L s.mem) := hinv
  obtain ⟨p, hpm, h1, h2, hendA, hfr, hlf, hap, hz, hacc', hinv'⟩ :=
    toy_alloc tysOK0 (A := 32) (K := 32) (by omega) (by omega) (by omega) hcost hinvT
  have hacB := bump_acc hinv
  have hH : s.mem.accessible HEAP HSIZE true = true := by
    obtain ⟨p', -, -, -, -, -, -, hac, -, -, -⟩ := hinvT
    rw [view_accessible] at hac; exact hac
  have hS : s.mem.accessible ((s.regs 2).toNat + 8) 8 false = true := by
    have h16 : 0 < 16 * (1 + nDec (segsOf s.mem (s.regs 0).toNat (s.regs 1).toNat)) := by omega
    rw [hsl] at hSl
    exact Memory.accessible_mono _ (hSl.2 h16) (by omega) (by omega)
  have hS2 : (s.regs 2).toNat + 16 ≤ 2 ^ 48 := by
    rw [hsl] at hSl
    have := hSl.1
    omega
  have hpm' : s.mem.readLE 4194304 8 = p := hpm
  have hrun := code_run s hpc h30b h30a hacB hH (by simp only [HEAP] at h1; omega)
    (by simp only [HEND, HEAP, HSIZE] at hendA; omega) hS hS2
  obtain ⟨k, s', hst, hpc', rfl⟩ := hrun
  refine ⟨k, errFinal s, hst, hpc', ?_⟩
  have hLp : ∀ r ∈ L, HEAP ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ p := by
    obtain ⟨p', hp', -, -, -, hL, -⟩ := hinvT
    have hp'p : p' = p := by
      rw [← hp', readLE_view (inRanges_bump tys0) (outside_live hL (by simp only [BUMP, HEAP]; omega))]; exact hpm
    intro r hr
    have := hL r hr
    omega
  have hmem : (errFinal s).mem = wr4 (s.mem.writeLE BUMP 8 (p + 32)) p 0 0 iErr
      (s.mem.readLE ((s.regs 2).toNat + 8) 8) := by
    simp only [errFinal, wr4, hpm']; rfl
  have hout : ∀ a, p ≤ a → Outside a 8 L := fun a ha => outside_live_above hLp ha
  have hobj : InRanges p 32 (L ++ [(p, p + 32)]) := ⟨(p, p + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩
  have hrt : InRanges p 32 (toyRt tys0) := inRanges_heap h1 hendA
  have hlen' : strBytes (errFinal s).mem ((errFinal s).mem.readLE p 8) 0 = [] := rfl
  unfold Pool.LiveRet
  refine ⟨(errFinal s).regs, s.vregs, s.flags, (errFinal s).mem, s.excl, s.exclPass, errFinal_ret s, ?_, ?_, ?_⟩
  · rw [hmem]
    refine (hfr.trans (wr4_frame _ hrt _ _ _ _) (fun a n h => ⟨h, h⟩)).mono ?_
    intro a n h; simp only [outside_append] at h; exact h.1
  · rw [hmem]; exact (hlf.trans (wr4_live (LiveFrame.refl _ _ _) hout _ _ _ _) (fun _ _ h => h)) 
  · have hmsg : msgOf s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat = [] := List.length_eq_zero_iff.mp hlen0
    have hp64 : p < 2 ^ 64 := by simp only [HEND, HEAP, HSIZE] at hendA; omega
    have hr0 : ((errFinal s).regs 0).toNat = iWrap := by simp [errFinal, setReg, iWrap]
    have hr1 : ((errFinal s).regs 1).toNat = p := by
      simp only [errFinal, setReg]
      simp [hpm', Nat.mod_eq_of_lt hp64]
    have hAp : ∀ r ∈ (calleeStack s 4096 5), p + 32 ≤ r.1 ∨ r.2 ≤ p := by
      intro r hr
      have := (apart_win hrt hWs) r hr
      unfold Apart at this; omega
    show ErrorfPost (Env.mk tErr iErr tInt iWrap) (toyR tys0 ok) s.mem (s.regs 0).toNat (s.regs 1).toNat
      (s.regs 2).toNat (calleeStack s 4096 5) L b (s.regs 28).toNat ((errFinal s).regs 0).toNat
      ((errFinal s).regs 1).toNat (errFinal s).mem
    rw [hr0, hr1, hmem]
    unfold ErrorfPost
    have hwb : wrapBytes = 32 := rfl
    simp only [hwb, wrapErrOffset]
    refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [HEND, HEAP, HSIZE] at hendA ⊢; omega
    · rw [wr4_acc]; exact hacc'
    · rw [wr4_r1, hlen0]
    · rw [hlen0, hmsg]; rfl
    · rw [hlen0]; refine ⟨?_, fun h => absurd h (by omega)⟩
      rw [wr4_r0]; simp
    · show (wr4 (s.mem.writeLE BUMP 8 (p + 32)) p 0 0 iErr (s.mem.readLE ((s.regs 2).toNat + 8) 8)).readLE (p + 16) 8 = iErr
      rw [wr4_r2]; decide
    · show (wr4 (s.mem.writeLE BUMP 8 (p + 32)) p 0 0 iErr (s.mem.readLE ((s.regs 2).toNat + 8) 8)).readLE (p + 24) 8 = _
      rw [wr4_r3, Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)]
      simp [operandD]
    · simp only [freshFrom_cons, freshFrom_nil, and_true, Nat.add_sub_cancel_left]; exact hap
    · exact hrt
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact outside_of_forall fun r' hr' => by have := hAp r' hr'; simp only [Nat.add_sub_cancel_left]; omega
    · rw [hlen0]; simp [range0]
    · rw [hcost32, hlen0]
      simp only [range0, if_true, List.append_nil]
      rw [wr4_view _ _ _ hobj]
      exact hinv'

/-! ## A call state that satisfies the whole precondition -/

/-- The format `%w` (2 bytes), the `[]any` (one operand: the errorString, type `tErr`), the
errorString header (empty text) and the witness call state; all in the writable buffer `CB`. -/
def eFP : Nat := CB
def eSP : Nat := CB + 0x10
def eE : Nat := CB + 0x30
def eTxt : Nat := CB + 0x50

def ewmem : Memory :=
  (((wmem.writeLE eFP 2 0x7725).writeLE eSP 8 tErr).writeLE (eSP + 8) 8 eE).writeLE eE 8 eTxt

def ewstate : State := { wst [eFP, 2, eSP, 1, 1] with mem := ewmem }

def okE : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [eFP, 2, eSP, 1, 1]

theorem ewframe : MemFrame wmem ewmem [(CB, CB + 0x100)] := by
  have hr : (CB, CB + 0x100) ∈ [(CB, CB + 0x100)] := by simp
  exact (((((MemFrame.refl wmem _).writeLE 0x7725 hr (a := eFP) (k := 2) (by simp [eFP, CB]) (by simp [eFP, CB])).writeLE
    tErr hr (a := eSP) (k := 8) (by simp [eSP, CB]) (by simp [eSP, CB])).writeLE eE hr (a := eSP + 8) (k := 8)
    (by simp [eSP, CB]) (by simp [eSP, CB])).writeLE eTxt hr (a := eE) (k := 8) (by simp [eE, CB]) (by simp [eE, CB]))

set_option maxRecDepth 100000 in
theorem ewargs : ArgsOK (Env.mk tErr iErr tInt iWrap) 2 0x7725 0 ewmem eFP 2 eSP 1 1 := by
  have h0 : nDec (segsOf ewmem eFP 2) = 0 := by decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, by unfold Readable; decide, by unfold Readable; decide, by decide,
    by decide, by unfold Readable; decide, by unfold Readable; decide, fun j hj => ?_, by decide, by decide⟩
  rw [h0] at hj; omega

theorem ewcall : CallOK ewstate 4096 5 := by
  obtain ⟨a, b, c, d, e, f, g⟩ := wcallOK (fun i => BitVec.ofNat 64 ([eFP, 2, eSP, 1, 1].getD i 0)) 5 (by omega)
  refine ⟨a, b, c, d, e, f, ?_⟩
  have := ewframe.accessible (wsp - 4096) (4096 + 8 + 8 * 5) true
  have e : ewstate.sp.toNat = wsp := wspn
  show ewmem.accessible _ _ true = true
  rw [e, this]
  have g' := g
  rw [wmem_eq, wsp_eq, wspn] at g'
  exact g'

theorem ewguard : StackRoom ewstate 4096 5 := by
  obtain ⟨⟨a, b, c⟩, d⟩ := wguard (fun i => BitVec.ofNat 64 ([eFP, 2, eSP, 1, 1].getD i 0)) 5 (by omega)
  refine ⟨⟨a, ?_, ?_⟩, d⟩
  · show ewmem.accessible _ _ false = true
    rw [ewframe.accessible]; exact b
  · have e28 : (ewstate.regs 28).toNat = wg := wgn
    show ewmem.readLE _ 8 + 4096 < _
    rw [ewframe.readLE _ _ (by
      show Outside ((ewstate.regs 28).toNat + 16) 8 [(CB, CB + 0x100)]
      rw [e28]; simp [wg, CB, outside_cons, outside_nil])]; exact c

set_option maxRecDepth 100000 in
theorem ewreads : ReadsOutside (errorfReads ewmem eFP 2 eSP) (calleeStack ewstate 4096 5) := by
  have : errorfReads ewmem eFP 2 eSP = [(eFP, 2), (eSP, 16), (eE, 16), (eTxt, 0)] := by decide
  rw [this]
  simp only [ReadsOutside, List.mem_cons, List.not_mem_nil, or_false]
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [calleeStack, ewstate, wst, wstate, wsp, eFP, eSP, eE, eTxt, CB, outside_cons, outside_nil]

theorem ewinv (g : Nat) : toyInv tys0 0x400 [] g (view (toyRt tys0) [] ewmem) := by
  have h := wmem_inv g
  have e : view (toyRt tys0) [] ewmem = view (toyRt tys0) [] wmem := by
    unfold ewmem
    have o : ∀ a n, a ≥ CB → a + n ≤ CB + 0x100 → Outside a n (toyRt tys0) := fun a n h1 h2 => by
      simp only [toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, HEAP, HEND, HSIZE, BUMP, WBUF,
        tyA, tyB, tyC, CB] at h1 h2 ⊢
      omega
    rw [view_writeLE_out (o _ _ (by simp [eE, CB]) (by simp [eE, CB])),
      view_writeLE_out (o _ _ (by simp [eSP, CB]) (by simp [eSP, CB])),
      view_writeLE_out (o _ _ (by simp [eSP, CB]) (by simp [eSP, CB])),
      view_writeLE_out (o _ _ (by simp [eFP, CB]) (by simp [eFP, CB]))]
  rw [e]; exact h

theorem ewwin : LiveSep (calleeStack ewstate 4096 5) (toyRt tys0) :=
  wwin (fun i => BitVec.ofNat 64 ([eFP, 2, eSP, 1, 1].getD i 0)) 5 (by omega)

set_option maxRecDepth 100000 in
theorem ewcost : errorfCost ewmem eFP 2 eSP ≤ 0x400 := by
  unfold errorfCost; decide

set_option maxRecDepth 100000 in
theorem ewsafe : ReadsSafe (toyR tys0 okE) [] (errorfReads ewmem eFP 2 eSP) := by
  have : errorfReads ewmem eFP 2 eSP = [(eFP, 2), (eSP, 16), (eE, 16), (eTxt, 0)] := by decide
  rw [this]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl (by
        simp only [toyR, toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, HEAP, HEND, HSIZE,
          BUMP, WBUF, tyA, tyB, tyC, eFP, eSP, eE, eTxt, CB]
        omega))

theorem errorfLive_satisfiable : ∃ (R : RtInv) (tErr iErr tInt iWrap Fl Fm B : Nat) (impl : List Segment),
    ErrorfLive (toy.link impl) A0 4096 R tErr iErr tInt iWrap Fl Fm B ∧
    ∃ (s : State) (L : List (Nat × Nat)) (b : Nat), s.pc = BitVec.ofNat 64 A0 ∧
      CallOK s 4096 5 ∧ StackRoom s 4096 5 ∧
      ArgsOK (Env.mk tErr iErr tInt iWrap) Fl Fm B s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat
        (s.regs 3).toNat (s.regs 4).toNat ∧
      ReadsOutside (errorfReads s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) (calleeStack s 4096 5) ∧
      ReadsSafe R L (errorfReads s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat, (s.regs 3).toNat, (s.regs 4).toNat] L b
        (errorfCost s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat) (s.regs 28).toNat s.mem
        (calleeStack s 4096 5) :=
  ⟨toyR tys0 okE, tErr, iErr, tInt, iWrap, 2, 0x7725, 0, at0 code, errorf_impl okE, ewstate, [], 0x400, rfl, ewcall, ewguard,
    ewargs, ewreads, ewsafe, ⟨⟨rfl, by decide⟩, ewinv (ewstate.regs 28).toNat, ewcost, by simp, ewwin⟩⟩

end Janus.Contracts.ErrorfSat
