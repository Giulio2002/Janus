import Extracted

/-!
# `Classify(x any) uint64`: a type switch over `nil`, `uint64`, `string`, `Hasher` and the rest (arm64)

**Guarantee.** For every interface value `x = (t, data)`, every model `R` of the interface
runtime satisfying its laws, every implementation of `runtime.interfaceSwitch` satisfying the
`InterfaceSwitch` contract and every Go call state in which the runtime is usable with
`R.depth` bytes of stack below `Classify`'s frame (`CallerOK`), the read-only data (the
`uint64` and `string` type descriptors) is in memory, the interface-switch descriptor the code
loads (`example.com/basic..interfaceSwitch.0`, a writable global) is well formed for its one
interface case `c` (`ISDescOK`: `NCases = 1`, `Cases[0] = c`, a well-formed cache), and the
dynamic type of a non-nil `x` is a type descriptor, the call returns, obeys the ABI, and `X0`
is `result R c t`:

* `0` for a nil `x`, `1` for `uint64`, `2` for `string` (the type descriptors the code compares
  with, recomputed from the extracted code; the code first compares the 32-bit type hash, read
  from the descriptor, then the pointer);
* `3` if `t` implements the case `c` (`getitab`'s answer `R.itab c t` is some), `4` otherwise;
* for `*MulHasher` and `c = Hasher` (the static itab's words), `3` (`StaticItabs`).

The descriptor stays well formed, memory changes only in the runtime's memory, the stack window
and the descriptor's `Cache` word. The interface case goes through the inline probe of the
switch cache (`loop`, as in `AsHasher`, with 24-byte entries holding the case index) and, on a
miss, `runtime.interfaceSwitch`.

**Assumptions (all in the statement).** `R` is *any* model satisfying `R.Laws`, and the code at
`runtime.interfaceSwitch` is *any* code that behaves as `InterfaceSwitch` says (pinned to the Go
runtime's code by the extraction).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Iface

namespace Proof

/-- `type:uint64`: the `ADRP`+`ADD` at `Classify+0x38`. -/
def u64T : Nat :=
  adrpLdTarget (Extracted.entry + 0x38) (segWord Extracted.program "example.com/basic.Classify" 14)
    (segWord Extracted.program "example.com/basic.Classify" 15) 0
/-- `type:string`: the `ADRP`+`ADD` at `Classify+0x68`. -/
def strT : Nat :=
  adrpLdTarget (Extracted.entry + 0x68) (segWord Extracted.program "example.com/basic.Classify" 26)
    (segWord Extracted.program "example.com/basic.Classify" 27) 0
/-- The interface-switch descriptor `example.com/basic..interfaceSwitch.0` (`.data`): the
`ADRP`+`ADD` at `Classify+0x88`. -/
def desc : Nat :=
  adrpLdTarget (Extracted.entry + 0x88) (segWord Extracted.program "example.com/basic.Classify" 34)
    (segWord Extracted.program "example.com/basic.Classify" 35) 0

/-- The loop head of the cache probe (`AND R5, R2, R6`). -/
abbrev head : Nat := Extracted.entry + 0xac

/-- The result: `0` for nil, `1` for `uint64`, `2` for `string`, `3` for a type implementing the
switch's interface case `c`, `4` otherwise. -/
def result (R : IfaceModel) (c t : Nat) : Nat :=
  if t = 0 then 0 else if t = u64T then 1 else if t = strT then 2
  else if (R.itab c t).isSome then 3 else 4

/-- The window `Classify` and the runtime write: `R.depth` bytes below the 64-byte frame, the frame,
and the two argument spill slots above `SP`. -/
abbrev window (R : IfaceModel) (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - (R.depth + 64), s.sp.toNat + 24)]

/-- The guarantee: the result in `X0`; the descriptor still well formed for the same case;
memory changed only in the runtime's memory, the window and the descriptor's `Cache` word; the
runtime still usable. -/
def Post (R : IfaceModel) (c : Nat) (t : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat = result R c t.toNat ∧ ISDescOK R s'.mem desc [c] ∧
    MemFrame s.mem s'.mem (R.priv ++ window R s ++ [(desc, desc + 8)]) ∧ R.Env s'.mem (s.regs 28)

/-- The memory at the loop head: the caller's memory with the frame record and the two spills. -/
def M0 (s : State) (ret : Nat) (t x : BitVec 64) : Memory :=
  (((s.mem.writeLE (s.sp.toNat - 64) 8 ret).writeLE (s.sp.toNat - 72) 8 (s.regs 29).toNat).writeLE
    (s.sp.toNat + 8) 8 t.toNat).writeLE (s.sp.toNat + 16) 8 x.toNat

/-- The entry address the probe computes in `X6`: `8 + 24·(h & Mask)` added to the cache. -/
theorem x6_toNat (c k : Nat) (h : BitVec 64) (hk : k ≤ 64) (hc : c + 8 + 24 * 2 ^ k ≤ 2 ^ 48) :
    (BitVec.ofNat 64 c + 8#64 +
      (((h &&& BitVec.ofNat 64 (2 ^ k - 1)).rotateRight 61 &&& 18446744073709551608#64 &&&
          18446744073709551615#64) +
        ((h &&& BitVec.ofNat 64 (2 ^ k - 1)).rotateRight 61 &&& 18446744073709551608#64 &&&
          18446744073709551615#64) <<< 1)).toNat = c + 8 + 24 * (h.toNat % 2 ^ k) := by
  have hm := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
  have h1 : ((h &&& BitVec.ofNat 64 (2 ^ k - 1)).rotateRight 61 &&& 18446744073709551608#64 &&&
      18446744073709551615#64).toNat = 8 * (h.toNat % 2 ^ k) := by
    rw [BitVec.toNat_and, BitVec.toNat_and, show (18446744073709551615#64).toNat = 2 ^ 64 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (18446744073709551608#64).toNat = 18446744073709551608 from rfl,
      lsl3_toNat, and_mask_toNat h k hk]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, h1,
    BitVec.toNat_ofNat, show (8#64).toNat = 8 from rfl, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c + 8 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 8 * (h.toNat % 2 ^ k) * 2 ^ 1 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 8 * (h.toNat % 2 ^ k) + 8 * (h.toNat % 2 ^ k) * 2 ^ 1 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem loop (impl : List Segment) (R : IfaceModel) (hl : R.Laws)
    (hsw : InterfaceSwitch (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.interfaceSwitch") R)
    (c : Nat) (t x : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (s : State) (hc : CallerOK R s 64 24) (hdesc : ISDescOK R s.mem desc [c])
    (hdo : desc + 24 ≤ s.sp.toNat - (R.depth + 64) ∨ s.sp.toNat + 24 ≤ desc)
    (ht0 : t.toNat ≠ 0) (hty : R.IsType t.toNat) (htu : t.toNat ≠ u64T) (hts : t.toNat ≠ strT)
    (k : Nat) (hk : s.mem.readLE (s.mem.readLE desc 8) 8 = 2 ^ k - 1)
    (hcb : s.mem.readLE desc 8 + 8 + 24 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : s.mem.accessible (s.mem.readLE desc 8) (8 + 24 * 2 ^ k) false = true)
    (hcin : InRanges (s.mem.readLE desc 8) (8 + 24 * 2 ^ k) R.priv)
    (hent : ∀ i, i < 2 ^ k → isTyp s.mem (s.mem.readLE desc 8) i ≠ 0 →
      isCase s.mem (s.mem.readLE desc 8) i = (switchCase R (isTyp s.mem (s.mem.readLE desc 8) i) [c]).1 ∧
      isItab s.mem (s.mem.readLE desc 8) i = (switchCase R (isTyp s.mem (s.mem.readLE desc 8) i) [c]).2)
    (j : Nat) (hj : j < 2 ^ k) (hj0 : isTyp s.mem (s.mem.readLE desc 8) j = 0) :
    ∀ n (S : State) (h : BitVec 64), (j + 2 ^ k - h.toNat % 2 ^ k) % 2 ^ k = n →
      h.toNat + n < 2 ^ 46 →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = t →
      S.regs 2 = h → S.regs 3 = BitVec.ofNat 64 desc →
      S.regs 4 = BitVec.ofNat 64 (s.mem.readLE desc 8) →
      S.regs 5 = BitVec.ofNat 64 (2 ^ k - 1) → S.regs 30 = BitVec.ofNat 64 ret →
      S.sp = s.sp - 64#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 72#64 →
      S.regs 18 = s.regs 18 → S.mem = M0 s ret t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R c t s s') := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, hdw, -⟩ := hdesc'
  have hdc := InRanges.disjoint hcin hout
  obtain ⟨-, htb, htacc, htin⟩ := hl.type_desc _ _ _ henv hty
  simp only [typeDescSize] at htb htacc htin
  have hdt := InRanges.disjoint htin hout
  have hk64 : k ≤ 64 := by
    refine Nat.le_of_not_lt fun hk => ?_
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 65 ≤ k by omega); omega
  have hand : ∀ h : BitVec 64, (h &&& BitVec.ofNat 64 (2 ^ k - 1)).toNat = h.toNat % 2 ^ k :=
    fun h => and_mask_toNat h k hk64
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  have hws : ∀ a n, InRanges a n R.priv → Outside a n [(s.sp.toNat - (R.depth + 64), s.sp.toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo' : Outside desc 24 [(s.sp.toNat - (R.depth + 64), s.sp.toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hMf : MemFrame s.mem (M0 s ret t x) [(s.sp.toNat - (R.depth + 64), s.sp.toNat + 24)] := by simp only [M0]; janus_frame
  have htlt : ∀ i, isTyp s.mem (s.mem.readLE desc 8) i % 18446744073709551616 =
      isTyp s.mem (s.mem.readLE desc 8) i := fun i => Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)
  have htyp : ∀ i, s.mem.readLE (s.mem.readLE desc 8 + 8 + (8 * i + 2 * (8 * i))) 8 =
      isTyp s.mem (s.mem.readLE desc 8) i := fun i => by
    simp only [isTyp]
    rw [show s.mem.readLE desc 8 + 8 + 24 * i = s.mem.readLE desc 8 + 8 + (8 * i + 2 * (8 * i)) by omega]
  -- the answer for the iface path, from the case word
  have hans : ∀ cw : Nat, cw = (switchCase R t.toNat [c]).1 →
      (if cw = 0 then 3 else 4) = result R c t.toNat := by
    intro cw hcw
    simp only [result, ht0, htu, hts, ite_false, hcw, switchCase_single]
    cases R.itab c t.toNat <;> rfl
  -- the hit: the cached case is the runtime's answer
  have hit : ∀ (S : State) (h : BitVec 64), h.toNat % 2 ^ k < 2 ^ k →
      t.toNat = isTyp s.mem (s.mem.readLE desc 8) (h.toNat % 2 ^ k) →
      S.pc = BitVec.ofNat 64 (Extracted.entry + 0xe4) →
      (S.regs 6).toNat = s.mem.readLE desc 8 + 8 + 24 * (h.toNat % 2 ^ k) →
      S.regs 30 = BitVec.ofNat 64 ret →
      S.sp = s.sp - 64#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 72#64 →
      S.regs 18 = s.regs 18 → S.mem = M0 s ret t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R c t s s') := by
    intro S h hmod heq hpc h6 h30 hsp h28 h29 h18 hm
    have hspa : S.sp.toNat % 16 = 0 := by rw [hsp]; janus_simp; omega
    have hcase : s.mem.readLE (s.mem.readLE desc 8 + 8 + 24 * (h.toNat % 2 ^ k) + 8) 8 =
        (switchCase R t.toNat [c]).1 := by
      have := (hent _ hmod (by rw [← heq]; exact ht0)).1
      rw [← heq] at this
      rw [← this]; simp only [isCase]
      rw [show s.mem.readLE desc 8 + 16 + 24 * (h.toNat % 2 ^ k) =
        s.mem.readLE desc 8 + 8 + 24 * (h.toNat % 2 ^ k) + 8 by omega]
    have hlt := Memory.readLE_lt s.mem (s.mem.readLE desc 8 + 8 + 24 * (h.toNat % 2 ^ k) + 8) 8
    simp only [M0] at hm
    janus_run [h6]
    all_goals refine ⟨?_, ISDescOK.frame hdesc hMf hdo' hws, hMf.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.1.2,
      hl.env_frame _ _ _ henv (agrees_of_memFrame_outside hMf hws)⟩
    all_goals (simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; rw [← hans _ hcase]; simp [hbr])
  -- a miss: the call of `runtime.interfaceSwitch`
  have miss : ∀ (S : State), S.pc = BitVec.ofNat 64 (Extracted.entry + 0xd4) → S.regs 0 = t →
      S.regs 3 = BitVec.ofNat 64 desc → S.regs 30 = BitVec.ofNat 64 ret →
      S.sp = s.sp - 64#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 72#64 →
      S.regs 18 = s.regs 18 → S.mem = M0 s ret t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R c t s s') := by
    intro S hpc h0 h3 h30 hsp h28 h29 h18 hm
    have hspa : S.sp.toNat % 16 = 0 := by rw [hsp]; janus_simp; omega
    have hd64 : desc % 2 ^ 64 = desc := Nat.mod_eq_of_lt (by omega)
    simp only [M0] at hm
    janus_run until [Extracted.program.contractAddr "runtime.interfaceSwitch"]
    refine Reaches.call (Summary.withExit (hsw [c]) hret) rfl
      ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) (by simp [setReg, h28])
        (by simp [setReg]) (by simp [setReg]) (by decide) (by decide), ?_, ?_, ?_⟩ ?_
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64]
      exact ISDescOK.frame hdesc (by janus_frame) hdo' hws
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h0]; exact ht0
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h0]; exact hty
    · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hcase, hitab, _, hdesc2⟩
      subst hs'
      simp only [rtWrites, calleeStack, setReg_apply, reduceIte, Nat.reduceEqDiff,
        BitVec.toNat_ofNat, hd64, h0] at hfr hcase hdesc2
      have hlt := BitVec.isLt (r 0)
      janus_run
      all_goals
        obtain ⟨MM, hMM⟩ : ∃ MM, MM = M0 s ret t x := ⟨_, rfl⟩
        simp only [M0] at hMM
        rw [← hMM] at hfr
        have hMf' : MemFrame s.mem MM [(s.sp.toNat - (R.depth + 64), s.sp.toNat + 24)] := by rw [hMM]; janus_frame
        refine ⟨?_, hdesc2, ?_, by simpa [setReg, h28] using henv'⟩
      all_goals first
        | (simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, Map.keepABI_apply]
           rw [← hans _ hcase]; simp [hbr]; done)
        | (refine hMf'.trans hfr fun a n h => ?_
           have hsp64 : (s.sp - 64#64).toNat = s.sp.toNat - 64 := by
             rw [BitVec.toNat_sub]; simp; omega
           simp only [outside_append, outside_cons, outside_nil, and_true, hsp64] at h ⊢
           exact ⟨h.1.2, ⟨h.1.1, by omega, by omega⟩, h.2⟩)
  intro n
  induction n with
  | zero =>
    intro S h hn hb' hpc h0 h2 h3 h4 h5 h30 hsp h28 h29 h18 hm
    simp only [M0] at hm
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    have hjr := probe_zero hj hmod hn
    janus_run [hand] until [head, Extracted.entry + 0xd4, Extracted.entry + 0xe4]
    · refine hit _ h hmod (by simpa [htlt] using hbr) (by rfl)
        (by simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; exact x6_toNat _ _ _ hk64 hcb)
        (by simp [setReg, h30]) rfl (by simp [setReg, h28]) (by simp [setReg, h29])
        (by simp [setReg, h18]) rfl
    · exact miss _ (by rfl) (by simp [setReg, h0]) (by simp [setReg, h3]) (by simp [setReg, h30])
        rfl (by simp [setReg, h28]) (by simp [setReg, h29]) (by simp [setReg, h18]) rfl
    · exfalso
      rw [htlt, hjr, hj0] at hbr
      exact hbr rfl
  | succ n ih =>
    intro S h hn hb' hpc h0 h2 h3 h4 h5 h30 hsp h28 h29 h18 hm
    simp only [M0] at hm
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    janus_run [hand] until [head, Extracted.entry + 0xd4, Extracted.entry + 0xe4]
    · refine hit _ h hmod (by simpa [htlt] using hbr) (by rfl)
        (by simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; exact x6_toNat _ _ _ hk64 hcb)
        (by simp [setReg, h30]) rfl (by simp [setReg, h28]) (by simp [setReg, h29])
        (by simp [setReg, h18]) rfl
    · exact miss _ (by rfl) (by simp [setReg, h0]) (by simp [setReg, h3]) (by simp [setReg, h30])
        rfl (by simp [setReg, h28]) (by simp [setReg, h29]) (by simp [setReg, h18]) rfl
    · have hne : h.toNat % 2 ^ k ≠ j := fun he => by rw [htlt, he, hj0] at hbr; exact hbr rfl
      have h1' : (h + 1#64).toNat = h.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      refine ih _ (h + 1#64) ?_ ?_ (by rfl) (by simp [setReg, h0]) (by simp [setReg])
        (by simp [setReg, h3]) (by simp [setReg, h4]) (by simp [setReg, h5])
        (by simp [setReg, h30]) rfl (by simp [setReg, h28]) (by simp [setReg, h29])
        (by simp [setReg, h18]) rfl
      · rw [h1']; have := probe_dist (2 ^ k) j h.toNat hj hne; omega
      · rw [h1']; omega

/-- The static itab of `*MulHasher` for `Hasher` (copied by `--targets`). -/
abbrev mulItab : String := "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher"
/-- Its `Inter` word: the address of the `Hasher` interface type. -/
def hasherInter : Nat := dataWord Extracted.program.data mulItab 0 8
/-- Its `Type` word: the address of the `*MulHasher` type descriptor. -/
def mulHasherType : Nat := dataWord Extracted.program.data mulItab 8 8

/-- A `*MulHasher` takes the `Hasher` case (`StaticItabs`). -/
theorem static_case (R : IfaceModel) (c : Nat) (t : BitVec 64) (s s' : State) (hp : Post R c t s s')
    (hst : StaticItabs R Extracted.program.data) (hi : c = hasherInter)
    (htt : t.toNat = mulHasherType) : (s'.regs 0).toNat = 3 := by
  obtain ⟨d, hd⟩ : ∃ d, dataNamed Extracted.program.data mulItab = some d := ⟨_, rfl⟩
  have hsome := hst.named hd (by decide +kernel)
    (by rw [show d = _ from (Option.some.inj hd).symm]; decide)
  janus_eval_nat hT : mulHasherType
  janus_eval_nat hU : u64T
  janus_eval_nat hS : strT
  rw [hp.1]
  simp only [hasherInter, mulHasherType] at hsome hT hi htt
  rw [hT] at hsome
  simp only [result, hi, htt, hT, hU, hS, hsome]
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (R : IfaceModel) (hl : R.Laws)
    (hsw : InterfaceSwitch (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.interfaceSwitch") R)
    (c : Nat) (t x : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [t, x]
      (fun s => CallerOK R s 64 24 ∧ Extracted.program.DataLoaded s.mem ∧
        ISDescOK R s.mem desc [c] ∧ Outside desc 24 (window R s) ∧
        (t.toNat ≠ 0 → R.IsType t.toNat))
      (fun s s' => Post R c t s s' ∧
        (StaticItabs R Extracted.program.data → c = hasherInter → t.toNat = mulHasherType →
          (s'.regs 0).toNat = 3)) := by
  intro ret hret s hs ⟨hc, hdl, hdesc, hdo, hty⟩
  suffices hmain : Reaches ((Extracted.program.link impl).withExit ret) s
      (IsReturn fun s' => ABIReturn s s' ∧ Post R c t s s') by
    exact (returns_of_reaches hmain).mono fun s' h =>
      ⟨h.1, h.2, fun hst hi htt => static_case R c t s s' h.2 hst hi htt⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_data hdl [hst]
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  simp only [window, outside_cons, outside_nil, and_true] at hdo
  janus_eval_nat hU : u64T
  janus_eval_nat hS : strT
  janus_eval_nat hD : desc
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, hdw, hn1, hcs, hint, k, hk, hcb, hcacc, hcin, hent, j, hj, hj0⟩ := hdesc'
  have hdc := InRanges.disjoint hcin hout
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [(s.sp.toNat - (R.depth + 64), s.sp.toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo' : Outside desc 24 [(s.sp.toNat - (R.depth + 64), s.sp.toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hcacc' := hcacc; have hdacc' := hdacc; have hdw' := hdw; have hdo'' := hdo
  have hdc' := hdc; have hdb' := hdb
  rw [hD] at hcacc' hdacc' hdw' hdo'' hdc' hdb'
  -- the returns without a runtime call
  have fin : ∀ (v : Nat) (m : Memory), v = result R c t.toNat →
      MemFrame s.mem m [(s.sp.toNat - (R.depth + 64), s.sp.toNat + 24)] →
      ∀ s' : State, (s'.regs 0).toNat = v → s'.mem = m → Post R c t s s' := by
    intro v m hv hm s' h0 h1
    unfold Post; rw [h1]
    exact ⟨by rw [h0, hv], ISDescOK.frame hdesc hm hdo' hws, hm.mono fun a n h => by
        simp only [window, outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.1.2,
      hl.env_frame _ _ _ henv (agrees_of_memFrame_outside hm hws)⟩
  by_cases ht0 : t.toNat = 0
  · janus_run
    exact fin 0 _ (by simp [result, ht0]) (by janus_frame) _ (by simp [setReg]) rfl
  by_cases htu : t.toNat = u64T
  · obtain rfl : t = BitVec.ofNat 64 695360 := by
      apply BitVec.eq_of_toNat_eq; rw [htu, hU]; rfl
    janus_run
    exact fin 1 _ (by simp [result, hU]) (by janus_frame) _ (by simp [setReg]) rfl
  by_cases hts : t.toNat = strT
  · obtain rfl : t = BitVec.ofNat 64 694848 := by
      apply BitVec.eq_of_toNat_eq; rw [hts, hS]; rfl
    janus_run
    exact fin 2 _ (by simp [result, hU, hS]) (by janus_frame) _ (by simp [setReg]) rfl
  obtain ⟨-, htb, htacc, htin⟩ := hl.type_desc _ _ _ henv (hty ht0)
  simp only [typeDescSize] at htb htacc htin
  have hdt := InRanges.disjoint htin hout
  have hhash := Memory.readLE_lt s.mem (t.toNat + 16) 4
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  have hkb : 2 ^ k < 2 ^ 44 := by omega
  janus_run until [head]
  all_goals
    refine loop impl R hl hsw c t x ret hret s hc hdesc hdo ht0 (hty ht0) htu hts k hk hcb hcacc
      hcin hent j hj hj0 _ _ (BitVec.ofNat 64 (s.mem.readLE (t.toNat + 16) 4)) rfl ?_ (by rfl)
      (by simp [setReg, h_x0]) (by simp [setReg]) (by simp [setReg, hD]) (by simp [setReg, hD])
      (by simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; rw [← hD, hk])
      (by simp [setReg, h_lr]) rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      (by simp [M0])
    have := probe_lt (j := j) (r := (BitVec.ofNat 64 (s.mem.readLE (t.toNat + 16) 4)).toNat) hN
    simp only [BitVec.toNat_ofNat] at this ⊢
    rw [Nat.mod_eq_of_lt (show s.mem.readLE (t.toNat + 16) 4 < 2 ^ 64 by simp at hhash; omega)] at this ⊢
    simp at hhash
    omega


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model of the runtime (`IfaceModel.R0`), code at `runtime.interfaceSwitch`'s address that meets
the `InterfaceSwitch` contract for it (`IfaceSat.interfaceSwitchCode`), an admissible return
address and a call state switching on a box of the model's type `TD`, with the read-only data
loaded and the descriptor at its real address (one case, the model's interface `ID`, and the
empty cache): `correctness` applies, and `Classify` takes the interface case (`3`) after a cache
miss. -/

namespace Witness

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat

/-- `runtime.interfaceSwitch`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.interfaceSwitch"

/-- `IfaceSat.interfaceSwitchCode` at `runtime.interfaceSwitch`'s address. -/
def implAt : List Segment := [{ name := "model", base := cAddr, words := interfaceSwitchCode }]

/-- The program linked with it, as a closed program. -/
def linked : Program :=
  { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : InterfaceSwitch (Extracted.program.link implAt) cAddr R0 := by
  rw [linked_eq]
  intro cs s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hdesc, ht0, ht⟩ := hpre
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, -, hn, -, hcs, -⟩ := hdesc'
  have hcs' : ∀ c ∈ cs, c = ID := hcs
  have hsw := switchCase_R0 (s.regs 1).toNat cs hcs'
  have hlen : cs.length < 2 ^ 48 := by omega
  janus_run
  all_goals
    refine rtReturn_of R0 2 _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
    refine ⟨?_, ?_, ?_, hdesc⟩
  all_goals (try rw [hn] at *)
  all_goals (try rw [switchCase_R0 _ cs hcs'])
  all_goals (try simp only [BitVec.toNat_ofNat])
  all_goals first
    | (simp_all [TD, TAB]; done)
    | (intro hne
       obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
         cases cs with
         | nil => simp_all
         | cons c cs' => exact ⟨c, cs', rfl⟩
       rw [hcs' c (by simp)]
       simpa [TD, TAB] using itabAt_TAB (g := s.regs 28) ⟨he1, he2, hd⟩)
    | (rw [ite_eq_right (fun h => by simp only [TD] at h; omega)]; exact Nat.mod_eq_of_lt (by omega))
    | done

/-- The descriptor's address, evaluated. -/
theorem desc_eq : desc = 0x1646f0 := by decide

/-- A byte of the program's read-only data, if `a` is in one of its objects. -/
def dbyte (a : Nat) : Option Nat :=
  Extracted.program.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

/-- The witness memory: the read-only data in read-only regions, the descriptor at `desc`
(cache `ISC`, `NCases = 1`, `Cases[0] = ID`) in a writable one, and `wmem`. -/
def mem2 : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyte a).getD ((([(0x1646f0 + 1, 0x05), (0x1646f0 + 2, 0x01),
      (0x1646f0 + 8, 1), (0x1646f0 + 17, 0x01), (0x1646f0 + 18, 0x01)] ++ wtable).lookup a).getD 0)),
    wmem.regions ++ [⟨0x164000, 0x1000, true⟩, ⟨0xa9000, 0x1000, false⟩, ⟨0xcc000, 0x1000, false⟩]⟩

theorem mem2_env (g : W64) : Env0 mem2 g := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Desc; decide

theorem mem2_data : Extracted.program.DataLoaded mem2 := by
  unfold Program.DataLoaded; decide +kernel

theorem mem2_desc : ISDescOK R0 mem2 desc [ID] := by
  rw [desc_eq]
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fun i hi => ?_, by simp, ?_⟩
  · simp at hi; subst hi; show mem2.readLE (0x1646f0 + 16) 8 = ID; decide +kernel
  · rw [show mem2.readLE 0x1646f0 8 = ISC by decide +kernel]
    exact ISCacheOK.empty (by decide +kernel) (by decide +kernel) (inPriv (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- `TD` and the value slot `VAL`, as words. -/
def td : BitVec 64 := BitVec.ofNat 64 TD
def val : BitVec 64 := BitVec.ofNat 64 VAL

/-- The witness call state: `Classify(x)` for the box `x = (TD, VAL)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then td else if i = 1 then val
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem2 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [td, val] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem pre : CallerOK R0 s0 64 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    ISDescOK R0 s0.mem desc [ID] ∧ Outside desc 24 (window R0 s0) ∧
    (td.toNat ≠ 0 → R0.IsType td.toNat) := by
  refine ⟨⟨mem2_env (s0.regs 28), ⟨by decide, by decide, by decide⟩, by decide, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_⟩, mem2_data, mem2_desc, ?_, fun _ => Or.inl rfl⟩
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide
  · rw [desc_eq]; simp only [window, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : IfaceModel) (c : Nat) (ret : Nat) (s : State)
    (t x : BitVec 64), R.Laws ∧
    InterfaceSwitch (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.interfaceSwitch") R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [t, x] s ∧
    (CallerOK R s 64 24 ∧ Extracted.program.DataLoaded s.mem ∧
      ISDescOK R s.mem desc [c] ∧ Outside desc 24 (window R s) ∧ (t.toNat ≠ 0 → R.IsType t.toNat)) :=
  ⟨implAt, R0, ID, ret, s0, td, val, R0_laws, model, hret, setup, pre⟩

/-- So the guarantee is reached: a box of `TD` takes the interface case `ID` (`3`). -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 3 := by
  refine (correctness implAt R0 R0_laws model ID td val ret hret s0 setup pre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2.1.1]
  janus_eval_nat hU : u64T
  janus_eval_nat hS : strT
  simp only [result, hU, hS]
  decide

end Witness

end Proof
