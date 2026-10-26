import Janus
import Extracted

/-!
# `Classify(x any) uint64`: a type switch over `nil`, `uint64`, `string`, `Hasher` and the rest (amd64)

**Guarantee.** For every interface value `x = (t, data)`, every model `R` of the interface
runtime satisfying its laws, every implementation of `runtime.interfaceSwitch` satisfying the
`InterfaceSwitch` contract and every Go call state in which the runtime is usable with
`R.depth` bytes of stack below `Classify`'s frame (`CallerOK`), the read-only data (the
`uint64` and `string` type descriptors) is in memory, the interface-switch descriptor the code
loads (`example.com/basic..interfaceSwitch.0`, a writable global) is well formed for its one
interface case `c` (`ISDescOK`: `NCases = 1`, `Cases[0] = c`, a well-formed cache), and the
dynamic type of a non-nil `x` is a type descriptor, the call returns, obeys the ABI, and `RAX`
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

**Readiness** (round 10). The statement also quantifies over `H : RtReady`, the runtime's readiness
for the one call that may allocate (`runtime.interfaceSwitch`), and assumes it at entry: the theorem says nothing
about a call the runtime cannot serve as the contract says (no room in the heap, a collection).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts.Iface Janus.Contracts.IfaceAmd64

namespace Proof

/-- `type:uint64`: the RIP-relative `LEAQ` at `Classify+0x30`. -/
def u64T : Nat := ripTarget Extracted.program (Extracted.entry + 0x30)
/-- `type:string`: the RIP-relative `LEAQ` at `Classify+0x4f`. -/
def strT : Nat := ripTarget Extracted.program (Extracted.entry + 0x4f)
/-- The interface-switch descriptor `example.com/basic..interfaceSwitch.0` (`.data`): the
RIP-relative operand of `MOVQ ..interfaceSwitch.0(SB), DX` at `Classify+0x66`. -/
def desc : Nat := ripTarget Extracted.program (Extracted.entry + 0x66)

/-- The loop head of the cache probe (`MOVQ CX, DI`). -/
abbrev head : Nat := Extracted.entry + 0x7a

/-- The result: `0` for nil, `1` for `uint64`, `2` for `string`, `3` for a type implementing the
switch's interface case `c`, `4` otherwise. -/
def result (R : IfaceModel) (c t : Nat) : Nat :=
  if t = 0 then 0 else if t = u64T then 1 else if t = strT then 2
  else if (R.itab c t).isSome then 3 else 4

/-- The window `Classify` and the runtime write. -/
abbrev window (R : IfaceModel) (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - (R.depth + 48), (s.regs 4).toNat + 24)]

/-- The guarantee: the result in `RAX`; the descriptor still well formed for the same case;
memory changed only in the runtime's memory, the window and the descriptor's `Cache` word; the
runtime still usable. -/
def Post (R : IfaceModel) (c : Nat) (t : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat = result R c t.toNat ∧ ISDescOK R s'.mem desc [c] ∧
    MemFrame s.mem s'.mem (R.priv ++ window R s ++ [(desc, desc + 8)]) ∧ R.Env s'.mem (s.regs 14)

/-- The memory at the loop head: the caller's memory with the saved frame pointer and the two
spills. -/
def M0 (s : State) (t x : BitVec 64) : Janus.Arm64.Memory :=
  ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 8) 8
    t.toNat).writeLE ((s.regs 4).toNat + 16) 8 x.toNat

/-- The entry index the probe computes in `CX` (`LEAQ (CX)(CX*2), CX`): `3·(h & Mask)`. -/
theorem probeIdx (k : Nat) (h : BitVec 64) (hk : k ≤ 64) (hkb : 2 ^ k < 2 ^ 44) :
    ((h &&& BitVec.ofNat 64 (2 ^ k - 1)) + (h &&& BitVec.ofNat 64 (2 ^ k - 1)) <<< 1).toNat =
      3 * (h.toNat % 2 ^ k) := by
  have hm := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
  rw [BitVec.toNat_add, Janus.Tactic.bv_toNat_shiftLeft, and_mask_toNat h k hk]
  rw [Nat.mod_eq_of_lt (show 2 ^ 1 * (h.toNat % 2 ^ k) < 18446744073709551616 by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]; omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem loop (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws) (H : Janus.Contracts.RtReady)
    (hsw : InterfaceSwitch (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.interfaceSwitch") R H)
    (c : Nat) (t x : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (s : State) (hc : CallerOK R s 48 24) (hdesc : ISDescOK R s.mem desc [c])
    (hdo : desc + 24 ≤ (s.regs 4).toNat - (R.depth + 48) ∨ (s.regs 4).toNat + 24 ≤ desc)
    (ht0 : t.toNat ≠ 0) (hty : R.IsType t.toNat) (htu : t.toNat ≠ u64T) (hts : t.toNat ≠ strT)
    (hra : s.mem.readLE (s.regs 4).toNat 8 = ret) (hx15 : s.xmm 15 = 0) (hdf : s.df = false)
    (hH : H [desc, t.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 48) (Janus.Contracts.rtView R.priv s.mem))
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
      S.rip = BitVec.ofNat 64 head → S.regs 0 = t → S.regs 1 = h →
      S.regs 2 = BitVec.ofNat 64 (s.mem.readLE desc 8) → S.regs 6 = BitVec.ofNat 64 (2 ^ k - 1) →
      S.regs 4 = s.regs 4 - 40#64 → S.regs 5 = s.regs 4 - 8#64 → S.regs 14 = s.regs 14 →
      S.xmm = s.xmm → S.df = s.df → S.mem = M0 s t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R c t s s') := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
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
  have hkb : 2 ^ k < 2 ^ 44 := by omega
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [((s.regs 4).toNat - (R.depth + 48), (s.regs 4).toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo' : Outside desc 24 [((s.regs 4).toNat - (R.depth + 48), (s.regs 4).toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hMf : MemFrame s.mem (M0 s t x) [((s.regs 4).toNat - (R.depth + 48), (s.regs 4).toNat + 24)] := by
    simp only [M0]; janus_frame
  have htlt : ∀ i, isTyp s.mem (s.mem.readLE desc 8) i % 18446744073709551616 =
      isTyp s.mem (s.mem.readLE desc 8) i := fun i => Nat.mod_eq_of_lt (Arm64.Memory.readLE_lt _ _ _)
  have htyp : ∀ i, Arm64.Memory.readLE s.mem (s.mem.readLE desc 8 + (i + i * 2) * 8 + 8) 8 =
      isTyp s.mem (s.mem.readLE desc 8) i := fun i => by
    simp only [isTyp]
    rw [show s.mem.readLE desc 8 + 8 + 24 * i = s.mem.readLE desc 8 + (i + i * 2) * 8 + 8 by omega]
  have hans : ∀ cw : Nat, cw = (switchCase R t.toNat [c]).1 →
      (if cw = 0 then 3 else 4) = result R c t.toNat := by
    intro cw hcw
    simp only [result, ht0, htu, hts, ite_false, hcw, switchCase_single]
    cases R.itab c t.toNat <;> rfl
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hpost : ∀ (s' : State), (s'.regs 0).toNat = result R c t.toNat → s'.mem = M0 s t x →
      Post R c t s s' := by
    intro s' h0 hm
    unfold Post; rw [hm]
    exact ⟨h0, ISDescOK.frame hdesc hMf hdo' hws, hMf.mono fun a n h => by
        simp only [window, outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.1.2,
      hl.env_frame _ _ _ henv (agrees_of_memFrame_outside hMf hws)⟩
  -- the hit: the cached case is the runtime's answer
  have hit : ∀ (S : State) (h : BitVec 64), h.toNat % 2 ^ k < 2 ^ k →
      t.toNat = isTyp s.mem (s.mem.readLE desc 8) (h.toNat % 2 ^ k) →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0xa8) →
      S.regs 2 = BitVec.ofNat 64 (s.mem.readLE desc 8) →
      (S.regs 1).toNat = 3 * (h.toNat % 2 ^ k) → S.regs 4 = s.regs 4 - 40#64 →
      S.regs 5 = s.regs 4 - 8#64 → S.regs 14 = s.regs 14 → S.xmm = s.xmm → S.df = s.df →
      S.mem = M0 s t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R c t s s') := by
    intro S h hmod heq hpc h2 h1 h4 h5 h14 hxm hdf' hm
    have hcase : Arm64.Memory.readLE s.mem (s.mem.readLE desc 8 + 3 * (h.toNat % 2 ^ k) * 8 + 16) 8 =
        (switchCase R t.toNat [c]).1 := by
      have := (hent _ hmod (by rw [← heq]; exact ht0)).1
      rw [← heq] at this
      rw [← this]; simp only [isCase]
      rw [show s.mem.readLE desc 8 + 16 + 24 * (h.toNat % 2 ^ k) =
        s.mem.readLE desc 8 + 3 * (h.toNat % 2 ^ k) * 8 + 16 by omega]
    simp only [M0] at hm
    have hlt := Arm64.Memory.readLE_lt s.mem (s.mem.readLE desc 8 + 3 * (h.toNat % 2 ^ k) * 8 + 16) 8
    rw [hcase] at hlt
    have hcl : (switchCase R t.toNat [c]).1 % 18446744073709551616 = (switchCase R t.toNat [c]).1 :=
      Nat.mod_eq_of_lt (by simpa using hlt)
    janus64_run [h1]
    all_goals exact ⟨by rw [hxm, hx15]; rfl, hpost _ (by
      simp only [setRegF, reduceIte, Nat.reduceEqDiff]; rw [← hans _ hcase]
      simp [hcase, hbr]) rfl⟩
  -- a miss: the call of `runtime.interfaceSwitch`
  have miss : ∀ (S : State), S.rip = BitVec.ofNat 64 (Extracted.entry + 0x97) → S.regs 0 = t →
      S.regs 4 = s.regs 4 - 40#64 → S.regs 5 = s.regs 4 - 8#64 → S.regs 14 = s.regs 14 →
      S.xmm = s.xmm → S.df = s.df → S.mem = M0 s t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R c t s s') := by
    intro S hpc h0 h4 h5 h14 hxm hdf' hm
    simp only [M0] at hm
    have hsp48 : (s.regs 4 - 40#64 - 8#64).toNat = (s.regs 4).toNat - 48 := by
      rw [BitVec.toNat_sub, hsp40]; simp; omega
    have hsp48' : (18446744073709551568 + (s.regs 4).toNat) % 18446744073709551616 =
        (s.regs 4).toNat - 48 := by omega
    have hd64 : desc % 2 ^ 64 = desc := Nat.mod_eq_of_lt (by omega)
    janus_eval_nat hD : desc
    have hdacc' := hdacc; have hdw' := hdw; have hdb' := hdb
    rw [hD] at hdacc' hdw' hdb'
    janus64_run until [Extracted.program.contractAddr "runtime.interfaceSwitch"]
    refine Reaches.call (Summary.withExit (hsw [c]) hret) rfl
      ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp48, hsp48']) (by simp [setRegF, h14])
        (by simp [hxm, hx15]) (by simp [hdf', hdf])
        (by simp [setRegF, hsp48, hsp48', Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide),
        ?_, ?_, ?_, ?_⟩ ?_
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, ← hD]
      exact ISDescOK.frame hdesc (by janus_frame) hdo' hws
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, h0]; exact ht0
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, h0]; exact hty
    · simp only [Janus.Contracts.Ready64, setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, h0,
        ← hD, h14]
      simp (disch := janus64_disch) only [Janus.Contracts.rtView_writeLE]
      have e1 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by bv_omega
      simpa [e1] using hH
    · intro s' hpc' ⟨r, x', y, fl, m', _, _, hs', hfr, henv', hcase, hitab, _, hdesc2⟩
      subst hs'
      simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
        Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, h0, hsp48, hsp48', ← hD] at hfr hcase hdesc2
      have hlt := BitVec.isLt (r 0)
      janus64_run
      all_goals
        refine ⟨by rw [hxm, hx15]; rfl, ?_, hdesc2, ?_, by simpa [setRegF, h14] using henv'⟩
      all_goals first
        | (simp only [setRegF, reduceIte, Nat.reduceEqDiff, Contracts.MapAmd64.keepABI_apply]
           rw [← hans _ hcase]; simp [hbr]; done)
        | (refine MemFrame.trans (rs := [((s.regs 4).toNat - (R.depth + 48), (s.regs 4).toNat + 24)])
             (by janus_frame) hfr fun a n h => ?_
           have hsp48'' : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
             rw [BitVec.toNat_sub]; simp; omega
           simp only [window, outside_append, outside_cons, outside_nil, and_true, hsp48, hsp48',
             hsp48''] at h ⊢
           exact ⟨h.1.2, ⟨h.1.1, by omega, by omega⟩, h.2⟩)
  intro n
  induction n with
  | zero =>
    intro S h hn hb' hpc h0 h1 h2 h6 h4 h5 h14 hxm hdf' hm
    simp only [M0] at hm
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    have hjr := probe_zero hj hmod hn
    janus64_run [hand] until [head, Extracted.entry + 0x97, Extracted.entry + 0xa8]
    · refine hit _ h hmod (by
          have h1 := Arm64.Memory.readLE_lt s.mem
            (s.mem.readLE desc 8 + (h.toNat % 2 ^ k + h.toNat % 2 ^ k * 2) * 8 + 8) 8
          have h2 := t.isLt
          rw [htyp] at h1; rw [htlt] at hbr; simp at h1; omega) (by rfl) (by simp [setRegF, h2])
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; exact probeIdx _ _ hk64 hkb)
        (by simp [setRegF, h4]) (by simp [setRegF, h5]) (by simp [setRegF, h14]) hxm
        (by simp [hdf', hdf]) rfl
    · exact miss _ (by rfl) (by simp [setRegF, h0]) (by simp [setRegF, h4]) (by simp [setRegF, h5])
        (by simp [setRegF, h14]) hxm (by simp [hdf', hdf]) rfl
    · exfalso
      rw [htlt, hjr, hj0] at hbr
      exact hbr rfl
  | succ n ih =>
    intro S h hn hb' hpc h0 h1 h2 h6 h4 h5 h14 hxm hdf' hm
    simp only [M0] at hm
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    janus64_run [hand] until [head, Extracted.entry + 0x97, Extracted.entry + 0xa8]
    · refine hit _ h hmod (by
          have h1 := Arm64.Memory.readLE_lt s.mem
            (s.mem.readLE desc 8 + (h.toNat % 2 ^ k + h.toNat % 2 ^ k * 2) * 8 + 8) 8
          have h2 := t.isLt
          rw [htyp] at h1; rw [htlt] at hbr; simp at h1; omega) (by rfl) (by simp [setRegF, h2])
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; exact probeIdx _ _ hk64 hkb)
        (by simp [setRegF, h4]) (by simp [setRegF, h5]) (by simp [setRegF, h14]) hxm
        (by simp [hdf', hdf]) rfl
    · exact miss _ (by rfl) (by simp [setRegF, h0]) (by simp [setRegF, h4]) (by simp [setRegF, h5])
        (by simp [setRegF, h14]) hxm (by simp [hdf', hdf]) rfl
    · have hne : h.toNat % 2 ^ k ≠ j := fun he => by rw [htlt, he, hj0] at hbr; exact hbr rfl
      have h1' : (h + 1#64).toNat = h.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      refine ih _ (h + 1#64) ?_ ?_ (by rfl) (by simp [setRegF, h0]) (by simp [setRegF])
        (by simp [setRegF, h2]) (by simp [setRegF, h6]) (by simp [setRegF, h4])
        (by simp [setRegF, h5]) (by simp [setRegF, h14]) hxm (by simp [hdf', hdf]) rfl
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
theorem correctness (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws) (H : Janus.Contracts.RtReady)
    (hsw : InterfaceSwitch (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.interfaceSwitch") R H)
    (c : Nat) (t x : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [t, x]
      (fun s => CallerOK R s 48 24 ∧ Extracted.program.DataLoaded s.mem ∧
        ISDescOK R s.mem desc [c] ∧ Outside desc 24 (window R s) ∧
        (t.toNat ≠ 0 → R.IsType t.toNat) ∧ H [desc, t.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 48)
          (Janus.Contracts.rtView R.priv s.mem))
      (fun s s' => Post R c t s s' ∧
        (StaticItabs R Extracted.program.data → c = hasherInter → t.toNat = mulHasherType →
          (s'.regs 0).toNat = 3)) := by
  intro ret hret s hs ⟨hc, hdl, hdesc, hdo, hty, hH⟩
  suffices hmain : Reaches ((Extracted.program.link impl).withExit ret) s
      (IsReturn fun s' => ABIReturn s s' ∧ Post R c t s s') by
    exact (returns_of_reaches hmain).mono fun s' h =>
      ⟨h.1, h.2, fun hst hi htt => static_case R c t s s' h.2 hst hi htt⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  janus64_data hdl [hst]
  simp only [window, outside_cons, outside_nil, and_true] at hdo
  janus_eval_nat hU : u64T
  janus_eval_nat hS : strT
  janus_eval_nat hD : desc
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, hdw, hn1, hcs, hint, k, hk, hcb, hcacc, hcin, hent, j, hj, hj0⟩ := hdesc'
  have hdc := InRanges.disjoint hcin hout
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [((s.regs 4).toNat - (R.depth + 48), (s.regs 4).toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo' : Outside desc 24 [((s.regs 4).toNat - (R.depth + 48), (s.regs 4).toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hx15 : s.xmm 15 = 0 := by simpa using hs.zero
  have hdf : s.df = false := by simpa using hs.df
  have hcacc' := hcacc; have hdacc' := hdacc; have hdw' := hdw; have hdo'' := hdo
  have hdc' := hdc; have hdb' := hdb
  rw [hD] at hcacc' hdacc' hdw' hdo'' hdc' hdb'
  -- the returns without a runtime call
  have fin : ∀ (v : Nat) (m : Janus.Arm64.Memory), v = result R c t.toNat →
      MemFrame s.mem m [((s.regs 4).toNat - (R.depth + 48), (s.regs 4).toNat + 24)] →
      ∀ s' : State, (s'.regs 0).toNat = v → s'.mem = m → Post R c t s s' := by
    intro v m hv hm s' h0 h1
    unfold Post; rw [h1]
    exact ⟨by rw [h0, hv], ISDescOK.frame hdesc hm hdo' hws, hm.mono fun a n h => by
        simp only [window, outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.1.2,
      hl.env_frame _ _ _ henv (agrees_of_memFrame_outside hm hws)⟩
  by_cases ht0 : t.toNat = 0
  · janus64_run
    exact fin 0 _ (by simp [result, ht0]) (by janus_frame) _ (by simp [setRegF]) rfl
  by_cases htu : t.toNat = u64T
  · obtain rfl : t = BitVec.ofNat 64 (janus_eval% u64T) := by
      apply BitVec.eq_of_toNat_eq; rw [htu, hU]; rfl
    janus64_run
    exact fin 1 _ (by simp [result, hU]) (by janus_frame) _ (by simp [setRegF]) rfl
  by_cases hts : t.toNat = strT
  · obtain rfl : t = BitVec.ofNat 64 (janus_eval% strT) := by
      apply BitVec.eq_of_toNat_eq; rw [hts, hS]; rfl
    janus64_run
    exact fin 2 _ (by simp [result, hU, hS]) (by janus_frame) _ (by simp [setRegF]) rfl
  obtain ⟨-, htb, htacc, htin⟩ := hl.type_desc _ _ _ henv (hty ht0)
  simp only [typeDescSize] at htb htacc htin
  have hdt := InRanges.disjoint htin hout
  have hhash := Arm64.Memory.readLE_lt s.mem (t.toNat + 16) 4
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  have hkb : 2 ^ k < 2 ^ 44 := by omega
  have hh : (BitVec.setWidth 64 (BitVec.ofNat 32 (Arm64.Memory.readLE s.mem (t.toNat + 16) 4))).toNat =
      Arm64.Memory.readLE s.mem (t.toNat + 16) 4 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; simp at hhash; omega
  have hpr := probe_lt (j := j) (r := Arm64.Memory.readLE s.mem (t.toNat + 16) 4) hN
  janus64_run until [head]
  all_goals
    refine loop impl R hl H hsw c t x ret hret s hc hdesc hdo ht0 (hty ht0) htu hts h_ret hx15 hdf hH k hk
      hcb hcacc hcin hent j hj hj0 _ _ (BitVec.setWidth 64 (BitVec.ofNat 32
        (Arm64.Memory.readLE s.mem (t.toNat + 16) 4))) rfl ?_ (by rfl)
      (by simp [setRegF, h_a0]) (by simp [setRegF]) (by simp [setRegF, hD])
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; rw [← hD, hk]) (by simp [setRegF])
      (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp [hdf]) (by simp [M0])
    rw [hh]; simp at hhash; omega


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model of the runtime (`IfaceModel.R0`), code at `runtime.interfaceSwitch`'s address that
meets the `InterfaceSwitch` contract for it (`IfaceSatAmd64.interfaceSwitchCode`), an admissible
return address and a call state switching on a box of the model's type `TD`, with the read-only
data loaded and the descriptor at its real address (one case, the model's interface `ID`, the
empty cache): `correctness` applies, and `Classify` takes the interface case (`3`). -/

namespace Witness

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64
open Janus.Contracts (IfaceSat.itabAt_TAB IfaceSat.itabResult_R0 IfaceSat.efaceEqual_R0)

/-- `runtime.interfaceSwitch`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.interfaceSwitch"

/-- `IfaceSatAmd64.interfaceSwitchCode` at `runtime.interfaceSwitch`'s address. -/
def implAt : List Janus.Amd64.Segment := [{ name := "model", base := cAddr, bytes := interfaceSwitchCode }]

/-- The program linked with it, as a closed program. -/
def linked : Janus.Amd64.Program :=
  { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : InterfaceSwitch (Extracted.program.link implAt) cAddr R0 Htrue := by
  rw [linked_eq]
  intro cs s hpc ⟨hpre, hdesc, ht0, ht, _⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, -, hn, -, hcs, -⟩ := hdesc'
  have hcs' : ∀ c ∈ cs, c = ID := hcs
  have hlen : cs.length < 2 ^ 48 := by omega
  have hsw := Janus.Contracts.IfaceModel.switchCase_R0 (s.regs 3).toNat cs hcs'
  have hlt3 := (s.regs 3).isLt
  by_cases htd : (s.regs 3).toNat = 65536 <;> by_cases hc0 : cs.length = 0
  all_goals
    janus64_run [hn]
    refine rtReturn_of R0 2 _ s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    simp only [setRegF, reduceIte, Nat.reduceEqDiff]
    refine ⟨?_, ?_, ?_, hdesc⟩
  all_goals (try rw [htd]) <;> (try rw [hsw]) <;> (try rw [htd] at hsw)
  all_goals (try simp only [BitVec.toNat_ofNat])
  all_goals first
    | (simp_all [TD, TAB]; done)
    | (intro hne
       obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
         cases cs with
         | nil => simp_all
         | cons c cs' => exact ⟨c, cs', rfl⟩
       rw [hcs' c (by simp)]
       simpa [TD, TAB, htd] using IfaceSat.itabAt_TAB (g := s.regs 14) ⟨he1, he2, hd⟩)
    | (rw [ite_eq_right (fun h => by simp only [TD] at h; omega)]; exact Nat.mod_eq_of_lt (by omega))
    | done


/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide +kernel)

/-- A byte of the program's read-only data, if `a` is in one of its objects. -/
def dbyte (a : Nat) : Option Nat :=
  Extracted.program.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

/-- The witness memory: the read-only data in read-only regions, the return address `ret` at
`[RSP]`, the descriptor at `desc` (cache `ISC`, `NCases = 1`, `Cases[0] = ID`) in a writable
region, and `wmem`. -/
def mem2 : Janus.Arm64.Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyte a).getD ((([(wsp + 2, 0x20), (desc + 1, 0x05),
      (desc + 2, 0x01), (desc + 8, 1), (desc + 17, 0x01), (desc + 18, 0x01)] ++
      wtable).lookup a).getD 0)),
    wmem.regions ++ [⟨desc - desc % 4096, 0x1000, true⟩] ++
      Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

theorem mem2_env (g : W64) : Env0 mem2 g := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  unfold Desc; decide +kernel

theorem mem2_data : Extracted.program.DataLoaded mem2 := by
  unfold Janus.Amd64.Program.DataLoaded; decide +kernel

theorem mem2_desc : ISDescOK R0 mem2 desc [ID] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, fun i hi => ?_,
    by simp, ?_⟩
  · simp at hi; subst hi; show mem2.readLE (desc + 16) 8 = ID; decide +kernel
  · rw [show mem2.readLE desc 8 = ISC by decide +kernel]
    exact ISCacheOK.empty (by decide +kernel) (by decide +kernel) (inPriv (by decide +kernel) (by decide +kernel))
      (by decide +kernel) (by decide +kernel)

/-- `TD` and the value slot `VAL`, as words. -/
def td : BitVec 64 := BitVec.ofNat 64 TD
def val : BitVec 64 := BitVec.ofNat 64 VAL

/-- The witness call state: `Classify(x)` for the box `x = (TD, VAL)`. -/
def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then td else if i = 3 then val
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem2 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [td, val] s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide +kernel, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem pre : CallerOK R0 s0 48 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    ISDescOK R0 s0.mem desc [ID] ∧ Outside desc 24 (window R0 s0) ∧
    (td.toNat ≠ 0 → R0.IsType td.toNat) := by
  refine ⟨⟨mem2_env (s0.regs 14), ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩, mem2_data, mem2_desc, ?_,
    fun _ => Or.inl rfl⟩
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide +kernel
  · unfold Janus.Spec.Disjoint; decide +kernel
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [window, outside_cons, outside_nil, and_true]; decide +kernel

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : IfaceModel) (H : Janus.Contracts.RtReady)
    (c : Nat) (ret : Nat) (s : Janus.Amd64.State) (t x : BitVec 64), R.Laws ∧
    InterfaceSwitch (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.interfaceSwitch") R H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [t, x] s ∧
    (CallerOK R s 48 24 ∧ Extracted.program.DataLoaded s.mem ∧
      ISDescOK R s.mem desc [c] ∧ Outside desc 24 (window R s) ∧ (t.toNat ≠ 0 → R.IsType t.toNat) ∧
      H [desc, t.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 48) (Janus.Contracts.rtView R.priv s.mem)) :=
  ⟨implAt, R0, Htrue, ID, ret, s0, td, val, R0_laws, model, hret, setup,
    pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2, trivial⟩

/-- So the guarantee is reached: a box of `TD` takes the interface case `ID` (`3`). -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 3 := by
  refine (correctness implAt R0 R0_laws Htrue model ID td val ret hret s0 setup
    ⟨pre.1, pre.2.1, pre.2.2.1, pre.2.2.2.1, pre.2.2.2.2, trivial⟩).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2.1.1]
  janus_eval_nat hU : u64T
  janus_eval_nat hS : strT
  simp only [result, hU, hS]
  decide +kernel

end Witness

end Proof
