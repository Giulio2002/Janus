import Janus
import Extracted

/-!
# `AsHasher(x any) (Hasher, bool)`: the comma-ok type assertion `h, ok := x.(Hasher)` (amd64)

**Guarantee.** For every interface value `x = (t, data)`, every model `R` of the interface
runtime satisfying its laws, every implementation of `runtime.typeAssert` satisfying the
`TypeAssert` contract (`Janus/Contracts/IfaceAmd64.lean`) and every Go call state in which the runtime is
usable with `R.depth` bytes of stack below `AsHasher`'s frame (`CallerOK`), the type-assertion
descriptor `desc` the code loads (`example.com/basic..typeAssert.0`, a writable global; its
address recomputed from the extracted code) is well formed with `CanFail` set (`TADescOK`: a
non-empty interface type and a well-formed cache), it does not overlap the stack window, and the
dynamic type of a non-nil `x` is a type descriptor, the call returns, obeys the ABI, and (`Post`):

* `RAX` is the itab of `t` for the descriptor's interface: `0` if `x` is nil, otherwise
  `getitab`'s answer `(R.itab inter t).getD 0` (`0` if `t` does not implement it);
* `RBX` is the data word, and `ok` (`CL`) is `1` exactly when the itab is non-zero;
* the descriptor is still well formed, with the same interface, and memory changed only in the
  runtime's memory, the stack window and the descriptor's `Cache` word;
* when the dynamic type is `*MulHasher` and the descriptor's interface is `Hasher` (the `Inter`
  and `Type` words of the static itab `go:itab.*MulHasher,Hasher`, copied by `--targets`), the
  result is that static itab and `ok = 1`, provided `getitab` returns the static itabs
  (`StaticItabs`, true of a statically linked Go 1.26 binary: docs/RUNTIME-CONTRACTS.md).

This holds whatever the state of the assertion cache: the inline probe (`loop`, by induction on
the cyclic distance to an empty entry) either hits an entry, whose itab is the runtime's answer
(`TACacheOK`), or reaches an empty one and calls `runtime.typeAssert` (`miss`).

**Assumptions (all in the statement).** `R` is *any* model satisfying `R.Laws`, and the code at
`runtime.typeAssert` is *any* code that behaves as `TypeAssert` says; the extraction pins that
function to the Go runtime's code (`(pinned)` in the report).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts.Iface Janus.Contracts.IfaceAmd64

namespace Proof

/-- The address of the type-assertion descriptor `example.com/basic..typeAssert.0` (`.data`): the
RIP-relative operand of `MOVQ ..typeAssert.0(SB), DX` at `AsHasher+0x1d`. -/
def desc : Nat := ripTarget Extracted.program (Extracted.entry + 0x1d)

/-- The loop head of the cache probe (`MOVQ DI, R8`). -/
abbrev head : Nat := Extracted.entry + 0x38

/-- The guarantee: the itab of `x.(Hasher)` for the dynamic type `t` (`0` for nil or a type that
does not implement it) in `RAX`, the data word in `RBX`, `ok` (`RAX ≠ 0`) in `CL`; the
descriptor still well formed; memory changed only in the runtime's memory, the stack window and
the descriptor's `Cache` word; the runtime still usable. -/
def Post (R : IfaceModel) (t x : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat = (if t.toNat = 0 then 0 else (R.itab (taInter s.mem desc) t.toNat).getD 0) ∧
    s'.regs 3 = x ∧ (s'.regs 1).toNat % 256 = (if (s'.regs 0).toNat = 0 then 0 else 1) ∧
    TADescOK R s'.mem desc ∧ taInter s'.mem desc = taInter s.mem desc ∧
    MemFrame s.mem s'.mem
      (R.priv ++ [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24), (desc, desc + 8)]) ∧
    R.Env s'.mem (s.regs 14)

/-- The memory at the loop head: the caller's memory with the saved frame pointer and the two
spills. -/
def M0 (s : State) (t x : BitVec 64) : Janus.Arm64.Memory :=
  ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 8) 8
    t.toNat).writeLE ((s.regs 4).toNat + 16) 8 x.toNat

/-- The entry address the probe computes (`((h & Mask) << 4) + cache + 8`). -/
theorem probeAddr (c k : Nat) (h : BitVec 64) (hk : k ≤ 64) (hc : c + 8 + 16 * 2 ^ k ≤ 2 ^ 48) :
    ((h &&& BitVec.ofNat 64 (2 ^ k - 1)) <<< 4).toNat = 16 * (h.toNat % 2 ^ k) := by
  have hm := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
  rw [Janus.Tactic.bv_toNat_shiftLeft, and_mask_toNat h k hk, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- A cache miss: the call of `runtime.typeAssert` and the return. -/
theorem miss (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws)
    (hta : TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R)
    (t x : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hc : CallerOK R s 40 24) (hdesc : TADescOK R s.mem desc) (hcf : taCanFail s.mem desc = true)
    (hdo : desc + 24 ≤ (s.regs 4).toNat - (R.depth + 40) ∨ (s.regs 4).toNat + 24 ≤ desc)
    (ht0 : t.toNat ≠ 0) (hty : R.IsType t.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 = ret) (hx15 : s.xmm 15 = 0) (hdf : s.df = false) :
    ∀ (S : State), S.rip = BitVec.ofNat 64 (Extracted.entry + 0x55) → S.regs 0 = t → S.regs 3 = x →
      S.regs 4 = s.regs 4 - 32#64 → S.regs 5 = s.regs 4 - 8#64 → S.regs 14 = s.regs 14 →
      S.xmm = s.xmm → S.df = s.df → S.mem = M0 s t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R t x s s') := by
  intro S hpc h0 h3 h4 h5 h14 hxm hdf' hm
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, hdw, hdi, -⟩ := hdesc'
  simp only [M0] at hm
  have hsp32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hsp40 : (s.regs 4 - 32#64 - 8#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub, hsp32]; simp; omega
  have hsp40' : (18446744073709551576 + (s.regs 4).toNat) % 18446744073709551616 =
      (s.regs 4).toNat - 40 := by omega
  have hd64 : desc % 2 ^ 64 = desc := Nat.mod_eq_of_lt (by omega)
  janus_eval_nat hD : desc
  have hdacc' := hdacc; have hdw' := hdw; have hdo' := hdo; have hdb' := hdb
  rw [hD] at hdacc' hdw' hdo' hdb'
  janus64_run until [Extracted.program.contractAddr "runtime.typeAssert"]
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo'' : Outside desc 24 [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  refine Reaches.call (Summary.withExit hta hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp40, hsp40']) (by simp [setRegF, h14])
      (by simp [hxm, hx15]) (by simp [hdf', hdf])
      (by simp [setRegF, hsp40, hsp40', Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide), ?_, ?_, ?_⟩ ?_
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, ← hD]
    exact TADescOK.frame hdesc (by janus_frame) hdo'' hws
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, h0]; intro h; exact absurd h ht0
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, h0, ← hD]
    intro _; refine ⟨hty, Or.inl ?_⟩
    exact (taCanFail_frame (m := s.mem) (by janus_frame) hdo'').trans hcf
  · intro s' hpc' ⟨r, x', y, fl, m', _, _, hs', hfr, henv', hres, hdesc2, hinter2, hcf2⟩
    subst hs'
    simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
      Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, h0, hsp40, hsp40', ← hD] at hfr hres hdesc2 hinter2 hcf2
    janus64_run
    obtain ⟨MM, hMM⟩ : ∃ MM, MM = ((M0 s t x).writeLE ((s.regs 4).toNat + 16) 8 x.toNat).writeLE
        ((s.regs 4).toNat - 40) 8 (janus_eval% (Extracted.entry + 0x69)) := ⟨_, rfl⟩  -- the pushed return address
    simp only [M0] at hMM
    rw [← hMM] at hres hinter2 hcf2 hfr
    have hMf : MemFrame s.mem MM [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] := by
      rw [hMM]; janus_frame
    rw [taInter_frame hMf hdo''] at hres hinter2
    refine ⟨by rw [hxm, hx15]; rfl, ?_, by simp [setRegF], ?_, hdesc2, hinter2, ?_,
      by simpa [setRegF, h14] using henv'⟩
    · simpa [setRegF, Contracts.MapAmd64.keepABI] using hres.1
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, Contracts.MapAmd64.keepABI_apply, setcc_low_byte]
      split <;> simp_all
    · refine hMf.trans hfr fun a n h => ?_
      have hsp40'' : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
        rw [BitVec.toNat_sub]; simp; omega
      simp only [outside_append, outside_cons, outside_nil, and_true, hsp40'', hsp40'] at h ⊢
      exact ⟨h.2.1, ⟨h.1, by omega, by omega⟩, h.2.2⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem loop (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws)
    (hta : TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R)
    (t x : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hc : CallerOK R s 40 24) (hdesc : TADescOK R s.mem desc) (hcf : taCanFail s.mem desc = true)
    (hdo : desc + 24 ≤ (s.regs 4).toNat - (R.depth + 40) ∨ (s.regs 4).toNat + 24 ≤ desc)
    (ht0 : t.toNat ≠ 0) (hty : R.IsType t.toNat)
    (hra : s.mem.readLE (s.regs 4).toNat 8 = ret) (hx15 : s.xmm 15 = 0) (hdf : s.df = false) (k : Nat)
    (hk : s.mem.readLE (s.mem.readLE desc 8) 8 = 2 ^ k - 1)
    (hcb : s.mem.readLE desc 8 + 8 + 16 * 2 ^ k ≤ 2 ^ 48)
    (hcacc : s.mem.accessible (s.mem.readLE desc 8) (8 + 16 * 2 ^ k) false = true)
    (hcin : InRanges (s.mem.readLE desc 8) (8 + 16 * 2 ^ k) R.priv)
    (hent : ∀ i, i < 2 ^ k → taTyp s.mem (s.mem.readLE desc 8) i ≠ 0 →
      taItab s.mem (s.mem.readLE desc 8) i =
        (R.itab (taInter s.mem desc) (taTyp s.mem (s.mem.readLE desc 8) i)).getD 0)
    (j : Nat) (hj : j < 2 ^ k) (hj0 : taTyp s.mem (s.mem.readLE desc 8) j = 0) :
    ∀ n (S : State) (h : BitVec 64), (j + 2 ^ k - h.toNat % 2 ^ k) % 2 ^ k = n →
      h.toNat + n < 2 ^ 46 →
      S.rip = BitVec.ofNat 64 head → S.regs 0 = t → S.regs 3 = x →
      S.regs 2 = BitVec.ofNat 64 (s.mem.readLE desc 8) → S.regs 6 = BitVec.ofNat 64 (2 ^ k - 1) →
      S.regs 7 = h → S.regs 4 = s.regs 4 - 32#64 → S.regs 5 = s.regs 4 - 8#64 →
      S.regs 14 = s.regs 14 → S.xmm = s.xmm → S.df = s.df → S.mem = M0 s t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R t x s s') := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, hdw, hdi, -⟩ := hdesc'
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
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo' : Outside desc 24 [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hMf : MemFrame s.mem (M0 s t x) [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] := by
    simp only [M0]; janus_frame
  have htlt : ∀ i, taTyp s.mem (s.mem.readLE desc 8) i % 18446744073709551616 =
      taTyp s.mem (s.mem.readLE desc 8) i := fun i => Nat.mod_eq_of_lt (Arm64.Memory.readLE_lt _ _ _)
  have htyp : ∀ i, Arm64.Memory.readLE s.mem (i * 16 + (s.mem.readLE desc 8 + 8)) 8 =
      taTyp s.mem (s.mem.readLE desc 8) i := fun i => by
    simp only [taTyp]
    rw [show s.mem.readLE desc 8 + 8 + 16 * i = i * 16 + (s.mem.readLE desc 8 + 8) by omega]
  have hsp32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp; omega
  -- the hit: the cached itab is the runtime's answer
  have hit : ∀ (S : State) (h : BitVec 64), h.toNat % 2 ^ k < 2 ^ k →
      t.toNat = taTyp s.mem (s.mem.readLE desc 8) (h.toNat % 2 ^ k) →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0x70) → S.regs 0 = t → S.regs 3 = x →
      S.regs 2 = BitVec.ofNat 64 (s.mem.readLE desc 8) →
      (S.regs 7).toNat = 16 * (h.toNat % 2 ^ k) → S.regs 4 = s.regs 4 - 32#64 →
      S.regs 5 = s.regs 4 - 8#64 → S.regs 14 = s.regs 14 → S.xmm = s.xmm → S.df = s.df →
      S.mem = M0 s t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R t x s s') := by
    intro S h hmod heq hpc h0 h3 h2 h7 h4 h5 h14 hxm hdf' hm
    simp only [M0] at hm
    janus64_run [h7]
    have hitab : Arm64.Memory.readLE s.mem (16 * (h.toNat % 2 ^ k) + (s.mem.readLE desc 8 + 16)) 8 =
        (R.itab (taInter s.mem desc) t.toNat).getD 0 := by
      have := hent _ hmod (by rw [← heq]; exact ht0)
      rw [← heq] at this
      rw [← this]; simp only [taItab]
      rw [show s.mem.readLE desc 8 + 16 + 16 * (h.toNat % 2 ^ k) =
        16 * (h.toNat % 2 ^ k) + (s.mem.readLE desc 8 + 16) by omega]
    have hlt := Arm64.Memory.readLE_lt s.mem (16 * (h.toNat % 2 ^ k) + (s.mem.readLE desc 8 + 16)) 8
    rw [hitab] at hlt
    refine ⟨by rw [hxm, hx15]; rfl, ?_, by simp [setRegF, h3], ?_, TADescOK.frame hdesc hMf hdo' hws,
      taInter_frame hMf hdo', hMf.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.2.1,
      hl.env_frame _ _ _ henv (agrees_of_memFrame_outside hMf hws)⟩
    · simp [setRegF, hitab, ht0, Nat.mod_eq_of_lt hlt]
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, setcc_low_byte, hitab, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlt]
      split <;> simp
  intro n
  induction n with
  | zero =>
    intro S h hn hb' hpc h0 h3 h2 h6 h7 h4 h5 h14 hxm hdf' hm
    simp only [M0] at hm
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    have hjr := probe_zero hj hmod hn
    janus64_run [hand] until [head, Extracted.entry + 0x55, Extracted.entry + 0x70]
    · refine hit _ h hmod (by
          have h1 := Arm64.Memory.readLE_lt s.mem (h.toNat % 2 ^ k * 16 + (s.mem.readLE desc 8 + 8)) 8
          have h2 := t.isLt
          rw [htyp] at h1; rw [htlt] at hbr; simp at h1; omega) (by rfl) (by simp [setRegF, h0])
        (by simp [setRegF, h3]) (by simp [setRegF, h2])
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; exact probeAddr _ _ _ hk64 hcb)
        (by simp [setRegF, h4]) (by simp [setRegF, h5]) (by simp [setRegF, h14]) hxm (by simp [hdf', hdf]) rfl
    · exact miss impl R hl hta t x ret hret s hc hdesc hcf hdo ht0 hty hra hx15 hdf _ (by rfl)
        (by simp [setRegF, h0]) (by simp [setRegF, h3]) (by simp [setRegF, h4]) (by simp [setRegF, h5])
        (by simp [setRegF, h14]) hxm (by simp [hdf', hdf]) rfl
    · exfalso
      rw [htlt, hjr, hj0] at hbr
      exact hbr rfl
  | succ n ih =>
    intro S h hn hb' hpc h0 h3 h2 h6 h7 h4 h5 h14 hxm hdf' hm
    simp only [M0] at hm
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    janus64_run [hand] until [head, Extracted.entry + 0x55, Extracted.entry + 0x70]
    · refine hit _ h hmod (by
          have h1 := Arm64.Memory.readLE_lt s.mem (h.toNat % 2 ^ k * 16 + (s.mem.readLE desc 8 + 8)) 8
          have h2 := t.isLt
          rw [htyp] at h1; rw [htlt] at hbr; simp at h1; omega) (by rfl) (by simp [setRegF, h0])
        (by simp [setRegF, h3]) (by simp [setRegF, h2])
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; exact probeAddr _ _ _ hk64 hcb)
        (by simp [setRegF, h4]) (by simp [setRegF, h5]) (by simp [setRegF, h14]) hxm (by simp [hdf', hdf]) rfl
    · exact miss impl R hl hta t x ret hret s hc hdesc hcf hdo ht0 hty hra hx15 hdf _ (by rfl)
        (by simp [setRegF, h0]) (by simp [setRegF, h3]) (by simp [setRegF, h4]) (by simp [setRegF, h5])
        (by simp [setRegF, h14]) hxm (by simp [hdf', hdf]) rfl
    · have hne : h.toNat % 2 ^ k ≠ j := fun he => by rw [htlt, he, hj0] at hbr; exact hbr rfl
      have h1' : (h + 1#64).toNat = h.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      refine ih _ (h + 1#64) ?_ ?_ (by rfl) (by simp [setRegF, h0]) (by simp [setRegF, h3])
        (by simp [setRegF, h2]) (by simp [setRegF, h6]) (by simp [setRegF]) (by simp [setRegF, h4])
        (by simp [setRegF, h5]) (by simp [setRegF, h14]) hxm (by simp [hdf', hdf]) rfl
      · rw [h1']; have := probe_dist (2 ^ k) j h.toNat hj hne; omega
      · rw [h1']; omega

/-- The static itab of `*MulHasher` for `Hasher` (copied by `--targets`). -/
abbrev mulItab : String := "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher"
/-- Its `Inter` word: the address of the `Hasher` interface type. -/
def hasherInter : Nat := dataWord Extracted.program.data mulItab 0 8
/-- Its `Type` word: the address of the `*MulHasher` type descriptor. -/
def mulHasherType : Nat := dataWord Extracted.program.data mulItab 8 8
/-- Its address. -/
def mulHasherItab : Nat := dataAddr Extracted.program.data mulItab

/-- For a `*MulHasher` the assertion succeeds with the static itab (`StaticItabs`). -/
theorem static_case (R : IfaceModel) (t x : BitVec 64) (s s' : State) (hp : Post R t x s s')
    (hst : StaticItabs R Extracted.program.data) (hi : taInter s.mem desc = hasherInter)
    (htt : t.toNat = mulHasherType) :
    (s'.regs 0).toNat = mulHasherItab ∧ (s'.regs 1).toNat % 256 = 1 := by
  obtain ⟨d, hd⟩ : ∃ d, dataNamed Extracted.program.data mulItab = some d := ⟨_, rfl⟩
  have hsome := hst.named hd (by decide +kernel)
    (by rw [show d = _ from (Option.some.inj hd).symm]; decide)
  janus_eval_nat hT : mulHasherType
  janus_eval_nat hI : mulHasherItab
  have hT0 : t.toNat ≠ 0 := by rw [htt, hT]; decide
  obtain ⟨h0, -, h2, -⟩ := hp
  rw [hi, ite_eq_right hT0, htt] at h0
  simp only [hasherInter, mulHasherType] at hsome h0
  rw [hsome] at h0
  simp only [Option.getD_some] at h0
  refine ⟨h0, ?_⟩
  rw [h2, h0]
  simp only [mulHasherItab] at hI
  rw [hI]; decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem correctness (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws)
    (hta : TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R)
    (t x : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [t, x]
      (fun s => CallerOK R s 40 24 ∧ TADescOK R s.mem desc ∧ taCanFail s.mem desc = true ∧
        Outside desc 24 [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] ∧
        (t.toNat ≠ 0 → R.IsType t.toNat))
      (fun s s' => Post R t x s s' ∧
        (StaticItabs R Extracted.program.data → taInter s.mem desc = hasherInter →
          t.toNat = mulHasherType →
          (s'.regs 0).toNat = mulHasherItab ∧ (s'.regs 1).toNat % 256 = 1)) := by
  intro ret hret s hs ⟨hc, hdesc, hcf, hdo, hty⟩
  suffices hmain : Reaches ((Extracted.program.link impl).withExit ret) s
      (IsReturn fun s' => ABIReturn s s' ∧ Post R t x s s') by
    exact (returns_of_reaches hmain).mono fun s' h =>
      ⟨h.1, h.2, fun hst hi htt => static_case R t x s s' h.2 hst hi htt⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  simp only [outside_cons, outside_nil, and_true] at hdo
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, hdw, hdi, k, hk, hcb, hcacc, hcin, hent, j, hj, hj0⟩ := hdesc'
  simp only [taCache] at hk hcb hcacc hcin hent hj0
  have hdc := InRanges.disjoint hcin hout
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo' : Outside desc 24 [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hx15 : s.xmm 15 = 0 := by simpa using hs.zero
  have hdf : s.df = false := by simpa using hs.df
  janus_eval_nat hD : desc
  have hcacc' := hcacc; have hdacc' := hdacc; have hdw' := hdw; have hdo'' := hdo
  have hdc' := hdc; have hdb' := hdb
  rw [hD] at hcacc' hdacc' hdw' hdo'' hdc' hdb'
  by_cases ht0 : t.toNat = 0
  · janus64_run
    have hMf : MemFrame s.mem ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
        ((s.regs 4).toNat + 8) 8 0 |>.writeLE ((s.regs 4).toNat + 16) 8 x.toNat)
        [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] := by janus_frame
    refine ⟨by simp [setRegF, h_a0, ht0], by simp [setRegF, h_a1], ?_,
      TADescOK.frame hdesc hMf hdo' hws, taInter_frame hMf hdo', hMf.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.2.1,
      hl.env_frame _ _ _ henv (agrees_of_memFrame_outside hMf hws)⟩
    have := setcc_low_byte (s.regs 1) 0#8
    simpa [setRegF, h_a0, ht0] using this
  · obtain ⟨-, htb, htacc, htin⟩ := hl.type_desc _ _ _ henv (hty ht0)
    simp only [typeDescSize] at htb htacc htin
    have hdt := InRanges.disjoint htin hout
    have hhash := Arm64.Memory.readLE_lt s.mem (t.toNat + 16) 4
    have hN : 0 < 2 ^ k := Nat.two_pow_pos k
    have hkb : 2 ^ k < 2 ^ 44 := by omega
    janus64_run until [head]
    have hh : (BitVec.setWidth 64 (BitVec.ofNat 32 (Arm64.Memory.readLE s.mem (t.toNat + 16) 4))).toNat =
        Arm64.Memory.readLE s.mem (t.toNat + 16) 4 := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; simp at hhash; omega
    refine loop impl R hl hta t x ret hret s hc hdesc hcf hdo ht0 (hty ht0) h_ret hx15 hdf k hk hcb
      hcacc hcin hent j hj hj0 _ _ (BitVec.setWidth 64 (BitVec.ofNat 32
        (Arm64.Memory.readLE s.mem (t.toNat + 16) 4))) rfl ?_ (by rfl)
      (by simp [setRegF, h_a0]) (by simp [setRegF, h_a1]) (by simp [setRegF, hD])
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; rw [← hD, hk]) (by simp [setRegF])
      (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp [hdf]) (by simp [M0])
    have := probe_lt (j := j) (r := Arm64.Memory.readLE s.mem (t.toNat + 16) 4) hN
    rw [hh]; simp at hhash; omega


/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model of the runtime (`IfaceModel.R0`), code at `runtime.typeAssert`'s address that meets
the `TypeAssert` contract for it (`IfaceSatAmd64.assertE2I2Code`), an admissible return address
and a call state asserting a box of the model's type `TD` to its interface `ID`, the descriptor
at its real address holding the empty cache: `correctness` applies, and the assertion succeeds
with the itab `TAB`. -/

namespace Witness

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64
open Janus.Contracts (IfaceSat.itabAt_TAB IfaceSat.itabResult_R0 IfaceSat.efaceEqual_R0)

/-- `runtime.typeAssert`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.typeAssert"

/-- `IfaceSatAmd64.assertE2I2Code` at `runtime.typeAssert`'s address. -/
def implAt : List Janus.Amd64.Segment := [{ name := "model", base := cAddr, bytes := assertE2I2Code }]

/-- The program linked with it, as a closed program. -/
def linked : Janus.Amd64.Program :=
  { Extracted.program with segments := Extracted.program.segments ++ implAt }

theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : TypeAssert (Extracted.program.link implAt) cAddr R0 := by
  rw [linked_eq]
  intro s hpc ⟨hpre, hdesc, _, _⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  have hi : taInter s.mem (s.regs 0).toNat = ID := hdesc.2.2.2.1
  have := IfaceSat.itabResult_R0 (g := s.regs 14) ⟨he1, he2, hd⟩ (s.regs 3).toNat
  janus64_run
  all_goals
    refine rtReturn_of R0 2 _ s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    refine ⟨?_, hdesc, rfl, rfl⟩
    rw [hi]
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    simp only [TD, TAB] at this
    have hlt := (s.regs 3).isLt
    first
      | (have h3 : (s.regs 3).toNat = 65536 := by omega
         simpa [h3] using this)
      | (have h3 : (s.regs 3).toNat ≠ 65536 := by omega
         simpa [h3] using this)

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide +kernel)

/-- The witness memory: `wmem` with the return address `ret` at `[RSP]` and the descriptor at
`desc` (cache `TAC`, interface `ID`, `CanFail`) in a writable region. -/
def mem1 : Janus.Arm64.Memory :=
  ⟨fun a => BitVec.ofNat 8 ((([(wsp + 2, 0x20), (desc + 1, 0x04), (desc + 2, 0x01),
      (desc + 9, 0x01), (desc + 10, 0x01), (desc + 16, 1)] ++ wtable).lookup a).getD 0),
    wmem.regions ++ [⟨desc - desc % 4096, 0x1000, true⟩]⟩

theorem mem1_env (g : W64) : Env0 mem1 g := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  unfold Desc; decide +kernel

theorem mem1_desc : TADescOK R0 mem1 desc := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by simp only [R0_isInter, taInter]; decide +kernel, ?_⟩
  show TACacheOK R0 mem1 (mem1.readLE desc 8) (taInter mem1 desc)
  rw [show mem1.readLE desc 8 = TAC by decide +kernel]
  exact TACacheOK.empty (by decide +kernel) (by decide +kernel) (inPriv (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

/-- `TD` and the value slot `VAL`, as words. -/
def td : BitVec 64 := BitVec.ofNat 64 TD
def val : BitVec 64 := BitVec.ofNat 64 VAL

/-- The witness call state: `AsHasher(x)` for the box `x = (TD, VAL)`. -/
def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then td else if i = 3 then val
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem1 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [td, val] s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide +kernel, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem pre : CallerOK R0 s0 40 24 ∧ TADescOK R0 s0.mem desc ∧ taCanFail s0.mem desc = true ∧
    Outside desc 24 [((s0.regs 4).toNat - (R0.depth + 40), (s0.regs 4).toNat + 24)] ∧
    (td.toNat ≠ 0 → R0.IsType td.toNat) := by
  refine ⟨⟨mem1_env (s0.regs 14), ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩, mem1_desc, ?_, ?_, fun _ => Or.inl rfl⟩
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide +kernel
  · unfold Janus.Spec.Disjoint; decide +kernel
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide +kernel
  · decide +kernel
  · simp only [outside_cons, outside_nil, and_true]; decide +kernel

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : IfaceModel) (ret : Nat)
    (s : Janus.Amd64.State) (t x : BitVec 64),
    R.Laws ∧ TypeAssert (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typeAssert") R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [t, x] s ∧
    (CallerOK R s 40 24 ∧ TADescOK R s.mem desc ∧ taCanFail s.mem desc = true ∧
      Outside desc 24 [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 24)] ∧
      (t.toNat ≠ 0 → R.IsType t.toNat)) :=
  ⟨implAt, R0, ret, s0, td, val, R0_laws, model, hret, setup, pre⟩

/-- So the guarantee is reached: the assertion succeeds with the model's itab `TAB`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = TAB ∧ s'.regs 3 = val ∧ (s'.regs 1).toNat % 256 = 1 := by
  refine (correctness implAt R0 R0_laws model td val ret hret s0 setup pre).mono ?_
  intro s' h
  obtain ⟨habi, ⟨h0, h1, h2, -⟩, -⟩ := h
  have hi : taInter s0.mem desc = ID := by decide +kernel
  rw [hi] at h0
  have h0' : (s'.regs 0).toNat = TAB := by rw [h0]; decide +kernel
  refine ⟨habi, h0', h1, ?_⟩
  rw [h2, h0']; decide +kernel

end Witness

end Proof
