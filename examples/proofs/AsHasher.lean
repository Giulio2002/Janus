import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Iface

namespace Proof

/-- The address of the type-assertion descriptor `example.com/basic..typeAssert.0` (in `.data`):
the `ADRP`+`ADD` at `AsHasher+0x24`, recomputed from the extracted words. -/
def desc : Nat :=
  adrpLdTarget (Extracted.entry + 0x24) (segWord Extracted.program "example.com/basic.AsHasher" 9)
    (segWord Extracted.program "example.com/basic.AsHasher" 10) 0

/-- The loop head of the cache probe (`AND R6, R5, R7`). -/
abbrev head : Nat := Extracted.entry + 0x50

/-- The guarantee: the itab of `x.(Hasher)` for the dynamic type `t` (`0` for nil or a type that
does not implement it) in `X0`, the data word in `X1`, `ok` (`X0 ≠ 0`) in `X2`; the descriptor
still well formed; memory changed only in the runtime's memory, the stack window and the
descriptor's `Cache` word; the runtime still usable. -/
def Post (R : IfaceModel) (t x : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat = (if t.toNat = 0 then 0 else (R.itab (taInter s.mem desc) t.toNat).getD 0) ∧
    s'.regs 1 = x ∧ (s'.regs 2).toNat = (if (s'.regs 0).toNat = 0 then 0 else 1) ∧
    TADescOK R s'.mem desc ∧ taInter s'.mem desc = taInter s.mem desc ∧
    MemFrame s.mem s'.mem
      (R.priv ++ [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24), (desc, desc + 8)]) ∧
    R.Env s'.mem (s.regs 28)

/-- The memory at the loop head: the caller's memory with the frame record and the two spills. -/
def M0 (s : State) (ret : Nat) (t x : BitVec 64) : Memory :=
  (((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE
    (s.sp.toNat + 8) 8 t.toNat).writeLE (s.sp.toNat + 16) 8 x.toNat

/-- A cache miss: the call of `runtime.typeAssert` and the return. -/
set_option maxRecDepth 20000 in
theorem miss (impl : List Segment) (R : IfaceModel) (hl : R.Laws)
    (hta : TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R)
    (t x : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hc : CallerOK R s 48 24) (hdesc : TADescOK R s.mem desc) (hcf : taCanFail s.mem desc = true)
    (hdo : desc + 24 ≤ s.sp.toNat - (R.depth + 48) ∨ s.sp.toNat + 24 ≤ desc)
    (ht0 : t.toNat ≠ 0) (hty : R.IsType t.toNat) :
    ∀ (S : State), S.pc = BitVec.ofNat 64 (Extracted.entry + 0x74) → S.regs 0 = t → S.regs 1 = x →
      S.regs 3 = BitVec.ofNat 64 desc → S.regs 30 = BitVec.ofNat 64 ret →
      S.sp = s.sp - 48#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 56#64 →
      S.regs 18 = s.regs 18 → S.mem = M0 s ret t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R t x s s') := by
  intro S hpc h0 h1 h3 h30 hsp h28 h29 h18 hm
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, hdw, hdi, -⟩ := hdesc'
  simp only [M0] at hm
  have hspa : S.sp.toNat % 16 = 0 := by rw [hsp]; janus_simp; omega
  have hd64 : desc % 2 ^ 64 = desc := Nat.mod_eq_of_lt (by omega)
  janus_run until [Extracted.program.contractAddr "runtime.typeAssert"]
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo' : Outside desc 24 [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  refine Reaches.call (Summary.withExit hta hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) (by simp [setReg, h28]) (by simp [setReg])
      (by simp [setReg]) (by decide) (by decide), ?_, ?_, ?_⟩ ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64]
    exact TADescOK.frame hdesc (by janus_frame) hdo' hws
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h0]; intro h; exact absurd h ht0
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hd64, h0]
    intro _; refine ⟨hty, Or.inl ?_⟩
    exact (taCanFail_frame (m := s.mem) (by janus_frame) hdo').trans hcf
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hres, hdesc2, hinter2, hcf2⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setReg_apply, reduceIte, Nat.reduceEqDiff,
      BitVec.toNat_ofNat, hd64, h0] at hfr hres hdesc2 hinter2 hcf2
    janus_run
    obtain ⟨MM, hMM⟩ : ∃ MM, MM = (M0 s ret t x).writeLE (s.sp.toNat + 16) 8 x.toNat := ⟨_, rfl⟩
    simp only [M0] at hMM
    rw [← hMM] at hres hinter2 hcf2 hfr
    have hMf : MemFrame s.mem MM [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] := by
      rw [hMM]; janus_frame
    rw [taInter_frame hMf hdo'] at hres hinter2
    refine ⟨?_, by simp [setReg], ?_, hdesc2, hinter2, ?_, by simpa [setReg, h28] using henv'⟩
    · simpa [setReg, Map.keepABI] using hres.1
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, Map.keepABI_apply]
      split <;> simp_all
    · refine hMf.trans hfr fun a n h => ?_
      have hsp48 : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by rw [BitVec.toNat_sub]; simp; omega
      simp only [outside_append, outside_cons, outside_nil, and_true, hsp48] at h ⊢
      exact ⟨h.2.1, ⟨h.1, by omega, by omega⟩, h.2.2⟩

/-- The entry address the probe computes in `X7` (`((h & Mask) << 4) + 8` added to the cache). -/
theorem x7_toNat (c k : Nat) (h : BitVec 64) (hk : k ≤ 64) (hc : c + 8 + 16 * 2 ^ k ≤ 2 ^ 48) :
    (BitVec.ofNat 64 c + (((h &&& BitVec.ofNat 64 (2 ^ k - 1)).rotateRight 60 &&&
      18446744073709551600#64 &&& 18446744073709551615#64) + 8#64)).toNat =
      c + (16 * (h.toNat % 2 ^ k) + 8) := by
  have hm := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
  have h1 : ((h &&& BitVec.ofNat 64 (2 ^ k - 1)).rotateRight 60 &&& 18446744073709551600#64 &&&
      18446744073709551615#64).toNat = 16 * (h.toNat % 2 ^ k) := by
    rw [BitVec.toNat_and, BitVec.toNat_and, show (18446744073709551615#64).toNat = 2 ^ 64 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (18446744073709551600#64).toNat = 18446744073709551600 from rfl,
      lsl4_toNat, and_mask_toNat h k hk]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, BitVec.toNat_add, h1, BitVec.toNat_ofNat, show (8#64).toNat = 8 from rfl,
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 16 * (h.toNat % 2 ^ k) + 8 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]

set_option maxRecDepth 20000 in
theorem loop (impl : List Segment) (R : IfaceModel) (hl : R.Laws)
    (hta : TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R)
    (t x : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret) (s : State)
    (hc : CallerOK R s 48 24) (hdesc : TADescOK R s.mem desc) (hcf : taCanFail s.mem desc = true)
    (hdo : desc + 24 ≤ s.sp.toNat - (R.depth + 48) ∨ s.sp.toNat + 24 ≤ desc)
    (ht0 : t.toNat ≠ 0) (hty : R.IsType t.toNat) (k : Nat)
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
      S.pc = BitVec.ofNat 64 head → S.regs 0 = t → S.regs 1 = x →
      S.regs 3 = BitVec.ofNat 64 desc → S.regs 4 = BitVec.ofNat 64 (s.mem.readLE desc 8) →
      S.regs 5 = h → S.regs 6 = BitVec.ofNat 64 (2 ^ k - 1) → S.regs 30 = BitVec.ofNat 64 ret →
      S.sp = s.sp - 48#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 56#64 →
      S.regs 18 = s.regs 18 → S.mem = M0 s ret t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R t x s s') := by
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
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
      Outside a n [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo' : Outside desc 24 [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hMf : MemFrame s.mem (M0 s ret t x) [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] := by
    simp only [M0]; janus_frame
  have htyp : ∀ i, i < 2 ^ k →
      s.mem.readLE (s.mem.readLE desc 8 + (16 * i + 8)) 8 = taTyp s.mem (s.mem.readLE desc 8) i :=
    fun i _ => by
      simp only [taTyp]
      rw [show s.mem.readLE desc 8 + 8 + 16 * i = s.mem.readLE desc 8 + (16 * i + 8) by omega]
  have htlt : ∀ i, taTyp s.mem (s.mem.readLE desc 8) i % 18446744073709551616 =
      taTyp s.mem (s.mem.readLE desc 8) i := fun i => Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)
  -- the hit: the cached itab is the runtime's answer
  have hit : ∀ (S : State) (h : BitVec 64), h.toNat % 2 ^ k < 2 ^ k →
      t.toNat = taTyp s.mem (s.mem.readLE desc 8) (h.toNat % 2 ^ k) →
      S.pc = BitVec.ofNat 64 (Extracted.entry + 0x8c) → S.regs 0 = t → S.regs 1 = x →
      (S.regs 7).toNat = s.mem.readLE desc 8 + (16 * (h.toNat % 2 ^ k) + 8) →
      S.regs 30 = BitVec.ofNat 64 ret →
      S.sp = s.sp - 48#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 56#64 →
      S.regs 18 = s.regs 18 → S.mem = M0 s ret t x →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R t x s s') := by
    intro S h hmod heq hpc h0 h1 h7 h30 hsp h28 h29 h18 hm
    have hspa : S.sp.toNat % 16 = 0 := by rw [hsp]; janus_simp; omega
    simp only [M0] at hm
    janus_run [h7]
    have htyp_eq : taTyp s.mem (s.mem.readLE desc 8) (h.toNat % 2 ^ k) = t.toNat := heq.symm
    have hitab : s.mem.readLE (s.mem.readLE desc 8 + (16 * (h.toNat % 2 ^ k) + 8) + 8) 8 =
        (R.itab (taInter s.mem desc) t.toNat).getD 0 := by
      have := hent _ hmod (by rw [htyp_eq]; exact ht0)
      rw [htyp_eq] at this
      rw [← this]; simp only [taItab]
      rw [show s.mem.readLE desc 8 + 16 + 16 * (h.toNat % 2 ^ k) =
        s.mem.readLE desc 8 + (16 * (h.toNat % 2 ^ k) + 8) + 8 by omega]
    have hlt := Memory.readLE_lt s.mem (s.mem.readLE desc 8 + (16 * (h.toNat % 2 ^ k) + 8) + 8) 8
    rw [hitab] at hlt
    refine ⟨?_, by simp [setReg, h1], ?_, TADescOK.frame hdesc hMf hdo' hws,
      taInter_frame hMf hdo', ?_, hl.env_frame _ _ _ henv (agrees_of_memFrame_outside hMf hws)⟩
    · simp [setReg, hitab, ht0, Nat.mod_eq_of_lt hlt]
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hitab, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlt]
      split <;> simp
    · exact hMf.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.2.1
  intro n
  induction n with
  | zero =>
    intro S h hn hb' hpc h0 h1 h3 h4 h5 h6 h30 hsp h28 h29 h18 hm
    simp only [M0] at hm
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    have hjr := probe_zero hj hmod hn
    janus_run [hand] until [head, Extracted.entry + 0x74, Extracted.entry + 0x8c]
    · refine hit _ h hmod (by simpa [htlt] using hbr) (by rfl) (by simp [setReg, h0])
        (by simp [setReg, h1]) (by simp only [setReg_apply]; exact x7_toNat _ _ _ hk64 hcb)
        (by simp [setReg, h30]) rfl (by simp [setReg, h28]) (by simp [setReg, h29])
        (by simp [setReg, h18]) rfl
    · exact miss impl R hl hta t x ret hret s hc hdesc hcf hdo ht0 hty _ (by rfl)
        (by simp [setReg, h0]) (by simp [setReg, h1]) (by simp [setReg, h3]) (by simp [setReg, h30])
        rfl (by simp [setReg, h28]) (by simp [setReg, h29]) (by simp [setReg, h18]) rfl
    · exfalso
      rw [htlt, hjr, hj0] at hbr
      exact hbr rfl
  | succ n ih =>
    intro S h hn hb' hpc h0 h1 h3 h4 h5 h6 h30 hsp h28 h29 h18 hm
    simp only [M0] at hm
    have hmod := Nat.mod_lt h.toNat (Nat.two_pow_pos k)
    janus_run [hand] until [head, Extracted.entry + 0x74, Extracted.entry + 0x8c]
    · refine hit _ h hmod (by simpa [htlt] using hbr) (by rfl) (by simp [setReg, h0])
        (by simp [setReg, h1]) (by simp only [setReg_apply]; exact x7_toNat _ _ _ hk64 hcb)
        (by simp [setReg, h30]) rfl (by simp [setReg, h28]) (by simp [setReg, h29])
        (by simp [setReg, h18]) rfl
    · exact miss impl R hl hta t x ret hret s hc hdesc hcf hdo ht0 hty _ (by rfl)
        (by simp [setReg, h0]) (by simp [setReg, h1]) (by simp [setReg, h3]) (by simp [setReg, h30])
        rfl (by simp [setReg, h28]) (by simp [setReg, h29]) (by simp [setReg, h18]) rfl
    · have hne : h.toNat % 2 ^ k ≠ j := fun he => by rw [htlt, he, hj0] at hbr; exact hbr rfl
      have h1' : (h + 1#64).toNat = h.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
      refine ih _ (h + 1#64) ?_ ?_ (by rfl) (by simp [setReg, h0]) (by simp [setReg, h1])
        (by simp [setReg, h3]) (by simp [setReg, h4]) (by simp [setReg]) (by simp [setReg, h6])
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
/-- Its address. -/
def mulHasherItab : Nat := dataAddr Extracted.program.data mulItab

/-- For a `*MulHasher` the assertion succeeds with the static itab (`StaticItabs`). -/
theorem static_case (R : IfaceModel) (t x : BitVec 64) (s s' : State) (hp : Post R t x s s')
    (hst : StaticItabs R Extracted.program.data) (hi : taInter s.mem desc = hasherInter)
    (htt : t.toNat = mulHasherType) : (s'.regs 0).toNat = mulHasherItab ∧ (s'.regs 2).toNat = 1 := by
  obtain ⟨d, hd⟩ : ∃ d, dataNamed Extracted.program.data mulItab = some d := ⟨_, rfl⟩
  have hsome := hst.named hd (by decide +kernel) (by rw [show d = _ from (Option.some.inj hd).symm]; decide)
  janus_eval_nat hT : mulHasherType
  janus_eval_nat hI : mulHasherItab
  have hT0 : t.toNat ≠ 0 := by rw [htt, hT]; decide
  obtain ⟨h0, -, h2, -⟩ := hp
  rw [hi, if_neg hT0, htt] at h0
  simp only [hasherInter, mulHasherType] at hsome h0
  rw [hsome] at h0
  simp only [Option.getD_some] at h0
  refine ⟨h0, ?_⟩
  rw [h2, h0]
  simp only [mulHasherItab] at hI
  rw [hI]; decide

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (R : IfaceModel) (hl : R.Laws)
    (hta : TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R)
    (t x : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [t, x]
      (fun s => CallerOK R s 48 24 ∧ TADescOK R s.mem desc ∧ taCanFail s.mem desc = true ∧
        Outside desc 24 [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] ∧
        (t.toNat ≠ 0 → R.IsType t.toNat))
      (fun s s' => Post R t x s s' ∧
        (StaticItabs R Extracted.program.data → taInter s.mem desc = hasherInter →
          t.toNat = mulHasherType → (s'.regs 0).toNat = mulHasherItab ∧ (s'.regs 2).toNat = 1)) := by
  intro ret hret s hs ⟨hc, hdesc, hcf, hdo, hty⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  simp only [outside_cons, outside_nil, and_true] at hdo
  have hdesc' := hdesc
  obtain ⟨hdb, hdacc, hdw, hdi, k, hk, hcb, hcacc, hcin, hent, j, hj, hj0⟩ := hdesc'
  simp only [taCache] at hk hcb hcacc hcin hent hj0
  have hdc := InRanges.disjoint hcin hout
  -- the corollary for the static itab, from the general result
  suffices hmain : Reaches ((Extracted.program.link impl).withExit ret) s
      (IsReturn fun s' => ABIReturn s s' ∧ Post R t x s s') by
    exact (returns_of_reaches hmain).mono fun s' h =>
      ⟨h.1, h.2, fun hst hi htt => static_case R t x s s' h.2 hst hi htt⟩
  have hws : ∀ a n, InRanges a n R.priv →
      Outside a n [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] := by
    intro a n ha
    have := InRanges.disjoint ha (Outside.of_sub hout (Nat.le_refl _) (Nat.le_refl _))
    simp only [outside_cons, outside_nil, and_true]; omega
  have hdo' : Outside desc 24 [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  by_cases ht0 : t.toNat = 0
  · janus_eval_nat hD : desc
    have hdacc' := hdacc; have hdw' := hdw; have hdo'' := hdo; have hdb' := hdb
    rw [hD] at hdacc' hdw' hdo'' hdb'
    janus_run
    have hMf : MemFrame s.mem ((((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8
        (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 0).writeLE (s.sp.toNat + 16) 8 x.toNat)
        [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 24)] := by janus_frame
    refine ⟨by simp [setReg, h_x0, ht0], by simp [setReg, h_x1], ?_, TADescOK.frame hdesc hMf hdo' hws,
      taInter_frame hMf hdo', hMf.mono fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.2.1,
      hl.env_frame _ _ _ henv (agrees_of_memFrame_outside hMf hws)⟩
    simp [setReg, h_x0, ht0]
  · obtain ⟨-, htb, htacc, htin⟩ := hl.type_desc _ _ _ henv (hty ht0)
    simp only [typeDescSize] at htb htacc htin
    have hdt := InRanges.disjoint htin hout
    janus_eval_nat hD : desc
    have hcacc' := hcacc; have hdacc' := hdacc; have hdw' := hdw; have hdo'' := hdo
    have hdc' := hdc; have hdb' := hdb
    rw [hD] at hcacc' hdacc' hdw' hdo'' hdc' hdb'
    janus_run until [head]
    have hhash := Memory.readLE_lt s.mem (t.toNat + 16) 4
    have hN : 0 < 2 ^ k := Nat.two_pow_pos k
    have hkb : 2 ^ k < 2 ^ 44 := by omega
    refine loop impl R hl hta t x ret hret s hc hdesc hcf hdo ht0 (hty ht0) k hk hcb hcacc hcin
      hent j hj hj0 _ _ (BitVec.ofNat 64 (s.mem.readLE (t.toNat + 16) 4)) rfl ?_ (by rfl)
      (by simp [setReg, h_x0]) (by simp [setReg, h_x1]) (by simp [setReg, hD]) (by simp [setReg, hD])
      (by simp [setReg]) (by simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; rw [← hD, hk]) (by simp [setReg, h_lr]) rfl (by simp [setReg])
      (by simp [setReg]) (by simp [setReg]) (by simp [M0])
    have := probe_lt (j := j) (r := (BitVec.ofNat 64 (s.mem.readLE (t.toNat + 16) 4)).toNat) hN
    simp only [BitVec.toNat_ofNat] at this ⊢
    rw [Nat.mod_eq_of_lt (show s.mem.readLE (t.toNat + 16) 4 < 2 ^ 64 by simp at hhash; omega)] at this ⊢
    simp at hhash
    omega

end Proof
