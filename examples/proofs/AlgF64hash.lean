import Extracted

/-!
# `runtime.f64hash` meets the `Fhash … binary64 8` contract

**Guarantee.** For every hash model `H` satisfying its laws, all stack bounds with `8 ≤ dr`, `dr + 48 ≤ d`,
`8 ≤ dm`, `dm + 48 ≤ d`, and every code at `runtime.rand` and `runtime.memhash` meeting `Rand`
(bound `dr`) and `Memhash` (bound `dm`), the machine code of Go 1.26's `runtime.f64hash(p, h)`
satisfies `Janus.Contracts.Hash.Fhash … H d binary64 8`: the result is `FHashIs` of the float `x` at
`p` (`c1 · (c0 ^ h)` for `±0`, `c1 · (c0 ^ h ^ rnd)` for a NaN with the random word `rnd` returned
by `rand`, `H.mem h 8 x` otherwise), with the frame of the hash contracts.

**What the code does.** A 48-byte frame; `FMOV` loads the float, `FCMP x, #0.0` (`Z` exactly for the zeros:
`feq_zero_r`, from `HashLaws.feq_zero_iff`) selects the zero case; `FCMP x, x` (`Z` exactly for
the non-NaNs: `feq_self`) selects `memhash(p, h, 8)`; otherwise `h` is spilled to its slot
`64(RSP)` (`SP + 16`, the caller's spill slot), `rand()` is called, `h` is reloaded, and the
result is `(rnd ^ h ^ c0) · c1`.

**Assumptions.** `H.Laws`, `FPCR = 0` (from the contract), and the callees' `Rand` and `Memhash` contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem Janus.Contracts.Hash Janus.Float Janus.Contracts.HashLaws

namespace Proof

/-! ## Calls from a frame (arm64)

The function pushes its frame record (`X30` at `SP - F`, `X29` at `SP - F - 8`) and calls a
callee with `SP - F`. These lemmas move the contract's precondition at the entry `s` to the call
site `S` (`EqPre`/`HPre` for the callee's bound `d'` with `d' + F ≤ d`), and the callee's frame
back to the caller's. -/

/-- A range inside `rs` and a range outside `rs` are apart. -/
theorem inRanges_apart {a k b j : Nat} {rs : List (Nat × Nat)} (hi : InRanges a k rs)
    (ho : Outside b j rs) : b + j ≤ a ∨ a + k ≤ b := by
  obtain ⟨r, hr, h1, h2⟩ := hi; have := MemFrame.outside_mem ho hr; omega

/-- The callee's window lies inside the caller's. -/
theorem sub_win {s S : State} {d n d' n' F : Nat} (hd : d' + F ≤ d) (hd1 : d ≤ s.sp.toNat)
    (hsp : S.sp.toNat = s.sp.toNat - F) (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) {a k : Nat}
    (h : Outside a k (calleeStack s d n)) : Outside a k (calleeStack S d' n') := by
  simp only [calleeStack, outside_cons, outside_nil, and_true, hsp] at h ⊢
  omega

theorem eqPre_call {s S : State} {d n d' n' F : Nat} (hp : EqPre d n s) (hF : F % 16 = 0)
    (hd : d' + F ≤ d) (hd8 : 8 ≤ d') (hsp : S.sp.toNat = s.sp.toNat - F) (hg : S.regs 28 = s.regs 28)
    (hm : MemFrame s.mem S.mem (calleeStack s d n)) (hlr : (S.regs 30).toNat % 4 = 0)
    (hlr' : (S.regs 30).toNat < 2 ^ 48) (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) : EqPre d' n' S := by
  obtain ⟨⟨g1, g2, g3⟩, ⟨l1, l2, al, dsp, d8, top, acc⟩, go⟩ := hp
  simp only [regG, stackguard0Offset, stackguard0] at g1 g2 g3
  refine ⟨⟨?_, ?_, ?_⟩, ⟨hlr, hlr', ?_, ?_, hd8, ?_, ?_⟩, sub_win hd dsp hsp hn (by rw [hg]; exact go)⟩
  · simp only [regG, stackguard0Offset, hg]; omega
  · simp only [regG, stackguard0Offset, hg, hm.accessible]; exact g2
  · simp only [stackguard0, regG, stackguard0Offset, hg, hsp]
    rw [hm.readLE _ _ go]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hm.accessible]; exact Memory.accessible_mono _ acc (by omega) (by omega)

theorem hPre_call {H : HashModel} (hl : H.Laws) {s S : State} {d n d' n' F : Nat} (hp : HPre H d n s)
    (hF : F % 16 = 0) (hd : d' + F ≤ d) (hd8 : 8 ≤ d') (hsp : S.sp.toNat = s.sp.toNat - F)
    (hg : S.regs 28 = s.regs 28) (hm : MemFrame s.mem S.mem (calleeStack s d n))
    (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48)
    (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) : HPre H d' n' S := by
  obtain ⟨he, hgd, hc, hout, go, gp⟩ := hp
  have hc' := hc
  obtain ⟨-, -, -, dsp, -, top, -⟩ := hc'
  obtain ⟨h1, h2, h3⟩ := eqPre_call ⟨hgd, hc, go⟩ hF hd hd8 hsp hg hm hlr hlr' hn
  refine ⟨?_, h1, h2, hout.of_sub (by rw [hsp]; omega) (by rw [hsp]; omega), h3, by rw [hg]; exact gp⟩
  rw [hg]
  refine hl.env_frame _ _ _ he (Agrees.of_memFrame hm fun a ha => ?_)
  have := inRanges_apart ha hout
  simp only [calleeStack, outside_cons, outside_nil, and_true]; omega

/-- The callee's frame (with the private ranges `P`) after the caller's frame pushes is the
caller's frame. -/
theorem frame_ret {s S : State} {m : Memory} {P : List (Nat × Nat)} {d n d' n' F : Nat}
    (hd : d' + F ≤ d) (hd1 : d ≤ s.sp.toNat) (hsp : S.sp.toNat = s.sp.toNat - F)
    (hn : (F = 0 ∧ n' ≤ n) ∨ 16 + 8 * n' ≤ F) (hm : MemFrame s.mem S.mem (calleeStack s d n))
    (h2 : MemFrame S.mem m (P ++ calleeStack S d' n')) : MemFrame s.mem m (P ++ calleeStack s d n) :=
  hm.trans h2 fun a k h => by
    simp only [outside_append] at h ⊢
    exact ⟨h.2, h.1, sub_win hd hd1 hsp hn h.2⟩

/-- An `EqRet`-shaped return whose memory keeps `H.Env` is an `HRet` return. -/
theorem hRet_intro {H : HashModel} {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18)
    (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid)
    (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hf : MemFrame s.mem s'.mem (H.priv ++ calleeStack s d nargs)) (he : H.Env s'.mem (s.regs 28))
    (hp : P s'.regs)
    (hex : s'.excl = s.excl := by first | rfl | simp_all)
    (hep : s'.exclPass = s.exclPass := by first | rfl | simp_all) : HRet H d nargs s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.fpsr, s'.mem, ?_, hf, he, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs, ex, ep⟩ := s'
  simp only at hsp hpc hdz htp hfc h18 h28 h29 hex hep ⊢
  subst hsp hpc hdz htp hfc hex hep
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-- `H.Env` survives stores into the caller's part of the window (outside `H.priv`). -/
theorem env_of_frame {H : HashModel} (hl : H.Laws) {s : State} {m : Memory} {g : W64} {d n : Nat}
    (he : H.Env s.mem g) (hout : Outside (s.sp.toNat - d) (d + 8 + 8 * n) H.priv)
    (hd1 : d ≤ s.sp.toNat) (hm : MemFrame s.mem m (calleeStack s d n)) : H.Env m g :=
  hl.env_frame _ _ _ he (Agrees.of_memFrame hm fun a ha => by
    have := inRanges_apart ha hout
    simp only [calleeStack, outside_cons, outside_nil, and_true]; omega)

/-- `FCMP x, #0.0` sets `Z` exactly for the zeros. -/
theorem feq_zero_r (f : Fmt) {x : Nat} (hx : x < 2 ^ f.width) (h0 : zero f false < 2 ^ f.width) :
    feq f x (zero f false) = true ↔ classify f x = .zero := by
  rw [feq_comm]; exact feq_zero_iff f h0 hx (classify_zero f false)

/-- `FCMP x, x` sets `Z` exactly for the non-NaNs. -/
theorem feq_self (f : Fmt) (x : Nat) : feq f x x = !isNaN f x := by
  cases h : isNaN f x
  · simp [feq_refl f h]
  · simp [feq_nan_left f x h]

theorem xor_c0 (h : W64) : (h ^^^ 33054211828000289#64).toNat = c0 ^^^ h.toNat := by
  rw [BitVec.toNat_xor, Nat.xor_comm]; rfl

theorem xor3_c0 (h r : W64) : (h ^^^ r ^^^ 33054211828000289#64).toNat = c0 ^^^ h.toNat ^^^ r.toNat := by
  simp only [BitVec.toNat_xor]
  rw [show (33054211828000289#64).toNat = c0 from rfl, Nat.xor_comm, ← Nat.xor_assoc]

theorem mul_c1 (x : W64) : (x * 23344194077549503#64).toNat = c1 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_mul, Nat.mul_comm]; rfl

theorem correctness (impl : List Segment) (H : HashModel) (hl : H.Laws) (d dr dm : Nat)
    (hdr : 8 ≤ dr) (hdr' : dr + 48 ≤ d) (hdm : 8 ≤ dm) (hdm' : dm + 48 ≤ d)
    (hr : Rand (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.rand") H dr)
    (hm : Memhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memhash") H dm) :
    Fhash (Extracted.program.link impl) Extracted.entry H d binary64 8 := by
  intro s hpc ⟨hpre, hf, ⟨hi1, hi2, hi3⟩⟩
  have hpre' := hpre
  obtain ⟨he, hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hout, hgo, hgp⟩ := hpre'
  have hg' := hg
  obtain ⟨hg1, hg2, hg3⟩ := hg'
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have ho1 : Outside (s.sp.toNat - 48) 8 H.priv := hout.of_sub (by omega) (by omega)
  have ho2 : Outside (s.sp.toNat - 56) 8 H.priv := hout.of_sub (by omega) (by omega)
  have ho3 : Outside (s.sp.toNat + 16) 8 H.priv := hout.of_sub (by omega) (by omega)
  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hi3' := hi3
  simp only [calleeStack, outside_cons, outside_nil, and_true] at hi3'
  have hx4 : s.mem.readLE (s.regs 0).toNat 8 < 18446744073709551616 := by
    simpa using s.mem.readLE_lt (s.regs 0).toNat 8
  have hm4 : s.mem.readLE (s.regs 0).toNat 8 % 340282366920938463463374607431768211456 =
      s.mem.readLE (s.regs 0).toNat 8 := by
    rw [Nat.mod_eq_of_lt (show s.mem.readLE (s.regs 0).toNat 8 < 340282366920938463463374607431768211456 by omega)]
  have hmf : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE
      (s.sp.toNat - 56) 8 (s.regs 29).toNat) (calleeStack s d 2) :=
    (MemFrame.of_writeLE _ _ (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_self ..) (by simp; omega) (by simp; omega)
  have hmf3 : MemFrame s.mem (((s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE
      (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE (s.sp.toNat + 16) 8 (s.regs 1).toNat) (calleeStack s d 2) :=
    hmf.writeLE _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by simp) (by simp)
  have hz : feq binary64 (s.mem.readLE (s.regs 0).toNat 8) (zero binary64 false) = true ↔
      classify binary64 (s.mem.readLE (s.regs 0).toNat 8) = .zero :=
    feq_zero_r _ (show _ < 2 ^ 64 from hx4) (by decide)
  janus_run [hf, hm4, feq_self] until [Extracted.program.contractAddr "runtime.memhash", Extracted.program.contractAddr "runtime.rand"]
  · -- ±0: `c1 · (c0 ^ h)`
    have hc : classify binary64 (s.mem.readLE (s.regs 0).toNat 8) = .zero := hz.1 (by assumption)
    refine hRet_intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl hf.symm
      (hmf.mono fun a k h => by simp only [outside_append] at h; exact h.2)
      (env_of_frame hl he hout hd1 hmf) ?_
    simp only [FHashIs, hc, ite_true, setReg_apply, Nat.reduceEqDiff, reduceIte, mul_c1, xor_c0]
  · -- not a NaN: `memhash(p, h, 8)`
    have hn : isNaN binary64 (s.mem.readLE (s.regs 0).toNat 8) = false := hbr
    have hb : ¬ feq binary64 (s.mem.readLE (s.regs 0).toNat 8) (zero binary64 false) = true := by
      assumption
    have hc : ¬ classify binary64 (s.mem.readLE (s.regs 0).toNat 8) = .zero := fun h => hb (hz.2 h)
    refine ReachesRet.call hm rfl ⟨hPre_call (F := 48) hl hpre (by decide) hdm' hdm hsp
      (by simp [setReg]) hmf (by simp [setReg]) (by simp [setReg]) (.inr (by decide)), ?_⟩ ?_
    · exact ⟨by simpa [setReg] using hi1, by simpa [setReg, hmf.accessible] using hi2,
        sub_win hdm' hd1 hsp (.inr (by decide)) hi3⟩
    intro s' hpc' ⟨r, v, fl, fs, m, hs', hfr, henv, hres⟩
    subst hs'
    have hfr0 := hfr
    simp only [calleeStack, hsp] at hfr
    janus_run
    refine hRet_intro rfl rfl (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI])
      (by simp [setReg]) rfl rfl hf.symm (frame_ret hdm' hd1 hsp (.inr (by decide)) hmf hfr0)
      (by simpa [setReg] using henv) ?_
    have h4 : (8#64).toNat = 8 := rfl
    simp only [setReg_apply, Map.keepABI, Nat.reduceEqDiff, reduceIte, h4] at hres ⊢
    rw [hmf.readLE _ _ hi3] at hres
    simp only [FHashIs, hc, hn, ite_false, Bool.false_eq_true]
    simpa using hres
  · -- a NaN: `c1 · (c0 ^ h ^ rand())`
    have hn : ¬ isNaN binary64 (s.mem.readLE (s.regs 0).toNat 8) = false := hbr
    have hb : ¬ feq binary64 (s.mem.readLE (s.regs 0).toNat 8) (zero binary64 false) = true := by
      assumption
    have hc : ¬ classify binary64 (s.mem.readLE (s.regs 0).toNat 8) = .zero := fun h => hb (hz.2 h)
    refine ReachesRet.call hr rfl (hPre_call (F := 48) hl hpre (by decide) hdr' hdr hsp
      (by simp [setReg]) hmf3 (by simp [setReg]) (by simp [setReg]) (.inr (by decide))) ?_
    intro s' hpc' ⟨r, v, fl, fs, m, hs', hfr, henv, _⟩
    subst hs'
    have hfr0 := hfr
    simp only [calleeStack, hsp] at hfr
    janus_run
    refine hRet_intro rfl rfl (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI])
      (by simp [setReg]) rfl rfl hf.symm (frame_ret hdr' hd1 hsp (.inr (by decide)) hmf3 hfr0)
      (by simpa [setReg] using henv) ?_
    simp only [FHashIs, hc, ite_false, Bool.not_eq_false] at hn ⊢
    simp only [hn, ite_true]
    refine ⟨(r 0).toNat, (r 0).isLt, ?_⟩
    simp only [setReg_apply, Map.keepABI, Nat.reduceEqDiff, reduceIte, mul_c1, xor3_c0]


namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.HashSat

/-- `runtime.rand` (a `RET`: any word is a random word) and `runtime.memhash`
(`HashSat.seedCode`, model `H0`), both straight-line, placed directly at their addresses. -/
def rAddr : Nat := Extracted.program.contractAddr "runtime.rand"
def mAddr : Nat := Extracted.program.contractAddr "runtime.memhash"
def rSeg : Segment := { name := "rand", base := rAddr, words := randCode }
def mSeg : Segment := { name := "memhash", base := mAddr, words := seedCode }
def implAt : List Segment := [rSeg, mSeg]

theorem link_eq : Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } := rfl

theorem modelR (d : Nat) : Rand (Extracted.program.link implAt) rAddr H0 d := by
  rw [link_eq]
  intro s hpc ⟨he, _, ⟨hl1, hl2, _⟩, _⟩
  janus_eval_nat hC : rAddr
  rw [hC] at hpc
  janus_run
  exact hRet_of ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (MemFrame.refl _ _) he trivial

theorem modelM (d : Nat) : Memhash (Extracted.program.link implAt) mAddr H0 d := by
  rw [link_eq]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  janus_eval_nat hC : mAddr
  rw [hC] at hpc
  janus_run
  exact seed_hRet he (by simp [setReg, seed_mod])

/-- The witness call state: `MemSat.wstate` at the entry, with `f64hash(VAL, 7)` (`VAL` holds 42,
a non-zero, non-NaN encoding, so the hash is `memhash`'s), `FPCR = 0`. -/
def r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 VAL else if i = 1 then 7 else 0
def s0 : State := { MemSat.wstate r with pc := BitVec.ofNat 64 Extracted.entry }

theorem pre : HPre H0 64 2 s0 ∧ s0.fpcr = 0 ∧ Input s0 64 2 (s0.regs 0).toNat 8 := by
  refine ⟨⟨wmem_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩ <;>
    simp only [CallOK, Input, calleeStack, H0_priv, outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together (bounds `dr = dm = 16`, `d = 64`). -/
theorem nonvacuous : ∃ (impl : List Segment) (H : HashModel) (d dr dm : Nat), H.Laws ∧ 8 ≤ dr ∧
    dr + 48 ≤ d ∧ 8 ≤ dm ∧ dm + 48 ≤ d ∧
    Rand (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.rand") H dr ∧
    Memhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memhash") H dm ∧
    ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧
      (HPre H d 2 s ∧ s.fpcr = 0 ∧ Input s d 2 (s.regs 0).toNat 8) :=
  ⟨implAt, H0, 64, 16, 16, H0_laws, by decide, by decide, by decide, by decide, modelR 16, modelM 16,
    s0, rfl, pre⟩

/-- `correctness` at `s0`: the result is `FHashIs` of the float at `VAL`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (s0.regs 30) s0
    (fun s' => HRet H0 64 2 s0 s' fun r =>
      FHashIs H0 binary64 8 (s0.mem.readLE (s0.regs 0).toNat 8) (s0.regs 1).toNat (r 0).toNat) :=
  correctness implAt H0 H0_laws 64 16 16 (by decide) (by decide) (by decide) (by decide) (modelR 16)
    (modelM 16) s0 rfl pre

end Witness

end Proof
