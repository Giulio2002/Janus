import Extracted

/-!
# `runtime.nilinterhash` meets the `Nilinterhash` contract

**Guarantee.** For every hash model `H` satisfying its laws, stack bounds with `8 ≤ d'` and `d' + 64 ≤ d`,
and every code at `runtime.typehash`'s address meeting `Typehash` with bound `d'`, the machine code
of Go 1.26's `runtime.nilinterhash(p, h)` satisfies `Janus.Contracts.Hash.Nilinterhash … H d`: for the `any` value at `p`
the result is `h` for a nil type, else `c1 · r` for a `TypeHash` result `r` of the value (the data
word itself for a direct-interface type, else its target) with seed `h ^ c0`.

**What the code does.** The stack check, a 64-byte frame, the type word (for `interhash` read through the itab), the
`Equal` word (`CBZ` to the panic path), the `TFlagDirectIface` bit (`TBZ $5`), and
`typehash(t, data, h ^ c0)`, then `MUL` by `c1`. The panic path (`rtype.string`,
`concatstring2`, `convTstring`, `gopanic`) is unreachable: a hashable type has `Equal ≠ 0`
(`HashModel.Laws.type_desc`), so those callees need no hypothesis.

**Assumptions.** `H.Laws` and the callee's `Typehash` contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem Janus.Contracts.Hash Janus.Spec.Type

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
    (hp : P s'.regs) : HRet H d nargs s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.fpsr, s'.mem, ?_, hf, he, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc hdz htp hfc h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc
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

theorem xor_c0 (h : W64) : (h ^^^ 33054211828000289#64).toNat = c0 ^^^ h.toNat := by
  rw [BitVec.toNat_xor, Nat.xor_comm]; rfl

theorem xor3_c0 (h r : W64) : (h ^^^ r ^^^ 33054211828000289#64).toNat = c0 ^^^ h.toNat ^^^ r.toNat := by
  simp only [BitVec.toNat_xor]
  rw [show (33054211828000289#64).toNat = c0 from rfl, Nat.xor_comm, ← Nat.xor_assoc]

theorem mul_c1 (x : W64) : (x * 23344194077549503#64).toNat = c1 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_mul, Nat.mul_comm]; rfl

theorem toNat_ofNat_readLE8 (m : Memory) (a : Nat) :
    (BitVec.ofNat 64 (m.readLE a 8)).toNat = m.readLE a 8 := by
  have := m.readLE_lt a 8
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simpa using this)

theorem direct_bit (m : Memory) (t : Nat) :
    (BitVec.ofNat 64 (m.readLE (t + 20) 1)).getLsbD 5 = isDirectIface m t := by
  simp only [isDirectIface, tyTFlag, BitVec.getLsbD_ofNat]
  have := (m.readLE_lt (t + 20) 1)
  simp only [show (5 : Nat) < 64 from by decide, decide_true, Bool.true_and]

theorem xor_c0' (h : W64) : (h ^^^ 33054211828000289#64).toNat = h.toNat ^^^ c0 := by
  rw [BitVec.toNat_xor]; rfl

theorem c1_mul (x : W64) : (23344194077549503#64 * x).toNat = c1 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_mul]; rfl

set_option maxHeartbeats 2000000 in
theorem correctness (impl : List Segment) (H : HashModel) (hl : H.Laws) (d d' : Nat)
    (hd' : 8 ≤ d') (hd : d' + 64 ≤ d)
    (ht : Typehash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typehash") H d') :
    Nilinterhash (Extracted.program.link impl) Extracted.entry H d := by
  intro s hpc ⟨hpre, ⟨ha1, ha2, ha3⟩, hok⟩
  have hpre' := hpre
  obtain ⟨he, hg, ⟨hl1, hl2, hal, hd1, hd8, hd2, hst⟩, hout, hgo, hgp⟩ := hpre'
  have hg' := hg
  obtain ⟨hg1, hg2, hg3⟩ := hg'
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have ho1 : Outside (s.sp.toNat - 64) 8 H.priv := hout.of_sub (by omega) (by omega)
  have ho2 : Outside (s.sp.toNat - 72) 8 H.priv := hout.of_sub (by omega) (by omega)
  have hsp : (s.sp - 64#64).toNat = s.sp.toNat - 64 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hmf : MemFrame s.mem ((s.mem.writeLE (s.sp.toNat - 64) 8 (s.regs 30).toNat).writeLE
      (s.sp.toNat - 72) 8 (s.regs 29).toNat) (calleeStack s d 2) :=
    (MemFrame.of_writeLE _ _ (List.mem_cons_self ..) (by simp; omega) (by simp; omega)).writeLE _
      (List.mem_cons_self ..) (by simp; omega) (by simp; omega)
  have ha3' := ha3
  simp only [calleeStack, outside_cons, outside_nil, and_true] at ha3'
  by_cases ht0 : s.mem.readLE (s.regs 0).toNat 8 = 0
  · janus_run
    refine hRet_intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
      (hmf.mono fun a k h => by simp only [outside_append] at h; exact h.2)
      (env_of_frame hl he hout hd1 hmf) ?_
    simp [IHashIs, ht0, setReg]
  · obtain ⟨hh, hhf⟩ := hok ht0
    obtain ⟨-, htb, hta, htin, hteq⟩ := hl.type_desc _ _ _ _ he hh
    have hapart := inRanges_apart htin (hout.of_sub (b := s.sp.toNat - d) (k := d + 8 + 8 * 2)
      (a := s.sp.toNat - 72) (n := 16) (by omega) (by omega))
    simp only [tyEqual, typeDescSize] at hteq htb hta hapart
    have hA8 : (s.regs 0 + 8#64).toNat = (s.regs 0).toNat + 8 := by
      rw [BitVec.toNat_add]; simp; omega
    have hdt : dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat =
        if isDirectIface s.mem (s.mem.readLE (s.regs 0).toNat 8) then (s.regs 0).toNat + 8
        else s.mem.readLE ((s.regs 0).toNat + 8) 8 := rfl
    janus_run [direct_bit] until [Extracted.program.contractAddr "runtime.typehash"]
    all_goals
      have hdir := hbr
      refine ReachesRet.call ht rfl ⟨hPre_call (F := 64) hl hpre (by decide) hd hd' hsp
        (by simp [setReg]) hmf (by simp [setReg]) (by simp [setReg]) (.inr (by decide)), ?_⟩ ?_
      · simp only [setReg_apply, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8, hA8]
        have := (hhf _ hmf).1 hh
        rw [hdt] at this
        try simp only [direct_bit] at hdir
        split at this
        · rename_i hc; simp [hc] at hdir <;> (exact this)
        · rename_i hc; simp [hc] at hdir <;> (exact this)
      intro s' hpc' ⟨r, v, fl, fs, m, hs', hfr, henv, hres⟩
      subst hs'
      have hfr0 := hfr
      simp only [calleeStack, hsp] at hfr
      janus_run
      refine hRet_intro rfl rfl (by simp [setReg, Map.keepABI]) (by simp [setReg, Map.keepABI])
        (by simp [setReg]) rfl rfl rfl (frame_ret hd hd1 hsp (.inr (by decide)) hmf hfr0)
        (by simpa [setReg] using henv) ?_
      simp only [setReg_apply, Map.keepABI, Nat.reduceEqDiff, reduceIte, toNat_ofNat_readLE8, hA8]
        at hres ⊢
      simp only [IHashIs, ht0, ite_false]
      refine ⟨(r 0).toNat, ?_, by first | exact c1_mul _ | exact mul_c1 _⟩
      rw [xor_c0'] at hres
      rw [← ((hhf _ hmf).2.1 _ _), hdt]
      try simp only [direct_bit] at hdir
      split
      · rename_i hc; simp [hc] at hdir <;> (exact hres)
      · rename_i hc; simp [hc] at hdir <;> (exact hres)


namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.HashSat

/-- `runtime.typehash`'s address, with `HashSat.typehashCode` (the hash is the seed, model
`H0`) placed there directly (it is straight-line). The panic path's callees are unreachable and
get no code. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.typehash"
def seg : Segment := { name := "typehash", base := cAddr, words := typehashCode }
def implAt : List Segment := [seg]

theorem model (d : Nat) : Typehash (Extracted.program.link implAt) cAddr H0 d := by
  rw [show Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } from rfl]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  janus_eval_nat hC : cAddr
  rw [hC] at hpc
  janus_run
  exact hRet_of ⟨rfl, rfl, by simp [setReg], by simp [setReg], by simp [setReg], rfl, rfl, rfl, rfl, rfl⟩
    (MemFrame.refl _ _) he (by simp [setReg, seed_mod])

/-- The witness call state: `MemSat.wstate` at the entry, with `nilinterhash(EFV, 7)` (the `any` value `EFV = (TD, VAL)`). -/
def r : Nat → W64 := fun i => if i = 0 then BitVec.ofNat 64 EFV else if i = 1 then 7 else 0
def s0 : State := { MemSat.wstate r with pc := BitVec.ofNat 64 Extracted.entry }

/-- The hashes of a `TD`-value do not depend on the window (as `HashSat.wstate_hashFrame`, for
the stack bound 72). -/
theorem hashFrame (p : Nat) : HashFrame H0 TD EqHashModel.wmem p (calleeStack s0 72 2) := by
  intro m' hf
  refine ⟨fun h => h, fun _ _ => Iff.rfl, ?_⟩
  simp only [isDirectIface, tyTFlag]
  rw [hf.readLE _ _ ?_]
  simp only [calleeStack, s0, MemSat.wstate, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
  simp [wsp, TD]

theorem pre : HPre H0 72 2 s0 ∧ IfaceInput s0 72 (s0.regs 0).toNat ∧
    (s0.mem.readLE (s0.regs 0).toNat 8 ≠ 0 →
      H0.Hashable (s0.mem.readLE (s0.regs 0).toNat 8) s0.mem
        (dataAt s0.mem (s0.mem.readLE (s0.regs 0).toNat 8) (s0.regs 0).toNat) ∧
      HashFrame H0 (s0.mem.readLE (s0.regs 0).toNat 8) s0.mem
        (dataAt s0.mem (s0.mem.readLE (s0.regs 0).toNat 8) (s0.regs 0).toNat) (calleeStack s0 72 2)) := by
  have hp : HPre H0 72 2 s0 := by
    refine ⟨wmem_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_⟩ <;>
      simp only [CallOK, calleeStack, H0_priv, outside_cons, outside_nil] <;> decide
  have hi : IfaceInput s0 72 (s0.regs 0).toNat := by
    simp only [IfaceInput, Input, calleeStack, outside_cons, outside_nil]; decide
  have em : s0.mem = EqHashModel.wmem := rfl
  have e0 : (s0.regs 0).toNat = EFV := by simp [s0, r, MemSat.wstate, EFV]
  refine ⟨hp, hi, fun _ => ?_⟩
  rw [em, e0]
  have ht : EqHashModel.wmem.readLE EFV 8 = TD := by decide
  rw [ht]
  exact ⟨rfl, by rw [← em]; exact hashFrame _⟩

/-- All hypotheses of `correctness` hold together (bounds `d' = 8`, `d = 72`). -/
theorem nonvacuous : ∃ (impl : List Segment) (H : HashModel) (d d' : Nat), H.Laws ∧ 8 ≤ d' ∧
    d' + 64 ≤ d ∧
    Typehash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typehash") H d' ∧
    ∃ s, s.pc = BitVec.ofNat 64 Extracted.entry ∧ (HPre H d 2 s ∧ IfaceInput s d (s.regs 0).toNat ∧
    (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
      H.Hashable (s.mem.readLE (s.regs 0).toNat 8) s.mem
        (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat) ∧
      HashFrame H (s.mem.readLE (s.regs 0).toNat 8) s.mem
        (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat) (calleeStack s d 2))) :=
  ⟨implAt, H0, 72, 8, H0_laws, by decide, by decide, model 8, s0, rfl, pre⟩

/-- `correctness` at `s0`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (s0.regs 30) s0
    (fun s' => HRet H0 72 2 s0 s' fun r =>
      IHashIs H0 s0.mem (s0.mem.readLE (s0.regs 0).toNat 8) (s0.regs 0).toNat (s0.regs 1).toNat (r 0).toNat) :=
  correctness implAt H0 H0_laws 72 8 (by decide) (by decide) (model 8) s0 rfl pre

end Witness

end Proof
