import Janus.Contracts.Map

/-!
# The allocating map contracts are satisfiable (arm64, round 10 V2)

`Assign` and `MakeSmall` were unsatisfiable together with `MapModel.Laws` before round 10
(`audit/round10/model/MapUnsat.lean`): each handed `M.Env` back, so one call state chained to
unboundedly many allocations in a finite private memory. With the readiness predicate `H` they
are not. This file gives, for each, a model `M0` whose laws hold (`M0_laws`), machine code placed
at `A0` of a program with no other code, a readiness predicate, a proof by symbolic execution
that the code meets the contract, and a call state that satisfies the whole precondition, `H`
included (`<contract>_satisfiable`; `audit/round9/run-round9.sh`, row SAT).

The model is a toy, not the Go runtime: a single map header `HDR` whose first word is its count
(0 or 1) and whose second word holds the value of the one key it can hold, `5`.
-/

namespace Janus.Contracts.MapSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Map

/-- A program with no code, stubs or data of its own. -/
def toy : Program := { segments := [], stubs := [], exitAddr := 0 }
/-- Where the implementations are placed. -/
def A0 : Nat := 0x100000
def at0 (ws : List Nat) : List Segment := [{ name := "model", base := A0, words := ws }]
def withCode (ws : List Nat) : Program := { segments := at0 ws, stubs := [], exitAddr := 0 }
theorem link_at0 (ws : List Nat) : toy.link (at0 ws) = withCode ws := rfl

def HDR : Nat := 0x10000
def SLOT : Nat := 0x10008
def TY : Nat := 0x30000
def K5 : BitVec 64 := 5

/-- The map at `mp` holds `f`: `mp` is the one header, its first word is the count, and the map
is empty or holds `5 ↦` the second word. -/
def Rep0 (m : Memory) (mp : Nat) (f : AMap (BitVec 64) (BitVec 64)) : Prop :=
  mp = HDR ∧ m.accessible HDR 16 true = true ∧ m.accessible HDR 8 false = true ∧
    ((m.readLE HDR 8 = 0 ∧ f = AMap.empty) ∨
     (m.readLE HDR 8 = 1 ∧ f = AMap.empty.set K5 (BitVec.ofNat 64 (m.readLE SLOT 8))))

def M0 : MapModel (BitVec 64) (BitVec 64) where
  Rep := Rep0
  Iter := fun _ _ _ _ _ => False
  Typ := fun t => t = TY
  Env := fun _ _ => True
  priv := [(HDR, HDR + 16)]
  depth := 64

theorem keys_one (v : BitVec 64) : Keys (AMap.empty.set K5 v : AMap (BitVec 64) (BitVec 64)) [K5] :=
  ⟨List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun k => by
    by_cases h : k = K5 <;> simp [AMap.set, h]⟩

theorem inPriv {a n : Nat} (h1 : HDR ≤ a) (h2 : a + n ≤ HDR + 16) : InRanges a n M0.priv :=
  ⟨(HDR, HDR + 16), by simp [M0], h1, h2⟩

theorem M0_laws : M0.Laws where
  rep_frame m m' mp f h ha := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have e1 : m'.readLE HDR 8 = m.readLE HDR 8 := ha.readLE (inPriv (Nat.le_refl _) (by decide))
    have e2 : m'.readLE SLOT 8 = m.readLE SLOT 8 := ha.readLE (inPriv (by decide) (by decide))
    exact ⟨h1, by rw [ha.accessible]; exact h2, by rw [ha.accessible]; exact h3, by rw [e1, e2]; exact h4⟩
  iter_frame _ _ _ _ _ _ h _ := h
  env_frame _ _ _ _ _ := trivial
  len m mp f h := by
    obtain ⟨rfl, -, h3, h4⟩ := h
    refine ⟨h3, by decide, fun ks hks => ?_⟩
    rcases h4 with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · rw [e, hks.eq_nil_of_empty]; rfl
    · rw [e, ← (keys_one _).length_eq hks]; rfl
  finite m mp f h := by
    obtain ⟨-, -, -, h4⟩ := h
    rcases h4 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨[], keys_empty⟩
    · exact ⟨[K5], keys_one _⟩

/-! ## The witness call state -/

def wsp : Nat := 0x48000
def wg : Nat := 0x50000
def wret : Nat := 0x200000

/-- Stack `[wsp - 64, wsp + 64)`, the goroutine (stack guard 0), the header (count `c`). -/
def wmem (c : Nat) : Memory :=
  ⟨fun a => if a = HDR then BitVec.ofNat 8 c else 0,
   [⟨wsp - 64, 128, true⟩, ⟨wg, 0x100, false⟩, ⟨HDR, 16, true⟩]⟩

def wstate (c : Nat) (r : Nat → W64) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else r i,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := wmem c }

theorem wmem_acc (c a n : Nat) (w : Bool) : (wmem c).accessible a n w = (wmem 0).accessible a n w := rfl

theorem wmem_guard (c : Nat) : (wmem c).readLE (wg + 16) 8 = 0 := by
  simp only [wmem, Memory.readLE, HDR, wg]
  simp

theorem wstate_rtpre (c : Nat) (r : Nat → W64) (n : Nat) (hn : n ≤ 3) : RTPre M0 n (wstate c r) := by
  have hw : (wmem 0).accessible (wsp - 64) (64 + 8 + 8 * 3) true = true := by decide
  have h28 : (wstate c r).regs 28 = BitVec.ofNat 64 wg := rfl
  have h30 : (wstate c r).regs 30 = BitVec.ofNat 64 wret := rfl
  have hsp : (wstate c r).sp = BitVec.ofNat 64 wsp := rfl
  have hm : (wstate c r).mem = wmem c := rfl
  refine ⟨trivial, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, by decide, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, h28]; decide
  · simp only [regG, stackguard0Offset, h28, hm, wmem_acc]; decide
  · simp only [stackguard0, regG, stackguard0Offset, h28, hm, hsp, BitVec.toNat_ofNat]
    rw [show wg % 2 ^ 64 + 16 = wg + 16 by decide, wmem_guard]; decide
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp]; decide
  · simp only [hsp]; simp [wsp]; omega
  · simp only [hsp, hm, wmem_acc, BitVec.toNat_ofNat]
    exact Memory.accessible_mono _ hw (by simp [wsp]; decide) (by simp [wsp, M0]; omega)
  · simp only [hsp, BitVec.toNat_ofNat]
    simp [wsp, HDR, M0]

theorem acc_read {m : Memory} {a n : Nat} (h : m.accessible a n true = true) :
    m.accessible a n false = true := by
  obtain ⟨⟨r, hr, h1, h2, h3, -⟩, -⟩ := (Memory.accessible_iff m a n true).1 h
  exact Memory.accessible_of_mem m hr h1 h2 h3

/-- The return of a model implementation as `RTReturn`: the preserved registers and fields. -/
theorem rtReturn_of (nargs : Nat) (except : Nat) (s s' : State)
    (P : (Nat → W64) → Memory → Prop) (hsp : s'.sp = s.sp) (hpc : s'.pc = s.regs 30)
    (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29)
    (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr) (hfc : s'.fpcr = s.fpcr)
    (hfs : s'.fpsr = s.fpsr) (hfr : MemFrame s.mem s'.mem (rtWrites M0 s nargs ++ []))
    (hok : OthersKept M0 s.mem s'.mem except) (hp : P s'.regs s'.mem) :
    RTReturn M0 nargs [] except s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.mem, ?_, hfr, trivial, hok, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc hdz htp hfc hfs h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc hfs
  congr
  funext i
  simp only [keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-! ## `Assign` -/

/-- `movz x9, #1; str x9, [x1]; add x0, x1, #8; ret`: count 1, return the value slot. -/
def assignCode : List Nat := [0xd2800029, 0xf9000029, 0x91002020, 0xd65f03c0]

/-- Ready for exactly `m[5] = v` on the one map. -/
def Hassign : RtReady := fun args _ _ _ => args = [TY, HDR, 5]

theorem assign_impl : Assign (toy.link (at0 assignCode)) A0 M0 Hassign := by
  rw [link_at0]
  intro f s hpc ⟨hrt, hty, hm0, hrep, hH⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hrt
  simp only [Ready, Hassign, List.cons.injEq, and_true] at hH
  obtain ⟨h0, h1, h2⟩ := hH
  obtain ⟨-, hacc16, hacc8, hcase⟩ := hrep
  have hr1 : s.regs 1 = BitVec.ofNat 64 HDR := by
    apply BitVec.eq_of_toNat_eq; rw [h1]; rfl
  have hr2 : s.regs 2 = K5 := by apply BitVec.eq_of_toNat_eq; rw [h2]; rfl
  janus_run
  have hs0 : ((setReg (setReg s.regs 0 (BitVec.ofNat 64 HDR + 8#64)) 9 1#64) 0).toNat = SLOT := by
    simp [setReg]; decide
  have hfs : ∀ v : BitVec 64, f.set K5 v = AMap.empty.set K5 v := by
    intro v; funext k
    rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> by_cases hk : k = K5 <;> simp [AMap.set, hk]
  refine rtReturn_of 3 HDR s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl ?_ (fun mp g hne hr => absurd hr.1 hne) ?_
  · simp only [rtWrites, calleeStack, M0, List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  · rw [hs0]; dsimp only
    refine ⟨?_, inPriv (by decide) (by decide), fun v => ⟨?_, trivial, fun mp g hne hr => absurd hr.1 hne⟩⟩
    · simp only [Memory.accessible_writeLE]
      exact Memory.accessible_mono _ hacc16 (by decide) (by decide)
    · refine ⟨rfl, by simp only [Memory.accessible_writeLE]; exact hacc16,
        by simp only [Memory.accessible_writeLE]; exact hacc8, Or.inr ⟨?_, ?_⟩⟩
      · rw [readLE_writeLE_disjoint _ _ (by decide), Memory.readLE_writeLE_self]
      · rw [Memory.readLE_writeLE_self, hfs, Nat.mod_eq_of_lt v.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `Assign` is satisfiable, together with the laws, for a call state meeting its whole
precondition. -/
theorem assign_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment) (H : RtReady),
    M.Laws ∧ Assign (toy.link impl) A0 M H ∧
    ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧ M.Rep s.mem (s.regs 1).toNat f ∧
      Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s :=
  ⟨M0, _, _, M0_laws, assign_impl, AMap.empty,
    wstate 0 (fun i => if i = 0 then BitVec.ofNat 64 TY else if i = 1 then BitVec.ofNat 64 HDR
      else if i = 2 then 5 else 0), rfl, wstate_rtpre _ _ 3 (Nat.le_refl _), rfl, by decide,
    ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩, rfl⟩

/-! ## `MakeSmall` -/

/-- `movz x0, #1, lsl 16; str xzr, [x0]; ret`: the header `HDR`, count 0. -/
def makeCode : List Nat := [0xd2a00020, 0xf900001f, 0xd65f03c0]

/-- Ready when the header is writable and not yet a map (its first word is 2, which no
represented map has). -/
def Hmake : RtReady := fun args _ _ v => args = [] ∧ v.accessible HDR 16 true = true ∧ v.readLE HDR 8 = 2

theorem makeSmall_impl : MakeSmall (toy.link (at0 makeCode)) A0 M0 Hmake := by
  rw [link_at0]
  intro s hpc ⟨hrt, hH⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩ := hrt
  obtain ⟨-, hacc, h2⟩ := hH
  rw [rtView_accessible] at hacc
  rw [readLE_rtView (inPriv (Nat.le_refl _) (by decide))] at h2
  have hno : ∀ mp g, ¬ M0.Rep s.mem mp g := by
    rintro mp g ⟨-, -, -, ⟨e, -⟩ | ⟨e, -⟩⟩ <;> rw [h2] at e <;> exact absurd e (by decide)
  janus_run
  refine rtReturn_of 0 0 s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl ?_ (fun mp g _ hr => absurd hr (hno mp g)) ?_
  · simp only [rtWrites, calleeStack, M0, HDR, List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  · have hs0 : ((setReg s.regs 0 (65536#64)) 0).toNat = HDR := by simp [setReg]; decide
    dsimp only
    rw [hs0]
    refine ⟨by decide, ⟨rfl, by simp only [Memory.accessible_writeLE]; exact hacc,
      by simp only [Memory.accessible_writeLE]; exact Memory.accessible_mono _ (acc_read hacc) (Nat.le_refl _) (by decide),
      Or.inl ⟨by rw [show (65536 : Nat) = HDR from rfl, Memory.readLE_writeLE_self], rfl⟩⟩, fun mp g hr => absurd hr (hno mp g)⟩

/-- `MakeSmall` is satisfiable, together with the laws, for a call state meeting its whole
precondition. -/
theorem makeSmall_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Segment) (H : RtReady),
    M.Laws ∧ MakeSmall (toy.link impl) A0 M H ∧
    ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧ RTPre M 0 s ∧ Ready H M.priv [] s :=
  ⟨M0, _, _, M0_laws, makeSmall_impl, wstate 2 (fun _ => 0), rfl, wstate_rtpre _ _ 0 (by decide),
    rfl, by decide, by decide⟩

end Janus.Contracts.MapSat
