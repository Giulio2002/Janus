import Janus.Contracts.MapAmd64
import Janus.Contracts.MapSat

/-!
# The allocating map contracts are satisfiable (amd64, round 10 V2)

As `Janus.Contracts.MapSat` for `Assign` and `MakeSmall` of `Janus.Contracts.MapAmd64`: the same
toy model `M0` (its laws `M0_laws`), x86-64 machine code at `A0` of a program with no other
code, a readiness predicate, a proof by symbolic execution that the code meets the contract,
and a call state that satisfies the whole precondition, `H` included.
-/

namespace Janus.Contracts.MapSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
open Janus (MemFrame InRanges Outside outside_cons outside_nil)
open Janus.Contracts (RtReady Ready64 rtView rtView_accessible readLE_rtView)
open Janus.Contracts.MapSat (M0 M0_laws Rep0 HDR SLOT TY K5 inPriv acc_read wmem wmem_acc wmem_guard
  wsp wg)

def toy : Janus.Amd64.Program := { segments := [], stubs := [], exitAddr := 0 }
def A0 : Nat := 0x100000
def at0 (bs : List Nat) : List Janus.Amd64.Segment := [{ name := "model", base := A0, bytes := bs }]
def withCode (bs : List Nat) : Janus.Amd64.Program := { segments := at0 bs, stubs := [], exitAddr := 0 }
theorem link_at0 (bs : List Nat) : toy.link (at0 bs) = withCode bs := rfl

/-- The witness call state: arguments `r`, `RSP = wsp` (its word, the return address, is `0`),
`R14 = wg`, memory `wmem c`. -/
def wstate (c : Nat) (r : Nat → W64) : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else r i,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := wmem c }

theorem wmem_ret (c : Nat) : (wmem c).readLE wsp 8 = 0 := by
  simp only [wmem, Janus.Arm64.Memory.readLE, HDR, wsp]; simp

theorem wstate_rtpre (c : Nat) (r : Nat → W64) (n : Nat) (hn : n ≤ 3) : RTPre M0 n (wstate c r) := by
  have hw : (wmem 0).accessible (wsp - 64) (64 + 8 + 8 * 3) true = true := by decide
  have h4 : (wstate c r).regs 4 = BitVec.ofNat 64 wsp := rfl
  have h14 : (wstate c r).regs 14 = BitVec.ofNat 64 wg := rfl
  have hm : (wstate c r).mem = wmem c := rfl
  refine ⟨trivial, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [regG, stackguard0Offset, h14]; decide
  · simp only [regG, stackguard0Offset, h14, hm, wmem_acc]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, h14, h4, hm, BitVec.toNat_ofNat]
    rw [show wg % 2 ^ 64 + 16 = wg + 16 by decide, wmem_guard]; decide
  · simp only [h4]; decide
  · simp only [h4]; decide
  · simp only [h4]; simp [wsp]; omega
  · simp only [h4, hm, wmem_acc, BitVec.toNat_ofNat]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by simp [wsp]; decide) (by simp [wsp, M0]; omega)
  · simp only [h4, hm, BitVec.toNat_ofNat]
    rw [show wsp % 2 ^ 64 = wsp by decide, wmem_ret]; decide
  · simp only [h4, BitVec.toNat_ofNat]
    simp [wsp, HDR, M0]

/-- The return of a model implementation as `RTReturn` (amd64). -/
theorem rtReturn_of (nargs : Nat) (except : Nat) (s s' : Janus.Amd64.State)
    (P : (Nat → W64) → Janus.Arm64.Memory → Prop) (hrip : s'.rip = retAddrOf s)
    (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hmx : s'.mxcsr = s.mxcsr)
    (hfr : MemFrame s.mem s'.mem (rtWrites M0 s nargs ++ []))
    (hok : OthersKept M0 s.mem s'.mem except) (hp : P s'.regs s'.mem) :
    RTReturn M0 nargs [] except s s' P := by
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, ?_, hfr, trivial, hok, hp⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx ⊢
  subst hrip hfs hdf hmx
  congr
  · funext i
    simp only [keepABI]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-! ## `Assign` -/

/-- `movq $1, (%rbx); lea 8(%rbx), %rax; ret`: count 1, return the value slot. -/
def assignCode : List Nat := [0x48, 0xc7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x43, 0x08, 0xc3]

/-- Ready for exactly `m[5] = v` on the one map (`t`, `m`, `k` in `RAX`, `RBX`, `RCX`). -/
def Hassign : RtReady := fun args _ _ _ => args = [TY, HDR, 5]

theorem assign_impl : Assign (toy.link (at0 assignCode)) A0 M0 Hassign := by
  rw [link_at0]
  intro f s hpc ⟨hrt, hty, hm0, hrep, hH⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hrt
  simp only [Ready64, Hassign, List.cons.injEq, and_true] at hH
  obtain ⟨h0, h1, h2⟩ := hH
  obtain ⟨-, hacc16, hacc8, hcase⟩ := hrep
  have hr3 : s.regs 3 = BitVec.ofNat 64 HDR := by
    apply BitVec.eq_of_toNat_eq; rw [h1]; rfl
  have hr1 : s.regs 1 = K5 := by apply BitVec.eq_of_toNat_eq; rw [h2]; rfl
  simp only [M0, outside_cons, outside_nil, and_true] at hout hd1 hst
  janus64_run
  have hs0 : ((setRegF (setRegF s.regs 0 (BitVec.ofNat 64 HDR + 8#64)) 4 (s.regs 4 + 8#64)) 0).toNat = SLOT := by
    simp [setRegF]; decide
  have hfs : ∀ v : BitVec 64, f.set K5 v = AMap.empty.set K5 v := by
    intro v; funext k
    rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> by_cases hk : k = K5 <;> simp [AMap.set, hk]
  refine rtReturn_of 3 HDR s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl ?_ (fun mp g hne hr => absurd hr.1 hne) ?_
  · simp only [rtWrites, Janus.Contracts.MapAmd64.calleeStack, M0, List.append_nil, List.cons_append, List.nil_append]
    janus_frame
  · dsimp only
    rw [hs0]
    refine ⟨?_, inPriv (by decide) (by decide), fun v => ⟨?_, trivial, fun mp g hne hr => absurd hr.1 hne⟩⟩
    · simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_mono _ hacc16 (by decide) (by decide)
    · refine ⟨rfl, by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc16,
        by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc8, Or.inr ⟨?_, ?_⟩⟩
      · rw [Janus.Tactic.readLE_writeLE_disjoint _ _ (by decide), Janus.Arm64.Memory.readLE_writeLE_self]
      · rw [Janus.Arm64.Memory.readLE_writeLE_self, hfs, Nat.mod_eq_of_lt v.isLt, BitVec.ofNat_toNat,
          BitVec.setWidth_eq]

/-- `Assign` is satisfiable (amd64), together with the laws, for a call state meeting its whole
precondition. -/
theorem assign_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment)
    (H : RtReady), M.Laws ∧ Assign (toy.link impl) A0 M H ∧
    ∃ (f : AMap (BitVec 64) (BitVec 64)) (s : Janus.Amd64.State), s.rip = BitVec.ofNat 64 A0 ∧
      RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧ M.Rep s.mem (s.regs 3).toNat f ∧
      Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s :=
  ⟨M0, _, _, M0_laws, assign_impl, AMap.empty,
    wstate 0 (fun i => if i = 0 then BitVec.ofNat 64 TY else if i = 3 then BitVec.ofNat 64 HDR
      else if i = 1 then 5 else 0), rfl, wstate_rtpre _ _ 3 (Nat.le_refl _), rfl, by decide,
    ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩, rfl⟩

/-! ## `MakeSmall` -/

/-- `mov $0x10000, %eax; movq $0, (%rax); ret`: the header `HDR`, count 0. -/
def makeCode : List Nat := [0xb8, 0x00, 0x00, 0x01, 0x00, 0x48, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc3]

/-- Ready when the header is writable and not yet a map (its first word is 2). -/
def Hmake : RtReady := fun args _ _ v => args = [] ∧ v.accessible HDR 16 true = true ∧ v.readLE HDR 8 = 2

theorem makeSmall_impl : MakeSmall (toy.link (at0 makeCode)) A0 M0 Hmake := by
  rw [link_at0]
  intro s hpc ⟨hrt, hH⟩
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hrt
  obtain ⟨-, hacc, h2⟩ := hH
  rw [rtView_accessible] at hacc
  rw [readLE_rtView (inPriv (Nat.le_refl _) (by decide))] at h2
  have hno : ∀ mp g, ¬ M0.Rep s.mem mp g := by
    rintro mp g ⟨-, -, -, ⟨e, -⟩ | ⟨e, -⟩⟩ <;> rw [h2] at e <;> exact absurd e (by decide)
  simp only [M0, HDR, outside_cons, outside_nil, and_true] at hout hd1 hst
  janus64_run
  refine rtReturn_of 0 0 s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl ?_ (fun mp g _ hr => absurd hr (hno mp g)) ?_
  · simp only [rtWrites, Janus.Contracts.MapAmd64.calleeStack, M0, HDR, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  · have hs0 : ((setRegF (setRegF s.regs 0 65536#64) 4 (s.regs 4 + 8#64)) 0).toNat = HDR := by
      simp [setRegF]; decide
    dsimp only
    rw [hs0]
    refine ⟨by decide, ⟨rfl, by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc,
      by simp only [Janus.Arm64.Memory.accessible_writeLE]
         exact Janus.Arm64.Memory.accessible_mono _ (acc_read hacc) (Nat.le_refl _) (by decide),
      Or.inl ⟨by rw [show (65536 : Nat) = HDR from rfl, Janus.Arm64.Memory.readLE_writeLE_self], rfl⟩⟩,
      fun mp g hr => absurd hr (hno mp g)⟩

/-- `MakeSmall` is satisfiable (amd64), together with the laws, for a call state meeting its whole
precondition. -/
theorem makeSmall_satisfiable : ∃ (M : MapModel (BitVec 64) (BitVec 64)) (impl : List Janus.Amd64.Segment)
    (H : RtReady), M.Laws ∧ MakeSmall (toy.link impl) A0 M H ∧
    ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧ RTPre M 0 s ∧ Ready64 H M.priv [] s :=
  ⟨M0, _, _, M0_laws, makeSmall_impl, wstate 2 (fun _ => 0), rfl, wstate_rtpre _ _ 0 (by decide),
    rfl, by decide, by decide⟩

end Janus.Contracts.MapSatAmd64
