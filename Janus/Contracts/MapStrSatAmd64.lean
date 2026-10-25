import Janus.Contracts.MapStrAmd64
import Janus.Contracts.MapStrSat
import Janus.Contracts.IfaceSatAmd64

/-!
# The string-keyed map contracts are satisfiable (amd64)

As `Janus.Contracts.MapStrSat`, for `Janus.Contracts.MapStrAmd64`.
-/

namespace Janus.Contracts.MapStr

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map
  Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
open Janus (MemFrame Outside outside_cons outside_nil InRanges)

/-- The return of a model implementation as `MapAmd64.RTReturn`. -/
theorem mapReturn64_of {K V : Type} (M : MapModel K V) (nargs : Nat) (extra : List (Nat × Nat))
    (except : Nat) (s s' : State) (P : (Nat → W64) → Janus.Arm64.Memory → Prop)
    (hrip : s'.rip = retAddrOf s) (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr = s.mxcsr)
    (hfr : MemFrame s.mem s'.mem (Contracts.MapAmd64.rtWrites M s nargs ++ extra))
    (henv : M.Env s'.mem (s.regs 14)) (hok : Contracts.MapAmd64.OthersKept M s.mem s'.mem except)
    (hp : P s'.regs s'.mem) : Contracts.MapAmd64.RTReturn M nargs extra except s s' P := by
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, ?_, hfr, henv, hok, hp⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx ⊢
  subst hrip hfs hdf hmx
  congr
  · funext i
    simp only [Contracts.MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [Contracts.MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-- `mov $0x10f00, %eax; xor %ebx, %ebx; ret`: the zero slot and `false`. -/
def access2StrCode64 : List Nat := [0xb8, 0x00, 0x0f, 0x01, 0x00, 0x31, 0xdb, 0xc3]

theorem access2Str64_impl : Access2Str64 (toy.link (at0 access2StrCode64)) A0 MS0 := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨⟨he1, he2⟩, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap, -⟩ := hpre
  obtain ⟨hmp, rfl⟩ := isMap_MS0 hmap
  janus64_run
  refine mapReturn64_of MS0 4 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) ⟨he1, he2⟩ (fun _ _ _ h => h)
    ⟨?_, ?_, ?_⟩
  · simp [IsMap, hmp]
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact ⟨he1, ⟨(0x10000, 0x11000), by simp [MS0], by decide, by decide⟩, by simpa [AMap.empty, ZS] using he2⟩
  · simp [setRegF, AMap.empty]

/-- `Access2Str64` is satisfiable. -/
theorem access2Str64_satisfiable : ∃ (M : MapModel (Nat × Nat) (BitVec 64))
    (impl : List Janus.Amd64.Segment), M.Laws ∧ Access2Str64 (toy.link impl) A0 M ∧
      ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (Contracts.MapAmd64.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat AMap.empty ∧
        (s.regs 1).toNat + (s.regs 7).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 1).toNat (s.regs 7).toNat false = true ∧
        Outside (s.regs 1).toNat (s.regs 7).toNat (Contracts.MapAmd64.calleeStack s M.depth 4)) := by
  refine ⟨MS0, _, MS0_laws, access2Str64_impl,
    { regs := fun i => if i = 1 then BitVec.ofNat 64 VAL else if i = 7 then 8#64
        else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
      rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
      mem := Janus.Contracts.EqHashModel.wmem64 }, rfl,
    ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
      by decide, rfl, rfl, by decide, ?_⟩, trivial, by simp [IsMap], by decide, by decide, ?_⟩⟩
  · simp only [MS0, outside_cons, outside_nil, and_true]; decide
  · simp only [Contracts.MapAmd64.calleeStack, MS0, outside_cons, outside_nil, and_true]; decide

end Janus.Contracts.MapStr
