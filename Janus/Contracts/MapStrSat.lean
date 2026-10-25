import Janus.Contracts.MapStr
import Janus.Contracts.EqHashModel
import Janus.Contracts.IfaceSat

/-!
# The string-keyed map contracts are satisfiable (arm64)

For every contract of `Janus.Contracts.MapStr`: a model of the map runtime, machine code at
`IfaceSat.A0` proved (by symbolic execution) to meet the contract for that model, and a call
state that satisfies the contract's whole precondition (`audit/round9/sat_check.py`, row SAT).
-/



namespace Janus.Contracts.MapStr

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Map

/-- The zero slot of the model: 8 bytes of the model runtime's heap. -/
def ZS : Nat := 0x10f00

/-- The model: no non-nil map exists; the environment is a readable zero slot `ZS`. -/
def MS0 : MapModel (Nat × Nat) (BitVec 64) where
  Rep _ _ _ := False
  Iter _ _ _ _ _ := False
  Typ _ := True
  Env m _ := m.accessible ZS 8 false = true ∧ m.readLE ZS 8 = 0
  priv := [(0x10000, 0x11000)]
  depth := 64

theorem MS0_laws : MS0.Laws where
  rep_frame _ _ _ _ h _ := h.elim
  iter_frame _ _ _ _ _ _ h _ := h.elim
  env_frame m m' g h ha := by
    obtain ⟨h1, h2⟩ := h
    have hin : InRanges ZS 8 MS0.priv := ⟨(0x10000, 0x11000), by simp [MS0], by decide, by decide⟩
    exact ⟨by rw [ha.accessible]; exact h1, (ha.readLE hin).trans h2⟩
  len _ _ _ h := h.elim
  finite _ _ _ h := h.elim

/-- A map value of `MS0` is nil and empty. -/
theorem isMap_MS0 {m : Memory} {mp : Nat} {f : AMap (Nat × Nat) (BitVec 64)} (h : IsMap MS0 m mp f) :
    mp = 0 ∧ f = AMap.empty := by
  unfold IsMap at h
  split at h
  · exact ⟨by assumption, h⟩
  · exact h.elim

theorem env_wmem : MS0.Env EqHashModel.wmem 0 := ⟨by decide, by decide⟩

theorem env_wmem64 : MS0.Env EqHashModel.wmem64 0 := ⟨by decide, by decide⟩

end Janus.Contracts.MapStr

namespace Janus.Contracts.MapStr

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel

/-- The return of a model implementation as `Map.RTReturn` (arm64). -/
theorem mapReturn_of {K V : Type} (M : MapModel K V) (nargs : Nat) (extra : List (Nat × Nat))
    (except : Nat) (s s' : State) (P : (Nat → W64) → Memory → Prop) (hsp : s'.sp = s.sp)
    (hpc : s'.pc = s.regs 30) (h18 : s'.regs 18 = s.regs 18) (h28 : s'.regs 28 = s.regs 28)
    (h29 : s'.regs 29 = s.regs 29) (hdz : s'.dczid = s.dczid) (htp : s'.tpidr = s.tpidr)
    (hfc : s'.fpcr = s.fpcr) (hfs : s'.fpsr = s.fpsr)
    (hfr : MemFrame s.mem s'.mem (Map.rtWrites M s nargs ++ extra)) (henv : M.Env s'.mem (s.regs 28))
    (hok : Map.OthersKept M s.mem s'.mem except) (hp : P s'.regs s'.mem) :
    Map.RTReturn M nargs extra except s s' P := by
  refine ⟨s'.regs, s'.vregs, s'.flags, s'.mem, ?_, hfr, henv, hok, hp⟩
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s'
  simp only at hsp hpc hdz htp hfc hfs h18 h28 h29 ⊢
  subst hsp hpc hdz htp hfc hfs
  congr
  funext i
  simp only [Map.keepABI]
  split
  · rename_i hi; rcases hi with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · rfl

/-- `movz x0, #0xf00; movk x0, #1, lsl #16; mov x1, xzr; ret`: the zero slot and `false`. -/
def access2StrCode : List Nat := [0xd281e000, 0xf2a00020, 0xaa1f03e1, 0xd65f03c0]

theorem access2Str_impl : Access2Str (toy.link (at0 access2StrCode)) A0 MS0 := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨⟨he1, he2⟩, hg, hc, hout⟩, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨hmp, rfl⟩ := isMap_MS0 hmap
  janus_run
  refine mapReturn_of MS0 4 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2⟩ (fun _ _ _ h => h) ⟨?_, ?_, ?_⟩
  · simp [IsMap, hmp]
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    exact ⟨he1, ⟨(0x10000, 0x11000), by simp [MS0], by decide, by decide⟩, by simpa [AMap.empty, ZS] using he2⟩
  · simp [setReg, AMap.empty]

/-- `Access2Str` is satisfiable. -/
theorem access2Str_satisfiable : ∃ (M : MapModel (Nat × Nat) (BitVec 64)) (impl : List Segment),
    M.Laws ∧ Access2Str (toy.link impl) A0 M ∧ ∃ s : State, s.pc = BitVec.ofNat 64 A0 ∧
      (Map.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat AMap.empty ∧
        (s.regs 2).toNat + (s.regs 3).toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.regs 2).toNat (s.regs 3).toNat false = true ∧
        Outside (s.regs 2).toNat (s.regs 3).toNat (calleeStack s M.depth 4)) := by
  refine ⟨MS0, _, MS0_laws, access2Str_impl,
    { regs := fun i => if i = 2 then BitVec.ofNat 64 VAL else if i = 3 then 8#64
        else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else 0,
      sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
      mem := EqHashModel.wmem }, rfl, ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩, trivial,
      by simp [IsMap], by decide, by decide, ?_⟩⟩
  · simp only [MS0, outside_cons, outside_nil, and_true]; decide
  · simp only [calleeStack, MS0, outside_cons, outside_nil, and_true]; decide

end Janus.Contracts.MapStr

