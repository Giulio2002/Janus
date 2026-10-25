import Janus
import Extracted

/-!
# `MakeHint(n int) map[uint64]uint64` returns `make(map[uint64]uint64, n)` (amd64)

As on arm64, under `MapVarAmd64.MakeMap` and a readiness predicate `H` at entry (`RSP` of the
call `40` bytes below the entry's).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
  Janus.Contracts.MapVarAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x13)

/-- The return address the call at `Extracted.entry + 0x1a` pushes. -/
def ret1f : Nat := Extracted.entry + 0x1f

/-- The precondition. -/
def pre (M : MapModel (BitVec 64) (BitVec 64)) (H : Contracts.RtReady) (n : BitVec 64) (s : State) :
    Prop :=
  CallerOK M s 40 8 ∧ M.Typ mapType ∧
    H [mapType, n.toNat, 0] (s.regs 14).toNat ((s.regs 4).toNat - 40) (Contracts.rtView M.priv s.mem)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws) (H : Contracts.RtReady)
    (hmk : MakeMap (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.makemap") M H)
    (n : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [n] (pre M H n)
      (fun s s' => (s'.regs 0).toNat ≠ 0 ∧ M.Rep s'.mem (s'.regs 0).toNat AMap.empty ∧
        (∀ mp f, M.Rep s.mem mp f → mp ≠ (s'.regs 0).toNat) ∧ M.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs ⟨hc, hty, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.makemap"]
  have hfw : MemFrame s.mem ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 ret1f)
      [((s.regs 4).toNat - (M.depth + 40), (s.regs 4).toNat + 8)] := by janus_frame
  janus_eval_nat hR : ret1f
  simp only [hR] at hfw
  refine Reaches.call (Summary.withExit hmk hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, by simp [setRegF], ?_⟩ ?_
  · simp only [Contracts.Ready64, setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
    repeat rw [Contracts.rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    simpa using hH
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hnz, hrep, hfresh⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    janus64_run
    simp only [setRegF, keepABI_apply, reduceIte, Nat.reduceEqDiff] at hnz hrep henv' hfresh ⊢
    refine ⟨hnz, hrep, fun mp f h => hfresh mp f (hl.rep_frame _ _ _ _ h
      (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))), henv'⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `MapModel0.MC ck64`, the readiness `MapModel0.HMake`, its code
`MapSatAmd64.makeCode` behind a `JMP` at the contract's address, and a call `MakeHint(100)`
with no map alive. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64 Janus.Contracts.MapVarSatAmd64

def cAddr : Nat := Extracted.program.contractAddr "runtime.makemap"

def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := makeCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : MakeMap (Extracted.program.link implAt) cAddr (MC ck64) HMake := by
  have hA : MakeMap (Extracted.program.link implAt) A0 (MC ck64) HMake := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) makeMap_impl
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def n : BitVec 64 := 100#64

/-- The witness call state: `MakeHint(100)`, no map alive. -/
def s0 : State :=
  { regs := fun i => if i = 0 then n
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmem64Dead }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0) with rfl; rfl, rfl⟩

theorem pre0 : pre (MC ck64) HMake n s0 := by
  refine ⟨⟨show ZEnv mmem64Dead from mmem64_zenv.writeLE _ (by decide), ⟨by decide, by decide, by decide⟩,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩, trivial, hMake_dead64 _ _ _⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (H : Contracts.RtReady) (ret : Nat) (s : State) (n : BitVec 64),
    M.Laws ∧ MakeMap (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.makemap") M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [n] s ∧ pre M H n s :=
  ⟨implAt, MC _, HMake, ret, s0, n, MC_laws _, model, hret, setup, pre0⟩

/-- So the guarantee is reached: a new, empty map. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat ≠ 0 ∧ (MC ck64).Rep s'.mem (s'.regs 0).toNat AMap.empty :=
  correctness implAt (MC _) (MC_laws _) HMake model n ret hret s0 setup pre0
    |>.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

end Witness

end Proof
