import Janus
import Extracted

/-!
# `InsertS(m map[string]uint64, k string, v uint64)` sets `m[k] = v` (amd64)

As on arm64, under `MapStr.AssignStr64` (8-byte values) and a readiness predicate `H` at entry
(`RSP` of the call `48` bytes below the entry's).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
  Janus.Contracts.MapStr Janus.Contracts.MapVar

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x21)

/-- The stack window of `InsertS` and the runtime call (amd64). -/
def window (M : MapModel (Nat × Nat) (BitVec 64)) (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - (M.depth + 48), (s.regs 4).toNat + 40)]

/-- The return address the call at `Extracted.entry + 0x28` pushes. -/
def ret2d : Nat := Extracted.entry + 0x2d

/-- The precondition. -/
def pre (M : MapModel (Nat × Nat) (BitVec 64)) (H : Contracts.RtReady) (m kp kl : BitVec 64)
    (f : AMap (Nat × Nat) (BitVec 64)) (s : State) : Prop :=
  CallerOK M s 48 40 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
    kp.toNat + kl.toNat ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat kl.toNat false = true ∧
    Outside kp.toNat kl.toNat (window M s) ∧ StrOwned M kp.toNat kl.toNat ∧
    H [mapType, m.toNat, kp.toNat, kl.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 48)
      (Contracts.rtView M.priv s.mem)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (Nat × Nat) (BitVec 64))
    (hl : M.Laws) (H : Contracts.RtReady)
    (hasn : AssignStr64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_faststr") 8 M H)
    (m kp kl v : BitVec 64) (f : AMap (Nat × Nat) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp, kl, v] (pre M H m kp kl f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set (strKey s.mem kp.toNat kl.toNat) v) ∧
        M.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap, hkb, hka, hko, hown, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  simp only [window, outside_cons, outside_nil, and_true] at hko
  have hsp48 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapassign_faststr"]
  have hfw : MemFrame s.mem ((((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) + 16) 8 kp.toNat).writeLE
      (BitVec.toNat (s.regs 4) + 32) 8 v.toNat).writeLE (BitVec.toNat (s.regs 4) - 48) 8 ret2d)
      [((s.regs 4).toNat - (M.depth + 48), (s.regs 4).toNat + 40)] := by janus_frame
  janus_eval_nat hR : ret2d
  simp only [hR] at hfw
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp [setRegF, hsp48]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, hsp48, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, by simpa [setRegF] using hm0, ?_,
      ⟨?_, ?_, ?_⟩, ?_, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simpa [setRegF] using hkb
  · simpa [setRegF, hfw.accessible] using hka
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, calleeStack, hsp48, outside_cons,
      outside_nil, and_true]
    omega
  · simpa [setRegF] using hown
  · simp only [Contracts.Ready64, setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
    repeat rw [Contracts.rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    simpa using hH
  · intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp48] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hset
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := Janus.InRanges.disjoint hin (Outside.of_sub hout (a := (s.regs 4).toNat - (M.depth + 48))
      (n := M.depth + 48 + 40) (by omega) (by omega))
    have hk := hfw.readLE kp.toNat kl.toNat (by simp only [outside_cons, outside_nil, and_true]; exact hko)
    janus64_run
    simp only [strKey, hk] at hset ⊢
    exact ⟨(hset v).1, (hset v).2.1⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `MapModel0.MC ckStr`, the readiness `MapSatAmd64.HAssignStr`, its code
`MapSatAmd64.assignStrCode64` behind a `JMP` at the contract's address, and a call inserting
the 8-byte string at `SK` (in the runtime's memory) with value `42` into the empty map `MP`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64

def cAddr : Nat := Extracted.program.contractAddr "runtime.mapassign_faststr"

def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := assignStrCode64 }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : AssignStr64 (Extracted.program.link implAt) cAddr 8 (MC ckStr) HAssignStr := by
  have hA : AssignStr64 (Extracted.program.link implAt) A0 8 (MC ckStr) HAssignStr := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (assignStr64_impl f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def mv : BitVec 64 := BitVec.ofNat 64 MP
def kp : BitVec 64 := BitVec.ofNat 64 SK
def kl : BitVec 64 := 8#64
def v : BitVec 64 := 42#64

/-- The witness call state: `InsertS(MP, "ABCD\0\0\0\0", 42)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 3 then kp else if i = 1 then kl else if i = 7 then v
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kp, kl, v] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem pre0 : pre (MC ckStr) HAssignStr mv kp kl AMap.empty s0 := by
  refine ⟨⟨mmem64_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩, trivial, by decide, mmem64_repC _, by decide, by decide, ?_,
    Or.inr (inPriv0 (by decide) (by decide)), ?_⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [window, MC_depth, outside_cons, outside_nil, and_true]; decide
  · refine ⟨?_, Or.inr (Or.inl (by decide))⟩
    show (Contracts.rtView priv0 mmem64).readLE MP 8 = 0
    rw [readLE_rtView0 (by decide) (by decide)]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (Nat × Nat) (BitVec 64))
    (H : Contracts.RtReady) (ret : Nat) (s : State) (m kp kl v : BitVec 64)
    (f : AMap (Nat × Nat) (BitVec 64)),
    M.Laws ∧ AssignStr64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_faststr") 8 M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, kp, kl, v] s ∧
    pre M H m kp kl f s :=
  ⟨implAt, MC _, HAssignStr, ret, s0, mv, kp, kl, v, AMap.empty, MC_laws _, model, hret, setup, pre0⟩

/-- So the guarantee is reached: the map now holds the key's content with `42`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (MC ckStr).Rep s'.mem MP (AMap.empty.set (strKey mmem64 SK 8) 42#64) :=
  correctness implAt (MC _) (MC_laws _) HAssignStr model mv kp kl v AMap.empty ret hret s0 setup pre0
    |>.mono fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
