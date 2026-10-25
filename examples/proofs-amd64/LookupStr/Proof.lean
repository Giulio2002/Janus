import Janus
import Extracted

/-!
# `LookupStr(m map[string]uint64, k string) (uint64, bool)` on amd64

As on arm64, under `MapStr.Access2Str64`; `ok` in `BL`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
  Janus.Contracts.MapStr

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x1c)

/-- The stack window of `LookupStr` and the runtime call (amd64). -/
def window (M : MapModel (Nat × Nat) (BitVec 64)) (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - (M.depth + 48), (s.regs 4).toNat + 24)]

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (Nat × Nat) (BitVec 64))
    (hl : M.Laws)
    (hacc : Access2Str64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_faststr") M)
    (m kp kl : BitVec 64) (f : AMap (Nat × Nat) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp, kl]
      (fun s => CallerOK M s 48 24 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f ∧
        kp.toNat + kl.toNat ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat kl.toNat false = true ∧
        Outside kp.toNat kl.toNat (window M s))
      (fun s s' => s'.regs 0 = (f (strKey s.mem kp.toNat kl.toNat)).getD 0 ∧
        (s'.regs 3).toNat % 256 = (f (strKey s.mem kp.toNat kl.toNat)).isSome.toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap, hkb, hka, hko⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  simp only [window, outside_cons, outside_nil, and_true] at hko
  have hsp48 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapaccess2_faststr"]
  have hfw : MemFrame s.mem (((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) + 16) 8 kp.toNat).writeLE
      (BitVec.toNat (s.regs 4) - 48) 8 4741512)
      [((s.regs 4).toNat - (M.depth + 48), (s.regs 4).toNat + 24)] := by janus_frame
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp [setRegF, hsp48]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, hsp48, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simpa [setRegF] using hkb
  · simpa [setRegF, hfw.accessible] using hka
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, calleeStack, hsp48, outside_cons,
      outside_nil, and_true]
    omega
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩, hok⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp48] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    have hk := hfw.readLE kp.toNat kl.toNat (by simp only [outside_cons, outside_nil, and_true]; exact hko)
    janus64_run
    all_goals try simp only [setRegF, reduceIte, Nat.reduceEqDiff, strKey, hk] at hs3 hok
    all_goals first | exact hok | (simpa [strKey] using hok) | (simp [strKey, hk]; done) | (simp [strKey, hk]; exact hok) | exact ⟨by rw [hs3]; simp [strKey], by simpa [strKey] using hok⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `MapStr.MS0` (every map is nil), its code `MapStr.access2StrCode64` at
`IfaceSatAmd64.A0` behind a `JMP` at the contract's address, and a lookup of the 8-byte string
`VAL` in a nil map, which returns `(0, false)`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel

/-- `runtime.mapaccess2_faststr`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.mapaccess2_faststr"

def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := access2StrCode64 }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : Access2Str64 (Extracted.program.link implAt) cAddr MS0 := by
  have hA : Access2Str64 (Extracted.program.link implAt) A0 MS0 := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (access2Str64_impl f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

/-- The witness return address (the word at `[wsp]` of `wmem64`). -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def kp : BitVec 64 := BitVec.ofNat 64 VAL
def kl : BitVec 64 := 8#64

/-- The witness call state: `LookupStr(nil, "…")`. -/
def s0 : State :=
  { regs := fun i => if i = 3 then kp else if i = 1 then kl
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [0#64, kp, kl] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem pre0 : CallerOK MS0 s0 48 24 ∧ MS0.Typ mapType ∧ IsMap MS0 s0.mem (0#64).toNat AMap.empty ∧
    kp.toNat + kl.toNat ≤ 2 ^ 48 ∧ s0.mem.accessible kp.toNat kl.toNat false = true ∧
    Outside kp.toNat kl.toNat (window MS0 s0) := by
  refine ⟨⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩, trivial, by simp [IsMap], by decide, by decide, ?_⟩
  · simp only [MS0, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [MS0, outside_cons, outside_nil, and_true]; decide
  · simp only [window, MS0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (Nat × Nat) (BitVec 64))
    (ret : Nat) (s : State) (m kp kl : BitVec 64) (f : AMap (Nat × Nat) (BitVec 64)),
    M.Laws ∧ Access2Str64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_faststr") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, kp, kl] s ∧
    (CallerOK M s 48 24 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f ∧
      kp.toNat + kl.toNat ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat kl.toNat false = true ∧
      Outside kp.toNat kl.toNat (window M s)) :=
  ⟨implAt, MS0, ret, s0, 0#64, kp, kl, AMap.empty, MS0_laws, model, hret, setup, pre0⟩

/-- So the guarantee is reached: a lookup in a nil map gives `(0, false)`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 ∧ (s'.regs 3).toNat % 256 = 0 := by
  refine (correctness implAt MS0 MS0_laws model 0#64 kp kl AMap.empty ret hret s0 setup pre0).mono ?_
  intro s' h
  exact ⟨h.1, by simpa [AMap.empty] using h.2.1, by simpa [AMap.empty] using h.2.2⟩

end Witness

end Proof
