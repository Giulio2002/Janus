import Janus
import Extracted

/-!
# `StrEq(s, t string) bool` on amd64: `s == t`

As on arm64: the lengths compare inline (`CMPQ BX, DI`), equal lengths call
`runtime.memequal(p1, p2, len)` under the `MemAmd64.Memequal` contract. On amd64 `memequal` stays
a contract: its `memeqbody` reads up to 7 bytes around short inputs (within a page), which the
model's byte-exact memory does not grant.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Mem
open Janus (MemFrame Outside outside_cons outside_nil)

/-- The precondition (see the module documentation). -/
def pre (d : Nat) (p1 l1 p2 l2 : BitVec 64) (s : State) : Prop :=
  MemAmd64.CallerOK s d 40 40 ∧ Buffer s p1 l1.toNat false ∧ Buffer s p2 l2.toNat false ∧
    Outside p1.toNat l1.toNat (MemAmd64.callerWindow s d 40 40) ∧
    Outside p2.toNat l2.toNat (MemAmd64.callerWindow s d 40 40)

/-- The return address the call at `Extracted.entry + 0x30` pushes. -/
def ret30 : Nat := Extracted.entry + 0x30

theorem correctness (impl : List Segment) (d : Nat)
    (hmem : MemAmd64.Memequal (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memequal") d)
    (p1 l1 p2 l2 : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p1, l1, p2, l2] (pre d p1 l1 p2 l2)
      (fun s s' => (s'.regs 0).toNat % 256 =
        (l1 == l2 && s.mem.readLE p1.toNat l1.toNat == s.mem.readLE p2.toNat l2.toNat).toNat) := by
  intro ret hret s hs ⟨hc, ⟨hP1', hP1⟩, ⟨hP2', hP2⟩, ho1, ho2⟩
  janus64_intro hs
  have hc' := hc
  obtain ⟨hg, hal, hd, hb, hst, hog⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  simp only [outside_cons, outside_nil, and_true] at hog
  by_cases hl : l1 = l2
  · subst hl
    have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
      rw [BitVec.toNat_sub]; simp; omega
    janus64_run until [Extracted.program.contractAddr "runtime.memequal"]
    have hfw : MemFrame s.mem ((((Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
        (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) + 8) 8 p1.toNat).writeLE
        (BitVec.toNat (s.regs 4) + 24) 8 p2.toNat).writeLE (BitVec.toNat (s.regs 4) - 40) 8 ret30)
        (MemAmd64.callerWindow s d 40 40) := by
      simp only [MemAmd64.callerWindow]; janus_frame
    janus_eval_nat hR30 : ret30
    simp only [hR30] at hfw
    refine Reaches.call (Summary.withExit hmem hret) rfl
      ⟨MemAmd64.EqPre.of_caller hc hfw (by simp [setRegF, hsp40]) (by simp [setRegF])
        (by simpa using hs.zero) (by simpa using hs.df)
        (by simp [setRegF, hsp40, Janus.Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide),
       MemAmd64.Input.of_caller hfw (by simp [setRegF, hsp40]) (by decide) (by omega)
         (by simpa [setRegF, h_a0] using hP1') (by simpa [setRegF, h_a0] using hP1)
         (by simpa [setRegF, h_a0] using ho1),
       MemAmd64.Input.of_caller hfw (by simp [setRegF, hsp40]) (by decide) (by omega)
         (by simpa [setRegF, h_a2] using hP2') (by simpa [setRegF, h_a2] using hP2)
         (by simpa [setRegF, h_a2] using ho2)⟩ ?_
    intro s' hpc' ⟨r, x, y, fl, mx, m', hs', hmx, hfr, hres⟩
    subst hs'
    simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte,
      Nat.reduceEqDiff, hsp40] at hfr
    simp only [BoolRes, setRegF, reduceIte, Nat.reduceEqDiff, h_a0, h_a2, hfw.readLE _ _ ho1,
      hfw.readLE _ _ ho2] at hres
    janus64_run
    exact hres
  · have hl' : l1.toNat ≠ l2.toNat := fun h => hl (BitVec.eq_of_toNat_eq h)
    janus64_run
    simp [beq_false_of_ne hl]

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: `MemSatAmd64.memequalCode` (a byte loop) at `A0` behind a `JMP` at
`runtime.memequal`'s address, and `StrEq` comparing the 8-byte string `VAL` with itself. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MemSatAmd64

def cAddr : Nat := Extracted.program.contractAddr "runtime.memequal"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := memequalCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model (d : Nat) : MemAmd64.Memequal (Extracted.program.link implAt) cAddr d := by
  have hA : MemAmd64.Memequal (Extracted.program.link implAt) A0 d := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (memequal_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨⟨g1, g2, g3⟩, hcall, hgo⟩, i1, i2⟩ := hpre
  exact hA _ rfl ⟨⟨⟨g1, g2, g3⟩, hcall, hgo⟩, i1, i2⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def p : BitVec 64 := BitVec.ofNat 64 VAL
def l : BitVec 64 := 8#64

def s0 : State :=
  { regs := fun i => if i = 0 ∨ i = 1 then p else if i = 3 ∨ i = 7 then l
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [p, l, p, l] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : pre 64 p l p l s0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_⟩ <;>
    simp only [MemAmd64.callerWindow, outside_cons, outside_nil, and_true] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (d ret : Nat) (s : State) (p1 l1 p2 l2 : BitVec 64),
    MemAmd64.Memequal (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memequal") d ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [p1, l1, p2, l2] s ∧
    pre d p1 l1 p2 l2 s :=
  ⟨implAt, 64, ret, s0, p, l, p, l, model 64, hret, setup, hpre⟩

/-- So the guarantee is reached: a string equals itself. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness implAt 64 (model 64) p l p l ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, by rw [h.2]; simp⟩

end Witness

end Proof
