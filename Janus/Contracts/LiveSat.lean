import Janus.Contracts.LiveToy
import Janus.Contracts.AllocSat

namespace Janus.Contracts.LiveSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy
open Janus.Contracts.AllocSat (toy A0 at0 link_at0)

def bumpCode (K : Nat) : List Nat := [0xd2a00809, 0xf9400120, 0x9100000a + K * 1024, 0xf900012a, 0xd65f03c0]

theorem callRegs_bump (old : Nat → W64) (x0 x9 x10 : W64) :
    callRegs old (setReg (setReg (setReg old 0 x0) 9 x9) 10 x10) [x0] =
      setReg (setReg (setReg old 0 x0) 9 x9) 10 x10 := by
  funext i
  simp only [callRegs, setReg]
  by_cases h : i = 18 ∨ i = 28 ∨ i = 29
  · rw [if_pos h]; rcases h with rfl | rfl | rfl <;> simp
  · rw [if_neg h]
    rcases i with _ | i
    · simp
    · simp [List.getD_cons_succ]

/-- The state the toy allocator `bumpCode K` returns in: `X0 = p`, `X9 = BUMP`, `X10 = p + K`, the
bump pointer advanced. -/
def bumpFinal (s : State) (K : Nat) : State :=
  { s with
    regs := setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE BUMP 8))) 9 (BitVec.ofNat 64 BUMP)) 10
      (BitVec.ofNat 64 (s.mem.readLE BUMP 8) + BitVec.ofNat 64 K),
    pc := s.regs 30, mem := s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + K) }

/-- What every bump-allocating contract returns (one result register): from the invariant. -/
theorem bump_ret {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {K stack nargs cost round b : Nat}
    {L : List (Nat × Nat)} {s : State} (hK : K % 16 = 0) (hc : cost = K) (hr : round = K) (hb : K ≤ b)
    (hinv : (toyR tys ok).inv b L (s.regs 28).toNat (view (toyR tys ok).rt L s.mem))
    (hWs : LiveSep (calleeStack s stack nargs) (toyR tys ok).rt)
    {Q : Memory → Nat → Prop}
    (hQ : ∀ p, HEAP ≤ p → p % 16 = 0 → p + K ≤ HEND →
      ZeroBytes (s.mem.writeLE BUMP 8 (p + K)) p K →
      (s.mem.writeLE BUMP 8 (p + K)).accessible p K true = true → ApartAll p K L →
      Q (s.mem.writeLE BUMP 8 (p + K)) p) :
    LiveAllocRet (toyR tys ok) stack nargs (fun ptr => [ptr]) L b cost round s (bumpFinal s K) Q := by
  rw [hc, hr]
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  obtain ⟨p, hpm, h1, h2, hend, hfr, hlf, hap, hz, hacc, hinv'⟩ := toy_alloc hty hK hb hinvT
  have hp : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; simp only [HEND] at hend; omega
  have e : bumpFinal s K = { s with
      regs := setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 p)) 9 (BitVec.ofNat 64 BUMP)) 10
        (BitVec.ofNat 64 p + BitVec.ofNat 64 K),
      pc := s.regs 30, mem := s.mem.writeLE BUMP 8 (p + K) } := by
    simp only [bumpFinal, hpm]
  refine ⟨BitVec.ofNat 64 p, setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 p)) 9 (BitVec.ofNat 64 BUMP)) 10
      (BitVec.ofNat 64 p + BitVec.ofNat 64 K), s.flags, s.vregs, s.mem.writeLE BUMP 8 (p + K), s.excl, s.exclPass,
    ?_, ?_, hlf, ?_, ?_, ?_⟩
  · rw [e]; simp only [retStateX]; rw [callRegs_bump]
  · exact hfr.mono fun a n h => by simp only [outside_append] at h ⊢; exact h.1
  · simp only [hp]; exact hQ p h1 h2 hend hz hacc hap
  · simp only [hp]; exact apart_win (inRanges_heap (by omega) hend) hWs
  · simp only [hp]; exact hinv'

/-- The bump pointer's cell is writable, from the invariant (for the run). -/
theorem bump_acc {tys : Tys} {ok : Nat → List Nat → Prop} {b : Nat} {L : List (Nat × Nat)} {g : Nat} {m : Memory}
    (h : (toyR tys ok).inv b L g (view (toyR tys ok).rt L m)) : m.accessible 4194304 8 true = true := by
  obtain ⟨p, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem finish_newobject {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr K b : Nat}
    {L : List (Nat × Nat)} {s : State} (hK : K % 16 = 0)
    (hok' : ∀ args, ok addr args → ∃ t ∈ tys, args = [t.1] ∧ blockSize t.2.1 (t.2.2 == 0) = K)
    (pre : NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem
        (calleeStack s 4096 1)) :
    LiveAllocRet (toyR tys ok) 4096 1 (fun ptr => [ptr]) L b (newobjectRound s) (newobjectRound s) s
      (bumpFinal s K) fun m ptr => 0 < typSize s.mem (s.regs 0).toNat →
        newobjectObj (toyR tys ok).rt s m ptr ∧ ApartAll ptr (newobjectRound s) L := by
  obtain ⟨-, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨t, ht, hargs, hbs⟩ := hok' _ hok
  have h0 : (s.regs 0).toNat = t.1 := by simpa using hargs
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  have hrd := toy_ty_read hty hinvT ht
  have hR : newobjectRound s = K := by
    simp only [newobjectRound, typSize, typNoscan, typPtrBytes, h0, hrd.1, hrd.2]; exact hbs
  rw [hR] at hcost ⊢
  refine bump_ret hty hK rfl rfl hcost hinv hWs (fun p h1 h2 hend hz hacc hap _ => ⟨?_, hap⟩)
  simp only [newobjectObj, typSize, typNoscan, typPtrBytes, h0, hrd.1, hrd.2, hbs]
  exact toy_fresh h1 h2 hend hz hacc _ (hbs ▸ AllocSat.le_blockSize _ _) _ _

set_option maxRecDepth 20000 in
theorem newobject16_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ t ∈ tys, args = [t.1] ∧ blockSize t.2.1 (t.2.2 == 0) = 16) :
    NewobjectLiveContract (toy.link (at0 (bumpCode 16))) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩ := pre.1
  janus_run
  exact finish_newobject hty (by omega) hok' pre

end Janus.Contracts.LiveSat
