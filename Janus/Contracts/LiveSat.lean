import Janus.Contracts.LiveToy
import Janus.Contracts.AllocSat
import Janus.Contracts.IfaceModel
import Janus.Contracts.LiveCost

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

theorem bumpFinal_ret (s : State) (A : Nat) (p : Nat) (hp : s.mem.readLE BUMP 8 = p) :
    bumpFinal s A = retStateX s (bumpFinal s A).regs [BitVec.ofNat 64 p] s.flags s.vregs
      (s.mem.writeLE BUMP 8 (p + A)) s.excl s.exclPass := by
  subst hp
  have : (bumpFinal s A).regs = setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE BUMP 8))) 9
      (BitVec.ofNat 64 BUMP)) 10 (BitVec.ofNat 64 (s.mem.readLE BUMP 8) + BitVec.ofNat 64 A) := rfl
  rw [this]
  simp only [retStateX]; rw [callRegs_bump]; rfl

/-- What every bump-allocating contract returns: from the invariant. `fin` is the state the
code returns in (`hfin`: `retStateX` with results `res ptr`). -/
theorem bump_ret {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {K A stack nargs cost round b : Nat}
    {L : List (Nat × Nat)} {s : State} (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 64 * K) (hc : cost = K) (hr : round = K) (hb : K ≤ b)
    (hinv : (toyR tys ok).inv b L (s.regs 28).toNat (view (toyR tys ok).rt L s.mem))
    (hWs : LiveSep (calleeStack s stack nargs) (toyR tys ok).rt)
    (res : W64 → List W64) (fin : State)
    (hfin : ∀ p, s.mem.readLE BUMP 8 = p → fin = retStateX s fin.regs (res (BitVec.ofNat 64 p)) s.flags s.vregs
      (s.mem.writeLE BUMP 8 (p + A)) s.excl s.exclPass)
    {Q : Memory → Nat → Prop}
    (hQ : ∀ p, HEAP ≤ p → p % 16 = 0 → p + K ≤ HEND →
      ZeroBytes (s.mem.writeLE BUMP 8 (p + A)) p K →
      (s.mem.writeLE BUMP 8 (p + A)).accessible p K true = true → ApartAll p K L →
      Q (s.mem.writeLE BUMP 8 (p + A)) p) :
    LiveAllocRet (toyR tys ok) stack nargs res L b cost round s fin Q := by
  rw [hc, hr]
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  obtain ⟨p, hpm, h1, h2, hendA, hfr, hlf, hap, hz, hacc, hinv'⟩ := toy_alloc hty hA hKA hA2 hb hinvT
  have hp : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; simp only [HEND, HEAP, HSIZE] at hendA; omega
  refine ⟨BitVec.ofNat 64 p, fin.regs, s.flags, s.vregs, s.mem.writeLE BUMP 8 (p + A), s.excl, s.exclPass,
    hfin p hpm, ?_, hlf, ?_, ?_, ?_⟩
  · exact hfr.mono fun a n h => by simp only [outside_append] at h ⊢; exact h.1
  · simp only [hp]; exact hQ p h1 h2 (by omega) hz hacc hap
  · simp only [hp]; exact apart_win (inRanges_heap (by omega) (by omega : p + K ≤ HEND)) hWs
  · simp only [hp]; exact hinv'

/-- The bump pointer's cell is writable, from the invariant (for the run). -/
theorem bump_acc {tys : Tys} {ok : Nat → List Nat → Prop} {b : Nat} {L : List (Nat × Nat)} {g : Nat} {m : Memory}
    (h : (toyR tys ok).inv b L g (view (toyR tys ok).rt L m)) : m.accessible 4194304 8 true = true := by
  obtain ⟨p, -, -, -, -, -, -, -, h, -⟩ := h
  exact h

theorem finish_newobject {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr K A b : Nat}
    {L : List (Nat × Nat)} {s : State} (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 64 * K)
    (hok' : ∀ args, ok addr args → ∃ t ∈ tys, args = [t.1] ∧ blockSize t.2.1 (t.2.2 == 0) = K)
    (pre : NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem
        (calleeStack s 4096 1)) :
    LiveAllocRet (toyR tys ok) 4096 1 (fun ptr => [ptr]) L b (newobjectRound s) (newobjectRound s) s
      (bumpFinal s A) fun m ptr => 0 < typSize s.mem (s.regs 0).toNat →
        newobjectObj (toyR tys ok).rt s m ptr ∧ ApartAll ptr (newobjectRound s) L := by
  obtain ⟨-, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨t, ht, hargs, hbs⟩ := hok' _ hok
  have h0 : (s.regs 0).toNat = t.1 := by simpa using hargs
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  have hrd := toy_ty_read hty hinvT ht
  have hR : newobjectRound s = K := by
    simp only [newobjectRound, typSize, typNoscan, typPtrBytes, h0, hrd.1, hrd.2]; exact hbs
  rw [hR] at hcost ⊢
  refine bump_ret hty hA hKA hA2 rfl rfl hcost hinv hWs _ _ (fun p hp => bumpFinal_ret s A p hp) (fun p h1 h2 hend hz hacc hap _ => ⟨?_, hap⟩)
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
  exact finish_newobject hty (by omega) (by omega) (by omega) hok' pre


theorem finish_makeslice {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr K A b : Nat}
    {L : List (Nat × Nat)} {s : State} (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 64 * K)
    (hok' : ∀ args, ok addr args → ∃ t ∈ tys, ∃ l c, args = [t.1, l, c] ∧
      blockSize (t.2.1 * c) (t.2.2 == 0) = K)
    (pre : MakeslicePre 4096 s ∧ StackRoom s 4096 3 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
        (s.regs 28).toNat s.mem (calleeStack s 4096 3)) :
    LiveAllocRet (toyR tys ok) 4096 3 (fun ptr => [ptr]) L b (makesliceRound s) (makesliceRound s) s
      (bumpFinal s A) fun m ptr => 0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat →
        makesliceObj (toyR tys ok).rt s m ptr ∧ ApartAll ptr (makesliceRound s) L := by
  obtain ⟨-, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨t, ht, l, c, hargs, hbs⟩ := hok' _ hok
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨h0, -, h2⟩ := hargs
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  have hrd := toy_ty_read hty hinvT ht
  have hR : makesliceRound s = K := by
    simp only [makesliceRound, typSize, typNoscan, typPtrBytes, h0, h2, hrd.1, hrd.2]; exact hbs
  rw [hR] at hcost ⊢
  refine bump_ret hty hA hKA hA2 rfl rfl hcost hinv hWs _ _ (fun p hp => bumpFinal_ret s A p hp) (fun p h1 h2' hend hz hacc hap _ => ⟨?_, hap⟩)
  simp only [makesliceObj, typSize, typNoscan, typPtrBytes, h0, h2, hrd.1, hrd.2, hbs]
  exact toy_fresh h1 h2' hend hz hacc _ (hbs ▸ AllocSat.le_blockSize _ _) _ _

theorem finish_mallocgc {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr K A b : Nat}
    {L : List (Nat × Nat)} {s : State} (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 64 * K)
    (hok' : ∀ args, ok addr args → ∃ sz typ nz, args = [sz, typ, nz] ∧
      ((typ = 0 ∧ blockSize sz true = K) ∨ ∃ t ∈ tys, t.1 = typ ∧ typ ≠ 0 ∧ blockSize sz (t.2.2 == 0) = K))
    (pre : MallocgcPre 4096 s ∧ StackRoom s 4096 3 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
        (s.regs 28).toNat s.mem (calleeStack s 4096 3)) :
    LiveAllocRet (toyR tys ok) 4096 3 (fun ptr => [ptr]) L b (mallocgcRound s) (mallocgcRound s) s
      (bumpFinal s A) fun m ptr => 0 < (s.regs 0).toNat →
        mallocgcObj (toyR tys ok).rt s m ptr ∧ ApartAll ptr (mallocgcRound s) L := by
  obtain ⟨-, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨sz, typ, nz, hargs, hcase⟩ := hok' _ hok
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨h0, h1', -⟩ := hargs
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  -- the block and the object, for both kinds of request
  have key : mallocgcRound s = K ∧ (blockSize sz ((s.regs 1).toNat == 0 || typNoscan s.mem (s.regs 1).toNat)
      = K) := by
    rcases hcase with ⟨ht0, hbs⟩ | ⟨t, ht, ht1, hne, hbs⟩
    · have : (s.regs 1).toNat = 0 := by rw [h1', ht0]
      simp only [mallocgcRound, h0, this, beq_self_eq_true, Bool.true_or]; exact ⟨hbs, hbs⟩
    · have hrd := toy_ty_read hty hinvT ht
      have e1 : (s.regs 1).toNat = t.1 := by rw [h1', ht1]
      have e2 : typNoscan s.mem (s.regs 1).toNat = (t.2.2 == 0) := by
        simp only [typNoscan, typPtrBytes, e1, hrd.2]
      have e3 : ((s.regs 1).toNat == 0 || typNoscan s.mem (s.regs 1).toNat) = (t.2.2 == 0) := by
        rw [e2]
        have : (s.regs 1).toNat ≠ 0 := by rw [h1']; exact hne
        simp [this]
      simp only [mallocgcRound, h0, e3]; exact ⟨hbs, by rw [h0, e3] at *; exact hbs⟩
  obtain ⟨hR, hB⟩ := key
  rw [hR] at hcost ⊢
  refine bump_ret hty hA hKA hA2 rfl rfl hcost hinv hWs _ _ (fun p hp => bumpFinal_ret s A p hp)
    (fun p h1 h2' hend hz hacc hap _ => ⟨?_, hap⟩)
  simp only [mallocgcObj, mallocHdr, h0]
  rw [hB]
  exact toy_fresh h1 h2' hend hz hacc _ (hB ▸ h0 ▸ AllocSat.le_blockSize _ _) _ _

set_option maxRecDepth 20000 in
theorem makeslice16_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ t ∈ tys, ∃ l c, args = [t.1, l, c] ∧ blockSize (t.2.1 * c) (t.2.2 == 0) = 16) :
    MakesliceLiveContract (toy.link (at0 (bumpCode 16))) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩ := pre.1
  janus_run
  exact finish_makeslice hty (by omega) (by omega) (by omega) hok' pre


set_option maxRecDepth 20000 in
/-- The toy `mallocgc`: advances the bump pointer by 16 for a request of `K ∈ [8, 16]` bytes. -/
theorem mallocgc16_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) {K : Nat}
    (hK1 : 8 ≤ K) (hK2 : K ≤ 16)
    (hok' : ∀ args, ok A0 args → ∃ sz typ nz, args = [sz, typ, nz] ∧
      ((typ = 0 ∧ blockSize sz true = K) ∨ ∃ t ∈ tys, t.1 = typ ∧ typ ≠ 0 ∧ blockSize sz (t.2.2 == 0) = K)) :
    MallocgcLiveContract (toy.link (at0 (bumpCode 16))) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩ := pre.1
  janus_run
  exact finish_mallocgc (A := 16) hty (by omega) (by omega) (by omega) hok' pre

/-! ### `growslice` -/

/-- `bumpCode 16` with `MOVZ X2, #2` (the new capacity) before the return; `X1` is untouched. -/
def growCode16 : List Nat := [0xd2a00809, 0xf9400120, 0x9100000a + 16 * 1024, 0xf900012a, 0xd2800042, 0xd65f03c0]

def growFinal (s : State) : State :=
  { s with
    regs := setReg (setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE BUMP 8))) 2 2) 9
      (BitVec.ofNat 64 BUMP)) 10 (BitVec.ofNat 64 (s.mem.readLE BUMP 8) + BitVec.ofNat 64 16),
    pc := s.regs 30, mem := s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + 16) }

theorem growFinal_ret (s : State) (p : Nat) (hp : s.mem.readLE BUMP 8 = p) :
    growFinal s = retStateX s (growFinal s).regs [BitVec.ofNat 64 p, s.regs 1, 2] s.flags s.vregs
      (s.mem.writeLE BUMP 8 (p + 16)) s.excl s.exclPass := by
  subst hp
  simp only [growFinal, retStateX]
  congr 1
  funext i
  simp only [callRegs, setReg]
  by_cases h : i = 18 ∨ i = 28 ∨ i = 29
  · rw [if_pos h]; rcases h with rfl | rfl | rfl <;> simp
  · rw [if_neg h]
    rcases i with _ | _ | _ | i <;> simp [List.getD]

theorem finish_growslice {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr b : Nat}
    {L : List (Nat × Nat)} {s : State}
    (hok' : ∀ args, ok addr args → ∃ p et, args = [p, 2, 0, 2, et])
    (pre : GrowslicePre 4096 s ∧ StackRoom s 4096 5 ∧
      LiveAt (toyR tys ok) addr (growsliceArgs s) L b (growsliceRound s) (s.regs 28).toNat s.mem
        (calleeStack s 4096 5)) :
    LiveAllocRet (toyR tys ok) 4096 5
      (fun ptr => [ptr, s.regs 1, BitVec.ofNat 64 (growCap8 (s.regs 1).toNat (s.regs 2).toNat)])
      L b (growsliceRound s) (growsliceRound s) s (growFinal s) fun m ptr =>
        growsliceObj (toyR tys ok).rt s m ptr ∧ ApartAll ptr (growsliceRound s) L := by
  obtain ⟨-, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨p0, et, hargs⟩ := hok' _ hok
  simp only [growsliceArgs, List.cons.injEq, and_true] at hargs
  obtain ⟨-, h1, h2, h3, -⟩ := hargs
  have hg : growCap8 2 0 = 2 := by decide
  have hR : growsliceRound s = 16 := by simp only [growsliceRound, h1, h2, hg]
  rw [hR] at hcost ⊢
  refine bump_ret hty (A := 16) (by omega) (by omega) (by omega) rfl rfl hcost hinv hWs _ _ (fun p hp => ?_) (fun p h1' h2' hend hz hacc hap => ⟨?_, hap⟩)
  · have := growFinal_ret s p hp
    simp only [h1, h2, hg] at this ⊢
    exact this
  · simp only [growsliceObj, h1, h2, h3, hg]
    refine ⟨toy_fresh h1' h2' hend hz hacc _ (by omega) _ _, fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩

set_option maxRecDepth 20000 in
theorem growslice16_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ p et, args = [p, 2, 0, 2, et]) :
    GrowsliceLiveContract (toy.link (at0 growCode16)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _, _, _, _, _, _⟩, _⟩ := pre.1
  janus_run
  exact finish_growslice hty hok' pre

/-! ## The witness world -/

def tyA : Nat := 0x30000
def tyB : Nat := 0x30010
/-- The descriptors: 16 bytes without pointers, 8 bytes without pointers. -/
def tyC : Nat := 0x30020
/-- A 16-byte type with pointers (`PtrBytes = 8`). -/
def tys0 : Tys := [(tyA, 16, 0), (tyB, 8, 0), (tyC, 16, 8)]
/-- The caller's buffer (outside the runtime's ranges) for the copies. -/
def CB : Nat := 0x30000000
def wsp : Nat := 0x200000
def wg : Nat := 0x300000
def wret : Nat := 0x1000

def wbytes (a : Nat) : Byte :=
  if a = BUMP + 3 then 0x10 else if a = tyA then 16 else if a = tyB then 8 else if a = tyC then 16
  else if a = tyC + 8 then 8 else 0

/-- The witness memory: stack, `g`, the descriptors, the bump cell and buffer, the heap. -/
def wmem : Memory :=
  ⟨wbytes, [⟨wsp - 4096, 4096 + 64, true⟩, ⟨wg, 0x100, false⟩, ⟨tyA, 48, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩, ⟨CB, 0x200, true⟩]⟩

def wstate (r : Nat → W64) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else r i,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := wmem }

theorem tysOK0 : TysOK tys0 := by
  intro t ht
  simp only [tys0, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp [tyA, tyB, tyC, BUMP]

theorem wmem_inv (g : Nat) : toyInv tys0 0x400 [] g (view (toyRt tys0) [] wmem) := by
  refine ⟨HEAP, by decide, Nat.le_refl _, by decide, by decide, fun r hr => absurd hr (by simp),
    fun i hi hi' => ?_, by decide, by decide, by decide, fun t ht => ?_⟩
  · rw [Memory.readLE_one]
    have : (view (toyRt tys0) [] wmem).bytes i = 0 := by
      simp only [view, wmem, wbytes]
      split
      · have e1 : i ≠ BUMP + 3 := by simp only [BUMP, HEAP, HEND, HSIZE] at *; omega
        have e2 : i ≠ tyA := by simp only [tyA, HEAP, HEND] at *; omega
        have e3 : i ≠ tyB := by simp only [tyB, HEAP, HEND] at *; omega
        have e4 : i ≠ tyC := by simp only [tyC, HEAP, HEND] at *; omega
        have e5 : i ≠ tyC + 8 := by simp only [tyC, HEAP, HEND] at *; omega
        simp [e1, e2, e3, e4, e5]
      · rfl
    rw [this]; rfl
  · simp only [tys0, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩


theorem w28 (r : Nat → W64) : (wstate r).regs 28 = BitVec.ofNat 64 wg := by simp [wstate]
theorem w30 (r : Nat → W64) : (wstate r).regs 30 = BitVec.ofNat 64 wret := by simp [wstate]
theorem wsp_eq (r : Nat → W64) : (wstate r).sp = BitVec.ofNat 64 wsp := rfl
theorem wmem_eq (r : Nat → W64) : (wstate r).mem = wmem := rfl
theorem wspn : (BitVec.ofNat 64 wsp).toNat = wsp := by decide
theorem wgn : (BitVec.ofNat 64 wg).toNat = wg := by decide

theorem wcallOK (r : Nat → W64) (n : Nat) (hn : n ≤ 5) : CallOK (wstate r) 4096 n := by
  have hw : wmem.accessible (wsp - 4096) (4096 + 8 + 8 * 5) true = true := by decide
  simp only [CallOK, w30, wsp_eq, wmem_eq, wspn]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by simp [wsp]; omega, ?_⟩
  exact Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem wguard (r : Nat → W64) (n : Nat) (hn : n ≤ 5) : StackRoom (wstate r) 4096 n := by
  simp only [StackRoom, GuardOK, w28, wsp_eq, wmem_eq, wspn, wgn, calleeStack]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true, wsp, wg]
  omega

theorem wwin (r : Nat → W64) (n : Nat) (hn : n ≤ 5) :
    LiveSep (calleeStack (wstate r) 4096 n) (toyRt tys0) := by
  intro x hx
  simp only [calleeStack, wsp_eq, wspn, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;>
    simp only [toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, wsp, HEAP, HEND, BUMP, WBUF,
      tyA, tyB, tyC] <;> omega

theorem wTypeOK : TypeOK wmem tyA := ⟨by decide, by decide⟩

def okNew : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyA]

theorem newobjectLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    NewobjectLiveContract (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
      LiveAt R A0 [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 1) ∧
      0 < typSize s.mem (s.regs 0).toNat := by
  have h0 : ((wstate fun i => if i = 0 then BitVec.ofNat 64 tyA else 0).regs 0).toNat = tyA := by
    simp [wstate]; decide
  refine ⟨at0 (bumpCode 16), toyR tys0 okNew, newobject16_impl tys0 tysOK0 okNew ?_, [], 0x400,
    wstate (fun i => if i = 0 then BitVec.ofNat 64 tyA else 0), rfl,
    ⟨wcallOK _ 1 (by omega), by rw [h0, wmem_eq]; exact wTypeOK, by rw [h0, wmem_eq]; decide⟩,
    wguard _ 1 (by omega), ⟨by rw [h0]; exact ⟨rfl, rfl⟩, wmem_inv 0, by simp only [newobjectRound, h0, wmem_eq]; decide,
      by simp, wwin _ 1 (by omega)⟩, by rw [h0, wmem_eq]; decide⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨(tyA, 16, 0), by simp [tys0], rfl, by decide⟩


/-- The witness call state with argument words `l` in `X0, X1, …`. -/
def wst (l : List Nat) : State := wstate fun i => BitVec.ofNat 64 (l.getD i 0)

theorem wst_wcallOK (l : List Nat) (n : Nat) (hn : n ≤ 5) : CallOK (wst l) 4096 n := wcallOK _ n hn

def okMake : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyB, 2, 2]

theorem makesliceLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MakesliceLiveContract (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      MakeslicePre 4096 s ∧ StackRoom s 4096 3 ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
        (s.regs 28).toNat s.mem (calleeStack s 4096 3) ∧
      0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat := by
  refine ⟨at0 (bumpCode 16), toyR tys0 okMake, makeslice16_impl tys0 tysOK0 okMake ?_, [], 0x400,
    wst [tyB, 2, 2], rfl, ⟨wst_wcallOK _ 3 (by omega), ⟨by decide, by decide⟩, by decide, by decide, by decide⟩,
    wguard _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp,
      wwin _ 3 (by omega)⟩, by decide⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨(tyB, 8, 0), by simp [tys0], 2, 2, rfl, by decide⟩

def okMalloc : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [16, tyB, 1]

theorem mallocgcLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MallocgcLiveContract (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      MallocgcPre 4096 s ∧ StackRoom s 4096 3 ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
        (s.regs 28).toNat s.mem (calleeStack s 4096 3) ∧
      0 < (s.regs 0).toNat := by
  refine ⟨at0 (bumpCode 16), toyR tys0 okMalloc, mallocgc16_impl tys0 tysOK0 okMalloc (K := 16) (by omega) (by omega) ?_, [], 0x400,
    wst [16, tyB, 1], rfl, ⟨wst_wcallOK _ 3 (by omega), by decide, Or.inr ⟨⟨by decide, by decide⟩, fun h => by revert h; decide⟩⟩,
    wguard _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp,
      wwin _ 3 (by omega)⟩, by decide⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨16, tyB, 1, rfl, Or.inr ⟨(tyB, 8, 0), by simp [tys0], rfl, by decide, by decide⟩⟩

def okGrow : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [HEAP, 2, 0, 2, tyB]

theorem growsliceLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    GrowsliceLiveContract (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      GrowslicePre 4096 s ∧ StackRoom s 4096 5 ∧
      LiveAt R A0 (growsliceArgs s) L b (growsliceRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 5) := by
  refine ⟨growCode16 |> at0, toyR tys0 okGrow, growslice16_impl tys0 tysOK0 okGrow ?_, [], 0x400,
    wst [HEAP, 2, 0, 2, tyB], rfl, ⟨⟨wst_wcallOK _ 5 (by omega), ⟨by decide, by decide⟩, by decide, by decide,
      by decide, by decide, by decide, by decide⟩, fun h => absurd h (by decide)⟩,
    wguard _ 5 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp,
      wwin _ 5 (by omega)⟩⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨HEAP, tyB, rfl⟩


def okScan : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [16, tyC, 1]
def okTiny : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [8, tyB, 1]

theorem mallocgcSmallNoScanSCLive_satisfiable : ∃ (n : Nat) (impl : List Segment) (R : RtInv),
    MallocgcSmallNoScanSCLiveContract n (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (MallocgcPre 4096 s ∧ StackRoom s 4096 3 ∧
        LiveAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
          (s.regs 28).toNat s.mem (calleeStack s 4096 3)) ∧
      NoScanArgs n s.mem (s.regs 0).toNat (s.regs 1).toNat := by
  refine ⟨2, at0 (bumpCode 16), toyR tys0 okMalloc,
    (mallocgc16_impl tys0 tysOK0 okMalloc (K := 16) (by omega) (by omega) ?_).smallNoScanSC, [], 0x400,
    wst [16, tyB, 1], rfl, ⟨⟨wst_wcallOK _ 3 (by omega), by decide, Or.inr ⟨⟨by decide, by decide⟩, fun h => by revert h; decide⟩⟩,
      wguard _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin _ 3 (by omega)⟩⟩, ?_⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨16, tyB, 1, rfl, Or.inr ⟨(tyB, 8, 0), by simp [tys0], rfl, by decide, by decide⟩⟩
  · unfold NoScanArgs; refine ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem mallocgcSmallScanNoHeaderSCLive_satisfiable : ∃ (n : Nat) (impl : List Segment) (R : RtInv),
    MallocgcSmallScanNoHeaderSCLiveContract n (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (MallocgcPre 4096 s ∧ StackRoom s 4096 3 ∧
        LiveAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
          (s.regs 28).toNat s.mem (calleeStack s 4096 3)) ∧
      ScanArgs n s.mem (s.regs 0).toNat (s.regs 1).toNat := by
  refine ⟨2, at0 (bumpCode 16), toyR tys0 okScan,
    (mallocgc16_impl tys0 tysOK0 okScan (K := 16) (by omega) (by omega) ?_).smallScanNoHeaderSC, [], 0x400,
    wst [16, tyC, 1], rfl, ⟨⟨wst_wcallOK _ 3 (by omega), by decide, Or.inr ⟨⟨by decide, by decide⟩, fun h => by revert h; decide⟩⟩,
      wguard _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin _ 3 (by omega)⟩⟩, ?_⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨16, tyC, 1, rfl, Or.inr ⟨(tyC, 16, 8), by simp [tys0], rfl, by decide, by decide⟩⟩
  · unfold ScanArgs; refine ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem mallocgcTinySizeLive_satisfiable : ∃ (n : Nat) (impl : List Segment) (R : RtInv),
    MallocgcTinySizeLiveContract n (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (MallocgcPre 4096 s ∧ StackRoom s 4096 3 ∧
        LiveAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
          (s.regs 28).toNat s.mem (calleeStack s 4096 3)) ∧
      TinyArgs n s.mem (s.regs 0).toNat (s.regs 1).toNat := by
  refine ⟨8, at0 (bumpCode 16), toyR tys0 okTiny,
    (mallocgc16_impl tys0 tysOK0 okTiny (K := 8) (by omega) (by omega) ?_).tinySize, [], 0x400,
    wst [8, tyB, 1], rfl, ⟨⟨wst_wcallOK _ 3 (by omega), by decide, Or.inr ⟨⟨by decide, by decide⟩, fun h => by revert h; decide⟩⟩,
      wguard _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin _ 3 (by omega)⟩⟩, ?_⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨8, tyB, 1, rfl, Or.inr ⟨(tyB, 8, 0), by simp [tys0], rfl, by decide, by decide⟩⟩
  · unfold TinyArgs; refine ⟨by decide, by decide, by decide, by decide, by decide⟩


/-! ### The write barrier -/

/-- `X25 = WBUF; RET`. -/
def wbCode : List Nat := [0xd2a00819, 0x91040339, 0xd65f03c0]

/-- The state the toy barrier returns in. -/
def wbFinal (s : State) : State := { s with regs := setReg s.regs 25 4194560#64, pc := s.regs 30 }

theorem wb_post {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {n b : Nat} (hn : n ≤ 8)
    {L : List (Nat × Nat)} {s : State}
    (hinv : (toyR tys ok).inv b L (s.regs 28).toNat (view (toyR tys ok).rt L s.mem))
    (hWs : LiveSep [(s.sp.toNat - 4096, s.sp.toNat - 8)] (toyR tys ok).rt) :
    ∃ (buf : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
        (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      wbFinal s = wbRetX s junk buf f v m ex ep ∧
      MemFrame s.mem m ((toyR tys ok).rt ++ [(s.sp.toNat - 4096, s.sp.toNat - 8)]) ∧ LiveFrame s.mem m L [] ∧
      WbSlots (toyR tys ok).rt m buf.toNat n ∧ ApartAll buf.toNat (8 * n) L ∧
      ApartAll buf.toNat (8 * n) [(s.sp.toNat - 4096, s.sp.toNat - 8)] ∧
      InvSlots (toyR tys ok) b L (s.regs 28).toNat (toyR tys ok).rt m buf.toNat n := by
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  have hb : (4194560#64 : W64).toNat = WBUF := by decide
  have ⟨p, _, _, _, _, hL, _, _, _, hacW, _⟩ := hinvT
  refine ⟨4194560#64, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, MemFrame.refl _ _,
    LiveFrame.refl _ _ _, ?_, ?_, ?_, ?_⟩
  · simp only [wbFinal, wbRetX]
    congr 1
    funext i
    simp only [setReg, wbRegs]
    by_cases h : i = 25
    · simp [h]
    · simp [h]
  · rw [hb]
    refine ⟨inRanges_wbuf hn, by simp [WBUF]; omega, ?_, by decide⟩
    rw [← view_accessible (toyRt tys) L s.mem]
    exact Memory.accessible_mono _ hacW (Nat.le_refl _) (by omega)
  · rw [hb]
    intro r hr
    have := hL r hr
    show WBUF + 8 * n ≤ r.1 ∨ r.1 + (r.2 - r.1) ≤ WBUF
    simp only [WBUF, HEAP] at *; omega
  · rw [hb]; exact apart_win (inRanges_wbuf hn) hWs
  · rw [hb]
    intro v' hf
    exact toyInv.frame hty hn hinvT hf

set_option maxRecDepth 20000 in
theorem wb_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) (n : Nat) (hn : n ≤ 8)
    (hok' : ∀ args, ok A0 args → args = [n]) :
    WbLiveContract (toy.link (at0 wbCode)) A0 4096 (toyR tys ok) n := by
  rw [link_at0]
  intro L b s hpc pre
  have ⟨⟨h30a, h30b, _⟩, _⟩ := pre
  janus_run
  simpa only [wbFinal, wbRetX, apartAll_cons, apartAll_nil, and_true] using wb_post hty hn pre.2.2.1 pre.2.2.2.2


def okWb (n : Nat) : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [n]

theorem wbLive_satisfiable : ∃ (n : Nat) (impl : List Segment) (R : RtInv),
    WbLiveContract (toy.link impl) A0 4096 R n ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧ CallOK s 4096 0 ∧
      R.ok A0 [n] ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
      LiveSep L [(s.sp.toNat - 4096, s.sp.toNat - 8)] ∧ LiveSep [(s.sp.toNat - 4096, s.sp.toNat - 8)] R.rt := by
  refine ⟨2, at0 wbCode, toyR tys0 (okWb 2), wb_impl tys0 tysOK0 _ 2 (by omega) (fun _ h => h.2), [], 0x400,
    wst [], rfl, wst_wcallOK _ 0 (by omega), ⟨rfl, rfl⟩, wmem_inv 0, by simp, ?_⟩
  have := wwin (fun i => BitVec.ofNat 64 (([] : List Nat).getD i 0)) 0 (by omega)
  intro x hx
  apply this x
  simp only [List.mem_singleton] at hx
  simp only [calleeStack, wsp_eq, wspn, List.mem_cons, List.not_mem_nil, or_false]
  left; rw [hx]; rfl


/-! ### The `RtSpec` contracts: `slicebytetostringtmp` (allocates nothing) -/

theorem callRegs_self (old r : Nat → W64) (h : r 18 = old 18 ∧ r 28 = old 28 ∧ r 29 = old 29)
    (res : List W64) (hres : ∀ i, i < res.length → res.getD i 0 = r i) : callRegs old r res = r := by
  funext i
  simp only [callRegs]
  by_cases hi : i = 18 ∨ i = 28 ∨ i = 29
  · rw [if_pos hi]; rcases hi with rfl | rfl | rfl <;> simp [h.1, h.2.1, h.2.2]
  · rw [if_neg hi]
    by_cases hl : i < res.length
    · have e1 : res.getD i (r i) = res.getD i 0 := by simp [List.getD, List.getElem?_eq_getElem hl]
      rw [e1]; exact hres i hl
    · simp [List.getD, List.getElem?_eq_none (by omega : res.length ≤ i)]

def okRt : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [0, 0]

/-- A call that returns with nothing changed (`pc := X30`) meets `RtLivePost` when the spec's
postcondition holds of the unchanged memory and the call costs and adds nothing. -/
theorem rt_post_nochange {R : RtInv} {stack : Nat} {sp : RtSpec} {ls : LiveSpec} {L : List (Nat × Nat)} {b : Nat}
    {s : State} (hc : ls.cost (argWords s sp.nargs) s.mem = 0)
    (hf : ls.fresh (argWords s sp.nargs) s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat = [])
    (hk : ls.keep (argWords s sp.nargs) s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat = [])
    (hq : sp.post R.rt (argWords s sp.nargs) s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat s.mem)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)) :
    RtLivePost stack R sp ls L b s { s with pc := s.regs 30 } := by
  refine ⟨s.regs 0, s.regs 1, s.regs 2, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, MemFrame.refl _ _,
    hq, LiveFrame.refl _ _ _, ?_, ?_, ?_⟩
  · simp only [retStateX]
    congr 1
    rw [callRegs_self s.regs s.regs ⟨rfl, rfl, rfl⟩]
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases i with _ | _ | _ | i
    · rfl
    · rfl
    · rfl
    · omega
  · simp [hf, FreshFrom]
  · simp [liveAdds, hf, hk, LiveApart]
  · simp only [liveAdds, hf, hk, hc, List.append_nil, Nat.sub_zero]; exact hinv

set_option maxRecDepth 20000 in
theorem rt_impl (tys : Tys) (hty : TysOK tys) :
    RtLiveContract (toy.link (at0 [0xd65f03c0])) A0 4096 (toyR tys okRt) slicebytetostringtmpSpec
      slicebytetostringtmpLive := by
  rw [link_at0]
  intro L b s hpc pre
  have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
  obtain ⟨-, -, -, -, -, hok, hinv, -⟩ := pre
  janus_run
  have ha : argWords s 2 = [0, 0] := (hok.2 : argWords s 2 = [0, 0])
  refine rt_post_nochange rfl rfl rfl ?_ hinv
  have ha' := ha
  simp [argWords, wordsFrom] at ha'
  simp only [slicebytetostringtmpSpec, ha, ha'.1, ha'.2]
  simp [strBytes]


theorem rtLive_satisfiable : ∃ (impl : List Segment) (R : RtInv) (sp : RtSpec) (ls : LiveSpec),
    RtLiveContract (toy.link impl) A0 4096 R sp ls ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      RtLivePre 4096 R sp ls A0 L b s := by
  refine ⟨at0 [0xd65f03c0], toyR tys0 okRt, _, _, rt_impl tys0 tysOK0, [], 0x400, wst [0, 0], rfl,
    wst_wcallOK _ 2 (by omega), ⟨by decide, by decide⟩, ?_, by trivial, wguard _ 2 (by omega),
    ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin _ 2 (by omega)⟩⟩
  intro x hx
  simp [slicebytetostringtmpSpec, argWords, wordsFrom, wst, wstate] at hx
  subst hx
  simp [calleeStack, wsp_eq, wspn, wsp]


/-! ### Copies and clears -/

/-- A call that stores one word at `dst` (a live object or caller memory outside `R.rt`) and
otherwise only changes registers meets `LiveMemRet`. -/
theorem liveMemRet_store {R : RtInv} {d nargs b dst v : Nat} {L : List (Nat × Nat)} {s fin : State}
    {P : Memory → Prop} (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (hmem : fin.mem = s.mem.writeLE dst 8 v) (hdst : InRanges dst 8 L ∨ Outside dst 8 R.rt)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)) (hP : P (s.mem.writeLE dst 8 v)) :
    LiveMemRet R d nargs [(dst, dst + 8)] L b s fin P := by
  obtain ⟨junk, f, vr, m, ex, ep, hs⟩ := retStateX_intro (res := []) hpc hsp h18 h28 h29 hdz htp hfc hfs
    (fun i hi => absurd hi (by simp))
  have hm : m = s.mem.writeLE dst 8 v := by
    have := congrArg State.mem hs
    simp only [retStateX] at this
    rw [← hmem]; exact this.symm ▸ rfl
  refine ⟨junk, f, vr, m, ex, ep, hs, ?_, ⟨fun a n hin hout => ?_⟩, ?_, ?_⟩
  · rw [hm]
    refine MemFrame.of_writeLE s.mem v (r := (dst, dst + 8)) ?_ (Nat.le_refl _) (Nat.le_refl _)
    simp
  · rw [hm]
    have := MemFrame.outside_mem hout (r := (dst, dst + 8)) (by simp)
    exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  · rw [hm]
    rcases hdst with h | h
    · rw [view_writeLE_live h]; exact hinv
    · rw [view_writeLE_out h]; exact hinv
  · rw [hm]; exact hP


def memmoveCode : List Nat := [0xf9400023, 0xf9000003, 0xd65f03c0]
def memclrCode : List Nat := [0xf900001f, 0xd65f03c0]
def typedmemmoveCode : List Nat := [0xf9400043, 0xf9000023, 0xd65f03c0]
def typedmemclrCode : List Nat := [0xf900003f, 0xd65f03c0]

theorem zeroed_store (m : Memory) (a : Nat) : Mem.Zeroed (m.writeLE a 8 0) a 8 := by
  intro i hi
  rw [IfaceModel.bytes_writeLE_self m a 8 0 i hi]
  simp

set_option maxRecDepth 20000 in
theorem memmove8_impl (tys : Tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ d sr, args = [d, sr, 8]) :
    MemmoveLive (toy.link (at0 memmoveCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  obtain ⟨d0, s0, hargs⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have h8 : (s.regs 2).toNat = 8 := hargs.2.2
  rw [h8] at hs2 hd2
  rw [h8] at hd4
  janus_run
  rw [h8]
  refine liveMemRet_store rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd4 hLm.2.1 ?_
  intro i hi
  exact IfaceModel.bytes_writeLE_readLE _ _ _ _ _ hi

set_option maxRecDepth 20000 in
theorem memclr8_impl (tys : Tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ d, args = [d, 8]) :
    MemclrNoHeapPointersLive (toy.link (at0 memclrCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  obtain ⟨d0, hargs⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have h8 : (s.regs 1).toNat = 8 := hargs.2
  rw [h8] at hd2 hd4
  janus_run
  rw [h8]
  exact liveMemRet_store rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd4 hLm.2.1 (zeroed_store _ _)

set_option maxRecDepth 20000 in
theorem memclrHasPointers8_impl (tys : Tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ d, args = [d, 8]) :
    MemclrHasPointersLive (toy.link (at0 memclrCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, h0, h1, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  obtain ⟨d0, hargs⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have h8 : (s.regs 1).toNat = 8 := hargs.2
  rw [h8] at hd2 hd4
  janus_run
  rw [h8]
  exact liveMemRet_store rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd4 hLm.2.1 (zeroed_store _ _)

/-- The size of an 8-byte type among the descriptors, read from memory. -/
theorem typ8_size {tys : Tys} (hty : TysOK tys) {b : Nat} {L : List (Nat × Nat)} {g : Nat} {m : Memory}
    (hinv : toyInv tys b L g (view (toyRt tys) L m)) {t : Nat × Nat × Nat} (ht : t ∈ tys) (h8 : t.2.1 = 8) :
    typSize m t.1 = 8 := by
  have := (toy_ty_read hty hinv ht).1
  simpa [typSize, h8] using this

set_option maxRecDepth 20000 in
theorem typedmemmove8_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ t ∈ tys, ∃ d sr, args = [t.1, d, sr] ∧ t.2.1 = 8) :
    TypedMemmoveLive (toy.link (at0 typedmemmoveCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, hty0, hty1, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  obtain ⟨t, ht, d0, s0, hargs, ht8⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hLm.2.1
  have h8t : typSize s.mem (s.regs 0).toNat = 8 := by rw [hargs.1]; exact typ8_size hty hinvT ht ht8
  have h8 : s.mem.readLE (s.regs 0).toNat 8 = 8 := h8t
  rw [h8t] at hs2 hd2 hd4
  janus_run
  rw [h8]
  refine liveMemRet_store rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd4 hLm.2.1 ?_
  intro i hi
  exact IfaceModel.bytes_writeLE_readLE _ _ _ _ _ hi

set_option maxRecDepth 20000 in
theorem typedmemclr8_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ t ∈ tys, ∃ d, args = [t.1, d] ∧ t.2.1 = 8) :
    TypedMemclrLive (toy.link (at0 typedmemclrCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨h30a, h30b, _, _, _, _, _⟩, _⟩, hLm, hty0, hty1, ⟨hd1, hd2, hd3, hd4⟩⟩ := pre
  obtain ⟨t, ht, d0, hargs, ht8⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hLm.2.1
  have h8t : typSize s.mem (s.regs 0).toNat = 8 := by rw [hargs.1]; exact typ8_size hty hinvT ht ht8
  have h8 : s.mem.readLE (s.regs 0).toNat 8 = 8 := h8t
  rw [h8t] at hd2 hd4
  janus_run
  rw [h8]
  exact liveMemRet_store rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hd4 hLm.2.1 (zeroed_store _ _)


theorem cb_out_win (r : Nat → W64) (k : Nat) (hk : k ≤ 5) (a n : Nat) (h1 : CB ≤ a) :
    Outside a n (calleeStack (wstate r) 4096 k) := by
  simp only [calleeStack, wsp_eq, wspn, outside_cons, outside_nil, and_true]
  simp only [wsp, CB] at *
  omega

theorem cb_out_rt (a n : Nat) (h1 : CB ≤ a) : Outside a n (toyRt tys0) := by
  simp only [toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, HEAP, HEND, HSIZE, BUMP, WBUF,
    tyA, tyB, tyC, CB] at *
  omega

theorem wguardE (r : Nat → W64) (n : Nat) (hn : n ≤ 5) : Mem.EqPre 4096 n (wstate r) := by
  have h := wguard r n hn
  exact ⟨(guardOK_iff _ _).1 h.1, wcallOK r n hn, h.2⟩

def okMove : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [CB, CB + 0x100, 8]

theorem memmoveLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MemmoveLive (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      Mem.EqPre 4096 3 s ∧
      LiveMemAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3) ∧
      Mem.Input s 4096 3 (s.regs 1).toNat (s.regs 2).toNat ∧
      LiveDest R L s 4096 3 (s.regs 0).toNat (s.regs 2).toNat := by
  refine ⟨at0 memmoveCode, toyR tys0 okMove, memmove8_impl tys0 okMove ?_, [], 0x400, wst [CB, CB + 0x100, 8], rfl,
    wguardE _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by simp, wwin _ 3 (by omega)⟩,
    ⟨by decide, by decide, cb_out_win _ 3 (by omega) _ _ (by decide)⟩,
    ⟨by decide, by decide, cb_out_win _ 3 (by omega) _ _ (by decide), Or.inr (cb_out_rt _ _ (by decide))⟩⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨CB, CB + 0x100, rfl⟩


def okClr : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [CB, 8]

theorem memclrNoHeapPointersLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MemclrNoHeapPointersLive (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      Mem.EqPre 4096 2 s ∧
      LiveMemAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat] L b s (calleeStack s 4096 2) ∧
      LiveDest R L s 4096 2 (s.regs 0).toNat (s.regs 1).toNat := by
  refine ⟨at0 memclrCode, toyR tys0 okClr, memclr8_impl tys0 okClr ?_, [], 0x400, wst [CB, 8], rfl,
    wguardE _ 2 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by simp, wwin _ 2 (by omega)⟩,
    ⟨by decide, by decide, cb_out_win _ 2 (by omega) _ _ (by decide), Or.inr (cb_out_rt _ _ (by decide))⟩⟩
  rintro args ⟨-, rfl⟩
  exact ⟨CB, rfl⟩

theorem memclrHasPointersLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MemclrHasPointersLive (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      Mem.EqPre 4096 2 s ∧
      LiveMemAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat] L b s (calleeStack s 4096 2) ∧
      (s.regs 0).toNat % 8 = 0 ∧ (s.regs 1).toNat % 8 = 0 ∧
      LiveDest R L s 4096 2 (s.regs 0).toNat (s.regs 1).toNat := by
  refine ⟨at0 memclrCode, toyR tys0 okClr, memclrHasPointers8_impl tys0 okClr ?_, [], 0x400, wst [CB, 8], rfl,
    wguardE _ 2 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by simp, wwin _ 2 (by omega)⟩, by decide, by decide,
    ⟨by decide, by decide, cb_out_win _ 2 (by omega) _ _ (by decide), Or.inr (cb_out_rt _ _ (by decide))⟩⟩
  rintro args ⟨-, rfl⟩
  exact ⟨CB, rfl⟩

def okTMove : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyB, CB, CB + 0x100]
def okTClr : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyB, CB]

theorem typedMemmoveLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    TypedMemmoveLive (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      Mem.EqPre 4096 3 s ∧
      LiveMemAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3) ∧
      TypeOK s.mem (s.regs 0).toNat ∧ Outside (s.regs 0).toNat 16 (calleeStack s 4096 3) ∧
      Mem.Input s 4096 3 (s.regs 2).toNat (typSize s.mem (s.regs 0).toNat) ∧
      LiveDest R L s 4096 3 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat) := by
  refine ⟨at0 typedmemmoveCode, toyR tys0 okTMove, typedmemmove8_impl tys0 tysOK0 okTMove ?_, [], 0x400,
    wst [tyB, CB, CB + 0x100], rfl, wguardE _ 3 (by omega),
    ⟨⟨rfl, by decide⟩, wmem_inv 0, by simp, wwin _ 3 (by omega)⟩, ⟨by decide, by decide⟩, ?_,
    ⟨by decide, by decide, cb_out_win _ 3 (by omega) _ _ (by decide)⟩,
    ⟨by decide, by decide, cb_out_win _ 3 (by omega) _ _ (by decide), Or.inr (cb_out_rt _ _ (by decide))⟩⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨(tyB, 8, 0), by simp [tys0], CB, CB + 0x100, rfl, rfl⟩
  · simp only [calleeStack, wsp_eq, wspn, outside_cons, outside_nil, and_true, wst, wstate]
    simp only [wsp, tyB]; decide

theorem typedMemclrLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    TypedMemclrLive (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      Mem.EqPre 4096 2 s ∧
      LiveMemAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat] L b s (calleeStack s 4096 2) ∧
      TypeOK s.mem (s.regs 0).toNat ∧ Outside (s.regs 0).toNat 16 (calleeStack s 4096 2) ∧
      LiveDest R L s 4096 2 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat) := by
  refine ⟨at0 typedmemclrCode, toyR tys0 okTClr, typedmemclr8_impl tys0 tysOK0 okTClr ?_, [], 0x400,
    wst [tyB, CB], rfl, wguardE _ 2 (by omega),
    ⟨⟨rfl, by decide⟩, wmem_inv 0, by simp, wwin _ 2 (by omega)⟩, ⟨by decide, by decide⟩, ?_,
    ⟨by decide, by decide, cb_out_win _ 2 (by omega) _ _ (by decide), Or.inr (cb_out_rt _ _ (by decide))⟩⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨(tyB, 8, 0), by simp [tys0], CB, rfl, rfl⟩
  · simp only [calleeStack, wsp_eq, wspn, outside_cons, outside_nil, and_true, wst, wstate]
    simp only [wsp, tyB]; decide


/-! ### Dynamic sizes: the toy that reads the size from the type descriptor

For the examples, whose type descriptors are read-only data outside `rt`, the toy cannot know a
request's size from the invariant. It computes the advance `A = 64·size` from the request itself
(`size` the descriptor's `Size_`, times the capacity for `makeslice`): `K ≤ A ≤ 64·K` for the
block `K = blockSize size …` (and `A = K = 0` for size 0), which `toyInv`'s slack allows. -/

theorem blockSize_zero (b : Bool) : blockSize 0 b = 0 := by cases b <;> decide

theorem blockSize_le64 (X : Nat) (b : Bool) : blockSize X b ≤ 64 * X := by
  rcases Nat.eq_zero_or_pos X with rfl | h
  · simp [blockSize_zero]
  · have := blockSize_le X b; omega

theorem callRegs_final (old r : Nat → W64) (x0 : W64) (h18 : r 18 = old 18) (h28 : r 28 = old 28)
    (h29 : r 29 = old 29) (h0 : r 0 = x0) : callRegs old r [x0] = r := by
  apply callRegs_self old r ⟨h18, h28, h29⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  have : i = 0 := by omega
  subst this; simp [h0]

def newobjectCodeD : List Nat :=
  [0xd2a00809, 0xf9400001, 0xd2800802, 0x9b027c21, 0xf9400120, 0x8b01000a, 0xf900012a, 0xd65f03c0]

/-- The state `newobjectCodeD` returns in. -/
def newobjFinalD (s : State) : State :=
  { s with
    regs := setReg (setReg (setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE BUMP 8))) 1
      (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) * 64#64)) 2 64#64) 9 (BitVec.ofNat 64 BUMP)) 10
      (BitVec.ofNat 64 (s.mem.readLE BUMP 8) + BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) * 64#64),
    pc := s.regs 30,
    mem := s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + s.mem.readLE (s.regs 0).toNat 8 * 64 % 2 ^ 64) }

theorem newobjFinalD_ret (s : State) (p : Nat) (hp : s.mem.readLE BUMP 8 = p) :
    newobjFinalD s = retStateX s (newobjFinalD s).regs [BitVec.ofNat 64 p] s.flags s.vregs
      (s.mem.writeLE BUMP 8 (p + s.mem.readLE (s.regs 0).toNat 8 * 64 % 2 ^ 64)) s.excl s.exclPass := by
  subst hp
  simp only [retStateX]
  rw [callRegs_final s.regs _ (BitVec.ofNat 64 (s.mem.readLE BUMP 8)) (by simp [newobjFinalD, setReg])
    (by simp [newobjFinalD, setReg]) (by simp [newobjFinalD, setReg]) (by simp [newobjFinalD, setReg])]
  rfl

theorem finish_newobjectD {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr b : Nat}
    {L : List (Nat × Nat)} {s : State}
    (pre : NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem
        (calleeStack s 4096 1)) :
    LiveAllocRet (toyR tys ok) 4096 1 (fun ptr => [ptr]) L b (newobjectRound s) (newobjectRound s) s
      (newobjFinalD s) fun m ptr => 0 < typSize s.mem (s.regs 0).toNat →
        newobjectObj (toyR tys ok).rt s m ptr ∧ ApartAll ptr (newobjectRound s) L := by
  obtain ⟨⟨-, -, hmax⟩, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  simp only [typSize, maxAlloc] at hmax
  have hmod : s.mem.readLE (s.regs 0).toNat 8 * 64 % 2 ^ 64 = 64 * s.mem.readLE (s.regs 0).toNat 8 := by omega
  have hK : newobjectRound s ≤ 64 * s.mem.readLE (s.regs 0).toNat 8 := blockSize_le64 _ _
  have hKX : s.mem.readLE (s.regs 0).toNat 8 ≤ newobjectRound s := AllocSat.le_blockSize _ _
  refine bump_ret hty (A := 64 * s.mem.readLE (s.regs 0).toNat 8) (by omega) hK (by omega) rfl rfl hcost hinv hWs _ _
    (fun p hp => ?_) (fun p h1 h2' hend hz hacc hap _ => ⟨toy_fresh h1 h2' hend hz hacc _ hKX _ _, hap⟩)
  have := newobjFinalD_ret s p hp
  rw [hmod] at this
  exact this

set_option maxRecDepth 20000 in
theorem newobjectD_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    NewobjectLiveContract (toy.link (at0 newobjectCodeD)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  janus_run
  exact finish_newobjectD hty pre


def makesliceCodeD : List Nat :=
  [0xd2a00809, 0xf9400003, 0x9b027c63, 0xd2800804, 0x9b047c63, 0xf9400120, 0x8b03000a, 0xf900012a, 0xd65f03c0]
def mallocgcCodeD : List Nat :=
  [0xd2a00809, 0xd2800804, 0x9b047c03, 0xf9400120, 0x8b03000a, 0xf900012a, 0xd65f03c0]

def makesliceFinalD (s : State) : State :=
  { s with
    regs := setReg (setReg (setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE BUMP 8))) 3
      (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) * s.regs 2 * 64#64)) 4 64#64) 9 (BitVec.ofNat 64 BUMP)) 10
      (BitVec.ofNat 64 (s.mem.readLE BUMP 8) + BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) * s.regs 2 * 64#64),
    pc := s.regs 30,
    mem := s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 +
      s.mem.readLE (s.regs 0).toNat 8 * (s.regs 2).toNat * 64 % 2 ^ 64) }

theorem makesliceFinalD_ret (s : State) (p : Nat) (hp : s.mem.readLE BUMP 8 = p) :
    makesliceFinalD s = retStateX s (makesliceFinalD s).regs [BitVec.ofNat 64 p] s.flags s.vregs
      (s.mem.writeLE BUMP 8 (p + s.mem.readLE (s.regs 0).toNat 8 * (s.regs 2).toNat * 64 % 2 ^ 64))
      s.excl s.exclPass := by
  subst hp
  simp only [retStateX]
  rw [callRegs_final s.regs _ (BitVec.ofNat 64 (s.mem.readLE BUMP 8)) (by simp [makesliceFinalD, setReg])
    (by simp [makesliceFinalD, setReg]) (by simp [makesliceFinalD, setReg]) (by simp [makesliceFinalD, setReg])]
  rfl

theorem finish_makesliceD {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr b : Nat}
    {L : List (Nat × Nat)} {s : State}
    (pre : MakeslicePre 4096 s ∧ StackRoom s 4096 3 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
        (s.regs 28).toNat s.mem (calleeStack s 4096 3)) :
    LiveAllocRet (toyR tys ok) 4096 3 (fun ptr => [ptr]) L b (makesliceRound s) (makesliceRound s) s
      (makesliceFinalD s) fun m ptr => 0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat →
        makesliceObj (toyR tys ok).rt s m ptr ∧ ApartAll ptr (makesliceRound s) L := by
  obtain ⟨⟨-, -, -, -, hmax⟩, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  simp only [typSize, maxAlloc] at hmax
  have hmod : s.mem.readLE (s.regs 0).toNat 8 * (s.regs 2).toNat * 64 % 2 ^ 64 =
      64 * (s.mem.readLE (s.regs 0).toNat 8 * (s.regs 2).toNat) := by
    generalize s.mem.readLE (s.regs 0).toNat 8 * (s.regs 2).toNat = X at hmax ⊢
    omega
  have hK : makesliceRound s ≤ 64 * (s.mem.readLE (s.regs 0).toNat 8 * (s.regs 2).toNat) := blockSize_le64 _ _
  have hKX : s.mem.readLE (s.regs 0).toNat 8 * (s.regs 2).toNat ≤ makesliceRound s := AllocSat.le_blockSize _ _
  refine bump_ret hty (A := 64 * (s.mem.readLE (s.regs 0).toNat 8 * (s.regs 2).toNat)) (by omega) hK (by omega)
    rfl rfl hcost hinv hWs _ _
    (fun p hp => ?_) (fun p h1 h2' hend hz hacc hap _ => ⟨toy_fresh h1 h2' hend hz hacc _ hKX _ _, hap⟩)
  have := makesliceFinalD_ret s p hp
  rw [hmod] at this
  exact this

set_option maxRecDepth 20000 in
theorem makesliceD_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    MakesliceLiveContract (toy.link (at0 makesliceCodeD)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, hq1, hq2, hq3, hq4, hq5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  janus_run
  exact finish_makesliceD hty pre

def mallocgcFinalD (s : State) : State :=
  { s with
    regs := setReg (setReg (setReg (setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE BUMP 8))) 3
      (s.regs 0 * 64#64)) 4 64#64) 9 (BitVec.ofNat 64 BUMP)) 10
      (BitVec.ofNat 64 (s.mem.readLE BUMP 8) + s.regs 0 * 64#64),
    pc := s.regs 30,
    mem := s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + (s.regs 0).toNat * 64 % 2 ^ 64) }

theorem mallocgcFinalD_ret (s : State) (p : Nat) (hp : s.mem.readLE BUMP 8 = p) :
    mallocgcFinalD s = retStateX s (mallocgcFinalD s).regs [BitVec.ofNat 64 p] s.flags s.vregs
      (s.mem.writeLE BUMP 8 (p + (s.regs 0).toNat * 64 % 2 ^ 64)) s.excl s.exclPass := by
  subst hp
  simp only [retStateX]
  rw [callRegs_final s.regs _ (BitVec.ofNat 64 (s.mem.readLE BUMP 8)) (by simp [mallocgcFinalD, setReg])
    (by simp [mallocgcFinalD, setReg]) (by simp [mallocgcFinalD, setReg]) (by simp [mallocgcFinalD, setReg])]
  rfl

theorem finish_mallocgcD {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr b : Nat}
    {L : List (Nat × Nat)} {s : State}
    (pre : MallocgcPre 4096 s ∧ StackRoom s 4096 3 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
        (s.regs 28).toNat s.mem (calleeStack s 4096 3)) :
    LiveAllocRet (toyR tys ok) 4096 3 (fun ptr => [ptr]) L b (mallocgcRound s) (mallocgcRound s) s
      (mallocgcFinalD s) fun m ptr => 0 < (s.regs 0).toNat →
        mallocgcObj (toyR tys ok).rt s m ptr ∧ ApartAll ptr (mallocgcRound s) L := by
  obtain ⟨⟨-, hmax, -⟩, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  simp only [maxAlloc] at hmax
  have hmod : (s.regs 0).toNat * 64 % 2 ^ 64 = 64 * (s.regs 0).toNat := by omega
  have hK : mallocgcRound s ≤ 64 * (s.regs 0).toNat := blockSize_le64 _ _
  have hKX : (s.regs 0).toNat ≤ mallocgcRound s := AllocSat.le_blockSize _ _
  refine bump_ret hty (A := 64 * (s.regs 0).toNat) (by omega) hK (by omega) rfl rfl hcost hinv hWs _ _
    (fun p hp => ?_) (fun p h1 h2' hend hz hacc hap _ => ⟨toy_fresh h1 h2' hend hz hacc _ hKX _ _, hap⟩)
  have := mallocgcFinalD_ret s p hp
  rw [hmod] at this
  exact this

set_option maxRecDepth 20000 in
theorem mallocgcD_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    MallocgcLiveContract (toy.link (at0 mallocgcCodeD)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩ := pre.1
  janus_run
  exact finish_mallocgcD hty pre

end Janus.Contracts.LiveSat
