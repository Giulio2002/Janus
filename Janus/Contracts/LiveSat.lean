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
    {L : List (Nat × Nat)} {s : State} (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 2 * K) (hc : cost = K) (hr : round = K) (hb : K ≤ b)
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
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; simp only [HEND] at hendA; omega
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
    {L : List (Nat × Nat)} {s : State} (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 2 * K)
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
    {L : List (Nat × Nat)} {s : State} (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 2 * K)
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
    {L : List (Nat × Nat)} {s : State} (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 2 * K)
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
def wsp : Nat := 0x200000
def wg : Nat := 0x300000
def wret : Nat := 0x1000

def wbytes (a : Nat) : Byte :=
  if a = BUMP + 2 then 0x50 else if a = tyA then 16 else if a = tyB then 8 else if a = tyC then 16
  else if a = tyC + 8 then 8 else 0

/-- The witness memory: stack, `g`, the descriptors, the bump cell and buffer, the heap. -/
def wmem : Memory :=
  ⟨wbytes, [⟨wsp - 4096, 4096 + 64, true⟩, ⟨wg, 0x100, false⟩, ⟨tyA, 48, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, 0x10000, true⟩]⟩

def wstate (r : Nat → W64) : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else r i,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 A0, flags := ⟨false, false, false, false⟩,
    mem := wmem }

theorem tysOK0 : TysOK tys0 := by
  intro t ht
  simp only [tys0, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp [tyA, tyB, tyC, BUMP]

theorem wmem_inv (g : Nat) : toyInv tys0 0x8000 [] g (view (toyRt tys0) [] wmem) := by
  refine ⟨HEAP, by decide, Nat.le_refl _, by decide, by decide, fun r hr => absurd hr (by simp),
    fun i hi hi' => ?_, by decide, by decide, by decide, fun t ht => ?_⟩
  · rw [Memory.readLE_one]
    have : (view (toyRt tys0) [] wmem).bytes i = 0 := by
      simp only [view, wmem, wbytes]
      split
      · have e1 : i ≠ BUMP + 2 := by simp only [BUMP, HEAP, HEND] at *; omega
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

theorem newobject_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    NewobjectLiveContract (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      NewobjectPre 4096 s ∧ StackRoom s 4096 1 ∧
      LiveAt R A0 [(s.regs 0).toNat] L b (newobjectRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 1) ∧
      0 < typSize s.mem (s.regs 0).toNat := by
  have h0 : ((wstate fun i => if i = 0 then BitVec.ofNat 64 tyA else 0).regs 0).toNat = tyA := by
    simp [wstate]; decide
  refine ⟨at0 (bumpCode 16), toyR tys0 okNew, newobject16_impl tys0 tysOK0 okNew ?_, [], 0x8000,
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

theorem makeslice_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MakesliceLiveContract (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      MakeslicePre 4096 s ∧ StackRoom s 4096 3 ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (makesliceRound s)
        (s.regs 28).toNat s.mem (calleeStack s 4096 3) ∧
      0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat := by
  refine ⟨at0 (bumpCode 16), toyR tys0 okMake, makeslice16_impl tys0 tysOK0 okMake ?_, [], 0x8000,
    wst [tyB, 2, 2], rfl, ⟨wst_wcallOK _ 3 (by omega), ⟨by decide, by decide⟩, by decide, by decide, by decide⟩,
    wguard _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp,
      wwin _ 3 (by omega)⟩, by decide⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨(tyB, 8, 0), by simp [tys0], 2, 2, rfl, by decide⟩

def okMalloc : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [16, tyB, 1]

theorem mallocgc_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MallocgcLiveContract (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      MallocgcPre 4096 s ∧ StackRoom s 4096 3 ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b (mallocgcRound s)
        (s.regs 28).toNat s.mem (calleeStack s 4096 3) ∧
      0 < (s.regs 0).toNat := by
  refine ⟨at0 (bumpCode 16), toyR tys0 okMalloc, mallocgc16_impl tys0 tysOK0 okMalloc (K := 16) (by omega) (by omega) ?_, [], 0x8000,
    wst [16, tyB, 1], rfl, ⟨wst_wcallOK _ 3 (by omega), by decide, Or.inr ⟨⟨by decide, by decide⟩, fun h => by revert h; decide⟩⟩,
    wguard _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp,
      wwin _ 3 (by omega)⟩, by decide⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨16, tyB, 1, rfl, Or.inr ⟨(tyB, 8, 0), by simp [tys0], rfl, by decide, by decide⟩⟩

def okGrow : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [HEAP, 2, 0, 2, tyB]

theorem growslice_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    GrowsliceLiveContract (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      GrowslicePre 4096 s ∧ StackRoom s 4096 5 ∧
      LiveAt R A0 (growsliceArgs s) L b (growsliceRound s) (s.regs 28).toNat s.mem (calleeStack s 4096 5) := by
  refine ⟨growCode16 |> at0, toyR tys0 okGrow, growslice16_impl tys0 tysOK0 okGrow ?_, [], 0x8000,
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
    (mallocgc16_impl tys0 tysOK0 okMalloc (K := 16) (by omega) (by omega) ?_).smallNoScanSC, [], 0x8000,
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
    (mallocgc16_impl tys0 tysOK0 okScan (K := 16) (by omega) (by omega) ?_).smallScanNoHeaderSC, [], 0x8000,
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
    (mallocgc16_impl tys0 tysOK0 okTiny (K := 8) (by omega) (by omega) ?_).tinySize, [], 0x8000,
    wst [8, tyB, 1], rfl, ⟨⟨wst_wcallOK _ 3 (by omega), by decide, Or.inr ⟨⟨by decide, by decide⟩, fun h => by revert h; decide⟩⟩,
      wguard _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin _ 3 (by omega)⟩⟩, ?_⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨8, tyB, 1, rfl, Or.inr ⟨(tyB, 8, 0), by simp [tys0], rfl, by decide, by decide⟩⟩
  · unfold TinyArgs; refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end Janus.Contracts.LiveSat
