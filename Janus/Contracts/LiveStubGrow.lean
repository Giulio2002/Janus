import Janus.Contracts.LiveStubSlice

/-!
# `runtime.growslice` live, at a program's own address (arm64)

`RtLiveContract linked addr 4096 (toyR tys ok) growsliceSpec growsliceLive`, for any element size
(including 1): the stub (`growsliceSeg addr ob A cap`) loads the `ob = oldLen · size` old bytes,
takes `A` bytes from the bump allocator, stores the old bytes at the new array and returns
`(array, newLen, cap)`. The numbers are fixed by the request, which the runtime's `ok` predicate
pins to `args = [oldPtr, n, c0, num, et]`, `et` a type descriptor of `tys` (so its `Size_` and
`PtrBytes` are known to the runtime: the descriptor is one of the runtime's ranges):

* `K = roundupsize (nextslicecap n c0 · size) noscan` (the call's cost) and `cap = growCap …`,
* `cap · size = K` (always when `size ∣ K`: size 1 and powers of two),
* `ob = (n - num) · size`, at most 11 chunks (`chunkList ob`), `A` a multiple of 16, `K ≤ A ≤ 64 K`.

All side conditions are closed numerals: the tactic proves them by `decide`.

```lean
theorem hg : RtLiveContract linked a 4096 (toyR tys ok) growsliceSpec growsliceLive := by
  janus_live_growslice (0x30000, 1, 0) 0 16 8 hok
```
-/

namespace Janus.Contracts.LiveStub

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

/-- `TysOK` of a literal list of descriptors is decided by evaluation. -/
instance instDecidableTysOK (tys : Tys) : Decidable (TysOK tys) := by
  unfold TysOK; infer_instance

/-- The registers the copy uses: `X3…X8, X11…X15`. -/
def growReg (j : Nat) : Nat := if j < 6 then j + 3 else j + 5

def growCodeN (ob A cap : Nat) : List Nat :=
  (chunkList ob).mapIdx (fun j c => ldrW c.2 c.1 0 (growReg j)) ++
  [0xd2a00809, 0xf9400120, 0x9100000a + A * 1024, 0xf900012a] ++
  (chunkList ob).mapIdx (fun j c => strW c.2 c.1 0 (growReg j)) ++
  [0xd2800002 + cap * 32, 0xd65f03c0]

def growsliceSeg (addr ob A cap : Nat) : Segment := ⟨"live-stub.growslice", addr, growCodeN ob A cap⟩

theorem outside_toyRt_heap_bump {tys : Tys} {a k : Nat} (h : Outside a k (toyRt tys)) :
    (a + k ≤ HEAP ∨ HEND ≤ a) ∧ (a + k ≤ BUMP ∨ BUMP + 8 ≤ a) := by
  simp only [toyRt, outside_append, outside_cons, outside_nil, and_true] at h
  exact ⟨h.1.1, h.1.2.1⟩

/-- The heap at the bump pointer is writable for as much as the budget allows. -/
theorem toy_heap_acc {tys : Tys} {b g ob : Nat} {m : Memory}
    {L' : List (Nat × Nat)} (h : toyInv tys b L' g (view (toyRt tys) L' m)) (hob : ob ≤ b) :
    m.accessible (m.readLE BUMP 8) ob true = true := by
  obtain ⟨p, hp, hH, h16, hbud, hL, hzero, hac, hacB, hacW, hty0⟩ := h
  have hpm : m.readLE BUMP 8 = p := by
    rw [← readLE_view (rt := toyRt tys) (L := L') (inRanges_bump tys) (outside_live hL (by simp [BUMP, HEAP]))]
    exact hp
  rw [hpm, ← view_accessible (toyRt tys) L' m]
  exact Memory.accessible_mono _ hac hH (by simp only [HEND, HEAP, HSIZE] at *; omega)

/-- The bump pointer plus the copied bytes does not wrap the address space (the stores of later
chunks address `p + 8`, ...). -/
theorem toy_heap_bound {tys : Tys} {b g ob : Nat} {m : Memory}
    {L' : List (Nat × Nat)} (h : toyInv tys b L' g (view (toyRt tys) L' m)) (hob : ob ≤ b) :
    m.readLE BUMP 8 + ob ≤ 2 ^ 48 := by
  obtain ⟨p, hp, hH, h16, hbud, hL, hzero, hac, hacB, hacW, hty0⟩ := h
  have hpm : m.readLE BUMP 8 = p := by
    rw [← readLE_view (rt := toyRt tys) (L := L') (inRanges_bump tys) (outside_live hL (by simp [BUMP, HEAP]))]
    exact hp
  rw [hpm]; simp only [HEND, HEAP, HSIZE] at *; omega

/-- What the request pins: the arguments, and the call's cost. -/
theorem growslice_unpack {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {t : Nat × Nat × Nat} (ht : t ∈ tys) {n c0 num K : Nat}
    (hok' : ∀ args, ok addr args → ∃ p, args = [p, n, c0, num, t.1])
    (hK : roundupsize (nextslicecap n c0 * t.2.1) (t.2.2 == 0) = K)
    {L : List (Nat × Nat)} {b : Nat} {s : State}
    (pre : RtLivePre 4096 (toyR tys ok) growsliceSpec growsliceLive addr L b s) :
    ∃ oldp, (s.regs 0).toNat = oldp ∧ (s.regs 1).toNat = n ∧
      argWords s growsliceSpec.nargs = [oldp, n, c0, num, t.1] ∧
      growsliceLive.cost (argWords s growsliceSpec.nargs) s.mem = K ∧ K ≤ b ∧
      s.mem.accessible BUMP 8 true = true ∧ typSize s.mem t.1 = t.2.1 := by
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨oldp, hargs⟩ := hok' _ hok
  have hargs0 : (s.regs 0).toNat = oldp := by
    have := congrArg (fun l => l.getD 0 0) hargs
    simpa [argWords, wordsFrom, growsliceSpec] using this
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  have hrd := toy_ty_read hty hinvT ht
  have hargs4 : (s.regs 4).toNat = t.1 := by
    have := congrArg (fun l => l.getD 4 0) hargs
    simpa [argWords, wordsFrom, growsliceSpec] using this
  have hargs1 : (s.regs 1).toNat = n := by
    have := congrArg (fun l => l.getD 1 0) hargs
    simpa [argWords, wordsFrom, growsliceSpec] using this
  have hargs2 : (s.regs 2).toNat = c0 := by
    have := congrArg (fun l => l.getD 2 0) hargs
    simpa [argWords, wordsFrom, growsliceSpec] using this
  have hsz : typSize s.mem (s.regs 4).toNat = t.2.1 := by
    simp only [typSize, hargs4]; exact hrd.1
  have hnoscan : typNoscan s.mem (s.regs 4).toNat = (t.2.2 == 0) := by
    simp only [typNoscan, typPtrBytes, hargs4, hrd.2]
  have hcostK : growsliceLive.cost (argWords s growsliceSpec.nargs) s.mem = K := by
    simp only [growsliceLive, arg, argWords, wordsFrom, growsliceSpec]
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.getD_nil, hsz, hnoscan, hargs1, hargs2]
    exact hK
  refine ⟨oldp, hargs0, hargs1, hargs, hcostK, ?_, LiveSat.bump_acc hinv, hrd.1⟩
  rw [hcostK] at hcost; exact hcost

/-- The old elements are readable. -/
theorem growslice_read {tys : Tys} {ok : Nat → List Nat → Prop} {addr : Nat}
    {t : Nat × Nat × Nat} {n c0 num ob oldp : Nat} {L : List (Nat × Nat)} {b : Nat} {s : State}
    (pre : RtLivePre 4096 (toyR tys ok) growsliceSpec growsliceLive addr L b s)
    (hq0 : (s.regs 0).toNat = oldp) (hargs : argWords s growsliceSpec.nargs = [oldp, n, c0, num, t.1])
    (hsz : typSize s.mem t.1 = t.2.1) (hob : (n - num) * t.2.1 = ob) :
    0 < ob → s.mem.accessible (s.regs 0).toNat ob false = true := by
  obtain ⟨hcall, hspec, -⟩ := pre
  obtain ⟨-, -, -, -, -, -, hacc⟩ := hspec
  simp only [hargs, arg, List.getD_cons_succ, List.getD_cons_zero, hsz, hob] at hacc
  rw [hq0]; exact hacc

/-- The old array does not wrap the address space: `p + ob ≤ 2^48`, the first component of
`Readable m p ob` in `growsliceSpec.pre` (the stepper needs it for the address of every later chunk). -/
theorem growslice_bound {tys : Tys} {ok : Nat → List Nat → Prop} {addr : Nat}
    {t : Nat × Nat × Nat} {n c0 num ob oldp : Nat} {L : List (Nat × Nat)} {b : Nat} {s : State}
    (pre : RtLivePre 4096 (toyR tys ok) growsliceSpec growsliceLive addr L b s)
    (hq0 : (s.regs 0).toNat = oldp) (hargs : argWords s growsliceSpec.nargs = [oldp, n, c0, num, t.1])
    (hsz : typSize s.mem t.1 = t.2.1) (hob : (n - num) * t.2.1 = ob) :
    (s.regs 0).toNat + ob ≤ 2 ^ 48 := by
  obtain ⟨hcall, hspec, -⟩ := pre
  obtain ⟨-, -, -, -, -, hrd, -⟩ := hspec
  simp only [hargs, arg, List.getD_cons_succ, List.getD_cons_zero, hsz, hob] at hrd
  rw [hq0]; exact hrd

set_option maxHeartbeats 1000000 in
/-- The return of the `growslice` stub meets the live contract. -/
theorem growslice_finish {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {t : Nat × Nat × Nat} (ht : t ∈ tys) {n c0 num ob A cap K : Nat}
    (hok' : ∀ args, ok addr args → ∃ p, args = [p, n, c0, num, t.1])
    (hK : roundupsize (nextslicecap n c0 * t.2.1) (t.2.2 == 0) = K)
    (hcap : growCap t.2.1 (t.2.2 == 0) n c0 = cap) (hCK : cap * t.2.1 = K) (hKpos : 0 < K)
    (hob : (n - num) * t.2.1 = ob) (hobK : ob ≤ K) (hA1 : K ≤ A) (hA2 : A ≤ 64 * K) (hA3 : A % 16 = 0)
    (hcap16 : cap < 65536)
    {L : List (Nat × Nat)} {b : Nat} {s fin : State}
    (pre : RtLivePre 4096 (toyR tys ok) growsliceSpec growsliceLive addr L b s)
    (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8)) (h1 : fin.regs 1 = s.regs 1)
    (h2 : fin.regs 2 = BitVec.ofNat 64 cap)
    (hmem : fin.mem = applyWrites (s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + A))
      (copyWrites s.mem (s.mem.readLE BUMP 8) (s.regs 0).toNat ob)) :
    RtLivePost 4096 (toyR tys ok) growsliceSpec growsliceLive L b s fin := by
  obtain ⟨oldp, hargs0, hargs1, hargs, hcostK, hcost, -, -⟩ := growslice_unpack hty ht hok' hK pre
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, -, hLs, hWs⟩ := pre
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  have hrd := toy_ty_read hty hinvT ht
  obtain ⟨p0, hbump0, hH0, h16, hbud, hL, hzero, hacH, hacB, hacW, hty0⟩ := hinvT
  have hinvT' : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) :=
    ⟨p0, hbump0, hH0, h16, hbud, hL, hzero, hacH, hacB, hacW, hty0⟩
  obtain ⟨p, hpm, hp1, hp2, hend, hfr, hlf, hap, hz, hacc, hinv'⟩ :=
    toy_alloc hty hA3 hA1 hA2 hcost hinvT'
  have hp64 : p + A < 2 ^ 64 := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hpn : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hcapn : (BitVec.ofNat 64 cap).toNat = cap := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hpm, hargs0] at hmem
  rw [hpm] at h0
  generalize hm1 : s.mem.writeLE BUMP 8 (p + A) = m1 at hlf hz hacc hinv' hmem
  generalize hws_def : copyWrites s.mem p oldp ob = ws at hmem
  have hws : ∀ w ∈ ws, p ≤ w.1 ∧ w.1 + w.2.1 ≤ p + ob := by
    rw [← hws_def]; exact copyWrites_sub _ _ _ _
  have hbytes : ∀ x, (x < p ∨ p + ob ≤ x) → (applyWrites m1 ws).bytes x = m1.bytes x := fun x hx =>
    bytes_applyWrites_untouched ws (fun w hw => by have := hws w hw; omega) m1
  have hbump : ∀ x, (x < BUMP ∨ BUMP + 8 ≤ x) → m1.bytes x = s.mem.bytes x := fun x hx =>
    by rw [← hm1]; exact Memory.bytes_writeLE_outside _ (by omega)
  have hpHE : p + K ≤ HEND := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hH : HEAP ≤ p := hp1
  have hBH : BUMP + 8 ≤ HEAP := by simp [BUMP, HEAP]
  have hargsW : argWords s growsliceSpec.nargs = [oldp, n, c0, num, t.1] := hargs
  have hargsW5 : argWords s 5 = [oldp, n, c0, num, t.1] := hargs
  have hsz' : typSize s.mem t.1 = t.2.1 := hrd.1
  have hrange : range0 p K = [(p, p + K)] := by
    unfold range0; rw [if_neg (by omega)]
  have hfresh_eq : growsliceLive.fresh (argWords s growsliceSpec.nargs) s.mem (BitVec.ofNat 64 p).toNat
      (s.regs 1).toNat (BitVec.ofNat 64 cap).toNat = [(p, p + K)] := by
    simp only [growsliceLive, hargsW, hpn, hcapn, arg, List.getD_cons_succ, List.getD_cons_zero, hsz', hCK]
    exact hrange
  have hadds_eq : liveAdds growsliceLive (argWords s growsliceSpec.nargs) s.mem (BitVec.ofNat 64 p).toNat
      (s.regs 1).toNat (BitVec.ofNat 64 cap).toNat = [(p, p + K)] := by
    simp only [liveAdds, hfresh_eq]
    rfl
  refine ⟨BitVec.ofNat 64 p, s.regs 1, BitVec.ofNat 64 cap, fin.regs, fin.flags, fin.vregs, fin.mem, fin.excl,
    fin.exclPass, retStateX_eq hpc hsp h18 h28 h29 hdz htp hfc hfs ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases i with _ | _ | _ | i
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · omega
  · -- the frame
    refine ⟨fun a k hout => ?_, fun a k w => ?_⟩
    · have hrt : Outside a k (toyRt tys) := by
        have h := hout
        simp only [outside_append] at h
        exact h.1.1
      have hHB := outside_toyRt_heap_bump hrt
      rw [hmem]
      refine Memory.readLE_congr (fun i hi => ?_)
      rw [hbytes (a + i) (by omega), hbump (a + i) (by omega)]
    · rw [hmem, accessible_applyWrites, ← hm1, Memory.accessible_writeLE]
  · -- the postcondition of the spec
    have hns' : typNoscan s.mem t.1 = (t.2.2 == 0) := by simp only [typNoscan, typPtrBytes, hrd.2]
    have hobn : ob ≤ n * t.2.1 := by rw [← hob]; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    simp only [growsliceSpec]
    refine ⟨?_, ?_, ?_⟩
    · simp only [hargsW5, arg, List.getD_cons_succ, List.getD_cons_zero]
      exact hargs1
    · simp only [hargsW5, hcapn, arg, List.getD_cons_succ, List.getD_cons_zero, hsz', hns']
      exact hcap.symm
    simp only [hargsW5, hpn, hcapn, arg, List.getD_cons_succ, List.getD_cons_zero, hsz', hns']
    unfold GrownArray
    rw [hCK, hob]
    refine ⟨inRanges_heap hH (by omega), by simp only [HEND, HEAP, HSIZE] at hpHE ⊢; omega, ?_, ?_, ?_, ?_⟩
    · rw [hmem, accessible_applyWrites]; exact hacc
    · intro i hi
      rw [hmem, ← hws_def]
      exact copied_copyWrites s.mem m1 p oldp ob i hi
    · intro i hi
      rw [hmem, show p + n * t.2.1 + i = p + (n * t.2.1 + i) by omega, hbytes _ (by omega)]
      exact hz (n * t.2.1 + i) (by omega)
    · intro _ i hi
      rw [hmem, show p + ob + i = p + (ob + i) by omega, hbytes _ (by omega)]
      exact hz (ob + i) (by omega)
  · -- the live objects are unchanged
    refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨r, hr, r1, r2⟩ := hin
    have hA := hap r hr
    unfold Apart at hA
    rw [hmem, ← hlf.readLE a k ⟨r, hr, r1, r2⟩ trivial]
    refine Memory.readLE_congr (fun i hi => ?_)
    rw [hbytes (a + i) (by omega)]
  · -- the new array is fresh
    have hadds := hadds_eq
    rw [hfresh_eq]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simpa using hap
  · rw [hadds_eq]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simpa using apart_win (inRanges_heap (tys := tys) hH hpHE) hWs
  · rw [hadds_eq, hcostK, hmem, view_applyWrites ws hws
      (Or.inl ⟨(p, p + K), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by omega⟩)]
    exact hinv'

end Janus.Contracts.LiveStub

/-- `RtLiveContract linked a 4096 (toyR tys ok) growsliceSpec growsliceLive` for the stub
`LiveStub.growsliceSeg a ob A cap` with `ob = (n - num) · size` (`t = (et, size, ptrBytes)` a
descriptor of `tys`). `hok : ∀ args, ok a args → ∃ p, args = [p, n, c0, num, t.1]`. -/
syntax "janus_live_growslice " term:max term:max term:max term:max term:max term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_growslice $t $n $c0 $num $A $cap $hok) => `(tactic| (
      intro L b s hpc pre
      have pre0 := pre
      have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
      obtain ⟨hc1, hc2, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      obtain ⟨oldp0, hq0, hq1, hq2, hq3, hq4, hacB', hq5⟩ :=
        Janus.Contracts.LiveStub.growslice_unpack (by decide) (t := $t) (by decide) $hok rfl pre
      have hheap := Janus.Contracts.LiveStub.toy_heap_acc (ob := (($n - $num) * ($t).2.1))
        (g := (s.regs 28).toNat) (L' := L) (tys := _) hinvx (Nat.le_trans (by decide) hq4)
      have hbump := Janus.Contracts.LiveStub.toy_heap_bound (ob := (($n - $num) * ($t).2.1))
        (g := (s.regs 28).toNat) (L' := L) (tys := _) hinvx (Nat.le_trans (by decide) hq4)
      first
        | (have hread := Janus.Contracts.LiveStub.growslice_read pre hq0 hq2 hq5 rfl (by decide))
        | skip
      open Janus.Contracts.Toy Janus.Tactic in
        simp only [BUMP, Nat.reduceSub, Nat.reduceMul, Nat.reducePow] at hbump hheap hacB'
      have hbnd := Janus.Contracts.LiveStub.growslice_bound pre hq0 hq2 hq5 rfl
      simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow] at hbnd
      first | (simp only [Nat.reduceSub, Nat.reduceMul] at hread) | skip
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      open Janus.Tactic in
        exact Janus.Contracts.LiveStub.growslice_finish (by decide) (t := $t) (cap := $cap) (A := $A)
          (by decide) $hok rfl (by decide) (by decide) (by decide) rfl (by decide) (by decide)
          (by decide) (by decide) (by decide)
          pre rfl rfl rfl rfl rfl rfl rfl rfl rfl (by simp [setReg, Janus.Contracts.Toy.BUMP]) rfl (by simp [setReg])
          (by (try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl)))
