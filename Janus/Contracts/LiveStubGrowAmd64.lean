import Janus.Contracts.LiveStubSliceAmd64
import Janus.Contracts.LiveStubGrow

/-!
# `runtime.growslice` live, at a program's own address (amd64)

The amd64 twin of `LiveStubGrow.lean`: `RtLiveContract64 linked addr 4096 (toyR tys ok) growsliceSpec
growsliceLive`, tactic `janus64_live_growslice t n c0 num A cap hok` (arguments as the arm64 tactic).
The stub loads the old bytes from `RAX` into `RDX, RSI, RDI, R8, R11, R12, R13` (at most 7 chunks),
bumps the allocator (`R9`, `R10`), stores the bytes at the new array and returns `(array, newLen, cap)`
in `RAX, RBX, RCX`.
-/

namespace Janus.Contracts.LiveStubAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy
open Janus.Contracts.LiveStub

/-- The registers the copy uses. -/
def growReg (j : Nat) : Nat := [2, 6, 7, 8, 11, 12, 13].getD j 13

def le32 (x : Nat) : List Nat := [x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256]

/-- loads from `[RAX]`; `mov r9d, BUMP; mov rax, [r9]; lea r10, [rax + A]; mov [r9], r10`; stores
to `[RAX]`; `mov ecx, cap; ret`. -/
def growCodeN (ob A cap : Nat) : List Nat :=
  ((chunkList ob).mapIdx (fun j c => movMem true 0 c.2 c.1 (growReg j))).flatten ++
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x49, 0x8b, 0x01, 0x4c, 0x8d, 0x90] ++ le32 A ++
  [0x4d, 0x89, 0x11] ++
  ((chunkList ob).mapIdx (fun j c => movMem false 0 c.2 c.1 (growReg j))).flatten ++
  [0xb9] ++ le32 cap ++ [0xc3]

def growsliceSeg (addr ob A cap : Nat) : Janus.Amd64.Segment :=
  ⟨"live-stub.growslice", addr, growCodeN ob A cap⟩

/-- What the request pins (amd64: `RAX, RBX, RCX, RDI, RSI`). -/
theorem growslice_unpack64 {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {t : Nat × Nat × Nat} (ht : t ∈ tys) {n c0 num K : Nat}
    (hok' : ∀ args, ok addr args → ∃ p, args = [p, n, c0, num, t.1])
    (hK : roundupsize (nextslicecap n c0 * t.2.1) (t.2.2 == 0) = K)
    {L : List (Nat × Nat)} {b : Nat} {s : State}
    (pre : RtLivePre64 4096 (toyR tys ok) growsliceSpec growsliceLive addr L b s) :
    ∃ oldp, (s.regs 0).toNat = oldp ∧ (s.regs 3).toNat = n ∧
      argWords64 s growsliceSpec.nargs = [oldp, n, c0, num, t.1] ∧
      growsliceLive.cost (argWords64 s growsliceSpec.nargs) s.mem = K ∧ K ≤ b ∧
      s.mem.accessible BUMP 8 true = true ∧ typSize s.mem t.1 = t.2.1 := by
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨oldp, hargs⟩ := hok' _ hok
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) := hinv
  have hrd := toy_ty_read hty hinvT ht
  have hargs0 : (s.regs 0).toNat = oldp := by
    have := congrArg (fun l => l.getD 0 0) hargs
    simpa [argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, growsliceSpec] using this
  have hargs1 : (s.regs 3).toNat = n := by
    have := congrArg (fun l => l.getD 1 0) hargs
    simpa [argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, growsliceSpec] using this
  have hargs2 : (s.regs 1).toNat = c0 := by
    have := congrArg (fun l => l.getD 2 0) hargs
    simpa [argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, growsliceSpec] using this
  have hargs4 : (s.regs 6).toNat = t.1 := by
    have := congrArg (fun l => l.getD 4 0) hargs
    simpa [argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, growsliceSpec] using this
  have hsz : typSize s.mem t.1 = t.2.1 := hrd.1
  have hnoscan : typNoscan s.mem t.1 = (t.2.2 == 0) := by simp only [typNoscan, typPtrBytes, hrd.2]
  have hcostK : growsliceLive.cost (argWords64 s growsliceSpec.nargs) s.mem = K := by
    simp only [growsliceLive, arg, hargs]
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.getD_nil, hsz, hnoscan]
    exact hK
  refine ⟨oldp, hargs0, hargs1, hargs, hcostK, ?_, LiveSat.bump_acc hinv, hsz⟩
  rw [hcostK] at hcost; exact hcost

/-- The old elements are readable. -/
theorem growslice_read64 {tys : Tys} {ok : Nat → List Nat → Prop} {addr : Nat}
    {t : Nat × Nat × Nat} {n c0 num ob oldp : Nat} {L : List (Nat × Nat)} {b : Nat} {s : State}
    (pre : RtLivePre64 4096 (toyR tys ok) growsliceSpec growsliceLive addr L b s)
    (hq0 : (s.regs 0).toNat = oldp) (hargs : argWords64 s growsliceSpec.nargs = [oldp, n, c0, num, t.1])
    (hsz : typSize s.mem t.1 = t.2.1) (hob : (n - num) * t.2.1 = ob) :
    0 < ob → s.mem.accessible (s.regs 0).toNat ob false = true := by
  obtain ⟨hcall, hspec, -⟩ := pre
  obtain ⟨-, -, -, -, -, -, hacc⟩ := hspec
  simp only [hargs, arg, List.getD_cons_succ, List.getD_cons_zero, hsz, hob] at hacc
  rw [hq0]; exact hacc

set_option maxHeartbeats 1000000 in
theorem growslice_finish64 {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {t : Nat × Nat × Nat} (ht : t ∈ tys) {n c0 num ob A cap K : Nat}
    (hok' : ∀ args, ok addr args → ∃ p, args = [p, n, c0, num, t.1])
    (hK : roundupsize (nextslicecap n c0 * t.2.1) (t.2.2 == 0) = K)
    (hcap : growCap t.2.1 (t.2.2 == 0) n c0 = cap) (hCK : cap * t.2.1 = K) (hKpos : 0 < K)
    (hob : (n - num) * t.2.1 = ob) (hobK : ob ≤ K) (hA1 : K ≤ A) (hA2 : A ≤ 64 * K) (hA3 : A % 16 = 0)
    (hcap16 : cap < 65536)
    {L : List (Nat × Nat)} {b : Nat} {s fin : State}
    (pre : RtLivePre64 4096 (toyR tys ok) growsliceSpec growsliceLive addr L b s)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64)
    (h5 : fin.regs 5 = s.regs 5) (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15)
    (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr)
    (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8)) (h3 : fin.regs 3 = s.regs 3)
    (h1 : fin.regs 1 = BitVec.ofNat 64 cap)
    (hmem : fin.mem = applyWrites (s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + A))
      (copyWrites s.mem (s.mem.readLE BUMP 8) (s.regs 0).toNat ob)) :
    RtLivePost64 4096 (toyR tys ok) growsliceSpec growsliceLive L b s fin := by
  obtain ⟨oldp, hargs0, hargs1, hargs, hcostK, hcost, -, hsz'⟩ := growslice_unpack64 hty ht hok' hK pre
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, -, hLs, hWs⟩ := pre
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) := hinv
  have hrd := toy_ty_read hty hinvT ht
  obtain ⟨p0, hbump0, hH0, h16, hbud, hL, hzero, hacH, hacB, hacW, hty0⟩ := hinvT
  have hinvT' : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) :=
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
    by rw [← hm1]; exact Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)
  have hpHE : p + K ≤ HEND := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hH : HEAP ≤ p := hp1
  have hBH : BUMP + 8 ≤ HEAP := by simp [BUMP, HEAP]
  have hargsW : argWords64 s growsliceSpec.nargs = [oldp, n, c0, num, t.1] := hargs
  have hargsW5 : argWords64 s 5 = [oldp, n, c0, num, t.1] := hargs
  have hrange : range0 p K = [(p, p + K)] := by
    unfold range0; rw [if_neg (by omega)]
  have hfresh_eq : growsliceLive.fresh (argWords64 s growsliceSpec.nargs) s.mem (BitVec.ofNat 64 p).toNat
      (s.regs 3).toNat (BitVec.ofNat 64 cap).toNat = [(p, p + K)] := by
    simp only [growsliceLive, hargsW, hpn, hcapn, arg, List.getD_cons_succ, List.getD_cons_zero, hsz', hCK]
    exact hrange
  have hadds_eq : liveAdds growsliceLive (argWords64 s growsliceSpec.nargs) s.mem (BitVec.ofNat 64 p).toNat
      (s.regs 3).toNat (BitVec.ofNat 64 cap).toNat = [(p, p + K)] := by
    simp only [liveAdds, hfresh_eq]
    rfl
  refine ⟨BitVec.ofNat 64 p, s.regs 3, BitVec.ofNat 64 cap, fin.regs, fin.flags, fin.xmm, fin.ymmHi, fin.mem,
    fin.zmmHi, fin.kreg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Janus.Contracts.AllocSatAmd64.ret_of s fin [BitVec.ofNat 64 p, s.regs 3, BitVec.ofNat 64 cap]
      hrip h4 h5 h14 (by simpa using h0) (by simpa using h3) (by simpa using h1) hx hfs hdf hmx hx87 hfw
  · refine ⟨fun a k hout => ?_, fun a k w => ?_⟩
    · have hrt : Outside a k (toyRt tys) := by
        have h := hout
        simp only [outside_append] at h
        exact h.1.1
      have hHB := outside_toyRt_heap_bump hrt
      rw [hmem]
      refine Janus.Arm64.Memory.readLE_congr (fun i hi => ?_)
      rw [hbytes (a + i) (by omega), hbump (a + i) (by omega)]
    · rw [hmem, accessible_applyWrites, ← hm1, Janus.Arm64.Memory.accessible_writeLE]
  · have hns' : typNoscan s.mem t.1 = (t.2.2 == 0) := by simp only [typNoscan, typPtrBytes, hrd.2]
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
  · refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨r, hr, r1, r2⟩ := hin
    have hA := hap r hr
    unfold Apart at hA
    rw [hmem, ← hlf.readLE a k ⟨r, hr, r1, r2⟩ trivial]
    refine Janus.Arm64.Memory.readLE_congr (fun i hi => ?_)
    rw [hbytes (a + i) (by omega)]
  · rw [hfresh_eq]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simpa using hap
  · rw [hadds_eq]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    have := apart_win (inRanges_heap (tys := tys) hH hpHE) hWs
    simpa using this
  · rw [hadds_eq, hcostK, hmem, view_applyWrites ws hws
      (Or.inl ⟨(p, p + K), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by omega⟩)]
    exact hinv'

end Janus.Contracts.LiveStubAmd64

syntax "janus64_live_growslice " term:max term:max term:max term:max term:max term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_growslice $t $n $c0 $num $A $cap $hok) => `(tactic| (
      intro L b s hpc pre
      have pre0 := pre
      have ⟨⟨hra, hal, h3, h4, h5⟩, _⟩ := pre
      obtain ⟨oldp0, hq0, hq1, hq2, hq3, hq4, hacB', hq5⟩ :=
        Janus.Contracts.LiveStubAmd64.growslice_unpack64 (by decide) (t := $t) (by simp) $hok rfl pre0
      have hheap := Janus.Contracts.LiveStub.toy_heap_acc (ob := (($n - $num) * ($t).2.1))
        pre0.2.2.2.2.2.2.1 (Nat.le_trans (by decide) hq4)
      first
        | (have hread := Janus.Contracts.LiveStubAmd64.growslice_read64 pre0 hq0 hq2 hq5 rfl (by decide))
        | skip
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy in
        exact Janus.Contracts.LiveStubAmd64.growslice_finish64 (by decide) (t := $t) (cap := $cap) (A := $A)
          (by simp) $hok rfl (by decide) (by decide) (by decide) rfl (by decide) (by decide) (by decide)
          (by decide) (by decide) pre0 (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
          (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl
          (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
          (by (try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl)))
