import Janus.Contracts.AllocAmd64
import Janus.Contracts.AllocSat

/-!
# The allocation contracts are satisfiable (amd64, round 9 C1)

As `Janus.Contracts.AllocSat` for the amd64 contracts of `Janus.Contracts` (`AllocAmd64.lean`):
x86-64 code at `A0` of a program with no other code that returns the 64 KiB heap, the same `rt`
and readiness predicates, a proof that the code meets each contract, and a call state that
satisfies each contract's whole precondition for a non-zero size.
-/

namespace Janus.Contracts.AllocSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Janus (MemFrame InRanges Outside outside_cons outside_nil)
open Janus.Contracts.AllocSat (heap tyA rt HeapReady fresh_heap le_blockSize Hnew Hmalloc Hmake Hgrow
  growCap8_1_0)

def toy : Janus.Amd64.Program := { segments := [], stubs := [], exitAddr := 0 }
def A0 : Nat := 0x100000
def at0 (bs : List Nat) : List Janus.Amd64.Segment := [{ name := "model", base := A0, bytes := bs }]
def withCode (bs : List Nat) : Janus.Amd64.Program := { segments := at0 bs, stubs := [], exitAddr := 0 }
theorem link_at0 (bs : List Nat) : toy.link (at0 bs) = withCode bs := rfl

def wsp : Nat := 0x200000
def wg : Nat := 0x300000

/-- The stack window (the return address `0` at `RSP`), `g`, a type descriptor of `sz` bytes
without pointers at `tyA`, and the heap. -/
def wmem (sz : Nat) : Janus.Arm64.Memory :=
  ⟨fun a => if a = tyA then BitVec.ofNat 8 sz else 0,
   [⟨wsp - 4096, 4096 + 64, true⟩, ⟨wg, 0x100, false⟩, ⟨tyA, 16, false⟩, ⟨heap, 0x10000, true⟩]⟩

def wstate (sz : Nat) (r : Nat → W64) : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else r i,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := wmem sz }

theorem heapReady_w (sz : Nat) (hsz : sz < 256) : HeapReady (rtView rt (wmem sz)) := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [rtView_accessible, show (wmem sz).accessible heap 0x10000 true =
      (wmem 0).accessible heap 0x10000 true from rfl]
    decide
  show (if _ then (wmem sz).bytes (heap + i) else 0) = 0
  split
  · show (if heap + i = tyA then BitVec.ofNat 8 sz else 0) = 0
    rw [if_neg (by simp only [heap, tyA]; omega)]
  · rfl

theorem callOK_w (sz : Nat) (r : Nat → W64) (n : Nat) (hn : n ≤ 5) : CallOK64 (wstate sz r) 4096 n := by
  have hw : (wmem sz).accessible (wsp - 4096) (4096 + 8 + 8 * 5) true = true := by
    rw [show (wmem sz).accessible (wsp - 4096) (4096 + 8 + 8 * 5) true =
      (wmem 0).accessible (wsp - 4096) (4096 + 8 + 8 * 5) true from rfl]
    decide
  have h4 : (wstate sz r).regs 4 = BitVec.ofNat 64 wsp := rfl
  have hm : (wstate sz r).mem = wmem sz := rfl
  simp only [CallOK64, h4, hm]
  refine ⟨?_, by decide, by decide, by simp [wsp]; omega, ?_⟩
  · show (wmem sz).readLE wsp 8 < 2 ^ 47
    rw [show (wmem sz).readLE wsp 8 = 0 by
      simp [Janus.Arm64.Memory.readLE, wmem, wsp, tyA]]
    decide
  · rw [show (BitVec.ofNat 64 wsp).toNat = wsp from rfl]
    exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

/-- `s'` is the return state `retState64 s s'.regs res …` when the result registers hold `res`. -/
theorem ret_of (s s' : Janus.Amd64.State) (res : List W64) (hrip : s'.rip = retAddrOf s)
    (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (h0 : s'.regs 0 = res.getD 0 (s'.regs 0)) (h3 : s'.regs 3 = res.getD 1 (s'.regs 3))
    (h1 : s'.regs 1 = res.getD 2 (s'.regs 1)) (hx : s'.xmm 15 = s.xmm 15)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) (hmx : s'.mxcsr = s.mxcsr)
    (hfw : s'.fpucw = s.fpucw) :
    s' = retState64 s s'.regs res s'.flags s'.xmm s'.ymmHi s'.mem := by
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx, fw⟩ := s'
  simp only at hrip h4 h5 h14 h0 h3 h1 hx hfs hdf hmx ⊢
  simp only [retState64]
  subst hrip hfs hdf hmx
  congr
  · funext i
    simp only [callRegs64]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · split
        · rename_i hi; subst hi; exact h0
        · split
          · rename_i hi; subst hi; exact h3
          · split
            · rename_i hi; subst hi; exact h1
            · rfl
  · funext i
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-! ## `newobject`, `mallocgc`, `makeslice`: `mov $0x10000, %eax; ret` -/

def heapCode : List Nat := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xc3]

theorem newobject64_impl : NewobjectContract64 (toy.link (at0 heapCode)) A0 rt 4096 Hnew := by
  rw [link_at0]
  intro s hpc ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, typ, hargs, hin, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
  rw [show (BitVec.ofNat 64 heap).toNat = heap from rfl]
  exact fresh_heap _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem newobject64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat))
    (H : RtReady), NewobjectContract64 (toy.link impl) A0 rt 4096 H ∧
    ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (NewobjectPre64 4096 s ∧ Ready64 H rt [(s.regs 0).toNat] s) ∧ 0 < typSize s.mem (s.regs 0).toNat :=
  ⟨_, _, _, newobject64_impl, wstate 16 (fun i => if i = 0 then BitVec.ofNat 64 tyA else 0), rfl,
    ⟨⟨callOK_w _ _ 1 (by omega), ⟨by decide, by decide⟩,
        by rw [show ((wstate 16 _).regs 0).toNat = tyA from rfl]; decide⟩,
     heapReady_w 16 (by decide), tyA, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩,
     by decide⟩,
    by rw [show ((wstate 16 _).regs 0).toNat = tyA from rfl]; decide⟩

theorem mallocgc64_impl : MallocgcContract64 (toy.link (at0 heapCode)) A0 rt 4096 Hmalloc := by
  rw [link_at0]
  intro s hpc ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, sz, typ, nz, hargs, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, -, -⟩ := hargs
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  rw [show (BitVec.ofNat 64 heap).toNat = heap from rfl]
  exact fresh_heap _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem mallocgc64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat))
    (H : RtReady), MallocgcContract64 (toy.link impl) A0 rt 4096 H ∧
    ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (MallocgcPre64 4096 s ∧ Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s) ∧
      0 < (s.regs 0).toNat :=
  ⟨_, _, _, mallocgc64_impl, wstate 16 (fun i => if i = 0 then 64 else if i = 1 then 1 else 0), rfl,
    ⟨⟨callOK_w _ _ 3 (by omega), by decide, Or.inl rfl⟩, heapReady_w 16 (by decide), 64, 0, 1, rfl,
      by decide⟩, by decide⟩

theorem makeslice64_impl : MakesliceContract64 (toy.link (at0 heapCode)) A0 rt 4096 Hmake := by
  rw [link_at0]
  intro s hpc ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, et, l, c, hargs, hin, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, -, rfl⟩ := hargs
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat ≤ 32768 at hsz
  rw [show (BitVec.ofNat 64 heap).toNat = heap from rfl]
  exact fresh_heap _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem makeslice64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat))
    (H : RtReady), MakesliceContract64 (toy.link impl) A0 rt 4096 H ∧
    ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (MakeslicePre64 4096 s ∧ Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s) ∧
      0 < typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat :=
  ⟨_, _, _, makeslice64_impl,
    wstate 16 (fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 3 then 2 else if i = 1 then 4 else 0), rfl,
    ⟨⟨callOK_w _ _ 3 (by omega), ⟨by decide, by decide⟩, by decide, by decide,
        by rw [show ((wstate 16 _).regs 0).toNat = tyA from rfl]; decide⟩,
     heapReady_w 16 (by decide), tyA, 2, 4, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩,
     by decide⟩,
    by rw [show ((wstate 16 _).regs 0).toNat = tyA from rfl]; decide⟩

/-! ## `growslice`: `mov $0x10000, %eax; mov $1, %ecx; ret` -/

def growCode : List Nat := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xb9, 0x01, 0x00, 0x00, 0x00, 0xc3]

theorem growslice64_impl : GrowsliceContract64 (toy.link (at0 growCode)) A0 rt 4096 Hgrow := by
  rw [link_at0]
  intro s hpc ⟨⟨⟨⟨hra, hal, _, _, _⟩, _, _, _, _, _, _, _⟩, _⟩, hr, p, et, hargs⟩
  simp only [growsliceArgs64, List.cons.injEq, and_true] at hargs
  obtain ⟨-, h1, h2, h3, -⟩ := hargs
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, ret_of s _ _
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp [setRegF]) (by simp [setRegF, h1, h2, growCap8_1_0]) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
  simp only [growsliceObj64, h1, h2, h3, growCap8_1_0, show (BitVec.ofNat 64 heap).toNat = heap from rfl]
  exact ⟨fresh_heap (size := 8) (round := 8) _ _ hr (Nat.le_refl _) (by decide),
    fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩

def r8 : Nat → W64 := fun i => if i = 3 then 1 else if i = 7 then 1 else if i = 6 then BitVec.ofNat 64 tyA else 0

theorem growslice64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat))
    (H : RtReady), GrowsliceContract64 (toy.link impl) A0 rt 4096 H ∧
    ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧ GrowslicePre64 4096 s ∧
      Ready64 H rt (growsliceArgs64 s) s :=
  ⟨_, _, _, growslice64_impl, wstate 8 r8, rfl,
    ⟨⟨callOK_w 8 r8 5 (by omega), ⟨by decide, by decide⟩, by decide, by decide, by decide, by decide,
        by decide, by decide⟩, fun h => absurd h (by decide)⟩,
    heapReady_w 8 (by decide), 0, tyA, rfl⟩

end Janus.Contracts.AllocSatAmd64
