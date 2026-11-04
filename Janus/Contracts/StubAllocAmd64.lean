import Janus.Contracts.AllocSatAmd64
import Janus.Contracts.StubAlloc

/-!
# The (non-live) allocation contracts at a program's own addresses (amd64)

The amd64 twin of `StubAlloc.lean`: the stub is `MOV EAX, heap; RET` (`StubAllocAmd64.heapSeg`), the
tactics are `janus64_newobject`, `janus64_mallocgc`, `janus64_makeslice` for
`NewobjectContract64` etc. with the readiness predicates `StubAlloc.NewReadyAt` / `MallocReadyAt` /
`MakeReadyAt`.
-/

namespace Janus.Contracts.StubAllocAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

/-- The stub: `MOV EAX, heap; RET` (`heap < 4 GiB`). -/
def heapSeg (addr heap : Nat) : Janus.Amd64.Segment :=
  ⟨"stub.heap", addr, [0xb8, heap % 256, heap / 256 % 256, heap / 65536 % 256, heap / 16777216 % 256, 0xc3]⟩

open Janus.Contracts.StubAlloc (HeapReadyAt fresh_heap_at)
open Janus.Contracts.AllocSat (le_blockSize)

theorem newobject_obj64 {rt : List (Nat × Nat)} {heap : Nat} (hrt : (heap, heap + 0x10000) ∈ rt)
    (hh : heap + 0x10000 ≤ 2 ^ 48) (hal : heap % 16 = 0) {s : State}
    (hr : HeapReadyAt heap (rtView rt s.mem)) (hin : InRanges (s.regs 0).toNat 16 rt)
    (hsz : typSize (rtView rt s.mem) (s.regs 0).toNat ≤ 32768) : newobjectObj64 rt s s.mem heap := by
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
  exact fresh_heap_at hrt hh hal _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem mallocgc_obj64 {rt : List (Nat × Nat)} {heap : Nat} (hrt : (heap, heap + 0x10000) ∈ rt)
    (hh : heap + 0x10000 ≤ 2 ^ 48) (hal : heap % 16 = 0) {s : State}
    (hr : HeapReadyAt heap (rtView rt s.mem)) (hsz : (s.regs 0).toNat ≤ 32768) :
    mallocgcObj64 rt s s.mem heap := by
  exact fresh_heap_at hrt hh hal _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

theorem makeslice_obj64 {rt : List (Nat × Nat)} {heap : Nat} (hrt : (heap, heap + 0x10000) ∈ rt)
    (hh : heap + 0x10000 ≤ 2 ^ 48) (hal : heap % 16 = 0) {s : State}
    (hr : HeapReadyAt heap (rtView rt s.mem)) (hin : InRanges (s.regs 0).toNat 16 rt)
    (hsz : typSize (rtView rt s.mem) (s.regs 0).toNat * (s.regs 1).toNat ≤ 32768) :
    makesliceObj64 rt s s.mem heap := by
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat ≤ 32768 at hsz
  exact fresh_heap_at hrt hh hal _ _ hr (le_blockSize _ _)
    (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz))

end Janus.Contracts.StubAllocAmd64

syntax "janus64_newobject " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_newobject $heap $hrt) => `(tactic| (
      intro s hpc pre
      obtain ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, typ, hargs, hin, hsz⟩ := pre
      simp only [List.cons.injEq, and_true] at hargs
      subst hargs
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts in
        refine ⟨BitVec.ofNat 64 $heap, _, _, _, _, _, _, _,
          Janus.Contracts.AllocSatAmd64.ret_of s _ [BitVec.ofNat 64 $heap]
          (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
          (by simp [setRegF]) (by simp) (by simp) rfl rfl rfl rfl rfl,
          ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
      rw [Janus.Contracts.StubAlloc.toNat_heap (by decide)]
      exact Janus.Contracts.StubAllocAmd64.newobject_obj64 $hrt (by decide) (by decide) hr hin hsz))

syntax "janus64_mallocgc " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_mallocgc $heap $hrt) => `(tactic| (
      intro s hpc pre
      obtain ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, sz, typ, nz, hargs, hsz⟩ := pre
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, -⟩ := hargs
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts in
        refine ⟨BitVec.ofNat 64 $heap, _, _, _, _, _, _, _,
          Janus.Contracts.AllocSatAmd64.ret_of s _ [BitVec.ofNat 64 $heap]
          (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
          (by simp [setRegF]) (by simp) (by simp) rfl rfl rfl rfl rfl,
          ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
      rw [Janus.Contracts.StubAlloc.toNat_heap (by decide)]
      exact Janus.Contracts.StubAllocAmd64.mallocgc_obj64 $hrt (by decide) (by decide) hr hsz))

syntax "janus64_makeslice " term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_makeslice $heap $hrt) => `(tactic| (
      intro s hpc pre
      obtain ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, et, l, c, hargs, hin, hsz⟩ := pre
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, rfl⟩ := hargs
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts in
        refine ⟨BitVec.ofNat 64 $heap, _, _, _, _, _, _, _,
          Janus.Contracts.AllocSatAmd64.ret_of s _ [BitVec.ofNat 64 $heap]
          (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
          (by simp [setRegF]) (by simp) (by simp) rfl rfl rfl rfl rfl,
          ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
      rw [Janus.Contracts.StubAlloc.toNat_heap (by decide)]
      exact Janus.Contracts.StubAllocAmd64.makeslice_obj64 $hrt (by decide) (by decide) hr hin
        hsz))
