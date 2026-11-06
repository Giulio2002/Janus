import Janus.Contracts.LiveSat
import Janus.Contracts.LiveStubConvT

/-!
# The live `convTstring` / `convT64` contracts are satisfiable (arm64)

For each shape of each contract: an implementation (a stub in the toy bump-allocator runtime), a
runtime `R` that serves the request, a proof that the stub meets `RtLiveContract`, and a call state
meeting the precondition (`RtLivePre`), so the contract is neither unsatisfiable nor vacuous. The
non-empty / `v ≥ 256` shapes allocate (cost `16` / `8`, a fresh box); the empty / `v < 256` shapes
return a static box inside `R.rt` and allocate nothing.
-/

namespace Janus.Contracts.IfaceLiveSat

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat
  Janus.Contracts.LiveStub
open Janus.Contracts.AllocSat (toy A0)

def okS : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [0, 5]
def okE : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [0, 0]
def ok6 : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [300]
def ok8 : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [7]

def linkS : Program := toy.link [convTstringSeg A0 16]
def linkE : Program := toy.link [convTstringEmptySeg A0]
def link6 : Program := toy.link [convT64Seg A0 16]
def link8 : Program := toy.link [convT64SmallSeg A0]

theorem hokS : ∀ args, okS A0 args → ∃ p, args = [p, 5] := by rintro args ⟨-, rfl⟩; exact ⟨0, rfl⟩
theorem hokE : ∀ args, okE A0 args → ∃ p, args = [p, 0] := by rintro args ⟨-, rfl⟩; exact ⟨0, rfl⟩
theorem hok6 : ∀ args, ok6 A0 args → args = [300] := by rintro args ⟨-, rfl⟩; rfl
theorem hok8 : ∀ args, ok8 A0 args → args = [7] := by rintro args ⟨-, rfl⟩; rfl

set_option maxHeartbeats 4000000 in
theorem convTstring_impl : RtLiveContract linkS A0 4096 (toyR tys0 okS)
    convTstringSpec convTstringLive := by
  janus_live_convtstring 5 16 hokS

set_option maxHeartbeats 4000000 in
theorem convTstringEmpty_impl : RtLiveContract linkE A0 4096 (toyR tys0 okE)
    convTstringSpec convTstringLive := by
  janus_live_convtstring_empty hokE

set_option maxHeartbeats 4000000 in
theorem convT64_impl : RtLiveContract link6 A0 4096 (toyR tys0 ok6)
    convT64Spec convT64Live := by
  janus_live_convt64 300 16 hok6

set_option maxHeartbeats 4000000 in
theorem convT64Small_impl : RtLiveContract link8 A0 4096 (toyR tys0 ok8)
    convT64Spec convT64Live := by
  janus_live_convt64_small hok8

/-- `runtime.convTstring` of a non-empty string: satisfiable (the allocating shape). -/
theorem convTstringLive_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    RtLiveContract (toy.link impl) A0 4096 R convTstringSpec convTstringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      RtLivePre 4096 R convTstringSpec convTstringLive A0 L b s ∧
      convTstringLive.cost (argWords s convTstringSpec.nargs) s.mem = 16 :=
  ⟨[convTstringSeg A0 16], toyR tys0 okS, convTstring_impl, [], 0x400, wst [0, 5], rfl,
    ⟨wst_wcallOK _ 2 (by omega), trivial, fun x hx => by simp [convTstringSpec] at hx, trivial,
      wguard _ 2 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin _ 2 (by omega)⟩⟩,
    by decide⟩

/-- … of the empty string (`&zeroVal`): satisfiable, allocating nothing. -/
theorem convTstringLive_satisfiable_empty : ∃ (impl : List Segment) (R : RtInv),
    RtLiveContract (toy.link impl) A0 4096 R convTstringSpec convTstringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      RtLivePre 4096 R convTstringSpec convTstringLive A0 L b s ∧
      convTstringLive.cost (argWords s convTstringSpec.nargs) s.mem = 0 :=
  ⟨[convTstringEmptySeg A0], toyR tys0 okE, convTstringEmpty_impl, [], 0x400, wst [0, 0], rfl,
    ⟨wst_wcallOK _ 2 (by omega), trivial, fun x hx => by simp [convTstringSpec] at hx, trivial,
      wguard _ 2 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin _ 2 (by omega)⟩⟩,
    by decide⟩

/-- `runtime.convT64` of `v ≥ 256`: satisfiable (the allocating shape). -/
theorem convT64Live_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    RtLiveContract (toy.link impl) A0 4096 R convT64Spec convT64Live ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      RtLivePre 4096 R convT64Spec convT64Live A0 L b s ∧
      convT64Live.cost (argWords s convT64Spec.nargs) s.mem = 8 :=
  ⟨[convT64Seg A0 16], toyR tys0 ok6, convT64_impl, [], 0x400, wst [300], rfl,
    ⟨wst_wcallOK _ 1 (by omega), trivial, fun x hx => by simp [convT64Spec] at hx, trivial,
      wguard _ 1 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin _ 1 (by omega)⟩⟩,
    by decide⟩

/-- … of `v < 256` (`&staticuint64s[v]`): satisfiable, allocating nothing. -/
theorem convT64Live_satisfiable_small : ∃ (impl : List Segment) (R : RtInv),
    RtLiveContract (toy.link impl) A0 4096 R convT64Spec convT64Live ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      RtLivePre 4096 R convT64Spec convT64Live A0 L b s ∧
      convT64Live.cost (argWords s convT64Spec.nargs) s.mem = 0 :=
  ⟨[convT64SmallSeg A0], toyR tys0 ok8, convT64Small_impl, [], 0x400, wst [7], rfl,
    ⟨wst_wcallOK _ 1 (by omega), trivial, fun x hx => by simp [convT64Spec] at hx, trivial,
      wguard _ 1 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin _ 1 (by omega)⟩⟩,
    by decide⟩

end Janus.Contracts.IfaceLiveSat
