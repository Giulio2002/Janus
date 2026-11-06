import Janus.Contracts.LiveSatAmd64
import Janus.Contracts.LiveStubConvTAmd64

/-!
# The live `convTstring` / `convT64` contracts are satisfiable (amd64)

For each shape of each contract: an implementation (a stub in the toy bump-allocator runtime), a
runtime `R` that serves the request, a proof that the stub meets `RtLiveContract`, and a call state
meeting the precondition (`RtLivePre`), so the contract is neither unsatisfiable nor vacuous. The
non-empty / `v ≥ 256` shapes allocate (cost `16` / `8`, a fresh box); the empty / `v < 256` shapes
return a static box inside `R.rt` and allocate nothing.
-/

namespace Janus.Contracts.IfaceLiveSatAmd64

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy
  Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64
open Janus.Contracts.AllocSatAmd64 (toy A0)

def okS : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [0, 5]
def okE : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [0, 0]
def ok6 : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [300]
def ok8 : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [7]

def linkS : Janus.Amd64.Program := toy.link [convTstringSeg A0 16]
def linkE : Janus.Amd64.Program := toy.link [convTstringEmptySeg A0]
def link6 : Janus.Amd64.Program := toy.link [convT64Seg A0 16]
def link8 : Janus.Amd64.Program := toy.link [convT64SmallSeg A0]

theorem hokS : ∀ args, okS A0 args → ∃ p, args = [p, 5] := by rintro args ⟨-, rfl⟩; exact ⟨0, rfl⟩
theorem hokE : ∀ args, okE A0 args → ∃ p, args = [p, 0] := by rintro args ⟨-, rfl⟩; exact ⟨0, rfl⟩
theorem hok6 : ∀ args, ok6 A0 args → args = [300] := by rintro args ⟨-, rfl⟩; rfl
theorem hok8 : ∀ args, ok8 A0 args → args = [7] := by rintro args ⟨-, rfl⟩; rfl

set_option maxHeartbeats 4000000 in
theorem convTstring_impl : RtLiveContract64 linkS A0 4096 (toyR LiveSat.tys0 okS)
    convTstringSpec convTstringLive := by
  janus64_live_convtstring 5 16 hokS

set_option maxHeartbeats 4000000 in
theorem convTstringEmpty_impl : RtLiveContract64 linkE A0 4096 (toyR LiveSat.tys0 okE)
    convTstringSpec convTstringLive := by
  janus64_live_convtstring_empty hokE

set_option maxHeartbeats 4000000 in
theorem convT64_impl : RtLiveContract64 link6 A0 4096 (toyR LiveSat.tys0 ok6)
    convT64Spec convT64Live := by
  janus64_live_convt64 300 16 hok6

set_option maxHeartbeats 4000000 in
theorem convT64Small_impl : RtLiveContract64 link8 A0 4096 (toyR LiveSat.tys0 ok8)
    convT64Spec convT64Live := by
  janus64_live_convt64_small hok8

/-- `runtime.convTstring` of a non-empty string: satisfiable (the allocating shape). -/
theorem convTstringLive_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    RtLiveContract64 (toy.link impl) A0 4096 R convTstringSpec convTstringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      RtLivePre64 4096 R convTstringSpec convTstringLive A0 L b s ∧
      convTstringLive.cost (argWords64 s convTstringSpec.nargs) s.mem = 16 :=
  ⟨[convTstringSeg A0 16], toyR LiveSat.tys0 okS, convTstring_impl, [], 0x400, wst [0, 5], rfl,
    ⟨wcallOK64 _ 2 (by omega), trivial, fun x hx => by simp [convTstringSpec] at hx, trivial,
      wguard64 _ 2 (by omega), ⟨⟨rfl, by decide⟩, LiveSat.wmem_inv 0, by decide, by simp, wwin64 _ 2 (by omega)⟩⟩,
    by decide⟩

/-- … of the empty string (`&zeroVal`): satisfiable, allocating nothing. -/
theorem convTstringLive_satisfiable_empty : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    RtLiveContract64 (toy.link impl) A0 4096 R convTstringSpec convTstringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      RtLivePre64 4096 R convTstringSpec convTstringLive A0 L b s ∧
      convTstringLive.cost (argWords64 s convTstringSpec.nargs) s.mem = 0 :=
  ⟨[convTstringEmptySeg A0], toyR LiveSat.tys0 okE, convTstringEmpty_impl, [], 0x400, wst [0, 0], rfl,
    ⟨wcallOK64 _ 2 (by omega), trivial, fun x hx => by simp [convTstringSpec] at hx, trivial,
      wguard64 _ 2 (by omega), ⟨⟨rfl, by decide⟩, LiveSat.wmem_inv 0, by decide, by simp, wwin64 _ 2 (by omega)⟩⟩,
    by decide⟩

/-- `runtime.convT64` of `v ≥ 256`: satisfiable (the allocating shape). -/
theorem convT64Live_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    RtLiveContract64 (toy.link impl) A0 4096 R convT64Spec convT64Live ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      RtLivePre64 4096 R convT64Spec convT64Live A0 L b s ∧
      convT64Live.cost (argWords64 s convT64Spec.nargs) s.mem = 8 :=
  ⟨[convT64Seg A0 16], toyR LiveSat.tys0 ok6, convT64_impl, [], 0x400, wst [300], rfl,
    ⟨wcallOK64 _ 1 (by omega), trivial, fun x hx => by simp [convT64Spec] at hx, trivial,
      wguard64 _ 1 (by omega), ⟨⟨rfl, by decide⟩, LiveSat.wmem_inv 0, by decide, by simp, wwin64 _ 1 (by omega)⟩⟩,
    by decide⟩

/-- … of `v < 256` (`&staticuint64s[v]`): satisfiable, allocating nothing. -/
theorem convT64Live_satisfiable_small : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    RtLiveContract64 (toy.link impl) A0 4096 R convT64Spec convT64Live ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      RtLivePre64 4096 R convT64Spec convT64Live A0 L b s ∧
      convT64Live.cost (argWords64 s convT64Spec.nargs) s.mem = 0 :=
  ⟨[convT64SmallSeg A0], toyR LiveSat.tys0 ok8, convT64Small_impl, [], 0x400, wst [7], rfl,
    ⟨wcallOK64 _ 1 (by omega), trivial, fun x hx => by simp [convT64Spec] at hx, trivial,
      wguard64 _ 1 (by omega), ⟨⟨rfl, by decide⟩, LiveSat.wmem_inv 0, by decide, by simp, wwin64 _ 1 (by omega)⟩⟩,
    by decide⟩

end Janus.Contracts.IfaceLiveSatAmd64
