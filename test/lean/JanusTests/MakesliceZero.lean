import Janus

/-! `makeslice` of zero bytes (both ISAs): `MakesliceZeroLive` holds of the pinned runtime code (`makeslice` +
`mallocgc` of go1.26.10, run in the model) and of the live stub at a program's own contract address (through
`MakesliceZeroLive.of_live`); a stub that charges the budget for a zero-byte request is REFUTED (a kernel-checked
`¬ MakesliceZeroLive …`, not only a failing tactic); and a call of zero bytes needs no fact about the result's
pointer to keep the live set. -/

namespace JanusTests.MakesliceZero.Arm

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat
open Janus.Contracts.LiveStub
open Janus.Contracts.AllocSat (toy A0 at0 link_at0)

-- the pinned go1.26 runtime.makeslice + runtime.mallocgc, for every runtime hypothesis
example (R : RtInv) : MakesliceZeroLive (toy.link makeslicePinnedSegs) makesliceA 104 R :=
  makesliceZeroLive_pinned 104 R (Nat.le_refl _)

-- the live stub at a program's own contract address (the consumer's witness recipe of LiveStub.lean)
def P : Program :=
  { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0,
    contracts := [("runtime.makeslice", 0x30000)] }
def linked : Program := P.link (stubSegs P)
variable (ok : Nat → List Nat → Prop)
theorem make_ : MakesliceLiveContract linked 0x30000 4096 (toyR [] ok) := by janus_live_makeslice
theorem makeZ : MakesliceZeroLive linked 0x30000 4096 (toyR [] ok) :=
  MakesliceZeroLive.of_live (make_ ok) (toyR_dropEmpty [] ok)

/-- `k` steps and `j` steps from one state both ending where no code is (the return address) end in the same state:
the machine is deterministic. -/
theorem steps_det {p : Program} {s t u : State} {k j : Nat} (h1 : Program.Steps p s k t)
    (h2 : Program.Steps p s j u) (ht : p.fetch t.pc.toNat = none) (hu : p.fetch u.pc.toNat = none) : t = u := by
  induction h1 generalizing j with
  | refl s =>
    cases h2 with
    | refl => rfl
    | step _ _ hf _ _ => rw [ht] at hf; cases hf
  | step hx hs hf hst _ ih =>
    cases h2 with
    | refl => rw [hu] at hf; cases hf
    | step _ _ hf' hst' h2' =>
      rw [hf] at hf'; cases hf'
      rw [hst] at hst'; cases hst'
      exact ih h2' ht

set_option maxRecDepth 20000 in
/-- The toy allocator `bumpCode 16` returns in `bumpFinal s 16` (bump pointer advanced by 16) whatever the request. -/
theorem bump16_run (s : State) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hacB' : s.mem.accessible BUMP 8 true = true) (hpc : s.pc = BitVec.ofNat 64 A0) :
    ReachesRet (toy.link (at0 (bumpCode 16))) (s.regs 30) s (fun t => t = bumpFinal s 16) := by
  rw [link_at0]
  janus_run
  rfl

def okZ : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyB, 0, 0]

/-- The witness memory with the whole heap promised to the budget: `HEAP + 64 · 2^22 = HEND`. -/
theorem wmem_inv_tight (g : Nat) : toyInv tys0 0x400000 [] g (view (toyRt tys0) [] wmem) := by
  obtain ⟨p, h1, h2, h3, -, h5, h6, h7, h8, h9, h10⟩ := wmem_inv g
  have hp : p = HEAP := by rw [← h1]; decide
  subst hp
  exact ⟨HEAP, h1, h2, h3, by decide, h5, h6, h7, h8, h9, h10⟩

/-- **red team**: `bumpCode 16` advances the bump pointer by 16 bytes also for a zero-byte request, i.e. it charges
the budget (and could hand out the block as an object) where the runtime allocates nothing. With the whole heap
promised to the budget the invariant fails after the call, so the stub does NOT meet `MakesliceZeroLive`. -/
theorem bump16_not_zero : ¬ MakesliceZeroLive (toy.link (at0 (bumpCode 16))) A0 4096 (toyR tys0 okZ) := by
  intro h
  have hpre : ((MakeslicePre 4096 (wst [tyB, 0, 0]) ∧ StackRoom (wst [tyB, 0, 0]) 4096 3 ∧
      LiveAt (toyR tys0 okZ) A0 [((wst [tyB, 0, 0]).regs 0).toNat, ((wst [tyB, 0, 0]).regs 1).toNat,
        ((wst [tyB, 0, 0]).regs 2).toNat] [] 0x400000 0 ((wst [tyB, 0, 0]).regs 28).toNat (wst [tyB, 0, 0]).mem
        (calleeStack (wst [tyB, 0, 0]) 4096 3)) ∧
      typSize (wst [tyB, 0, 0]).mem ((wst [tyB, 0, 0]).regs 0).toNat * ((wst [tyB, 0, 0]).regs 2).toNat = 0) :=
    ⟨⟨⟨wst_wcallOK _ 3 (by omega), ⟨by decide, by decide⟩, by decide, by decide, by decide,
        by simp only [calleeStack, outside_cons, outside_nil, and_true]; decide⟩,
      wguard _ 3 (by omega), ⟨⟨rfl, by decide⟩, wmem_inv_tight wg, by decide, by simp, wwin _ 3 (by omega)⟩⟩,
      by decide⟩
  obtain ⟨k, s', hst, hpc', hq⟩ := h [] 0x400000 (wst [tyB, 0, 0]) rfl hpre
  obtain ⟨k0, fin, hst0, hpc0, rfl⟩ := bump16_run (wst [tyB, 0, 0]) (by decide) (by decide) (by decide) rfl
  have hnone : (toy.link (at0 (bumpCode 16))).fetch ((wst [tyB, 0, 0]).regs 30).toNat = none := by decide
  have e : s' = bumpFinal (wst [tyB, 0, 0]) 16 :=
    steps_det hst hst0 (by rw [hpc']; exact hnone) (by rw [hpc0]; exact hnone)
  subst e
  obtain ⟨ptr, junk, f, v, m, ex, ep, hs, -, -, hinv⟩ := hq
  have hm : m = (bumpFinal (wst [tyB, 0, 0]) 16).mem := by
    have := congrArg State.mem hs; simp only [retStateX] at this; exact this.symm
  subst hm
  obtain ⟨p, h1, -, -, h4, -⟩ := (hinv : toyInv tys0 0x400000 [] _ _)
  have : p = HEAP + 16 := by rw [← h1]; decide
  subst this
  simp [HEAP, HEND, HSIZE] at h4

-- the same stub DOES meet `MakesliceLiveContract` for its 16-byte requests: the refutation is about the zero-byte case
example : MakesliceLiveContract (toy.link (at0 (bumpCode 16))) A0 4096 (toyR tys0 okMake) :=
  makeslice16_impl tys0 tysOK0 okMake fun _ h => by
    obtain ⟨-, rfl⟩ := h; exact ⟨(tyB, 8, 0), by simp [tys0], 2, 2, rfl, by decide⟩

-- a zero-byte call keeps the live set: a later live call needs no `LiveSep` for the returned pointer
example {p : Program} {a st : Nat} {R : RtInv} (hz : MakesliceZeroLive p a st R) (L : List (Nat × Nat)) (b : Nat)
    (s : State) (hpc : s.pc = BitVec.ofNat 64 a)
    (hpre : (MakeslicePre st s ∧ StackRoom s st 3 ∧
      LiveAt R a [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b 0 (s.regs 28).toNat s.mem
        (calleeStack s st 3)) ∧ typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat = 0) :
    ReachesRet p (s.regs 30) s fun s' => ∃ m, s'.mem = m ∧ R.inv b L (s.regs 28).toNat (view R.rt L m) := by
  obtain ⟨k, s', h1, h2, ptr, junk, f, v, m, ex, ep, hs, -, -, hinv⟩ := hz L b s hpc hpre
  exact ⟨k, s', h1, h2, m, by rw [hs]; rfl, hinv⟩

end JanusTests.MakesliceZero.Arm

namespace JanusTests.MakesliceZero.Amd

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64
open Janus.Contracts.LiveStubAmd64
open Janus.Contracts.LiveSat (tys0 tysOK0 tyB wmem wmem_inv toyR_dropEmpty okMakeZ wsp wspn wg)
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0)

example (R : RtInv) : MakesliceZeroLive64 (toy.link makeslicePinnedSegs64) makesliceA64 48 R :=
  makesliceZeroLive64_pinned 48 R (Nat.le_refl _)

def P : Janus.Amd64.Program :=
  { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0,
    contracts := [("runtime.makeslice", 0x420000)] }
def linked : Janus.Amd64.Program := P.link (stubSegs P)
variable (ok : Nat → List Nat → Prop)
theorem make_ : MakesliceLiveContract64 linked 0x420000 4096 (toyR [] ok) := by janus64_live_makeslice
theorem makeZ : MakesliceZeroLive64 linked 0x420000 4096 (toyR [] ok) :=
  MakesliceZeroLive64.of_live (make_ ok) (toyR_dropEmpty [] ok)

theorem steps_det {p : Janus.Amd64.Program} {s t u : State} {k j : Nat} (h1 : Janus.Amd64.Program.Steps p s k t)
    (h2 : Janus.Amd64.Program.Steps p s j u) (ht : p.fetch t.rip.toNat = none) (hu : p.fetch u.rip.toNat = none) :
    t = u := by
  induction h1 generalizing j with
  | refl s =>
    cases h2 with
    | refl => rfl
    | step _ _ hf _ _ => rw [ht] at hf; cases hf
  | step hx hs hf hst _ ih =>
    cases h2 with
    | refl => rw [hu] at hf; cases hf
    | step _ _ hf' hst' h2' =>
      rw [hf] at hf'; cases hf'
      rw [hst] at hst'; cases hst'
      exact ih h2' ht

/-- A toy allocator that advances the bump pointer by 16 whatever the request (amd64): `MOV R9D, BUMP;
MOV RAX, [R9]; LEA R10, [RAX+16]; MOV [R9], R10; RET`. -/
def bump16Code : List Nat :=
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x49, 0x8b, 0x01, 0x4c, 0x8d, 0x50, 0x10, 0x4d, 0x89, 0x11, 0xc3]

set_option maxRecDepth 20000 in
theorem bump16_run (s : State) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hacB' : s.mem.accessible BUMP 8 true = true) (hap : Apart 4194304 8 (s.regs 4).toNat 8)
    (hrs : s.mem.accessible (s.regs 4).toNat 8 false = true) (hpc : s.rip = BitVec.ofNat 64 A0) :
    ReachesRet (toy.link (at0 bump16Code)) (retAddrOf s) s
      (fun t => t.mem = s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + 16)) := by
  rw [link_at0]
  janus64_run
  rfl

def okZ : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyB, 0, 0]

/-- **red team** (amd64): `bump16Code` charges the budget for a zero-byte request; refuted as on arm64. -/
theorem bump16_not_zero : ¬ MakesliceZeroLive64 (toy.link (at0 bump16Code)) A0 4096 (toyR tys0 okZ) := by
  intro h
  have h0 : ((wst [tyB, 0, 0]).regs 0).toNat = tyB := wr0 _ (by decide)
  have h3 : ((wst [tyB, 0, 0]).regs 3).toNat = 0 := wr3 _ (by decide)
  have h1 : ((wst [tyB, 0, 0]).regs 1).toNat = 0 := wr1 _ (by decide)
  have het : Outside ((wst [tyB, 0, 0]).regs 0).toNat 16 (calleeStack64 (wst [tyB, 0, 0]) 4096 3) := by
    rw [h0]; simp only [calleeStack64, w4, outside_cons, outside_nil, and_true, tyB, wsp]; decide
  obtain ⟨k, s', hst, hpc', hq⟩ := h [] 0x400000 (wst [tyB, 0, 0]) rfl
    ⟨⟨⟨wcallOK64 _ 3 (by omega), by rw [h0, wmem_eq]; exact ⟨by decide, by decide⟩, by rw [h3, h1]; decide,
      by rw [h1]; decide, by rw [h0, h1, wmem_eq]; decide, het⟩,
      wguard64 _ 3 (by omega), ⟨by rw [h0, h3, h1]; exact ⟨rfl, rfl⟩, JanusTests.MakesliceZero.Arm.wmem_inv_tight wg,
        Nat.zero_le _, by simp, wwin64 _ 3 (by omega)⟩⟩, by rw [h0, h1, wmem_eq]; decide⟩
  obtain ⟨k0, fin, hst0, hpc0, hfin⟩ := bump16_run (wst [tyB, 0, 0]) (by rw [w4]; decide) (by decide)
    (by unfold Apart; rw [w4]; decide) (by rw [w4]; decide) rfl
  have hnone : (toy.link (at0 bump16Code)).fetch (retAddrOf (wst [tyB, 0, 0])).toNat = none := by decide
  have e : s' = fin := steps_det hst hst0 (by rw [hpc']; exact hnone) (by rw [hpc0]; exact hnone)
  subst e
  obtain ⟨ptr, junk, f, x, yh, m, zh, kr, hs, -, -, hinv⟩ := hq
  have hm : m = s'.mem := by
    have := congrArg State.mem hs; simp only [retState64] at this; exact this.symm
  subst hm
  rw [hfin] at hinv
  obtain ⟨p, h1', -, -, h4, -⟩ := (hinv : toyInv tys0 0x400000 [] _ _)
  have : p = HEAP + 16 := by rw [← h1']; decide
  subst this
  simp [HEAP, HEND, HSIZE] at h4

end JanusTests.MakesliceZero.Amd
