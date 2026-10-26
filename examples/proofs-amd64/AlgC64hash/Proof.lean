import Janus
import Extracted

/-!
# `runtime.c64hash` (amd64) meets the `Chash binary32 4` contract, with `runtime.f32hash` as a contract

**Guarantee.** For every hash model `H` with its laws, every stack bound `d` of `runtime.f32hash`
and every code `impl` linked at the contract addresses, if `runtime.f32hash` meets
`HashAmd64.Fhash … H d binary32 4`, the amd64 machine code of Go 1.26's `runtime.c64hash(p, h)`
(the hash of `complex64`) satisfies `Janus.Contracts.HashAmd64.Chash … H (d + 32) binary32 4`:
from every call state with the contract's precondition it returns to `[RSP]` without faulting,
with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`, `FS` and the control bits of `MXCSR` kept, memory
changed only in `H.priv` and its stack window, `H.Env` kept, and `RAX` a hash of the imaginary
part seeded with a hash `h1` of the real part (`FHashIs` twice).

**What the code does.** The stack check, `PUSHQ BP; SUBQ $0x10, SP`, spill `p` to its argument
slot `0x20(SP)`, the nil check `TESTB AL, (AX)`, `CALL runtime.f32hash(p, h)`, reload `p`,
`CALL runtime.f32hash(p + 4, h1)`, `ADDQ; POPQ BP; RET`. At both calls `RSP` is 32 bytes below the
entry `RSP` (saved `RBP`, the 16-byte frame, the return address), so `f32hash` with bound `d`
stays within `d + 32`. The first call's precondition comes from the entry (`hPre_at`); the second
call's memory differs from the entry also in `H.priv` (the first call may write there), so its
precondition comes from the first call's return (`hPre_at'`: its environment, and the guard word,
which the contract keeps outside `H.priv`), and the imaginary part, outside `H.priv` by the
contract, still reads as at the entry.

**Assumptions.** The contract's precondition, `H.Laws`, and the `Fhash` contract of
`runtime.f32hash`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Float Janus.Contracts.MemAmd64 Janus.Contracts.HashAmd64 Janus.Contracts.HashLaws
open Janus.Contracts.Hash (HashModel FHashIs c0 c1)

namespace Proof

/-- Name the state a run stopped in. -/
theorem reach_name {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

/-- A final state that keeps `RBP`, `R14`, `X15`, `DF` and `FS`, has `RSP + 8` and is at the
return address is `retState` of its own registers, flags and memory (the state part of
`MemAmd64.EqRet.intro`). -/
theorem retState_of {s s' : State} (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) :
    s' = retState s s'.regs s'.xmm s'.ymmHi s'.flags s'.mxcsr s'.mem := by
  obtain ⟨r, rip, fl, xmm, mem, yh, fsb, df, mx, x8, fw⟩ := s'
  simp only at hsp h5 h14 hx hrip hfs hdf hx87 hfw ⊢
  subst hrip hfs hdf hx87 hfw
  simp only [retState, State.mk.injEq, and_true, true_and]
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Janus.Contracts.MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact hsp
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [Janus.Contracts.MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-- `EqPre` at a call site `S` whose memory differs from the entry `s` only in the entry's
callee window (frame pushes and argument spills), with `RSP` at `frame` bytes below the entry
`RSP` (amd64; as `MemAmd64.EqPre.of_caller`, with the spill slots allowed). -/
theorem eqPre_at {s S : State} {d frame nargs : Nat} (hg : StackGuardOK s (d + frame))
    (hal : (s.regs 4).toNat % 8 = 0) (hd : d + frame ≤ (s.regs 4).toNat)
    (hb : (s.regs 4).toNat + 8 + 8 * 2 ≤ 2 ^ 48)
    (hacc : s.mem.accessible ((s.regs 4).toNat - (d + frame)) (d + frame + 8 + 8 * 2) true = true)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 (calleeStack s (d + frame) 2))
    (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 2))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg' : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame) : EqPre d nargs S := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have hgo' := hgo
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
    and_true] at hgo'
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, hx, hdf, hra⟩, ?_⟩
  · simp only [regG, stackguard0Offset, hg']; omega
  · simp only [regG, stackguard0Offset, hg', hf.accessible]; exact hg2
  · simp only [stackguard0, regG, regSP, stackguard0Offset, hg', hsp]
    rw [hf.readLE _ _ hgo]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hg', hsp]
    omega

/-- `Input` at such a call site of a range readable at the entry and outside the entry's callee
window (amd64). -/
theorem input_at {s S : State} {d frame nargs a n : Nat} {ws : List (Nat × Nat)}
    (hf : MemFrame s.mem S.mem ws)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame)
    (hfd : frame ≤ (s.regs 4).toNat) (hb : a + n ≤ 2 ^ 48) (hacc : s.mem.accessible a n false = true)
    (ho : Outside a n (calleeStack s (d + frame) 2)) : Input S d nargs a n := by
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
    and_true] at ho
  refine ⟨hb, by rw [hf.accessible]; exact hacc, ?_⟩
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
    and_true, hsp]
  omega

/-- A model environment living in `priv` survives changes in the entry's callee window when that
window is outside `priv`. -/
theorem env_at {Env : Janus.Arm64.Memory → W64 → Prop} {priv : List (Nat × Nat)}
    (hl : ∀ m m' g, Env m g → Agrees m m' priv → Env m' g) {s : State} {m : Janus.Arm64.Memory}
    {g : W64} {D : Nat} (he : Env s.mem g) (hout : Outside ((s.regs 4).toNat - D) (D + 8 + 8 * 2) priv)
    (hD : D ≤ (s.regs 4).toNat) (hm : MemFrame s.mem m (calleeStack s D 2)) : Env m g :=
  hl _ _ _ he (Agrees.of_memFrame hm fun a ha => by
    obtain ⟨r, hr, h1, h2⟩ := ha
    have := MemFrame.outside_mem hout hr
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true]
    omega)

/-- `HPre` at such a call site (amd64). -/
theorem hPre_at {H : Janus.Contracts.Hash.HashModel} (hH : H.Laws) {s S : State} {d frame nargs : Nat}
    (hp : HPre H (d + frame) 2 s) (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 2))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg' : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame) : HPre H d nargs S := by
  obtain ⟨he, hg, ⟨hal, hd, hb, hacc, -, -, -⟩, hout, hgo, hgp⟩ := hp
  obtain ⟨q1, q2, q3⟩ := eqPre_at hg hal hd hb hacc hgo hf hsp hg' hx hdf hra hfr hn
  refine ⟨?_, q1, q2, ?_, q3, by rw [hg']; exact hgp⟩
  · rw [hg']; exact env_at hH.env_frame he hout hd hf
  · rw [hsp]; exact Outside.of_sub hout (by omega) (by omega)

/-- The caller's frame then the callee's frame (with the private ranges `P`) is the caller's
frame (amd64). -/
theorem frame_ret {s S : State} {m : Janus.Arm64.Memory} {P : List (Nat × Nat)} {d frame nargs : Nat}
    (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 2))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame)
    (hfd : d + frame ≤ (s.regs 4).toNat)
    (h2 : MemFrame S.mem m (P ++ calleeStack S d nargs)) :
    MemFrame s.mem m (P ++ calleeStack s (d + frame) 2) :=
  hf.trans h2 fun a k h => by
    simp only [outside_append] at h ⊢
    refine ⟨h.2, h.1, ?_⟩
    have h2 := h.2
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hsp] at h2 ⊢
    omega

/-- `HPre` at a call site whose memory differs from the entry `s` in the private ranges and the
entry's callee window, given the environment there (amd64; for a second call). -/
theorem hPre_at' {H : Janus.Contracts.Hash.HashModel} {s S : State} {d frame nargs : Nat}
    (hp : HPre H (d + frame) 2 s) (he : H.Env S.mem (s.regs 14))
    (hf : MemFrame s.mem S.mem (H.priv ++ calleeStack s (d + frame) 2))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hg' : S.regs 14 = s.regs 14)
    (hx : S.xmm 15 = 0) (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47)
    (hfr : frame % 8 = 0) (hn : 8 + 8 * nargs ≤ frame) : HPre H d nargs S := by
  obtain ⟨-, ⟨hg1, hg2, hg3⟩, ⟨hal, hd, hb, hacc, -, -, -⟩, hout, hgo, hgp⟩ := hp
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have hgo' := hgo
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
    and_true] at hgo'
  have hgw : Outside ((s.regs 14).toNat + 16) 8 (H.priv ++ calleeStack s (d + frame) 2) := by
    rw [outside_append]; exact ⟨hgp, hgo⟩
  refine ⟨by rw [hg']; exact he, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, hx, hdf, hra⟩, ?_, ?_, by rw [hg']; exact hgp⟩
  · simp only [regG, stackguard0Offset, hg']; omega
  · simp only [regG, stackguard0Offset, hg', hf.accessible]; exact hg2
  · simp only [stackguard0, regG, regSP, stackguard0Offset, hg', hsp]
    rw [hf.readLE _ _ hgw]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp]; omega
  · rw [hsp, hf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · rw [hsp]; exact Outside.of_sub hout (by omega) (by omega)
  · simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hg', hsp]
    omega

/-- As `frame_ret`, from a frame that may already include the private ranges. -/
theorem frame_ret' {s S : State} {m : Janus.Arm64.Memory} {P : List (Nat × Nat)} {d frame nargs : Nat}
    (hf : MemFrame s.mem S.mem (P ++ calleeStack s (d + frame) 2))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame)
    (hfd : d + frame ≤ (s.regs 4).toNat)
    (h2 : MemFrame S.mem m (P ++ calleeStack S d nargs)) :
    MemFrame s.mem m (P ++ calleeStack s (d + frame) 2) :=
  hf.trans h2 fun a k h => by
    refine ⟨h, ?_⟩
    simp only [outside_append] at h ⊢
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hsp] at h2 ⊢
    omega

/-- How a hashing proof ends (amd64): the final state keeps `RBP`, `R14`, `X15`, `DF` and `FS`,
has `RSP + 8`, the control bits of `MXCSR`, is at the return address, changes memory only in
`H.priv` and the callee window, and keeps `H.Env`. -/
theorem hRet_intro {H : Janus.Contracts.Hash.HashModel} {d nargs : Nat} {s s' : State}
    {P : (Nat → W64) → Prop}
    (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64)
    (hf : MemFrame s.mem s'.mem (H.priv ++ calleeStack s d nargs)) (he : H.Env s'.mem (s.regs 14))
    (hp : P s'.regs) : HRet H d nargs s s' P :=
  ⟨_, _, _, _, _, _, _, _, retState_of hsp h5 h14 hx hrip hfs hdf, hmx, hf, he, hp⟩

set_option maxHeartbeats 4000000 in
/-- **`runtime.c64hash` (amd64) meets its contract**, given `runtime.f32hash`'s. -/
theorem correctness (impl : List Janus.Amd64.Segment) (H : HashModel) (hH : H.Laws) (d : Nat)
    (hf : Fhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.f32hash") H d
      binary32 4) :
    Chash (Extracted.program.link impl) Extracted.entry H (d + 32) binary32 4 := by
  intro s hpc ⟨hpre, hm, ⟨hA1, hA2, hA3⟩, hAp⟩
  have hpre' := hpre
  obtain ⟨he, hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hout, hgo, hgp⟩ := hpre'
  have hA3' := hA3
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    at hA3 hgo
  have hsp32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hS1 : ∀ v, MemFrame s.mem (((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat + 8) 8 (s.regs 0).toNat).writeLE ((s.regs 4).toNat - 32) 8 v)
      (calleeStack s (d + 32) 2) := by
    intro v; simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame
  have ha4 : (s.regs 0 + 4#64).toNat = (s.regs 0).toNat + 4 := by
    rw [BitVec.toNat_add]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.f32hash"]
  refine ReachesRet.call hf rfl ⟨(hPre_at (frame := 32) hH hpre
      (by simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32]) (by rfl) (by exact hx) (by rfl)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32]
          rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide) (by decide) (by decide)),
    (by exact hm),
    (input_at (s := s) (frame := 32) (ws := calleeStack s (d + 32) 2)
      (by simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32]) (by decide) (by omega)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; omega)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]
          exact Arm64.Memory.accessible_mono _ hA2 (by omega) (by omega))
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]
          exact Outside.of_sub hA3' (by omega) (by omega)))⟩ ?_
  intro s1 hpc1 ⟨r1, x1, y1, fl1, mx1, m1, hs1, hmx1, hfr1, he1, hres1⟩
  subst hs1
  have hfr1' := hfr1
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
    Nat.reduceEqDiff, hsp32, List.append_nil] at hfr1
  simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hmx1 hres1 he1
  rw [(hS1 _).readLE _ _ (Outside.of_sub hA3' (by omega) (by omega))] at hres1
  have hF1 := frame_ret (hS1 _) (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32])
    (by decide) (by omega) hfr1'
  janus64_run until [Extracted.program.contractAddr "runtime.f32hash"]
  have hF1w : ∀ v, MemFrame s.mem (m1.writeLE ((s.regs 4).toNat - 32) 8 v)
      (H.priv ++ calleeStack s (d + 32) 2) := fun v =>
    hF1.writeLE v (List.mem_append_right _ (List.mem_cons_self ..)) (by simp; omega) (by simp; omega)
  refine ReachesRet.call hf rfl ⟨(hPre_at' (frame := 32) hpre
      (hH.env_frame _ _ _ he1 (agrees_writeLE _ _ (Outside.of_sub hout (by omega) (by omega)))) (hF1w _)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32]) (by rfl)
      (by simp only [Janus.Contracts.MapAmd64.keepX15, reduceIte]; exact hx) (by rfl)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32]
          rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide) (by decide) (by decide)),
    (by unfold GoMXCSR; simp only; rw [hmx1]; exact hm),
    (input_at (s := s) (frame := 32) (hF1w _)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32]) (by decide) (by omega)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, ha4]; omega)
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, ha4]
          exact Arm64.Memory.accessible_mono _ hA2 (by omega) (by omega))
      (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, ha4]
          exact Outside.of_sub hA3' (by omega) (by omega)))⟩ ?_
  intro s2 hpc2 ⟨r2, x2, y2, fl2, mx2, m2, hs2, hmx2, hfr2, he2, hres2⟩
  subst hs2
  have hfr2' := hfr2
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
    Nat.reduceEqDiff, hsp32] at hfr2
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, ha4] at hmx2 hres2 he2
  have hF2 := frame_ret' (hF1w _) (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32])
    (by decide) (by omega) hfr2'
  have hm2acc : m2.accessible ((s.regs 4).toNat - (d + 32)) (d + 32 + 8 + 8 * 2) true = true := by
    rw [hF2.accessible]; exact hacc
  have hm2acc' := Janus.Arm64.Memory.accessible_read_of_write _ hm2acc
  have hm1acc : m1.accessible ((s.regs 4).toNat - (d + 32)) (d + 32 + 8 + 8 * 2) true = true := by
    rw [hF1.accessible]; exact hacc
  have hm1acc' := Janus.Arm64.Memory.accessible_read_of_write _ hm1acc
  simp only [retState] at hpc2 ⊢
  janus64_run
  have ho4 : Outside ((s.regs 0).toNat + 4) 4 (H.priv ++ calleeStack s (d + 32) 2) := by
    rw [outside_append]
    exact ⟨Outside.of_sub hAp (by omega) (by omega), Outside.of_sub hA3' (by omega) (by omega)⟩
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hF1.readLE _ _ ho4] at hres2
  refine hRet_intro (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) hdf.symm
    (by simp only; rw [hmx2, hmx1]) hF2
    (by simpa [Janus.Contracts.MapAmd64.keepABI, setRegF] using he2) ⟨(r1 0).toNat, hres1, ?_⟩
  simpa [Janus.Contracts.MapAmd64.keepABI, setRegF] using hres2

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.HashSatAmd64

/-- `runtime.f32hash` is the model `f32hashCode` of `H0` (at `A0`, behind a jump at the contract
address). -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.f32hash"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := f32hashCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model (d : Nat) : Fhash (Extracted.program.link implAt) cAddr H0 d binary32 4 := by
  have hA : Fhash (Extracted.program.link implAt) A0 H0 d binary32 4 := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (f32hash_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

/-- The witness call state: `c64hash(VAL, 7)` on `EqHashModel.wmem64` (model `H0`), goroutine
`wg`, `RSP = wsp`, the default `MXCSR`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 VAL else if i = 3 then 7
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (the callee's bound 64). -/
theorem pre : HPre H0 (64 + 32) 2 s0 ∧ GoMXCSR s0 ∧ Input s0 (64 + 32) 2 (s0.regs 0).toNat (2 * 4) ∧
    Outside (s0.regs 0).toNat (2 * 4) H0.priv := by
  refine ⟨⟨wmem64_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_⟩, by unfold GoMXCSR; decide,
    ?_, ?_⟩ <;>
    simp only [CallOK, Input, H0_priv, calleeStack, Janus.Contracts.MapAmd64.calleeStack,
      outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (H : HashModel) (d : Nat) (s : State), H.Laws ∧
    Fhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.f32hash") H d binary32 4 ∧
    s.rip = BitVec.ofNat 64 Extracted.entry ∧
    (HPre H (d + 32) 2 s ∧ GoMXCSR s ∧ Input s (d + 32) 2 (s.regs 0).toNat (2 * 4) ∧
      Outside (s.regs 0).toNat (2 * 4) H.priv) :=
  ⟨implAt, H0, 64, s0, H0_laws, model 64, rfl, pre⟩

/-- `correctness` at `s0`: the call returns a possible hash of the complex number at `VAL`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (retAddrOf s0) s0
    (fun s' => HRet H0 (64 + 32) 2 s0 s' fun r => ∃ h1,
      FHashIs H0 binary32 4 (s0.mem.readLE (s0.regs 0).toNat 4) (s0.regs 3).toNat h1 ∧
      FHashIs H0 binary32 4 (s0.mem.readLE ((s0.regs 0).toNat + 4) 4) h1 (r 0).toNat) :=
  correctness implAt H0 H0_laws 64 (model 64) s0 rfl pre

end Witness

end Proof
