import Janus
import Extracted

/-!
# `runtime.nilinterhash` (amd64) meets the `Nilinterhash` contract, with `runtime.typehash` as a contract

**Guarantee.** For every hash model `H` with its laws, every stack bound `d` of
`runtime.typehash` and every code `impl` linked at the contract addresses, if `runtime.typehash`
meets `HashAmd64.Typehash … H d`, the amd64 machine code of Go 1.26's `runtime.nilinterhash(p, h)` (the
hash of `any`) satisfies `Janus.Contracts.HashAmd64.Nilinterhash … H (d + 56)`: from every call state
with the contract's precondition it returns to `[RSP]` without faulting, with `RSP + 8`, `RBP`,
`R14`, `X15`, `DF`, `FS` and the control bits of `MXCSR` kept, memory changed only in `H.priv` and
its stack window, `H.Env` kept, and `RAX` as `IHashIs`: `h` for a nil dynamic type, else
`c1 · r` for a `typehash(t, data, h ^ c0)` result `r`.

**What the code does.** The stack check, `PUSHQ BP; SUBQ $0x28, SP`, then the type word `t = 0(AX)`: nil, return
`h`; else the check `t.Equal ≠ nil` (its failure path, `panic(errorString("hash of unhashable
type " + t.string()))` through `runtime.rtype.string`, `concatstring2`, `convTstring`, `gopanic`,
is excluded: the contract makes `t` hashable, and `HashModel.Laws.type_desc` gives `t.Equal ≠ 0`),
the `TFlagDirectIface` test (bit 5 of `t.TFlag`, `isDirectIface`) choosing the data pointer
(`p + 8` or `8(p)`, `dataAt`), `CALL runtime.typehash(t, data, h ^ c0)`, `IMULQ c1`. At the call
`RSP` is 56 bytes below the entry `RSP` (saved `RBP`, the 40-byte frame, the return address), so
`typehash` with bound `d` stays within `d + 56`; hashability and the hash carry between the entry
memory and the call's by the contract's `HashFrame`.

**Assumptions.** The contract's precondition, `H.Laws`, and the `Typehash` contract of
`runtime.typehash` (the panic path's callees are left out as contracts and are unreachable).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Float Janus.Contracts.MemAmd64 Janus.Contracts.HashAmd64
open Janus.Contracts.Hash (HashModel IHashIs HashFrame dataAt c0 c1)

namespace Proof

/-- Name the state a run stopped in. -/
theorem reach_name {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

/-- A final state that keeps `RBP`, `R14`, `X15`, `DF` and `FS`, has `RSP + 8` and is at the
return address is `retState` of its own registers, flags and memory (the state part of
`MemAmd64.EqRet.intro`). -/
theorem retState_of {s s' : State} (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) (hcw : s'.fpucw = s.fpucw := by first | rfl | simp_all) :
    s' = retState s s'.regs s'.xmm s'.ymmHi s'.flags s'.mxcsr s'.mem := by
  obtain ⟨r, rip, fl, xmm, mem, yh, fsb, df, mx, cw⟩ := s'
  simp only at hsp h5 h14 hx hrip hfs hdf hcw ⊢
  subst hrip hfs hdf hcw
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
    (hp : P s'.regs)
    (hcw : s'.fpucw = s.fpucw := by first | rfl | simp_all) : HRet H d nargs s s' P :=
  ⟨_, _, _, _, _, _, retState_of hsp h5 h14 hx hrip hfs hdf hcw, hmx, hf, he, hp⟩

/-- `TESTL $0x20` on the `TFlag` byte: bit 5, `TFlagDirectIface`. -/
theorem tflag_key (x : Nat) : (BitVec.ofNat 8 x &&& 32#8 = 0#8) ↔ x.testBit 5 = false := by
  constructor
  · intro h
    have := congrArg (fun v : BitVec 8 => v.getLsbD 5) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat] at this
    have h32 : (32 : Nat).testBit 5 = true := by decide
    cases hx : x.testBit 5 <;> simp_all
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
    by_cases h5 : i = 5
    · subst h5; simp [h]
    · have : (32 : Nat).testBit i = false := by
        rw [show (32 : Nat) = 2 ^ 5 from rfl, Nat.testBit_two_pow_of_ne (Ne.symm h5)]
      simp [this]

theorem tflag_bit (x : Nat) (hx : x < 256) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x))) &&& 32#8 = 0#8) ↔
      x.testBit 5 = false := by
  have : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x))) = BitVec.ofNat 8 x := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  rw [this]; exact tflag_key x

theorem mul_c1 (x : W64) : (x * 23344194077549503#64).toNat = c1 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_mul, Nat.mul_comm]; rfl

theorem xor_c0' (h : W64) : (33054211828000289#64 ^^^ h).toNat = h.toNat ^^^ c0 := by
  rw [BitVec.toNat_xor, Nat.xor_comm]; rfl

theorem inRanges_apart {a k b j : Nat} {rs : List (Nat × Nat)} (hi : InRanges a k rs)
    (ho : Outside b j rs) : b + j ≤ a ∨ a + k ≤ b := by
  obtain ⟨r, hr, h1, h2⟩ := hi; have := MemFrame.outside_mem ho hr; omega

set_option maxHeartbeats 4000000 in
/-- **`runtime.nilinterhash` (amd64) meets its contract**, given `runtime.typehash`'s. -/
theorem correctness (impl : List Janus.Amd64.Segment) (H : HashModel) (hH : H.Laws) (d : Nat)
    (hth : Typehash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typehash") H d) :
    Nilinterhash (Extracted.program.link impl) Extracted.entry H (d + 56) := by
  intro s hpc ⟨hpre, ⟨hA1, hA2, hA3⟩, hok⟩
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
  have hsp56 : (s.regs 4 - 56#64).toNat = (s.regs 4).toNat - 56 := by
    rw [BitVec.toNat_sub]; simp; omega
  by_cases ht : s.mem.readLE (s.regs 0).toNat 8 = 0
  · janus64_run
    refine hRet_intro (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) hdf.symm rfl
      (by refine MemFrame.of_writeLE _ _ (List.mem_append_right _ (List.mem_cons_self ..)) ?_ ?_ <;>
            simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack] <;> omega)
      (env_at hH.env_frame he hout hd (by
         simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame)) ?_
    simp [IHashIs, setRegF]
  · obtain ⟨hhash, hfr0⟩ := hok ht
    obtain ⟨-, ht48, htacc, htpriv, htE⟩ := hH.type_desc _ _ _ _ he hhash
    have hap := inRanges_apart htpriv hout
    simp only [tyEqual] at htE
    simp only [typeDescSize] at ht48 htacc hap
    have hS : ∀ v w, MemFrame s.mem ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).writeLE
        ((s.regs 4).toNat - 56) 8 w) (calleeStack s (d + 56) 2) := by
      intro v w; simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame
    have hfl := Arm64.Memory.readLE_lt s.mem (s.mem.readLE (s.regs 0).toNat 8 + 20) 1
    have hT := Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
    have hD := Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 8) 8
    have eT : (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8)).toNat = s.mem.readLE (s.regs 0).toNat 8 := by
      rw [BitVec.toNat_ofNat]; omega
    have eD : (BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8)).toNat =
        s.mem.readLE ((s.regs 0).toNat + 8) 8 := by rw [BitVec.toNat_ofNat]; omega
    have eA : (s.regs 0 + 8#64).toNat = (s.regs 0).toNat + 8 := by
      rw [BitVec.toNat_add]; simp; omega
    janus64_run until [Extracted.program.contractAddr "runtime.typehash"]
    all_goals
      have hdir : isDirectIface s.mem (s.mem.readLE (s.regs 0).toNat 8) =
          (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 20) 1).testBit 5 := rfl
      first
        | have hd' := (tflag_bit _ (by simpa using hfl)).1 hbr
          rw [hd'] at hdir
        | have hd' : (s.mem.readLE (s.mem.readLE (s.regs 0).toNat 8 + 20) 1).testBit 5 = true := by
            have := mt (tflag_bit _ (by simpa using hfl)).2 hbr; simpa using this
          rw [hd'] at hdir
      have hdata : dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat =
          if isDirectIface s.mem (s.mem.readLE (s.regs 0).toNat 8) then (s.regs 0).toNat + 8
          else s.mem.readLE ((s.regs 0).toNat + 8) 8 := rfl
      rw [hdir] at hdata
      simp only [reduceIte, Bool.false_eq_true] at hdata
      refine ReachesRet.call hth rfl ⟨hPre_at (frame := 56) hH hpre (hS _ _)
          (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp56]) (by rfl) (by exact hx) (by rfl)
          (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp56]
              rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide) (by decide) (by decide), ?_⟩ ?_
      · simp only [setRegF, reduceIte, Nat.reduceEqDiff, eT, eD, eA]
        rw [← hdata]; exact (hfr0 _ (hS _ _)).1 hhash
      intro s1 hpc1 ⟨r, x, y, fl, mx, m1, hs1, hmx, hfr, he1, hres⟩
      subst hs1
      have hfr' := hfr
      simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
        Nat.reduceEqDiff, hsp56] at hfr
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, eT, eD, eA, xor_c0'] at hres he1 hmx
      rw [← hdata] at hres
      janus64_run
      refine hRet_intro (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) hdf.symm (by simp only; rw [hmx])
        (frame_ret (hS _ _) (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp56]) (by decide)
          (by omega) hfr') he1 ?_
      unfold IHashIs
      rw [if_neg ht]
      refine ⟨(r 0).toNat, ((hfr0 _ (hS _ _)).2.1 _ _).1 hres, ?_⟩
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, Janus.Contracts.MapAmd64.keepABI, or_self]
      rw [mul_c1]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.HashSatAmd64

/-- `runtime.typehash` is the straight-line model `typehashCode` of `H0` (the seed), placed at
the contract address. -/
def tAddr : Nat := Extracted.program.contractAddr "runtime.typehash"
def thSeg : Janus.Amd64.Segment := { name := "typehash", base := tAddr, bytes := typehashCode }
def implAt : List Janus.Amd64.Segment := [thSeg]

theorem model (d : Nat) : Typehash (Extracted.program.link implAt) tAddr H0 d := by
  rw [show Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } from rfl]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _⟩
  janus_eval_nat hC : tAddr
  rw [hC] at hpc
  janus64_run
  seed_close hdf

/-- `H0`'s hashes of `TD` values do not depend on memory outside `TD.TFlag` (over `wmem64`). -/
theorem hashFrame_TD64 (p : Nat) (ws : List (Nat × Nat)) (hws : Outside (TD + 20) 1 ws) :
    HashFrame H0 TD wmem64 p ws := fun m' hf =>
  ⟨id, fun _ _ => Iff.rfl, by
    simp only [Janus.Spec.Type.isDirectIface, Janus.Spec.Type.tyTFlag]; rw [hf.readLE _ _ hws]⟩

/-- The witness call state: `nilinterhash(EFV, 7)` on `EqHashModel.wmem64` (model `H0`; `EFV = (TD, VAL)`),
goroutine `wg`, `RSP = wsp`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 EFV else if i = 3 then 7
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (`typehash`'s bound 64). -/
theorem pre : HPre H0 (64 + 56) 2 s0 ∧ Input s0 (64 + 56) 2 (s0.regs 0).toNat 16 ∧
    (s0.mem.readLE (s0.regs 0).toNat 8 ≠ 0 →
      H0.Hashable (s0.mem.readLE (s0.regs 0).toNat 8) s0.mem
        (dataAt s0.mem (s0.mem.readLE (s0.regs 0).toNat 8) (s0.regs 0).toNat) ∧
      HashFrame H0 (s0.mem.readLE (s0.regs 0).toNat 8) s0.mem
        (dataAt s0.mem (s0.mem.readLE (s0.regs 0).toNat 8) (s0.regs 0).toNat)
        (calleeStack s0 (64 + 56) 2)) := by
  have hw : Outside (TD + 20) 1 (calleeStack s0 (64 + 56) 2) := by
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil]; decide
  refine ⟨⟨wmem64_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_⟩, ?_, fun _ => ?_⟩
  rotate_left 5
  · have e1 : s0.mem.readLE (s0.regs 0).toNat 8 = TD := by decide
    rw [e1]; exact ⟨rfl, hashFrame_TD64 _ _ hw⟩
  all_goals simp only [CallOK, Input, H0_priv, calleeStack, Janus.Contracts.MapAmd64.calleeStack,
      outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (H : HashModel) (d : Nat) (s : State), H.Laws ∧
    Typehash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.typehash") H d ∧
    s.rip = BitVec.ofNat 64 Extracted.entry ∧ (HPre H (d + 56) 2 s ∧ Input s (d + 56) 2 (s.regs 0).toNat 16 ∧
      (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        H.Hashable (s.mem.readLE (s.regs 0).toNat 8) s.mem
          (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat) ∧
        HashFrame H (s.mem.readLE (s.regs 0).toNat 8) s.mem
          (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat)
          (calleeStack s (d + 56) 2))) :=
  ⟨implAt, H0, 64, s0, H0_laws, model 64, rfl, pre⟩

/-- `correctness` at `s0`: the call returns the interface hash of the value at `EFV`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (retAddrOf s0) s0
    (fun s' => HRet H0 (64 + 56) 2 s0 s' fun r =>
      IHashIs H0 s0.mem (s0.mem.readLE (s0.regs 0).toNat 8) (s0.regs 0).toNat (s0.regs 3).toNat (r 0).toNat) :=
  correctness implAt H0 H0_laws 64 (model 64) s0 rfl pre

end Witness

end Proof
