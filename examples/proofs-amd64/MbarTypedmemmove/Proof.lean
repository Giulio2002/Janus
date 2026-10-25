import Janus
import Extracted

/-!
# `runtime.typedmemmove` (amd64) meets the `TypedMemmove` contract, with `runtime.memmove` as contracts

**Guarantee.** For every memory model `M` with its laws, every stack bound `d` of the callees and
every code `impl` linked at the contract addresses, if the callees meet `MemAmd64.Memmove … M d`, the
amd64 machine code of Go 1.26's `runtime.typedmemmove` satisfies `Janus.Contracts.MemAmd64.TypedMemmove … M wb (d + 48)`: from every
call state with the contract's precondition (the write barrier off) it returns to `[RSP]` without
faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`, `FS` and the control bits of `MXCSR` kept,
memory changed only in `M.priv`, its stack window and the destination, `M.Env` kept, and `dst` holds a copy of the `typ.Size_` bytes that were at `src` (`Copied`).

**What the code does.** No stack check; `PUSHQ BP; SUBQ $0x20, SP`; `dst = src`: return (nothing
to copy); else `CMPB runtime.writeBarrier(SB), $0`: off (`WriteBarrierOff`), so the
`bulkBarrierPreWrite` path is not taken (left out as a contract, unreachable);
`CALL runtime.memmove(dst, src, typ.Size_)`, `ADDQ; POPQ BP; RET`. `wb` is the address the `CMPB`
reads (`ripTarget`). At the call `RSP` is 48 bytes below the entry `RSP`, so `memmove` with bound
`d` stays within `d + 48`.

**Assumptions.** The contract's precondition, `M.Laws`, and the `Memmove` contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts.MemAmd64
open Janus.Contracts.Mem (MemModel WriteBarrierOff Zeroed Copied)
open Janus.Contracts (typSize TypeOK)

namespace Proof

/-- Name the state a run stopped in. -/
theorem reach_name {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

/-- A final state that keeps `RBP`, `R14`, `X15`, `DF` and `FS`, has `RSP + 8` and is at the
return address is `retState` of its own registers, flags and memory (the state part of
`MemAmd64.EqRet.intro`). -/
theorem retState_of {s s' : State} (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) :
    s' = retState s s'.regs s'.xmm s'.ymmHi s'.flags s'.mxcsr s'.mem := by
  obtain ⟨r, rip, fl, xmm, mem, yh, fsb, df, mx⟩ := s'
  simp only at hsp h5 h14 hx hrip hfs hdf ⊢
  subst hrip hfs hdf
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
    (hb : (s.regs 4).toNat + 8 + 8 * 3 ≤ 2 ^ 48)
    (hacc : s.mem.accessible ((s.regs 4).toNat - (d + frame)) (d + frame + 8 + 8 * 3) true = true)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 (calleeStack s (d + frame) 3))
    (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 3))
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
    (ho : Outside a n (calleeStack s (d + frame) 3)) : Input S d nargs a n := by
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
    {g : W64} {D : Nat} (he : Env s.mem g) (hout : Outside ((s.regs 4).toNat - D) (D + 8 + 8 * 3) priv)
    (hD : D ≤ (s.regs 4).toNat) (hm : MemFrame s.mem m (calleeStack s D 3)) : Env m g :=
  hl _ _ _ he (Agrees.of_memFrame hm fun a ha => by
    obtain ⟨r, hr, h1, h2⟩ := ha
    have := MemFrame.outside_mem hout hr
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true]
    omega)

/-- The caller's frame then the callee's frame (with the private ranges `P`) is the caller's
frame (amd64). -/
theorem frame_ret {s S : State} {m : Janus.Arm64.Memory} {P : List (Nat × Nat)} {d frame nargs : Nat}
    (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 3))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame)
    (hfd : d + frame ≤ (s.regs 4).toNat)
    (h2 : MemFrame S.mem m (P ++ calleeStack S d nargs)) :
    MemFrame s.mem m (P ++ calleeStack s (d + frame) 3) :=
  hf.trans h2 fun a k h => by
    simp only [outside_append] at h ⊢
    refine ⟨h.2, h.1, ?_⟩
    have h2 := h.2
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hsp] at h2 ⊢
    omega

/-- How a typed-memory proof ends (amd64): as `hRet_intro`, for `TRet`. -/
theorem tRet_intro {M : Janus.Contracts.Mem.MemModel} {d nargs : Nat} {extra : List (Nat × Nat)}
    {s s' : State} {P : Janus.Arm64.Memory → Prop}
    (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64)
    (hf : MemFrame s.mem s'.mem (M.priv ++ calleeStack s d nargs ++ extra))
    (he : M.Env s'.mem (s.regs 14)) (hp : P s'.mem) : TRet M d nargs extra s s' P :=
  ⟨_, _, _, _, _, _, retState_of hsp h5 h14 hx hrip hfs hdf, hmx, hf, he, hp⟩

/-- The caller's frame then the callee's frame (with the private ranges `P` and the extra
ranges `X` of a typed-memory contract) is the caller's frame (amd64). -/
theorem frame_retx {s S : State} {m : Janus.Arm64.Memory} {P X : List (Nat × Nat)} {d frame nargs : Nat}
    (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 3))
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - frame) (hn : 8 + 8 * nargs ≤ frame)
    (hfd : d + frame ≤ (s.regs 4).toNat)
    (h2 : MemFrame S.mem m (P ++ calleeStack S d nargs ++ X)) :
    MemFrame s.mem m (P ++ calleeStack s (d + frame) 3 ++ X) :=
  hf.trans h2 fun a k h => by
    simp only [outside_append] at h ⊢
    refine ⟨h.1.2, ⟨h.1.1, ?_⟩, h.2⟩
    have h2 := h.1.2
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
      and_true, hsp] at h2 ⊢
    omega

/-- `runtime.writeBarrier` (`.noptrbss`): the flag word that `CMPB runtime.writeBarrier(SB), $0`
(at offset `0xd`) reads, taken from the extracted code. -/
def wb : Nat := ripTarget Extracted.program (Extracted.entry + 0xd)

/-- The first byte of a zero word is zero. -/
theorem byte_of_off {m : Janus.Arm64.Memory} {a : Nat} (h : m.readLE a 4 = 0) : m.readLE a 1 = 0 := by
  have := Janus.Arm64.Memory.readLE_lt m a 1
  simp only [Janus.Arm64.Memory.readLE] at h ⊢
  omega

/-- A frame keeps the bytes outside it. -/
theorem bytes_of_frame {m m' : Janus.Arm64.Memory} {rs : List (Nat × Nat)} (hf : MemFrame m m' rs)
    {a : Nat} (ho : Outside a 1 rs) : m'.bytes a = m.bytes a := by
  have := hf.readLE a 1 ho
  simp only [Janus.Arm64.Memory.readLE] at this
  exact BitVec.eq_of_toNat_eq (by omega)

set_option maxHeartbeats 4000000 in
/-- **`runtime.typedmemmove` (amd64) meets its contract**, given its callees'. -/
theorem correctness (impl : List Janus.Amd64.Segment) (M : MemModel) (hM : M.Laws) (d : Nat)
    (hmv : Memmove (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") M d) :
    TypedMemmove (Extracted.program.link impl) Extracted.entry M wb (d + 48) := by
  intro s hpc ⟨⟨he, hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hout, ⟨hw1, hw2, hw3⟩, hwb, hgo, hgp⟩,
    ⟨hT1, hT2⟩, hT3, ⟨hI1, hI2, hI3⟩, ⟨hD1, hD2, hD3, hD4, hD5⟩⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  have hD3' := hD3
  have hI3' := hI3
  have hgo' := hgo
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    at hT3 hD3 hI3 hw3 hgo hD5
  simp only [WriteBarrierOff] at hwb
  have hwb1 := byte_of_off hwb
  simp only [wb, reduceRipTarget] at hw1 hw2 hw3 hwb1 ⊢
  have hsp48 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hS : ∀ v, MemFrame s.mem ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat - 48) 8 v) (calleeStack s (d + 48) 3) := by
    intro v; simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame
  have hn := Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have eN : (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8)).toNat = s.mem.readLE (s.regs 0).toNat 8 := by
    rw [BitVec.toNat_ofNat]; omega
  simp only [typSize] at hD1 hD2 hD3 hD4 hD5 hD3' hI1 hI2 hI3 hI3' ⊢
  janus64_run until [Extracted.program.contractAddr "runtime.memmove"]
  · -- `dst = src`: nothing to move
    have heq : (s.regs 3).toNat = (s.regs 1).toNat := by
      have := (s.regs 3).isLt; have := (s.regs 1).isLt; omega
    have hf1 : MemFrame s.mem (Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat)
        (calleeStack s (d + 48) 3) := by
      simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame
    refine tRet_intro (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) hdf.symm rfl
      (hf1.mono fun a n h => by simp only [outside_append] at h; exact h.1.2)
      (env_at hM.env_frame he hout hd hf1) ?_
    intro i hi
    rw [← heq, bytes_of_frame hf1 (Outside.of_sub hD3' (by omega) (by omega))]
  · refine ReachesRet.call hmv rfl ⟨?_, eqPre_at (frame := 48) hg hal hd hsp hacc hgo' (hS _)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]) (by rfl) (by exact hx) (by rfl)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
            rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide) (by decide) (by decide), ?_, ?_, ?_⟩ ?_
    · exact env_at hM.env_frame he hout hd (hS _)
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
      exact Outside.of_sub hout (by omega) (by omega)
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48, eN]
      refine ⟨hI1, by rw [(hS _).accessible]; exact hI2, ?_⟩
      simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
        and_true, setRegF, reduceIte, Nat.reduceEqDiff, hsp48]
      omega
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48, eN]
      refine ⟨hD1, by rw [(hS _).accessible]; exact hD2, ?_, hD4, ?_⟩ <;>
        simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil,
          and_true, setRegF, reduceIte, Nat.reduceEqDiff, hsp48] <;> omega
    intro s1 hpc1 ⟨r, x, y, fl, mx, m1, hs1, hmx, hfr, he1, hcp⟩
    subst hs1
    have hfr' := hfr
    have hF := frame_retx (nargs := 3) (hS _) (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp48])
      (by decide) (by omega) hfr'
    simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
      Nat.reduceEqDiff, hsp48, eN] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, eN] at hcp he1 hmx hF
    janus64_run
    refine tRet_intro (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15]) hdf.symm (by simp only; rw [hmx]) hF he1 ?_
    intro i hi
    rw [hcp i hi, bytes_of_frame (hS _) (Outside.of_sub hI3' (by omega) (by omega))]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MemSatAmd64

/-- `runtime.memmove` is the model `memmoveCode` (at `A0`, behind a jump at the contract address). -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.memmove"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := memmoveCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model (d : Nat) : Memmove (Extracted.program.link implAt) cAddr M0 d := by
  have hA : Memmove (Extracted.program.link implAt) A0 M0 d := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (memmove_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨e, ⟨⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨e, ⟨⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

/-- The witness memory: `EqHashModel.wmem64` with the (zero) flag word `runtime.writeBarrier`
at `wb` readable. -/
def mem0 : Janus.Arm64.Memory := ⟨wmem64.bytes, wmem64.regions ++ [⟨wb, 4, false⟩]⟩

/-- The witness call state: `typedmemmove(TD, DST, VAL)` on `mem0` (`TD` an 8-byte type), goroutine
`wg`, `RSP = wsp`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 TD else if i = 3 then BitVec.ofNat 64 DST
      else if i = 1 then BitVec.ofNat 64 VAL
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

/-- The precondition holds at `s0` (`memmove`'s bound 64). -/
theorem pre : TPre M0 wb (64 + 48) 3 s0 ∧ TypeOK s0.mem (s0.regs 0).toNat ∧
    Outside (s0.regs 0).toNat 16 (calleeStack s0 (64 + 48) 3) ∧
    Input s0 (64 + 48) 3 (s0.regs 1).toNat (typSize s0.mem (s0.regs 0).toNat) ∧
    Dest M0 s0 (64 + 48) 3 (s0.regs 3).toNat (typSize s0.mem (s0.regs 0).toNat) := by
  simp only [s0, mem0, wb, reduceRipTarget]
  refine ⟨⟨trivial, ⟨by decide, by decide, by decide⟩, ?_, trivial, ?_, ?_, ?_, trivial⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp only [CallOK, Input, Dest, TypeOK, typSize, WriteBarrierOff, M0, calleeStack,
      Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MemModel) (d : Nat) (s : State), M.Laws ∧
    Memmove (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") M d ∧
    s.rip = BitVec.ofNat 64 Extracted.entry ∧
    (TPre M wb (d + 48) 3 s ∧ TypeOK s.mem (s.regs 0).toNat ∧
      Outside (s.regs 0).toNat 16 (calleeStack s (d + 48) 3) ∧
      Input s (d + 48) 3 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat) ∧
      Dest M s (d + 48) 3 (s.regs 3).toNat (typSize s.mem (s.regs 0).toNat)) :=
  ⟨implAt, M0, 64, s0, M0_laws, model 64, rfl, pre⟩

/-- `correctness` at `s0`: the 8 bytes at `VAL` are copied to `DST`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (retAddrOf s0) s0
    (fun s' => TRet M0 (64 + 48) 3
      [((s0.regs 3).toNat, (s0.regs 3).toNat + typSize s0.mem (s0.regs 0).toNat)] s0 s'
      fun m => Copied s0.mem m (s0.regs 3).toNat (s0.regs 1).toNat (typSize s0.mem (s0.regs 0).toNat)) :=
  correctness implAt M0 M0_laws 64 (model 64) s0 rfl pre

end Witness

end Proof
