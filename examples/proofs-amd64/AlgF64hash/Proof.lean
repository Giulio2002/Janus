import Janus
import Extracted

/-!
# `runtime.f64hash` (amd64) meets the `Fhash binary64 8` contract, with `runtime.rand` and `runtime.memhash` as contracts

**Guarantee.** For every hash model `H` with its laws, every stack bound `d` of the callees and
every code `impl` linked at the contract addresses, if `runtime.rand` meets `HashAmd64.Rand … H d`
and `runtime.memhash` meets `HashAmd64.Memhash … H d`, the amd64 machine code of Go 1.26's
`runtime.f64hash(p, h)` satisfies `Janus.Contracts.HashAmd64.Fhash … H (d + 40) binary64 8`: from
every call state with the contract's precondition (with Go's `MXCSR`) it returns to `[RSP]`
without faulting, with `RSP + 8`, `RBP`, `R14`, `X15`, `DF`, `FS` and the control bits of `MXCSR`
kept, memory changed only in `H.priv` and its stack window, `H.Env` kept, and `RAX` a possible
hash `FHashIs H binary64 8 x h` of the float `x` at `p`: `c1 · (c0 ^ h)` for `±0`,
`c1 · (c0 ^ h ^ rand())` for a NaN, `memhash(p, h, 8)` otherwise.

**What the code does.** The stack check, `PUSHQ BP; SUBQ $0x18, SP`, `MOVSD 0(AX), X0`,
`UCOMISD` against `0` (`XORPS X1, X1`): equal, the zero hash; else `UCOMISD X0, X0`: unordered (a
NaN), spill `h` to its argument slot `0x30(SP)`, `CALL runtime.rand`, reload `h` and combine;
else `MOVL $8, CX; CALL runtime.memhash`. The flags of each `UCOMISD` are Go's `==`
(`MemAmd64.comis_feq`), which `HashLaws.feq_zero_iff` and `feq_refl`/`feq_nan_left` turn into
"is a zero" and "is a NaN". At each call `RSP` is 40 bytes below the entry `RSP`; the call states
differ from the entry only in the entry's callee window (the frame pushes and the spill), so
`eqPre_at`/`hPre_at` give the callees' preconditions with bound `d`, and `frame_ret` composes the
frames back.

**Assumptions.** The contract's precondition, `H.Laws` (its environment lives in `H.priv`), and the
`Rand` and `Memhash` contracts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Float Janus.Contracts.MemAmd64 Janus.Contracts.HashAmd64 Janus.Contracts.HashLaws
open Janus.Contracts.Hash (HashModel FHashIs c0 c1)
open Janus.Contracts.Mem (feq)

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
    s' = retState s s'.regs s'.xmm s'.ymmHi s'.flags s'.mxcsr s'.mem s'.zmmHi s'.kreg := by
  obtain ⟨r, rip, fl, xmm, mem, yh, fsb, df, mx, x8, fw, zh, kr⟩ := s'
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
theorem input_at {s S : State} {d frame nargs a n : Nat}
    (hf : MemFrame s.mem S.mem (calleeStack s (d + frame) 2))
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

/-- `UCOMIS x, 0` sets `ZF ∧ ¬PF` exactly for the zeros. -/
theorem feq_zero_r (f : Fmt) {x : Nat} (hx : x < 2 ^ f.width) (h0 : 0 < 2 ^ f.width)
    (hz : zero f false = 0) : feq f x 0 = true ↔ classify f x = .zero := by
  rw [feq_comm, ← hz]; exact feq_zero_iff f (by rw [hz]; exact h0) hx (classify_zero f false)

/-- `UCOMIS x, x` sets `ZF ∧ ¬PF` exactly for the non-NaNs. -/
theorem feq_self (f : Fmt) (x : Nat) : feq f x x = !isNaN f x := by
  cases h : isNaN f x
  · simp [feq_refl f h]
  · simp [feq_nan_left f x h]

theorem xor_c0 (h : W64) : (33054211828000289#64 ^^^ h).toNat = c0 ^^^ h.toNat := by
  rw [BitVec.toNat_xor]; rfl

theorem mul_c1 (x : W64) : (x * 23344194077549503#64).toNat = c1 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_mul, Nat.mul_comm]; rfl

theorem xor3_c0 (r h : W64) : (r ^^^ h ^^^ 33054211828000289#64).toNat = c0 ^^^ h.toNat ^^^ r.toNat := by
  simp only [BitVec.toNat_xor]
  rw [show (33054211828000289#64).toNat = c0 from rfl]
  rw [Nat.xor_comm, Nat.xor_comm r.toNat, Nat.xor_assoc]

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
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all) (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) : HRet H d nargs s s' P :=
  ⟨_, _, _, _, _, _, _, _, retState_of hsp h5 h14 hx hrip hfs hdf hx87 hfw, hmx, hf, he, hp⟩

set_option maxHeartbeats 4000000 in
/-- **`runtime.f64hash` (amd64) meets its contract**, given `runtime.rand`'s and `runtime.memhash`'s. -/
theorem correctness (impl : List Janus.Amd64.Segment) (H : HashModel) (hH : H.Laws) (d : Nat)
    (hr : Rand (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.rand") H d)
    (hmh : Memhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memhash") H d) :
    Fhash (Extracted.program.link impl) Extracted.entry H (d + 40) binary64 8 := by
  intro s hpc ⟨hpre, hm, ⟨hA1, hA2, hA3⟩⟩
  have hpre' := hpre
  obtain ⟨he, hg, ⟨hal, hd, hsp, hacc, hx, hdf, hra⟩, hout, hgo, hgp⟩ := hpre'
  have hA3' := hA3
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  have hgo' := hgo
  simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    at hA3 hgo
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  have hx8 := Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have hm8 : s.mem.readLE (s.regs 0).toNat 8 % 340282366920938463463374607431768211456 = s.mem.readLE (s.regs 0).toNat 8 :=
    Nat.mod_eq_of_lt (by simp only [Nat.reducePow] at hx8; omega)
  have hx64 : s.mem.readLE (s.regs 0).toNat 8 < 2 ^ binary64.width := by
    rw [show binary64.width = 64 from rfl]; simpa using hx8
  have hz0 := feq_zero_r binary64 hx64 (by decide) (by decide)
  janus64_run [GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, hm8]
    until [Extracted.program.contractAddr "runtime.memhash", Extracted.program.contractAddr "runtime.rand"]
  all_goals
    have hz := comis_feq false binary64 (s.mem.readLE (s.regs 0).toNat 8) 0
    have hn := comis_feq false binary64 (s.mem.readLE (s.regs 0).toNat 8) (s.mem.readLE (s.regs 0).toNat 8)
    simp only [*, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.and_true,
      Bool.and_false, Bool.false_and, feq_self] at hz hn
  all_goals first
  | -- `±0`: `c1 · (c0 ^ h)`, no call
    (refine hRet_intro (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) hdf.symm
       (by simp only [BitVec.toNat_ofNat]
           rw [show (2:Nat) ^ 32 = 4294967296 from rfl, mx_raise_div, GoMXCSR.mod hm])
       (by refine MemFrame.of_writeLE _ _ (List.mem_append_right _ (List.mem_cons_self ..)) ?_ ?_ <;>
             omega)
       (env_at hH.env_frame he hout hd (by
         simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame)) ?_
     unfold FHashIs
     simp only [hz0.1 hz.symm, ↓reduceIte]
     simp only [setRegF, reduceIte, Nat.reduceEqDiff]
     rw [mul_c1, xor_c0])
  | -- a NaN: `c1 · (c0 ^ h ^ rand())`
    (refine ReachesRet.call hr rfl (hPre_at hH hpre
        (by simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]) (by rfl) (by exact hx) (by rfl)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
            rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide) (by decide) (by decide)) ?_
     intro s' hpc' ⟨r, x, y, fl, mx, m', _, _, hs', hmx, hfr, he', _⟩
     subst hs'
     have hfr0 := hfr
     simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
       Nat.reduceEqDiff, hsp40] at hfr
     janus64_run
     refine hRet_intro (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) hdf.symm
       (by simp only at hmx ⊢; rw [hmx]; simp only [BitVec.toNat_ofNat]
           rw [show (2:Nat) ^ 32 = 4294967296 from rfl, mx_raise_div, Nat.mod_mod, mx_raise_div,
             GoMXCSR.mod hm])
       (frame_ret (by simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame)
         (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]) (by decide) (by omega) hfr0)
       he' ?_
     have hnan : isNaN binary64 (s.mem.readLE (s.regs 0).toNat 8) = true := by
       revert hn; cases isNaN binary64 (s.mem.readLE (s.regs 0).toNat 8) <;> simp
     have hnz : classify binary64 (s.mem.readLE (s.regs 0).toNat 8) ≠ .zero := fun h => by
       rw [not_isNaN_of_zero h] at hnan; exact Bool.noConfusion hnan
     unfold FHashIs
     simp only [hnz, hnan, ↓reduceIte]
     refine ⟨(r 0).toNat, (r 0).isLt, ?_⟩
     simp only [setRegF, reduceIte, Nat.reduceEqDiff]
     rw [mul_c1, xor3_c0])

  | -- a number: `memhash(p, h, 8)`
    (refine ReachesRet.call hmh rfl ⟨(hPre_at hH hpre
        (by simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]) (by rfl) (by exact hx) (by rfl)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
            rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide) (by decide) (by decide)),
      (input_at (s := s) (frame := 40) (by simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]) (by decide) (by omega)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; simpa using hA1)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; simpa using hA2)
        (by simp only [setRegF, reduceIte, Nat.reduceEqDiff]; simpa using hA3'))⟩ ?_
     intro s' hpc' ⟨r, x, y, fl, mx, m', _, _, hs', hmx, hfr, he', hres⟩
     subst hs'
     have hfr0 := hfr
     simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack, setRegF, reduceIte,
       Nat.reduceEqDiff, hsp40] at hfr
     janus64_run
     refine hRet_intro (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) (by simp [setRegF, retAddrOf, Janus.Contracts.MapAmd64.keepABI, Janus.Contracts.MapAmd64.keepX15, setXmmF]) hdf.symm
       (by simp only at hmx ⊢; rw [hmx]; simp only [BitVec.toNat_ofNat]
           rw [show (2:Nat) ^ 32 = 4294967296 from rfl, mx_raise_div, Nat.mod_mod, mx_raise_div,
             GoMXCSR.mod hm])
       (frame_ret (by simp only [calleeStack, Janus.Contracts.MapAmd64.calleeStack]; janus_frame)
         (by simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp40]) (by decide) (by omega) hfr0)
       he' ?_
     have hnn : isNaN binary64 (s.mem.readLE (s.regs 0).toNat 8) = false := by
       revert hn; cases isNaN binary64 (s.mem.readLE (s.regs 0).toNat 8) <;> simp
     have hnz : classify binary64 (s.mem.readLE (s.regs 0).toNat 8) ≠ .zero := fun h => by
       rw [hz0.2 h] at hz; exact Bool.noConfusion hz
     unfold FHashIs
     simp only [hnz, hnn, reduceIte, Bool.false_eq_true]
     simp only [setRegF, reduceIte, Nat.reduceEqDiff, Janus.Contracts.MapAmd64.keepABI, or_self,
       BitVec.toNat_ofNat] at hres ⊢
     rw [hres, show (8 : Nat) % 2 ^ 64 = 8 from rfl]
     rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
       <;> omega)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.HashSatAmd64

/-- `runtime.rand` and `runtime.memhash` are the straight-line models `randCode` (`RET`) and
`seedCode` (the seed) of `H0`, placed at the contract addresses. -/
def rAddr : Nat := Extracted.program.contractAddr "runtime.rand"
def mAddr : Nat := Extracted.program.contractAddr "runtime.memhash"
def randSeg : Janus.Amd64.Segment := { name := "rand", base := rAddr, bytes := randCode }
def memSeg : Janus.Amd64.Segment := { name := "memhash", base := mAddr, bytes := seedCode }
def implAt : List Janus.Amd64.Segment := [randSeg, memSeg]

theorem modelR (d : Nat) : Rand (Extracted.program.link implAt) rAddr H0 d := by
  rw [show Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } from rfl]
  intro s hpc ⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩
  janus_eval_nat hC : rAddr
  rw [hC] at hpc
  janus64_run
  exact hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv trivial

theorem modelM (d : Nat) : Memhash (Extracted.program.link implAt) mAddr H0 d := by
  rw [show Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } from rfl]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _⟩
  janus_eval_nat hC : mAddr
  rw [hC] at hpc
  janus64_run
  seed_close hdf

/-- The witness call state: `f64hash(VAL, 7)` on `EqHashModel.wmem64` (model `H0`; `VAL` holds 42,
a denormal: the `memhash` path), goroutine `wg`, `RSP = wsp`, the default `MXCSR`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 VAL else if i = 3 then 7
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

/-- The precondition holds at `s0` (the callees' bound 64). -/
theorem pre : HPre H0 (64 + 40) 2 s0 ∧ GoMXCSR s0 ∧ Input s0 (64 + 40) 2 (s0.regs 0).toNat 8 := by
  refine ⟨⟨wmem64_henv _, ⟨by decide, by decide, by decide⟩, ?_, ?_, ?_, ?_⟩, by unfold GoMXCSR; decide,
    ?_⟩ <;>
    simp only [CallOK, Input, H0_priv, calleeStack, Janus.Contracts.MapAmd64.calleeStack,
      outside_cons, outside_nil] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (H : HashModel) (d : Nat) (s : State), H.Laws ∧
    Rand (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.rand") H d ∧
    Memhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memhash") H d ∧
    s.rip = BitVec.ofNat 64 Extracted.entry ∧
    (HPre H (d + 40) 2 s ∧ GoMXCSR s ∧ Input s (d + 40) 2 (s.regs 0).toNat 8) :=
  ⟨implAt, H0, 64, s0, H0_laws, modelR 64, modelM 64, rfl, pre⟩

/-- `correctness` at `s0`: the call returns a possible hash of the float at `VAL`. -/
theorem returns : ReachesRet (Extracted.program.link implAt) (retAddrOf s0) s0
    (fun s' => HRet H0 (64 + 40) 2 s0 s' fun r =>
      FHashIs H0 binary64 8 (s0.mem.readLE (s0.regs 0).toNat 8) (s0.regs 3).toNat (r 0).toNat) :=
  correctness implAt H0 H0_laws 64 (modelR 64) (modelM 64) s0 rfl pre

end Witness

end Proof
