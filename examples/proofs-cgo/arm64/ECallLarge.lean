import Extracted

/-!
# `int64_t e_calllarge(int64_t x)` (C, arm64) calls back into Go code whose frame is over 4096
# bytes: the goroutine stack size as a parameter of the `cgocallback` contract

```c
int64_t e_calllarge(int64_t x) { return GoLarge(x); }
```
```go
//go:noinline
func fill(a *[600]int64, x int64) { a[x&7] = x; a[(x+1)&7] = 2 * x }

//export GoLarge
func GoLarge(x C.int64_t) C.int64_t {
	var a [600]int64            // 4800 bytes on the stack: a 4848-byte frame
	fill(&a, int64(x))
	return C.int64_t(a[x&7] + a[(x+1)&7])
}
```

The Go side `_cgoexp_…_GoLarge` (with `GoLarge` inlined) has a 4848-byte frame: its prologue is
the large-frame stack check (`SUBS X17, SP, #4720; B.LO morestack; CMP X17, X16; B.LS
morestack`), it zeroes the array with a 75-iteration loop of four `STP XZR, XZR, [X0], #16`
(`loop`, by induction on the iterations left: the frame's slots and everything outside the
goroutine stack window are kept, `LoopMem`), calls `fill` and stores `3x` in the frame.

**Guarantee (`correctness`).** For every `x`, every runtime memory `rtc` and every readiness `Hc`
of an 8192-byte goroutine stack (`cbk`): every AAPCS64 call of `e_calllarge` in a state as in
`ECallGo` (the runtime initialised, the guard and the TLS `g` slot readable, the C stack window
outside `rtc`, `Hc` at the stub) returns `3x (mod 2^64)`, restoring the callee-saved state,
**under the trusted contract `CgoCallback` alone**. With the earlier fixed 4096-byte goroutine
stack this callback could not be stated: its frame alone is larger.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI Janus.Contracts

namespace Proof

abbrev goFn : Nat := exportAddr Extracted.program "GoLarge"
abbrev gsL : Nat := 8192
abbrev head : Nat := goFn + 0x50

/-- The goroutine stack of the callback: `gsL` bytes, under the readiness `H` of `rtc`. -/
def cbk (rtc : List (Nat × Nat)) (H : RtReady) : CbStack := ⟨gsL, rtc, H⟩

def GoPre (a : W64) (u : State) : Prop :=
  GuardOK u 4720 ∧ StackOK u gsL 16 ∧ 4720 ≤ u.sp.toNat ∧
    Outside ((u.regs 28).toNat + 16) 8 [(u.sp.toNat - gsL, u.sp.toNat + 16)] ∧
    a.toNat + 16 ≤ 2 ^ 48 ∧ u.mem.accessible a.toNat 16 true = true ∧
    Outside a.toNat 16 [(u.sp.toNat - gsL, u.sp.toNat + 16)]

/-- `k` zero words at `a`, `a + 8`, …, stored in this order. -/
def fill8 (M : Memory) (a : Nat) : Nat → Memory
  | 0 => M
  | k + 1 => (fill8 M a k).writeLE (a + 8 * k) 8 0

@[janus_exec, janus_post] theorem regions_fill8 (M : Memory) (a k : Nat) :
    (fill8 M a k).regions = M.regions := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [fill8, Memory.regions_writeLE, ih]

@[janus_exec, janus_post] theorem accessible_fill8 (M : Memory) (a k b n : Nat) (w : Bool) :
    (fill8 M a k).accessible b n w = M.accessible b n w :=
  Memory.accessible_congr (regions_fill8 M a k) b n w

theorem readLE_fill8_disjoint (M : Memory) (a k b n : Nat) (h : b + n ≤ a ∨ a + 8 * k ≤ b) :
    (fill8 M a k).readLE b n = M.readLE b n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [fill8]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), ih (by omega)]

/-- The memory at the loop head before the first iteration. -/
def M0 (u : State) (a : W64) (ret : Nat) : Memory :=
  ((((u.mem.writeLE (u.sp.toNat - 4856) 8 (u.regs 29).toNat).writeLE (u.sp.toNat - 4848) 8
      ret).writeLE (u.sp.toNat + 8) 8 a.toNat).writeLE
    (u.sp.toNat - 16) 8 (u.mem.readLE a.toNat 8 % 8)).writeLE
    (u.sp.toNat - 24) 8 ((u.mem.readLE a.toNat 8 + 1) % 18446744073709551616 % 8)

/-- One iteration of the zeroing loop: eight zero words at `x`. -/
theorem readLE_zero8 (m : Memory) (x b n : Nat) (h : b + n ≤ x ∨ x + 64 ≤ b) :
    ((((((((m.writeLE x 8 0).writeLE (x + 8) 8 0).writeLE (x + 16) 8 0).writeLE (x + 24) 8 0).writeLE
      (x + 32) 8 0).writeLE (x + 40) 8 0).writeLE (x + 48) 8 0).writeLE (x + 56) 8 0).readLE b n =
      m.readLE b n := by
  simp (disch := omega) only [readLE_writeLE_disjoint]

/-- The memory at the loop head: the frame's slots (saved `X29`/`X30`, the two indices, the
frame pointer) as stored before the loop, the accessibility and, outside the goroutine stack
window, the bytes of the entry memory. -/
structure LoopMem (u : State) (a : W64) (ret : Nat) (m : Memory) : Prop where
  acc : ∀ b n w, m.accessible b n w = u.mem.accessible b n w
  out : ∀ b n, Outside b n [(u.sp.toNat - gsL, u.sp.toNat + 16)] → m.readLE b n = u.mem.readLE b n
  fp : m.readLE (u.sp.toNat - 4856) 8 = (u.regs 29).toNat
  lr : m.readLE (u.sp.toNat - 4848) 8 = ret
  frm : m.readLE (u.sp.toNat + 8) 8 = a.toNat
  i1 : m.readLE (u.sp.toNat - 16) 8 = u.mem.readLE a.toNat 8 % 8
  i2 : m.readLE (u.sp.toNat - 24) 8 = (u.mem.readLE a.toNat 8 + 1) % 18446744073709551616 % 8

/-- The frame's result slot holds `3 · p0`; the rest of memory changes only on the goroutine
stack. -/
def GoPost (a : W64) (u u' : State) : Prop :=
  MemFrame (u.mem.writeLE (a.toNat + 8) 8 (3 * u.mem.readLE a.toNat 8)) u'.mem
    [(u.sp.toNat - gsL, u.sp.toNat + 16)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem loop (a : W64) (ret : Nat) (hret : RetAddr Extracted.program ret) (u : State) (hpre : GoPre a u) :
    ∀ k (S : State) (i : Nat), i + k + 1 = 75 →
      S.pc = BitVec.ofNat 64 head → S.sp = u.sp - 4848#64 →
      S.regs 0 = BitVec.ofNat 64 (u.sp.toNat - 4824 + 64 * i) →
      S.regs 1 = BitVec.ofNat 64 (u.mem.readLE a.toNat 8) →
      S.regs 2 = BitVec.ofNat 64 (75 - i) → S.regs 28 = u.regs 28 → S.regs 29 = u.sp - 4856#64 →
      S.regs 30 = BitVec.ofNat 64 ret → LoopMem u a ret S.mem →
      Reaches (Extracted.program.withExit ret) S
        (IsReturnC (Extracted.program.withExit ret) Contract.none fun s' => ABIReturnC u s' ∧ GoPost a u s') := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hsp, hgo, hab, haw, hao⟩ := hpre
  simp only [outside_cons, outside_nil, and_true, gsL] at hgo hao hb hw
  intro k
  induction k with
  | zero =>
    intro S i hk hpc hS hr0 hr1 hr2 h28 h29 h30 ⟨macc, mout, mfp, mlr, mfrm, mi1, mi2⟩
    have hh : head = janus_eval% head := rfl
    rw [hh] at hpc
    have e0 : (BitVec.ofNat 64 (u.sp.toNat - 4824 + 64 * i)).toNat = u.sp.toNat - 4824 + 64 * i := by
      rw [BitVec.toNat_ofNat]; omega
    have e2 : (BitVec.ofNat 64 (75 - i)).toNat = 75 - i := by rw [BitVec.toNat_ofNat]; omega
    have hwS : S.mem.accessible (u.sp.toNat - 8192) (8192 + 16) true = true := by rw [macc]; exact hw
    have hfa : S.mem.accessible a.toNat 16 true = true := by rw [macc]; exact haw
    janus_run [e0, e2, mfp, mlr, mfrm, mi1, mi2]
    unfold GoPost
    rw [show 3 * u.mem.readLE a.toNat 8 = u.mem.readLE a.toNat 8 +
      (u.mem.readLE a.toNat 8 + u.mem.readLE a.toNat 8) by omega]
    apply MemFrame.writeLE_both
    refine ⟨fun b n hb => ?_, fun b n w => ?_⟩
    · simp only [outside_cons, outside_nil, and_true, gsL] at hb
      have h8 := Nat.mod_lt (u.mem.readLE a.toNat 8) (show 0 < 8 by decide)
      have h8' := Nat.mod_lt ((u.mem.readLE a.toNat 8 + 1) % 18446744073709551616) (show 0 < 8 by decide)
      rw [readLE_writeLE_disjoint _ _ (by omega), readLE_writeLE_disjoint _ _ (by omega),
        readLE_zero8 _ _ _ _ (by omega)]
      exact mout b n (by simp only [outside_cons, outside_nil, and_true, gsL]; omega)
    · simp only [Memory.accessible_writeLE, macc]
  | succ k ih =>
    intro S i hk hpc hS hr0 hr1 hr2 h28 h29 h30 ⟨macc, mout, mfp, mlr, mfrm, mi1, mi2⟩
    have hh : head = janus_eval% head := rfl
    rw [hh] at hpc
    have e0 : (BitVec.ofNat 64 (u.sp.toNat - 4824 + 64 * i)).toNat = u.sp.toNat - 4824 + 64 * i := by
      rw [BitVec.toNat_ofNat]; omega
    have e2 : (BitVec.ofNat 64 (75 - i)).toNat = 75 - i := by rw [BitVec.toNat_ofNat]; omega
    have hwS : S.mem.accessible (u.sp.toNat - 8192) (8192 + 16) true = true := by rw [macc]; exact hw
    janus_run [e0, e2] until [janus_eval% head]
    have hi : i ≤ 73 := by omega
    refine ih _ (i + 1) (by omega) rfl rfl ?_ (by simp only [setReg_apply, ↓reduceIte]; exact hr1) ?_
      (by simp only [setReg_apply, ↓reduceIte]; exact h28) (by simp only [setReg_apply, ↓reduceIte]; exact h29)
      (by simp only [setReg_apply, ↓reduceIte]; exact h30) ⟨fun b n w => ?_, fun b n hb => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show _ = BitVec.ofNat 64 _
      simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, e0, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    · show _ = BitVec.ofNat 64 _
      simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, e2, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    · simp only [Memory.accessible_writeLE, macc]
    · simp only [outside_cons, outside_nil, and_true, gsL] at hb
      rw [readLE_zero8 _ _ _ _ (by omega)]
      exact mout b n (by simp only [outside_cons, outside_nil, and_true, gsL]; omega)
    · rw [readLE_zero8 _ _ _ _ (by omega)]; exact mfp
    · rw [readLE_zero8 _ _ _ _ (by omega)]; exact mlr
    · rw [readLE_zero8 _ _ _ _ (by omega)]; exact mfrm
    · rw [readLE_zero8 _ _ _ _ (by omega)]; exact mi1
    · rw [readLE_zero8 _ _ _ _ (by omega)]; exact mi2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem go_spec (a : W64) :
    EnsuresC Extracted.program Contract.none goFn [a] (GoPre a) (GoPost a) := by
  intro ret hret u hu hpre
  have hpre' := hpre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hsp, hgo, hab, haw, hao⟩ := hpre
  simp only [outside_cons, outside_nil, and_true, gsL] at hgo hao hb hw
  have hgf : goFn = janus_eval% goFn := rfl
  have hh : head = janus_eval% head := rfl
  have hr : (BitVec.ofNat 64 ret).toNat = ret := by
    rw [BitVec.toNat_ofNat]; have := hret.user; omega
  have ret_lt : ret < 2 ^ 64 := by have := hret.user; omega
  apply ReturnsC.of_reaches
  janus_intro hu
  janus_run until [janus_eval% head]
  refine loop a ret hret u hpre' 74 _ 0 rfl (by rw [hh]) rfl ?_ rfl ?_ rfl rfl
    (by simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]; exact h_lr) ⟨fun b n w => ?_, fun b n hb => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  · simp (config := { decide := true }) only [setReg_apply, ↓reduceIte]
  · simp only [Memory.accessible_writeLE]
  · simp only [outside_cons, outside_nil, and_true, gsL] at hb
    simp (disch := omega) only [readLE_writeLE_disjoint]
  all_goals (simp (disch := omega) only [readLE_writeLE_disjoint, readLE_writeLE_same]; try simp only [hr])
  all_goals (apply Nat.mod_eq_of_lt; first | omega | (have := ret_lt; omega) | exact Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))

/-! ## The C side, under the callback assumption -/

abbrev rid : Nat := CData.addr Extracted.cdata "runtime_init_done"
abbrev ctxf : Nat := CData.addr Extracted.cdata "cgo_context_function"
/-- `runtime.iscgo`, which `load_g` reads (`ADRP`+`LDRSB`). -/
def iscgo : Nat :=
  adrpLdTarget (segAddr Extracted.program "runtime.load_g.abi0")
    (segWord Extracted.program "runtime.load_g.abi0" 0) (segWord Extracted.program "runtime.load_g.abi0" 1) 0
/-- The GOT slot of `__stack_chk_guard` (an `R_AARCH64_GLOB_DAT` relocation: the dynamic linker
fills it; named by the relocation's symbol, `Extracted.dyngot`). -/
def gslot : Nat := DynGOT.slotOf Extracted.dyngot "__stack_chk_guard"

/-- The C stack `e_calllarge` needs: `GoLarge`'s and `crosscall2`'s frames (the stub at `SP - 256`)
and `cgocallback`'s. -/
abbrev win : Nat := 256 + cbStackScratch

/-- The frame `crosscall2` passes (`[SP+16]` at `cgocallback`). -/
def frameOf (S : State) : Nat := S.mem.readLE (S.sp.toNat + 16) 8

/-- At the stub: the stack window, the callback's readiness and the frame (C memory). -/
def G (k : CbStack) (S : State) : Prop :=
  CStack S cbStackScratch 32 ∧ k.Ready Extracted.tls S ∧ frameOf S + 16 ≤ 2 ^ 48 ∧
    S.mem.accessible (frameOf S) 16 true = true ∧ Outside (frameOf S) 16 (cbClobber Extracted.tls S)

def E (S : State) : Memory :=
  S.mem.writeLE (frameOf S + 8) 8 (3 * S.mem.readLE (frameOf S) 8)

/-- Go's TLS `g` slot of the thread. -/
abbrev slot (s : State) : Nat := tlsGSlot Extracted.tls s.tpidr

def CPre (rtc : List (Nat × Nat)) (Hc : RtReady) (s : State) : Prop :=
  Extracted.program.DataLoaded s.mem ∧ CStack s win 0 ∧
  s.mem.accessible rid 4 false = true ∧ s.mem.readLE rid 4 = 2 ∧
  s.mem.accessible ctxf 8 false = true ∧ s.mem.readLE ctxf 8 = 0 ∧
  s.mem.accessible iscgo 1 false = true ∧ Outside iscgo 1 [(s.sp.toNat - win, s.sp.toNat)] ∧
  slot s + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (slot s) 8 false = true ∧
  s.mem.accessible gslot 8 false = true ∧
  s.mem.accessible (s.mem.readLE gslot 8) 8 false = true ∧
  Outside rid 4 [(s.sp.toNat - win, s.sp.toNat)] ∧ Outside ctxf 8 [(s.sp.toNat - win, s.sp.toNat)] ∧
  Outside gslot 8 [(s.sp.toNat - win, s.sp.toNat)] ∧
  Outside (s.mem.readLE gslot 8) 8 [(s.sp.toNat - win, s.sp.toNat)] ∧
  Outside (slot s) 8 [(s.sp.toNat - win, s.sp.toNat)] ∧
  Outside gslot 8 [(slot s, slot s + 8)] ∧
  Outside (s.mem.readLE gslot 8) 8 [(slot s, slot s + 8)] ∧
  Outside ctxf 8 [(slot s, slot s + 8)] ∧
  Outside (s.sp.toNat - win) win rtc ∧
  Hc [goFn, gsL] (s.mem.readLE (slot s) 8) (s.sp.toNat - 256) (rtView rtc s.mem)

theorem bit_4_2 : Janus.Arm64.bit 4 2 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem c_spec (rtc : List (Nat × Nat)) (Hc : RtReady) (x : W64) :
    CEnsuresC Extracted.program (CallbackSpec Extracted.tls goFn (G (cbk rtc Hc)) E) Extracted.entry [x]
      (CPre rtc Hc) (fun _ s' => s'.regs 0 = 3 * x) := by
  intro ret hret s hs hpre
  obtain ⟨hd, ⟨hal, hb, ha, hw⟩, hra, hrv, hca, hcv, hia, hio, htb, hta, hga, hgpa, hro, hco, hgo, hgpo, hto, hgt,
    hgpt, hct, hrt, hH⟩ := hpre
  have et : Extracted.tls.a64Off + Extracted.tls.varOff "runtime.tls_g" =
      janus_eval% (Extracted.tls.a64Off + Extracted.tls.varOff "runtime.tls_g") := rfl
  have hsl : slot s = s.tpidr.toNat + janus_eval% (Extracted.tls.a64Off + Extracted.tls.varOff "runtime.tls_g") := by
    simp only [slot, tlsGSlot, TLSImage.a64Addr, Nat.add_assoc, et]
  rw [hsl] at htb hta hto hgt hgpt hct hH
  have e1 : rid = janus_eval% rid := rfl
  have e2 : ctxf = janus_eval% ctxf := rfl
  have e3 : iscgo = janus_eval% iscgo := rfl
  have e4 : gslot = janus_eval% gslot := rfl
  rw [e1] at hra hrv hro
  rw [e2] at hca hcv hco hct
  rw [e3] at hia hio
  rw [e4] at hga hgpa hgo hgpo hgt hgpt
  simp only [outside_cons, outside_nil, and_true, win, cbStackScratch] at hro hco hgo hgpo hto hb hw hgt hgpt hct hio
  simp only [win, cbStackScratch] at hrt
  have hv : ∀ (m : Memory) a n v, s.sp.toNat - 16640 ≤ a → a + n ≤ s.sp.toNat →
      rtView rtc (m.writeLE a n v) = rtView rtc m :=
    fun _ _ _ _ h1 h2 => rtView_writeLE (Outside.of_sub hrt h1 (by omega))
  apply ReturnsC.of_reaches
  janus_intro hs.call
  janus_data hd [hw]
  have hrv32 : (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (janus_eval% rid) 4))).toNat = 2 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := Memory.readLE_lt s.mem (janus_eval% rid) 4; omega
  have hgf : goFn = janus_eval% goFn := rfl
  have h256 : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  janus_run
  all_goals (refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩)
  all_goals try (rw [hgf]; janus_simp; done)
  all_goals try (
    simp only [G, frameOf, cbClobber, CStack, cbStackScratch, CbStack.Ready, cbk, tlsGSlot,
      TLSImage.a64Addr, Nat.add_assoc, et, outside_cons, outside_nil, and_true]
    simp (disch := omega) only [hv]
    janus_simp
    rw [hgf] at hH
    exact ⟨⟨by omega, by omega, by omega, Memory.accessible_mono _ hw (by omega) (by omega)⟩, hH, by omega,
      Memory.accessible_mono _ hw (by omega) (by omega), ⟨by omega, by omega, by omega⟩⟩)
  all_goals (rintro s' ⟨-, m, ⟨regs, flags, vregs, fpsr, excl, rfl⟩, hmf⟩)
  all_goals (simp only [E, frameOf, cbClobber, cbStackScratch, tlsGSlot, TLSImage.a64Addr, Nat.add_assoc, et,
    h256] at hmf)
  all_goals (apply ReturnsC.of_reaches; janus_run [bit_4_2])
  all_goals
    refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega

/-! ## Composition: the Go function's theorem discharges the callback assumption -/

theorem frame_lt (S : State) : frameOf S < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Memory.readLE_lt _ _ _) (by decide)

theorem refines (k : CbStack) (hk : k.size = gsL) :
    (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True) k).Refines
      (CallbackSpec Extracted.tls goFn (G k) E) := by
  refine CgoCallback.refines (fun a => go_spec a) (fun S hG => hG.1) (fun S hG => hG.2.1) ?_
    (fun _ _ => rfl) ?_ ?_
  · rintro S u ret ⟨-, -, hb, hacc, hout⟩ he -
    have hf : (BitVec.ofNat 64 (S.mem.readLE (S.sp.toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    have hsep := he.stackSep _ _ _ hacc
    have hgo := he.gOff
    have hst := he.goStack
    rw [hk] at hsep hgo hst
    simp only [outside_cons, outside_nil, and_true, gsL] at hsep hgo hst
    unfold GoPre
    rw [hf]
    refine ⟨he.guardOK (by rw [hk]; simp only [gsL, stackGuard]; decide), hst, by omega, ?_, hb,
      he.keptAcc _ _ _ ⟨hacc, hout⟩, ?_⟩
    · simp only [outside_cons, outside_nil, and_true, gsL, gStructSize] at hgo ⊢; omega
    · simp only [outside_cons, outside_nil, and_true, gsL]; omega
  · rintro S u ret u' ⟨-, -, hb, hacc, hout⟩ he - - hpost b hb' hbacc
    have hf : (BitVec.ofNat 64 (S.mem.readLE (S.sp.toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    unfold GoPost at hpost
    rw [hf] at hpost
    have hsep := he.stackSep _ _ _ hbacc
    rw [hk] at hsep
    have h1 := hpost.readLE b 1 hsep
    simp only [Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Memory.bytes_writeLE, Memory.bytes_writeLE]
    have hk8 : u.mem.readLE (frameOf S) 8 = S.mem.readLE (frameOf S) 8 :=
      he.kept _ _ ⟨Memory.accessible_mono _ (Memory.accessible_read_of_write _ hacc) (Nat.le_refl _) (by omega),
        Outside.of_sub hout (Nat.le_refl _) (by omega)⟩
    rw [hk8]
    split
    · rfl
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro S ⟨-, -, hb, hacc, hout⟩ b _ hna
    rw [E, Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`e_calllarge` end to end**: under the trusted `cgocallback` contract with an 8192-byte
goroutine stack (for every runtime memory `rtc` and readiness `Hc`), the call returns `3x`;
the Go code's frame is 4848 bytes (its stack check is the large-frame form). -/
theorem correctness (rtc : List (Nat × Nat)) (Hc : RtReady) (x : W64) :
    CEnsuresC Extracted.program
      (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True) (cbk rtc Hc))
      Extracted.entry [x] (CPre rtc Hc) (fun _ s' => s'.regs 0 = 3 * x) :=
  (c_spec rtc Hc x).refine (refines _ rfl)

end Proof
