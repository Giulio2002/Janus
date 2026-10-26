import Extracted

/-!
# `int64_t e_callbox(int64_t x)` (C, arm64) calls back into Go code that calls a Go function and
# allocates: C → Go → `runtime.newobject`, composed end to end

```c
int64_t e_callbox(int64_t x) { return GoBox(x); }
```
```go
type box struct{ v int64 }

//go:noinline
func newBox(v int64) *box { return &box{v} }      // runtime.newobject

//export GoBox
func GoBox(x C.int64_t) C.int64_t { return C.int64_t(newBox(int64(x)).v + 1) }
```

`e_callbox` tail-calls `GoBox`, the C function cgo generates for `//export GoBox` (as in
`ECallGo`: `_cgo_wait_runtime_init_done`, the frame, `crosscall2`, `_cgo_release_context`, the
stack protector). `crosscall2` and `load_g` call `runtime.cgocallback`, which runs the Go side
of the export, `_cgoexp_…_GoBox`, on the goroutine stack: its stack check reads `stackguard0`
through `X28 = g`, it calls `newBox` (another stack check), which calls `runtime.newobject` for a
fresh 8-byte cell, stores `x` in it; `_cgoexp_…_GoBox` reads it back and stores `x + 1` in the
frame's result slot.

**Guarantee (`correctness`).** For every `x`, every list `rt` of runtime-owned memory ranges,
every implementation of `runtime.newobject` meeting `NewobjectContract` with readiness `Ha`, and
every readiness `Hc` of an 8192-byte goroutine stack (`cbk`): every AAPCS64 call of `e_callbox`
in a state where the runtime is initialised, the stack protector's guard and Go's TLS `g` slot
are readable, the C stack has room for the frames and `cgocallback`, the C memory is not
runtime-owned (`rt`, `rtc`), and the runtime is ready for the callback (`Hc` at the stub), returns
`x + 1 (mod 2^64)` restoring the callee-saved state, **under the trusted contract `CgoCallback`**
whose readiness `R` is the allocator's readiness `Ha` at the `newobject` call (`ROK`). Every
instruction of the C code, `crosscall2`, `load_g`, `_cgoexp_…_GoBox` and `newBox` is executed by
the model; `newobject` is the contract.

**How.** `go_spec` proves the Go side (`EnsuresC`, both stack checks and the allocation through
`hnew.pos`), from the goroutine stack and `g` that `CallbackEntry` gives; `c_spec` proves the C
side under `CallbackSpec`; `CgoCallback.refines` composes them.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.Spec Janus.FFI Janus.Contracts

namespace Proof

abbrev goFn : Nat := exportAddr Extracted.program "GoBox"

/-- The goroutine stack the callback needs: `_cgoexp_…_GoBox`'s 32-byte frame, `newBox`'s 48,
`newobject`'s 4096-byte window and the spill slots, below 8192 with the stack-check margin. -/
abbrev gsBox : Nat := 8192

/-- The goroutine stack of the callback: `gsBox` bytes, under the readiness `H` of `rtc`. -/
def cbk (rtc : List (Nat × Nat)) (H : RtReady) : CbStack := ⟨gsBox, rtc, H⟩

/-- `box`'s type descriptor (`newBox`'s `ADRP` + `ADD` at `+0x1c`), recomputed from the words. -/
def boxType : Nat :=
  adrpLdTarget (segAddr Extracted.program "example.com/cgo/cenv.newBox" + 0x1c)
    (segWord Extracted.program "example.com/cgo/cenv.newBox" 7)
    (segWord Extracted.program "example.com/cgo/cenv.newBox" 8) 0

/-! ## The Go side -/

/-- The allocator's readiness at the `newobject` call: the goroutine stack is apart from the
runtime-owned memory, and `Ha` holds for `[boxType]`, the `g`, `SP - 80` (the two frames) and
the runtime's view of the memory at the callback's entry. -/
def ROK (rt : List (Nat × Nat)) (Ha : RtReady) (u : State) : Prop :=
  Outside (u.sp.toNat - gsBox) (gsBox + 16) rt ∧
    Ha [boxType] (u.regs 28).toNat (u.sp.toNat - 80) (rtView rt u.mem)

def GoPre (rt : List (Nat × Nat)) (Ha : RtReady) (a : W64) (u : State) : Prop :=
  GuardOK u 32 ∧ StackOK u gsBox 16 ∧
    Outside ((u.regs 28).toNat + 16) 8 [(u.sp.toNat - gsBox, u.sp.toNat + 16)] ∧
    a.toNat + 16 ≤ 2 ^ 48 ∧ u.mem.accessible a.toNat 16 true = true ∧
    Outside a.toNat 16 [(u.sp.toNat - gsBox, u.sp.toNat + 16)] ∧ Outside a.toNat 16 rt ∧
    TypeOK u.mem boxType ∧ typSize u.mem boxType = 8 ∧ typPtrBytes u.mem boxType = 0 ∧
    Outside boxType 16 [(u.sp.toNat - gsBox, u.sp.toNat + 16)] ∧ ROK rt Ha u

/-- The frame's result slot holds `p0 + 1`; the rest of memory changes only inside the
runtime-owned ranges and the goroutine stack. -/
def GoPost (rt : List (Nat × Nat)) (a : W64) (u u' : State) : Prop :=
  MemFrame (u.mem.writeLE (a.toNat + 8) 8 (u.mem.readLE a.toNat 8 + 1)) u'.mem
    (rt ++ [(u.sp.toNat - gsBox, u.sp.toNat + 16)])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem go_spec (impl : List Segment) (rt : List (Nat × Nat)) (Ha : RtReady)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 Ha) (a : W64) :
    EnsuresC (Extracted.program.link impl) Contract.none goFn [a] (GoPre rt Ha a) (GoPost rt a) := by
  intro ret hret u hu ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgo, hab, haw, hao, hart, ⟨ht1, ht2⟩, hts, hpb,
    hto, hrto, hH⟩
  simp only [outside_cons, outside_nil, and_true, gsBox] at hgo hao hto hrto hb hw
  janus_eval_nat h_bt : boxType
  rw [h_bt] at ht1 ht2 hts hpb hto hH
  simp only [typSize, typPtrBytes] at hts hpb
  have hgf : goFn = janus_eval% goFn := rfl
  apply ReturnsC.of_reaches
  janus_intro hu
  janus_run until [segAddr Extracted.program "example.com/cgo/cenv.newBox" + 0x28] calls [hnew.pos]
  simp only [hts, hpb, beq_self_eq_true, reduceBlockSize] at *
  have hdj := InRanges.disjoint ‹InRanges _ 8 rt› hrto
  have hdf := InRanges.disjoint ‹InRanges _ 8 rt› hart
  janus_run
  unfold GoPost
  apply MemFrame.writeLE_both
  have hf := ‹MemFrame _ _ (rt ++ _)›
  have hin := ‹InRanges _ 8 rt›
  refine ⟨fun b n hb => ?_, fun b n w => ?_⟩
  · simp only [outside_append, outside_cons, outside_nil, and_true, gsBox] at hb
    obtain ⟨hbr, hbw⟩ := hb
    have hd := InRanges.disjoint hin hbr
    rw [readLE_writeLE_disjoint _ _ (by omega), hf.readLE b n (by
      simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hbr, by omega, by omega⟩)]
    simp (disch := omega) only [readLE_writeLE_disjoint]
  · rw [Memory.accessible_writeLE, hf.accessible]
    simp only [Memory.accessible_writeLE]

/-! ## The C side, under the callback assumption -/

abbrev rid : Nat := CData.addr Extracted.cdata "runtime_init_done"
abbrev ctxf : Nat := CData.addr Extracted.cdata "cgo_context_function"
/-- `runtime.iscgo`, which `load_g` reads (`ADRP`+`LDRSB`). -/
def iscgo : Nat :=
  adrpLdTarget (segAddr Extracted.program "runtime.load_g.abi0")
    (segWord Extracted.program "runtime.load_g.abi0" 0) (segWord Extracted.program "runtime.load_g.abi0" 1) 0
/-- The GOT slot of `__stack_chk_guard` (a dynamic relocation: not part of the extracted data). -/
def gslot : Nat :=
  adrpLdTarget (segAddr Extracted.program "GoBox" + 0x14)
    (segWord Extracted.program "GoBox" 5) (segWord Extracted.program "GoBox" 6) 3

/-- The C stack `e_callbox` needs: `GoBox`'s and `crosscall2`'s frames (the stub at `SP - 256`)
and `cgocallback`'s. -/
abbrev win : Nat := 256 + cbStackScratch

/-- The frame `crosscall2` passes (`[SP+16]` at `cgocallback`). -/
def frameOf (S : State) : Nat := S.mem.readLE (S.sp.toNat + 16) 8

/-- At the stub: the stack window, the callback's readiness, the frame (C memory), no C memory
runtime-owned, and `box`'s type descriptor (read-only data the Go code passes to
`newobject`). -/
def G (rt : List (Nat × Nat)) (k : CbStack) (S : State) : Prop :=
  CStack S cbStackScratch 32 ∧ k.Ready Extracted.tls S ∧ frameOf S + 16 ≤ 2 ^ 48 ∧
    S.mem.accessible (frameOf S) 16 true = true ∧ Outside (frameOf S) 16 (cbClobber Extracted.tls S) ∧
    (∀ a n w, S.mem.accessible a n w = true → Outside a n rt) ∧
    boxType + 16 ≤ 2 ^ 48 ∧ S.mem.accessible boxType 16 false = true ∧ S.mem.readLE boxType 8 = 8 ∧
    S.mem.readLE (boxType + 8) 8 = 0 ∧ Outside boxType 16 (cbClobber Extracted.tls S)

def E (S : State) : Memory :=
  S.mem.writeLE (frameOf S + 8) 8 (S.mem.readLE (frameOf S) 8 + 1)

/-- Go's TLS `g` slot of the thread. -/
abbrev slot (s : State) : Nat := tlsGSlot Extracted.tls s.tpidr

def CPre (rt rtc : List (Nat × Nat)) (Hc : RtReady) (s : State) : Prop :=
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
  Outside ctxf 8 [(slot s, slot s + 8)] ∧ Outside boxType 16 [(slot s, slot s + 8)] ∧
  (∀ a n w, s.mem.accessible a n w = true → Outside a n rt) ∧
  Outside (s.sp.toNat - win) win rtc ∧
  Hc [goFn, gsBox] (s.mem.readLE (slot s) 8) (s.sp.toNat - 256) (rtView rtc s.mem)

theorem bit_4_2 : Janus.Arm64.bit 4 2 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem c_spec (impl : List Segment) (rt rtc : List (Nat × Nat)) (Hc : RtReady) (x : W64) :
    CEnsuresC (Extracted.program.link impl) (CallbackSpec Extracted.tls goFn (G rt (cbk rtc Hc)) E) Extracted.entry [x]
      (CPre rt rtc Hc) (fun _ s' => s'.regs 0 = x + 1) := by
  intro ret hret s hs hpre
  obtain ⟨hd, ⟨hal, hb, ha, hw⟩, hra, hrv, hca, hcv, hia, hio, htb, hta, hga, hgpa, hro, hco, hgo, hgpo, hto, hgt,
    hgpt, hct, hbt, hcrt, hrt, hH⟩ := hpre
  have et : Extracted.tls.a64Off + Extracted.tls.varOff "runtime.tls_g" =
      janus_eval% (Extracted.tls.a64Off + Extracted.tls.varOff "runtime.tls_g") := rfl
  have hsl : slot s = s.tpidr.toNat + janus_eval% (Extracted.tls.a64Off + Extracted.tls.varOff "runtime.tls_g") := by
    simp only [slot, tlsGSlot, TLSImage.a64Addr, Nat.add_assoc, et]
  rw [hsl] at htb hta hto hgt hgpt hct hbt hH
  have e1 : rid = janus_eval% rid := rfl
  have e2 : ctxf = janus_eval% ctxf := rfl
  have e3 : iscgo = janus_eval% iscgo := rfl
  have e4 : gslot = janus_eval% gslot := rfl
  have e5 : boxType = janus_eval% boxType := rfl
  rw [e1] at hra hrv hro
  rw [e2] at hca hcv hco hct
  rw [e3] at hia hio
  rw [e4] at hga hgpa hgo hgpo hgt hgpt
  rw [e5] at hbt
  simp only [outside_cons, outside_nil, and_true, win, cbStackScratch] at hro hco hgo hgpo hto hb hw hgt hgpt hct hio hbt
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
      TLSImage.a64Addr, Nat.add_assoc, et, e5, outside_cons, outside_nil, and_true]
    simp (disch := omega) only [hv]
    janus_simp
    rw [hgf] at hH
    exact ⟨⟨by omega, by omega, by omega, Memory.accessible_mono _ hw (by omega) (by omega)⟩, hH, by omega,
      Memory.accessible_mono _ hw (by omega) (by omega), ⟨by omega, by omega, by omega⟩, hcrt,
      Memory.accessible_mono _ ‹s.mem.accessible (janus_eval% boxType) 256 false = true› (by omega) (by omega),
      by omega, by omega, by omega⟩)
  all_goals (rintro s' ⟨-, m, ⟨regs, flags, vregs, fpsr, excl, rfl⟩, hmf⟩)
  all_goals (simp only [E, frameOf, cbClobber, cbStackScratch, tlsGSlot, TLSImage.a64Addr, Nat.add_assoc, et,
    h256] at hmf)
  all_goals (apply ReturnsC.of_reaches; janus_run [bit_4_2])
  all_goals
    refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-! ## Composition: the Go function's theorem discharges the callback assumption -/

theorem frame_lt (S : State) : frameOf S < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Memory.readLE_lt _ _ _) (by decide)

theorem refines (impl : List Segment) (rt : List (Nat × Nat)) (Ha : RtReady)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 Ha) (rtc : List (Nat × Nat)) (Hc : RtReady) :
    (CgoCallback Extracted.tls (Extracted.program.link impl) Contract.none (ROK rt Ha) (cbk rtc Hc)).Refines
      (CallbackSpec Extracted.tls goFn (G rt (cbk rtc Hc)) E) := by
  refine CgoCallback.refines (fun a => go_spec impl rt Ha hnew a) (fun S hG => hG.1) (fun S hG => hG.2.1) ?_
    (fun _ _ => rfl) ?_ ?_
  · rintro S u ret ⟨-, -, hb, hacc, hout, hcrt, hbb, hba, hb8, hb0, hbo⟩ he hR
    have hf : (BitVec.ofNat 64 (S.mem.readLE (S.sp.toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    have hsep := he.stackSep _ _ _ hacc
    have hsepb := he.stackSep _ _ _ hba
    have hgo := he.gOff
    have hk8 : u.mem.readLE boxType 8 = S.mem.readLE boxType 8 :=
      he.kept _ _ ⟨Memory.accessible_mono _ hba (Nat.le_refl _) (by omega), Outside.of_sub hbo (Nat.le_refl _) (by omega)⟩
    have hk0 : u.mem.readLE (boxType + 8) 8 = S.mem.readLE (boxType + 8) 8 :=
      he.kept _ _ ⟨Memory.accessible_mono _ hba (by omega) (by omega), Outside.of_sub hbo (by omega) (by omega)⟩
    simp only [cbk, gsBox] at hsep hsepb hgo
    simp only [outside_cons, outside_nil, and_true] at hsep hsepb hgo
    unfold GoPre
    rw [hf]
    refine ⟨he.guardOK (by simp only [cbk, gsBox, stackGuard]; decide), he.goStack, ?_, hb,
      he.keptAcc _ _ _ ⟨hacc, hout⟩, ?_, hcrt _ _ _ hacc, ⟨hbb, he.keptAcc _ _ _ ⟨hba, hbo⟩⟩,
      by simp only [typSize]; rw [hk8, hb8], by simp only [typPtrBytes]; rw [hk0, hb0], ?_, hR⟩
    · simp only [outside_cons, outside_nil, and_true, gsBox, gStructSize] at hgo ⊢; omega
    · simp only [outside_cons, outside_nil, and_true, gsBox]; omega
    · simp only [outside_cons, outside_nil, and_true, gsBox]; omega
  · rintro S u ret u' ⟨-, -, hb, hacc, hout, hcrt, -⟩ he - - hpost b hb' hbacc
    have hf : (BitVec.ofNat 64 (S.mem.readLE (S.sp.toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    unfold GoPost at hpost
    rw [hf] at hpost
    have hsep := he.stackSep _ _ _ hbacc
    simp only [cbk] at hsep
    have h1 := hpost.readLE b 1 (by
      simp only [outside_append]; exact ⟨hcrt _ _ _ hbacc, hsep⟩)
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
  · rintro S ⟨-, -, hb, hacc, hout, -⟩ b _ hna
    rw [E, Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`e_callbox` end to end**: under the trusted `cgocallback` contract (with the allocator's
readiness `ROK rt Ha` at the Go entry) and the allocation contract `hnew`, for every runtime
memory `rt`, `rtc` and readinesses `Ha`, `Hc`, the call returns `x + 1`. -/
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (Ha : RtReady)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 Ha)
    (rtc : List (Nat × Nat)) (Hc : RtReady) (x : W64) :
    CEnsuresC (Extracted.program.link impl)
      (CgoCallback Extracted.tls (Extracted.program.link impl) Contract.none (ROK rt Ha) (cbk rtc Hc))
      Extracted.entry [x] (CPre rt rtc Hc) (fun _ s' => s'.regs 0 = x + 1) :=
  (c_spec impl rt rtc Hc x).refine (refines impl rt Ha hnew rtc Hc)

end Proof
