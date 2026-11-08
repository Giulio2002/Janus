import Extracted

/-!
# `int64_t e_callgo(int64_t x)` (C, arm64) calls the exported Go function `GoTwice`: C → Go,
# composed end to end

```c
int64_t e_callgo(int64_t x) { return GoTwice(x) + 1; }   /* GoTwice: //export, returns 2x */
```

`GoTwice` here is the C function cgo generates for `//export GoTwice`: it waits for the runtime
(`_cgo_wait_runtime_init_done`), packs `x` into a frame, calls `crosscall2(_cgoexp_…_GoTwice,
&frame, 16, ctxt)`, releases the context and returns the frame's result; it is compiled with the
stack protector. `crosscall2` and `load_g` (Go assembly) save the callee-saved registers and load
`g`, and call `runtime.cgocallback`, which runs the Go function `_cgoexp_…_GoTwice` (the Go side
of the export: `frame.r0 = GoTwice(frame.p0)`, inlined to `2 * p0`).

**Guarantee (`correctness`).** For every `x`, every AAPCS64 call of `e_callgo` in a state where
the runtime is initialised (`runtime_init_done = 2`, no `SetCgoTraceback` context function), the
stack protector's guard and Go's TLS `g` slot (`tlsGSlot Extracted.tls`) are readable, the C
stack has room for the frames and for `cgocallback` (`cbStackScratch`) and lies outside the
runtime-owned memory `rt`, and the runtime is ready to enter the Go code with a 4096-byte
goroutine stack (`H`, for every readiness predicate `H`: `CbStack`), returns `2x + 1 (mod 2^64)`
restoring the callee-saved state, **under the trusted contract `CgoCallback` alone**: every
instruction of the C code, of `crosscall2`, `load_g` and of the Go function is executed by the
model.

**How.** `go_spec` proves the Go function (`EnsuresC`); `c_spec` proves the C side under the
assumption `CallbackSpec` (the callback stores `2 * p0` in the frame's result slot);
`CgoCallback.refines` (the reverse composition theorem) turns the second into a theorem under the
trusted contract.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI

namespace Proof

abbrev goFn : Nat := exportAddr Extracted.program "GoTwice"

/-! ## The Go side -/

def GoPre (a : W64) (u : State) : Prop := a.toNat + 16 ≤ 2 ^ 48 ∧ u.mem.accessible a.toNat 16 true = true

def GoPost (a : W64) (u u' : State) : Prop :=
  u'.mem = u.mem.writeLE (a.toNat + 8) 8 (2 * u.mem.readLE a.toNat 8)

theorem go_spec (a : W64) : EnsuresC Extracted.program Contract.none goFn [a] (GoPre a) (GoPost a) := by
  intro ret hret u hu ⟨hb, hacc⟩
  apply ReturnsC.of_reaches
  janus_intro hu
  janus_run
  unfold GoPost
  rw [show u.mem.readLE a.toNat 8 + u.mem.readLE a.toNat 8 = 2 * u.mem.readLE a.toNat 8 by omega]

/-! ## The C side, under the callback assumption -/

abbrev rid : Nat := CData.addr Extracted.cdata "runtime_init_done"
abbrev ctxf : Nat := CData.addr Extracted.cdata "cgo_context_function"
/-- `runtime.iscgo`, which `load_g` reads (`ADRP`+`LDRSB`). -/
def iscgo : Nat :=
  Janus.Spec.adrpLdTarget (segAddr Extracted.program "runtime.load_g.abi0")
    (Janus.Spec.segWord Extracted.program "runtime.load_g.abi0" 0) (Janus.Spec.segWord Extracted.program "runtime.load_g.abi0" 1) 0
/-- The GOT slot of `__stack_chk_guard` (an `R_AARCH64_GLOB_DAT` relocation: the dynamic linker
fills it; named by the relocation's symbol, `Extracted.dyngot`). -/
def gslot : Nat := DynGOT.slotOf Extracted.dyngot "__stack_chk_guard"

/-- The C stack `e_callgo` needs: its frames and `cgocallback`'s. -/
abbrev win : Nat := 16656

/-- The goroutine stack the callback gets: 4096 bytes, under the readiness `H` of the runtime
memory `rt`. -/
def cbk (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) : CbStack := ⟨cbGoStack, rt, H⟩

/-- The frame `crosscall2` passes (`[SP+16]` at `cgocallback`). -/
def frameOf (S : State) : Nat := S.mem.readLE (S.sp.toNat + 16) 8

def G (k : CbStack) (S : State) : Prop :=
  CStack S cbStackScratch 32 ∧ k.Ready Extracted.tls S ∧ frameOf S + 16 ≤ 2 ^ 48 ∧
    S.mem.accessible (frameOf S) 16 true = true ∧ Outside (frameOf S) 16 (cbClobber Extracted.tls S)

def E (S : State) : Memory :=
  S.mem.writeLE (frameOf S + 8) 8 (2 * S.mem.readLE (frameOf S) 8)

/-- Go's TLS `g` slot of the thread. -/
abbrev slot (s : State) : Nat := tlsGSlot Extracted.tls s.tpidr

def CPre (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (s : State) : Prop :=
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
  Outside (s.sp.toNat - win) win rt ∧
  H [goFn, cbGoStack] (s.mem.readLE (slot s) 8) (s.sp.toNat - 272) (Janus.Contracts.rtView rt s.mem)

theorem bit_4_2 : Janus.Arm64.bit 4 2 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem c_spec (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (x : W64) :
    CEnsuresC Extracted.program (CallbackSpec Extracted.tls goFn (G (cbk rt H)) E) Extracted.entry [x]
      (CPre rt H) (fun _ s' => s'.regs 0 = 2 * x + 1) := by
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
  simp only [outside_cons, outside_nil, and_true, win] at hro hco hgo hgpo hto hb hw hgt hgpt hct hio
  simp only [win] at hrt
  have hv : ∀ (m : Memory) a n v, s.sp.toNat - 16656 ≤ a → a + n ≤ s.sp.toNat →
      Janus.Contracts.rtView rt (m.writeLE a n v) = Janus.Contracts.rtView rt m :=
    fun _ _ _ _ h1 h2 => Janus.Contracts.rtView_writeLE (Outside.of_sub hrt h1 (by omega))
  apply ReturnsC.of_reaches
  janus_intro hs.call
  janus_data hd [hw]
  have hrv32 : (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (janus_eval% rid) 4))).toNat = 2 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := Memory.readLE_lt s.mem (janus_eval% rid) 4; omega
  have hgf : goFn = janus_eval% goFn := rfl
  have h272 : (s.sp - 272#64).toNat = s.sp.toNat - 272 := by
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
      Memory.accessible_mono _ hw (by omega) (by omega), by omega, by omega, by omega⟩)
  all_goals (rintro s' ⟨-, m, ⟨regs, flags, vregs, fpsr, excl, rfl⟩, hmf⟩)
  all_goals (simp only [E, frameOf, cbClobber, cbStackScratch, tlsGSlot, TLSImage.a64Addr, Nat.add_assoc, et,
    h272] at hmf)
  all_goals (apply ReturnsC.of_reaches; janus_run [bit_4_2])
  all_goals
    refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega


/-! ## Composition: the Go function's theorem discharges the callback assumption -/

theorem frame_lt (S : State) : frameOf S < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Memory.readLE_lt _ _ _) (by decide)

theorem refines (k : CbStack) :
    (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True) k).Refines
      (CallbackSpec Extracted.tls goFn (G k) E) := by
  refine CgoCallback.refines (fun a => go_spec a) (fun S hG => hG.1) (fun S hG => hG.2.1) ?_
    (fun _ _ => rfl) ?_ ?_
  · rintro S u ret ⟨-, -, hb, hacc, hout⟩ he -
    have hf : (BitVec.ofNat 64 (S.mem.readLE (S.sp.toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    refine ⟨by rw [hf]; exact hb, ?_⟩
    rw [hf]; exact he.keptAcc _ _ _ ⟨hacc, hout⟩
  · rintro S u ret u' ⟨-, -, hb, hacc, hout⟩ he - - hpost b hb' hbacc
    have hf : (BitVec.ofNat 64 (S.mem.readLE (S.sp.toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    unfold GoPost at hpost
    rw [hpost, hf, E, Memory.bytes_writeLE, Memory.bytes_writeLE]
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

/-- **`e_callgo` end to end**, under the trusted `cgocallback` contract only, for every runtime
memory `rt` and readiness `H` of the 4096-byte goroutine stack. -/
theorem correctness (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (x : W64) :
    CEnsuresC Extracted.program
      (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True) (cbk rt H))
      Extracted.entry [x] (CPre rt H) (fun _ s' => s'.regs 0 = 2 * x + 1) :=
  (c_spec rt H x).refine (refines _)

namespace Witness

open Janus.Spec Janus.Contracts

/-- A byte of the program's read-only data, if `a` is in one of its objects. -/
def dbyte (a : Nat) : Option Nat :=
  Extracted.program.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

/-- Little-endian byte `j` of `v`. -/
def byteOf (v j : Nat) : Nat := v / 256 ^ j % 256

/-- The witness call: the C stack ends at `SP0`, the thread pointer is `TP`, the guard at
`GUARD`, the return address `RET` (no code there). -/
def SP0 : Nat := 0x1000000
def TP : Nat := 0x800000
def GUARD : Nat := 0x900000
def RET : Nat := 0x1000

/-- The witness memory: the read-only data in read-only regions, `runtime_init_done = 2`, no
context function, `runtime.iscgo`, the TLS `g` slot, the guard's GOT slot holding `GUARD`, the
guard, and the C stack. -/
def mem0 : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyte a).getD
      (if a = rid then 2 else if gslot ≤ a ∧ a < gslot + 8 then byteOf GUARD (a - gslot) else 0)),
    [⟨rid, 4, true⟩, ⟨ctxf, 8, true⟩, ⟨iscgo, 1, true⟩, ⟨TP + 16, 8, true⟩, ⟨gslot, 8, false⟩,
     ⟨GUARD, 8, false⟩, ⟨SP0 - win, win, true⟩] ++
      Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 0 then 7#64 else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0, tpidr := BitVec.ofNat 64 TP }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [7#64] s0 :=
  ⟨⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩, by decide, by decide⟩

theorem data : Extracted.program.DataLoaded mem0 :=
  -- not `decide +kernel` over every byte (114 s: each byte scans the object list): the objects are disjoint and every
  -- address reads as `dataSegByte` does (Janus/Program.lean)
  Program.DataLoaded_of_dataSegByte (by unfold DataSegsDisjoint; decide +kernel) (by decide +kernel) (by decide +kernel) fun a n h => by
    have h' : dbyte a = some n := h
    show (BitVec.ofNat 8 ((dbyte a).getD _)).toNat = n % 256
    rw [h']
    simp

set_option maxRecDepth 100000 in
theorem pre : CPre [] (fun _ _ _ _ => True) s0 := by
  refine ⟨data, ?_⟩
  repeat' (first | exact trivial | apply And.intro)
  all_goals first
    | decide +kernel
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | trivial

/-- All hypotheses of `correctness` hold together (for the readiness that always holds and no
runtime-owned memory). -/
theorem nonvacuous : ∃ (rtc : List (Nat × Nat)) (Hc : RtReady) (x : W64) (ret : Nat) (s : State),
    RetAddr Extracted.program ret ∧ CCall (Extracted.program.withExit ret) Extracted.entry [x] s ∧
      CPre rtc Hc s ∧
      ReturnsC (Extracted.program.withExit ret)
        (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True) (cbk rtc Hc))
        (fun s' => CReturn s s' ∧ (s'.regs 0 = 2 * x + 1)) s :=
  ⟨[], fun _ _ _ _ => True, 7#64, RET, s0, hret, call, pre,
    correctness [] (fun _ _ _ _ => True) 7#64 RET hret s0 call pre⟩

end Witness

end Proof
