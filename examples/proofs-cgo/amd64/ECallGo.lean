import Extracted

/-!
# `int64_t e_callgo(int64_t x)` (C, amd64) calls the exported Go function `GoTwice`: C → Go,
# composed end to end

```c
int64_t e_callgo(int64_t x) { return GoTwice(x) + 1; }   /* GoTwice: //export, returns 2x */
```

The x86-64 counterpart of the arm64 proof. `GoTwice` (cgo's C wrapper, with the stack
protector) waits for the runtime (`_cgo_wait_runtime_init_done`), packs `x` into a 16-byte frame
on its stack, calls `crosscall2(_cgoexp_…_GoTwice, &frame, 16, ctxt)` (Go assembly: saves `RBX
RBP R12–R15`, passes `fn`, `frame`, `ctxt` at `[RSP]`, `[RSP+8]`, `[RSP+16]` and calls
`runtime.cgocallback`), releases the context and returns the frame's result. The Go side is
`_cgoexp_…_GoTwice` (ABIInternal, `RAX` the frame: `frame.r0 = 2 * frame.p0`).

**Guarantee (`correctness`).** For every `x`, every System V call of `e_callgo` in a state where
the runtime is initialised (`runtime_init_done = 2`, no context function), the guard `%fs:0x28`
is readable, the C stack has room for the frames and `cgocallback`'s scratch and lies outside
the runtime-owned memory `rt`, and the runtime is ready to enter the Go code with a 4096-byte
goroutine stack (`H`, for every readiness predicate `H`), returns `2x + 1
(mod 2^64)` restoring the callee-saved state, **under the trusted contract `CgoCallback`
alone** (for this binary's TLS image: Go's `g` slot is `runtime.tlsg` at `FS − 24`, the C code
having `__thread` variables).

**How.** `go_spec` (the Go function, `EnsuresC`), `c_spec` (the C side under `CallbackSpec`),
`refines` (`CgoCallback.refines`, the reverse composition theorem).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI

namespace Proof

abbrev goFn : Nat := exportAddr Extracted.program "GoTwice"

/-! ## The Go side -/

def GoPre (a : W64) (u : State) : Prop :=
  a.toNat + 16 ≤ 2 ^ 48 ∧ u.mem.accessible a.toNat 16 true = true ∧
    (u.regs 4).toNat + 8 ≤ 2 ^ 48 ∧ u.mem.accessible (u.regs 4).toNat 8 false = true ∧
    Outside a.toNat 16 [((u.regs 4).toNat, (u.regs 4).toNat + 8)]

def GoPost (a : W64) (u u' : State) : Prop :=
  u'.mem = u.mem.writeLE (a.toNat + 8) 8 (2 * u.mem.readLE a.toNat 8)

theorem go_spec (a : W64) : EnsuresC Extracted.program Contract.none goFn [a] (GoPre a) (GoPost a) := by
  intro ret hret u hu ⟨hb, hacc, hsb, hsa, hout⟩
  simp only [outside_cons, outside_nil, and_true] at hout
  apply ReturnsC.of_reaches
  janus64_intro hu
  janus64_run
  unfold GoPost
  rw [show u.mem.readLE a.toNat 8 + u.mem.readLE a.toNat 8 = 2 * u.mem.readLE a.toNat 8 by omega]

/-! ## The C side, under the callback assumption -/

abbrev rid : Nat := CData.addr Extracted.cdata "runtime_init_done"
abbrev ctxf : Nat := CData.addr Extracted.cdata "cgo_context_function"

/-- The C stack `e_callgo` needs: its frames (down to the `cgocallback` stub at `RSP − 168`) and
`cgocallback`'s scratch. -/
abbrev win : Nat := 168 + cbStackScratch

/-- The frame `crosscall2` passes (`[RSP+16]` at `cgocallback`). -/
def frameOf (S : State) : Nat := S.mem.readLE ((S.regs 4).toNat + 16) 8

/-- The goroutine stack the callback gets: 4096 bytes, under the readiness `H` of the runtime
memory `rt`. -/
def cbk (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) : Janus.FFI.CbStack := ⟨cbGoStack, rt, H⟩

def G (k : Janus.FFI.CbStack) (S : State) : Prop :=
  CbStack S ∧ CbReady k Extracted.tls S ∧ frameOf S + 16 ≤ 2 ^ 48 ∧ S.mem.accessible (frameOf S) 16 true = true ∧
    Outside (frameOf S) 16 (cbClobber Extracted.tls S)

def E (S : State) : Janus.Arm64.Memory :=
  S.mem.writeLE (frameOf S + 8) 8 (2 * S.mem.readLE (frameOf S) 8)

def CPre (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (s : State) : Prop :=
  Extracted.program.DataLoaded s.mem ∧ CStack s win 8 ∧
  s.mem.accessible rid 4 false = true ∧ s.mem.readLE rid 4 = 2 ∧
  s.mem.accessible ctxf 8 false = true ∧ s.mem.readLE ctxf 8 = 0 ∧
  s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ 24 ≤ s.fsBase.toNat ∧ s.mem.accessible (s.fsBase.toNat + 40) 8 false = true ∧
  Outside rid 4 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside ctxf 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat + 40) 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 24) 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside ctxf 8 [(s.fsBase.toNat - 24, s.fsBase.toNat - 16)] ∧
  Outside rid 4 [(s.fsBase.toNat - 24, s.fsBase.toNat - 16)] ∧
  Outside ((s.regs 4).toNat - win) win rt ∧
  H [goFn, cbGoStack] (s.mem.readLE (tlsGSlot Extracted.tls s.fsBase) 8) ((s.regs 4).toNat - 168)
    (Janus.Contracts.rtView rt s.mem)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem c_spec (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (x : W64) :
    CEnsuresC Extracted.program (CallbackSpec Extracted.tls goFn (G (cbk rt H)) E) Extracted.entry [x]
      (CPre rt H) (fun _ s' => s'.regs 0 = 2 * x + 1) := by
  intro ret hret s hs hpre
  obtain ⟨hd, ⟨hal, hb, ha, hw⟩, hra, hrv, hca, hcv, hfb, hfl, hga, hro, hco, hgo, hto, hct, hrt, hrtw, hH⟩ := hpre
  have et1 : Extracted.tls.x64Off = janus_eval% Extracted.tls.x64Off := rfl
  have et2 : Extracted.tls.varOff "runtime.tlsg" = janus_eval% (Extracted.tls.varOff "runtime.tlsg") := rfl
  simp only [tlsGSlot, TLSImage.x64Addr, et1, et2] at hH
  simp only [win, cbStackScratch] at hrtw
  have hv : ∀ (m : Janus.Arm64.Memory) a n v, (s.regs 4).toNat - (168 + 16384) ≤ a → a + n ≤ (s.regs 4).toNat →
      Janus.Contracts.rtView rt (m.writeLE a n v) = Janus.Contracts.rtView rt m :=
    fun _ _ _ _ h1 h2 => Janus.Contracts.rtView_writeLE (Outside.of_sub hrtw h1 (by omega))
  have e1 : rid = janus_eval% rid := rfl
  have e2 : ctxf = janus_eval% ctxf := rfl
  rw [e1] at hra hrv hro hrt
  rw [e2] at hca hcv hco hct
  simp only [outside_cons, outside_nil, and_true, win, cbStackScratch] at hro hco hgo hto hb hw hct hrt
  simp only [CABI.regSP] at hal hb ha hw
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = x := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  have hr47 : ret < 2 ^ 47 := hret.user
  apply ReturnsC.of_reaches
  janus64_data hd [hw]
  have hgf : goFn = janus_eval% goFn := rfl
  have h72 : ((s.regs 4).toNat - 72) % 16 = 0 := by omega
  janus64_run [h72]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp
  · simp only [G, frameOf, cbClobber, CbStack, cbStackScratch, CbReady, cbk, tlsGSlot, TLSImage.x64Addr, et1, et2,
      outside_cons, outside_nil, and_true]
    simp (disch := omega) only [hv]
    janus64_simp
    rw [hgf] at hH
    exact ⟨⟨by omega, by omega, Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)⟩, hH, by omega,
      Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega), by omega, by omega, by omega⟩
  · rintro s' ⟨-, m, ⟨regs, flags, xmm, ymmHi, mx, zh, kr, rfl, hr4, hmx⟩, hmf⟩
    simp only [E, frameOf, cbClobber, cbStackScratch, tlsGSlot, TLSImage.x64Addr, et1, et2, setRegF_apply, ↓reduceIte,
      Nat.reduceEqDiff] at hmf
    have h168 : (s.regs 4 - 168#64).toNat = (s.regs 4).toNat - 168 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    rw [h168] at hmf
    simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff] at hr4
    have h160 : (s.regs 4 - 168#64 + 8) = s.regs 4 - 160#64 := by
      apply BitVec.eq_of_toNat_eq
      show ((s.regs 4 - 168#64) + 8#64).toNat = _
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [h160] at hr4
    have hregs : regs = setRegF regs 4 (s.regs 4 - 160#64) := by
      funext i; simp only [setRegF]; split <;> simp_all
    rw [hregs]
    apply ReturnsC.of_reaches
    janus64_run
    refine ⟨hmx, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]


/-! ## Composition: the Go function's theorem discharges the callback assumption -/

theorem frame_lt (S : State) : frameOf S < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Janus.Arm64.Memory.readLE_lt _ _ _) (by decide)

theorem refines (k : Janus.FFI.CbStack) :
    (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True) k).Refines
      (CallbackSpec Extracted.tls goFn (G k) E) := by
  refine CgoCallback.refines (fun a => go_spec a) (fun S hG => hG.1) (fun S hG => hG.2.1) ?_
    (fun _ _ => rfl) ?_ ?_
  · rintro S u ret ⟨-, -, hb, hacc, hout⟩ he -
    have hf : (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    obtain ⟨g1, g2, g3⟩ := he.goStack
    have hsep := he.stackSep _ _ _ hacc
    simp only [outside_cons, outside_nil, and_true] at hsep
    refine ⟨by rw [hf]; exact hb, by rw [hf]; exact he.keptAcc _ _ _ ⟨hacc, hout⟩, by omega,
      Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ g3 (by omega) (by omega)), ?_⟩
    rw [hf]; simp only [outside_cons, outside_nil, and_true] at hsep ⊢; omega
  · rintro S u ret u' ⟨-, -, hb, hacc, hout⟩ he - - hpost b hb' hbacc
    have hf : (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    unfold GoPost at hpost
    rw [hpost, hf, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk8 : u.mem.readLE (frameOf S) 8 = S.mem.readLE (frameOf S) 8 :=
      he.kept _ _ ⟨Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hacc)
        (Nat.le_refl _) (by omega), Outside.of_sub hout (Nat.le_refl _) (by omega)⟩
    rw [hk8]
    split
    · rfl
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro S ⟨-, -, hb, hacc, hout⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`e_callgo` end to end** (amd64), under the trusted `cgocallback` contract only. -/
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

/-- The witness call: `RSP = SP0` (its slot holding `RET`, where there is no code), `FS = FS0`. -/
def SP0 : Nat := 0x1000008
def FS0 : Nat := 0x800000
def RET : Nat := 0x1000

def mem0 : Janus.Arm64.Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyte a).getD
      (if a = rid then 2 else if SP0 ≤ a ∧ a < SP0 + 8 then byteOf RET (a - SP0) else 0)),
    [⟨rid, 4, true⟩, ⟨ctxf, 8, true⟩, ⟨FS0 - 24, 8, true⟩, ⟨FS0 + 40, 8, false⟩,
     ⟨SP0 - win, win + 8, true⟩] ++
      Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 7 then 7#64 else if i = 4 then BitVec.ofNat 64 SP0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 FS0 }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [7#64] s0 :=
  ⟨rfl, by decide +kernel, by decide, by intro i h; simp at h; subst h; rfl, by decide, rfl⟩

theorem data : Extracted.program.DataLoaded mem0 := by
  unfold Amd64.Program.DataLoaded; decide +kernel

set_option maxRecDepth 100000 in
theorem pre : CPre [] (fun _ _ _ _ => True) s0 := by
  refine ⟨data, ?_⟩
  repeat' (first | exact trivial | apply And.intro)
  all_goals first
    | decide +kernel
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | trivial

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (x : W64) (ret : Nat) (s : State),
    RetAddr Extracted.program ret ∧ CCall (Extracted.program.withExit ret) Extracted.entry [x] s ∧
      CPre rt H s ∧
      ReturnsC (Extracted.program.withExit ret)
        (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True) (cbk rt H))
        (fun s' => CReturn s s' ∧ (s'.regs 0 = 2 * x + 1)) s :=
  ⟨[], fun _ _ _ _ => True, 7#64, RET, s0, hret, call, pre,
    correctness [] (fun _ _ _ _ => True) 7#64 RET hret s0 call pre⟩

end Witness

end Proof
