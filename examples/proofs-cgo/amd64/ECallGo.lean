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
is readable and the C stack has room for the frames and `cgocallback`'s scratch, returns `2x + 1
(mod 2^64)` restoring the callee-saved state, **under the trusted contract `CgoCallback`
alone** (for this binary's TLS image: Go's `g` slot is `runtime.tlsg` at `FS − 24`, the C code
having `__thread` variables).

**How.** `go_spec` (the Go function, `EnsuresC`), `c_spec` (the C side under `CallbackSpec`),
`refines` (`CgoCallback.refines`, the reverse composition theorem).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI

namespace Proof

abbrev goFn : Nat := segAddr Extracted.program "_cgoexp_4a03c2e7d4cf_GoTwice"

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

def G (S : State) : Prop :=
  CbStack S ∧ frameOf S + 16 ≤ 2 ^ 48 ∧ S.mem.accessible (frameOf S) 16 true = true ∧
    Outside (frameOf S) 16 (cbClobber Extracted.tls S)

def E (S : State) : Janus.Arm64.Memory :=
  S.mem.writeLE (frameOf S + 8) 8 (2 * S.mem.readLE (frameOf S) 8)

def CPre (s : State) : Prop :=
  Extracted.program.DataLoaded s.mem ∧ CStack s win 8 ∧
  s.mem.accessible rid 4 false = true ∧ s.mem.readLE rid 4 = 2 ∧
  s.mem.accessible ctxf 8 false = true ∧ s.mem.readLE ctxf 8 = 0 ∧
  s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ 24 ≤ s.fsBase.toNat ∧ s.mem.accessible (s.fsBase.toNat + 40) 8 false = true ∧
  Outside rid 4 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside ctxf 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat + 40) 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 24) 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside ctxf 8 [(s.fsBase.toNat - 24, s.fsBase.toNat - 16)] ∧
  Outside rid 4 [(s.fsBase.toNat - 24, s.fsBase.toNat - 16)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem c_spec (x : W64) :
    CEnsuresC Extracted.program (CallbackSpec Extracted.tls goFn G E) Extracted.entry [x] CPre
      (fun _ s' => s'.regs 0 = 2 * x + 1) := by
  intro ret hret s hs hpre
  obtain ⟨hd, ⟨hal, hb, ha, hw⟩, hra, hrv, hca, hcv, hfb, hfl, hga, hro, hco, hgo, hto, hct, hrt⟩ := hpre
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
  have et1 : Extracted.tls.x64Off = janus_eval% Extracted.tls.x64Off := rfl
  have et2 : Extracted.tls.varOff "runtime.tlsg" = janus_eval% (Extracted.tls.varOff "runtime.tlsg") := rfl
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp
  · simp only [G, frameOf, cbClobber, CbStack, cbStackScratch, TLSImage.x64Addr, et1, et2, outside_cons,
      outside_nil, and_true]
    janus64_simp
    exact ⟨⟨by omega, by omega, Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)⟩, by omega,
      Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega), by omega, by omega, by omega⟩
  · rintro s' ⟨-, m, ⟨regs, flags, xmm, ymmHi, mx, rfl, hr4, hmx⟩, hmf⟩
    simp only [E, frameOf, cbClobber, cbStackScratch, TLSImage.x64Addr, et1, et2, setRegF_apply, ↓reduceIte,
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

theorem refines :
    (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True)).Refines
      (CallbackSpec Extracted.tls goFn G E) := by
  refine CgoCallback.refines (fun a => go_spec a) (fun S hG => hG.1) ?_ (fun _ _ => rfl) ?_ ?_
  · rintro S u ret ⟨-, hb, hacc, hout⟩ he -
    have hf : (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    obtain ⟨g1, g2, g3⟩ := he.goStack
    have hsep := he.stackSep _ _ _ hacc
    simp only [outside_cons, outside_nil, and_true] at hsep
    refine ⟨by rw [hf]; exact hb, by rw [hf]; exact he.keptAcc _ _ _ ⟨hacc, hout⟩, g2,
      Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ g3 (by omega) (by omega)), ?_⟩
    rw [hf]; simp only [outside_cons, outside_nil, and_true, cbGoStack] at hsep ⊢; omega
  · rintro S u ret u' ⟨-, hb, hacc, hout⟩ he - - hpost b hb' hbacc
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
  · rintro S ⟨-, hb, hacc, hout⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`e_callgo` end to end** (amd64), under the trusted `cgocallback` contract only. -/
theorem correctness (x : W64) :
    CEnsuresC Extracted.program (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True))
      Extracted.entry [x] CPre (fun _ s' => s'.regs 0 = 2 * x + 1) :=
  (c_spec x).refine refines

end Proof
