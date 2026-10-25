import Extracted

/-!
# `int e_setjmp(int v)` (C, arm64): `setjmp` and a non-local `longjmp` back to it

```c
static jmp_buf e_env;
static void e_thrower(int v) { if (v) longjmp(e_env, v); }   /* __longjmp_chk under FORTIFY */
int e_setjmp(int v) { if (setjmp(e_env)) return 1; e_thrower(v); return 0; }
```

**Guarantee.** For every `jmp_buf` model `J` (glibc's layout and pointer mangling are not
assumed: any model with the laws of `JmpModel`), every `v`, and every AAPCS64 call of the
gcc-compiled `e_setjmp` with the static `jmp_buf` `e_env` writable and a stack window for the
calls, the call returns without faulting, restores the callee-saved state (`CReturn`), and
returns `1` if `W0 = v ≠ 0` (through `longjmp`: `_setjmp` returns a second time, with `v`) and `0`
otherwise. Every accessible byte outside `e_env` and the stack below `SP` is unchanged. This
holds under the trusted contract `SetJmp J` only.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI Janus.Contracts.Libc

namespace Proof

abbrev env : Nat := CData.addr Extracted.cdata "e_env"

def Pre (s : State) : Prop :=
  CStack s (libcStack + 48) 0 ∧ env + jmpBufSize ≤ 2 ^ 48 ∧ s.mem.accessible env jmpBufSize true = true ∧
    Outside env jmpBufSize [(s.sp.toNat - (libcStack + 48), s.sp.toNat)]

def Post (v : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).setWidth 32 = (if v.setWidth 32 = 0 then 0 else 1) ∧
  (∀ a k w, s'.mem.accessible a k w = s.mem.accessible a k w) ∧
  ∀ a, Outside a 1 [(env, env + jmpBufSize), (s.sp.toNat - (libcStack + 48), s.sp.toNat)] →
    s'.mem.bytes a = s.mem.bytes a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem correctness (J : JmpModel) (v : BitVec 64) :
    CEnsuresC Extracted.program (SetJmp J) Extracted.entry [v] Pre (Post v) := by
  intro ret hret s hs hpre
  obtain ⟨⟨hal, hb, ha, hw⟩, heb, hea, heo⟩ := hpre
  have he : env = janus_eval% env := rfl
  rw [he] at heb hea heo
  simp only [Post, he]
  simp only [outside_cons, outside_nil, and_true, libcStack, jmpBufSize] at heo hb hw heb hea ⊢
  apply ReturnsC.of_reaches
  janus_intro hs.call
  have h32 : (s.sp - 32#64).toNat = s.sp.toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hcs : CStack s (libcStack + 32) 0 :=
    CStack.mono (s := s) (below := libcStack + 48) ⟨hal, by simp [libcStack]; omega, ha, hw⟩ (by omega) (Nat.le_refl _)
  janus_run
  -- _setjmp(e_env)
  refine setJmp_call (sp := setjmpSpec J) (by simp [setJmpSpecs])
    ⟨libcCall_of (rs := [(s.sp.toNat - 32, s.sp.toNat)]) hcs (by omega) h32 (by janus_frame), ?_, ?_⟩ ?_
  · simp only [Buffer, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, Memory.accessible_writeLE, jmpBufSize]
    exact ⟨by simpa using heb, by simpa using hea⟩
  · simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h32, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, outside_cons, outside_nil, and_true, jmpBufSize, libcStack]
    omega
  rintro s1 ⟨m, hmr, hmb, hhold, h1⟩
  simp only [setReg_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
    jmpBufSize] at hmb hhold hmr
  have hmf0 := memFrame_of_bytes (d := 5968984) (n := 312) hmr hmb
  have F0 := memFrame_trans (m₀ := s.mem) (rs := [(s.sp.toNat - 32, s.sp.toNat)]) (by janus_frame) hmf0
  have V1 := h1.cret
  obtain ⟨hpc1, hx01, hcr1, htp1, hdz1, hreg1, hmf1⟩ := h1
  simp only [cReturn_iff, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, h32, libcStack, Nat.reducePow]
    at hcr1 hpc1 hx01 hmf1
  obtain_cret hcr1
  apply ReturnsC.of_reaches
  janus_run
  · -- v = 0: e_thrower returns, e_setjmp returns 0
    refine ⟨V1.vlow.goal, ?_, fun _ _ _ => trivial, fun a ⟨h1, h2⟩ => ?_⟩
    · have : v.setWidth 32 = 0#32 := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; simpa using hbr
      rw [if_pos this]
    · rw [Memory.bytes_writeLE_outside (m := s1.mem) (a := s.sp.toNat - 4) (n := 4) (v := 0) (x := a)
        (by omega), hmf1.bytes (by simp; omega), F0.bytes (by simp; omega)]
  · -- v ≠ 0: longjmp back into e_setjmp
    have h48 : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    have F1 := memFrame_trans F0 hmf1
    have hcs48 : CStack s (libcStack + 48) 0 := ⟨hal, by simp [libcStack]; omega, ha, hw⟩
    refine setJmp_call (sp := longjmpChkSpec J) (by simp [setJmpSpecs])
      ⟨libcCall_of (rs := _) hcs48 (by omega) h48 (memFrame_trans (rs' := [(s.sp.toNat - 48, s.sp.toNat)]) F1 (by janus_frame)),
       _, J.locality _ _ _ _ (fun i hi =>
          (memFrame_trans (rs' := [(s.sp.toNat - 48, s.sp.toNat)]) hmf1 (by janus_frame)).bytes
            (by simp [jmpBufSize, setReg_apply] at hi ⊢; omega)) hhold, ?_⟩ ?_
    · simp [jmpCtxOf, h48, h32]; omega
    rintro s3 ⟨c, hc, hl⟩
    have hcu := J.unique _ _ _ _ hc (J.locality _ _ _ _ (fun i hi =>
          (memFrame_trans (rs' := [(s.sp.toNat - 48, s.sp.toNat)]) hmf1 (by janus_frame)).bytes
            (by simp [jmpBufSize, setReg_apply] at hi ⊢; omega)) hhold)
    subst hcu
    have h19 := hl.x ⟨0, by decide⟩
    have h20 := hl.x ⟨1, by decide⟩
    have h21 := hl.x ⟨2, by decide⟩
    have h22 := hl.x ⟨3, by decide⟩
    have h23 := hl.x ⟨4, by decide⟩
    have h24 := hl.x ⟨5, by decide⟩
    have h25 := hl.x ⟨6, by decide⟩
    have h26 := hl.x ⟨7, by decide⟩
    have h27 := hl.x ⟨8, by decide⟩
    have h28 := hl.x ⟨9, by decide⟩
    have h29 := hl.x ⟨10, by decide⟩
    have hVL : VLow s s3 := fun i h1 h2 => by
      have := hl.d ⟨i - 8, by omega⟩
      simp only [jmpCtxOf, show 8 + (i - 8) = i by omega] at this
      have := congrArg BitVec.toNat this
      simpa [BitVec.toNat_setWidth] using this
    have hpc3 := hl.pc
    have hlr3 := hl.lr
    have hsp3 := hl.sp
    have hx03 := hl.x0
    have hfc3 := hl.fpcr
    have hmf3 := hl.mem
    have hreg3 := hl.regions
    simp only [jmpCtxOf, setReg_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd, h48, libcStack]
      at h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 hpc3 hlr3 hsp3 hx03 hfc3 hmf3
    rw [if_neg (by
      intro h; apply hbr; have := congrArg BitVec.toNat h
      simpa [BitVec.toNat_setWidth] using this)] at hx03
    have hx03' : s3.regs 0 = BitVec.ofNat 64 (v.toNat % 4294967296) := by
      rw [hx03]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
    clear hx03
    have F3 := memFrame_trans (memFrame_trans (rs' := [(s.sp.toNat - 48, s.sp.toNat)]) F1 (by janus_frame)) hmf3
    apply ReturnsC.of_reaches
    janus_run
    refine ⟨hVL.goal, by rw [if_neg (by
        intro h; apply hbr; have := congrArg BitVec.toNat h; simpa [BitVec.toNat_setWidth] using this)],
      fun _ _ _ => trivial, fun a ⟨h1, h2⟩ => F3.bytes (by simp; omega)⟩

end Proof
