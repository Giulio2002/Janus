import Extracted

/-!
# `int e_setjmp(int v)` (C, amd64): `setjmp` and a non-local `longjmp` back to it

```c
static jmp_buf e_env;
static void e_thrower(int v) { if (v) longjmp(e_env, v); }   /* __longjmp_chk under FORTIFY */
int e_setjmp(int v) { if (setjmp(e_env)) return 1; e_thrower(v); return 0; }
```

**Guarantee.** For every `jmp_buf` model `J` (glibc's layout and pointer mangling are not
assumed: any model with the laws of `JmpModel64`), every `v`, and every System V call of the
gcc-compiled `e_setjmp` with the static `jmp_buf` `e_env` writable and a stack window for the
calls, the call returns without faulting, restores the callee-saved state (`CReturn`), and
returns `1` if `EDI = v ≠ 0` (through `__longjmp_chk`: `_setjmp` returns a second time, with
`v`) and `0` otherwise. Every accessible byte outside `e_env` and the stack below `RSP` is
unchanged. This holds under the trusted contract `SetJmp J` only. After the second return the
code's `je` path (taken when `_setjmp` returns `0`) is infeasible: the contract gives `EAX = v`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI
open Janus.Contracts.LibcAmd64
open Janus.Contracts.Libc (libcStack memFrame_of_bytes memFrame_trans)

namespace Proof

abbrev env : Nat := CData.addr Extracted.cdata "e_env"
abbrev sp (s : State) : Nat := (s.regs 4).toNat

def Pre (s : State) : Prop :=
  CStack s (libcStack + 48) 8 ∧ env + jmpBufSize64 ≤ 2 ^ 48 ∧ s.mem.accessible env jmpBufSize64 true = true ∧
    Outside env jmpBufSize64 [(sp s - (libcStack + 48), sp s + 8)]

def Post (v : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).setWidth 32 = (if v.setWidth 32 = 0 then 0 else 1) ∧
  (∀ a k w, s'.mem.accessible a k w = s.mem.accessible a k w) ∧
  ∀ a, Outside a 1 [(env, env + jmpBufSize64), (sp s - (libcStack + 48), sp s)] →
    s'.mem.bytes a = s.mem.bytes a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem correctness (J : JmpModel64) (v : BitVec 64) :
    CEnsuresC Extracted.program (SetJmp J) Extracted.entry [v] Pre (Post v) := by
  intro ret hret s hs hpre
  obtain ⟨⟨hal, hb, ha, hw⟩, heb, hea, heo⟩ := hpre
  have he : env = janus_eval% env := rfl
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = v := hs.reg (i := 0) (by simp)
  rw [he] at heb hea heo
  simp only [Post, he]
  simp only [sp, CABI.regSP, Amd64.Program.withExit, libcStack, jmpBufSize64] at heo hb hw heb hea ha hal h_ret
  simp only [outside_cons, outside_nil, and_true] at heo
  have h32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have h24 : (s.regs 4 - 24#64).toNat = (s.regs 4).toNat - 24 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  apply ReturnsC.of_reaches
  janus64_run
  -- _setjmp(e_env)
  refine setJmp_call (sp := setjmpSpec J) (by simp [setJmpSpecs]) ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ ?_
  all_goals try simp only [CABI.regSP, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h32, libcStack,
    Janus.Arm64.Memory.accessible_writeLE, Janus.Contracts.LibcAmd64.Buffer, BitVec.toNat_ofNat, jmpBufSize64,
    Nat.reduceMod, Nat.reducePow, outside_cons, outside_nil, and_true]
  · omega
  · omega
  · omega
  · exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · exact ⟨by omega, hea⟩
  · omega
  rintro s1 ⟨m, hmr, hmb, hhold, h1⟩
  simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
    jmpBufSize64] at hmb hhold hmr
  have hmf0 := memFrame_of_bytes (d := 5951104) (n := 200) hmr hmb
  obtain ⟨hpc1, hx01, hcr1, hfs1, hreg1, hmf1⟩ := h1
  simp only [cReturn_iff, retAddrOf_eq, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h32, libcStack, Nat.reducePow,
    Janus.Arm64.Memory.readLE_writeLE_self] at hcr1 hpc1 hx01 hmf1 hreg1 hfs1
  obtain ⟨c1sp, c1bx, c1bp, c112, c113, c114, c115, c1df, c1mx, c1cw⟩ := hcr1
  have hch1 : ∀ a k, (s.regs 4).toNat - 32 ≤ a → a + k ≤ (s.regs 4).toNat + 8 →
      s1.mem.readLE a k = ((Janus.Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 16) 4 (v.toNat % 4294967296)).writeLE
        ((s.regs 4).toNat - 32) 8 4859128).readLE a k := fun a k h1 h2 => by
    rw [hmf1.readLE a k (by simp; omega), hmf0.readLE a k (by simp; omega)]
  have rd16 : s1.mem.readLE ((s.regs 4).toNat - 16) 4 = v.toNat % 4294967296 := by
    rw [hch1 _ _ (by omega) (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    all_goals omega
  have rdr : s1.mem.readLE ((s.regs 4).toNat) 8 = ret := by
    rw [hch1 _ _ (by omega) (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, h_ret]
    all_goals omega
  have hacc1 : ∀ a k w, s1.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hmf1.accessible, hmf0.accessible]; simp
  have acc1 : s1.mem.accessible ((s.regs 4).toNat - 48) 56 true = true := by
    rw [hacc1]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hmf1x : True ∧ _ := ⟨trivial, hmf1⟩
  clear hmf1
  apply ReturnsC.of_reaches
  have h24' : (s.regs 4 - 32#64 + 8#64).toNat = (s.regs 4).toNat - 24 := by
    rw [BitVec.toNat_add, h32]; simp only [BitVec.toNat_ofNat]; omega
  have hv : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 (v.toNat % 4294967296))) = v.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  janus64_run
  · -- v = 0: e_thrower returns, e_setjmp returns 0
    obtain ⟨-, hmf1⟩ := hmf1x
    rw [hv] at hbr
    refine ⟨⟨by rw [c1mx], by rw [c1cw]⟩, by rw [if_pos hbr], hacc1, fun a ⟨h1, h2⟩ => ?_⟩
    simp only [sp] at h2
    rw [Janus.Arm64.Memory.bytes_writeLE_outside, Janus.Arm64.Memory.bytes_writeLE_outside,
      hmf1.bytes, hmf0.bytes, Janus.Arm64.Memory.bytes_writeLE_outside,
      Janus.Arm64.Memory.bytes_writeLE_outside]
    all_goals first | omega | (simp; omega)
  · -- v ≠ 0: longjmp back into e_setjmp
    obtain ⟨-, hmf1⟩ := hmf1x
    rw [hv] at hbr
    have h48 : (s.regs 4 - 48#64).toNat = (s.regs 4).toNat - 48 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    have hloc : ∀ i, i < jmpBufSize64 →
        (((Janus.Arm64.Memory.writeLE s1.mem ((s.regs 4).toNat - 12) 4 0).writeLE ((s.regs 4).toNat - 32) 8
          4859165).writeLE ((s.regs 4).toNat - 40) 8 0 |>.writeLE ((s.regs 4).toNat - 48) 8 4858740).bytes
            (5951104 + i) = m.bytes (5951104 + i) := fun i hi => by
      simp only [jmpBufSize64] at hi
      rw [Janus.Arm64.Memory.bytes_writeLE_outside, Janus.Arm64.Memory.bytes_writeLE_outside,
        Janus.Arm64.Memory.bytes_writeLE_outside, Janus.Arm64.Memory.bytes_writeLE_outside,
        hmf1.bytes]
      all_goals first | omega | (simp; omega)
    have hhold2 := J.locality _ _ _ _ hloc hhold
    refine setJmp_call (sp := longjmpChkSpec J) (by simp [setJmpSpecs]) ⟨⟨?_, ?_, ?_, ?_⟩, _, hhold2, ?_⟩ ?_
    all_goals try simp only [CABI.regSP, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h48, libcStack,
      Janus.Arm64.Memory.accessible_writeLE, jmpCtxOf, h24']
    · omega
    · omega
    · omega
    · rw [hacc1]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · show _ ≤ ((s.regs 4 - 32#64) + 8#64).toNat
      rw [h24']; omega
    rintro s3 ⟨c, hc, hl⟩
    have hcu := J.unique _ _ _ _ hc hhold2
    subst hcu
    have hsw : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) = v.setWidth 32 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
    obtain ⟨hpc3, hsp3, hbx3, hbp3, h123, h133, h143, h153, hax3, hdf3, hmx3, hcw3, hfs3, hreg3, hmf3⟩ := hl
    simp only [jmpCtxOf, retAddrOf_eq, setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h32, h48, libcStack,
      Janus.Arm64.Memory.readLE_writeLE_self, hv, hsw, if_neg hbr] at hpc3 hsp3 hbx3 hbp3 h123 h133 h143 h153 hax3 hmf3
    have hax3' : s3.regs 0 = BitVec.ofNat 64 (v.toNat % 4294967296) := by
      rw [hax3, if_neg (show ¬ (BitVec.setWidth 32 v = 0) from fun h => hbr h)]
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
    have hnz : v.toNat % 4294967296 ≠ 0 := fun h => hbr (by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, h])
    have hz : ¬ (BitVec.setWidth 32 (BitVec.ofNat 64 (v.toNat % 4294967296)) = 0#32) := fun h => hnz (by
      have := congrArg BitVec.toNat h; simpa [BitVec.toNat_setWidth] using this)
    clear hax3
    have rdr3 : s3.mem.readLE ((s.regs 4).toNat) 8 = ret := by
      rw [hmf3.readLE ((s.regs 4).toNat) 8 (by simp <;> omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint, rdr]
      all_goals omega
    have hacc3 : ∀ a k w, s3.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
      rw [hmf3.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc1 a k w
    have acc3 : s3.mem.accessible ((s.regs 4).toNat - 48) 56 true = true := by
      rw [hacc3]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    have hmf3x : True ∧ _ := ⟨trivial, hmf3⟩
    clear hmf3
    apply ReturnsC.of_reaches
    janus64_run
    -- the paths through `je` after the second return are infeasible (`EAX = v ≠ 0`)
    all_goals first
      | exact absurd ‹BitVec.setWidth 32 (BitVec.ofNat 64 (v.toNat % 4294967296)) = 0#32› hz
      | skip
    obtain ⟨-, hmf3⟩ := hmf3x
    refine ⟨⟨by rw [hmx3]; exact c1mx, by rw [hcw3]; exact c1cw⟩, hacc3, fun a ⟨h1, h2⟩ => ?_⟩
    simp only [sp] at h2
    rw [hmf3.bytes, Janus.Arm64.Memory.bytes_writeLE_outside, Janus.Arm64.Memory.bytes_writeLE_outside,
      Janus.Arm64.Memory.bytes_writeLE_outside, Janus.Arm64.Memory.bytes_writeLE_outside,
      hmf1.bytes, hmf0.bytes, Janus.Arm64.Memory.bytes_writeLE_outside,
      Janus.Arm64.Memory.bytes_writeLE_outside]
    all_goals first | omega | (simp; omega)

end Proof
