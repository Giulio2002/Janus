import Extracted

/-!
# `uint32_t e_atomic_inc(uint32_t *p)` (C, arm64): GCC `__atomic` through libgcc's outline atomics

```c
uint32_t e_atomic_inc(uint32_t *p) { return __atomic_add_fetch(p, 1, __ATOMIC_ACQ_REL); }
```

**Guarantee.** For every 4-aligned pointer `p` to 4 writable bytes, every AAPCS64 call of the
gcc-compiled `e_atomic_inc` on a CPU with the Armv8.1 LSE atomics (libgcc's flag
`__aarch64_have_lse_atomics`, a writable C global its constructor sets from `HWCAP_ATOMICS`, is
non-zero) returns without faulting, restores the callee-saved state, stores `*p + 1 (mod 2^32)`
at `p` and returns it in `W0`; memory changes nowhere else but in the frame record below `SP`.

**How.** gcc's `-moutline-atomics` (Ubuntu's default) compiles the atomic to a call of the libgcc
helper `__aarch64_ldadd4_acq_rel`, which is statically linked into the executable and so
extracted and executed like the rest: it tests the flag and, on an LSE CPU, does
`LDADDAL W0, W0, [X1]`. The helper's LL/SC fallback (`LDAXR`/`STLXR`, for pre-LSE CPUs) is the
path the flag excludes; it needs the store-exclusive model (WP-A).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI

namespace Proof

/-- libgcc's CPU-feature flag. -/
abbrev lse : Nat := CData.addr Extracted.cdata "__aarch64_have_lse_atomics"

theorem correctness (p : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p]
      (fun s => p.toNat % 4 = 0 ∧ p.toNat + 4 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 4 true = true ∧
        s.mem.accessible lse 1 false = true ∧ s.mem.readLE lse 1 ≠ 0 ∧ CStack s 16 0 ∧
        Outside p.toNat 4 [(s.sp.toNat - 16, s.sp.toNat)] ∧ Outside lse 1 [(s.sp.toNat - 16, s.sp.toNat)])
      (fun s s' => (s'.regs 0).toNat % 2 ^ 32 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
        s'.mem.readLE p.toNat 4 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
        MemFrame s.mem s'.mem [(p.toNat, p.toNat + 4), (s.sp.toNat - 16, s.sp.toNat)]) := by
  intro ret hret s hs ⟨hal4, hpb, hpw, hla, hlv, ⟨hal, hb, ha, hw⟩, hout, hlo⟩
  janus_intro hs.call
  have hl : lse = janus_eval% lse := rfl
  rw [hl] at hla hlv hlo
  simp only [outside_cons, outside_nil, and_true] at hout hlo
  have hlt : s.mem.readLE (janus_eval% lse) 1 < 256 ^ 1 := Memory.readLE_lt _ _ _
  janus_run
  refine ⟨?_, by janus_frame⟩
  have h4 : s.mem.readLE p.toNat 4 < 2 ^ 32 := Memory.readLE_lt _ _ _
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end Proof
