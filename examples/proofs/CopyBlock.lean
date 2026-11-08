import Extracted

/-!
# `CopyBlock(dst, src *[16]uint64)`: `copy(dst[:], src[:])` copies 128 bytes through `runtime.memmove`

**Guarantee.** For all pointers `dst`, `src` and every Go call state `s` of
`example.com/basic.CopyBlock` such that
* the stack-growth prologue falls through (`GuardOK s 0`), `SP` is aligned and the 56 bytes
  below `SP` are writable (the 48-byte frame and the saved frame pointer),
* the 128 bytes at `dst` are writable, the 128 bytes at `src` readable, and the two arrays and
  that stack window are pairwise disjoint,

the call returns (never faulting or panicking), obeys the ABI, and afterwards word `j < 16` of
`dst` equals word `j` of `src` before the call. Nothing outside `dst` changes except the two
saved registers in the callee's own frame (`OnlyWrites (M₀ s) … dst 128`).

**What this covers.** `CopyBlock` nil-checks both pointers, skips the call if `dst = src`, and
calls `runtime.memmove(dst, src, 128)`. The proof executes both functions instruction by
instruction from the extracted words: memmove's size dispatch, and the 33..128-byte path that
loads all 128 bytes into sixteen registers with `LDP` before storing them with `STP` (so it is
also correct for overlapping arrays, which this theorem does not need). Go 1.26 memmove uses
only general-purpose registers, so no SIMD state is involved.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Memory after the prologue saved `X30` and `X29` below `SP` (in the 48-byte frame). -/
def M₀ (s : State) : Memory :=
  (s.mem.writeLE (s.sp.toNat - 48) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat

theorem correctness (d r : BitVec 64) :
    Ensures Extracted.program Extracted.entry [d, r]
      (fun s => GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr s.mem d 128 true ∧ Ptr s.mem r 128 false ∧
        Disjoint d.toNat 128 r.toNat 128 ∧ Disjoint d.toNat 128 (s.sp.toNat - 56) 56 ∧
        Disjoint r.toNat 128 (s.sp.toNat - 56) 56)
      (fun s s' => (∀ j < 16, s'.mem.readLE (d.toNat + 8 * j) 8 = s.mem.readLE (r.toNat + 8 * j) 8) ∧
        OnlyWrites (M₀ s) s'.mem d.toNat 128) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hd, hd'⟩, ⟨hr, hr'⟩, hdr, hds, hrs⟩
  janus_intro hs
  simp only [Disjoint] at hdr hds hrs
  janus_run
  have hret' : ret < 2 ^ 64 := by have := hret.user; omega
  refine ⟨fun j hj => ?_, by
    simp only [M₀, h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hret']; exact onlyWrites_refl _ _ _⟩
  janus_cases hj
  all_goals janus_simp
  all_goals congr 1; omega

namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 1 then (0x300100) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64), (0x300100 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (d : BitVec 64) (r : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [d, r] s ∧ (GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr s.mem d 128 true ∧ Ptr s.mem r 128 false ∧
        Disjoint d.toNat 128 r.toNat 128 ∧ Disjoint d.toNat 128 (s.sp.toNat - 56) 56 ∧
        Disjoint r.toNat 128 (s.sp.toNat - 56) 56) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((∀ j < 16, s'.mem.readLE (d.toNat + 8 * j) 8 = s.mem.readLE (r.toNat + 8 * j) 8) ∧
        OnlyWrites (M₀ s) s'.mem d.toNat 128)) := by
  refine ⟨ret, s0, (0x300000), (0x300100), hret, setup, ?pre, correctness (0x300000) (0x300100) ret hret s0 setup ?pre⟩
  case pre =>
    simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp] <;> decide

end Witness
