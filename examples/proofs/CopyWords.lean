import Extracted

/-!
# `CopyWords(dst, src []uint64) int` copies `min(len dst, len src)` words (a loop over memory)

**Guarantee.** For all slice headers `dst = (d, dl, dc)` in `X0`–`X2` and `src = (r, sl, sc)` in
`X3`–`X5` and every Go call state `s` of `example.com/basic.CopyWords` such that
* `SP` is aligned and `[SP+8, SP+40)` is writable (the function spills `d` and `r` there),
* `dl, sl < 2^63` (Go lengths), the `8·dl` bytes at `d` are writable, the `8·sl` bytes at `r` are
  readable, and the two buffers and the spill area are pairwise disjoint,

the call returns (never faulting or panicking), obeys the ABI, returns `n = min dl sl` in `X0`, word `j < n` of `dst` afterwards
equals word `j` of `src` before the call, and nothing outside `dst[0..n)` and the two spill slots
changes. There are no out-of-bounds accesses and the loop terminates for every length.

**How.** The loop invariant at the loop head (`cmp x2, x1`) says the memory is exactly
`copyWords M₀ d r i` (the first `i` words copied); `loop` proves it by induction on the
iterations left.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Address of the loop head `cmp x2, x1`. -/
abbrev head : Nat := Extracted.entry + 0x24

/-- Memory after the two spills, before the loop. -/
def M₀ (s : State) (d r : BitVec 64) : Memory :=
  (s.mem.writeLE (s.sp.toNat + 8) 8 d.toNat).writeLE (s.sp.toNat + 32) 8 r.toNat

theorem loop (d r : BitVec 64) (dl sl : Nat) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hn : dl < 2 ^ 63) (hsl : sl < 2 ^ 63)
    (hd : s.mem.accessible d.toNat (8 * dl) true = true) (hd' : d.toNat + 8 * dl ≤ 2 ^ 48)
    (hr : s.mem.accessible r.toNat (8 * sl) false = true) (hr' : r.toNat + 8 * sl ≤ 2 ^ 48)
    (hdr : d.toNat + 8 * dl ≤ r.toNat ∨ r.toNat + 8 * sl ≤ d.toNat)
    (hds : d.toNat + 8 * dl ≤ s.sp.toNat + 8 ∨ s.sp.toNat + 40 ≤ d.toNat)
    (hrs : r.toNat + 8 * sl ≤ s.sp.toNat + 8 ∨ s.sp.toNat + 40 ≤ r.toNat)
    (nb : BitVec 64) (hnb : nb.toNat ≤ dl ∧ nb.toNat ≤ sl) :
    ∀ k (S : State) (i : BitVec 64), i.toNat + k = nb.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = d → S.regs 1 = nb → S.regs 2 = i →
      S.regs 3 = r → S.regs 30 = BitVec.ofNat 64 ret → S.sp = s.sp → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 18 = s.regs 18 →
      S.mem = copyWords (M₀ s d r) d.toNat r.toNat i.toNat →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        s'.regs 0 = nb ∧ s'.mem = copyWords (M₀ s d r) d.toNat r.toNat nb.toNat) := by
  unfold M₀
  intro k
  induction k with
  | zero =>
    intro S i hk hpc h0 h1 h2 h3 h30 hsp h28 h29 h18 hm
    janus_run
    rw [show i.toNat = nb.toNat by omega]
  | succ k ih =>
    intro S i hk hpc h0 h1 h2 h3 h30 hsp h28 h29 h18 hm
    janus_run until [head]
    apply ih _ (i + 1#64)
    all_goals try janus_simp [copyWords_succ]
    all_goals omega

theorem model (d dl dc r sl sc : BitVec 64) :
    Ensures Extracted.program Extracted.entry [d, dl, dc, r, sl, sc]
      (fun s => StackOK s 0 40 ∧ dl.toNat < 2 ^ 63 ∧ sl.toNat < 2 ^ 63 ∧
        Ptr s.mem d (8 * dl.toNat) true ∧ Ptr s.mem r (8 * sl.toNat) false ∧
        Disjoint d.toNat (8 * dl.toNat) r.toNat (8 * sl.toNat) ∧
        Disjoint d.toNat (8 * dl.toNat) (s.sp.toNat + 8) 32 ∧
        Disjoint r.toNat (8 * sl.toNat) (s.sp.toNat + 8) 32)
      (fun s s' => (s'.regs 0).toNat = min dl.toNat sl.toNat ∧
        s'.mem = copyWords (M₀ s d r) d.toNat r.toNat (min dl.toNat sl.toNat)) := by
  intro ret hret s hs ⟨⟨hal, hb, ha, hst⟩, hdl, hsl, ⟨hd, hd'⟩, ⟨hr, hr'⟩, hdr, hds, hrs⟩
  janus_intro hs
  simp only [Disjoint] at hdr hds hrs
  janus_run until [head]
  -- `csel` computed the length as a signed comparison; it is `min dl sl`
  have hnb : (if (dl.toNat : Int) < sl.toNat then dl else sl).toNat = min dl.toNat sl.toNat := by
    split <;> omega
  refine Reaches.mono (loop d r dl.toNat sl.toNat ret hret s hdl hsl hd hd' hr hr'
    hdr hds hrs
    (if (dl.toNat : Int) < sl.toNat then dl else sl) (by omega)
    (if (dl.toNat : Int) < sl.toNat then dl else sl).toNat _ 0#64 (by simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)
    (by janus_simp [copyWords_zero, M₀])) ?_
  rintro (s' | _) h
  · obtain ⟨habi, h0, hm⟩ := h
    exact ⟨habi, by rw [h0, hnb], by rw [hm, hnb]⟩
  · exact h.elim

theorem correctness (d dl dc r sl sc : BitVec 64) :
    Ensures Extracted.program Extracted.entry [d, dl, dc, r, sl, sc]
      (fun s => StackOK s 0 40 ∧ dl.toNat < 2 ^ 63 ∧ sl.toNat < 2 ^ 63 ∧
        Ptr s.mem d (8 * dl.toNat) true ∧ Ptr s.mem r (8 * sl.toNat) false ∧
        Disjoint d.toNat (8 * dl.toNat) r.toNat (8 * sl.toNat) ∧
        Disjoint d.toNat (8 * dl.toNat) (s.sp.toNat + 8) 32 ∧
        Disjoint r.toNat (8 * sl.toNat) (s.sp.toNat + 8) 32)
      (fun s s' => (s'.regs 0).toNat = min dl.toNat sl.toNat ∧
        (∀ j < min dl.toNat sl.toNat,
          s'.mem.readLE (d.toNat + 8 * j) 8 = s.mem.readLE (r.toNat + 8 * j) 8) ∧
        OnlyWrites (M₀ s d r) s'.mem d.toNat (8 * min dl.toNat sl.toNat)) := by
  refine (model d dl dc r sl sc).mono (fun _ h => h) ?_
  rintro s s' ⟨-, -, -, -, -, hdr, -, hrs⟩ ⟨h0, hm⟩
  simp only [Disjoint] at hdr hrs
  refine ⟨h0, fun j hj => ?_, hm ▸ onlyWrites_copyWords _ _ _ _⟩
  rw [hm, readLE_copyWords_inside _ _ _ _ _ hj (by omega), M₀,
    readLE_writeLE_disjoint _ _ (by omega), readLE_writeLE_disjoint _ _ (by omega)]

end Proof
