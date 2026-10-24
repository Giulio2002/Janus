import JanusX86.Proofs.MemW

/-! # Memory operands: the model's loads and stores against Janus' checked memory

A Janus access that succeeds lies in one of its regions, which lie below `2^47` (`Rel.canon`), so
the model's canonical-address checks pass and, by `Rel.mem`, the model's bytes are Janus'. -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem readLE_sumLE' (m : Janus.Arm64.Memory) : ∀ (a n : Nat),
    m.readLE a n = sumLE (fun j => (m.bytes (a + j)).toNat) n
  | _, 0 => rfl
  | a, n + 1 => by
    rw [Janus.Arm64.Memory.readLE, sumLE_cons, readLE_sumLE' m (a + 1) n]
    simp only [Nat.add_zero]
    congr 2; apply sumLE_congr; intro j _; congr 2; omega

theorem Rel.acc_bound {js : Janus.Amd64.State} {s : SState} (h : Rel js s) {a n : Nat} {w : Bool}
    (hacc : js.mem.accessible a n w = true) : a + n ≤ 2 ^ 47 := by
  obtain ⟨⟨r, hr, h1, h2, -, -⟩, -⟩ := (Janus.Arm64.Memory.accessible_iff js.mem a n w).1 hacc
  have := h.canon r hr; omega

theorem Rel.acc_bytes {js : Janus.Amd64.State} {s : SState} (h : Rel js s) {a n : Nat} {w : Bool}
    (hacc : js.mem.accessible a n w = true) : ∀ j < n, s.mem[a + j]? = some (js.mem.bytes (a + j)) := by
  intro j hj
  apply h.mem
  exact Janus.Arm64.Memory.accessible_sub js.mem hacc (by cases w <;> simp) (by omega) (by omega)

/-- A load through a non-FS segment of bytes Janus can read. -/
theorem run_load_rel {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s) (asz : Nat)
    {n : Nat} (hn : 0 < n) (eff : BitVec 64) {seg : Nat} (hseg : seg ≠ 4 ∧ seg ≠ 5) (k : String) (mp : Bool)
    {w : Bool} (hacc : js.mem.accessible eff.toNat n w = true) :
    (load_bytes_from_ea .Mode_64bit asz n eff none seg k false mp).run s =
      .ok (BitVec.ofNat (8 * n) (js.mem.readLE eff.toNat n)) s := by
  rw [run_load_bytes_from_ea hc h.rip asz hn eff none hseg k mp (h.acc_bound hacc) (fun j => js.mem.bytes (eff.toNat + j))
    (h.acc_bytes hacc), readLE_sumLE']

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_ea_to_la_fs {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (eff : BitVec 64) (n : Nat)
    (ha : (js.fsBase + eff).toNat < 2 ^ 47) :
    (ea_to_la .Mode_64bit eff 4 n).run s = .ok (js.fsBase + eff) s := by
  obtain ⟨v, hv, hv1⟩ := h.fs
  have e : bits_of_int (Sail.BitVec.toNatInt (GetElem?.getElem! v 1) + Sail.BitVec.toNatInt eff) 64 = js.fsBase + eff := by
    rw [hv1]
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast]
    rw [show ((js.fsBase.toNat : Int) + (eff.toNat : Int)) = ((js.fsBase.toNat + eff.toNat : Nat) : Int) by omega,
      bits_of_int_natCast_toNat, BitVec.toNat_add]
  have hint : (js.fsBase + eff).toInt = (js.fsBase + eff).toNat := toInt_of_lt _ (by omega)
  simp (config := {decide := true}) only [ea_to_la, in_64bit_mode, ↓reduceIte, run_bind,
    segment_base_and_bounds, read_msr, run_readReg hv, run_pure, e, run_canonical_address_p, hint,
    canon_ok (Int.natCast_nonneg _) (by omega : ((js.fsBase + eff).toNat : Int) < 2 ^ 47), Bool.not_true,
    Bool.false_eq_true]

theorem run_load_rel_fs {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s) (asz : Nat)
    {n : Nat} (hn : 0 < n) (eff : BitVec 64) (k : String) (mp : Bool) {w : Bool}
    (hacc : js.mem.accessible (js.fsBase + eff).toNat n w = true) :
    (load_bytes_from_ea .Mode_64bit asz n eff none 4 k false mp).run s =
      .ok (BitVec.ofNat (8 * n) (js.mem.readLE (js.fsBase + eff).toNat n)) s := by
  obtain ⟨v, hv, _⟩ := hc.csl
  have hb := h.acc_bound hacc
  simp only [load_bytes_from_ea, run_bind, run_readReg hv, run_pure, in_64bit_mode, Bool.not_true,
    Bool.false_and, Bool.false_eq_true, ite_false, run_ea_to_la_fs h eff n (by omega),
    run_check_linear_memory_access_nochk]
  rw [run_rb hc.app h.rip hn _ hb (fun j => js.mem.bytes ((js.fsBase + eff).toNat + j)) (h.acc_bytes hacc),
    readLE_sumLE']

/-- A store through a segment with linear address `la` (`ea_to_la` result). -/
theorem run_store_core {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s) (asz : Nat)
    {n : Nat} (hn : 0 < n) (eff la : BitVec 64) (seg : Nat) (hla : (ea_to_la .Mode_64bit eff seg n).run s = .ok la s)
    (data : BitVec (8 * n)) (mp : Bool) (hacc : js.mem.accessible la.toNat n true = true) :
    ∃ s', (store_bytes_to_ea .Mode_64bit asz n eff none seg data false mp).run s = .ok () s' ∧
      Rel { js with mem := js.mem.writeLE la.toNat n data.toNat } s' ∧ X86Config s' := by
  obtain ⟨v, hv, _⟩ := hc.csl
  have hb := h.acc_bound hacc
  obtain ⟨s', hw, hreg, hwr⟩ := run_wb hc.app h.rip hn la hb data ":W"
  refine ⟨s', ?_, ?_, ?_⟩
  · simp only [store_bytes_to_ea, run_bind, run_readReg hv, run_pure, in_64bit_mode, Bool.not_true,
      Bool.false_and, Bool.false_eq_true, ite_false, hla, run_check_linear_memory_access_nochk, hw]
  · obtain ⟨f, hf, hfr⟩ := h.flags
    obtain ⟨m, hm, hmr⟩ := h.fs
    refine ⟨fun i hi => ?_, by rw [hreg]; exact h.rip, ⟨f, by rw [hreg]; exact hf, hfr⟩,
      ⟨m, by rw [hreg]; exact hm, hmr⟩, ?_, h.canon⟩
    · have := h.gpr i hi
      unfold gprVal at this ⊢; rw [hreg]; exact this
    · intro a ha
      simp only [Janus.Arm64.Memory.accessible_writeLE] at ha
      rw [hwr a, Janus.Arm64.Memory.bytes_writeLE]
      split
      · rfl
      · exact h.mem a ha
  · obtain ⟨u, hu⟩ := hc.undef
    obtain ⟨a, ha, ha'⟩ := hc.efer
    obtain ⟨b, hb', hb''⟩ := hc.csl
    obtain ⟨c, hcc, hc'⟩ := hc.cpl
    obtain ⟨d, hd, hd'⟩ := hc.ctrs
    exact ⟨by rw [hreg]; exact hc.ms, by rw [hreg]; exact hc.fault, by rw [hreg]; exact hc.app,
      by rw [hreg]; exact hc.log, ⟨u, by rw [hreg]; exact hu⟩, ⟨a, by rw [hreg]; exact ha, ha'⟩,
      ⟨b, by rw [hreg]; exact hb', hb''⟩, ⟨c, by rw [hreg]; exact hcc, hc'⟩, ⟨d, by rw [hreg]; exact hd, hd'⟩⟩

end JanusX86.Proofs
