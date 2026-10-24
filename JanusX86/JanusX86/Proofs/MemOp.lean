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

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

theorem run_andM_pure_false_r (b : Bool) {y : SailM Bool} {s : SState} (hy : y.run s = .ok false s) :
    ((pure b : SailM Bool) <&&> y).run s = .ok false s := by
  cases b
  · rfl
  · simp only [andM, run_bind, run_pure]; exact hy

theorem beq2_3 : ∀ a < 4, (BitVec.ofNat 2 a == 3#2) = decide (a = 3) := by decide +kernel

theorem run_alignment_checking {js : Janus.Amd64.State} {s : SState} (h : Rel js s) (hc : X86Config s) :
    (alignment_checking_enabled_p ()).run s = .ok false s := by
  obtain ⟨d, hd, -, hd2⟩ := hc.ctrs
  obtain ⟨c, hcc, -⟩ := hc.cpl
  obtain ⟨f, hf, -⟩ := h.flags
  simp only [alignment_checking_enabled_p, run_bind, run_readReg hd, run_readReg hf, run_readReg hcc, run_pure,
    Mk_cr0bits] at *
  rw [hd2]; rfl

theorem setWidth_ofNat_mem (w : Nat) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (v : Nat) (hv : v < 2 ^ w) :
    (BitVec.ofNat (8 * (w / 8)) v).setWidth 128 = ((BitVec.ofNat w v).setWidth 64).setWidth 128 := by
  apply BitVec.eq_of_toNat_eq
  rcases hw with rfl | rfl | rfl | rfl <;> simp <;> omega

open Janus.Amd64 Janus.Amd64.Decode in
theorem run_operand_from_mem {js : State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex)
    (hrv : ∀ r, p.rex = some r → r < 16) {q m : Nat} {rest : List Nat} (hcs : CodeAt s (q + 1) rest) (hm : m < 256)
    {md reg ext : Nat} {a : Addr} {r3 : List Nat} {c : Nat}
    (hmd : modrm (p.rex.getD 0) (m :: rest) = some (⟨md, reg, ext, .m a⟩, r3, c)) {nimm : Nat} (hni : nimm < 8)
    (hq : q + c + nimm < 2 ^ 47) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {sg : Nat}
    (hsg : sg = 4 ↔ p.fs = true) (hsg5 : sg ≠ 5) (iac mp : Bool) {wr : Bool}
    (hacc : js.mem.accessible (ea js (BitVec.ofNat 64 (q + c + nimm)) (if p.fs then { a with fs := true } else a)).toNat
      (w / 8) wr = true) :
    (x86_operand_from_modr_m_and_sib_bytes .Mode_64bit 0#1 (w / 8) iac mp sg x
      (BitVec.ofNat 48 (q + 1 + (if sibP m then 1 else 0))) rex (BitVec.ofNat 3 (m % 8)) (BitVec.ofNat 2 (m / 64))
      (if sibP m then BitVec.ofNat 8 (rest.getD 0 0) else 0#8) (BitVec.ofNat 3 nimm)).run s =
      .ok (((BitVec.ofNat w (js.mem.readLE (ea js (BitVec.ofNat 64 (q + c + nimm))
          (if p.fs then { a with fs := true } else a)).toNat (w / 8))).setWidth 64).setWidth 128,
        ((c - 1 - (if sibP m then 1 else 0) : Nat) : Int), eaOff js (BitVec.ofNat 64 (q + c + nimm)) a) s := by
  obtain ⟨hea, hfs, hmdq⟩ := run_x86_effective_addr h hc h.rip hp hrv hcs hm hmd hni hq
  have hmd3 : m / 64 ≠ 3 := by
    intro e; unfold modrm at hmd; simp [show m / 64 = 3 from e] at hmd
  have hm3 : (BitVec.ofNat 2 (m / 64) == 3#2) = false := by
    rw [beq2_3 _ (by omega)]; simpa using hmd3
  have hadr : (0x67#8 == _get_prefixes_adr x) = false := by rw [hp.adr]; decide
  simp only [x86_operand_from_modr_m_and_sib_bytes, hm3, Bool.false_eq_true, ↓reduceIte, run_bind, hea, run_pure,
    run_andM_pure_false_r iac (run_alignment_checking h hc), run_select_address_size x hadr, select_base_register,
    rme_size]
  have hv := Janus.Arm64.Memory.readLE_lt js.mem
    (ea js (BitVec.ofNat 64 (q + c + nimm)) (if p.fs then { a with fs := true } else a)).toNat (w / 8)
  have hv' : js.mem.readLE (ea js (BitVec.ofNat 64 (q + c + nimm)) (if p.fs then { a with fs := true } else a)).toNat (w / 8)
      < 2 ^ w := by
    rcases hw with rfl | rfl | rfl | rfl <;> simpa using hv
  cases hf : p.fs
  · have hsg' : sg ≠ 4 := fun e => by simp [hsg.1 e] at hf
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at hacc hv'
    have hea' : ea js (BitVec.ofNat 64 (q + c + nimm)) a = eaOff js (BitVec.ofNat 64 (q + c + nimm)) a := by
      simp [ea, hfs]
    rw [hea'] at hacc hv'
    rw [run_load_rel h hc _ (by rcases hw with rfl | rfl | rfl | rfl <;> decide) _ ⟨hsg', hsg5⟩ _ _ hacc]
    simp only [run_pure, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, hf, Bool.false_eq_true, ↓reduceIte,
      hea', setWidth_ofNat_mem w hw _ hv']
  · have hsg4 : sg = 4 := hsg.2 hf
    subst hsg4
    simp only [hf, ↓reduceIte] at hacc hv'
    have hea' : ea js (BitVec.ofNat 64 (q + c + nimm)) { a with fs := true } =
        js.fsBase + eaOff js (BitVec.ofNat 64 (q + c + nimm)) a := by
      simp only [ea, ↓reduceIte]; rfl
    rw [hea'] at hacc hv'
    rw [run_load_rel_fs h hc _ (by rcases hw with rfl | rfl | rfl | rfl <;> decide) _ _ _ hacc]
    simp only [run_pure, Sail.BitVec.zeroExtend, BitVec.zeroExtend_eq_setWidth, hf, ↓reduceIte, hea',
      setWidth_ofNat_mem w hw _ hv']

end JanusX86.Proofs

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

open Janus.Amd64 Janus.Amd64.Decode in
theorem run_operand_to_mem {js : State} {s : SState} (h : Rel js s) (hc : X86Config s)
    {p : Prefixes} {x : BitVec 52} {rex : BitVec 8} (hp : PfxRel p x rex) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {sg : Nat} (hsg : sg = 4 ↔ p.fs = true) (hsg5 : sg ≠ 5)
    (iac mp : Bool) (a : Addr) (hafs : a.fs = false) (next : BitVec 64) (rm : BitVec 3) {md : BitVec 2}
    (hmd : (md == 3#2) = false) (sib : BitVec 8) (v : BitVec w)
    (hacc : js.mem.accessible (ea js next (if p.fs then { a with fs := true } else a)).toNat (w / 8) true = true) :
    ∃ s', (x86_operand_to_reg_mem .Mode_64bit (w / 8) iac mp ((v.setWidth 64).setWidth 128) sg (eaOff js next a)
      x rex rm md sib).run s = .ok () s' ∧
      Rel { js with mem := js.mem.writeLE (ea js next (if p.fs then { a with fs := true } else a)).toNat (w / 8) v.toNat } s' ∧
      X86Config s' := by
  have hadr : (0x67#8 == _get_prefixes_adr x) = false := by rw [hp.adr]; decide
  have htr : (Sail.BitVec.truncate (BitVec.setWidth 128 (BitVec.setWidth 64 v)) (8 * (w / 8))).toNat = v.toNat := by
    rcases hw with rfl | rfl | rfl | rfl <;> simp [Sail.BitVec.truncate] <;> omega
  simp only [x86_operand_to_reg_mem, hmd, Bool.false_eq_true, ↓reduceIte, run_bind, run_pure,
    run_andM_pure_false_r iac (run_alignment_checking h hc), run_select_address_size x hadr, select_base_register,
    wme_size]
  have hn : 0 < w / 8 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  cases hf : p.fs
  · have hsg' : sg ≠ 4 := fun e => by simp [hsg.1 e] at hf
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at hacc ⊢
    have hea' : ea js next a = eaOff js next a := by simp [ea, hafs]
    rw [hea'] at hacc ⊢
    have hb := h.acc_bound hacc
    obtain ⟨s', h1, h2, h3⟩ := run_store_core h hc _ hn _ _ sg (run_ea_to_la _ ⟨hsg', hsg5⟩ _ (by omega)) _ mp hacc
    exact ⟨s', h1, by rw [← htr]; exact h2, h3⟩
  · have hsg4 : sg = 4 := hsg.2 hf
    subst hsg4
    simp only [hf, ↓reduceIte] at hacc ⊢
    have hea' : ea js next { a with fs := true } = js.fsBase + eaOff js next a := by simp only [ea, ↓reduceIte]; rfl
    rw [hea'] at hacc ⊢
    have hb := h.acc_bound hacc
    obtain ⟨s', h1, h2, h3⟩ := run_store_core h hc _ hn _ _ 4 (run_ea_to_la_fs h _ _ (by omega)) _ mp hacc
    exact ⟨s', h1, by rw [← htr]; exact h2, h3⟩

end JanusX86.Proofs
