import JanusX86.Proofs.Prefix

/-! # `x86_fetch_decode_execute` up to the one-byte dispatch

From a configured state whose memory holds the instruction bytes at `RIP`, the model reads the
prefixes (`get_prefixes`, simulated by `run_get_prefixes`), the opcode, and, when the opcode has
one, the ModRM byte and (when ModRM asks for one) the SIB byte, and calls
`one_byte_opcode_execute` with them. -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- ModRM selects a SIB byte (32/64-bit addressing): `r/m = 100` and `mod ≠ 11`. -/
def sibP (m : Nat) : Bool := m % 8 == 4 && m / 64 != 3

theorem sib_p_all : ∀ m < 256, x86_decode_sib_p (BitVec.ofNat 8 m) false = sibP m := by
  decide +kernel

/-- Does the one-byte opcode `op` have a ModRM byte (the model's 64-bit-mode table)? -/
def modrmP1 (op : Nat) : Bool := n64_bit_mode_one_byte_opcode_modr_m_p (BitVec.ofNat 8 op)

/-- The instruction bytes `bs` are at `base` in the Sail memory. -/
def CodeAt (s : SState) (base : Nat) (bs : List Nat) : Prop :=
  (∀ b ∈ bs, b < 256) ∧ ∀ i (hi : i < bs.length), s.mem[base + i]? = some (BitVec.ofNat 8 bs[i])

/-- The ModRM byte, the SIB byte and the number of bytes they take, after the opcode (`rest`). -/
def modrmSib (mp : Bool) (rest : List Nat) : BitVec 8 × BitVec 8 × Nat :=
  if mp then
    let m := rest.getD 0 0
    if sibP m then (BitVec.ofNat 8 m, BitVec.ofNat 8 (rest.getD 1 0), 2) else (BitVec.ofNat 8 m, 0#8, 1)
  else (0#8, 0#8, 0)

theorem run_orM_false {x y : SailM Bool} {s : SState} (hx : x.run s = .ok false s) (hy : y.run s = .ok false s) :
    (x <||> y).run s = .ok false s := by
  simp only [orM, run_bind, hx]; exact hy

theorem run_andM_pure_false (y : SailM Bool) (s : SState) : ((pure false : SailM Bool) <&&> y).run s = .ok false s := rfl

theorem run_andM_pure_true (y : SailM Bool) (s : SState) : ((pure true : SailM Bool) <&&> y).run s = y.run s := by
  simp only [andM, run_bind, run_pure]; rfl

theorem run_read_iptr {s : SState} {base : Nat} (hr : s.regs.get? .rip = some (BitVec.ofNat 64 base)) :
    (read_iptr .Mode_64bit).run s = .ok (BitVec.ofNat 48 base) s := by
  simp only [read_iptr, read_rip, regval_from_reg, run_bind, run_readReg hr, run_pure, in_64bit_mode,
    ↓reduceIte, Sail.BitVec.truncate]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 48 ∣ 2 ^ 64)]

open Janus.Amd64.Decode in
/-- Fetch and decode up to `one_byte_opcode_execute`. -/
theorem run_fetch_one {s : SState} (h : X86Config s) {base : Nat}
    (hr : s.regs.get? .rip = some (BitVec.ofNat 64 base)) {bs : List Nat} (hc : CodeAt s base bs)
    {p : Prefixes} {op : Nat} {rest : List Nat} {n : Nat}
    (hp : parsePrefixes bs {} 0 = some (p, op :: rest, n)) (hn : n ≤ 14) (hlim : base + 17 < 2 ^ 47)
    (hop : prefixGroup op = 0) (hop4 : op / 16 ≠ 4) (hvex : op ≠ 0xC4 ∧ op ≠ 0xC5 ∧ op ≠ 0x62)
    (hlen : (modrmSib (modrmP1 op) rest).2.2 ≤ rest.length) :
    ∃ x rex, PfxRel p x rex ∧ _get_prefixes_nxt x = BitVec.ofNat 8 op ∧
      (x86_fetch_decode_execute ()).run s =
        (one_byte_opcode_execute .Mode_64bit (BitVec.ofNat 48 base)
          (BitVec.ofNat 48 (base + n + 1 + (modrmSib (modrmP1 op) rest).2.2)) x rex (BitVec.ofNat 8 op)
          (modrmSib (modrmP1 op) rest).1 (modrmSib (modrmP1 op) rest).2.1).run s := by
  have hcode := hc.2
  obtain ⟨x, rex, hgp, hrel, hnxt, hnum⟩ := run_get_prefixes h (by exact hr) base bs {} 0 _ _ pfxRel_init hc.1
    (by simpa using hcode) hp (by omega) (by omega) hop hop4
  refine ⟨x, rex, hrel, hnxt, ?_⟩
  simp only [Nat.add_zero, Nat.sub_zero, Mk_prefixes] at hgp
  have hnum' : Sail.BitVec.toNatInt (_get_prefixes_num x) = (n : Int) := by
    simp [Sail.BitVec.toNatInt, hnum]
  have hadd1 : (add_to_iptr .Mode_64bit (BitVec.ofNat 48 base) (bits_of_int (1 + (n : Int)) 48)).run s =
      .ok (BitVec.ofNat 48 (base + n + 1)) s := by
    have e : (bits_of_int (1 + (n : Int)) 48).toNat = n + 1 := by
      rw [show (1 + (n : Int)) = ((n + 1 : Nat) : Int) by omega, bits_of_int_natCast_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [run_add_to_iptr _ _ (by rw [e]; simp; omega), e]
    simp; congr 1; omega
  have hdrop : bs.drop n = op :: rest := by simpa using parsePrefixes_drop _ _ _ hp
  have hlen0 : n < bs.length := by
    have := congrArg List.length hdrop; simp at this; omega
  have hops : ∀ i (hi : i < rest.length + 1), s.mem[base + n + i]? = some (BitVec.ofNat 8 ((op :: rest)[i])) := by
    intro i hi
    have hi' : n + i < bs.length := by have := congrArg List.length hdrop; simp at this; omega
    have := hcode (n + i) hi'
    rw [← Nat.add_assoc] at this
    rw [this]
    congr 2
    have e2 : ∀ (l : List Nat) (hl : l = op :: rest) (hi2 : i < l.length), l[i] = (op :: rest)[i] := by
      intro l hl _; subst hl; rfl
    rw [← e2 (bs.drop n) hdrop (by simp; omega), List.getElem_drop]
  have hb256 : ∀ b ∈ op :: rest, b < 256 := fun b hb => hc.1 b (by rw [← hdrop] at hb; exact List.mem_of_mem_drop hb)
  have hop256 : op < 256 := hb256 op (by simp)
  have hnx : _get_prefixes_nxt x = BitVec.ofNat 8 op := hnxt
  have beq8 : ∀ c : Nat, c < 256 → op ≠ c → (BitVec.ofNat 8 op == BitVec.ofNat 8 c) = false := by
    intro c hc hne
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp [Nat.mod_eq_of_lt hop256, Nat.mod_eq_of_lt hc] at this
    exact hne this
  have hv5 := beq8 0xC5 (by decide) hvex.2.1
  have hv4 := beq8 0xC4 (by decide) hvex.1
  have hv6 := beq8 0x62 (by decide) hvex.2.2
  have hmp : one_byte_opcode_modr_m_p .Mode_64bit (BitVec.ofNat 8 op) = modrmP1 op := rfl
  have hsel : ∀ q, PfxRel q x rex → (select_address_size .Mode_64bit (some x)).run s = .ok 8 s := by
    intro q hq; exact run_select_address_size x (by rw [hq.adr]; decide) s
  simp only [x86_fetch_decode_execute, run_bind, run_orM_false (run_ms h) (run_fault h), Bool.false_eq_true,
    ↓reduceIte, run_x86_operation_mode h, in_64bit_mode, run_read_iptr hr, hgp, hnum', hadd1, hnx, hv5, hv4,
    hv6, Bool.or_false, Bool.false_or, Bool.false_and, run_pure, Mk_prefixes, Mk_modr_m, Mk_sib, hmp,
    hsel p hrel]
  have hm1 : ∀ k, k < rest.length → k ≤ 2 → s.mem[(Sail.BitVec.signExtend (BitVec.ofNat 48 (base + n + 1 + k)) 64).toNat]? =
      some (BitVec.ofNat 8 (rest.getD k 0)) := by
    intro k hk hk2
    rw [signExtend48_toNat _ (by omega)]
    have := hops (k + 1) (by omega)
    rw [show base + n + (k + 1) = base + n + 1 + k by omega] at this
    rw [this]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have hadd2 : ∀ k, k ≤ 1 → (add_to_iptr .Mode_64bit (BitVec.ofNat 48 (base + n + 1 + k)) 1#48).run s =
      .ok (BitVec.ofNat 48 (base + n + 1 + (k + 1))) s := by
    intro k hk
    rw [run_add_to_iptr _ _ (by simp; omega)]
    simp; congr 1; omega
  cases hmpv : modrmP1 op
  · simp only [Bool.false_eq_true, ↓reduceIte, run_pure, Bool.false_and, modrmSib, Nat.add_zero,
      run_andM_pure_false]
  · have hr0 : 0 < rest.length := by simp [modrmSib, hmpv] at hlen; split at hlen <;> simp at hlen <;> omega
    have hm0 := hm1 0 hr0 (by decide)
    have ha0 := hadd2 0 (by decide)
    simp only [Nat.add_zero] at hm0 ha0
    have hmb := hb256 (rest.getD 0 0) (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr0])
    simp only [↓reduceIte, run_rme08 h hr _ _ (by rw [signExtend48_toNat _ (by omega)]; omega) hm0,
      ha0, Bool.true_and, run_pure, run_bind, run_andM_pure_true, modrmSib, hsel p hrel,
      show (2 == (8 : Int)) = false from rfl, sib_p_all _ hmb]
    cases hsb : sibP (rest.getD 0 0)
    · simp only [Bool.false_eq_true, ↓reduceIte, run_pure, Nat.zero_add]
    · have hr1 : 1 < rest.length := by
        have : (modrmSib (modrmP1 op) rest).2.2 = 2 := by simp only [modrmSib, hmpv, ↓reduceIte, hsb]
        omega
      have hm1' := hm1 1 hr1 (by decide)
      have ha1 := hadd2 1 (by decide)
      simp only [↓reduceIte, run_bind, run_pure, hsel p hrel, Nat.zero_add,
        run_rme08 h hr _ _ (by rw [signExtend48_toNat _ (by omega)]; omega) hm1', ha1]

end JanusX86.Proofs
