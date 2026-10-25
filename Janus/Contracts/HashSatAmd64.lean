import Janus.Contracts.MemSatAmd64

/-!
# The hashing contracts are satisfiable (amd64)

As `Janus.Contracts.MemSatAmd64` for the contracts of `Janus.Contracts.HashAmd64`, with the
hashing model `EqHashModel.H0` (every byte hash is its seed, `typehash` of `TD` too): for every
contract x86-64 machine code (its bytes below, from GNU `as`) at the address `A0` of a program
with no other code, a proof that it satisfies the contract for every stack bound, and a call
state over `EqHashModel.wmem` that satisfies the precondition.
-/

namespace Janus.Contracts.HashSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.MemAmd64
  Janus.Contracts.HashAmd64 Janus.Contracts.EqHashModel
  Janus.Contracts.MemSatAmd64
open Janus (MemFrame InRanges Outside outside_cons outside_nil)
open Janus.Contracts.IfaceSatAmd64 (toy A0 at0 withCode link_at0)
open Janus.Contracts.Hash (HashModel FHashIs IHashIs HashFrame c0 c1 dataAt itabType)
open Janus.Float (classify isNaN Kind binary32 binary64)

/-- The return of a model implementation as `HRet`. -/
theorem hRet_of {H : HashModel} {d nargs : Nat} {s s' : State} {P : (Nat → W64) → Prop}
    (hsp : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hrip : s'.rip = retAddrOf s) (hfs : s'.fsBase = s.fsBase)
    (hdf : s.df = false) (hdf' : s'.df = false) (hmx : s'.mxcsr.toNat / 64 = s.mxcsr.toNat / 64)
    (hf : MemFrame s.mem s'.mem (H.priv ++ MemAmd64.calleeStack s d nargs))
    (he : H.Env s'.mem (s.regs 14)) (hp : P s'.regs) : HRet H d nargs s s' P :=
  ⟨_, _, _, _, _, _, retState_of hsp h5 h14 hx hrip hfs hdf hdf', hmx, hf, he, hp⟩

/-- The witness call states satisfy `HPre` for `H0` (stack bound 64). -/
theorem wstate_hPre (r : Nat → W64) (n : Nat) (hn : n ≤ 4) : HPre H0 64 n (wstate r) := by
  obtain ⟨hg, hc, ho⟩ := wstate_eqPre r n hn
  refine ⟨wmem_henv _, hg, hc, ?_, ho, ?_⟩ <;> simp [wstate, IfaceModel.wsp, IfaceModel.wg]

/-! ## Byte hashes: the seed -/

/-- `mov %rbx, %rax; ret`: the seed. -/
def seedCode : List Nat := [0x48, 0x89, 0xd8, 0xc3]

/-- Close a hash contract whose code is `seedCode` (memory unchanged, result the seed). -/
macro "seed_close" hdf:term : tactic => `(tactic| (
  refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl $hdf rfl rfl (MemFrame.refl _ _) ‹_› ?_
  simp [setRegF, Nat.mod_eq_of_lt (BitVec.isLt _)]))

theorem memhash_impl (d : Nat) : Memhash (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _⟩
  janus64_run
  seed_close hdf

theorem memhash0_impl (d : Nat) : Memhash0 (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩
  janus64_run
  refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv ?_
  simp [setRegF]

theorem memhashN_impl (d n : Nat) : MemhashN (toy.link (at0 seedCode)) A0 H0 d n := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _⟩
  janus64_run
  seed_close hdf

theorem memhash32_impl (d : Nat) : Memhash32 (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _⟩
  janus64_run
  seed_close hdf

theorem memhash64_impl (d : Nat) : Memhash64 (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _⟩
  janus64_run
  seed_close hdf

theorem memhashVarlen_impl (d : Nat) : MemhashVarlen (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _, _⟩
  janus64_run
  seed_close hdf

theorem strhash_impl (d : Nat) : Strhash (toy.link (at0 seedCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _⟩
  janus64_run
  seed_close hdf

/-- `mov %rcx, %rax; ret`: `typehash(t, p, h)` of `H0` is `h`. -/
def typehashCode : List Nat := [0x48, 0x89, 0xc8, 0xc3]

theorem typehash_impl (d : Nat) : Typehash (toy.link (at0 typehashCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _⟩
  janus64_run
  seed_close hdf

/-- `ret`: some word. -/
def randCode : List Nat := [0xc3]

theorem rand_impl (d : Nat) : Rand (toy.link (at0 randCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩
  janus64_run
  exact hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
    (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv trivial


/-! ## Floats and complex numbers -/

theorem classify_zero_iff (f : Janus.Float.Fmt) (x : Nat) :
    classify f x = .zero ↔ Janus.Float.expOf f x = 0 ∧ Janus.Float.fracOf f x = 0 := by
  unfold classify
  by_cases he : Janus.Float.expOf f x = 0 <;> by_cases hm : Janus.Float.fracOf f x = 0 <;>
    simp only [he, hm, ite_true, ite_false, and_true, and_false] <;> (try split) <;>
    (try split) <;> simp

/-- The inverse of Go's multiplier `c1` modulo `2^64`. -/
theorem c1_inv : c1 * 7906388553261026367 % 2 ^ 64 = 1 := by
  simp only [c1, Nat.reducePow, Nat.reduceMul, Nat.reduceMod]

/-- `H0`'s float hash of `±0`. -/
theorem fhash_zero {f : Janus.Float.Fmt} {k x h : Nat} (hz : classify f x = .zero) :
    FHashIs H0 f k x h (c1 * (c0 ^^^ h) % 2 ^ 64) := by
  simp [FHashIs, hz]

/-- `H0`'s float hash of anything but `±0` may be the seed (for a NaN with the random word
chosen to cancel `c1`). -/
theorem fhash_seed {f : Janus.Float.Fmt} {k x h : Nat} (hz : classify f x ≠ .zero) (hh : h < 2 ^
    64) :
    FHashIs H0 f k x h h := by
  simp only [FHashIs, hz, ite_false, H0_mem]
  split
  · refine ⟨c0 ^^^ h ^^^ (h * 7906388553261026367 % 2 ^ 64), ?_, ?_⟩
    · have h0 : c0 < 2 ^ 64 := by decide
      exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h0 hh) (Nat.mod_lt _ (by decide))
    · rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.mul_mod, Nat.mod_mod,
        ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_comm c1 h, Nat.mul_assoc, Nat.mul_mod,
        c1_inv, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hh]
  · exact (Nat.mod_eq_of_lt hh).symm

/-- `SHL $1` of a binary32 encoding is zero exactly for `±0`. -/
theorem shl_zero32 (x : Nat) (_hx : x < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 x)) <<< 1 = 0#32) ↔
      classify binary32 x = .zero := by
  rw [classify_zero_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Janus.Float.expOf,
    Janus.Float.fracOf, binary32]
  simp only [Nat.reducePow, Nat.shiftLeft_eq, Nat.pow_one]
  omega

/-- `SHL $1` of a binary64 encoding is zero exactly for `±0`. -/
theorem shl_zero64 (x : Nat) (_hx : x < 2 ^ 64) :
    (x * 2 % 18446744073709551616 = 0) ↔ classify binary64 x = .zero := by
  rw [classify_zero_iff]
  simp only [Janus.Float.expOf, Janus.Float.fracOf, binary64, Nat.reducePow]
  omega

/-- The hash of a zero, as the code computes it. -/
theorem xor_mul_toNat (b : W64) (u v : Nat) (hu : u < 2 ^ 64) :
    ((b ^^^ BitVec.ofNat 64 u) * BitVec.ofNat 64 v).toNat = v * (u ^^^ b.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_mul, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hu, Nat.mul_comm, Nat.xor_comm, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem zero_hash_toNat (b : W64) :
    ((b ^^^ 33054211828000289#64) * 23344194077549503#64).toNat = c1 * (c0 ^^^ b.toNat) % 2 ^ 64 :=
  xor_mul_toNat b 33054211828000289 23344194077549503 (by simp)

/-- `mov (%rax), %ecx; shl $1, %ecx; jnz 1f` (bits other than the sign non-zero: the seed);
`movabs $c0, %rdx; xor %rdx, %rbx; movabs $c1, %rdx; imul %rdx, %rbx; 1: mov %rbx, %rax; ret`. -/
def f32hashCode : List Nat :=
  [0x8b, 0x08, 0xd1, 0xe1, 0x75, 0x1b, 0x48, 0xba, 0x21, 0xa6, 0x56, 0x6a, 0xa1, 0x6e, 0x75, 0x00,
   0x48, 0x31, 0xd3, 0x48, 0xba, 0xbf, 0x63, 0x8f, 0xbb, 0x6b, 0xef, 0x52, 0x00, 0x48, 0x0f, 0xaf,
   0xda, 0x48, 0x89, 0xd8, 0xc3]

theorem f32hash_impl (d : Nat) : Fhash (toy.link (at0 f32hashCode)) A0 H0 d binary32 4 := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, hm, ⟨ha1, ha2,
      ha3⟩⟩
  have hx := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 4
  simp only [Nat.reducePow] at hx
  janus64_run
  · refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv ?_
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, zero_hash_toNat]
    exact fhash_zero ((shl_zero32 _ hx).1 ‹_›)
  · refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv ?_
    simp only [setRegF, reduceIte, Nat.reduceEqDiff]
    exact fhash_seed (fun h => ‹¬_› ((shl_zero32 _ hx).2 h)) (BitVec.isLt _)


/-- As `f32hashCode` with `mov (%rax), %rcx; shl $1, %rcx`. -/
def f64hashCode : List Nat :=
  [0x48, 0x8b, 0x08, 0x48, 0xd1, 0xe1, 0x75, 0x1b, 0x48, 0xba, 0x21, 0xa6, 0x56, 0x6a, 0xa1, 0x6e,
   0x75, 0x00, 0x48, 0x31, 0xd3, 0x48, 0xba, 0xbf, 0x63, 0x8f, 0xbb, 0x6b, 0xef, 0x52, 0x00, 0x48,
   0x0f, 0xaf, 0xda, 0x48, 0x89, 0xd8, 0xc3]

theorem f64hash_impl (d : Nat) : Fhash (toy.link (at0 f64hashCode)) A0 H0 d binary64 8 := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, hm, ⟨ha1, ha2,
      ha3⟩⟩
  have hx := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  simp only [Nat.reducePow] at hx
  janus64_run
  · refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv ?_
    rename_i hz
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, zero_hash_toNat]
    exact fhash_zero ((shl_zero64 _ hx).1 hz)
  · refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv ?_
    rename_i hz
    simp only [setRegF, reduceIte, Nat.reduceEqDiff]
    exact fhash_seed (fun h => hz ((shl_zero64 _ hx).2 h)) (BitVec.isLt _)

/-- `f32hashCode`'s step on the real part `(%rax)`, then on the imaginary part `4(%rax)` with the
first hash as the seed (`rbx`), then `mov %rbx, %rax; ret`. -/
def c64hashCode : List Nat :=
  [0x8b, 0x08, 0xd1, 0xe1, 0x75, 0x1b, 0x48, 0xba, 0x21, 0xa6, 0x56, 0x6a, 0xa1, 0x6e, 0x75, 0x00,
   0x48, 0x31, 0xd3, 0x48, 0xba, 0xbf, 0x63, 0x8f, 0xbb, 0x6b, 0xef, 0x52, 0x00, 0x48, 0x0f, 0xaf,
   0xda, 0x8b, 0x48, 0x04, 0xd1, 0xe1, 0x75, 0x1b, 0x48, 0xba, 0x21, 0xa6, 0x56, 0x6a, 0xa1, 0x6e,
   0x75, 0x00, 0x48, 0x31, 0xd3, 0x48, 0xba, 0xbf, 0x63, 0x8f, 0xbb, 0x6b, 0xef, 0x52, 0x00, 0x48,
   0x0f, 0xaf, 0xda, 0x48, 0x89, 0xd8, 0xc3]

theorem c64hash_impl (d : Nat) : Chash (toy.link (at0 c64hashCode)) A0 H0 d binary32 4 := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, hm, ⟨ha1, ha2,
      ha3⟩, _⟩
  have hx := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 4
  have hy := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 4) 4
  simp only [Nat.reducePow] at hx hy
  janus64_run
  all_goals
    rename_i hb1 hb2
    refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv ?_
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, zero_hash_toNat]
    first
      | exact ⟨_, fhash_zero ((shl_zero32 _ hx).1 hb1), fhash_zero ((shl_zero32 _ hy).1 hb2)⟩
      | exact ⟨_, fhash_zero ((shl_zero32 _ hx).1 hb1),
          fhash_seed (fun h => hb2 ((shl_zero32 _ hy).2 h)) (Nat.mod_lt _ (by decide))⟩
      | exact ⟨_, fhash_seed (fun h => hb1 ((shl_zero32 _ hx).2 h)) (BitVec.isLt _),
          fhash_zero ((shl_zero32 _ hy).1 hb2)⟩
      | exact ⟨_, fhash_seed (fun h => hb1 ((shl_zero32 _ hx).2 h)) (BitVec.isLt _),
          fhash_seed (fun h => hb2 ((shl_zero32 _ hy).2 h)) (BitVec.isLt _)⟩


/-- As `c64hashCode` for binary64 (`(%rax)`, `8(%rax)`, 64-bit loads and shifts). -/
def c128hashCode : List Nat :=
  [0x48, 0x8b, 0x08, 0x48, 0xd1, 0xe1, 0x75, 0x1b, 0x48, 0xba, 0x21, 0xa6, 0x56, 0x6a, 0xa1, 0x6e,
   0x75, 0x00, 0x48, 0x31, 0xd3, 0x48, 0xba, 0xbf, 0x63, 0x8f, 0xbb, 0x6b, 0xef, 0x52, 0x00, 0x48,
   0x0f, 0xaf, 0xda, 0x48, 0x8b, 0x48, 0x08, 0x48, 0xd1, 0xe1, 0x75, 0x1b, 0x48, 0xba, 0x21, 0xa6,
   0x56, 0x6a, 0xa1, 0x6e, 0x75, 0x00, 0x48, 0x31, 0xd3, 0x48, 0xba, 0xbf, 0x63, 0x8f, 0xbb, 0x6b,
   0xef, 0x52, 0x00, 0x48, 0x0f, 0xaf, 0xda, 0x48, 0x89, 0xd8, 0xc3]

theorem c128hash_impl (d : Nat) : Chash (toy.link (at0 c128hashCode)) A0 H0 d binary64 8 := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, hm, ⟨ha1, ha2,
      ha3⟩, _⟩
  have hx := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  have hy := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 0).toNat + 8) 8
  simp only [Nat.reducePow] at hx hy
  janus64_run
  all_goals
    rename_i hb1 hb2
    refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv ?_
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, zero_hash_toNat]
    first
      | exact ⟨_, fhash_zero ((shl_zero64 _ hx).1 hb1), fhash_zero ((shl_zero64 _ hy).1 hb2)⟩
      | exact ⟨_, fhash_zero ((shl_zero64 _ hx).1 hb1),
          fhash_seed (fun h => hb2 ((shl_zero64 _ hy).2 h)) (Nat.mod_lt _ (by decide))⟩
      | exact ⟨_, fhash_seed (fun h => hb1 ((shl_zero64 _ hx).2 h)) (BitVec.isLt _),
          fhash_zero ((shl_zero64 _ hy).1 hb2)⟩
      | exact ⟨_, fhash_seed (fun h => hb1 ((shl_zero64 _ hx).2 h)) (BitVec.isLt _),
          fhash_seed (fun h => hb2 ((shl_zero64 _ hy).2 h)) (BitVec.isLt _)⟩


/-! ## Interfaces -/

/-- The hash of a non-nil interface value in `H0`. -/
theorem ihash_nonnil {m : Janus.Arm64.Memory} {t a : Nat} (ht : t ≠ 0) (b : W64) :
    IHashIs H0 m t a b.toNat ((b ^^^ 33054211828000289#64) * 23344194077549503#64).toNat := by
  simp only [Hash.IHashIs, ht, ite_false, H0_typeHash]
  refine ⟨_, rfl, ?_⟩
  rw [zero_hash_toNat, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (BitVec.isLt _) (by decide)),
    Nat.xor_comm]

/-- `mov (%rax), %rcx; test %rcx, %rcx; jz 1f` (nil: the seed); `movabs $c0, %rdx;
xor %rdx, %rbx; movabs $c1, %rdx; imul %rdx, %rbx` (`c1 · typehash(h ^ c0)`, `H0`'s typehash being
its seed); `1: mov %rbx, %rax; ret`. -/
def interhashCode : List Nat :=
  [0x48, 0x8b, 0x08, 0x48, 0x85, 0xc9, 0x74, 0x1b, 0x48, 0xba, 0x21, 0xa6, 0x56, 0x6a, 0xa1, 0x6e,
   0x75, 0x00, 0x48, 0x31, 0xd3, 0x48, 0xba, 0xbf, 0x63, 0x8f, 0xbb, 0x6b, 0xef, 0x52, 0x00, 0x48,
   0x0f, 0xaf, 0xda, 0x48, 0x89, 0xd8, 0xc3]

theorem nilinterhash_impl (d : Nat) : Nilinterhash (toy.link (at0 interhashCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, ⟨ha1, ha2, ha3⟩, _⟩
  have ht := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  simp only [Nat.reducePow] at ht
  janus64_run
  all_goals
    rename_i hb
    refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv ?_
    simp only [setRegF, reduceIte, Nat.reduceEqDiff]
  · simp [Hash.IHashIs]
  · exact ihash_nonnil hb _

theorem interhash_impl (d : Nat) : Interhash (toy.link (at0 interhashCode)) A0 H0 d := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, ⟨ha1, ha2, ha3⟩,
      hok⟩
  have ht := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 8
  simp only [Nat.reducePow] at ht
  janus64_run
  all_goals
    rename_i hb
    refine hRet_of (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl
      (by simp [retAddrOf]) rfl hdf rfl rfl (MemFrame.refl _ _) henv ?_
    simp only [setRegF, reduceIte, Nat.reduceEqDiff]
  · simp [Hash.IHashIs, itabType, hb]
  · have h2 := (hok hb).2.1
    generalize itabType s.mem (s.regs 0).toNat = t at h2 ⊢
    exact ihash_nonnil h2 (s.regs 3)

/-! ## Satisfiability -/

/-- The witness seed. -/
def seed : Nat := 7

/-- `H0`'s hashes of `TD` values do not depend on memory outside `TD.TFlag`. -/
theorem hashFrame_TD (p : Nat) (ws : List (Nat × Nat)) (hws : Outside (IfaceModel.TD + 20) 1 ws) :
    HashFrame H0 IfaceModel.TD wmem p ws := fun m' hf =>
  ⟨id, fun _ _ => Iff.rfl, by
    simp only [Janus.Spec.Type.isDirectIface, Janus.Spec.Type.tyTFlag]; rw [hf.readLE _ _ hws]⟩

/-- `Memhash` is satisfiable (amd64): 8 bytes at `VAL`. -/
theorem memhash_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat), H.Laws
    ∧
    Memhash (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 3 s ∧ MemAmd64.Input s d 3 (s.regs 0).toNat (s.regs 1).toNat) :=
  ⟨_, _, 64, H0_laws, memhash_impl 64, wstate (args IfaceModel.VAL seed 8 0), rfl,
    wstate_hPre _ 3 (by decide), by inp⟩

/-- `Memhash0` is satisfiable (amd64). -/
theorem memhash0_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧
    Memhash0 (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s) :=
  ⟨_, _, 64, H0_laws, memhash0_impl 64, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide)⟩

/-- `MemhashN 1` is satisfiable (amd64). -/
theorem memhash8_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧
    MemhashN (toy.link impl) A0 H d 1 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 1) :=
  ⟨_, _, 64, H0_laws, memhashN_impl 64 1, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by inp⟩

/-- `MemhashN 2` is satisfiable (amd64). -/
theorem memhash16_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧
    MemhashN (toy.link impl) A0 H d 2 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 2) :=
  ⟨_, _, 64, H0_laws, memhashN_impl 64 2, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by inp⟩

/-- `MemhashN 16` is satisfiable (amd64). -/
theorem memhash128_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧
    MemhashN (toy.link impl) A0 H d 16 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 16) :=
  ⟨_, _, 64, H0_laws, memhashN_impl 64 16, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by inp⟩

/-- `Memhash32` is satisfiable (amd64). -/
theorem memhash32_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧
    Memhash32 (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 4) :=
  ⟨_, _, 64, H0_laws, memhash32_impl 64, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by inp⟩

/-- `Memhash64` is satisfiable (amd64). -/
theorem memhash64_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧
    Memhash64 (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 8) :=
  ⟨_, _, 64, H0_laws, memhash64_impl 64, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by inp⟩

/-- `MemhashVarlen` is satisfiable (amd64): the closure `VLEN`. -/
theorem memhashVarlen_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧
    MemhashVarlen (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ MemAmd64.Input s d 2 ((s.regs 2).toNat + 8) 8 ∧
        MemAmd64.Input s d 2 (s.regs 0).toNat (MemAmd64.varlenSize s)) :=
  ⟨_, _, 64, H0_laws, memhashVarlen_impl 64, wstate (args IfaceModel.VAL seed 0 VLEN), rfl,
    wstate_hPre _ 2 (by decide), by inp, by inp⟩

/-- `Strhash` is satisfiable (amd64): the header `STR`. -/
theorem strhash_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat), H.Laws
    ∧
    Strhash (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ MemAmd64.StrInput s d 2 (s.regs 0).toNat) :=
  ⟨_, _, 64, H0_laws, strhash_impl 64, wstate (args STR seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by inp⟩

/-- `Fhash binary32 4` is satisfiable (amd64). -/
theorem f32hash_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat), H.Laws
    ∧
    Fhash (toy.link impl) A0 H d binary32 4 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ GoMXCSR s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 4) :=
  ⟨_, _, 64, H0_laws, f32hash_impl 64, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by unfold GoMXCSR; decide, by inp⟩

/-- `Fhash binary64 8` is satisfiable (amd64). -/
theorem f64hash_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat), H.Laws
    ∧
    Fhash (toy.link impl) A0 H d binary64 8 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ GoMXCSR s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 8) :=
  ⟨_, _, 64, H0_laws, f64hash_impl 64, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by unfold GoMXCSR; decide, by inp⟩

/-- `Chash binary32 4` is satisfiable (amd64). -/
theorem c64hash_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat), H.Laws
    ∧
    Chash (toy.link impl) A0 H d binary32 4 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ GoMXCSR s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat (2 * 4) ∧
        Outside (s.regs 0).toNat (2 * 4) H.priv) :=
  ⟨_, _, 64, H0_laws, c64hash_impl 64, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by unfold GoMXCSR; decide, by inp, by simp [wstate, args,
        IfaceModel.VAL]⟩

/-- `Chash binary64 8` is satisfiable (amd64). -/
theorem c128hash_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧
    Chash (toy.link impl) A0 H d binary64 8 ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ GoMXCSR s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat (2 * 8) ∧
        Outside (s.regs 0).toNat (2 * 8) H.priv) :=
  ⟨_, _, 64, H0_laws, c128hash_impl 64, wstate (args IfaceModel.VAL seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by unfold GoMXCSR; decide, by inp, by simp [wstate, args,
        IfaceModel.VAL]⟩

/-- `Typehash` is satisfiable (amd64): a `TD` value at `VAL`. -/
theorem typehash_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧
    Typehash (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 3 s ∧ H.Hashable (s.regs 0).toNat s.mem (s.regs 3).toNat) :=
  ⟨_, _, 64, H0_laws, typehash_impl 64, wstate (args IfaceModel.TD IfaceModel.VAL seed 0), rfl,
    wstate_hPre _ 3 (by decide), by simp [wstate, args, IfaceModel.TD]⟩

/-- `Nilinterhash` is satisfiable (amd64): `EFV = (TD, VAL)`. -/
theorem nilinterhash_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧ Nilinterhash (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 16 ∧
      (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        H.Hashable (s.mem.readLE (s.regs 0).toNat 8) s.mem
          (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat) ∧
        HashFrame H (s.mem.readLE (s.regs 0).toNat 8) s.mem
          (dataAt s.mem (s.mem.readLE (s.regs 0).toNat 8) (s.regs 0).toNat)
          (MemAmd64.calleeStack s d 2))) := by
  refine ⟨_, _, 64, H0_laws, nilinterhash_impl 64, wstate (args EFV seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by inp, fun _ => ?_⟩
  have e1 : (wstate (args EFV seed 0 0)).mem.readLE ((wstate (args EFV seed 0 0)).regs 0).toNat 8 =
    IfaceModel.TD := by decide
  rw [e1]
  exact ⟨rfl, hashFrame_TD _ _ (by simp [MapAmd64.calleeStack, wstate, IfaceModel.TD,
      IfaceModel.wsp])⟩

/-- `Interhash` is satisfiable (amd64): `IFV = (TAB, VAL)`, `TAB.Type = TD`. -/
theorem interhash_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat),
    H.Laws ∧ Interhash (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧
      (HPre H d 2 s ∧ MemAmd64.Input s d 2 (s.regs 0).toNat 16 ∧
      (s.mem.readLE (s.regs 0).toNat 8 ≠ 0 →
        MemAmd64.Input s d 2 (s.mem.readLE (s.regs 0).toNat 8) 16 ∧
        itabType s.mem (s.regs 0).toNat ≠ 0 ∧
        H.Hashable (itabType s.mem (s.regs 0).toNat) s.mem
          (dataAt s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat) ∧
        HashFrame H (itabType s.mem (s.regs 0).toNat) s.mem
          (dataAt s.mem (itabType s.mem (s.regs 0).toNat) (s.regs 0).toNat)
          (MemAmd64.calleeStack s d 2))) := by
  refine ⟨_, _, 64, H0_laws, interhash_impl 64, wstate (args IFV seed 0 0), rfl,
    wstate_hPre _ 2 (by decide), by inp, fun _ => ?_⟩
  have e1 : (wstate (args IFV seed 0 0)).mem.readLE ((wstate (args IFV seed 0 0)).regs 0).toNat 8 =
    IfaceModel.TAB := by decide
  have e2 : itabType (wstate (args IFV seed 0 0)).mem ((wstate (args IFV seed 0 0)).regs 0).toNat =
    IfaceModel.TD := by unfold itabType; decide
  rw [e1, e2]
  exact ⟨by inp, by decide, rfl,
    hashFrame_TD _ _ (by simp [MapAmd64.calleeStack, wstate, IfaceModel.TD, IfaceModel.wsp])⟩

/-- `Rand` is satisfiable (amd64). -/
theorem rand_satisfiable : ∃ (H : HashModel) (impl : List Janus.Amd64.Segment) (d : Nat), H.Laws ∧
    Rand (toy.link impl) A0 H d ∧ ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ HPre H d 0 s :=
  ⟨_, _, 64, H0_laws, rand_impl 64, wstate (args 0 0 0 0), rfl, wstate_hPre _ 0 (by decide)⟩

/-! ## Names for the SAT row (`audit/round9/sat_check.py` looks for `<contract>_satisfiable`) -/

/-- `memhash8` under the name of its contract. -/
theorem memhashN_satisfiable : type_of% @memhash8_satisfiable := @memhash8_satisfiable

/-- `f32hash` under the name of its contract. -/
theorem fhash_satisfiable : type_of% @f32hash_satisfiable := @f32hash_satisfiable

/-- `c64hash` under the name of its contract. -/
theorem chash_satisfiable : type_of% @c64hash_satisfiable := @c64hash_satisfiable

end Janus.Contracts.HashSatAmd64
