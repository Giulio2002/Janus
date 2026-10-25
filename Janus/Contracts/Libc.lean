import Janus.FFI

/-!
# libc contracts, `setjmp`/`longjmp`, and the TLS block (arm64)

A cgo executable is dynamically linked: a C call to `memcpy`, `strlen`, `malloc`, `setjmp`, …
goes to the function's **PLT entry**, which jumps through a GOT slot the dynamic linker fills
with the address of the function in `libc.so.6` (on the first call through the lazy-binding
resolver). The code behind the slot is not in the binary, so it cannot be executed by the
model. `janus extract` recognises the PLT entries (`cmd/janus/cenv.go`: the canonical
`ADRP X16 / LDR X17 / ADD X16 / BR X17` form, whose GOT slot is the target of an
`R_AARCH64_JUMP_SLOT` relocation for the symbol) and makes each an external stub named
`<symbol>@plt` (`StubKind.external`). This module gives them a meaning, as `Janus.FFI` contracts
(`ReturnsC`): the **trusted** descriptions of what glibc's functions do, stated against the C
standard and the glibc manual, not against glibc's code.

* `Libc` — `memcpy`, `memmove`, `memset`, `strlen`, `strcmp`, `malloc`, `free`, and the
  `_FORTIFY_SOURCE` variants gcc emits at `-O2` (`__memcpy_chk`, `__memmove_chk`,
  `__memset_chk`). Each says when the call is defined (`safe`: the C standard's preconditions,
  e.g. non-overlapping buffers for `memcpy`, a terminated string for `strlen`) and what it
  returns (`next`): the result in `X0`, the AAPCS64 callee-saved state (`CReturn`), and memory
  `MemFrame`-equal to the specified one outside the stack bytes the call may use below `SP`
  (`libcStack`).
* `SetJmp J` — `_setjmp` and `longjmp`/`__longjmp_chk`, with a **non-local return**: `longjmp`
  resumes the context `_setjmp` saved, a second return from `_setjmp` with the value passed to
  `longjmp`. The `jmp_buf` layout and glibc's pointer mangling are abstract (`JmpModel`):
  a theorem holds for every model with the stated laws.
* `TLSBlock` — where a `__thread` variable of the executable lives (the AArch64 TLS ABI), and
  `TLSDescFn`, the function-pointer hypothesis of a TLS descriptor call (general dynamic,
  TLSDESC).

**The C heap.** `malloc` returns a block in **fresh** memory: a new writable region disjoint from
every region of the state (so from the Go heap, the stacks and every object the program holds),
with indeterminate contents. The model has no other state, so the heap's bookkeeping is a ghost
region at `heapTag + p` (above `2^48`, where no access can reach: `Memory.accessible` requires a
region below `2^48`) recording that `[p, p + n)` came from `malloc` and is live. `free(p)` is
defined for a null `p` or a live block, and removes both regions; its contents become
inaccessible. Bytes outside every region are not memory of the program (libc's own data, the
heap's free lists): no access can read them, and every byte that becomes accessible (a new
block) has arbitrary contents.

**Satisfiable.** Every contract here is total (`Contract.Total`: every allowed call has a
result), `LibcSat.lean`: `libc_satisfiable`, `setJmp_satisfiable`, `jmpModel_satisfiable`, and a
TLS descriptor function proved from machine code (`tlsDescFn_satisfiable`).
-/

namespace Janus.Contracts.Libc

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.CABI Janus.FFI

/-! ## Returning from a libc call -/

/-- Bytes below `SP` a libc call may write: its own frames and those of the dynamic linker's
lazy-binding resolver on the first call through a PLT slot (`_dl_runtime_resolve` saves the
argument and SIMD&FP registers; 32 KiB is far above what glibc 2.42 uses). -/
def libcStack : Nat := 32768

/-- What every libc call needs: the C stack window (`SP` 16-aligned, `libcStack` writable bytes
below it). -/
def LibcCall (s : State) : Prop := CStack s libcStack 0

/-- The call from `s` returned in `s'` with `X0` satisfying `ret` and memory `m` (outside the
stack bytes below `SP`): at the return address `X30`, with the AAPCS64 callee-saved state
(`CReturn`: `SP`, `X19`–`X29`, `FPCR`, the low halves of `V8`–`V15`), the same thread
(`TPIDR_EL0`) and `DCZID_EL0`. Every other register, the flags and `FPSR` are arbitrary. -/
structure LibcRet (s s' : State) (m : Memory) (ret : W64 → Prop) : Prop where
  pc : s'.pc = s.regs 30
  x0 : ret (s'.regs 0)
  cret : CReturn s s'
  tpidr : s'.tpidr = s.tpidr
  dczid : s'.dczid = s.dczid
  regions : s'.mem.regions = m.regions
  mem : MemFrame m s'.mem [(s.sp.toNat - libcStack, s.sp.toNat)]

/-! ## Memory and strings -/

/-- `n` bytes copied from `src` to `d`, reading the old memory (so also right for overlapping
buffers: `memmove`). -/
def copyMem (m : Memory) (d src n : Nat) : Memory :=
  { m with bytes := fun a => if d ≤ a ∧ a < d + n then m.bytes (src + (a - d)) else m.bytes a }

/-- `n` bytes at `d` set to `c`. -/
def setMem (m : Memory) (d c n : Nat) : Memory :=
  { m with bytes := fun a => if d ≤ a ∧ a < d + n then BitVec.ofNat 8 c else m.bytes a }

/-- A NUL-terminated string of length `n` at `p`: `n` non-zero bytes, then a zero byte, all
readable and below `2^48`. -/
def CStr (m : Memory) (p n : Nat) : Prop :=
  p + n + 1 ≤ 2 ^ 48 ∧ m.accessible p (n + 1) false = true ∧ m.bytes (p + n) = 0 ∧
    ∀ i, i < n → m.bytes (p + i) ≠ 0

/-- A string has one length. -/
theorem CStr.unique {m : Memory} {p n n' : Nat} (h : CStr m p n) (h' : CStr m p n') : n = n' := by
  rcases Nat.lt_trichotomy n n' with hl | he | hl
  · exact absurd h.2.2.1 (h'.2.2.2 n hl)
  · exact he
  · exact absurd h'.2.2.1 (h.2.2.2 n' hl)

/-- The bytes of the string of length `n` at `p` (without the terminator). -/
def cstrBytes (m : Memory) (p n : Nat) : List Nat := (List.range n).map fun i => (m.bytes (p + i)).toNat

/-- Lexicographic comparison of byte strings (as `unsigned char`, C11 7.24.4). -/
def lexCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else lexCmp as bs

/-- The result of `strcmp` as an `int` in `W0` has the sign of the comparison. -/
def CmpResult (o : Ordering) (r : W64) : Prop :=
  match o with
  | .lt => (r.setWidth 32).toInt < 0
  | .eq => r.setWidth 32 = 0
  | .gt => 0 < (r.setWidth 32).toInt

/-! ## The C heap -/

/-- Where the ghost record of a live `malloc` block at `p` is kept: the region
`⟨heapTag + p, n, true⟩`, above every address an access can reach. -/
def heapTag : Nat := 2 ^ 48

/-- The live-block record of `[p, p + n)`. -/
def heapToken (p n : Nat) : Region := ⟨heapTag + p, n, true⟩

/-- `[p, p + n)` is a live `malloc` block of `m`. -/
def HeapBlock (m : Memory) (p n : Nat) : Prop := ⟨p, n, true⟩ ∈ m.regions ∧ heapToken p n ∈ m.regions

/-- `[p, p + n)` is fresh in `m`: disjoint from every region (and below `2^48`). -/
def Fresh (m : Memory) (p n : Nat) : Prop :=
  p + n ≤ 2 ^ 48 ∧ ∀ r ∈ m.regions, p + n ≤ r.base ∨ r.base + r.size ≤ p

/-- The memory after `malloc` returned the block `[p, p + n)` with contents `junk`. -/
def heapAlloc (m : Memory) (p n : Nat) (junk : Nat → Byte) : Memory :=
  { bytes := fun a => if p ≤ a ∧ a < p + n then junk a else m.bytes a,
    regions := m.regions ++ [⟨p, n, true⟩, heapToken p n] }

/-- The memory after `free` of the block `[p, p + n)` (its bytes now arbitrary, `junk`). -/
def heapFree (m : Memory) (p n : Nat) (junk : Nat → Byte) : Memory :=
  { bytes := fun a => if p ≤ a ∧ a < p + n then junk a else m.bytes a,
    regions := (m.regions.erase ⟨p, n, true⟩).erase (heapToken p n) }


/-! ### Lemmas for proofs through libc calls -/

/-- A string survives a change of memory outside it. -/
theorem CStr.of_frame {m m' : Memory} {p n : Nat} {rs : List (Nat × Nat)} (h : CStr m p n)
    (hf : MemFrame m m' rs) (ho : Outside p (n + 1) rs) : CStr m' p n := by
  obtain ⟨hb, ha, hz, hnz⟩ := h
  have hbyte : ∀ i, i ≤ n → m'.bytes (p + i) = m.bytes (p + i) := fun i hi => by
    have := hf.readLE (p + i) 1 (Janus.FFI.outside_one ho (by omega))
    simp only [Memory.readLE_one] at this
    exact BitVec.eq_of_toNat_eq this
  refine ⟨hb, by rw [hf.accessible]; exact ha, ?_, fun i hi => ?_⟩
  · rw [hbyte n (Nat.le_refl _)]; exact hz
  · rw [hbyte i (by omega)]; exact hnz i hi

theorem cstrBytes_of_frame {m m' : Memory} {p n : Nat} {rs : List (Nat × Nat)}
    (hf : MemFrame m m' rs) (ho : Outside p (n + 1) rs) : cstrBytes m' p n = cstrBytes m p n := by
  unfold cstrBytes
  apply List.map_congr_left
  intro i hi
  have := hf.readLE (p + i) 1 (Janus.FFI.outside_one ho (by simp at hi; omega))
  simp only [Memory.readLE_one] at this
  rw [this]

/-- Bytes through a frame. -/
theorem _root_.Janus.MemFrame.bytes {m m' : Memory} {rs : List (Nat × Nat)} (hf : MemFrame m m' rs) {a : Nat}
    (ho : Outside a 1 rs) : m'.bytes a = m.bytes a := by
  have := hf.readLE a 1 ho
  simp only [Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this


@[simp] theorem copyMem_regions (m : Memory) (d src n : Nat) : (copyMem m d src n).regions = m.regions := rfl
@[simp] theorem setMem_regions (m : Memory) (d c n : Nat) : (setMem m d c n).regions = m.regions := rfl
@[simp] theorem accessible_copyMem (m : Memory) (d src n a k : Nat) (w : Bool) :
    (copyMem m d src n).accessible a k w = m.accessible a k w := rfl
@[simp] theorem accessible_setMem (m : Memory) (d c n a k : Nat) (w : Bool) :
    (setMem m d c n).accessible a k w = m.accessible a k w := rfl

theorem copyMem_bytes_in {m : Memory} {d src n a : Nat} (h1 : d ≤ a) (h2 : a < d + n) :
    (copyMem m d src n).bytes a = m.bytes (src + (a - d)) := by
  simp [copyMem, h1, h2]

theorem copyMem_bytes_out {m : Memory} {d src n a : Nat} (h : a < d ∨ d + n ≤ a) :
    (copyMem m d src n).bytes a = m.bytes a := by
  simp only [copyMem]; rw [if_neg (by omega)]

/-- A memory that differs from `m₀` only inside `[d, d + n)` (and has its accessibility). -/
theorem memFrame_of_bytes {m₀ m : Memory} {d n : Nat} (hreg : m.regions = m₀.regions)
    (h : ∀ a, a < d ∨ d + n ≤ a → m.bytes a = m₀.bytes a) : MemFrame m₀ m [(d, d + n)] where
  readLE a k ho := Janus.FFI.readLE_congr fun i hi => by
    simp only [outside_cons, outside_nil, and_true] at ho; exact h _ (by omega)
  accessible a k w := by simp only [Memory.accessible, hreg]

theorem memFrame_copyMem (m : Memory) (d src n : Nat) : MemFrame m (copyMem m d src n) [(d, d + n)] :=
  memFrame_of_bytes rfl fun _ h => copyMem_bytes_out h

theorem memFrame_setMem (m : Memory) (d c n : Nat) : MemFrame m (setMem m d c n) [(d, d + n)] :=
  memFrame_of_bytes rfl fun a h => by simp only [setMem]; rw [if_neg (by omega)]

/-- Frames compose: `m₁` a frame of `m₀` outside `rs`, `m₂` of `m₁` outside `rs'`. -/
theorem memFrame_trans {m₀ m₁ m₂ : Memory} {rs rs' : List (Nat × Nat)} (h₁ : MemFrame m₀ m₁ rs)
    (h₂ : MemFrame m₁ m₂ rs') : MemFrame m₀ m₂ (rs ++ rs') where
  readLE a k ho := by
    rw [outside_append] at ho
    rw [h₂.readLE a k ho.2, h₁.readLE a k ho.1]
  accessible a k w := by rw [h₂.accessible, h₁.accessible]

/-- The memory after a libc call, as a frame of the memory before it: the call's own effect
(`m`, a frame of `s.mem` outside `rs`) and the stack bytes below `SP`. -/
theorem LibcRet.frame {s s' : State} {m : Memory} {ret : W64 → Prop} {rs : List (Nat × Nat)}
    (h : LibcRet s s' m ret) (hm : MemFrame s.mem m rs) :
    MemFrame s.mem s'.mem (rs ++ [(s.sp.toNat - libcStack, s.sp.toNat)]) := memFrame_trans hm h.mem

@[simp] theorem heapAlloc_regions (m : Memory) (p n : Nat) (j : Nat → Byte) :
    (heapAlloc m p n j).regions = m.regions ++ [⟨p, n, true⟩, heapToken p n] := rfl

theorem heapAlloc_bytes_out {m : Memory} {p n a : Nat} {j : Nat → Byte} (h : a < p ∨ p + n ≤ a) :
    (heapAlloc m p n j).bytes a = m.bytes a := by
  simp only [heapAlloc]; rw [if_neg (by omega)]

theorem heapAlloc_readLE_out {m : Memory} {p n a k : Nat} {j : Nat → Byte} (h : a + k ≤ p ∨ p + n ≤ a) :
    (heapAlloc m p n j).readLE a k = m.readLE a k :=
  Janus.FFI.readLE_congr fun i hi => heapAlloc_bytes_out (by omega)

/-- Adding writable regions keeps every access allowed. -/
theorem accessible_append_writable {m : Memory} {rs : List Region} (hw : ∀ r ∈ rs, r.writable = true)
    {a k : Nat} {w : Bool} (h : m.accessible a k w = true) :
    ({ m with regions := m.regions ++ rs } : Memory).accessible a k w = true := by
  simp only [Memory.accessible, Bool.and_eq_true, List.any_append, List.all_append, Bool.or_eq_true,
    Bool.not_eq_true'] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨.inl h1, ?_⟩
  rcases h2 with h2 | h2
  · exact .inl h2
  · right; refine ⟨h2, ?_⟩
    simp only [List.all_eq_true]
    intro r hr; simp [hw r hr]

theorem accessible_heapAlloc {m : Memory} {p n a k : Nat} {j : Nat → Byte} {w : Bool}
    (h : m.accessible a k w = true) : (heapAlloc m p n j).accessible a k w = true := by
  have := accessible_append_writable (m := m) (rs := [⟨p, n, true⟩, heapToken p n])
    (by simp [heapToken]) h
  simpa [Memory.accessible, heapAlloc] using this

/-- The new block is accessible (writable) in the memory `malloc` returns. -/
theorem accessible_heapAlloc_block {m : Memory} {p n : Nat} {j : Nat → Byte} (hf : Fresh m p n)
    {a k : Nat} (h1 : p ≤ a) (h2 : a + k ≤ p + n) (w : Bool) :
    (heapAlloc m p n j).accessible a k w = true := by
  obtain ⟨hb, hd⟩ := hf
  simp only [Memory.accessible, heapAlloc, Bool.and_eq_true, List.any_append, List.all_append,
    Bool.or_eq_true, Bool.not_eq_true', List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    heapToken]
  refine ⟨.inr (.inl (by simp; omega)), ?_⟩
  cases w
  · exact .inl rfl
  · right
    refine ⟨?_, by simp⟩
    simp only [List.all_eq_true]
    intro r hr
    rcases hd r hr with h | h <;> simp <;> omega

/-- A fresh block is disjoint from every accessible range. -/
theorem Fresh.disjoint {m : Memory} {p n a k : Nat} {w : Bool} (hf : Fresh m p n) (hk : 0 < k)
    (h : m.accessible a k w = true) : p + n ≤ a ∨ a + k ≤ p := by
  obtain ⟨⟨r, hr, h1, h2, -, -⟩, -⟩ := (Memory.accessible_iff m a k w).1 h
  rcases hf.2 r hr with h3 | h3 <;> omega

theorem heapBlock_heapAlloc {m : Memory} {p n : Nat} {j : Nat → Byte} :
    HeapBlock (heapAlloc m p n j) p n := by
  simp [HeapBlock, heapAlloc]

/-- A region list without `r` keeps its accessibility when `r` is appended and then erased. -/
theorem any_all_erase_append {l : List Region} {r t : Region} (hr : r ∉ l) (ht : t.writable = true)
    (htn : t.base + t.size ≤ 2 ^ 48 → False) (P : Region → Bool) (hP : P t = false)
    (Q : Region → Bool) (hQ : Q t = true) :
    (((l ++ [r, t]).erase r).erase t).any P = l.any P ∧
      (((l ++ [r, t]).erase r).erase t).all Q = l.all Q := by
  have h1 : (l ++ [r, t]).erase r = l ++ [t] := by
    rw [List.erase_append_right _ hr]; simp
  rw [h1]
  by_cases htl : t ∈ l
  · rw [List.erase_append_left _ htl]
    have hp := List.perm_cons_erase htl
    constructor
    · rw [List.any_append]
      simp only [List.any_cons, List.any_nil, hP, Bool.or_false]
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨x, hx, hpx⟩; exact ⟨x, List.mem_of_mem_erase hx, hpx⟩
      · rintro ⟨x, hx, hpx⟩
        refine ⟨x, ?_, hpx⟩
        rcases List.mem_cons.1 (hp.mem_iff.1 hx) with h | h
        · subst h; simp [hP] at hpx
        · exact h
    · rw [List.all_append]
      simp only [List.all_cons, List.all_nil, hQ, Bool.and_true]
      apply Bool.eq_iff_iff.2
      simp only [List.all_eq_true]
      constructor
      · intro h x hx
        rcases List.mem_cons.1 (hp.mem_iff.1 hx) with h' | h'
        · subst h'; exact hQ
        · exact h x h'
      · intro h x hx; exact h x (List.mem_of_mem_erase hx)
  · rw [List.erase_append_right _ htl]; simp [hP, hQ]

/-- `free` after `malloc` of a non-empty block gives back the accessibility of the memory before
the `malloc`. -/
theorem accessible_heapFree_heapAlloc {m : Memory} {p n : Nat} (hf : Fresh m p n) (hn : 0 < n)
    (hp : p ≠ 0) (j j' : Nat → Byte) (bytes : Nat → Byte) (a k : Nat) (w : Bool) :
    ({ bytes := bytes, regions := ((m.regions ++ [⟨p, n, true⟩, heapToken p n]).erase ⟨p, n, true⟩).erase
        (heapToken p n) } : Memory).accessible a k w = m.accessible a k w := by
  have hr : (⟨p, n, true⟩ : Region) ∉ m.regions := by
    intro h; rcases hf.2 _ h with h | h <;> simp only at h <;> omega
  have := any_all_erase_append hr (t := heapToken p n) rfl (by simp [heapToken, heapTag]; omega)
    (fun r => r.base ≤ a && a + k ≤ r.base + r.size && r.base + r.size ≤ 2 ^ 48 && (!w || r.writable))
    (by
      have : ¬ (2 ^ 48 + p + n ≤ 2 ^ 48) := by omega
      simp only [heapToken, heapTag, this, decide_false, Bool.and_false, Bool.false_and])
    (fun r => r.writable || a + k ≤ r.base || r.base + r.size ≤ a) (by simp [heapToken])
  simp only [Memory.accessible, this.1, this.2]


/-! Rewrite rules for `janus_run` after a libc call (`janus_run [copyMem_readLE_out, …]`): reads
and accesses away from the block a call changed. -/

theorem copyMem_readLE_out {m : Memory} {d src n a k : Nat} (h : a + k ≤ d ∨ d + n ≤ a) :
    (copyMem m d src n).readLE a k = m.readLE a k :=
  Janus.FFI.readLE_congr fun i hi => copyMem_bytes_out (by omega)

theorem setMem_readLE_out {m : Memory} {d c n a k : Nat} (h : a + k ≤ d ∨ d + n ≤ a) :
    (setMem m d c n).readLE a k = m.readLE a k :=
  Janus.FFI.readLE_congr fun i hi => by simp only [setMem]; rw [if_neg (by omega)]

/-- Regions that do not contain a non-empty range do not decide whether it is accessible. -/
theorem any_erase_of {l : List Region} {x : Region} {P : Region → Bool} (hx : P x = false) :
    (l.erase x).any P = l.any P := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨y, List.mem_of_mem_erase hy, hp⟩
  · rintro ⟨y, hy, hp⟩
    refine ⟨y, ?_, hp⟩
    by_cases hyx : y = x
    · subst hyx; simp [hx] at hp
    · exact (List.mem_erase_of_ne hyx).2 hy

theorem all_erase_of {l : List Region} {x : Region} {Q : Region → Bool} (hx : Q x = true) :
    (l.erase x).all Q = l.all Q := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  constructor
  · intro h y hy
    by_cases hyx : y = x
    · subst hyx; exact hx
    · exact h y ((List.mem_erase_of_ne hyx).2 hy)
  · intro h y hy; exact h y (List.mem_of_mem_erase hy)

theorem token_any_false {p n a k : Nat} {w : Bool} (hk : 0 < k) :
    (decide (2 ^ 48 + p ≤ a) && decide (a + k ≤ 2 ^ 48 + p + n) &&
      decide (2 ^ 48 + p + n ≤ 2 ^ 48) && (!w || true)) = false := by
  by_cases h : 2 ^ 48 + p ≤ a ∧ a + k ≤ 2 ^ 48 + p + n ∧ 2 ^ 48 + p + n ≤ 2 ^ 48
  · omega
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega

theorem heapAlloc_accessible_out {m : Memory} {p n a k : Nat} {j : Nat → Byte} {w : Bool}
    (hk : 0 < k) (h : a + k ≤ p ∨ p + n ≤ a) :
    (heapAlloc m p n j).accessible a k w = m.accessible a k w := by
  simp only [Memory.accessible, heapAlloc, heapToken, heapTag, List.any_append, List.all_append,
    List.any_cons, List.any_nil, List.all_cons, List.all_nil]
  have h1 : (decide (p ≤ a) && decide (a + k ≤ p + n) && decide (p + n ≤ 2 ^ 48) && (!w || true)) = false := by
    rcases h with h | h <;> simp <;> omega
  have h2 : (decide (2 ^ 48 + p ≤ a) && decide (a + k ≤ 2 ^ 48 + p + n) &&
      decide (2 ^ 48 + p + n ≤ 2 ^ 48) && (!w || true)) = false := token_any_false hk
  simp only [h1, h2, Bool.or_false, Bool.true_or, Bool.and_true]

theorem heapFree_bytes_out {m : Memory} {p n a : Nat} {j : Nat → Byte} (h : a < p ∨ p + n ≤ a) :
    (heapFree m p n j).bytes a = m.bytes a := by
  simp only [heapFree]; rw [if_neg (by omega)]

theorem heapFree_readLE_out {m : Memory} {p n a k : Nat} {j : Nat → Byte} (h : a + k ≤ p ∨ p + n ≤ a) :
    (heapFree m p n j).readLE a k = m.readLE a k :=
  Janus.FFI.readLE_congr fun i hi => heapFree_bytes_out (by omega)

theorem heapFree_accessible_out {m : Memory} {p n a k : Nat} {j : Nat → Byte} {w : Bool}
    (hk : 0 < k) (h : a + k ≤ p ∨ p + n ≤ a) :
    (heapFree m p n j).accessible a k w = m.accessible a k w := by
  simp only [Memory.accessible, heapFree]
  rw [any_erase_of (by simp only [heapToken, heapTag]; exact token_any_false hk), all_erase_of (by simp [heapToken]),
    any_erase_of (by rcases h with h | h <;> simp <;> omega), all_erase_of (by simp)]


/-- `free` of a block `malloc` added to `m` gives back `m`'s accessibility. -/
theorem accessible_heapFree_of {M m : Memory} {p n : Nat} {j : Nat → Byte}
    (hM : M.regions = m.regions ++ [⟨p, n, true⟩, heapToken p n]) (hf : Fresh m p n) (hn : 0 < n)
    (hp : p ≠ 0) (a k : Nat) (w : Bool) : (heapFree M p n j).accessible a k w = m.accessible a k w := by
  have := accessible_heapFree_heapAlloc (j := j) (j' := j) (bytes := (heapFree M p n j).bytes) hf hn hp a k w
  simp only [heapFree, hM] at this ⊢
  exact this

/-- The live block `free` finds at `p` is the one `malloc` added, when no region of `m` is empty. -/
theorem heapBlock_size {m : Memory} {p n n' : Nat} (hf : Fresh m p n) (hn : 0 < n)
    (hne : ∀ r ∈ m.regions, 0 < r.size) (h : (⟨p, n', true⟩ : Region) ∈ m.regions ++ [⟨p, n, true⟩, heapToken p n]) :
    n' = n := by
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h
  · have := hne _ h; rcases hf.2 _ h with h1 | h1 <;> simp at h1 this <;> omega
  · simp at h; exact h
  · simp [heapToken, heapTag] at h

/-! ## The libc contract -/

/-- One external function of a contract: its stub name, when a call is defined, its results. -/
structure Spec where
  name : String
  safe : State → Prop
  next : State → State → Prop

/-- The contract of a list of functions (the first spec of a name applies). -/
def ofSpecs (l : List Spec) : Contract where
  safe f s := ∃ sp ∈ l, sp.name = f ∧ sp.safe s
  next f s s' := ∃ sp ∈ l, sp.name = f ∧ sp.safe s ∧ sp.next s s'

/-- Use a spec of the list at its stub. -/
theorem ofSpecs_safe {l : List Spec} {sp : Spec} (hm : sp ∈ l) {s : State} (h : sp.safe s) :
    (ofSpecs l).safe sp.name s := ⟨sp, hm, rfl, h⟩

/-- A result at a stub whose name only one spec of the list has. -/
theorem ofSpecs_next {l : List Spec} {sp : Spec} (hm : sp ∈ l)
    (hu : ∀ sp' ∈ l, sp'.name = sp.name → sp' = sp) {s s' : State}
    (h : (ofSpecs l).next sp.name s s') : sp.next s s' := by
  obtain ⟨sp', hm', hn, -, hx⟩ := h
  rw [hu sp' hm' hn] at hx; exact hx

theorem ofSpecs_total {l : List Spec} (h : ∀ sp ∈ l, ∀ s, sp.safe s → ∃ s', sp.next s s') :
    (ofSpecs l).Total := fun _ s ⟨sp, hm, hn, hs⟩ =>
  let ⟨s', h'⟩ := h sp hm s hs; ⟨s', sp, hm, hn, hs, h'⟩

/-- `memcpy(d, s, n)`: `n` readable bytes at `s` and `n` writable bytes at `d`, not overlapping
(C11 7.24.2.1); returns `d`. -/
def memcpySpec (name : String := "memcpy@plt") : Spec where
  name := name
  safe s := LibcCall s ∧ Buffer s (s.regs 0) (s.regs 2).toNat true ∧
    Buffer s (s.regs 1) (s.regs 2).toNat false ∧
    ((s.regs 0).toNat + (s.regs 2).toNat ≤ (s.regs 1).toNat ∨
      (s.regs 1).toNat + (s.regs 2).toNat ≤ (s.regs 0).toNat)
  next s s' := LibcRet s s' (copyMem s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat)
    (· = s.regs 0)

/-- `__memcpy_chk(d, s, n, dlen)` (`_FORTIFY_SOURCE`): `memcpy` when `n ≤ dlen`; otherwise it
aborts, so the call is not allowed. -/
def memcpyChkSpec : Spec where
  name := "__memcpy_chk@plt"
  safe s := (memcpySpec).safe s ∧ (s.regs 2).toNat ≤ (s.regs 3).toNat
  next s s' := (memcpySpec).next s s'

/-- `memmove(d, s, n)`: the buffers may overlap (C11 7.24.2.2); returns `d`. -/
def memmoveSpec (name : String := "memmove@plt") : Spec where
  name := name
  safe s := LibcCall s ∧ Buffer s (s.regs 0) (s.regs 2).toNat true ∧
    Buffer s (s.regs 1) (s.regs 2).toNat false
  next s s' := LibcRet s s' (copyMem s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat)
    (· = s.regs 0)

def memmoveChkSpec : Spec where
  name := "__memmove_chk@plt"
  safe s := (memmoveSpec).safe s ∧ (s.regs 2).toNat ≤ (s.regs 3).toNat
  next s s' := (memmoveSpec).next s s'

/-- `memset(d, c, n)`: `n` writable bytes at `d` set to `(unsigned char) c` (C11 7.24.6.1);
returns `d`. -/
def memsetSpec (name : String := "memset@plt") : Spec where
  name := name
  safe s := LibcCall s ∧ Buffer s (s.regs 0) (s.regs 2).toNat true
  next s s' := LibcRet s s' (setMem s.mem (s.regs 0).toNat ((s.regs 1).toNat % 256) (s.regs 2).toNat)
    (· = s.regs 0)

def memsetChkSpec : Spec where
  name := "__memset_chk@plt"
  safe s := (memsetSpec).safe s ∧ (s.regs 2).toNat ≤ (s.regs 3).toNat
  next s s' := (memsetSpec).next s s'

/-- `strlen(p)`: a terminated string at `p` (C11 7.24.6.3); returns its length. -/
def strlenSpec : Spec where
  name := "strlen@plt"
  safe s := LibcCall s ∧ ∃ n, CStr s.mem (s.regs 0).toNat n
  next s s' := ∃ n, CStr s.mem (s.regs 0).toNat n ∧ LibcRet s s' s.mem (· = BitVec.ofNat 64 n)

/-- `strcmp(a, b)`: two terminated strings (C11 7.24.4.2); returns an `int` with the sign of
their lexicographic comparison as `unsigned char`s. -/
def strcmpSpec : Spec where
  name := "strcmp@plt"
  safe s := LibcCall s ∧ (∃ n, CStr s.mem (s.regs 0).toNat n) ∧ ∃ n, CStr s.mem (s.regs 1).toNat n
  next s s' := ∃ na nb, CStr s.mem (s.regs 0).toNat na ∧ CStr s.mem (s.regs 1).toNat nb ∧
    LibcRet s s' s.mem (CmpResult (lexCmp (cstrBytes s.mem (s.regs 0).toNat na)
      (cstrBytes s.mem (s.regs 1).toNat nb)))

/-- `malloc(n)`: null, memory unchanged; or a 16-aligned (glibc's `MALLOC_ALIGNMENT` on
AArch64) non-null pointer to a fresh block of `n` bytes with indeterminate contents, now a live
heap block (C11 7.22.3.4). -/
def mallocSpec : Spec where
  name := "malloc@plt"
  safe s := LibcCall s
  next s s' := LibcRet s s' s.mem (· = 0) ∨
    ∃ p junk, p ≠ 0 ∧ p % 16 = 0 ∧ Fresh s.mem p (s.regs 0).toNat ∧
      LibcRet s s' (heapAlloc s.mem p (s.regs 0).toNat junk) (· = BitVec.ofNat 64 p)

/-- `free(p)`: `p` null (nothing happens) or a live block, which is released (C11 7.22.3.3). -/
def freeSpec : Spec where
  name := "free@plt"
  safe s := LibcCall s ∧ (s.regs 0 = 0 ∨ ∃ n, HeapBlock s.mem (s.regs 0).toNat n)
  next s s' := (s.regs 0 = 0 ∧ LibcRet s s' s.mem fun _ => True) ∨
    ∃ n junk, HeapBlock s.mem (s.regs 0).toNat n ∧
      LibcRet s s' (heapFree s.mem (s.regs 0).toNat n junk) fun _ => True

/-- The functions of the `Libc` contract. -/
def libcSpecs : List Spec :=
  [memcpySpec, memcpyChkSpec, memmoveSpec, memmoveChkSpec, memsetSpec, memsetChkSpec, strlenSpec,
   strcmpSpec, mallocSpec, freeSpec]

/-- The **trusted** libc contract (glibc on Linux/arm64, called through the PLT). -/
def Libc : Contract := ofSpecs libcSpecs

/-- Each name occurs once in `libcSpecs`. -/
theorem libcSpecs_unique : ∀ sp ∈ libcSpecs, ∀ sp' ∈ libcSpecs, sp'.name = sp.name → sp' = sp := by
  simp only [libcSpecs, List.mem_cons, List.mem_nil_iff, or_false]
  intro sp hsp sp' hsp' hn
  rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hsp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | rfl | (simp only [memcpySpec, memcpyChkSpec, memmoveSpec, memmoveChkSpec, memsetSpec, memsetChkSpec, strlenSpec, strcmpSpec, mallocSpec, freeSpec] at hn; exact absurd hn (by decide))

theorem libc_next {sp : Spec} (hm : sp ∈ libcSpecs) {s s' : State}
    (h : Libc.next sp.name s s') : sp.next s s' :=
  ofSpecs_next hm (fun sp' hm' hn => libcSpecs_unique sp hm sp' hm' hn) h

theorem libc_safe {sp : Spec} (hm : sp ∈ libcSpecs) {s : State} (h : sp.safe s) :
    Libc.safe sp.name s := ofSpecs_safe hm h

/-- A libc call in a run: prove the spec's precondition, then continue from every result. -/
theorem libc_call {sp : Spec} (hm : sp ∈ libcSpecs) {S : State} {K : State → Prop}
    (hs : sp.safe S) (hk : ∀ s', sp.next S s' → K s') :
    Libc.safe sp.name S ∧ ∀ s', Libc.next sp.name S s' → K s' :=
  ⟨libc_safe hm hs, fun s' h => hk s' (libc_next hm h)⟩

/-- `LibcCall` for a caller that keeps `k` bytes of frame below the `SP` of its own window. -/
theorem libcCall_of {s t : State} {k : Nat} {rs : List (Nat × Nat)} (h : CStack s (libcStack + k) 0)
    (h16 : k % 16 = 0) (hsp : t.sp.toNat = s.sp.toNat - k) (hf : MemFrame s.mem t.mem rs) :
    LibcCall t := by
  have := CStack.frame (n := k) h (by omega) h16 hsp hf
  unfold LibcCall; simpa using CStack.mono this (Nat.le_refl _) (Nat.zero_le _)

/-! ## `setjmp` and `longjmp`: a non-local return -/

/-- What `_setjmp` saves (glibc `sysdeps/aarch64/setjmp.S`): the callee-saved general registers
`X19`–`X29`, the return address `X30`, `SP`, and the low halves of `V8`–`V15`. -/
structure JmpCtx where
  x : Fin 11 → W64
  lr : W64
  sp : W64
  d : Fin 8 → W64

/-- The context of a call to `_setjmp` in state `s`. -/
def jmpCtxOf (s : State) : JmpCtx :=
  ⟨fun i => s.regs (19 + i.val), s.regs 30, s.sp, fun i => (s.vregs (8 + i.val)).setWidth 64⟩

/-- `sizeof(jmp_buf)` on Linux/arm64 (glibc: 22 saved words, the `__mask_was_saved` flag,
padding and the 128-byte signal mask). -/
def jmpBufSize : Nat := 312

/-- The contents of a `jmp_buf`, abstractly: `holds m env c` says the `jmp_buf` at `env` in `m`
holds the context `c`. glibc's layout and pointer mangling (`PTR_MANGLE` of `SP`, `X29`, `X30`
with the process's pointer guard) are not part of the contract; a theorem quantifies over every
model with these laws, which glibc's encoding has (it is a function of the saved registers,
injective, and stored in the `jmp_buf`'s own bytes). -/
structure JmpModel where
  holds : Memory → Nat → JmpCtx → Prop
  /-- a `jmp_buf` holds at most one context -/
  unique : ∀ m env c c', holds m env c → holds m env c' → c = c'
  /-- what it holds depends only on its own bytes -/
  locality : ∀ m m' env c, (∀ i, i < jmpBufSize → m'.bytes (env + i) = m.bytes (env + i)) →
    holds m env c → holds m' env c
  /-- every context can be stored (into any memory, changing only the `jmp_buf`'s bytes) -/
  store : ∀ (m : Memory) env c, ∃ m' : Memory, m'.regions = m.regions ∧
    (∀ a, a < env ∨ env + jmpBufSize ≤ a → m'.bytes a = m.bytes a) ∧ holds m' env c

/-- `_setjmp(env)`: `env` is a writable `jmp_buf` (not in the stack bytes below `SP`); the call
stores the caller's context in it and returns 0 (the first return). -/
def setjmpSpec (J : JmpModel) (name : String := "_setjmp@plt") : Spec where
  name := name
  safe s := LibcCall s ∧ Buffer s (s.regs 0) jmpBufSize true ∧
    Outside (s.regs 0).toNat jmpBufSize [(s.sp.toNat - libcStack, s.sp.toNat)]
  next s s' := ∃ m, m.regions = s.mem.regions ∧
    (∀ a, a < (s.regs 0).toNat ∨ (s.regs 0).toNat + jmpBufSize ≤ a → m.bytes a = s.mem.bytes a) ∧
    J.holds m (s.regs 0).toNat (jmpCtxOf s) ∧ LibcRet s s' m (· = 0)

/-- `longjmp(env, v)` resumes the context `c` held in `env`: a second return from `_setjmp`,
at `c.lr` with `c`'s `SP`, `X19`–`X30` and `D8`–`D15`, and `W0 = v` (`1` if `v = 0`; the upper
half of `X0` zero). `FPCR`, the thread and memory are the current ones (outside the stack bytes
below the current `SP`); every other register is arbitrary. -/
structure LongjmpTo (s s' : State) (c : JmpCtx) : Prop where
  pc : s'.pc = c.lr
  lr : s'.regs 30 = c.lr
  sp : s'.sp = c.sp
  x : ∀ i : Fin 11, s'.regs (19 + i.val) = c.x i
  d : ∀ i : Fin 8, (s'.vregs (8 + i.val)).setWidth 64 = c.d i
  x0 : s'.regs 0 = if (s.regs 1).setWidth 32 = 0 then 1 else ((s.regs 1).setWidth 32).setWidth 64
  fpcr : s'.fpcr = s.fpcr
  tpidr : s'.tpidr = s.tpidr
  dczid : s'.dczid = s.dczid
  regions : s'.mem.regions = s.mem.regions
  mem : MemFrame s.mem s'.mem [(s.sp.toNat - libcStack, s.sp.toNat)]

/-- `longjmp(env, v)`: `env` holds a context (C11 7.13.2.1: the `setjmp` that saved it must not
have returned for good; this is the caller's obligation and not checkable here, but the
resumption does exactly what the hardware does with the saved registers). -/
def longjmpSpec (J : JmpModel) (name : String := "longjmp@plt") : Spec where
  name := name
  safe s := LibcCall s ∧ ∃ c, J.holds s.mem (s.regs 0).toNat c
  next s s' := ∃ c, J.holds s.mem (s.regs 0).toNat c ∧ LongjmpTo s s' c

/-- `__longjmp_chk(env, v)` (`_FORTIFY_SOURCE`'s `longjmp`): as `longjmp`, but glibc aborts when
the saved `SP` is below the current one (a jump into a frame that has returned), so the call is
only allowed upwards. -/
def longjmpChkSpec (J : JmpModel) : Spec where
  name := "__longjmp_chk@plt"
  safe s := LibcCall s ∧ ∃ c, J.holds s.mem (s.regs 0).toNat c ∧ s.sp.toNat ≤ c.sp.toNat
  next s s' := ∃ c, J.holds s.mem (s.regs 0).toNat c ∧ LongjmpTo s s' c

def setJmpSpecs (J : JmpModel) : List Spec :=
  [setjmpSpec J, longjmpSpec J, longjmpChkSpec J, longjmpSpec J "_longjmp@plt"]

/-- The **trusted** `setjmp`/`longjmp` contract, for the `jmp_buf` model `J`. -/
def SetJmp (J : JmpModel) : Contract := ofSpecs (setJmpSpecs J)

theorem setJmpSpecs_unique (J : JmpModel) :
    ∀ sp ∈ setJmpSpecs J, ∀ sp' ∈ setJmpSpecs J, sp'.name = sp.name → sp' = sp := by
  simp only [setJmpSpecs, List.mem_cons, List.mem_nil_iff, or_false]
  intro sp hsp sp' hsp' hn
  rcases hsp with rfl | rfl | rfl | rfl <;> rcases hsp' with rfl | rfl | rfl | rfl <;>
  first | rfl | (simp only [memcpySpec, memcpyChkSpec, memmoveSpec, memmoveChkSpec, memsetSpec, memsetChkSpec, strlenSpec, strcmpSpec, mallocSpec, freeSpec, setjmpSpec, longjmpSpec, longjmpChkSpec] at hn; exact absurd hn (by decide))

theorem setJmp_next {J : JmpModel} {sp : Spec} (hm : sp ∈ setJmpSpecs J) {s s' : State}
    (h : (SetJmp J).next sp.name s s') : sp.next s s' :=
  ofSpecs_next hm (fun sp' hm' hn => setJmpSpecs_unique J sp hm sp' hm' hn) h

theorem setJmp_safe {J : JmpModel} {sp : Spec} (hm : sp ∈ setJmpSpecs J) {s : State}
    (h : sp.safe s) : (SetJmp J).safe sp.name s := ofSpecs_safe hm h

/-- `Libc` and `SetJmp J` name different functions. -/
theorem libc_disjoint_setJmp (J : JmpModel) : Libc.Disjoint (SetJmp J) := by
  rintro f s s' ⟨sp, hm, rfl, -⟩ ⟨sp', hm', hn, -⟩
  simp only [libcSpecs, setJmpSpecs, List.mem_cons, List.mem_nil_iff, or_false] at hm hm'
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hm' with rfl | rfl | rfl | rfl <;> (simp only [memcpySpec, memcpyChkSpec, memmoveSpec, memmoveChkSpec, memsetSpec, memsetChkSpec, strlenSpec, strcmpSpec, mallocSpec, freeSpec, setjmpSpec, longjmpSpec, longjmpChkSpec] at hn; exact absurd hn (by decide))

/-! ## Thread-local storage

On Linux/arm64 (the AArch64 ELF TLS ABI, variant I) `TPIDR_EL0` points at the thread's thread
control block (16 bytes), followed by the executable's TLS block (module 1, the image of
`PT_TLS`, `Extracted.tls`) at the TCB size rounded up to the segment's alignment. glibc allocates
it with the thread (static TLS), so its address is fixed for the thread's lifetime. In an
executable the linker resolves every access to a variable of module 1 to a constant offset from
the thread pointer: local-exec (`MRS TPIDR_EL0` plus `ADD #:tprel_hi12:`/`#:tprel_lo12:`),
initial-exec relaxed to `MOVZ`/`MOVK` of the offset, and general-dynamic (TLSDESC) relaxed to the
same. These are ordinary instructions; what the theorem needs is where the block is
(`TLSBlock`). An unrelaxed TLS descriptor call (a shared object, or a variable of another module)
calls the descriptor's function: `TLSDescFn`. -/

/-- The offset of the executable's TLS block from the thread pointer. -/
def _root_.Janus.TLSImage.a64Off (t : TLSImage) : Nat := roundUp 16 t.align

/-- The address of the `__thread` variable `name` of the thread whose pointer is `tp`. -/
def _root_.Janus.TLSImage.a64Addr (t : TLSImage) (tp : W64) (name : String) : Nat :=
  tp.toNat + t.a64Off + t.varOff name

/-- The **TLS-block contract**: in state `s`, the thread's TLS block of the executable is
writable memory at `TPIDR_EL0 + a64Off`, of the segment's size, below `2^48`. -/
def TLSBlock (t : TLSImage) (s : State) : Prop :=
  s.tpidr.toNat + t.a64Off + t.size ≤ 2 ^ 48 ∧
    s.mem.accessible (s.tpidr.toNat + t.a64Off) t.size true = true

/-- A TLS descriptor's function (`blr` through the first word of the descriptor, AArch64 TLSDESC
ABI): called with `X0` the descriptor's address, it returns in `X0` the variable's offset from
the thread pointer (`off`) and preserves every other general register but `X30`, `SP`, the
SIMD&FP registers and memory (except its own stack bytes below `SP`, `stack`). -/
def TLSDescFn (p : Program) (f : W64) (desc off : Nat) (stack : Nat) : Prop :=
  f.toNat % 4 = 0 ∧ f.toNat < 2 ^ 48 ∧
  Summary p f.toNat (fun s => s.regs 0 = BitVec.ofNat 64 desc ∧ CStack s stack 0 ∧
      (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48)
    (fun s s' => s'.regs 0 = BitVec.ofNat 64 off ∧ (∀ i, i ≠ 0 → i ≠ 30 → s'.regs i = s.regs i) ∧
      s'.sp = s.sp ∧ s'.vregs = s.vregs ∧ s'.fpcr = s.fpcr ∧
      MemFrame s.mem s'.mem [(s.sp.toNat - stack, s.sp.toNat)])

end Janus.Contracts.Libc
