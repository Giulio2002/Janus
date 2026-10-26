import Janus.Contracts.CmpstringAmd64

/-!
# The `runtime.cmpstring` contract is satisfiable (amd64)

As `Janus.Contracts.CmpstringSat`: a byte loop in x86-64 machine code at `A0` meets
`CmpstringContract64`, and a call state satisfying its precondition exists.

```
loop: TEST RBX, RBX; JZ aend; TEST RDI, RDI; JZ gt
      MOVZX EDX, BYTE [RAX]; MOVZX ESI, BYTE [RCX]; CMP EDX, ESI; JB lt; JA gt
      ADD RAX, 1; ADD RCX, 1; SUB RBX, 1; SUB RDI, 1; JMP loop
aend: TEST RDI, RDI; JZ eq
lt:   MOV RAX, -1; RET
gt:   MOV EAX, 1; RET
eq:   XOR EAX, EAX; RET
```
-/

set_option linter.unusedSimpArgs false

namespace Janus.Contracts.CmpstringSatAmd64

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Cmpstring

/-- A program with no code, stubs or data of its own. -/
def toy : Janus.Amd64.Program := { segments := [], stubs := [], exitAddr := 0 }

/-- Where the implementation is placed. -/
abbrev A0 : Nat := 0x100000

/-- The byte loop. -/
def code : List Nat :=
  [0x48, 0x85, 0xdb, 0x74, 0x23, 0x48, 0x85, 0xff, 0x74, 0x2b, 0x0f, 0xb6, 0x10, 0x0f, 0xb6, 0x31,
   0x39, 0xf2, 0x72, 0x19, 0x77, 0x1f, 0x48, 0x83, 0xc0, 0x01, 0x48, 0x83, 0xc1, 0x01, 0x48, 0x83,
   0xeb, 0x01, 0x48, 0x83, 0xef, 0x01, 0xeb, 0xd8, 0x48, 0x85, 0xff, 0x74, 0x0e, 0x48, 0xc7, 0xc0,
   0xff, 0xff, 0xff, 0xff, 0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0x31, 0xc0, 0xc3]

/-- The implementation: `code` at `A0`. -/
def impl : List Janus.Amd64.Segment := [{ name := "cmpstring", base := A0, bytes := code }]

/-- `toy` linked with `impl`, as a closed program. -/
def prog : Janus.Amd64.Program := { segments := impl, stubs := [], exitAddr := 0 }

theorem link_eq : toy.link impl = prog := rfl

/-- The return of the implementation as `CmpRet64`. -/
theorem ret_of (s : State) (R : Nat → W64) (F : Flags) (hR0 : R 0 = cmpResult64 s)
    (h4 : R 4 = s.regs 4 + 8#64) (h5 : R 5 = s.regs 5) (h14 : R 14 = s.regs 14) :
    CmpRet64 16 s { s with regs := R, flags := F, rip := retAddrOf s } := by
  refine ⟨R, F, s.xmm, s.ymmHi, s.mem, s.zmmHi, s.kreg, ?_, MemFrame.refl _ _⟩
  simp only [retState64]
  congr 1
  · funext i
    simp only [callRegs64]
    by_cases e4 : i = 4
    · subst e4; simp [h4]
    by_cases e5 : i = 5 ∨ i = 14
    · rcases e5 with rfl | rfl <;> simp [h5, h14]
    simp only [e4, e5, ite_false]
    by_cases e0 : i = 0
    · subst e0; simp [hR0]
    by_cases e3 : i = 3
    · subst e3; simp
    by_cases e1 : i = 1
    · subst e1; simp
    simp [e0, e3, e1]
  · funext i; split <;> simp_all

/-- The loop, from its head with `la` bytes of `a` left. -/
theorem loop (s : State) (hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hacc : s.mem.accessible (s.regs 4).toNat 8 false = true) (hnw : (s.regs 4).toNat + 8 ≤ 2 ^ 48) :
    ∀ la (R : Nat → W64) (F : Flags) (a b lb : Nat),
      R 0 = BitVec.ofNat 64 a → R 3 = BitVec.ofNat 64 la → R 1 = BitVec.ofNat 64 b →
      R 7 = BitVec.ofNat 64 lb → la < 2 ^ 64 → lb < 2 ^ 64 →
      R 4 = s.regs 4 → R 5 = s.regs 5 → R 14 = s.regs 14 →
      StrOK s.mem a la → StrOK s.mem b lb →
      strCmp s.mem a b la lb = strCmp s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 3).toNat (s.regs 7).toNat →
      ReachesRet prog (retAddrOf s) { s with regs := R, flags := F, rip := 0x100000#64 } (CmpRet64 16 s) := by
  intro la
  induction la with
  | zero =>
    intro R F a b lb h0 h3 h1 h7 hla hlb h4 h5 h14 hsa hsb hc
    janus64_run [h0, h1, h3, h7, h4]
    all_goals
      apply ret_of
      all_goals try (simp only [setRegF]; simp [h4, h5, h14])
      simp only [cmpResult64]
      rw [← hc]
      clear hc
      cases lb <;> simp_all [strCmp] <;> decide
  | succ la ih =>
    intro R F a b lb h0 h3 h1 h7 hla hlb h4 h5 h14 hsa hsb hc
    rcases hsa with hsa | ⟨hsa1, hsa2⟩
    · omega
    have ha1 : s.mem.accessible a 1 false = true :=
      Janus.Arm64.Memory.accessible_mono _ hsa1 (Nat.le_refl _) (by omega)
    cases lb with
    | zero =>
      janus64_run [h0, h1, h3, h7, h4]
      all_goals
        apply ret_of
        all_goals try (simp only [setRegF]; simp [h4, h5, h14])
        simp only [cmpResult64]
        rw [← hc]
        clear hc
        simp [strCmp]
    | succ lb =>
      rcases hsb with hsb | ⟨hsb1, hsb2⟩
      · omega
      have hb1 : s.mem.accessible b 1 false = true :=
        Janus.Arm64.Memory.accessible_mono _ hsb1 (Nat.le_refl _) (by omega)
      have hx : s.mem.readLE a 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem a 1
      have hy : s.mem.readLE b 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem b 1
      have e : ∀ x, x < 256 → BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x)))
          = BitVec.ofNat 32 x := by
        intro x hx; apply BitVec.eq_of_toNat_eq; simp; omega
      have hsub : (BitVec.ofNat 32 (s.mem.readLE a 1) - BitVec.ofNat 32 (s.mem.readLE b 1) = 0#32) ↔
          s.mem.readLE a 1 = s.mem.readLE b 1 := by
        constructor
        · intro h; have := congrArg BitVec.toNat h
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
        · intro h; rw [h]; simp
      janus64_run [h0, h1, h3, h7, h4] until [0x100000]
      all_goals simp only [e _ hx, e _ hy, hsub, Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 4294967296),
        Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 4294967296)] at *
      all_goals first
        | (apply ret_of
           all_goals try (simp only [setRegF]; simp [h4, h5, h14])
           simp only [cmpResult64]
           rw [← hc]
           clear hc
           simp only [strCmp]
           split <;> (try split) <;> first | rfl | omega | decide)
        | skip
      apply ih _ _ (a + 1) (b + 1) lb
      all_goals try (simp only [setRegF]; simp [h4, h5, h14])
      all_goals first
        | (apply BitVec.eq_of_toNat_eq; simp <;> omega)
        | omega
        | (by_cases hl : la = 0
           · exact Or.inl hl
           · exact Or.inr ⟨Janus.Arm64.Memory.accessible_mono _ hsa1 (by omega) (by omega), by omega⟩)
        | (by_cases hl : lb = 0
           · exact Or.inl hl
           · exact Or.inr ⟨Janus.Arm64.Memory.accessible_mono _ hsb1 (by omega) (by omega), by omega⟩)
        | (rw [← hc]; simp only [strCmp, hbr, Nat.lt_irrefl, ite_false])

/-- The byte loop meets the contract. -/
theorem impl_ok : CmpstringContract64 (toy.link impl) A0 16 := by
  rw [link_eq]
  intro s hpc ⟨⟨hr, _, hst, _, hw⟩, hsa, hsb⟩
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  have key := loop s hr hacc (by omega) (s.regs 3).toNat s.regs s.flags (s.regs 0).toNat (s.regs 1).toNat
    (s.regs 7).toNat (by simp) (by simp) (by simp) (by simp) (s.regs 3).isLt (s.regs 7).isLt rfl rfl rfl
    hsa hsb rfl
  have hs : ({ s with regs := s.regs, flags := s.flags, rip := 0x100000#64 } : State) = s := by
    cases s; simp only at hpc ⊢; rw [hpc]
  rw [hs] at key
  exact key

/-- The witness call state: two empty strings, `RSP = 0x1800` in a writable region holding a zero
return address. -/
def wstate : State :=
  { regs := fun i => if i = 4 then 0x1800#64 else 0#64, rip := BitVec.ofNat 64 A0,
    flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := ⟨fun _ => 0, [⟨0x1000, 0x1000, true⟩]⟩,
    ymmHi := fun _ => 0, fsBase := 0, df := false, mxcsr := 0x1F80 }

theorem wstate_pre : CmpstringPre64 16 wstate := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, Or.inl (by decide), Or.inl (by decide)⟩

/-- `CmpstringContract64` is satisfiable. -/
theorem cmpstring64_satisfiable : ∃ impl : List Janus.Amd64.Segment,
    CmpstringContract64 (toy.link impl) A0 16 ∧
    ∃ s : State, s.rip = BitVec.ofNat 64 A0 ∧ CmpstringPre64 16 s :=
  ⟨impl, impl_ok, wstate, rfl, wstate_pre⟩

end Janus.Contracts.CmpstringSatAmd64
