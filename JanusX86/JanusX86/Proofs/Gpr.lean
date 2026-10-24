import JanusX86.Proofs.Monad

/-! # General-purpose registers of the generated model

`read_gpr`/`write_gpr` dispatch on the register number (encoding order `RAX RCX RDX RBX RSP RBP
RSI RDI R8..R15`) to the 16 Sail registers `rax`..`r15`. -/

set_option linter.unusedSimpArgs false

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

/-- The value of GPR `i < 16` held in a Sail state (`none` if the register is missing). -/
def gprVal (s : SState) : Nat → Option (BitVec 64)
  | 0 => s.regs.get? .rax
  | 1 => s.regs.get? .rcx
  | 2 => s.regs.get? .rdx
  | 3 => s.regs.get? .rbx
  | 4 => s.regs.get? .rsp
  | 5 => s.regs.get? .rbp
  | 6 => s.regs.get? .rsi
  | 7 => s.regs.get? .rdi
  | 8 => s.regs.get? .r8
  | 9 => s.regs.get? .r9
  | 10 => s.regs.get? .r10
  | 11 => s.regs.get? .r11
  | 12 => s.regs.get? .r12
  | 13 => s.regs.get? .r13
  | 14 => s.regs.get? .r14
  | 15 => s.regs.get? .r15
  | _ => none

/-- GPR `i := v` in a Sail state. -/
def setGpr (s : SState) (v : BitVec 64) : Nat → SState
  | 0 => s.set .rax v
  | 1 => s.set .rcx v
  | 2 => s.set .rdx v
  | 3 => s.set .rbx v
  | 4 => s.set .rsp v
  | 5 => s.set .rbp v
  | 6 => s.set .rsi v
  | 7 => s.set .rdi v
  | 8 => s.set .r8 v
  | 9 => s.set .r9 v
  | 10 => s.set .r10 v
  | 11 => s.set .r11 v
  | 12 => s.set .r12 v
  | 13 => s.set .r13 v
  | 14 => s.set .r14 v
  | 15 => s.set .r15 v
  | _ => s

/-- The Sail registers holding GPRs. -/
def isGprReg : Register → Bool
  | .rax => true
  | .rcx => true
  | .rdx => true
  | .rbx => true
  | .rsp => true
  | .rbp => true
  | .rsi => true
  | .rdi => true
  | .r8 => true
  | .r9 => true
  | .r10 => true
  | .r11 => true
  | .r12 => true
  | .r13 => true
  | .r14 => true
  | .r15 => true
  | _ => false

theorem run_read_gpr {s : SState} {i : Nat} (hi : i < 16) {v : BitVec 64}
    (h : gprVal s i = some v) : (read_gpr i).run s = .ok v s := by
  match i, hi with
  | 0, _ => exact run_readReg h
  | 1, _ => exact run_readReg h
  | 2, _ => exact run_readReg h
  | 3, _ => exact run_readReg h
  | 4, _ => exact run_readReg h
  | 5, _ => exact run_readReg h
  | 6, _ => exact run_readReg h
  | 7, _ => exact run_readReg h
  | 8, _ => exact run_readReg h
  | 9, _ => exact run_readReg h
  | 10, _ => exact run_readReg h
  | 11, _ => exact run_readReg h
  | 12, _ => exact run_readReg h
  | 13, _ => exact run_readReg h
  | 14, _ => exact run_readReg h
  | 15, _ => exact run_readReg h
  | _ + 16, hi => exact absurd hi (by omega)

theorem run_write_gpr {s : SState} (hl : s.regs.get? .log_register_writes = some false) {i : Nat}
    (hi : i < 16) (v : BitVec 64) : (write_gpr i v).run s = .ok () (setGpr s v i) := by
  match i, hi with
  | 0, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 1, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 2, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 3, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 4, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 5, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 6, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 7, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 8, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 9, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 10, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 11, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 12, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 13, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 14, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | 15, _ => simp only [write_gpr, run_bind, run_writeReg]; rw [run_readReg (by rw [get?_set_ne _ _ (by decide)]; exact hl)]; rfl
  | _ + 16, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_same (s : SState) {i : Nat} (hi : i < 16) (v : BitVec 64) :
    gprVal (setGpr s v i) i = some v := by
  match i, hi with
  | 0, _ => simp [gprVal, setGpr, get?_set_same]
  | 1, _ => simp [gprVal, setGpr, get?_set_same]
  | 2, _ => simp [gprVal, setGpr, get?_set_same]
  | 3, _ => simp [gprVal, setGpr, get?_set_same]
  | 4, _ => simp [gprVal, setGpr, get?_set_same]
  | 5, _ => simp [gprVal, setGpr, get?_set_same]
  | 6, _ => simp [gprVal, setGpr, get?_set_same]
  | 7, _ => simp [gprVal, setGpr, get?_set_same]
  | 8, _ => simp [gprVal, setGpr, get?_set_same]
  | 9, _ => simp [gprVal, setGpr, get?_set_same]
  | 10, _ => simp [gprVal, setGpr, get?_set_same]
  | 11, _ => simp [gprVal, setGpr, get?_set_same]
  | 12, _ => simp [gprVal, setGpr, get?_set_same]
  | 13, _ => simp [gprVal, setGpr, get?_set_same]
  | 14, _ => simp [gprVal, setGpr, get?_set_same]
  | 15, _ => simp [gprVal, setGpr, get?_set_same]
  | _ + 16, hi => exact absurd hi (by omega)

theorem gprVal_setGpr_ne (s : SState) {i j : Nat} (hi : i < 16) (hj : j < 16) (hij : j ≠ i) (v : BitVec 64) :
    gprVal (setGpr s v i) j = gprVal s j := by
  match i, hi, j, hj with
  | 0, _, 0, _ => exact absurd rfl hij
  | 0, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 0, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 1, _ => exact absurd rfl hij
  | 1, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 1, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 2, _ => exact absurd rfl hij
  | 2, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 2, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 3, _ => exact absurd rfl hij
  | 3, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 3, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 4, _ => exact absurd rfl hij
  | 4, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 4, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 5, _ => exact absurd rfl hij
  | 5, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 5, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 6, _ => exact absurd rfl hij
  | 6, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 6, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 7, _ => exact absurd rfl hij
  | 7, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 7, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 8, _ => exact absurd rfl hij
  | 8, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 8, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 9, _ => exact absurd rfl hij
  | 9, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 9, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 10, _ => exact absurd rfl hij
  | 10, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 10, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 11, _ => exact absurd rfl hij
  | 11, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 11, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 12, _ => exact absurd rfl hij
  | 12, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 12, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 13, _ => exact absurd rfl hij
  | 13, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 13, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 14, _, 14, _ => exact absurd rfl hij
  | 14, _, 15, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 0, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 1, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 2, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 3, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 4, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 5, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 6, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 7, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 8, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 9, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 10, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 11, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 12, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 13, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 14, _ => simp [gprVal, setGpr, get?_set_ne]
  | 15, _, 15, _ => exact absurd rfl hij
  | _ + 16, hi, _, _ => exact absurd hi (by omega)
  | _, _, _ + 16, hj => exact absurd hj (by omega)

/-- A register other than a GPR is unchanged by `setGpr`. -/
theorem get?_setGpr_of_not (s : SState) (v : BitVec 64) {i : Nat} (hi : i < 16) {r : Register}
    (hr : isGprReg r = false) : (setGpr s v i).regs.get? r = s.regs.get? r := by
  match i, hi with
  | 0, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 1, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 2, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 3, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 4, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 5, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 6, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 7, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 8, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 9, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 10, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 11, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 12, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 13, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 14, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 15, _ => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | _ + 16, hi => exact absurd hi (by omega)

theorem gprVal_set_of_not (s : SState) {r : Register} (hr : isGprReg r = false) (v : RegisterType r) (i : Nat) :
    gprVal (s.set r v) i = gprVal s i := by
  match i with
  | 0 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 1 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 2 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 3 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 4 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 5 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 6 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 7 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 8 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 9 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 10 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 11 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 12 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 13 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 14 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | 15 => exact get?_set_ne _ _ (by rintro rfl; simp [isGprReg] at hr)
  | _ + 16 => rfl

end JanusX86.Proofs
