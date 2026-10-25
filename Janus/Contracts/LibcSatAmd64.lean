import Janus.Contracts.LibcSat
import Janus.Contracts.LibcAmd64

/-!
# The C environment contracts are satisfiable (amd64)

The x86-64 counterparts of `Janus.Contracts.LibcSat`: `libc_satisfiable`, `setJmp_satisfiable`,
`jmpModel_satisfiable`, `tlsGetAddr_satisfiable` (every allowed call has a result) and
`cgoCallback_satisfiable` (for a total inner contract and an admissible return address).
-/

namespace Janus.Contracts.LibcSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Amd64.CABI Janus.Amd64.FFI
open Janus.Contracts.LibcAmd64
open Janus.Contracts.Libc (CmpResult heapFree)

/-- The state after a call from `s` (at the stub) returned `r` with memory `m`. -/
def retState (s : State) (r : W64) (m : Memory) : State :=
  { s with regs := fun i => if i = 0 then r else if i = 4 then s.regs 4 + 8 else s.regs i,
           rip := retAddrOf s, mem := m, df := false }

theorem libcRet_retState' (s : State) (r : W64) (m : Memory) {P : W64 → Prop} (h : P r) :
    LibcRet s (retState s r m) m P where
  rip := rfl
  rax := by simp [retState]; exact h
  cret := ⟨by simp [retState, CABI.regSP], by simp [retState], by simp [retState], by simp [retState],
    by simp [retState], by simp [retState], by simp [retState], rfl, rfl, rfl⟩
  fs := rfl
  regions := rfl
  mem := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem libcRet_retState (s : State) (r : W64) (m : Memory) : LibcRet s (retState s r m) m (· = r) :=
  libcRet_retState' s r m rfl

theorem libc_satisfiable : Libc.Total := by
  apply ofSpecs_total
  simp only [libcSpecs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro sp (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) s hs
  · exact ⟨_, libcRet_retState _ _ _⟩
  · exact ⟨_, libcRet_retState _ _ _⟩
  · exact ⟨_, libcRet_retState _ _ _⟩
  · exact ⟨_, libcRet_retState _ _ _⟩
  · exact ⟨_, libcRet_retState _ _ _⟩
  · exact ⟨_, libcRet_retState _ _ _⟩
  · obtain ⟨-, n, hn⟩ := hs
    exact ⟨_, n, hn, libcRet_retState _ _ _⟩
  · obtain ⟨-, ⟨na, ha⟩, nb, hb⟩ := hs
    exact ⟨_, na, nb, ha, hb, libcRet_retState' _ _ _ (LibcSat.cmpResult_cmpValue _)⟩
  · exact ⟨_, .inl (libcRet_retState _ _ _)⟩
  · obtain ⟨-, h0 | ⟨n, hb⟩⟩ := hs
    · exact ⟨_, .inl ⟨h0, libcRet_retState' _ 0 _ trivial⟩⟩
    · exact ⟨_, .inr ⟨n, s.mem.bytes, hb, libcRet_retState' _ 0 _ trivial⟩⟩

theorem tlsGetAddr_satisfiable (block : Nat → Nat) : (TlsGetAddr block).Total := by
  apply ofSpecs_total
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  rintro sp rfl s -
  exact ⟨_, libcRet_retState _ _ _⟩

/-! ## `jmp_buf` -/

def jmpWords (c : JmpCtx64) (k : Nat) : W64 :=
  match k with
  | 0 => c.rbx | 1 => c.rbp | 2 => c.r12 | 3 => c.r13 | 4 => c.r14 | 5 => c.r15 | 6 => c.sp
  | 7 => c.pc | _ => 0

theorem jmpWords_inj {c c' : JmpCtx64} (h : ∀ k, k < 8 → jmpWords c k = jmpWords c' k) : c = c' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := c
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := c'
  have e1 := h 0 (by omega); have e2 := h 1 (by omega); have e3 := h 2 (by omega)
  have e4 := h 3 (by omega); have e5 := h 4 (by omega); have e6 := h 5 (by omega)
  have e7 := h 6 (by omega); have e8 := h 7 (by omega)
  simp only [jmpWords] at e1 e2 e3 e4 e5 e6 e7 e8
  subst e1 e2 e3 e4 e5 e6 e7 e8; rfl

def wordModel : JmpModel64 where
  holds m env c := ∀ k, k < 8 → m.readLE (env + 8 * k) 8 = (jmpWords c k).toNat
  unique m env c c' h h' := jmpWords_inj fun k hk => BitVec.eq_of_toNat_eq ((h k hk).symm.trans (h' k hk))
  locality m m' env c hb h k hk := by
    rw [← h k hk]
    exact Janus.FFI.readLE_congr fun i hi => by
      have := hb (8 * k + i) (by simp only [jmpBufSize64]; omega)
      rw [Nat.add_assoc]; exact this
  store m env c := by
    refine ⟨{ m with bytes := (fun a => if env ≤ a ∧ a < env + 64 then
        (m.writeLE (env + 8 * ((a - env) / 8)) 8 (jmpWords c ((a - env) / 8)).toNat).bytes a
        else m.bytes a) }, rfl, fun a ha => ?_, fun k hk => ?_⟩
    · simp only [jmpBufSize64] at ha
      simp only; rw [if_neg (by omega)]
    · rw [Janus.Arm64.Memory.readLE_congr (m' := m.writeLE (env + 8 * k) 8 (jmpWords c k).toNat) fun i hi => by
        simp only
        rw [if_pos (by omega), show (env + 8 * k + i - env) / 8 = k by omega]]
      rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (jmpWords c k).isLt]

theorem jmpModel_satisfiable : Nonempty JmpModel64 := ⟨wordModel⟩

def jmpState (s : State) (c : JmpCtx64) : State :=
  { s with
    rip := c.pc, df := false,
    regs := fun i => if i = 4 then c.sp else if i = 3 then c.rbx else if i = 5 then c.rbp
      else if i = 12 then c.r12 else if i = 13 then c.r13 else if i = 14 then c.r14
      else if i = 15 then c.r15 else if i = 0 then
        (if (s.regs 6).setWidth 32 = 0 then 1 else ((s.regs 6).setWidth 32).setWidth 64)
      else s.regs i }

theorem longjmpTo_jmpState (s : State) (c : JmpCtx64) : LongjmpTo s (jmpState s c) c where
  rip := rfl
  sp := by simp [jmpState]
  rbx := by simp [jmpState]
  rbp := by simp [jmpState]
  r12 := by simp [jmpState]
  r13 := by simp [jmpState]
  r14 := by simp [jmpState]
  r15 := by simp [jmpState]
  rax := by simp [jmpState]
  df := rfl
  mxcsr := rfl
  fpucw := rfl
  fs := rfl
  regions := rfl
  mem := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem setJmp_satisfiable (J : JmpModel64) : (SetJmp J).Total := by
  apply ofSpecs_total
  simp only [setJmpSpecs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro sp (rfl | rfl | rfl | rfl) s hs
  · obtain ⟨m, hr, hb, hh⟩ := J.store s.mem (s.regs 7).toNat (jmpCtxOf s)
    exact ⟨_, m, hr, hb, hh, libcRet_retState _ _ _⟩
  · obtain ⟨-, c, hc⟩ := hs
    exact ⟨_, c, hc, longjmpTo_jmpState s c⟩
  · obtain ⟨-, c, hc, -⟩ := hs
    exact ⟨_, c, hc, longjmpTo_jmpState s c⟩
  · obtain ⟨-, c, hc⟩ := hs
    exact ⟨_, c, hc, longjmpTo_jmpState s c⟩

/-! ## A TLS descriptor function: `mov $0x10, %eax; ret` -/

def A0 : Nat := 0x100000
def descProg : Janus.Amd64.Program :=
  { segments := [{ name := "tlsdesc", base := A0, bytes := [0xb8, 0x10, 0x00, 0x00, 0x00, 0xc3] }],
    stubs := [], exitAddr := 0 }

theorem tlsDescFn_satisfiable (desc : Nat) : TlsDescFn descProg (BitVec.ofNat 64 A0) desc 0x10 0 := by
  refine ⟨by decide, ?_⟩
  intro s hpc ⟨hd, ⟨ha, hb, hc, hw⟩, hr⟩
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add] at ha hb hc hw
  have hrd := Janus.Arm64.Memory.accessible_read_of_write _ hw
  simp only [descProg, A0] at hpc ⊢
  janus64_run
  exact ⟨fun i h0 h4 => by simp [h0, h4], ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

end Janus.Contracts.LibcSatAmd64
