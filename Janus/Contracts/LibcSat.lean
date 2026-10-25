import Janus.Contracts.Libc

/-!
# The C environment contracts are satisfiable (arm64)

A contract whose `next` is empty for some allowed call would make every theorem about a run
reaching that call vacuous there (`ReturnsC.ext` asks for every result, of which there would be
none). So every contract of the C environment comes with a witness:

* `libc_satisfiable`, `setJmp_satisfiable`: `Libc` and `SetJmp J` are **total**
  (`Contract.Total`): every call they allow has a result, for every `jmp_buf` model `J`;
* `jmpModel_satisfiable`: a `jmp_buf` model exists (glibc's is one; here, the saved words
  stored in order);
* `cgoCallback_satisfiable`: `CgoCallback p Cin (fun _ => True)` is total when the Go code's
  own contract `Cin` is and an admissible return address exists;
* `tlsDescFn_satisfiable`: a TLS descriptor function exists, as machine code (`MOVZ X0, #off;
  RET`, what glibc's `_dl_tlsdesc_return` computes for a static TLS variable) proved by symbolic
  execution.
-/

namespace Janus.Contracts.LibcSat

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.CABI Janus.FFI Janus.Contracts.Libc

/-- The state after a call from `s` returned `r` with memory `m`, every other register kept. -/
def retState (s : State) (r : W64) (m : Memory) : State :=
  { s with regs := setReg s.regs 0 r, pc := s.regs 30, mem := m }

theorem libcRet_retState (s : State) (r : W64) (m : Memory) :
    LibcRet s (retState s r m) m (· = r) where
  pc := rfl
  x0 := by simp [retState, setReg]
  cret := by
    refine CReturn.of_eqs rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl <;> simp [retState, setReg]
  tpidr := rfl
  dczid := rfl
  regions := rfl
  mem := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem libcRet_retState' (s : State) (r : W64) (m : Memory) {P : W64 → Prop} (h : P r) :
    LibcRet s (retState s r m) m P :=
  let h' := libcRet_retState s r m
  { h' with x0 := by rw [h'.x0]; exact h }

/-- An `int` result of every sign. -/
def cmpValue : Ordering → W64
  | .lt => BitVec.ofInt 64 (-1)
  | .eq => 0
  | .gt => 1

theorem cmpResult_cmpValue (o : Ordering) : CmpResult o (cmpValue o) := by
  cases o <;> (simp only [CmpResult, cmpValue]; decide)

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
    exact ⟨_, na, nb, ha, hb, libcRet_retState' _ _ _ (cmpResult_cmpValue _)⟩
  · exact ⟨_, .inl (libcRet_retState _ _ _)⟩
  · obtain ⟨-, h0 | ⟨n, hb⟩⟩ := hs
    · exact ⟨_, .inl ⟨h0, libcRet_retState' _ 0 _ trivial⟩⟩
    · exact ⟨_, .inr ⟨n, s.mem.bytes, hb, libcRet_retState' _ 0 _ trivial⟩⟩

/-! ## `jmp_buf` -/

/-- The 21 words of a context, in order. -/
def jmpWords (c : JmpCtx) (k : Nat) : W64 :=
  if h : k < 11 then c.x ⟨k, h⟩ else if k = 11 then c.lr else if k = 12 then c.sp
  else if h' : k - 13 < 8 then c.d ⟨k - 13, h'⟩ else 0

theorem jmpWords_inj {c c' : JmpCtx} (h : ∀ k, k < 21 → jmpWords c k = jmpWords c' k) :
    c = c' := by
  obtain ⟨x, lr, sp, d⟩ := c
  obtain ⟨x', lr', sp', d'⟩ := c'
  have hx : x = x' := funext fun i => by
    have := h i.val (by omega); simpa [jmpWords, i.isLt] using this
  have hlr : lr = lr' := by have := h 11 (by omega); simpa [jmpWords] using this
  have hsp : sp = sp' := by have := h 12 (by omega); simpa [jmpWords] using this
  have hd : d = d' := funext fun i => by
    have := h (13 + i.val) (by omega)
    simp only [jmpWords, show ¬ 13 + i.val < 11 by omega, show 13 + i.val ≠ 11 by omega,
      show 13 + i.val ≠ 12 by omega, show 13 + i.val - 13 = i.val by omega, i.isLt, dite_false,
      ite_false, dite_true] at this
    exact this
  subst hx hlr hsp hd; rfl

/-- The model: the 21 words stored in order from `env`. -/
def wordModel : JmpModel where
  holds m env c := ∀ k, k < 21 → m.readLE (env + 8 * k) 8 = (jmpWords c k).toNat
  unique m env c c' h h' := jmpWords_inj fun k hk => BitVec.eq_of_toNat_eq ((h k hk).symm.trans (h' k hk))
  locality m m' env c hb h k hk := by
    rw [← h k hk]
    exact Memory.readLE_congr fun i hi => by
      have := hb (8 * k + i) (by simp only [jmpBufSize]; omega)
      rw [Nat.add_assoc]; exact this
  store m env c := by
    refine ⟨{ m with bytes := (fun a => if env ≤ a ∧ a < env + 168 then
        (m.writeLE (env + 8 * ((a - env) / 8)) 8 (jmpWords c ((a - env) / 8)).toNat).bytes a
        else m.bytes a) }, rfl, fun a ha => ?_, fun k hk => ?_⟩
    · simp only [jmpBufSize] at ha
      simp only; rw [if_neg (by omega)]
    · rw [Memory.readLE_congr (m' := m.writeLE (env + 8 * k) 8 (jmpWords c k).toNat) fun i hi => by
        simp only
        rw [if_pos (by omega), show (env + 8 * k + i - env) / 8 = k by omega]]
      rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (jmpWords c k).isLt]

theorem jmpModel_satisfiable : Nonempty JmpModel := ⟨wordModel⟩

theorem setWidth_setWidth_64 (x : W64) : (x.setWidth 128).setWidth 64 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide)), Nat.mod_eq_of_lt x.isLt]

/-- The state `longjmp` resumes, for the context `c`. -/
def jmpState (s : State) (c : JmpCtx) : State :=
  { s with
    pc := c.lr, sp := c.sp,
    regs := fun i => if i = 30 then c.lr else if h : 19 ≤ i ∧ i < 30 then c.x ⟨i - 19, by omega⟩
      else if i = 0 then
        (if (s.regs 1).setWidth 32 = 0 then 1 else ((s.regs 1).setWidth 32).setWidth 64)
      else s.regs i,
    vregs := fun i => if h : 8 ≤ i ∧ i < 16 then (c.d ⟨i - 8, by omega⟩).setWidth 128 else s.vregs i }

theorem longjmpTo_jmpState (s : State) (c : JmpCtx) : LongjmpTo s (jmpState s c) c where
  pc := rfl
  lr := by simp [jmpState]
  sp := rfl
  x i := by
    have := i.isLt
    simp only [jmpState, show 19 + i.val ≠ 30 by omega, ite_false,
      show 19 ≤ 19 + i.val ∧ 19 + i.val < 30 from ⟨by omega, by omega⟩, dite_true]
    congr 1; ext; simp
  d i := by
    have := i.isLt
    show ((if h : 8 ≤ 8 + i.val ∧ 8 + i.val < 16 then (c.d ⟨8 + i.val - 8, by omega⟩).setWidth 128
      else s.vregs (8 + i.val)) : BitVec 128).setWidth 64 = c.d i
    rw [dif_pos ⟨by omega, by omega⟩, setWidth_setWidth_64]; congr 1; ext; simp
  x0 := by simp [jmpState]
  fpcr := rfl
  tpidr := rfl
  dczid := rfl
  regions := rfl
  mem := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem setJmp_satisfiable (J : JmpModel) : (SetJmp J).Total := by
  apply ofSpecs_total
  simp only [setJmpSpecs, List.mem_cons, List.mem_nil_iff, or_false]
  rintro sp (rfl | rfl | rfl | rfl) s hs
  · obtain ⟨m, hr, hb, hh⟩ := J.store s.mem (s.regs 0).toNat (jmpCtxOf s)
    exact ⟨_, m, hr, hb, hh, libcRet_retState _ _ _⟩
  · obtain ⟨-, c, hc⟩ := hs
    exact ⟨_, c, hc, longjmpTo_jmpState s c⟩
  · obtain ⟨-, c, hc, -⟩ := hs
    exact ⟨_, c, hc, longjmpTo_jmpState s c⟩
  · obtain ⟨-, c, hc⟩ := hs
    exact ⟨_, c, hc, longjmpTo_jmpState s c⟩

/-! ## `cgocallback` -/

/-- A Go call state `cgocallback` may make from every C state: on a goroutine stack at `2^50`,
far from every C region (below `2^48`), with the C state's memory. -/
def cbState (s : State) (ret : Nat) : State :=
  { s with pc := BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 8) 8),
           regs := setReg (setReg s.regs 0 (BitVec.ofNat 64 (s.mem.readLE (s.sp.toNat + 16) 8)))
             30 (BitVec.ofNat 64 ret),
           sp := BitVec.ofNat 64 (2 ^ 50) }

theorem callbackEntry_cbState {p : Program} {ret : Nat} (s : State) (hret : RetAddr p ret) :
    CallbackEntry p s (cbState s ret) ret where
  pc := rfl
  arg := by simp [cbState, setReg]
  lr := by simp [cbState, setReg]
  retAddr := hret
  stackSep a n w h := by
    have := Memory.accessible_bound s.mem h
    simp only [outside_cons, outside_nil, and_true, cbState, cbGoStack]
    left; simp only [BitVec.toNat_ofNat]; omega
  kept _ _ _ := rfl
  keptAcc _ _ _ h := h.1
  tpidr := rfl
  dczid := rfl
  fpcr := rfl

/-- The resumed C state of a final Go state `u'`. -/
def cbResumeState (s u' : State) : State :=
  { s with pc := s.regs GoABI.regLR,
           mem := { bytes := fun a => if s.mem.accessible a 1 false then u'.mem.bytes a else s.mem.bytes a,
                    regions := s.mem.regions } }

theorem cbResumed_cbResumeState (s u' : State) : CbResumed s u' (cbResumeState s u') :=
  ⟨_, ⟨s.regs, s.flags, s.vregs, s.fpsr, rfl⟩, rfl, fun _ _ => rfl⟩

theorem cgoCallback_satisfiable {p : Program} {Cin : Contract} {ret : Nat} (hC : Cin.Total)
    (hret : RetAddr p ret) : (CgoCallback p Cin (fun _ => True)).Total := by
  rintro f s ⟨hf, -, hgo⟩
  obtain ⟨u', hr, hab⟩ := (hgo _ ret (callbackEntry_cbState s hret) trivial).exists_runsTo hC
  exact ⟨_, hf, _, ret, u', callbackEntry_cbState s hret, trivial, hr, hab,
    cbResumed_cbResumeState s u'⟩

/-! ## A TLS descriptor function -/

/-- The program with the descriptor function `MOVZ X0, #off; RET` at `A0`. -/
def A0 : Nat := 0x100000
def descProg (off : Nat) : Program :=
  { segments := [{ name := "tlsdesc", base := A0, words := [0xd2800000 + 32 * off, 0xd65f03c0] }],
    stubs := [], exitAddr := 0 }

theorem tlsDescFn_satisfiable (desc : Nat) :
    TLSDescFn (descProg 0x10) (BitVec.ofNat 64 A0) desc 0x10 0 := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hpc ⟨hd, hst, hl1, hl2⟩
  simp only [descProg, A0] at hpc ⊢
  janus_run
  exact ⟨fun i h0 _ => by simp [h0], ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

end Janus.Contracts.LibcSat
