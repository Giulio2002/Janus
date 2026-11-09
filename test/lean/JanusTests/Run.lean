import Janus.Run

/-! Tests for fetch on literal segment lists and the ISA-independent run lemmas. -/

namespace JanusTests.Run

open Janus Janus.Arm64

/-- `main.f2` and the first words of `main.small` as emitted by Go 1.26 for linux/arm64. -/
def prog : Program where
  segments := [
    { name := "main.small", base := 0x84500,
      words := [0xf9400b90, 0xeb3063ff, 0x540002a9, 0xf81e0ffe] },
    { name := "main.f2", base := 0x84580,
      words := [0xf81b0ffe, 0xf81f83fd, 0xd10023fd, 0x910023e1, 0xa9007c3f, 0xa9017c3f,
                0xa9027c3f, 0xa9037c3f, 0x92400802, 0xf8227820, 0xf94013e0, 0x910123fd,
                0x910143ff, 0xd65f03c0] } ]
  stubs := [{ name := "runtime.panicBounds", addr := 0x7a1b0, kind := .panic },
            { name := "runtime.morestack_noctxt.abi0", addr := 0x7f000, kind := .morestack }]
  exitAddr := 0xdead0000

/-! `fetch` by kernel evaluation (`decide` / `rfl`). -/
example : prog.fetch 0x84580 = some 0xf81b0ffe := by decide
example : prog.fetch 0x845b4 = some 0xd65f03c0 := by decide
example : prog.fetch 0x84504 = some 0xeb3063ff := rfl
example : prog.fetch 0x845b8 = none := by decide          -- one past the end of f2
example : prog.fetch 0x84582 = none := by decide          -- misaligned
example : prog.fetch 0x84510 = none := by decide          -- gap between segments

/-! `fetch` by `simp`, starting from a `BitVec` pc as it appears in a symbolic state. -/
example : prog.fetch (0x84588 : W64).toNat = some 0xd10023fd := by
  simp [prog, Program.fetch, Program.fetchIn]
example (s : State) (h : s.pc = 0x845a4) : prog.fetch s.pc.toNat = some 0xf8227820 := by
  simp [h, prog, Program.fetch, Program.fetchIn]
example : prog.fetch 0x84600 = none := by
  simp [prog, Program.fetch, Program.fetchIn]

/-! `fetch` by the structured lemmas. -/
example : prog.fetch 0x8458c = some 0x910023e1 := by
  rw [Program.fetch_eq]; simp only [prog]
  rw [Program.fetchIn_cons_miss (by decide), Program.fetchIn_cons_hit (by decide) (by decide)
    (by decide)]
  rfl
example : Program.fetchIn prog.segments (0x84580 + 4 * 13) = some 0xd65f03c0 := by
  simp only [prog]
  rw [Program.fetchIn_cons_miss (by decide)]
  exact Program.fetchIn_cons_index (seg := { name := "main.f2", base := 0x84580, words := _ })
    (i := 13) (by decide)

/-! `stubAt`. -/
example : prog.stubAt 0x7a1b0 = some { name := "runtime.panicBounds", addr := 0x7a1b0, kind := .panic } := rfl
example : prog.stubAt 0x84580 = none := by decide
example : prog.stubAt 0x84580 = none := by simp [Program.stubAt, prog]
example : prog.stubAt 0x84580 = none :=
  Program.stubAt_eq_none (by simp [prog])

/-! Run unfolding that does not depend on the instruction semantics. -/
example (s : State) (h : s.pc = 0xdead0000) (n : Nat) : prog.run (n + 1) s = .ok (.returned s) :=
  Program.run_succ_exit (by simp [h, prog])

example (s : State) (h : s.pc = 0x7a1b0) (n : Nat) :
    prog.run (n + 1) s = .ok (.stub "runtime.panicBounds" .panic s) :=
  Program.run_succ_stub (p := prog) (s := s)
    (st := { name := "runtime.panicBounds", addr := 0x7a1b0, kind := .panic })
    (by simp [h, prog]) (by simp [h]; rfl)

example (s : State) (h : s.pc = 0x84510) (n : Nat) :
    prog.run (n + 1) s = .error (.noCode 0x84510) := by
  have := Program.run_succ_noCode (p := prog) (n := n) (s := s) (by simp [h, prog])
    (by simp [h]; decide) (by simp [h]; decide)
  simpa [h] using this

/-! Fuel. -/
example (p : Program) (s : State) (o : Outcome) (h : p.run 10 s = .ok o) : p.run 1000 s = .ok o :=
  Program.run_mono h (by decide)

example (p : Program) (s : State) {n m : Nat} {o o' : Outcome}
    (h : p.run n s = .ok o) (h' : p.run m s = .ok o') : o = o' := Program.run_ok_unique h h'

/-! Composition: three ordinary steps followed by the exit. -/
example (p : Program) (s₀ s₁ s₂ s₃ : State) (w₀ w₁ w₂ : Nat)
    (x₀ : s₀.pc.toNat ≠ p.exitAddr) (x₁ : s₁.pc.toNat ≠ p.exitAddr) (x₂ : s₂.pc.toNat ≠ p.exitAddr)
    (t₀ : p.stubAt s₀.pc.toNat = none) (t₁ : p.stubAt s₁.pc.toNat = none)
    (t₂ : p.stubAt s₂.pc.toNat = none)
    (f₀ : p.fetch s₀.pc.toNat = some w₀) (f₁ : p.fetch s₁.pc.toNat = some w₁)
    (f₂ : p.fetch s₂.pc.toNat = some w₂)
    (e₀ : step w₀ s₀ = .ok s₁) (e₁ : step w₁ s₁ = .ok s₂) (e₂ : step w₂ s₂ = .ok s₃)
    (hx : s₃.pc.toNat = p.exitAddr) :
    p.run 4 s₀ = .ok (.returned s₃) := by
  have hs : Program.Steps p s₀ 3 s₃ :=
    ((Program.Steps.single x₀ t₀ f₀ e₀).snoc x₁ t₁ f₁ e₁).snoc x₂ t₂ f₂ e₂
  exact Program.run_steps_exit hs hx

end JanusTests.Run
