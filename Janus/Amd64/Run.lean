import Janus.Amd64.Program

/-!
# Fuel and run lemmas

The amd64 copies of the facts in `Janus.Run` about `Amd64.Program.run`.

* One-step unfolding: `run_succ_exit`, `run_succ_stub`, `run_succ_noCode`, `run_succ_step`,
  `run_succ_fault`. Each rewrites `p.run (n + 1) s` given facts about `exitAddr`, `stubAt`,
  `fetch` and `step` at `s.pc`.
* Fuel: `run_mono` (more fuel never changes an `.ok` result), `run_error_mono` (nor a real
  fault), `run_ok_unique` (two successful runs agree).
* Composition: `Steps p s k s'` is `k` ordinary instruction steps from `s` to `s'` (never at
  the exit address or a stub). `run_steps` turns it into `p.run (k + n) s = p.run n s'`.
* Code lookup: `fetchIn_cons_hit` / `fetchIn_cons_miss` and `stubAt` lemmas. On a concrete
  segment list `p.fetch pc = some bs` is closed by `decide` or `rfl`.
-/

namespace Janus.Amd64



namespace Program

variable (p : Program)

/-! ## Unfolding -/

@[simp] theorem run_zero (s : State) : p.run 0 s = .error .outOfFuel := rfl

theorem run_succ (n : Nat) (s : State) :
    p.run (n + 1) s =
      if s.rip.toNat = p.exitAddr then .ok (.returned s) else
      match p.stubAt s.rip.toNat with
      | some st => .ok (.stub st.name st.kind s)
      | none =>
        match p.fetch s.rip.toNat with
        | none => .error (.noCode s.rip.toNat)
        | some w => (Amd64.step w s).bind (p.run n) := rfl

variable {p} {n : Nat} {s s' : State}

theorem run_succ_exit (hx : s.rip.toNat = p.exitAddr) : p.run (n + 1) s = .ok (.returned s) := by
  rw [run_succ, ite_eq_left hx]

theorem run_succ_stub {st : Stub} (hx : s.rip.toNat ≠ p.exitAddr)
    (hs : p.stubAt s.rip.toNat = some st) : p.run (n + 1) s = .ok (.stub st.name st.kind s) := by
  rw [run_succ, ite_eq_right hx, hs]

theorem run_succ_noCode (hx : s.rip.toNat ≠ p.exitAddr) (hs : p.stubAt s.rip.toNat = none)
    (hf : p.fetch s.rip.toNat = none) : p.run (n + 1) s = .error (.noCode s.rip.toNat) := by
  rw [run_succ, ite_eq_right hx, hs]; simp only [hf]

theorem run_succ_step {w : List Nat} (hx : s.rip.toNat ≠ p.exitAddr) (hs : p.stubAt s.rip.toNat = none)
    (hf : p.fetch s.rip.toNat = some w) (hst : Amd64.step w s = .ok s') :
    p.run (n + 1) s = p.run n s' := by
  rw [run_succ, ite_eq_right hx, hs]; simp only [hf, hst]; rfl

theorem run_succ_fault {w : List Nat} {e : Fault} (hx : s.rip.toNat ≠ p.exitAddr)
    (hs : p.stubAt s.rip.toNat = none) (hf : p.fetch s.rip.toNat = some w)
    (hst : Amd64.step w s = .error e) : p.run (n + 1) s = .error e := by
  rw [run_succ, ite_eq_right hx, hs]; simp only [hf, hst]; rfl

/-- At the exit address with any positive fuel the call has returned. -/
theorem run_exit_of_pos (hx : s.rip.toNat = p.exitAddr) (hn : 0 < n) :
    p.run n s = .ok (.returned s) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact run_succ_exit hx

/-! ## Fuel -/

/-- More fuel never changes a successful (`.ok`) result. -/
theorem run_mono {m : Nat} {o : Outcome} (h : p.run n s = .ok o) (hle : n ≤ m) :
    p.run m s = .ok o := by
  induction n generalizing s m with
  | zero => cases h
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    by_cases hx : s.rip.toNat = p.exitAddr
    · rw [run_succ_exit hx] at h ⊢; exact h
    · cases hs : p.stubAt s.rip.toNat with
      | some st => rw [run_succ_stub hx hs] at h ⊢; exact h
      | none =>
        cases hf : p.fetch s.rip.toNat with
        | none => rw [run_succ_noCode hx hs hf] at h; cases h
        | some w =>
          cases hst : Amd64.step w s with
          | error e => rw [run_succ_fault hx hs hf hst] at h; cases h
          | ok s₁ =>
            rw [run_succ_step hx hs hf hst] at h ⊢
            exact ih h (by omega)

/-- A fault other than running out of fuel is also stable under more fuel. -/
theorem run_error_mono {m : Nat} {e : Fault} (h : p.run n s = .error e) (he : e ≠ .outOfFuel)
    (hle : n ≤ m) : p.run m s = .error e := by
  induction n generalizing s m with
  | zero => cases h; exact absurd rfl he
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    by_cases hx : s.rip.toNat = p.exitAddr
    · rw [run_succ_exit hx] at h; cases h
    · cases hs : p.stubAt s.rip.toNat with
      | some st => rw [run_succ_stub hx hs] at h; cases h
      | none =>
        cases hf : p.fetch s.rip.toNat with
        | none => rw [run_succ_noCode hx hs hf] at h ⊢; exact h
        | some w =>
          cases hst : Amd64.step w s with
          | error e' => rw [run_succ_fault hx hs hf hst] at h ⊢; exact h
          | ok s₁ =>
            rw [run_succ_step hx hs hf hst] at h ⊢
            exact ih h (by omega)

/-- Successful runs are deterministic across fuel budgets. -/
theorem run_ok_unique {m : Nat} {o o' : Outcome} (h : p.run n s = .ok o)
    (h' : p.run m s = .ok o') : o = o' := by
  rcases Nat.le_total n m with hle | hle
  · rw [run_mono h hle] at h'; exact Except.ok.inj h'
  · rw [run_mono h' hle] at h; exact (Except.ok.inj h).symm

/-- A successful run and a real fault cannot both happen. -/
theorem run_ok_not_error {m : Nat} {o : Outcome} {e : Fault} (h : p.run n s = .ok o)
    (h' : p.run m s = .error e) (he : e ≠ .outOfFuel) : False := by
  rcases Nat.le_total n m with hle | hle
  · rw [run_mono h hle] at h'; cases h'
  · rw [run_error_mono h' he hle] at h; cases h

/-- Any run ends in `.ok`, or a fault; running out of fuel is the only fuel-dependent one. -/
theorem run_outOfFuel_of_le {m : Nat} (h : p.run m s = .error .outOfFuel) (hle : n ≤ m) :
    p.run n s = .error .outOfFuel := by
  cases hn : p.run n s with
  | ok o => rw [run_mono hn hle] at h; cases h
  | error e =>
    by_cases he : e = .outOfFuel
    · rw [he]
    · rw [run_error_mono hn he hle] at h; cases h; exact absurd rfl he

/-! ## Composition -/

/-- `Steps p s k s'`: `k` ordinary instructions take `s` to `s'`. None of the intermediate
states (including `s`, excluding `s'`) is at the exit address or a stub. -/
inductive Steps (p : Program) : State → Nat → State → Prop where
  | refl (s : State) : Steps p s 0 s
  | step {s s₁ s₂ : State} {k : Nat} {w : List Nat} :
      s.rip.toNat ≠ p.exitAddr → p.stubAt s.rip.toNat = none → p.fetch s.rip.toNat = some w →
      Amd64.step w s = .ok s₁ → Steps p s₁ k s₂ → Steps p s (k + 1) s₂

namespace Steps

theorem single {w : List Nat} (hx : s.rip.toNat ≠ p.exitAddr) (hs : p.stubAt s.rip.toNat = none)
    (hf : p.fetch s.rip.toNat = some w) (hst : Amd64.step w s = .ok s') : Steps p s 1 s' :=
  .step hx hs hf hst (.refl s')

theorem trans {k j : Nat} {s'' : State} (h₁ : Steps p s k s') (h₂ : Steps p s' j s'') :
    Steps p s (k + j) s'' := by
  induction h₁ with
  | refl => simpa using h₂
  | @step _ _ _ k _ hx hs hf hst _ ih =>
    rw [show k + 1 + j = (k + j) + 1 by omega]
    exact .step hx hs hf hst (ih h₂)

/-- Append one ordinary step at the end. -/
theorem snoc {k : Nat} {w : List Nat} {s'' : State} (h : Steps p s k s')
    (hx : s'.rip.toNat ≠ p.exitAddr) (hs : p.stubAt s'.rip.toNat = none)
    (hf : p.fetch s'.rip.toNat = some w) (hst : Amd64.step w s' = .ok s'') :
    Steps p s (k + 1) s'' :=
  h.trans (single hx hs hf hst)

end Steps

/-- `k` ordinary steps consume exactly `k` fuel. -/
theorem run_steps {k : Nat} (h : Steps p s k s') (n : Nat) : p.run (k + n) s = p.run n s' := by
  induction h with
  | refl => simp
  | @step _ _ _ k _ hx hs hf hst _ ih =>
    rw [show k + 1 + n = (k + n) + 1 by omega, run_succ_step hx hs hf hst, ih]

/-- Steps to the exit address: the call returns with `k + 1` fuel. -/
theorem run_steps_exit {k : Nat} (h : Steps p s k s') (hx : s'.rip.toNat = p.exitAddr) :
    p.run (k + 1) s = .ok (.returned s') := by
  rw [run_steps h 1, run_succ_exit hx]

/-- Steps to a stub: the run ends at that stub with `k + 1` fuel. -/
theorem run_steps_stub {k : Nat} {st : Stub} (h : Steps p s k s') (hx : s'.rip.toNat ≠ p.exitAddr)
    (hs : p.stubAt s'.rip.toNat = some st) :
    p.run (k + 1) s = .ok (.stub st.name st.kind s') := by
  rw [run_steps h 1, run_succ_stub hx hs]

/-- Compose: run the prefix as ordinary steps, then any successful continuation. -/
theorem run_steps_ok {k m : Nat} {o : Outcome} (h : Steps p s k s') (h' : p.run m s' = .ok o) :
    p.run (k + m) s = .ok o := by
  rw [run_steps h, h']

/-! ## Code lookup -/

@[simp] theorem fetchIn_nil (pc : Nat) : fetchIn [] pc = none := rfl

theorem fetchIn_cons (seg : Segment) (rest : List Segment) (pc : Nat) :
    fetchIn (seg :: rest) pc =
      if seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length then
        some ((seg.bytes.drop (pc - seg.base)).take 15)
      else fetchIn rest pc := rfl

theorem fetchIn_cons_hit {seg : Segment} {rest : List Segment} {pc : Nat}
    (h1 : seg.base ≤ pc) (h2 : pc < seg.base + seg.bytes.length) :
    fetchIn (seg :: rest) pc = some ((seg.bytes.drop (pc - seg.base)).take 15) := by
  rw [fetchIn_cons, ite_eq_left ⟨h1, h2⟩]

theorem fetchIn_cons_miss {seg : Segment} {rest : List Segment} {pc : Nat}
    (h : pc < seg.base ∨ seg.base + seg.bytes.length ≤ pc) :
    fetchIn (seg :: rest) pc = fetchIn rest pc := by
  rw [fetchIn_cons, ite_eq_right (by omega)]

theorem fetch_eq (pc : Nat) : p.fetch pc = fetchIn p.segments pc := rfl

theorem stubAt_eq (pc : Nat) : p.stubAt pc = p.stubs.find? (·.addr = pc) := rfl

theorem stubAt_eq_none {pc : Nat} (h : ∀ st ∈ p.stubs, st.addr ≠ pc) : p.stubAt pc = none := by
  rw [stubAt_eq, List.find?_eq_none]
  intro st hst; simpa using h st hst

theorem stubAt_some {pc : Nat} {st : Stub} (h : p.stubAt pc = some st) : st.addr = pc := by
  rw [stubAt_eq] at h
  simpa using List.find?_some h

/-! ## Return address -/

@[simp] theorem exitAddr_withExit (ret : Nat) : (p.withExit ret).exitAddr = ret := rfl
@[simp] theorem fetch_withExit (ret pc : Nat) : (p.withExit ret).fetch pc = p.fetch pc := rfl
@[simp] theorem stubAt_withExit (ret pc : Nat) : (p.withExit ret).stubAt pc = p.stubAt pc := rfl
@[simp] theorem data_withExit (ret : Nat) : (p.withExit ret).data = p.data := rfl

/-- No segment covers `pc`: there is no code there. -/
theorem fetchIn_eq_none {segs : List Segment} {pc : Nat}
    (h : ∀ seg ∈ segs, pc < seg.base ∨ seg.base + seg.bytes.length ≤ pc) :
    fetchIn segs pc = none := by
  induction segs with
  | nil => rfl
  | cons seg rest ih =>
    rw [fetchIn_cons_miss (by have := h seg (List.mem_cons_self ..); omega)]
    exact ih fun seg' hs => h seg' (List.mem_cons_of_mem _ hs)

end Program
end Janus.Amd64
