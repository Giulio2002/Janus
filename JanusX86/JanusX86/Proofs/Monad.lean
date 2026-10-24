import X86Sail

/-! # Running generated Sail x86 code symbolically

`SailM` is `EStateM` over Sail's sequential state (registers in an `ExtDHashMap`, memory in an
`ExtHashMap`). These lemmas turn `(m).run s` for the monad primitives into results, so that
`simp` can evaluate generated Sail x86 code on a symbolic state. -/

namespace JanusX86.Proofs
open X86Sail X86Sail.Functions

abbrev SState :=
  Sail.ConcurrencyInterfaceV1.SequentialState RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource

/-- Registers replaced in a state. -/
def SState.set (s : SState) (r : Register) (v : RegisterType r) : SState :=
  { s with regs := s.regs.insert r v }

@[simp] theorem get?_set_same (s : SState) (r : Register) (v : RegisterType r) :
    (s.set r v).regs.get? r = some v := by
  simp [SState.set]

theorem get?_set_ne (s : SState) {r r' : Register} (v : RegisterType r) (h : r ≠ r') :
    (s.set r v).regs.get? r' = s.regs.get? r' := by
  simp only [SState.set, Std.ExtDHashMap.get?_insert]
  have : (r == r') = false := by simpa using h
  simp [this]

@[simp] theorem set_set (s : SState) (r : Register) (v w : RegisterType r) :
    (s.set r v).set r w = s.set r w := by
  simp only [SState.set]
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro k
  simp only [Std.ExtDHashMap.get?_insert]
  split <;> rfl

theorem set_self {s : SState} {r : Register} {v : RegisterType r} (h : s.regs.get? r = some v) :
    s.set r v = s := by
  cases s with
  | mk regs cs mem tags cc out =>
    simp only [SState.set]
    congr 1
    apply Std.ExtDHashMap.ext_get?
    intro k
    simp only [Std.ExtDHashMap.get?_insert]
    split
    · next he =>
      have he' : r = k := by simpa using he
      subst he'; simpa using h.symm
    · rfl

@[simp] theorem set_mem (s : SState) (r : Register) (v : RegisterType r) : (s.set r v).mem = s.mem := rfl

theorem run_bind {α β} (x : SailM α) (f : α → SailM β) (s : SState) :
    (x >>= f).run s = match x.run s with
      | .ok a s' => (f a).run s'
      | .error e s' => .error e s' := by
  show EStateM.bind x f s = _
  simp only [EStateM.bind, EStateM.run]
  cases x s <;> rfl

@[simp] theorem run_pure {α} (a : α) (s : SState) : (pure a : SailM α).run s = .ok a s := rfl

theorem run_readReg {r : Register} {v : RegisterType r} {s : SState} (h : s.regs.get? r = some v) :
    (readReg r).run s = .ok v s := by
  show (Sail.ConcurrencyInterfaceV1.PreSail.readReg r) s = _
  simp [Sail.ConcurrencyInterfaceV1.PreSail.readReg, h, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure]

@[simp] theorem run_writeReg (r : Register) (v : RegisterType r) (s : SState) :
    (writeReg r v).run s = .ok PUnit.unit (s.set r v) := rfl

theorem run_sailTryCatch {α} (x : SailM α) (f : exception → SailM α) (s : SState) :
    (sailTryCatch x f).run s = match x.run s with
      | .ok a s' => .ok a s'
      | .error (.User u) s' => (f u).run s'
      | .error e s' => .error e s' := by
  show (EStateM.tryCatch x _) s = _
  simp only [EStateM.tryCatch, EStateM.run]
  cases x s with
  | ok a s' => rfl
  | error e s' => cases e <;> rfl

theorem run_map {α β} (f : α → β) (x : SailM α) (s : SState) :
    (f <$> x).run s = match x.run s with
      | .ok a s' => .ok (f a) s'
      | .error e s' => .error e s' := by
  show EStateM.map f x s = _
  simp only [EStateM.map, EStateM.run]
  cases x s <;> rfl

theorem run_sail_assert_of {p : Bool} (h : p = true) (msg : String) (s : SState) :
    (sail_assert p msg).run s = .ok () s := by subst h; rfl

@[simp] theorem run_sail_assert_true (msg : String) (s : SState) :
    (sail_assert true msg).run s = .ok () s := rfl

@[simp] theorem run_undefined_bitvector (n : Nat) (s : SState) :
    (undefined_bitvector n).run s = .ok 0#n s := by
  cases s; rfl

theorem run_throw {α} (e : exception) (s : SState) :
    (sailThrow e : SailM α).run s = .error (.User e) s := rfl

end JanusX86.Proofs
