import ArmASL

/-! # Running generated ASL code symbolically

`SailM` is `EStateM` over Sail's sequential state (registers in an `ExtDHashMap`, memory in an
`ExtHashMap`). These lemmas turn `(m).run s` for the monad primitives into results, so that
`simp` can evaluate generated ASL code on a symbolic state. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

abbrev SState :=
  Sail.ConcurrencyInterfaceV1.SequentialState RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource

/-- Registers replaced in a state. -/
def SState.set (s : SState) (r : Register) (v : RegisterType r) : SState :=
  { s with regs := s.regs.insert r v }

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

end JanusASL.Proofs
