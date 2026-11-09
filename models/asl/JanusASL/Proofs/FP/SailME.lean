import JanusASL.Proofs.Config

/-! # Evaluating `SailME` (the early-return monad, `ExceptT` over `SailM`)

`run_ME` lemmas compute `(ExceptT.run m).run s` for lifts, `pure`, bind, map and the early return
`SailME.throw`, and `run_ME_top` turns `PreSailME.run` (`SailME.run`) into it, so a function
written with an early return evaluates by `simp` like a `SailM` one. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions Sail.ConcurrencyInterfaceV1

variable {β α γ : Type}

theorem run_ME_lift (x : SailM α) (s : SState) :
    (ExceptT.run (liftM x : SailME β α)).run s =
      match x.run s with
      | .ok a s' => .ok (.ok a) s'
      | .error e s' => .error e s' := by
  show (ExceptT.lift x).run.run s = _
  simp only [ExceptT.lift, ExceptT.run, ExceptT.mk]
  show (Functor.map Except.ok x).run s = _
  simp only [Functor.map, EStateM.map, EStateM.run]
  split <;> simp_all

theorem run_ME_pure (a : α) (s : SState) :
    (ExceptT.run (pure a : SailME β α)).run s = .ok (.ok a) s := rfl

theorem run_ME_bind (m : SailME β α) (f : α → SailME β γ) (s : SState) :
    (ExceptT.run (m >>= f)).run s =
      match (ExceptT.run m).run s with
      | .ok (.ok a) s' => (ExceptT.run (f a)).run s'
      | .ok (.error e) s' => .ok (.error e) s'
      | .error e s' => .error e s' := by
  show (ExceptT.bind m f).run.run s = _
  simp only [ExceptT.bind, ExceptT.run, ExceptT.mk, ExceptT.bindCont, bind, EStateM.bind, EStateM.run]
  split
  · next a s' h => rw [h]; cases a <;> rfl
  · next e s' h => rw [h]

theorem run_ME_map (g : α → γ) (m : SailME β α) (s : SState) :
    (ExceptT.run (g <$> m)).run s =
      match (ExceptT.run m).run s with
      | .ok (.ok a) s' => .ok (.ok (g a)) s'
      | .ok (.error e) s' => .ok (.error e) s'
      | .error e s' => .error e s' := by
  rw [map_eq_pure_bind, run_ME_bind]; rfl

theorem run_ME_throw (b : β) (s : SState) :
    (ExceptT.run (SailME.throw b : SailME β α)).run s = .ok (.error (.inr b)) s := rfl

theorem run_ME_top (m : SailME β β) (s : SState) :
    (Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run m).run s =
      match (ExceptT.run m).run s with
      | .ok (.ok a) s' => .ok a s'
      | .ok (.error (.inr b)) s' => .ok b s'
      | .ok (.error (.inl e)) s' => .error e s'
      | .error e s' => .error e s' := by
  simp only [Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, bind, EStateM.bind, EStateM.run]
  split
  · next a s' h => rw [h]; rcases a with (e | b) | a <;> rfl
  · next e s' h => rw [h]

theorem run_SailME_run (m : SailME β β) (s : SState) :
    (SailME.run m).run s =
      match (ExceptT.run m).run s with
      | .ok (.ok a) s' => .ok a s'
      | .ok (.error (.inr b)) s' => .ok b s'
      | .ok (.error (.inl e)) s' => .error e s'
      | .error e s' => .error e s' := run_ME_top m s

end JanusASL.Proofs
