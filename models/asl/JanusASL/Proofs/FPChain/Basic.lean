import JanusASL.Proofs.Step

/-! # Skipping and taking a clause of a generated decode chain

`tools/chain.py` proves a decode-chain lemma by one `chain_skip` per earlier clause and one `chain_take`. Each is a
unification at the head of the chain, so the proof does not traverse the rest of the (megabyte-sized) chain. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem chain_skip (b : Bool) (hb : b = false) (m : SailM Bool) (A R : SailM Unit) :
    (do let c ← ((pure b : SailM Bool) <&&> m); if c = true then A else R : SailM Unit) = R := by
  subst hb
  simp [andM, toBool]

theorem chain_take (b : Bool) (hb : b = true) (n : Int) (hn : (-1 : Int) < n) {s : SState}
    (hs : s.regs.get? .SEE = some (-1)) (A R : SailM Unit) :
    (do let c ← ((pure b : SailM Bool) <&&> (do pure ((← readReg Register.SEE) <b n))); if c = true then A else R : SailM Unit).run s
      = A.run s := by
  subst hb
  simp [andM, toBool, run_readReg hs, hn]

end JanusASL.Proofs
