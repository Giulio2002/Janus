import Janus.Tactic.Basic
import Janus.Arm64.CryptoLemmas

/-!
# Symbolic execution of the crypto-extension, CRC32 and permute instructions

* `exec_crypto`: the `exec` equation of `Instr.crypto` (by `rfl`), and `execCrypto` registered
  in `janus_exec`, so one step of a decoded `CryptoInstr` unfolds to its register reads and
  writes. The operations (`crc32Op`, `sha256Hash`, `pmullOp`, ...) are **not** unfolded: a
  symbolic register holds a term like `crc32Op false 64 acc v`, which a proof rewrites with
  the lemmas of `Janus.Arm64.CryptoLemmas` (`crc32Op_eq_update`).

Nothing here is trusted: every lemma is proved from the model.
-/

namespace Janus.Tactic

open Janus Janus.Arm64

@[janus_exec] theorem exec_crypto (s : State) (c : CryptoInstr) :
    exec (.crypto c) s = .ok (execCrypto s c).next := rfl

attribute [janus_exec] execCrypto

end Janus.Tactic
