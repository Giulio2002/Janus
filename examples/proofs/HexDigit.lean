import Extracted

/-!
# `HexDigit(i uint64) byte` returns `"0123456789abcdef"[i & 15]` (an indexed `.rodata` load)

**Guarantee.** For every 64-bit `i` and every Go call state `s` of `example.com/basic.HexDigit`
(`i` in `X0`) in which memory holds the program's read-only data (`Program.DataLoaded`, which
includes the string constant), the call returns, obeys the ABI, and `X0` is the ASCII code of
the hexadecimal digit of `i mod 16`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- ASCII code of the hexadecimal digit `d < 16`. -/
def hexDigit (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => Extracted.program.DataLoaded s.mem)
      (fun _ s' => (s'.regs 0).toNat = hexDigit (i.toNat % 16)) := by
  intro s hs hd
  janus_intro hs
  janus_data hd
  janus_run
  -- one case per digit: the load address becomes a literal and is read from the data
  generalize hk : i.toNat % 16 = k
  have hlt : k < 16 := hk ▸ Nat.mod_lt _ (by decide)
  janus_cases hlt
  all_goals janus_simp [hexDigit]

end Proof
