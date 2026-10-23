import Extracted

/-! Finding R2-A2 (direction flag): a theorem about a mid-function state that every real
execution reaches with `DF = 1`.

`runtime.memmove` (Go 1.26, extracted with `CopyBlock`) has the overlapping backward path

```
47d6d5: STD
47d6d6: MOVQ BX, CX ; SHRQ $3, CX ; ANDQ $7, BX ; SUBQ $8, DI ; SUBQ $8, SI
47d6e9: REP MOVSQ          <- here DF = 1 on every real execution
47d6ec: CLD
```

`STD` is undecodable, so no *call* theorem (`Ensures`/`CallSetup`) can reach `0x47d6e9`. But
`State` has no `DF`, and `janus verify` accepts any theorem statement that mentions
`Extracted.` (it prints the statement for review). The theorem below is kernel-checked against
the shipped model and says that from `0x47d6e9` with `RCX = 2` the copy runs **forward**
(`RSI += 16`, the words at `RSI`, `RSI+8` go to `RDI`, `RDI+8`). On hardware every state at
`0x47d6e9` has `DF = 1` (it follows `STD`), and the instruction copies backward
(`RSI -= 16`, words at `RSI`, `RSI-8` to `RDI`, `RDI-8`); see `host/probe.c` case 5.

Run: `audit/round2/amd64/build-controls.sh` builds `work/CopyBlock`; then
`LEAN_PATH=$PWD/audit/round2/amd64/work/CopyBlock:$(lake env printenv LEAN_PATH) lake env lean audit/round2/amd64/controls/DFMemmove.lean`. -/

open Janus Janus.Amd64

namespace DFRepro

def repMovsq : Nat := 0x47d6e9

set_option maxRecDepth 100000 in
theorem fetch_rep : Extracted.program.fetch repMovsq =
    some [0xf3, 0x48, 0xa5, 0xfc, 0x48, 0x83, 0xc7, 0x08, 0x48, 0x83, 0xc6, 0x08, 0x48, 0x29, 0xdf] := by
  rfl

def mem : Memory :=
  ⟨fun a => if a = 0x3000 then 0x11 else if a = 0x3008 then 0x22 else if a = 0x3010 then 0x33 else 0,
   [⟨0x2000, 0x40, true⟩, ⟨0x3000, 0x40, false⟩]⟩

def t : State :=
  { regs := fun i => if i = 1 then 2 else if i = 6 then 0x3008 else if i = 7 then 0x2008 else 0,
    rip := BitVec.ofNat 64 repMovsq, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem }

/-- The model: forward copy. Hardware (DF = 1 at this PC): `RSI = 0x2FF8`, `RDI = 0x1FF8`,
`[0x2008] = 0x22`, `[0x2000] = 0x11`, `[0x2010]` untouched (0). -/
theorem model_copies_forward :
    ∃ t', Amd64.step [0xf3, 0x48, 0xa5, 0xfc, 0x48, 0x83, 0xc7, 0x08, 0x48, 0x83, 0xc6, 0x08,
        0x48, 0x29, 0xdf] t = .ok t' ∧
      t'.regs 6 = 0x3018 ∧ t'.regs 7 = 0x2018 ∧ t'.regs 1 = 0 ∧
      t'.mem.readLE 0x2008 8 = 0x22 ∧ t'.mem.readLE 0x2010 8 = 0x33 ∧ t'.mem.readLE 0x2000 8 = 0 := by
  refine ⟨_, rfl, ?_⟩
  decide


set_option maxRecDepth 100000 in
/-- The same claim as a statement about `Extracted.program` (accepted by `janus verify`): run
from the `REP MOVSQ` of `memmove`'s backward path until the `CLD` after it. -/
theorem memmove_backward_rep_copies_forward :
    ∃ t', (Extracted.program.withExit 0x47d6ec).run 2 t = .ok (.returned t') ∧
      t'.regs 6 = 0x3018 ∧ t'.regs 7 = 0x2018 ∧
      t'.mem.readLE 0x2008 8 = 0x22 ∧ t'.mem.readLE 0x2010 8 = 0x33 ∧ t'.mem.readLE 0x2000 8 = 0 := by
  obtain ⟨t', h, h6, h7, -, ha, hb, hc⟩ := model_copies_forward
  refine ⟨t', ?_, h6, h7, ha, hb, hc⟩
  have hs : Extracted.program.stubAt t.rip.toNat = none := by decide
  rw [Program.run_succ_step (s' := t') (by decide) (by simpa using hs) (by rw [show t.rip.toNat = repMovsq from rfl]; exact fetch_rep) h]
  have ht : t'.rip.toNat = 0x47d6ec := by
    have := congrArg (fun r => match r with | .ok s => s.rip.toNat | .error _ => 0) h
    simp only at this; rw [← this]; rfl
  exact Program.run_succ_exit (by simpa using ht)

end DFRepro
