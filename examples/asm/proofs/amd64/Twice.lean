import Janus
import Extracted

/-!
# `Twice(x uint64) uint64` (Go assembly, ABI0, amd64) calling Go through the ABI0 → ABIInternal wrapper

```
TEXT ·Twice(SB), NOSPLIT, $16-16           // examples/asm/asm_amd64.s
	MOVQ x+0(FP), AX ; MOVQ AX, 0(SP) ; CALL ·double(SB)
	MOVQ 8(SP), AX ; INCQ AX ; MOVQ AX, ret+8(FP) ; RET
```

The ABI0 → ABIInternal wrapper `double.abi0` the compiler generates does the **re-entry** before
it calls Go: `MOVQ 24(SP), AX` (the frame word into the register), `XORPS X15, X15`,
`MOVQ FS:-8, R14` (ABIInternal's fixed registers), `CALL double`, `MOVQ AX, 32(SP)`.

**Guarantee.** For all `x` and every ABI0 call state of `example.com/asm.Twice.abi0` in which
`[RSP-56, RSP)` is writable and the TLS slot `FS:-8` is readable, the call returns (never
faulting), obeys `ABIReturn0`, its result word is `2·x + 1`, and its memory equals the call
state's with the result word written, outside `[RSP-56, RSP)`.

**How.** `double_summary` (Go, `Summary`), `double0_summary` (the wrapper, `Summary0`, which
executes the re-entry), and the theorem with `calls [double0_summary]`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic

namespace Proof

abbrev double : Nat := segAddr Extracted.program "example.com/asm.double"
abbrev double0 : Nat := segAddr Extracted.program "example.com/asm.double.abi0"

theorem double_summary :
    Summary Extracted.program double
      (fun s => s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => ∃ f, s' = { s with regs := setRegF (setRegF s.regs 0 (s.regs 0 + s.regs 0)) 4
                                         (s.regs 4 + 8), rip := retAddrOf s, flags := f }) := by
  intro s hpc ⟨h1, h2⟩
  janus64_run
  exact ⟨_, rfl⟩

theorem double0_summary :
    Summary0 Extracted.program double0
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ 24 ≤ (s.regs 4).toNat ∧
        (s.regs 4).toNat + 24 ≤ 2 ^ 48 ∧
        s.mem.accessible ((s.regs 4).toNat - 24) 48 true = true ∧
        8 ≤ s.fsBase.toNat ∧ s.fsBase.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.fsBase.toNat - 8) 8 false = true)
      (fun s m => MemFrame (s.mem.writeLE ((s.regs 4).toNat + 16) 8
        (2 * s.mem.readLE ((s.regs 4).toNat + 8) 8 % 2 ^ 64)) m
        [((s.regs 4).toNat - 24, (s.regs 4).toNat)]) := by
  intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7⟩
  janus64_run calls [double_summary]
  refine MemFrame.writeLE_congr ?_ _ _ (by omega)
  janus_frame

theorem correctness (x : BitVec 64) :
    Ensures0 Extracted.program Extracted.entry [x] 1
      (fun s => 56 ≤ (s.regs 4).toNat ∧ s.mem.accessible ((s.regs 4).toNat - 56) 56 true = true ∧
        8 ≤ s.fsBase.toNat ∧ s.fsBase.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.fsBase.toNat - 8) 8 false = true)
      (fun s s' => results0 s s' 1 1 = [2 * x + 1] ∧
        MemFrame (s.mem.writeLE ((s.regs 4).toNat + 16) 8 (2 * x + 1).toNat) s'.mem
          [((s.regs 4).toNat - 56, (s.regs 4).toNat)]) := by
  intro ret hret s hs ⟨hb, hst, hf1, hf2, hf3⟩
  janus64_intro0 hs
  janus64_run calls [double0_summary]
  refine ⟨?_, ?_⟩
  · simp only [List.cons.injEq, and_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
  · refine MemFrame.writeLE_congr ?_ _ _ (by simp [BitVec.toNat_mul])
    janus_frame

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def tls0 : Nat := 0x400000
def dat : Nat := 0x500000

def bytes (a : Nat) : Byte := if a = sp0 + 2 then 0x20 else if a = sp0 + 8 then 3 else 0

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x100, false⟩, ⟨tls0, 0x100, false⟩, ⟨dat, 0x100, false⟩]⟩,
    fsBase := BitVec.ofNat 64 (tls0 + 8) }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup0 (Extracted.program.withExit ret) Extracted.entry [(3 : BitVec 64)] 1 s0 :=
  ⟨rfl, by decide, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0) with rfl
    exact (by decide : s0.mem.readLE ((s0.regs 4).toNat + 8 + 8 * 0) 8 = ((3 : BitVec 64)).toNat),
   ⟨by decide, by decide⟩, rfl⟩

theorem hpre : 56 ≤ (s0.regs 4).toNat ∧ s0.mem.accessible ((s0.regs 4).toNat - 56) 56 true = true ∧
    8 ≤ s0.fsBase.toNat ∧ s0.fsBase.toNat ≤ 2 ^ 48 ∧
    s0.mem.accessible (s0.fsBase.toNat - 8) 8 false = true :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The theorem fires: `Twice(3)` returns `7`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0
    (fun s' => ABIReturn0 s0 s' ∧
      (results0 s0 s' 1 1 = [2 * (3 : BitVec 64) + 1] ∧
        MemFrame (s0.mem.writeLE ((s0.regs 4).toNat + 16) 8 (2 * (3 : BitVec 64) + 1).toNat) s'.mem
          [((s0.regs 4).toNat - 56, (s0.regs 4).toNat)])) :=
  correctness 3 ret hret s0 setup hpre

/-- All the hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Janus.Amd64.State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup0 (Extracted.program.withExit ret) Extracted.entry [x] 1 s ∧
    (56 ≤ (s.regs 4).toNat ∧ s.mem.accessible ((s.regs 4).toNat - 56) 56 true = true ∧
      8 ≤ s.fsBase.toNat ∧ s.fsBase.toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.fsBase.toNat - 8) 8 false = true) ∧
    Returns (Extracted.program.withExit ret) s
      (fun s' => ABIReturn0 s s' ∧
        (results0 s s' 1 1 = [2 * x + 1] ∧
          MemFrame (s.mem.writeLE ((s.regs 4).toNat + 16) 8 (2 * x + 1).toNat) s'.mem
            [((s.regs 4).toNat - 56, (s.regs 4).toNat)])) :=
  ⟨ret, s0, 3, hret, setup, hpre, returns⟩

end Witness

end Proof
