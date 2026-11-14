import Janus

/-! # Red team round `roundretaddr`: a precondition cannot restrict the caller's return address (v0.4.0)

Before v0.4.0 `Ensures` evaluated `pre` on the call state with the return address installed (arm64: `X30`; amd64: the
word at `[RSP]`), so a precondition such as `(s.regs 30).toNat = 0` pinned the caller's return address (to `0`:
a jump to a nil code pointer counted as a return). Now `pre` is evaluated on the state BEFORE `State.setRet` installs
the return address: the claim covers every admissible `ret` whatever `pre` says about `X30` / `[RSP]`.

Every statement below is a theorem about an arbitrary program, entry, arguments and postcondition. Rows named in
`test/redteam/rounds/roundretaddr/run-roundretaddr.sh`. -/

namespace JanusTests.RetAddr

/-! ## arm64 -/
section Arm64

open Janus Janus.Arm64 Janus.GoABI

/-- a1: with a precondition that pins `X30` to `0` (the old attack), the run claim holds for EVERY admissible return
address, not just `0`: each admissible `ret` is installed after the precondition is evaluated. -/
theorem a1_pin_covers_every_ret {p : Program} {entry : Nat} {args : List W64} {post : State → State → Prop}
    (h : Ensures p entry args (fun s => (s.regs 30).toNat = 0) post)
    {s : State} (hs : CallSetup0 entry args s) (hp : (s.regs 30).toNat = 0) {r₁ r₂ : Nat}
    (h₁ : RetAddr p r₁) (h₂ : RetAddr p r₂) :
    Returns (p.withExit r₁) (s.setRet r₁) (fun s' => ABIReturn (s.setRet r₁) s' ∧ post (s.setRet r₁) s') ∧
    Returns (p.withExit r₂) (s.setRet r₂) (fun s' => ABIReturn (s.setRet r₂) s' ∧ post (s.setRet r₂) s') :=
  ⟨h s hs hp r₁ h₁, h s hs hp r₂ h₂⟩

/-- a2: the same for a two-sided bound (`X30 < 2^20`, the `LrPin.lean` probe e2). -/
theorem a2_bound_covers_every_ret {p : Program} {entry : Nat} {args : List W64} {post : State → State → Prop}
    (h : Ensures p entry args (fun s => (s.regs 30).toNat < 2 ^ 20) post)
    {s : State} (hs : CallSetup0 entry args s) (hp : (s.regs 30).toNat < 2 ^ 20) {r : Nat} (hr : RetAddr p r) :
    Returns (p.withExit r) (s.setRet r) (fun s' => ABIReturn (s.setRet r) s' ∧ post (s.setRet r) s') :=
  h s hs hp r hr

/-- a3: a state that satisfies the pinning precondition becomes, for each admissible `ret`, a call state of the old
shape with exactly that return address: nothing about `ret` is constrained by the precondition. -/
theorem a3_every_ret_is_a_call {p : Program} {entry : Nat} {args : List W64} {s : State}
    (hs : CallSetup0 entry args s) (ret : Nat) :
    CallSetup (p.withExit ret) entry args (s.setRet ret) := hs.setRet ret

/-- a4: the pinning precondition is NOT invariant under installing the return address (so the old proof strategy
`Ensures.of_old (by janus_pre_setRet) …` correctly has no proof for it): the installed `X30` is `ret`, not `0`. -/
theorem a4_pin_not_invariant :
    ¬ ∀ (s : State) (ret : Nat), (s.regs 30).toNat = 0 → ((s.setRet ret).regs 30).toNat = 0 := by
  intro h
  have := h { regs := fun _ => 0, sp := 0, pc := 0, flags := ⟨false, false, false, false⟩, mem := default } 4 rfl
  simp at this

/-- a4b: and the tactic correctly fails on it. -/
example (p : Program) : True := by
  fail_if_success (have _h : ∀ s ret, RetAddr p ret → (fun s : State => (s.regs 30).toNat = 0) s →
    (fun s : State => (s.regs 30).toNat = 0) (s.setRet ret) := by janus_pre_setRet)
  trivial

/-- A function that is a single `ret` (`0xd65f03c0`) at `0x1000`. -/
def retProg : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

/-- a4c: the OLD attack's statement is now a true theorem about every admissible return address, proved directly in
the new shape (the run tactics start on `s.setRet ret`: `hs.setRet ret` is the old-shaped `CallSetup`). The
precondition pins the caller's old `X30`; the proof never needs it. -/
example : Ensures retProg 0x1000 [] (fun s => (s.regs 30).toNat = 0) (fun _ _ => True) := by
  intro s hs _ ret hret
  have hs1 := hs.setRet (p := retProg) ret
  generalize s.setRet ret = s1 at hs1 ⊢
  janus_intro hs1
  janus_run

/-- a5: a precondition on any other register or on the memory survives `setRet`: `janus_pre_setRet` proves it. -/
example (p : Program) : ∀ s ret, RetAddr p ret →
    (fun s : State => (s.regs 5).toNat < 7 ∧ s.mem.readLE s.sp.toNat 8 = 3) s →
    (fun s : State => (s.regs 5).toNat < 7 ∧ s.mem.readLE s.sp.toNat 8 = 3) (s.setRet ret) := by
  janus_pre_setRet

end Arm64

/-! ## amd64 -/
section Amd64

open Janus.Amd64 Janus.Amd64.GoABI

/-- m1: with a precondition that pins the word at `[RSP]` (the old `RetLow`-style attack, `readLE RSP 8 = 0`), the run
claim holds for every admissible return address. -/
theorem m1_pin_covers_every_ret {p : Program} {entry : Nat} {args : List W64} {post : State → State → Prop}
    (h : Ensures p entry args (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0) post)
    {s : State} (hs : CallSetup0 entry args s) (hp : s.mem.readLE (s.regs 4).toNat 8 = 0) {r₁ r₂ : Nat}
    (h₁ : RetAddr p r₁) (h₂ : RetAddr p r₂) :
    Returns (p.withExit r₁) (s.setRet r₁) (fun s' => ABIReturn (s.setRet r₁) s' ∧ post (s.setRet r₁) s') ∧
    Returns (p.withExit r₂) (s.setRet r₂) (fun s' => ABIReturn (s.setRet r₂) s' ∧ post (s.setRet r₂) s') :=
  ⟨h s hs hp r₁ h₁, h s hs hp r₂ h₂⟩

/-- m2: every `RspBypass64.lean` probe form is the same statement about the OLD word: an alias through `∃`. -/
theorem m2_alias_covers_every_ret {p : Program} {entry : Nat} {args : List W64} {post : State → State → Prop}
    (h : Ensures p entry args (fun s => ∃ sp, (s.regs 4).toNat = sp ∧ s.mem.readLE sp 8 = 0) post)
    {s : State} (hs : CallSetup0 entry args s) (hp : ∃ sp, (s.regs 4).toNat = sp ∧ s.mem.readLE sp 8 = 0)
    {r : Nat} (hr : RetAddr p r) :
    Returns (p.withExit r) (s.setRet r) (fun s' => ABIReturn (s.setRet r) s' ∧ post (s.setRet r) s') :=
  h s hs hp r hr

/-- m3: a pin of the whole memory is a pin of the OLD memory. -/
theorem m3_memory_pin_covers_every_ret {p : Program} {entry : Nat} {args : List W64} {post : State → State → Prop}
    (zeroMem : Janus.Arm64.Memory → Janus.Arm64.Memory)
    (h : Ensures p entry args (fun s => s.mem = zeroMem s.mem) post)
    {s : State} (hs : CallSetup0 entry args s) (hp : s.mem = zeroMem s.mem) {r : Nat} (hr : RetAddr p r) :
    Returns (p.withExit r) (s.setRet r) (fun s' => ABIReturn (s.setRet r) s' ∧ post (s.setRet r) s') :=
  h s hs hp r hr

/-- m4: for each admissible `ret` the state `s.setRet ret` is an old-shaped call state whose `[RSP]` holds `ret`, even if
`s` held `0` there. -/
theorem m4_every_ret_is_a_call {p : Program} {entry : Nat} {args : List W64} {s : State}
    (hs : CallSetup0 entry args s) {ret : Nat} (hr : RetAddr p ret) :
    CallSetup (p.withExit ret) entry args (s.setRet ret) := hs.setRet hr.lt64

/-- m5: the word at `[RSP]` of the installed state is `ret`; the old word is gone. -/
theorem m5_slot_holds_ret {s : State} {ret : Nat} (h : ret < 2 ^ 64) :
    (s.setRet ret).mem.readLE (s.regs 4).toNat 8 = ret := readLE_setRet_sp h

/-- m6: the pinning precondition is not invariant under `setRet`: the tactic fails on it. -/
example (p : Program) : True := by
  fail_if_success (have _h : ∀ s ret, RetAddr p ret → (fun s : State => s.mem.readLE (s.regs 4).toNat 8 = 0) s →
    (fun s : State => s.mem.readLE (s.regs 4).toNat 8 = 0) (s.setRet ret) := by janus64_pre_setRet)
  trivial

/-- m7: stack-argument words at `RSP + 8`, `RSP + 16` survive `setRet`. -/
example (p : Program) : ∀ s ret, RetAddr p ret →
    (fun s : State => StackWritable s 0 32 ∧ StackWords s 0 [5, 7]) s →
    (fun s : State => StackWritable s 0 32 ∧ StackWords s 0 [5, 7]) (s.setRet ret) := by
  janus64_pre_setRet

/-- m8: a pointer read survives when the precondition keeps the pointer apart from the return slot. -/
example (p : Program) : ∀ s ret, RetAddr p ret →
    (fun s : State => Janus.Apart (s.regs 0).toNat 8 (s.regs 4).toNat 8 ∧ s.mem.readLE (s.regs 0).toNat 8 = 5) s →
    (fun s : State => Janus.Apart (s.regs 0).toNat 8 (s.regs 4).toNat 8 ∧ s.mem.readLE (s.regs 0).toNat 8 = 5) (s.setRet ret) := by
  janus64_pre_setRet

/-- m9: a pointer read with nothing keeping it off the return slot is NOT discharged (extra conjunct needed). -/
example (p : Program) : True := by
  fail_if_success (have _h : ∀ s ret, RetAddr p ret →
    (fun s : State => Buffer s (s.regs 0) 8 false ∧ s.mem.readLE (s.regs 0).toNat 8 = 5) s →
    (fun s : State => Buffer s (s.regs 0) 8 false ∧ s.mem.readLE (s.regs 0).toNat 8 = 5) (s.setRet ret) := by janus64_pre_setRet)
  trivial

/-- m10: `[RSP] < 2^47` (a `CallOK64`-style conjunct) is not a pin: it follows from `RetAddr`. -/
example (p : Program) : ∀ s ret, RetAddr p ret →
    (fun s : State => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) s →
    (fun s : State => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (s.setRet ret) := by
  janus64_pre_setRet

/-- A function that is a single `ret` (`0xc3`) at `0x1000`. -/
def retProg64 : Program := { segments := [⟨"f", 0x1000, [0xc3]⟩], stubs := [], exitAddr := 0 }

/-- m11: the old attack's statement (a pin of `[RSP]`) is a true theorem about every admissible return address, proved
directly in the new shape: `hs.setRet` is the old-shaped `CallSetup` of `s.setRet ret`, the run starts there, and the facts
about the new state come from the precondition on `s` (`setRet_accessible`, `setRet_regs`). The equation `hsr` is cleared
before the run so that the tactic keeps speaking of `s1`. -/
example : Ensures retProg64 0x1000 [] (fun s => s.mem.readLE (s.regs 4).toNat 8 = 0 ∧ StackWritable s 0 8)
    (fun _ _ => True) := by
  intro s hs ⟨_, hw⟩ ret hret
  have hs1 := hs.setRet (p := retProg64) hret.lt64
  obtain ⟨-, hnw, hacc⟩ := hw
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  generalize hsr : s.setRet ret = s1 at hs1 ⊢
  have h4 : s1.regs 4 = s.regs 4 := by rw [← hsr]; rfl
  have hacc1 : s1.mem.accessible (s1.regs 4).toNat 8 false = true := by
    rw [h4, ← hsr]; simp only [setRet_accessible]; exact Janus.Arm64.Memory.accessible_read_of_write _ hacc
  clear h4 hsr hacc hnw
  janus64_intro hs1
  janus64_run

end Amd64

end JanusTests.RetAddr
