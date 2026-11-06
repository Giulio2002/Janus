import Janus.Amd64.Exec
import Janus.Amd64.Decode
import Janus.Amd64.Run
import Janus.Amd64.Tactic

/-!
# Translation invariance of position-independent amd64 code

The amd64 counterpart of `RelocArm64`: a runtime-contract stub proven once, at one address `a`, holds at any address
`a1` where a program fetches the same bytes. Instructions are variable-length, so the stub is described by its
instruction starts (`stSet`, the sequential decode) and the static check `CodeOK64`:

* the first instruction is `mov r15, [rsp]` (the return address into `R15`), every other is `jmp r15` (the last: no
  successor) or a position-independent instruction (`RelOK`: no `RIP`-relative operand) that does not write `R15` and
  whose branch targets are instruction starts of the stub;
* `exec_ok_shift`: such an instruction commutes with adding a constant to `RIP` (branch targets must stay canonical
  user addresses, `< 2^47`); `exec_post`: where it goes (`RIP` plus one of `relTargets`) and which registers it writes;
* `sim64`: a run of the stub at `a` is a run at `a1` (shifted start state, same final state), by induction on the
  steps; `summary_transport64` moves a `Summary` of the stub at `a` to any `p1` that fetches the stub at `a1`. The
  preconditions must force the saved return address below `a` (so `jmp r15` leaves the stub), and `pre`/`post` must not
  mention `RIP`.

The `ret` of the real functions is replaced in the stub by `add rsp, 8; jmp r15`, with `R15` holding the saved return
address since the prologue: an absolute jump through a register the stub never writes, as `X30` is on arm64.
Nothing is trusted; no axiom.
-/

open Janus Janus.Amd64

set_option maxRecDepth 100000
namespace Janus.Contracts.RelocAmd64

def shiftRip (d : BitVec 64) (s : State) : State := { s with rip := s.rip + d }

/-- Results correspond: `ok` states are shifted, faults are faults. -/
def ExR (d : BitVec 64) : Except Fault State → Except Fault State → Prop
  | .ok a, .ok b => b = shiftRip d a
  | .error _, .error _ => True
  | _, _ => False

def addrOK (a : Addr) : Bool := !a.rip
@[simp] theorem mem_s (d) (s : State) : (shiftRip d s).mem = s.mem := rfl
@[simp] theorem regs_s (d) (s : State) : (shiftRip d s).regs = s.regs := rfl
@[simp] theorem flags_s (d) (s : State) : (shiftRip d s).flags = s.flags := rfl
@[simp] theorem rip_s (d) (s : State) : (shiftRip d s).rip = s.rip + d := rfl

@[simp] theorem getReg_s (d) (s : State) (w r) : (shiftRip d s).getReg w r = s.getReg w r := rfl
@[simp] theorem getHigh_s (d) (s : State) (r) : (shiftRip d s).getHigh r = s.getHigh r := rfl

def locOK : Loc → Bool | .mem a => addrOK a | _ => true
def srcOK : Src → Bool | .loc l => locOK l | .imm _ => true

theorem ea_s (d) (s : State) (n n' : W64) (a : Addr) (h : addrOK a = true) :
    ea (shiftRip d s) n' a = ea s n a := by
  have h' : a.rip = false := by simpa [addrOK] using h
  simp [ea, eaOff, h', shiftRip]

theorem readLoc_s (d) (s : State) (n n' : W64) (w) (l : Loc) (h : locOK l = true) :
    readLoc (shiftRip d s) n' w l = readLoc s n w l := by
  cases l with
  | reg r => rfl
  | high r => rfl
  | mem a => simp only [locOK] at h; simp only [readLoc, ea_s d s n n' a h]; rfl

theorem readLocRW_s (d) (s : State) (n n' : W64) (w) (l : Loc) (h : locOK l = true) :
    readLocRW (shiftRip d s) n' w l = readLocRW s n w l := by
  cases l with
  | reg r => rfl
  | high r => rfl
  | mem a => simp only [locOK] at h; simp only [readLocRW, ea_s d s n n' a h]; rfl

theorem readSrc_s (d) (s : State) (n n' : W64) (w) (l : Src) (h : srcOK l = true) :
    readSrc (shiftRip d s) n' w l = readSrc s n w l := by
  cases l with
  | loc l => exact readLoc_s d s n n' w l h
  | imm v => rfl

theorem putReg_s (d) (s : State) (w r) (v : BitVec w) : (shiftRip d s).putReg w r v = shiftRip d (s.putReg w r v) := by
  unfold State.putReg State.setReg shiftRip; split <;> rfl


@[simp] theorem setReg_s (d) (s : State) (r) (v : W64) : (shiftRip d s).setReg r v = shiftRip d (s.setReg r v) := rfl

theorem writeLoc_s (d) (s : State) (n n' : W64) (w) (l : Loc) (v : BitVec w) (h : locOK l = true) :
    writeLoc (shiftRip d s) n' w l v = (writeLoc s n w l v).map (shiftRip d) := by
  cases l with
  | reg r => simp [writeLoc, putReg_s, Except.map]
  | high r => simp [writeLoc, State.putHigh, Except.map]
  | mem a =>
    simp only [locOK] at h
    simp only [writeLoc, ea_s d s n n' a h, mem_s]
    split <;> simp [Except.map, shiftRip]

@[simp] theorem setFlags_s (d) (s : State) (f) : (shiftRip d s).setFlags f = shiftRip d (s.setFlags f) := rfl
theorem setRip_s (d) (s : State) (n : W64) : (shiftRip d s).setRip (n + d) = shiftRip d (s.setRip n) := by
  simp [State.setRip, shiftRip]

theorem execAlu_s (d) (s : State) (n : W64) (op w dst src) (h1 : locOK dst = true) (h2 : srcOK src = true) :
    ExR d (execAlu s n op w dst src) (execAlu (shiftRip d s) (n + d) op w dst src) := by
  unfold execAlu
  simp only [readSrc_s d s n (n + d) w src h2, readLoc_s d s n (n + d) w dst h1, readLocRW_s d s n (n + d) w dst h1,
    writeLoc_s d s n (n + d) w dst _ h1, mem_s, regs_s, flags_s]
  repeat' split
  all_goals (try simp_all [Except.map, ExR, setRip_s])
  all_goals (subst_vars; rfl)



theorem execUnary_s (d) (s : State) (n : W64) (op w dst) (h1 : locOK dst = true) :
    ExR d (execUnary s n op w dst) (execUnary (shiftRip d s) (n + d) op w dst) := by
  unfold execUnary
  simp only [readLocRW_s d s n (n + d) w dst h1, writeLoc_s d s n (n + d) w dst _ h1, mem_s, regs_s, flags_s]
  repeat' split
  all_goals (try simp_all [Except.map, ExR, setRip_s])
  all_goals (subst_vars; rfl)

theorem execImul_s (d) (s : State) (n : W64) (w dst) (a : Loc) (b : Src) (h1 : locOK a = true) (h2 : srcOK b = true) :
    ExR d (execImul s n w dst a b) (execImul (shiftRip d s) (n + d) w dst a b) := by
  unfold execImul
  simp only [readLoc_s d s n (n + d) w a h1, readSrc_s d s n (n + d) w b h2, mem_s, regs_s, flags_s]
  repeat' split
  all_goals (try simp_all [Except.map, ExR, setRip_s, putReg_s])
  all_goals (subst_vars; rfl)

theorem execDiv_s (d) (s : State) (n : W64) (signed w) (src : Loc) (h1 : locOK src = true) :
    ExR d (execDiv s n signed w src) (execDiv (shiftRip d s) (n + d) signed w src) := by
  unfold execDiv
  simp only [readLoc_s d s n (n + d) w src h1, mem_s, regs_s, flags_s, getReg_s, getHigh_s]
  repeat' split
  all_goals (try simp_all [Except.map, ExR, setRip_s, putReg_s])
  all_goals (subst_vars; rfl)


theorem next_s (d) (s : State) (len : Nat) :
    BitVec.ofNat 64 (((shiftRip d s).rip.toNat + len) % 2 ^ 64) = BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64) + d := by
  apply BitVec.eq_of_toNat_eq
  simp only [rip_s, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

def RelOK : Instr → Bool
  | .alu op _ dst src => (op != .adc && op != .sbb) && locOK dst && srcOK src
  | .test _ a b => locOK a && srcOK b
  | .mov _ dst src => locOK dst && srcOK src
  | .lea _ _ a => addrOK a
  | .unary _ _ dst => locOK dst
  | .imul _ _ a b => locOK a && srcOK b
  | .div _ _ src => locOK src
  | .setcc _ dst => locOK dst
  | .cmov _ _ _ src => locOK src
  | .jcc _ _ => true
  | .jmp _ => true
  | _ => false

/-- The offsets from the current `rip` of the places a `RelOK` instruction of length `len` can go. -/
def relTargets (i : Instr) (len : Nat) : List (BitVec 64) :=
  match i with
  | .jcc _ rel => [BitVec.ofNat 64 len, BitVec.ofNat 64 len + BitVec.ofNat 64 rel]
  | .jmp rel => [BitVec.ofNat 64 len + BitVec.ofNat 64 rel]
  | _ => [BitVec.ofNat 64 len]

def isBr : Instr → Bool | .jcc .. => true | .jmp .. => true | _ => false

theorem exec_ExR (d) (i : Instr) (len : Nat) (s : State) (h : RelOK i = true) (hb : isBr i = false) :
    ExR d (exec i len s) (exec i len (shiftRip d s)) := by
  cases i <;> first | (simp [RelOK] at h; done) | (simp [isBr] at hb; done) | skip
  case alu op w dst src =>
    simp only [RelOK, Bool.and_eq_true] at h
    simp only [exec, next_s]
    exact execAlu_s d s _ op w dst src h.1.2 h.2
  case unary op w dst =>
    simp only [RelOK] at h
    simp only [exec, next_s]
    exact execUnary_s d s _ op w dst h
  case imul w dst a b =>
    simp only [RelOK, Bool.and_eq_true] at h
    simp only [exec, next_s]
    exact execImul_s d s _ w dst a b h.1 h.2
  case div sg w src =>
    simp only [RelOK] at h
    simp only [exec, next_s]
    exact execDiv_s d s _ sg w src h
  case test w a b =>
    simp only [RelOK, Bool.and_eq_true] at h
    simp only [exec, next_s]
    generalize BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64) = n
    simp only [readLoc_s d s n (n + d) w a h.1, readSrc_s d s n (n + d) w b h.2, mem_s, regs_s, flags_s]
    repeat' split
    all_goals (try simp_all [Except.map, ExR, setRip_s])
    all_goals (subst_vars; rfl)
  case mov w dst src =>
    simp only [RelOK, Bool.and_eq_true] at h
    simp only [exec, next_s]
    generalize BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64) = n
    simp only [readSrc_s d s n (n + d) w src h.2, writeLoc_s d s n (n + d) w dst _ h.1, mem_s, regs_s, flags_s]
    repeat' split
    all_goals (try simp_all [Except.map, ExR, setRip_s])
    all_goals (subst_vars; rfl)
  case lea w dst a =>
    simp only [RelOK] at h
    simp only [exec, next_s]
    generalize BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64) = n
    simp only [ea_s d s n (n + d) a h, putReg_s, ExR, setRip_s]
  case setcc cc dst =>
    simp only [RelOK] at h
    simp only [exec, next_s]
    generalize BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64) = n
    simp only [writeLoc_s d s n (n + d) 8 dst _ h, mem_s, regs_s, flags_s]
    repeat' split
    all_goals (try simp_all [Except.map, ExR, setRip_s])
    all_goals (subst_vars; rfl)
  case cmov cc w dst src =>
    simp only [RelOK] at h
    simp only [exec, next_s]
    generalize BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64) = n
    simp only [readLoc_s d s n (n + d) w src h, mem_s, regs_s, flags_s, getReg_s]
    repeat' split
    all_goals (try simp_all [Except.map, ExR, setRip_s, putReg_s])
    all_goals (subst_vars; rfl)


theorem add_p1 (a b c d : BitVec 64) : a + d + b + c = a + b + c + d := by ac_rfl
theorem add_p2 (a b d : BitVec 64) : a + d + b = a + b + d := by ac_rfl
theorem add_p3 (a b c d : BitVec 64) : a + d + (b + c) = a + d + b + c := (BitVec.add_assoc _ _ _).symm

theorem next_eq (x : W64) (len : Nat) :
    BitVec.ofNat 64 ((x.toNat + len) % 2 ^ 64) = x + BitVec.ofNat 64 len := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem tgt_eq (n : W64) (rel : Nat) : BitVec.ofNat 64 ((n.toNat + rel) % 2 ^ 64) = n + BitVec.ofNat 64 rel := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem exec_ok_shift (d) (i : Instr) (len : Nat) (s s1 : State) (h : RelOK i = true)
    (hx : exec i len s = .ok s1) (hb : ∀ o ∈ relTargets i len, (s.rip + d + o).toNat < 2 ^ 47) :
    exec i len (shiftRip d s) = .ok (shiftRip d s1) := by
  by_cases hbr : isBr i = true
  · cases i <;> simp [isBr] at hbr
    case jcc cc rel =>
      simp only [exec, next_eq, rip_s, flags_s] at hx ⊢
      cases hc : condition cc s.flags with
      | none => simp [hc] at hx
      | some b =>
        simp only [hc] at hx ⊢
        by_cases hb' : b = true
        · simp only [hb', if_true, branchTo, tgt_eq, next_eq] at hx ⊢
          have hlt := hb (BitVec.ofNat 64 len + BitVec.ofNat 64 rel) (by simp [relTargets])
          have e : s.rip + d + BitVec.ofNat 64 len + BitVec.ofNat 64 rel = (s.rip + BitVec.ofNat 64 len + BitVec.ofNat 64 rel) + d := add_p1 _ _ _ _
          have e2 : s.rip + d + (BitVec.ofNat 64 len + BitVec.ofNat 64 rel) = s.rip + d + BitVec.ofNat 64 len + BitVec.ofNat 64 rel := add_p3 _ _ _ _
          rw [e2] at hlt
          rw [if_pos hlt]
          split at hx
          · simp only [Except.ok.injEq] at hx; subst hx; rw [e, setRip_s]
          · simp at hx
        · have hb'' : b = false := by simpa using hb'
          subst hb''
          simp only [Bool.false_eq_true, if_false, next_eq] at hx ⊢
          simp only [Except.ok.injEq] at hx; subst hx
          have e3 : s.rip + d + BitVec.ofNat 64 len = (s.rip + BitVec.ofNat 64 len) + d := add_p2 _ _ _
          rw [e3, setRip_s]
    case jmp rel =>
      simp only [exec, next_eq, rip_s, flags_s, branchTo, tgt_eq] at hx ⊢
      have hlt := hb (BitVec.ofNat 64 len + BitVec.ofNat 64 rel) (by simp [relTargets])
      have e : s.rip + d + BitVec.ofNat 64 len + BitVec.ofNat 64 rel = (s.rip + BitVec.ofNat 64 len + BitVec.ofNat 64 rel) + d := add_p1 _ _ _ _
      have e2 : s.rip + d + (BitVec.ofNat 64 len + BitVec.ofNat 64 rel) = s.rip + d + BitVec.ofNat 64 len + BitVec.ofNat 64 rel := add_p3 _ _ _ _
      rw [e2] at hlt
      rw [if_pos hlt]
      split at hx
      · simp only [Except.ok.injEq] at hx; subst hx; rw [e, setRip_s]
      · simp at hx
  · have hbr' : isBr i = false := by simpa using hbr
    have hE := exec_ExR d i len s h hbr'
    rw [hx] at hE
    cases h2 : exec i len (shiftRip d s) with
    | error e => rw [h2] at hE; simp [ExR] at hE
    | ok b => rw [h2] at hE; simp only [ExR] at hE; rw [hE]


theorem putReg_regs (s : State) (w r r' : Nat) (v : BitVec w) (h : r' ≠ r) : (s.putReg w r v).regs r' = s.regs r' := by
  unfold State.putReg State.setReg; split <;> simp [h]

theorem putHigh_regs (s : State) (r r' : Nat) (v : BitVec 8) (h : r' ≠ r) : (s.putHigh r v).regs r' = s.regs r' := by
  unfold State.putHigh State.setReg; simp [h]

def locDest : Loc → List Nat | .reg r => [r] | .high r => [r] | .mem _ => []

def dest : Instr → List Nat
  | .alu op _ dst _ => if op = .cmp then [] else locDest dst
  | .mov _ dst _ => locDest dst
  | .lea _ dst _ => [dst]
  | .unary _ _ dst => locDest dst
  | .imul _ dst _ _ => [dst]
  | .div .. => [0, 2]
  | .setcc _ dst => locDest dst
  | .cmov _ _ dst _ => [dst]
  | _ => []

theorem writeLoc_regs (s : State) (n : W64) (w) (l : Loc) (v : BitVec w) (r : Nat) (h : r ∉ locDest l) (s' : State)
    (hx : writeLoc s n w l v = .ok s') : s'.regs r = s.regs r := by
  cases l with
  | reg r0 =>
    simp only [writeLoc, Except.ok.injEq] at hx; subst hx
    exact putReg_regs s w r0 r v (by simpa [locDest] using h)
  | high r0 =>
    simp only [writeLoc, Except.ok.injEq] at hx; subst hx
    exact putHigh_regs s r0 r _ (by simpa [locDest] using h)
  | mem a =>
    simp only [writeLoc] at hx
    split at hx
    · simp only [Except.ok.injEq] at hx; subst hx; rfl
    · simp at hx



theorem writeLoc_regs2 (s : State) (n : W64) (w) (l : Loc) (v : BitVec w) (r : Nat) (h : r ∉ locDest l) (s' : State)
    (hx : writeLoc s n w l v = .ok s') (t : State) (ht : t.regs = s'.regs) : t.regs r = s.regs r := by
  rw [ht]; exact writeLoc_regs s n w l v r h s' hx

/-- The result, if it succeeds, is at `n` and keeps the registers outside `D`. -/
def PostR (s : State) (n : W64) (D : List Nat) : Except Fault State → Prop
  | .ok s1 => s1.rip = n ∧ ∀ r, r ∉ D → s1.regs r = s.regs r
  | .error _ => True

theorem execAlu_post (s : State) (n : W64) (op w dst src) (hop : (op != .adc && op != .sbb) = true) :
    PostR s n (if op = .cmp then [] else locDest dst) (execAlu s n op w dst src) := by
  cases op <;> simp [bne_iff_ne] at hop <;> unfold execAlu <;> simp only [reduceCtorEq, if_true, if_false, ite_true, ite_false] <;>
    (repeat' split) <;> (try simp only [PostR]) <;> (try trivial) <;> first | exact ⟨rfl, fun r _ => rfl⟩ | (refine ⟨rfl, fun r hr => ?_⟩; simp only [State.setFlags, State.setRip]; apply writeLoc_regs s n w dst _ r hr; assumption)


macro "post_close" : tactic =>
  `(tactic| first
    | exact ⟨rfl, fun r _ => rfl⟩
    | (refine ⟨rfl, fun r hr => ?_⟩; simp only [State.setFlags, State.setRip]
       first
        | (apply writeLoc_regs _ _ _ _ _ r hr; assumption)
        | (exact putReg_regs _ _ _ r _ (by simpa [locDest] using hr))))

theorem execUnary_post (s : State) (n : W64) (op w dst) :
    PostR s n (locDest dst) (execUnary s n op w dst) := by
  unfold execUnary
  (repeat' split) <;> (try simp only [PostR]) <;> (try trivial) <;> post_close

theorem execImul_post (s : State) (n : W64) (w dst a b) :
    PostR s n [dst] (execImul s n w dst a b) := by
  unfold execImul
  (repeat' split) <;> (try simp only [PostR]) <;> (try trivial) <;> post_close


theorem execDiv_post (s : State) (n : W64) (signed w src) :
    PostR s n [0, 2] (execDiv s n signed w src) := by
  unfold execDiv
  dsimp only
  repeat' split
  all_goals (try simp only [PostR])
  all_goals (try trivial)
  all_goals (refine ⟨rfl, fun r hr => ?_⟩
             simp only [State.setFlags, State.setRip, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
             first
              | (rw [putReg_regs _ _ _ r _ hr.2, putReg_regs _ _ _ r _ hr.1])
              | (rw [putReg_regs _ _ _ r _ hr.1]))

theorem exec_postR (i : Instr) (len : Nat) (s : State) (h : RelOK i = true) (hb : isBr i = false) :
    PostR s (BitVec.ofNat 64 ((s.rip.toNat + len) % 2 ^ 64)) (dest i) (exec i len s) := by
  cases i <;> first | (simp [RelOK] at h; done) | (simp [isBr] at hb; done) | skip
  case alu op w dst src =>
    simp only [RelOK, Bool.and_eq_true] at h
    simp only [exec, dest]
    exact execAlu_post s _ op w dst src (by simp only [Bool.and_eq_true]; exact h.1.1)
  case unary op w dst => simp only [exec, dest]; exact execUnary_post s _ op w dst
  case imul w dst a b => simp only [exec, dest]; exact execImul_post s _ w dst a b
  case div sg w src => simp only [exec, dest]; exact execDiv_post s _ sg w src
  case test w a b =>
    simp only [exec, dest]
    repeat' split
    all_goals (try simp only [PostR])
    all_goals (try trivial)
    all_goals post_close
  case mov w dst src =>
    simp only [exec, dest]
    repeat' split
    all_goals (try simp only [PostR])
    all_goals (try trivial)
    all_goals post_close
  case lea w dst a =>
    simp only [exec, dest, PostR]
    post_close
  case setcc cc dst =>
    simp only [exec, dest]
    repeat' split
    all_goals (try simp only [PostR])
    all_goals (try trivial)
    all_goals post_close
  case cmov cc w dst src =>
    simp only [exec, dest]
    repeat' split
    all_goals (try simp only [PostR])
    all_goals (try trivial)
    all_goals post_close


theorem exec_post (i : Instr) (len : Nat) (s s1 : State) (h : RelOK i = true) (hx : exec i len s = .ok s1) :
    (∃ o ∈ relTargets i len, s1.rip = s.rip + o) ∧ (∀ r, r ∉ dest i → s1.regs r = s.regs r) := by
  by_cases hbr : isBr i = true
  · cases i <;> simp [isBr] at hbr
    case jcc cc rel =>
      simp only [exec, next_eq] at hx
      cases hc : condition cc s.flags with
      | none => simp [hc] at hx
      | some b =>
        simp only [hc] at hx
        by_cases hb' : b = true
        · simp only [hb', if_true, branchTo, tgt_eq, next_eq] at hx
          split at hx
          · simp only [Except.ok.injEq] at hx; subst hx
            refine ⟨⟨BitVec.ofNat 64 len + BitVec.ofNat 64 rel, by simp [relTargets], ?_⟩, fun r _ => rfl⟩
            simp only [State.setRip]; exact BitVec.add_assoc _ _ _
          · simp at hx
        · have hb'' : b = false := by simpa using hb'
          subst hb''
          simp only [Bool.false_eq_true, if_false, next_eq] at hx
          simp only [Except.ok.injEq] at hx; subst hx
          exact ⟨⟨BitVec.ofNat 64 len, by simp [relTargets], rfl⟩, fun r _ => rfl⟩
    case jmp rel =>
      simp only [exec, next_eq, branchTo, tgt_eq] at hx
      split at hx
      · simp only [Except.ok.injEq] at hx; subst hx
        refine ⟨⟨BitVec.ofNat 64 len + BitVec.ofNat 64 rel, by simp [relTargets], ?_⟩, fun r _ => rfl⟩
        simp only [State.setRip]; exact BitVec.add_assoc _ _ _
      · simp at hx
  · have hbr' : isBr i = false := by simpa using hbr
    have hp := exec_postR i len s h hbr'
    rw [hx] at hp
    simp only [PostR] at hp
    refine ⟨⟨BitVec.ofNat 64 len, ?_, ?_⟩, hp.2⟩
    · cases i <;> simp [relTargets, isBr] at hbr' ⊢
    · rw [hp.1, next_eq]


/-! ## Programs -/

def win (bs : List Nat) (off : Nat) : List Nat := (bs.drop off).take 15

def seqStarts (bs : List Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, off =>
    if off < bs.length then
      match decode (win bs off) with
      | some (_, len) => off :: seqStarts bs fuel (off + len)
      | none => [off]
    else []

def codeProg64 (a : Nat) (bs : List Nat) : Amd64.Program := { segments := [⟨"reloc", a, bs⟩], stubs := [], exitAddr := 0 }

/-- The prologue: `mov r15, [rsp]` (the return address into `R15`, which the rest of the stub never writes). -/
def prologue : Instr := .mov 64 (.reg 15) (.loc (.mem ⟨some 4, none, 0, 0, false, false⟩))
/-- The epilogue's jump: `jmp r15`. -/
def absJ : Instr := .jmpInd (.reg 15)

def stSet (bs : List Nat) : List Nat := seqStarts bs bs.length 0

/-- The static check of a position-independent stub: the first instruction is `prologue`, every other is `jmp r15`
(no successor) or a position-independent instruction that does not write `R15` and whose targets are instruction
starts of the stub (not the prologue). -/
def CodeOK64 (bs : List Nat) : Bool :=
  (match decode (win bs 0) with
    | some (i, len) => decide (i = prologue) && (relTargets i len).all fun o =>
        (stSet bs).contains (o.toNat % 2 ^ 64) && (o.toNat % 2 ^ 64 != 0)
    | none => false) &&
  (stSet bs).all fun off => off == 0 ||
    match decode (win bs off) with
    | none => false
    | some (i, len) => decide (i = absJ) || (RelOK i && !((dest i).contains 15) && (relTargets i len).all fun o =>
        (stSet bs).contains ((off + o.toNat) % 2 ^ 64) && ((off + o.toNat) % 2 ^ 64 != 0))

theorem codeOK_zero {bs : List Nat} (h : CodeOK64 bs = true) :
    ∃ len, decode (win bs 0) = some (prologue, len) ∧ ∀ o ∈ relTargets prologue len,
      (o.toNat) % 2 ^ 64 ∈ stSet bs ∧ o.toNat % 2 ^ 64 ≠ 0 := by
  simp only [CodeOK64, Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  split at h1
  · rename_i i len hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨hi, ht⟩ := h1
    subst hi
    refine ⟨len, hd, fun o ho => ?_⟩
    have := List.all_eq_true.mp ht o ho
    simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at this
    exact this
  · simp at h1

theorem codeOK_off {bs : List Nat} (h : CodeOK64 bs = true) {off : Nat} (ho : off ∈ stSet bs) (hz : off ≠ 0) :
    ∃ i len, decode (win bs off) = some (i, len) ∧ (i = absJ ∨ (RelOK i = true ∧ 15 ∉ dest i ∧
      ∀ o ∈ relTargets i len, (off + o.toNat) % 2 ^ 64 ∈ stSet bs ∧ (off + o.toNat) % 2 ^ 64 ≠ 0)) := by
  simp only [CodeOK64, Bool.and_eq_true] at h
  obtain ⟨-, h2⟩ := h
  have := List.all_eq_true.mp h2 off ho
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h0 | h1
  · exact absurd h0 hz
  · split at h1
    · simp at h1
    · rename_i i len hd
      refine ⟨i, len, hd, ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true'] at h1
      rcases h1 with h1 | ⟨⟨h1, h2⟩, h3⟩
      · exact Or.inl h1
      · refine Or.inr ⟨h1, ?_, fun o ho => ?_⟩
        · simpa using h2
        · have := List.all_eq_true.mp h3 o ho
          simp only [Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at this
          exact this


theorem fetch_c {a : Nat} {bs : List Nat} {pc : Nat} {w : List Nat} (h : (codeProg64 a bs).fetch pc = some w) :
    ∃ off, off < bs.length ∧ pc = a + off ∧ w = win bs off := by
  simp only [codeProg64, Amd64.Program.fetch, Amd64.Program.fetchIn] at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    exact ⟨pc - a, by omega, by omega, by rw [← h]; rfl⟩
  · simp [Amd64.Program.fetchIn] at h

theorem pc_shift64 (a a1 off : Nat) (h1 : a + off < 2 ^ 64) (h2 : a1 + off < 2 ^ 64) (x : W64) (hx : x.toNat = a + off) :
    (x + (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a)).toNat = a1 + off := by
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hx]
  omega

theorem tgt_shift64 (a a1 off t : Nat) (o : W64) (h1 : a + off < 2 ^ 64) (h2 : a1 + t < 2 ^ 64)
    (ht : t = (off + o.toNat) % 2 ^ 64) (x : W64) (hx : x.toNat = a + off) :
    (x + (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) + o).toNat = a1 + t := by
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hx]
  have := o.isLt
  omega

theorem tgt_unshift64 (a off t : Nat) (o : W64) (h1 : a + off < 2 ^ 64) (h2 : a + t < 2 ^ 64)
    (ht : t = (off + o.toNat) % 2 ^ 64) (x : W64) (hx : x.toNat = a + off) :
    (x + o).toNat = a + t := by
  simp only [BitVec.toNat_add, hx]
  have := o.isLt
  omega


theorem seqStarts_lt (bs : List Nat) : ∀ f o off, off ∈ seqStarts bs f o → off < bs.length := by
  intro f
  induction f with
  | zero => intro o off h; simp [seqStarts] at h
  | succ f ih =>
    intro o off h
    simp only [seqStarts] at h
    split at h
    · rename_i hlt
      split at h
      · rename_i i len hd
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact hlt
        · exact ih _ _ h
      · simp only [List.mem_singleton] at h; omega
    · simp at h

theorem absJ_exec (len : Nat) (s s1 : State) (hx : exec absJ len s = .ok s1) :
    s1 = s.setRip (s.regs 15) ∧ (s.regs 15).toNat < 2 ^ 47 := by
  simp only [absJ, exec, readLoc, State.getReg, branchTo] at hx
  split at hx
  · rename_i hlt
    simp only [Except.ok.injEq] at hx
    simp only [BitVec.setWidth_eq] at hlt hx
    exact ⟨hx.symm, hlt⟩
  · simp at hx

theorem absJ_shift (d : BitVec 64) (len : Nat) (s s1 : State) (hx : exec absJ len s = .ok s1) :
    exec absJ len (shiftRip d s) = .ok s1 := by
  obtain ⟨h1, h2⟩ := absJ_exec len s s1 hx
  simp only [absJ, exec, readLoc, State.getReg, branchTo, regs_s]
  simp only [BitVec.setWidth_eq]
  rw [if_pos h2, h1]
  rfl


theorem sim64 (a a1 : Nat) (bs : List Nat) (p1 : Amd64.Program) (hc : CodeOK64 bs = true)
    (hfit : a + bs.length < 2 ^ 47) (hfit1 : a1 + bs.length ≤ 2 ^ 47)
    (hp1 : ∀ off ∈ stSet bs, p1.fetch (a1 + off) = some (win bs off) ∧ p1.stubAt (a1 + off) = none ∧
      a1 + off ≠ p1.exitAddr) :
    ∀ k s s', Amd64.Program.Steps (codeProg64 a bs) s k s' →
      (∃ off ∈ stSet bs, off ≠ 0 ∧ s.rip.toNat = a + off) → (s.regs 15).toNat < a →
      ¬ (∃ off ∈ stSet bs, off ≠ 0 ∧ s'.rip.toNat = a + off) →
      Amd64.Program.Steps p1 (shiftRip (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s) k s' := by
  intro k s s' hs
  induction hs with
  | refl s => intro h1 _ h3; exact absurd h1 h3
  | @step s s1 s2 k w hx hst hf hexec rest ih =>
    intro hin h15 hout
    obtain ⟨off0, ho0, hz0, hpc0⟩ := hin
    obtain ⟨off, hlen, hpc, hw⟩ := fetch_c hf
    have hoff : off = off0 := by omega
    subst hoff
    obtain ⟨i, len, hd, hcase⟩ := codeOK_off hc ho0 hz0
    rw [hw] at hexec
    rw [step_of_decode hd] at hexec
    have hlt : off < bs.length := seqStarts_lt bs _ _ _ ho0
    obtain ⟨hf1, hst1, hx1⟩ := hp1 off ho0
    have hrip1 : (shiftRip (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s).rip.toNat = a1 + off :=
      pc_shift64 a a1 off (by omega) (by omega) s.rip hpc0
    rcases hcase with hj | ⟨hrel, h15d, htg⟩
    · subst hj
      obtain ⟨hs1, hlt47⟩ := absJ_exec len s s1 hexec
      have hnot : ¬ (∃ off' ∈ stSet bs, off' ≠ 0 ∧ s1.rip.toNat = a + off') := by
        rintro ⟨off', _, _, hp⟩
        rw [hs1] at hp
        simp only [State.setRip] at hp
        omega
      cases rest with
      | refl =>
        exact Amd64.Program.Steps.single (by rw [hrip1]; exact hx1) (by rw [hrip1]; exact hst1)
          (by rw [hrip1]; exact hf1) (by rw [step_of_decode hd]; exact absJ_shift _ len s s1 hexec)
      | @step _ s3 _ k' w' hx' hst' hf' hexec' rest' =>
        obtain ⟨off', hlen', hpc', _⟩ := fetch_c hf'
        rw [hs1] at hpc'
        simp only [State.setRip] at hpc'
        omega
    · obtain ⟨⟨o, ho, hrip⟩, hregs⟩ := exec_post i len s s1 hrel hexec
      have hto := htg o ho
      have hs1rip : s1.rip.toNat = a + (off + o.toNat) % 2 ^ 64 := by
        rw [hrip]
        exact tgt_unshift64 a off _ o (by omega) (by have := seqStarts_lt bs _ _ _ hto.1; omega) rfl s.rip hpc0
      have hin' : ∃ off' ∈ stSet bs, off' ≠ 0 ∧ s1.rip.toNat = a + off' := ⟨_, hto.1, hto.2, hs1rip⟩
      have h15' : (s1.regs 15).toNat < a := by rw [hregs 15 h15d]; exact h15
      have ih' := ih hin' h15' hout
      have hb : ∀ o ∈ relTargets i len, (s.rip + (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) + o).toNat < 2 ^ 47 := by
        intro o ho
        have hto := htg o ho
        have hl := seqStarts_lt bs _ _ _ hto.1
        rw [tgt_shift64 a a1 off _ o (by omega) (by omega) rfl s.rip hpc0]
        omega
      have h1 := exec_ok_shift (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) i len s s1 hrel hexec hb
      exact Amd64.Program.Steps.step (by rw [hrip1]; exact hx1) (by rw [hrip1]; exact hst1)
        (by rw [hrip1]; exact hf1) (by rw [step_of_decode hd]; exact h1) ih'


theorem relOK_prologue : RelOK prologue = true := by simp [prologue, RelOK, locOK, srcOK, addrOK]

theorem prologue_exec (len : Nat) (s s1 : State) (hx : exec prologue len s = .ok s1) :
    (s1.regs 15).toNat ≤ s.mem.readLE (s.regs 4).toNat 8 := by
  simp only [prologue, exec, readSrc, readLoc, ea, eaOff, writeLoc, Bool.false_eq_true, if_false, load] at hx
  have e : s.regs 4 + 0 + 0#64 = s.regs 4 := by simp
  simp only [e, Nat.reduceDiv] at hx
  by_cases hacc : s.mem.accessible (BitVec.toNat (s.regs 4)) 8 false = true
  · simp only [hacc, ↓reduceIte, Except.ok.injEq] at hx
    subst hx
    simp only [State.putReg, State.setReg, State.setRip]
    simp
    exact Nat.mod_le _ _
  · simp [hacc] at hx


theorem shift_back64 (a a1 : Nat) (t : State) (ht : t.rip = BitVec.ofNat 64 a1) :
    shiftRip (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) { t with rip := BitVec.ofNat 64 a } = t := by
  have e : BitVec.ofNat 64 a + (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) = t.rip := by
    rw [ht]; bv_omega
  show ({ t with rip := BitVec.ofNat 64 a + (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) } : State) = t
  rw [e]

open Janus.Amd64.Tactic in
/-- **Translation invariance (amd64).** -/
theorem summary_transport64 (a a1 : Nat) (bs : List Nat) (p1 : Amd64.Program) (pre : State → Prop)
    (post : State → State → Prop) (hn : 0 < bs.length) (hc : CodeOK64 bs = true)
    (hfit : a + bs.length < 2 ^ 47) (hfit1 : a1 + bs.length ≤ 2 ^ 47)
    (hp1 : ∀ off ∈ stSet bs, p1.fetch (a1 + off) = some (win bs off) ∧ p1.stubAt (a1 + off) = none ∧
      a1 + off ≠ p1.exitAddr)
    (hret : ∀ t, pre t → t.mem.readLE (t.regs 4).toNat 8 < a)
    (hpre : ∀ s (q : BitVec 64), pre s → pre { s with rip := q })
    (hpost : ∀ s s' (q : BitVec 64), post s s' → post { s with rip := q } s')
    (h : Summary (codeProg64 a bs) a pre post) : Summary p1 a1 pre post := by
  intro t ht hp
  have hs0 : ({ t with rip := BitVec.ofNat 64 a } : State).rip = BitVec.ofNat 64 a := rfl
  have hpre0 : pre { t with rip := BitVec.ofNat 64 a } := hpre t _ hp
  have hrb := hret _ hpre0
  obtain ⟨k, s', hsteps, hpc', hq⟩ := h _ hs0 hpre0
  have hrb' : (retAddrOf { t with rip := BitVec.ofNat 64 a }).toNat < a := by
    simp only [retAddrOf, BitVec.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hrb
  have hnot : ¬ (∃ off ∈ stSet bs, off ≠ 0 ∧ s'.rip.toNat = a + off) := by
    rintro ⟨off, _, _, hp⟩
    rw [hpc'] at hp
    omega
  cases hsteps with
  | refl =>
    exfalso
    rw [hpc'] at hs0
    have := congrArg BitVec.toNat hs0
    simp only [BitVec.toNat_ofNat] at this
    omega
  | @step _ s1 _ k' w hx hst hf hexec rest =>
    obtain ⟨off, hlen, hpc, hw⟩ := fetch_c hf
    have hs0n : ({ t with rip := BitVec.ofNat 64 a } : State).rip.toNat = a := by
      simp only [BitVec.toNat_ofNat]; omega
    have hoff : off = 0 := by
      have := hpc
      rw [hs0n] at this
      omega
    subst hoff
    obtain ⟨len0, hd, hz⟩ := codeOK_zero hc
    rw [hw] at hexec
    rw [step_of_decode hd] at hexec
    have h0st : 0 ∈ stSet bs := by
      obtain ⟨m, hm⟩ : ∃ m, bs.length = m + 1 := ⟨bs.length - 1, by omega⟩
      simp only [stSet, hm, seqStarts]
      rw [if_pos (by omega), hd]
      simp
    generalize hsdef : ({ t with rip := BitVec.ofNat 64 a } : State) = s at *
    obtain ⟨⟨o, ho, hrip⟩, hregs⟩ := exec_post prologue len0 s s1 relOK_prologue hexec
    have hz' := hz o ho
    have ho' : o ∈ relTargets prologue len0 := ho
    have hs1rip : s1.rip.toNat = a + o.toNat % 2 ^ 64 := by
      rw [hrip]
      have hl := seqStarts_lt bs _ _ _ hz'.1
      exact tgt_unshift64 a 0 (o.toNat % 2 ^ 64) o (by omega) (by omega) (by simp) s.rip hs0n
    have hin' : ∃ off' ∈ stSet bs, off' ≠ 0 ∧ s1.rip.toNat = a + off' := ⟨_, hz'.1, hz'.2, hs1rip⟩
    have h15' : (s1.regs 15).toNat < a := by
      have := prologue_exec len0 s s1 hexec
      exact Nat.lt_of_le_of_lt this hrb
    have hsim := sim64 a a1 bs p1 hc hfit hfit1 hp1 k' s1 s' rest hin' h15' hnot
    obtain ⟨hf1, hst1, hx1⟩ := hp1 0 h0st
    have hrip1 : (shiftRip (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s).rip.toNat = a1 + 0 :=
      pc_shift64 a a1 0 (by omega) (by omega) s.rip (by simpa using hs0n)
    have hb : ∀ o ∈ relTargets prologue len0, (s.rip + (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) + o).toNat < 2 ^ 47 := by
      intro o ho
      have hz' := hz o ho
      have hl := seqStarts_lt bs _ _ _ hz'.1
      rw [tgt_shift64 a a1 0 (o.toNat % 2 ^ 64) o (by omega) (by omega) (by simp) s.rip (by simpa using hs0n)]
      omega
    have h1 := exec_ok_shift (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) prologue len0 s s1 relOK_prologue hexec hb
    have hfull : Amd64.Program.Steps p1 (shiftRip (BitVec.ofNat 64 a1 - BitVec.ofNat 64 a) s) (k' + 1) s' :=
      Amd64.Program.Steps.step (by rw [hrip1]; exact hx1) (by rw [hrip1]; exact hst1)
        (by rw [hrip1]; simpa using hf1) (by rw [step_of_decode (by simpa using hd)]; exact h1) hsim
    rw [← hsdef, shift_back64 a a1 t ht] at hfull
    have hrt : retAddrOf s = retAddrOf t := by rw [← hsdef]; rfl
    refine ⟨k' + 1, s', hfull, hpc'.trans hrt, ?_⟩
    have e : ({ s with rip := t.rip } : State) = t := by rw [← hsdef]
    have := hpost s s' t.rip hq
    rw [e] at this
    exact this

end Janus.Contracts.RelocAmd64
