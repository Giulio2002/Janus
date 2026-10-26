import Janus.Contracts.Print
import Janus.Contracts.SyscallAmd64
import Janus.Contracts.AllocSatAmd64

/-!
# `print` and `println` (amd64; R8)

The amd64 counterpart of `Janus.Print` (read that module first: the lowering of `print`/`println`,
what is executed from the binary and what is a contract, and the output predicate `Emits`, which
is shared). The amd64 specifics:

* registers: `g` is `R14` (`regs 14`), `SP` is `RSP` (`regs 4`), the return address is at
  `[RSP]`; Go's ABIInternal passes `RAX RBX RCX RDI RSI …` (`regs 0 3 1 7 6`);
* `runtime.write` reloads `g` from the TLS slot `[FS - 8]` after `write1` (an ABI0 call), so the
  call state must have `FS` pointing just above a word holding `g` (`PrintReady64`);
* `runtime.lock2`/`unlock2` take the mutex in `RAX`, `runtime.memmove(to, from, n)` takes
  `RAX RBX RCX`.

The contracts (`Lock2Contract`, `Unlock2Contract`, `MemmoveContract`) state the same behaviour as
on arm64; their `_satisfiable` witnesses are in `Janus.Contracts.PrintSatAmd64`.
-/

namespace Janus.Amd64.Print

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Kernel
  Janus.Amd64.Kernel Janus.Print

/-- A `ReturnsK` run is a `Reaches` run to an outcome satisfying `IsReturnK` (amd64; the converse
of `ReturnsK.of_reaches`). -/
theorem ReturnsK.to_reaches {p : Program} {E : KEnv} {post : State → Kern → Prop}
    {onExit : Nat → Kern → Prop} {s : State} {k : Kern} (h : Amd64.Kernel.ReturnsK p E post onExit s k) :
    Reaches p s (IsReturnK p E post onExit k) := by
  induction h with
  | exit hx hp => exact ⟨1, .returned _, by simp [Program.run, hx], hp⟩
  | @step s s' k w hx hs hf hst _ ih =>
    obtain ⟨n, o, hr, hq⟩ := ih
    refine ⟨n + 1, o, ?_, hq⟩
    simp only [Program.run, ite_eq_right hx, hs, hf, hst]
    exact hr
  | @sys s k st site hx hs hk hsite hsafe hn _ =>
    refine ⟨1, .stub st.name st.kind s, by simp [Program.run, hx, hs], ?_⟩
    rw [hk]
    exact ⟨site, hsite, Or.inl ⟨hsafe, hn⟩⟩
  | @halt s k st site code hx hs hk hsite he hp =>
    refine ⟨1, .stub st.name st.kind s, by simp [Program.run, hx, hs], ?_⟩
    rw [hk]
    exact ⟨site, hsite, Or.inr ⟨code, he, hp⟩⟩

/-! ## Runtime contracts -/

/-- What `lock2`/`unlock2` need at the call (amd64): as `Print.LockPre`, with the mutex in `RAX`
and `g` in `R14`. -/
def LockPre (rt : List (Nat × Nat)) (lo : Nat) (s : State) : Prop :=
  (s.regs 0).toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 8 true = true ∧
    InRanges (s.regs 0).toNat 8 rt ∧
    (s.regs 14).toNat + gM + 8 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + gM) 8 false = true ∧
    Outside ((s.regs 14).toNat + gM) 8 rt ∧
    s.mem.readLE ((s.regs 14).toNat + gM) 8 + mLocks + 4 ≤ 2 ^ 48 ∧
    s.mem.accessible (s.mem.readLE ((s.regs 14).toNat + gM) 8 + mLocks) 4 true = true ∧
    InRanges (s.mem.readLE ((s.regs 14).toNat + gM) 8 + mLocks) 4 rt ∧
    Apart (s.regs 0).toNat 8 (s.mem.readLE ((s.regs 14).toNat + gM) 8 + mLocks) 4 ∧
    lo ≤ mLocksOf s.mem (s.regs 14).toNat ∧ mLocksOf s.mem (s.regs 14).toNat + 1 < 2 ^ 31

/-- **`runtime.lock2(l)`** (amd64; `RAX = l`): as `Print.Lock2Contract` (the uncontended fast
path: the key's lock bit set, `m.locks` one higher, every other change inside `rt` and the stack
window). The return (`retState64`) keeps `RSP + 8`, `RBP`, `R14`, `X15`, `FS` and `DF`. -/
def Lock2Contract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  Summary p addr (fun s => CallOK64 s stack 1 ∧ LockPre rt 0 s ∧ ¬ lockHeld s.mem (s.regs 0).toNat)
    (fun s s' => AllocRet64 rt stack 1 (fun _ => []) s s' fun m _ =>
      lockHeld m (s.regs 0).toNat ∧
        mLocksOf m (s.regs 14).toNat = mLocksOf s.mem (s.regs 14).toNat + 1)

/-- **`runtime.unlock2(l)`** (amd64; `RAX = l`): as `Print.Unlock2Contract`. -/
def Unlock2Contract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  Summary p addr (fun s => CallOK64 s stack 1 ∧ LockPre rt 1 s ∧ lockHeld s.mem (s.regs 0).toNat)
    (fun s s' => AllocRet64 rt stack 1 (fun _ => []) s s' fun m _ =>
      m.readLE (s.regs 0).toNat 1 = 0 ∧
        mLocksOf m (s.regs 14).toNat + 1 = mLocksOf s.mem (s.regs 14).toNat)

/-- What `memmove(to, from, n)` needs here (amd64; `RAX = to`, `RBX = from`, `RCX = n`): the
return address at `[RSP]` (`CallOK64 s 0 0`), `n` writable bytes at `to` and `n` readable bytes at
`from`, below `2^48` and disjoint. -/
def MemmovePre (s : State) : Prop :=
  CallOK64 s 0 0 ∧
    (s.regs 0).toNat + (s.regs 1).toNat ≤ 2 ^ 48 ∧ (s.regs 3).toNat + (s.regs 1).toNat ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 0).toNat (s.regs 1).toNat true = true ∧
    s.mem.accessible (s.regs 3).toNat (s.regs 1).toNat false = true ∧
    ((s.regs 0).toNat + (s.regs 1).toNat ≤ (s.regs 3).toNat ∨
      (s.regs 3).toNat + (s.regs 1).toNat ≤ (s.regs 0).toNat)

/-- **`runtime.memmove(to, from, n)`** (amd64): returns (`retState64`, no result), memory changed
only at `[to, to + n)`, which then holds the `n` bytes that were at `from`. -/
def MemmoveContract (p : Program) (addr : Nat) : Prop :=
  Summary p addr MemmovePre
    (fun s s' => ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory),
      s' = retState64 s junk [] f x yh m ∧
        MemFrame s.mem m [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] ∧
        readBytes m (s.regs 0).toNat (s.regs 1).toNat =
          readBytes s.mem (s.regs 3).toNat (s.regs 1).toNat)

/-! ### Byte arithmetic the amd64 print code does (`MOVZX` of a count, `LEA` + byte store, `TEST`) -/

theorem zx8_chain (v : Nat) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 v))) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat8_eq_zero_iff (v : Nat) : (BitVec.ofNat 8 v = 0#8) = (v % 256 = 0) := by
  apply propext; constructor
  · intro h; have := congrArg BitVec.toNat h; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

theorem lea_byte (v : Nat) (h : v < 255) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 v)) + 1#64))).toNat % 256 =
      v + 1 := by
  simp [BitVec.toNat_setWidth, BitVec.toNat_add]; omega

/-! ### Branch-free index arithmetic (`SAR $63` masks, signed compares on small values) -/

/-- `(a - c) >>s 63` is all ones when `a < c` (both small): masking `a` with it keeps `a`. -/
theorem sshr_sub_and (a c : Nat) (hac : a < c) (hc : c < 2 ^ 63) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 c).sshiftRight 63).toNat &&& a = a := by
  have h : (BitVec.ofNat 64 a - BitVec.ofNat 64 c).sshiftRight 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_allOnes, hj, decide_true]
    have hmsb : (BitVec.ofNat 64 a - BitVec.ofNat 64 c).msb = true := by
      rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
    by_cases h' : 63 + j < 64
    · simp [h']
      have : j = 0 := by omega
      subst this
      simpa [BitVec.msb_eq_getLsbD_last] using hmsb
    · simp [h', hmsb, hj]
  rw [h, BitVec.toNat_allOnes]
  have ha : a < 2 ^ 64 := by omega
  rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt ha]

/-- `(a - c) >>s 63` is zero when `c ≤ a` (both small). -/
theorem sshr_sub_zero (a c : Nat) (hac : c ≤ a) (ha : a < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c).sshiftRight 63 = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_sshiftRight, hj, decide_true, BitVec.getLsbD_zero]
  have hmsb : (BitVec.ofNat 64 a - BitVec.ofNat 64 c).msb = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  by_cases h' : 63 + j < 64
  · have : j = 0 := by omega
    subst this
    simp only [h', ite_true, Bool.not_true, Bool.false_and, Bool.and_false]
    simpa [BitVec.msb_eq_getLsbD_last] using hmsb
  · simp [h', hmsb]

theorem toNat_sub_small (a b : Nat) (hba : b ≤ a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat = a - b := by
  simp [BitVec.toNat_sub]; omega

theorem toInt_small (x : BitVec 64) (h : x.toNat < 2 ^ 63) : x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]; simp; omega

theorem neg_sub_512 (b : Nat) (hb : b < 512) :
    (0#64 - (BitVec.ofNat 64 b - 512#64)).toNat = 512 - b := by
  simp [BitVec.toNat_sub]; omega

theorem sshr_sub_and_bv (a c : Nat) (hac : a < c) (hc : c < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c).sshiftRight 63 &&& BitVec.ofNat 64 a = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  have ha : (BitVec.ofNat 64 a).toNat = a := by simp; omega
  rw [BitVec.toNat_and, ha, sshr_sub_and a c hac hc]

/-- `x &&& ~511` (as a natural number below `2^64`) rounds `x` down to a multiple of 512. -/
theorem andmask512_nat (x : Nat) (hx : x < 2 ^ 64) : x &&& 18446744073709551104 = x - x % 512 := by
  have h := congrArg BitVec.toNat (mask512 (BitVec.ofNat 64 x))
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx] at h
  rw [show (18446744073709551104 : Nat) % 2 ^ 64 = 18446744073709551104 from rfl] at h
  rw [h]; omega

theorem ofNat_add_sub (b l i : Nat) (h : i ≤ l) (hl : b + l < 2 ^ 64) :
    BitVec.ofNat 64 b + (BitVec.ofNat 64 l - BitVec.ofNat 64 i) = BitVec.ofNat 64 (b + (l - i)) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega

theorem ofNat_add_neg512 (b : Nat) (hb : b < 512) :
    BitVec.ofNat 64 b + (0#64 - (BitVec.ofNat 64 b - 512#64)) = 512#64 := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega

/-! ## Proof helpers (amd64) -/

/-- A state literal `s'` is the return state `retState64 s s'.regs res …` of a call from `s`. -/
theorem eq_retState64 {s s' : State} (res : List W64) (hrip : s'.rip = retAddrOf s)
    (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (h0 : s'.regs 0 = res.getD 0 (s'.regs 0)) (h3 : s'.regs 3 = res.getD 1 (s'.regs 3))
    (h1 : s'.regs 1 = res.getD 2 (s'.regs 1)) (hx : s'.xmm 15 = s.xmm 15)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) (hmx : s'.mxcsr = s.mxcsr) :
    s' = retState64 s s'.regs res s'.flags s'.xmm s'.ymmHi s'.mem :=
  Janus.Contracts.AllocSatAmd64.ret_of s s' res hrip h4 h5 h14 h0 h3 h1 hx hfs hdf hmx

/-- `ret_state64 [h, …]`: `s' = retState64 s ?junk [] ?f ?x ?yh ?m` for a state literal `s'`
(the side conditions by `simp` with the register equations `h, …`). -/
macro "ret_state64" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  exact eq_retState64 [] (by simp [setRegF, retAddrOf, $hs,*]) (by apply BitVec.eq_of_toNat_eq; simp [setRegF, $hs,*]; try omega)
    (by simp [setRegF, $hs,*]) (by simp [setRegF, $hs,*]) rfl rfl rfl (by simp [$hs,*]) (by simp [$hs,*])
    (by simp [$hs,*]) (by simp [$hs,*]))

/-- `ret_state64_res r [h, …]`: as `ret_state64`, with the result `r` in `RAX`. -/
macro "ret_state64_res" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  exact eq_retState64 [_] (by simp [setRegF, retAddrOf, $hs,*]) (by apply BitVec.eq_of_toNat_eq; simp [setRegF, $hs,*]; try omega)
    (by simp [setRegF, $hs,*]) (by simp [setRegF, $hs,*]) (by simp [setRegF, $hs,*]) rfl rfl (by simp [$hs,*])
    (by simp [$hs,*]) (by simp [$hs,*]) (by simp [$hs,*]))

/-- `kobl64`: one obligation of a continuation lemma at a call site (amd64; as `kobl`). -/
macro "kobl64_slow" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | apart_mono
  | (dsimp only; with_reducible assumption)
  | (dsimp only; apply BitVec.eq_of_toNat_eq; simp; omega)
  | omega
  | (dsimp only; janus64_disch)
  | (janus64_simp; first | done | with_reducible assumption | omega))

open Lean Elab Tactic Meta in
elab "kobl64" : tactic => do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let run (stx : TSyntax `tactic) : TacticM Unit := evalTactic stx
  if t.isAppOfArity ``Janus.Apart 4 then
    run (← `(tactic| first | with_reducible assumption | apart_mono | (janus64_simp; first | with_reducible assumption | apart_mono | (unfold Janus.Apart; omega)))); return
  if t.isAppOfArity ``Janus.MemFrame 3 then
    run (← `(tactic| janus_frame)); return
  if let some (ty, lhs, _) := t.eq? then
    let ty ← whnfR ty
    if ty.isAppOfArity ``BitVec 1 then
      run (← `(tactic| first | with_reducible rfl | (dsimp only; with_reducible assumption) | (dsimp only; simp only [Janus.Amd64.Tactic.setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff]; try (first | with_reducible assumption | with_reducible rfl); done) | (dsimp only; simp only [Janus.Amd64.Tactic.setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub]; try omega; done) | (dsimp only; simp only [Janus.Amd64.Tactic.setRegF_apply, callRegs64_apply, reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq; simp; try omega; done) | (apply BitVec.eq_of_toNat_eq; simp; try omega; done))); return
    if lhs.isAppOfArity ``Janus.Arm64.Memory.accessible 4 then
      run (← `(tactic| first | with_reducible assumption | (dsimp only; janus64_disch) | (janus64_simp; first | done | janus64_disch))); return
    if lhs.isAppOfArity ``Janus.Arm64.Memory.readLE 3 then
      run (← `(tactic| first | with_reducible assumption | (dsimp only; with_reducible assumption) | (janus64_simp; first | done | with_reducible assumption | omega))); return
    if ty.isConstOf ``Nat then
      run (← `(tactic| first | with_reducible rfl | omega | (janus64_simp; first | done | omega))); return
  if t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 then
    run (← `(tactic| first | omega | (janus64_simp; first | done | omega))); return
  run (← `(tactic| kobl64_slow))

/-! ## The runtime state `print` and `println` need (amd64) -/

/-- As `Print.PrintReady`, for amd64: `SP = RSP`, `g = R14`, and the TLS slot `[FS - 8]` holds `g`
(`runtime.write` reloads `R14` from it), outside `rt` and the other ranges. -/
def PrintReady (A : PrintGlobals) (rt : List (Nat × Nat)) (below above adj : Nat) (s : State) : Prop :=
  let SP := (s.regs 4).toNat
  let G := (s.regs 14).toNat
  let MP := s.mem.readLE (G + gM) 8
  let TL := s.fsBase.toNat - 8
  -- the stack and the stack-growth checks
  below ≤ SP ∧ SP + above ≤ 2 ^ 48 ∧ s.mem.accessible (SP - below) (below + above) true = true ∧
  SP % 8 = 0 ∧ G + 24 ≤ 2 ^ 48 ∧ s.mem.accessible (G + 16) 8 false = true ∧
  s.mem.readLE (G + 16) 8 + adj < SP ∧
  -- `g`: `g.m`, no `writebuf`; the TLS slot
  0 < G ∧ G + 256 ≤ 2 ^ 48 ∧ s.mem.accessible (G + gM) 8 false = true ∧
  s.mem.accessible (G + gWritebuf) 16 false = true ∧ s.mem.readLE (G + gWritebuf) 8 = 0 ∧
  8 ≤ s.fsBase.toNat ∧ s.fsBase.toNat ≤ 2 ^ 48 ∧ s.mem.accessible TL 8 false = true ∧
  s.mem.readLE TL 8 = G ∧
  -- the M: `locks`, `dying`, the print count (0: outside any print)
  MP + 280 ≤ 2 ^ 48 ∧ s.mem.accessible (MP + mLocks) 16 true = true ∧
  s.mem.readLE (MP + mDying) 4 = 0 ∧ s.mem.readLE (MP + mPrintlock) 1 = 0 ∧
  s.mem.readLE (MP + mLocks) 4 + 4 < 2 ^ 31 ∧
  -- the globals
  s.mem.accessible A.pk 4 false = true ∧ s.mem.accessible A.bi 8 true = true ∧
  s.mem.readLE A.bi 8 < 512 ∧ s.mem.accessible A.bl 512 true = true ∧
  s.mem.accessible A.ow 8 false = true ∧ s.mem.readLE A.ow 8 = 0 ∧
  s.mem.accessible A.dl 8 true = true ∧ ¬ lockHeld s.mem A.dl ∧
  -- what the mutex contracts may write, and what they may not
  InRanges A.dl 8 rt ∧ InRanges (MP + mLocks) 4 rt ∧
  Outside (SP - below) (below + above) rt ∧ Outside (G + 16) 8 rt ∧ Outside (G + gM) 8 rt ∧
  Outside (G + gWritebuf) 16 rt ∧ Outside (MP + mDying) 4 rt ∧ Outside (MP + mPrintlock) 1 rt ∧
  Outside A.pk 4 rt ∧ Outside A.bi 8 rt ∧ Outside A.bl 512 rt ∧ Outside A.ow 8 rt ∧ Outside TL 8 rt ∧
  -- the stack window, `g`'s and the M's fields, the TLS slot and the globals apart
  Sep (SP - below) (below + above) [(G + 16, 8), (G + gM, 8), (G + gWritebuf, 16), (MP + mLocks, 16),
    (A.pk, 4), (A.bi, 8), (A.bl, 512), (A.ow, 8), (A.dl, 8), (TL, 8)] ∧
  Sep (MP + mLocks) 16 [(G + 16, 8), (G + gM, 8), (G + gWritebuf, 16), (A.pk, 4), (A.bi, 8),
    (A.bl, 512), (A.ow, 8), (A.dl, 8), (TL, 8)] ∧
  Sep (G + 16) 8 [(A.bi, 8), (A.bl, 512), (A.dl, 8)] ∧ Sep (G + gM) 8 [(A.bi, 8), (A.bl, 512), (A.dl, 8)] ∧
  Sep (G + gWritebuf) 16 [(A.bi, 8), (A.bl, 512), (A.dl, 8)] ∧ Sep A.dl 8 [(A.bi, 8), (A.bl, 512)] ∧
  Sep TL 8 [(A.bi, 8), (A.bl, 512), (A.dl, 8)]

end Janus.Amd64.Print
