import Janus
import Extracted

/-!
# `DeferOrder(p *uint64, x uint64, e any) uint64`: three open-coded defers run in LIFO order (amd64)

`DeferOrder` defers `*p = *p*10+1`, `*p = *p*10+2`, `*p = *p*10+3` (open-coded: `deferBits` bits
0, 1, 2), then returns `x` if `x ≤ 10` and panics with `e` otherwise.

**Guarantee (example 1 of docs/COVERAGE.md R6).** For every panic-runtime model `P` satisfying its
laws and every implementation of `runtime.gopanic` meeting its contract (`Janus.Contracts.PanicAmd64`,
pinned to the Go 1.26 runtime's code), every admissible return address and every call state in which
the runtime is usable with room for a record, `p` points to a writable word outside the runtime's
memory and the stack window, and `e` is not nil: for `x ≤ 10` the call returns `x`, and for `x > 10`
it panics with exactly `e`; either way the three deferred calls ran, last to first, so `*p` ends as
`((*p*10+3)*10+2)*10+1`. The order is the contract's: `gopanic` runs the open-coded defers from the
highest bit of `deferBits` down.
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64
open Janus.Contracts.Panic (frameItems openItems frameKeep bitsWin recItems recItems_above Frame)
open Janus.Spec (openBits)

/-! Code addresses are read off the extraction (`janus_eval%`), never copied: a relinked
binary needs no edit. -/
local macro "loc_DeferOrder_236" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferOrder" + 236))
local macro "loc_DeferOrder_func3_18" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferOrder.func3" + 18))
local macro "loc_DeferOrder_func2_18" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferOrder.func2" + 18))



local macro "func1A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferOrder.func1"))
local macro "func2A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferOrder.func2"))
local macro "func3A" : term => `(janus_eval% (segAddr Extracted.program "example.com/basic.DeferOrder.func3"))

/-- One deferred call: append the decimal digit `k` (mod `2^64`). -/
def digit (k v : Nat) : Nat := (v * 10 + k) % 2 ^ 64

/-- The three deferred calls in LIFO order. -/
def order (v : Nat) : Nat := digit 1 (digit 2 (digit 3 v))

/-- `DeferOrder`'s frame as the panic runtime finds it, for the call state `s`: `SP = RSP - 112` (`RSP`
being the call's entry `RSP`), the `deferBits` byte at `RSP - 89`, the slots from `RSP - 32`. -/
def frame0 (s : State) : Janus.Contracts.Panic.Frame :=
  ⟨(s.regs 4).toNat - 112, (s.regs 4).toNat, Extracted.entry + 0xed,
    some ((s.regs 4).toNat - 89, (s.regs 4).toNat - 32)⟩

/-- The memory the runtime reads again between the deferred calls (`frameKeep`). -/
def keep0 (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 89, (s.regs 4).toNat - 89 + 1), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8),
   ((s.regs 4).toNat - 24, (s.regs 4).toNat - 16), ((s.regs 4).toNat - 32, (s.regs 4).toNat - 24),
   ((s.regs 4).toNat - 80, (s.regs 4).toNat - 72), ((s.regs 4).toNat - 64, (s.regs 4).toNat - 56),
   ((s.regs 4).toNat - 48, (s.regs 4).toNat - 40)]

/-- What the runtime and the deferred calls write during the panic: `P.priv`, the runtime's window
below the frame, the `deferBits` byte and `*p`. -/
def win0 (P : Spec.PanicRuntime) (s : State) (p : BitVec 64) : List (Nat × Nat) :=
  P.priv ++ [((s.regs 4).toNat - 112 - P.depth, (s.regs 4).toNat - 112 - 8),
    ((s.regs 4).toNat - 89, (s.regs 4).toNat - 89 + 1), (p.toNat, p.toNat + 8)]

set_option maxHeartbeats 0 in
/-- The deferred closure `DeferOrder.func1` (a leaf `RET`): `*p = *p*10 + 1`. -/
theorem cl1 (impl : List Janus.Amd64.Segment) (e : State) (p : BitVec 64) (a v : Nat)
    (hpe : e.rip = BitVec.ofNat 64 func1A) (hrdx : e.regs 2 = BitVec.ofNat 64 a) (ha : a + 8 < 2 ^ 64)
    (hcap : e.mem.readLE (a + 8) 8 = p.toNat) (hv : e.mem.readLE p.toNat 8 = v)
    (haa : e.mem.accessible (a + 8) 8 false = true) (hpa : e.mem.accessible p.toNat 8 true = true)
    (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47)
    (hdj : p.toNat + 8 ≤ (e.regs 4).toNat ∨ (e.regs 4).toNat + 8 ≤ p.toNat)
    (hrac : e.mem.accessible (e.regs 4).toNat 8 false = true) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun e' =>
      e'.rip = retAddrOf e ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = e.regs 14 ∧ e'.regs 5 = e.regs 5 ∧
      e'.xmm 15 = e.xmm 15 ∧ e'.df = e.df ∧ MemFrame e.mem e'.mem [(p.toNat, p.toNat + 8)] ∧
      e'.mem.readLE p.toNat 8 = digit 1 v) := by
  have hpn : p.toNat % 2 ^ 64 = p.toNat := Nat.mod_eq_of_lt p.isLt
  have hpa' : e.mem.accessible p.toNat 8 false = true := Janus.Arm64.Memory.accessible_weaken _ hpa
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpe
  have hcr : cr = setRegF cr 2 (BitVec.ofNat 64 a) := by
    funext i; simp only [setRegF]; split
    · subst_vars; exact hrdx
    · rfl
  rw [hcr]
  janus64_run [hcap, hv, hpn]
  refine ⟨MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega), ?_⟩
  simp only [digit]; omega

set_option maxHeartbeats 0 in
/-- The deferred closure `DeferOrder.func2` (a leaf `RET`): `*p = *p*10 + 2`. -/
theorem cl2 (impl : List Janus.Amd64.Segment) (e : State) (p : BitVec 64) (a v : Nat)
    (hpe : e.rip = BitVec.ofNat 64 func2A) (hrdx : e.regs 2 = BitVec.ofNat 64 a) (ha : a + 8 < 2 ^ 64)
    (hcap : e.mem.readLE (a + 8) 8 = p.toNat) (hv : e.mem.readLE p.toNat 8 = v)
    (haa : e.mem.accessible (a + 8) 8 false = true) (hpa : e.mem.accessible p.toNat 8 true = true)
    (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47)
    (hdj : p.toNat + 8 ≤ (e.regs 4).toNat ∨ (e.regs 4).toNat + 8 ≤ p.toNat)
    (hrac : e.mem.accessible (e.regs 4).toNat 8 false = true) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun e' =>
      e'.rip = retAddrOf e ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = e.regs 14 ∧ e'.regs 5 = e.regs 5 ∧
      e'.xmm 15 = e.xmm 15 ∧ e'.df = e.df ∧ MemFrame e.mem e'.mem [(p.toNat, p.toNat + 8)] ∧
      e'.mem.readLE p.toNat 8 = digit 2 v) := by
  have hpn : p.toNat % 2 ^ 64 = p.toNat := Nat.mod_eq_of_lt p.isLt
  have hpa' : e.mem.accessible p.toNat 8 false = true := Janus.Arm64.Memory.accessible_weaken _ hpa
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpe
  have hcr : cr = setRegF cr 2 (BitVec.ofNat 64 a) := by
    funext i; simp only [setRegF]; split
    · subst_vars; exact hrdx
    · rfl
  rw [hcr]
  have hvlt : v < 2 ^ 64 := by
    rw [← hv]; have := Janus.Arm64.Memory.readLE_lt cm p.toNat 8; simpa using this
  janus64_run [hcap, hv, hpn] until [loc_DeferOrder_func2_18]
  generalize hw : (BitVec.ofNat 64 v + BitVec.ofNat 64 v + (BitVec.ofNat 64 v + BitVec.ofNat 64 v) <<< 2 + 2#64) = w
  have hwn : w.toNat = digit 2 v := by
    rw [← hw]
    simp only [digit, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  janus64_run [hcap, hv, hpn, hwn]
  exact MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 0 in
/-- The deferred closure `DeferOrder.func3` (a leaf `RET`): `*p = *p*10 + 3`. -/
theorem cl3 (impl : List Janus.Amd64.Segment) (e : State) (p : BitVec 64) (a v : Nat)
    (hpe : e.rip = BitVec.ofNat 64 func3A) (hrdx : e.regs 2 = BitVec.ofNat 64 a) (ha : a + 8 < 2 ^ 64)
    (hcap : e.mem.readLE (a + 8) 8 = p.toNat) (hv : e.mem.readLE p.toNat 8 = v)
    (haa : e.mem.accessible (a + 8) 8 false = true) (hpa : e.mem.accessible p.toNat 8 true = true)
    (hra : e.mem.readLE (e.regs 4).toNat 8 < 2 ^ 47)
    (hdj : p.toNat + 8 ≤ (e.regs 4).toNat ∨ (e.regs 4).toNat + 8 ≤ p.toNat)
    (hrac : e.mem.accessible (e.regs 4).toNat 8 false = true) :
    ReachesRet (Extracted.program.link impl) (retAddrOf e) e (fun e' =>
      e'.rip = retAddrOf e ∧ e'.regs 4 = e.regs 4 + 8 ∧ e'.regs 14 = e.regs 14 ∧ e'.regs 5 = e.regs 5 ∧
      e'.xmm 15 = e.xmm 15 ∧ e'.df = e.df ∧ MemFrame e.mem e'.mem [(p.toNat, p.toNat + 8)] ∧
      e'.mem.readLE p.toNat 8 = digit 3 v) := by
  have hpn : p.toNat % 2 ^ 64 = p.toNat := Nat.mod_eq_of_lt p.isLt
  have hpa' : e.mem.accessible p.toNat 8 false = true := Janus.Arm64.Memory.accessible_weaken _ hpa
  obtain ⟨cr, crip, cfl, cxm, cm, cyh, cfs, cdf, cmx⟩ := e
  dsimp only at *
  subst hpe
  have hcr : cr = setRegF cr 2 (BitVec.ofNat 64 a) := by
    funext i; simp only [setRegF]; split
    · subst_vars; exact hrdx
    · rfl
  rw [hcr]
  have hvlt : v < 2 ^ 64 := by
    rw [← hv]; have := Janus.Arm64.Memory.readLE_lt cm p.toNat 8; simpa using this
  janus64_run [hcap, hv, hpn] until [loc_DeferOrder_func3_18]
  generalize hw : (BitVec.ofNat 64 v + BitVec.ofNat 64 v + (BitVec.ofNat 64 v + BitVec.ofNat 64 v) <<< 2 + 3#64) = w
  have hwn : w.toNat = digit 3 v := by
    rw [← hw]
    simp only [digit, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  janus64_run [hcap, hv, hpn, hwn]
  exact MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 0 in
theorem correctness (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime) (hl : P.Laws)
    (U : State → Nat → Nat → Prop)
    (hpan : GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs)
    (p x etyp edata : BitVec 64) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [p, x, etyp, edata]
      (fun s => PanicCallerOK P s 120 40 ∧ Buffer s p 8 true ∧
        Spec.Disjoint p.toNat 8 ((s.regs regSP).toNat - (P.depth + 120)) (P.depth + 120 + 40) ∧
        Outside p.toNat 8 P.priv ∧ etyp.toNat ≠ 0 ∧ 0 < P.room s.mem (gOf s) ∧
        ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp)
      (goClassU P U)
      (fun s s' => x.toNat ≤ 10 ∧ (s'.regs 0).toNat = x.toNat ∧
        s'.mem.readLE p.toNat 8 = order (s.mem.readLE p.toNat 8))
      (fun s v s' => 10 < x.toNat ∧ v = ⟨etyp.toNat, edata.toNat⟩ ∧
        s'.mem.readLE p.toNat 8 = order (s.mem.readLE p.toNat 8)) := by
  intro ret hret s hs ⟨hc, ⟨hpb, hps⟩, hdj, hpo, hne, hroom, hds⟩
  have hc' := hc
  obtain ⟨henv, hg, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, Spec.Disjoint] at hgl hgb hnw2 hgr hgd hst hout hd hb hal hds hdj
  by_cases hx : x.toNat ≤ 10
  · refine GoReturns.of_reaches ?_
    janus64_run
    refine ⟨hx, ?_⟩
    simp only [order, digit]
    generalize s.mem.readLE p.toNat 8 = v
    omega
  · have hx' : 10 < x.toNat := by omega
    refine GoReturns.of_reachesRet_exit (tgt := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic"))
      hret.fetch_none ?_
    janus64_run until [Extracted.program.contractAddr "runtime.gopanic"]
    refine ReachesRet.done rfl ?_
    refine GoReturns.name fun S hS => ?_
    have h120 : (s.regs 4 - 120#64).toNat = (s.regs 4).toNat - 120 := by
      rw [BitVec.toNat_sub]; simp; omega
    have hSsp : S.regs 4 = s.regs 4 - 120#64 := by rw [hS] <;> simp [setRegF]
    have hSspn : (S.regs 4).toNat = (s.regs 4).toNat - 120 := by rw [hSsp]; exact h120
    have hSpc : S.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gopanic") := by rw [hS] <;> rfl
    have hS0 : S.regs 0 = etyp := by rw [hS] <;> simp [setRegF]
    have hS3 : S.regs 3 = edata := by rw [hS] <;> simp [setRegF]
    have hS14 : S.regs 14 = s.regs 14 := by rw [hS] <;> simp [setRegF]
    have hSx : S.xmm 15 = 0 := by rw [hS]; exact h_x15
    have hSdf : S.df = false := by rw [hS]
    have hSf : MemFrame s.mem S.mem [((s.regs 4).toNat - (P.depth + 120), (s.regs 4).toNat + 40)] := by
      rw [hS]; janus_frame
    have hSra : S.mem.readLE (S.regs 4).toNat 8 = loc_DeferOrder_236 := by
      rw [hS]; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, h120, Janus.Arm64.Memory.readLE_writeLE_self]
    have hbits : S.mem.readLE ((s.regs 4).toNat - 89) 1 = 7 := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
    have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    have hsl0 : S.mem.readLE ((s.regs 4).toNat - 32) 8 = (s.regs 4).toNat - 48 := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
    have hsl1 : S.mem.readLE ((s.regs 4).toNat - 24) 8 = (s.regs 4).toNat - 64 := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
    have hsl2 : S.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 80 := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have := (s.regs 4).isLt; omega)
    have hfv1 : S.mem.readLE ((s.regs 4).toNat - 48) 8 = func1A := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      try decide
    have hfv2 : S.mem.readLE ((s.regs 4).toNat - 64) 8 = func2A := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      try decide
    have hfv3 : S.mem.readLE ((s.regs 4).toNat - 80) 8 = func3A := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      try decide
    have hcap1 : S.mem.readLE ((s.regs 4).toNat - 40) 8 = p.toNat := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have := p.isLt; omega)
    have hcap2 : S.mem.readLE ((s.regs 4).toNat - 56) 8 = p.toNat := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have := p.isLt; omega)
    have hcap3 : S.mem.readLE ((s.regs 4).toNat - 72) 8 = p.toNat := by
      rw [hS]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by have := p.isLt; omega)
    clear hS
    obtain ⟨fi, hfi⟩ : ∃ fi : Spec.FuncInfo, fi = Spec.FuncInfo.named Extracted.funcs "example.com/basic.DeferOrder" :=
      ⟨_, rfl⟩
    have f_frame : fi.frame = 112 := by rw [hfi]; rfl
    have f_od : fi.openDefer = some (81, 24) := by rw [hfi]; rfl
    have f_res : fi.resume = Extracted.entry + 0xed := by rw [hfi]; rfl
    have hag : Spec.Map.Agrees s.mem S.mem P.priv :=
      Spec.Map.Agrees.of_window hSf (Outside.of_sub hout (by omega) (by omega))
    have hgS : gOf S = gOf s := by simp only [gOf, hS14]
    have hdsS : P.defers S.mem (gOf S) = P.defers s.mem (gOf s) := by
      rw [hgS]; exact hl.defers_frame _ _ _ hag
    have hdsS' : ∀ d ∈ P.defers S.mem (gOf S), (S.regs 4).toNat + 8 < d.sp := by
      intro d hd; rw [hdsS] at hd; have := hds d hd; omega
    have hfsp : fspOf S = (s.regs 4).toNat - 112 := by simp only [fspOf, hSspn]; omega
    have hri : recItems ((s.regs 4).toNat - 112) (P.defers S.mem (gOf S)) = [] :=
      recItems_above (by rw [← hfsp]; exact hdsS')
    have hF : frameOf fi (fspOf S) S.mem = frame0 s := by
      simp only [frameOf, Panic.frameOf, Spec.FuncInfo.bound, Spec.FuncInfo.bitsAt, Spec.FuncInfo.slotsAt,
        Spec.FuncInfo.varp, f_frame, f_od, hfsp, Option.map_some, Option.getD_some, f_res, frame0]
      have e1 : (s.regs 4).toNat - 112 + 112 - 8 - 81 = (s.regs 4).toNat - 89 := by omega
      have e2 : (s.regs 4).toNat - 112 + 112 - 8 - 24 = (s.regs 4).toNat - 32 := by omega
      have e3 : (s.regs 4).toNat - 112 + 112 = (s.regs 4).toNat := by omega
      rw [e1, e2, e3, hbits]; rfl
    have hob : openBits 7 = [2, 1, 0] := by decide
    have hI : frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S)) =
        [{ fn := (s.regs 4).toNat - 80, bits := some 3, chain := P.defers S.mem (gOf S) },
         { fn := (s.regs 4).toNat - 64, bits := some 1, chain := P.defers S.mem (gOf S) },
         { fn := (s.regs 4).toNat - 48, bits := some 0, chain := P.defers S.mem (gOf S) }] := by
      have e1 : (s.regs 4).toNat - 32 + 8 * 2 = (s.regs 4).toNat - 16 := by omega
      have e2 : (s.regs 4).toNat - 32 + 8 * 1 = (s.regs 4).toNat - 24 := by omega
      have e3 : (s.regs 4).toNat - 32 + 8 * 0 = (s.regs 4).toNat - 32 := by omega
      rw [hF]
      unfold frame0
      simp only [frameItems, openItems, hbits, hob, List.map_cons, List.map_nil, hri,
        List.append_nil, e1, e2, e3, hsl0, hsl1, hsl2, Nat.reducePow, Nat.reduceMod]
    have hSfW : MemFrame s.mem S.mem
        (P.priv ++ [((s.regs 4).toNat - (P.depth + 120), (s.regs 4).toNat + 40)]) :=
      hSf.mono fun a n h => by simp only [outside_append] at h; exact h.2
    refine GopanicContract.apply (fi := fi) hpan hSpc (by rw [hSra, hfi]; rfl) ?_ ?_
    · refine ⟨PanicPre.of_within hc hSfW (hl.env_frame _ _ henv hag) (by omega) (by omega)
          (by rw [hSspn]; omega) hS14 hSx hSdf (by rw [hSra]; decide),
        by rw [hS0]; exact hne, ?_, ?_, ?_⟩
      · rw [hgS, hl.room_frame _ _ _ hag]; exact hroom
      · intro _
        have e : fi.bitsAt (fspOf S) = (s.regs 4).toNat - 89 := by
          simp only [Spec.FuncInfo.bitsAt, Spec.FuncInfo.varp, f_frame, f_od, hfsp, Option.map_some,
            Option.getD_some]; omega
        rw [e]
        refine ⟨?_, Outside.of_sub hout (by omega) (by omega)⟩
        rw [hSf.accessible]
        exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
      · rw [hI, hF]
        unfold frame0
        refine ⟨⟨⟨by omega, by rw [hSf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega),
          Outside.of_sub hout (by omega) (by omega), by dsimp only; omega, ?_, ?_⟩, ?_⟩, ?_⟩
        · rw [hbits, hob]
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;>
            refine ⟨by omega, ?_, by omega, by dsimp only; omega, Outside.of_sub hout (by omega) (by omega)⟩ <;>
            rw [hSf.accessible] <;>
            exact Janus.Contracts.IfaceModel.acc_read_of_write
              (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
        · intro it hit
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
          rcases hit with rfl | rfl | rfl <;> dsimp only <;> omega
        · intro it hit
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
          rcases hit with rfl | rfl | rfl <;> dsimp only <;> refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;>
            first
            | (exact Outside.of_sub hout (by omega) (by omega))
            | omega
            | (rw [hSf.accessible]; exact Janus.Contracts.IfaceModel.acc_read_of_write
                (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)))
            | (simp only [hfv1, hfv2, hfv3]; try decide)
        · intro it hit
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
          rcases hit with rfl | rfl | rfl <;> dsimp only <;> simp only [hfv1, hfv2, hfv3] <;> decide
    intro hE
    have hK : frameKeep S.mem (frameOf fi (fspOf S) S.mem)
        (frameItems S.mem (frameOf fi (fspOf S) S.mem) (P.defers S.mem (gOf S))) = keep0 s := by
      have e1 : (s.regs 4).toNat - 32 + 8 * 2 = (s.regs 4).toNat - 16 := by omega
      have e2 : (s.regs 4).toNat - 32 + 8 * 1 = (s.regs 4).toNat - 24 := by omega
      have e3 : (s.regs 4).toNat - 32 + 8 * 0 = (s.regs 4).toNat - 32 := by omega
      have e4 : (s.regs 4).toNat - 16 + 8 = (s.regs 4).toNat - 8 := by omega
      have e5 : (s.regs 4).toNat - 24 + 8 = (s.regs 4).toNat - 16 := by omega
      have e6 : (s.regs 4).toNat - 32 + 8 = (s.regs 4).toNat - 24 := by omega
      have e7 : (s.regs 4).toNat - 80 + 8 = (s.regs 4).toNat - 72 := by omega
      have e8 : (s.regs 4).toNat - 64 + 8 = (s.regs 4).toNat - 56 := by omega
      have e9 : (s.regs 4).toNat - 48 + 8 = (s.regs 4).toNat - 40 := by omega
      rw [hI, hF]
      unfold frame0 keep0
      simp only [frameKeep, hbits, hob, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        e1, e2, e3, e4, e5, e6, e7, e8, e9]
    rw [hK, hI, hF] at hE
    unfold frame0 at hE
    have hpa0 : S.mem.accessible p.toNat 8 true = true := by rw [hSf.accessible]; exact hps
    have hv0 : S.mem.readLE p.toNat 8 = s.mem.readLE p.toNat 8 := hSf.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)
    have hsubR : ∀ a n, Outside a n (win0 P s p) →
        Outside a n (P.priv ++ rtWin P (frame0 s) ++ bitsWin (frame0 s)) := by
      intro a n h
      unfold win0 frame0 at *
      simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨⟨h.1, h.2.1⟩, h.2.2.1⟩
    have hsubP : ∀ a n, Outside a n (win0 P s p) → Outside a n [(p.toNat, p.toNat + 8)] := by
      intro a n h
      unfold win0 at h
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact h.2.2.2
    have hacc0 : MemFrame S.mem S.mem (win0 P s p) := MemFrame.refl _ _
    -- the deferred call 1 (bit 2): `*p = *p*10 + 3`
    rw [Engine_cons] at hE
    obtain ⟨k1, e1, hst1, ⟨hpc1, h2_1, h14_1, hx1, hdf1, hal1, hlo1, hhi1, hra1, henv1⟩,
      hfr1, -, -, hpn1, -, -, hcont1, -⟩ := hE
    dsimp only at hpc1 h2_1 hlo1 hhi1 hra1 hfr1 hcont1
    refine GoReturns.of_steps (hst1.withExit hret.fetch_none) ?_
    have hae1 : MemFrame S.mem e1.mem (win0 P s p) := hacc0.trans hfr1 fun a n h => ⟨h, hsubR a n h⟩
    have hm1 : e1.mem.readLE ((s.regs 4).toNat - 80) 8 = func3A := by
      rw [hae1.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hfv3
    have hc1 : e1.mem.readLE ((s.regs 4).toNat - 80 + 8) 8 = p.toNat := by
      rw [show (s.regs 4).toNat - 80 + 8 = (s.regs 4).toNat - 72 by omega]
      rw [hae1.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hcap3
    have hv1 : e1.mem.readLE p.toNat 8 = s.mem.readLE p.toNat 8 := by
      rw [hfr1.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hpo, by omega⟩, by omega⟩)]; exact hv0
    rw [hm1] at hpc1
    have hpa1 : e1.mem.accessible p.toNat 8 true = true := by
      rw [hae1.accessible]; exact hpa0
    have haa1 : e1.mem.accessible ((s.regs 4).toNat - 80 + 8) 8 false = true := by
      rw [hae1.accessible, hSf.accessible]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    have hrac1 : e1.mem.accessible (e1.regs 4).toNat 8 false = true := by
      rw [hae1.accessible, hSf.accessible]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    have hcl1 := cl3 impl e1 p ((s.regs 4).toNat - 80) (s.mem.readLE p.toNat 8) hpc1 (by rw [h2_1]) (by omega)
      hc1 hv1 haa1 hpa1 hra1 (by omega) hrac1
    obtain ⟨j1, f1, hj1, -, hfpc1, hfsp1, hf141, hf51, hfx1, hfdf1, hff1, hpv1⟩ := hcl1
    refine GoReturns.of_steps (hj1.withExit hret.fetch_none) ?_
    have hacc1 : MemFrame S.mem f1.mem (win0 P s p) := hae1.trans hff1 fun a n h => ⟨h, hsubP a n h⟩
    obtain ⟨hdr1, hpf1⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 112) (keep := keep0 s) hl
      (by rw [hfpc1, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
      hfsp1 (hf141.trans h14_1) hf51 (by rw [hfx1]; exact hx1) (by rw [hfdf1]; exact hdf1)
      henv1 hff1 (by
        unfold keep0; simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpo, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    have hE1 := (hcont1 f1 hdr1).1 (hpf1.trans hpn1)
    -- the deferred call 2 (bit 1): `*p = *p*10 + 2`
    rw [Engine_cons] at hE1
    obtain ⟨k2, e2, hst2, ⟨hpc2, h2_2, h14_2, hx2, hdf2, hal2, hlo2, hhi2, hra2, henv2⟩,
      hfr2, -, -, hpn2, -, -, hcont2, -⟩ := hE1
    dsimp only at hpc2 h2_2 hlo2 hhi2 hra2 hfr2 hcont2
    refine GoReturns.of_steps (hst2.withExit hret.fetch_none) ?_
    have hae2 : MemFrame S.mem e2.mem (win0 P s p) := hacc1.trans hfr2 fun a n h => ⟨h, hsubR a n h⟩
    have hm2 : e2.mem.readLE ((s.regs 4).toNat - 64) 8 = func2A := by
      rw [hae2.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hfv2
    have hc2 : e2.mem.readLE ((s.regs 4).toNat - 64 + 8) 8 = p.toNat := by
      rw [show (s.regs 4).toNat - 64 + 8 = (s.regs 4).toNat - 56 by omega]
      rw [hae2.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hcap2
    have hv2 : e2.mem.readLE p.toNat 8 = digit 3 (s.mem.readLE p.toNat 8) := by
      rw [hfr2.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hpo, by omega⟩, by omega⟩)]; exact hpv1
    rw [hm2] at hpc2
    have hpa2 : e2.mem.accessible p.toNat 8 true = true := by
      rw [hae2.accessible]; exact hpa0
    have haa2 : e2.mem.accessible ((s.regs 4).toNat - 64 + 8) 8 false = true := by
      rw [hae2.accessible, hSf.accessible]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    have hrac2 : e2.mem.accessible (e2.regs 4).toNat 8 false = true := by
      rw [hae2.accessible, hSf.accessible]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    have hcl2 := cl2 impl e2 p ((s.regs 4).toNat - 64) (digit 3 (s.mem.readLE p.toNat 8)) hpc2 (by rw [h2_2]) (by omega)
      hc2 hv2 haa2 hpa2 hra2 (by omega) hrac2
    obtain ⟨j2, f2, hj2, -, hfpc2, hfsp2, hf142, hf52, hfx2, hfdf2, hff2, hpv2⟩ := hcl2
    refine GoReturns.of_steps (hj2.withExit hret.fetch_none) ?_
    have hacc2 : MemFrame S.mem f2.mem (win0 P s p) := hae2.trans hff2 fun a n h => ⟨h, hsubP a n h⟩
    obtain ⟨hdr2, hpf2⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 112) (keep := keep0 s) hl
      (by rw [hfpc2, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
      hfsp2 (hf142.trans h14_2) hf52 (by rw [hfx2]; exact hx2) (by rw [hfdf2]; exact hdf2)
      henv2 hff2 (by
        unfold keep0; simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpo, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    have hE2 := (hcont2 f2 hdr2).1 (hpf2.trans hpn2)
    -- the deferred call 3 (bit 0): `*p = *p*10 + 1`
    rw [Engine_cons] at hE2
    obtain ⟨k3, e3, hst3, ⟨hpc3, h2_3, h14_3, hx3, hdf3, hal3, hlo3, hhi3, hra3, henv3⟩,
      hfr3, -, -, hpn3, -, -, hcont3, -⟩ := hE2
    dsimp only at hpc3 h2_3 hlo3 hhi3 hra3 hfr3 hcont3
    refine GoReturns.of_steps (hst3.withExit hret.fetch_none) ?_
    have hae3 : MemFrame S.mem e3.mem (win0 P s p) := hacc2.trans hfr3 fun a n h => ⟨h, hsubR a n h⟩
    have hm3 : e3.mem.readLE ((s.regs 4).toNat - 48) 8 = func1A := by
      rw [hae3.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hfv1
    have hc3 : e3.mem.readLE ((s.regs 4).toNat - 48 + 8) 8 = p.toNat := by
      rw [show (s.regs 4).toNat - 48 + 8 = (s.regs 4).toNat - 40 by omega]
      rw [hae3.readLE _ _ (by unfold win0; simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]; exact hcap1
    have hv3 : e3.mem.readLE p.toNat 8 = digit 2 (digit 3 (s.mem.readLE p.toNat 8)) := by
      rw [hfr3.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hpo, by omega⟩, by omega⟩)]; exact hpv2
    rw [hm3] at hpc3
    have hpa3 : e3.mem.accessible p.toNat 8 true = true := by
      rw [hae3.accessible]; exact hpa0
    have haa3 : e3.mem.accessible ((s.regs 4).toNat - 48 + 8) 8 false = true := by
      rw [hae3.accessible, hSf.accessible]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    have hrac3 : e3.mem.accessible (e3.regs 4).toNat 8 false = true := by
      rw [hae3.accessible, hSf.accessible]
      exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega))
    have hcl3 := cl1 impl e3 p ((s.regs 4).toNat - 48) (digit 2 (digit 3 (s.mem.readLE p.toNat 8))) hpc3 (by rw [h2_3]) (by omega)
      hc3 hv3 haa3 hpa3 hra3 (by omega) hrac3
    obtain ⟨j3, f3, hj3, -, hfpc3, hfsp3, hf143, hf53, hfx3, hfdf3, hff3, hpv3⟩ := hcl3
    refine GoReturns.of_steps (hj3.withExit hret.fetch_none) ?_
    have hacc3 : MemFrame S.mem f3.mem (win0 P s p) := hae3.trans hff3 fun a n h => ⟨h, hsubP a n h⟩
    obtain ⟨hdr3, hpf3⟩ := DeferReturned.of_window (fsp := (s.regs 4).toNat - 112) (keep := keep0 s) hl
      (by rw [hfpc3, retAddrOf, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
      hfsp3 (hf143.trans h14_3) hf53 (by rw [hfx3]; exact hx3) (by rw [hfdf3]; exact hdf3)
      henv3 hff3 (by
        unfold keep0; simp only [Nat.add_sub_cancel_left, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hpo, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)
    have hE3 := (hcont3 f3 hdr3).1 (hpf3.trans hpn3)
    rw [Engine_nil] at hE3
    obtain ⟨k4, d, hst4, hU, hpd, -, hfrd, -, -, -⟩ := hE3
    refine GoReturns.leave (v := ⟨etyp.toNat, edata.toNat⟩) (hst4.withExit hret.fetch_none) ?_ ?_
    · have hg' : gOf s = (S.regs 14).toNat := by simp only [gOf, hS14]
      have hU' := hU; rw [← hg'] at hU'
      have hpd' := hpd; rw [show (S.regs 14).toNat = gOf s from hg'.symm] at hpd'
      refine ⟨hU', _, _, hpd', ?_, rfl⟩
      simp only [hS0, hS3]
    · refine ⟨hx', rfl, ?_⟩
      rw [hfrd.readLE _ _ (by
        simp only [rtWin, bitsWin, outside_append, outside_cons, outside_nil, and_true]
        exact ⟨⟨hpo, by omega⟩, by omega⟩), hpv3]
      rfl

/-! ## Non-vacuity

The theorem's hypotheses hold together: the model engine of `Janus.Contracts.PanicSatAmd64` (code that
`PanicSatAmd64Run` proves meets the `gopanic` contract in every program that contains it), linked into
`DeferOrder`'s program with a `jmp` to it at the `runtime.gopanic` address, and a call state — an `any`
of type word `1`, `x = 11` — in the precondition; the call panics. -/

namespace Witness

open Janus.Contracts.PanicSat (tabWords witMem witRet witArg)
open Janus.Contracts.PanicSatAmd64
open Janus.Contracts.PanicModel

abbrev T0 : List Spec.FuncInfo := Extracted.funcs

/-- The panic runtime: the model, with the funcs table of this binary. -/
abbrev PW : Spec.PanicRuntime := P0 T0 RPa

def gA : Nat := Extracted.program.contractAddr "runtime.gopanic"

/-- The code linked next to `DeferOrder`: the model engine and a `jmp` to it at `runtime.gopanic`. -/
def implW : List Janus.Amd64.Segment := panicImpl Extracted.program [("runtime.gopanic", eGopanic)]

theorem tok : TOK T0 := by
  unfold TOK T0 Extracted.funcs
  decide

set_option maxRecDepth 100000 in
theorem engineAt : EngineAt (Extracted.program.link implW) :=
  EngineAt.of_link (rest := _) (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem stubAt : StubAt (Extracted.program.link implW) gA eGopanic :=
  StubAt.of_jmp (bs := stubCode gA eGopanic) (rel := (eGopanic + 2 ^ 64 - (gA + 5)) % 2 ^ 64) (len := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem hpan : GopanicContract (Extracted.program.link implW) gA PW U1 T0 :=
  gopanic_at stubAt (gopanic_run engineAt T0 tok)

abbrev pA : Nat := witArg
abbrev ret : Nat := witRet

/-- Memory: the model's table and runtime range writable, a stack (a region of the witness memory) holding the
return address `ret` at `[wsp]` (and `*pA`), the goroutine readable. -/
def wmW : Janus.Arm64.Memory := witMem (tabWords T0 ++ [(wsp, ret)])

theorem env_w : Env0 T0 wmW := by
  unfold Env0
  have hnd : ndef wmW = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem hret : RetAddr (Extracted.program.link implW) ret := RetAddr.of_check (by decide)

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg
      else if i = 0 then BitVec.ofNat 64 pA else if i = 3 then 11#64 else if i = 1 then 1#64 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmW }

theorem setup : CallSetup ((Extracted.program.link implW).withExit ret) Extracted.entry
    [BitVec.ofNat 64 pA, 11#64, 1#64, 0#64] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, fun i h => ?_, rfl⟩
  simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem pre : PanicCallerOK PW s0 120 40 ∧ Buffer s0 (BitVec.ofNat 64 pA) 8 true ∧
    Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 ((s0.regs regSP).toNat - (PW.depth + 120)) (PW.depth + 120 + 40) ∧
    Outside (BitVec.ofNat 64 pA).toNat 8 PW.priv ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧
    0 < PW.room s0.mem (gOf s0) ∧ ∀ d ∈ PW.defers s0.mem (gOf s0), (s0.regs regSP).toNat ≤ d.sp := by
  refine ⟨⟨env_w, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩,
    ⟨by decide, by decide⟩, ?_, ?_, by decide, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · unfold Spec.Disjoint; decide
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · show 0 < room0 wmW
    rw [room0_eq]; decide
  · intro d hd
    have hnd : ndef wmW = 0 := by decide
    have : defers0 wmW = [] := by rw [defers0_eq, hnd]; rfl
    exact absurd hd (by rw [show PW.defers s0.mem (gOf s0) = defers0 wmW from rfl, this]; simp)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (P : Spec.PanicRuntime)
    (U : Janus.Amd64.State → Nat → Nat → Prop) (ret : Nat) (s : Janus.Amd64.State), P.Laws ∧
    GopanicContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gopanic") P U Extracted.funcs ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry
      [BitVec.ofNat 64 pA, 11#64, 1#64, 0#64] s ∧
    (PanicCallerOK P s 120 40 ∧ Buffer s (BitVec.ofNat 64 pA) 8 true ∧
      Spec.Disjoint (BitVec.ofNat 64 pA).toNat 8 ((s.regs regSP).toNat - (P.depth + 120)) (P.depth + 120 + 40) ∧
      Outside (BitVec.ofNat 64 pA).toNat 8 P.priv ∧ (1#64 : BitVec 64).toNat ≠ 0 ∧
      0 < P.room s.mem (gOf s) ∧ ∀ d ∈ P.defers s.mem (gOf s), (s.regs regSP).toNat ≤ d.sp) :=
  ⟨implW, PW, U1, ret, s0, P0_laws T0 RPa, hpan, hret, setup, pre⟩

/-- So the guarantee is reached: with `x = 11` `DeferOrder` panics with `e`, after the three deferred
calls ran in LIFO order. -/
theorem returns : GoReturns ((Extracted.program.link implW).withExit ret) (goClassU PW U1 s0) s0 fun o =>
    match o with
    | .returned s' => ABIReturn s0 s' ∧ ((11#64 : BitVec 64).toNat ≤ 10 ∧ (s'.regs 0).toNat = (11#64 : BitVec 64).toNat ∧
        s'.mem.readLE (BitVec.ofNat 64 pA).toNat 8 = order (s0.mem.readLE (BitVec.ofNat 64 pA).toNat 8))
    | .panicked v s' => 10 < (11#64 : BitVec 64).toNat ∧ v = ⟨(1#64 : BitVec 64).toNat, (0#64 : BitVec 64).toNat⟩ ∧
        s'.mem.readLE (BitVec.ofNat 64 pA).toNat 8 = order (s0.mem.readLE (BitVec.ofNat 64 pA).toNat 8)
    | .goexited _ => False :=
  correctness implW PW (P0_laws T0 RPa) U1 hpan (BitVec.ofNat 64 pA) 11#64 1#64 0#64 ret hret s0 setup pre

end Witness

end Proof
