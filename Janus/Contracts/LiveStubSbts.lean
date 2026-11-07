import Janus.Contracts.LiveStubConvT

/-!
# `runtime.slicebytetostring` live, non-empty strings, at a program's own address (arm64)

`RtLiveContract linked addr 4096 (toyR tys ok) (slicebytetostringSpec st) slicebytetostringLive` by a stub that copies the `n`
bytes at `ptr` into a fresh block of the toy bump allocator and returns `(block, n)` (`sbtsSeg addr n A`; the `StrAt` case
`2 ≤ n ∧ (buf = 0 ∨ 32 < n) ∧ InRanges r0 n rt`). The request is pinned by `hok : ∀ args, ok addr args → ∃ ptr, args = [0, ptr, n]`.
`n` must be a size class (`roundupsize n true = n`: 16, 24, 32, 48, …) so that the block `[p, p + n)` the contract adds to the
live set is the block the toy allocator hands out.

**What a stub cannot witness** (the toy runtime `toyR`): `n = 1` (`r0 = st + 8·byte`: the result is the static table, whose
contents are a fact about the binary's data, not of the call; no memory-independent stub meets `StrOut` there) and the
caller's-buffer case (`buf ≠ 0`, `2 ≤ n ≤ 32`: the live set then gets the caller's STACK buffer, which `toyInv` (live objects
are heap blocks below the bump pointer) cannot hold). A witness should use `n = 0` (`janus_live_sbts_empty`) or a size class
`n ≥ 16` with `buf = 0` (`janus_live_sbts`).
-/

namespace Janus.Contracts.LiveStub

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

set_option maxHeartbeats 2000000 in
/-- The return of an **allocating** stub (`BUMP` advanced by `A`, the stores `wsf p` inside the new box
`[p, p + K)`) meets the live contract of `sp`/`ls`. -/
theorem alloc_copy_finish {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {sp : RtSpec} {ls : LiveSpec} {K A : Nat} {wsf : Nat → List Wr}
    {L : List (Nat × Nat)} {b : Nat} {s fin : State}
    (hrw : sp.rtWrites = true) (hwr : sp.writes (argWords s sp.nargs) s.mem = [])
    (hA3 : A % 16 = 0) (hA1 : K ≤ A) (hA2 : A ≤ 64 * K) (hKpos : 0 < K)
    (hcost : ls.cost (argWords s sp.nargs) s.mem = K)
    (hfresh : ∀ r0, ls.fresh (argWords s sp.nargs) s.mem r0 (fin.regs 1).toNat (fin.regs 2).toNat = [(r0, r0 + K)])
    (hkeep : ∀ r0, ls.keep (argWords s sp.nargs) s.mem r0 (fin.regs 1).toNat (fin.regs 2).toNat = [])
    (hws : ∀ p, ∀ w ∈ wsf p, p ≤ w.1 ∧ w.1 + w.2.1 ≤ p + K)
    (hpost : ∀ p, HEAP ≤ p → p + A ≤ HEND →
      (s.mem.writeLE BUMP 8 (p + A)).accessible p K true = true →
      sp.post (toyRt tys) (argWords s sp.nargs) s.mem p (fin.regs 1).toNat (fin.regs 2).toNat
        (applyWrites (s.mem.writeLE BUMP 8 (p + A)) (wsf p)))
    (pre : RtLivePre 4096 (toyR tys ok) sp ls addr L b s)
    (hpc : fin.pc = s.regs 30) (hsp : fin.sp = s.sp) (h18 : fin.regs 18 = s.regs 18)
    (h28 : fin.regs 28 = s.regs 28) (h29 : fin.regs 29 = s.regs 29) (hdz : fin.dczid = s.dczid)
    (htp : fin.tpidr = s.tpidr) (hfc : fin.fpcr = s.fpcr) (hfs : fin.fpsr = s.fpsr)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8))
    (hmem : fin.mem = applyWrites (s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + A)) (wsf (s.mem.readLE BUMP 8))) :
    RtLivePost 4096 (toyR tys ok) sp ls L b s fin := by
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, hcostb, hLs, hWs⟩ := pre
  have hinvT : toyInv tys b L (s.regs 28).toNat (view (toyRt tys) L s.mem) := hinv
  have hcb : K ≤ b := hcost ▸ hcostb
  obtain ⟨p, hpm, hp1, hp2, hend, hfr, hlf, hap, hz, hacc, hinv'⟩ :=
    toy_alloc hty hA3 hA1 hA2 hcb hinvT
  have hp64 : p + A < 2 ^ 64 := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hpn : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hpm] at hmem h0
  have hpost' := hpost p hp1 hend hacc
  generalize hm1 : s.mem.writeLE BUMP 8 (p + A) = m1 at hlf hz hacc hinv' hmem hpost'
  have hbytes : ∀ x, (x < p ∨ p + K ≤ x) → (applyWrites m1 (wsf p)).bytes x = m1.bytes x := fun x hx =>
    bytes_applyWrites_untouched _ (fun w hw => by have := hws p w hw; omega) m1
  have hbump : ∀ x, (x < BUMP ∨ BUMP + 8 ≤ x) → m1.bytes x = s.mem.bytes x := fun x hx =>
    by rw [← hm1]; exact Memory.bytes_writeLE_outside _ (by omega)
  have hpHE : p + K ≤ HEND := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hBH : BUMP + 8 ≤ HEAP := by simp [BUMP, HEAP]
  refine ⟨BitVec.ofNat 64 p, fin.regs 1, fin.regs 2, fin.regs, fin.flags, fin.vregs, fin.mem, fin.excl,
    fin.exclPass, retStateX_eq hpc hsp h18 h28 h29 hdz htp hfc hfs ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rcases i with _ | _ | _ | i
    · simpa using h0
    · rfl
    · rfl
    · omega
  · refine ⟨fun a k hout => ?_, fun a k w => ?_⟩
    · simp only [hrw, rtIf_true, hwr, List.append_nil, outside_append] at hout
      have hHB := outside_toyRt_heap_bump hout.1
      rw [hmem]
      refine Memory.readLE_congr (fun i hi => ?_)
      rw [hbytes (a + i) (by omega), hbump (a + i) (by omega)]
    · rw [hmem, accessible_applyWrites, ← hm1, Memory.accessible_writeLE]
  · rw [hpn]; rw [hmem]; exact hpost'
  · rw [hwr]
    refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨r, hr, r1, r2⟩ := hin
    have hA := hap r hr
    unfold Apart at hA
    rw [hmem, ← hlf.readLE a k ⟨r, hr, r1, r2⟩ trivial]
    refine Memory.readLE_congr (fun i hi => ?_)
    rw [hbytes (a + i) (by omega)]
  · rw [hfresh, hpn]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simpa using hap
  · simp only [liveAdds, hfresh, hkeep, List.append_nil, hpn]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simpa using apart_win (inRanges_heap (tys := tys) hp1 hpHE) hWs
  · simp only [liveAdds, hfresh, hkeep, hcost, List.append_nil, hpn]
    rw [hmem, view_applyWrites (wsf p) (hws p)
      (Or.inl ⟨(p, p + K), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, by omega⟩)]
    exact hinv'


/-- The stub: load the `n` bytes at `X1` into registers, take `A` bytes from the bump allocator, store them at the block,
return `(block, n)`. -/
def sbtsCode (n A : Nat) : List Nat :=
  (chunkList n).mapIdx (fun j c => ldrW c.2 c.1 1 (growReg j)) ++
  [0xd2a00809, 0xf9400120, 0x9100000a + A * 1024, 0xf900012a] ++
  (chunkList n).mapIdx (fun j c => strW c.2 c.1 0 (growReg j)) ++
  [0xd2800001 + n * 32, 0xd65f03c0]

def sbtsSeg (addr n A : Nat) : Segment := ⟨"live-stub.slicebytetostring", addr, sbtsCode n A⟩

/-- The postcondition of `slicebytetostring` for the block `[p, p + n)` holding the copy (ISA independent: `a` is the argument
words, `m0` the memory at the call). -/
theorem sbts_hpost {tys : Tys} {st n ptr p A r1 r2 : Nat} {a : List Nat} {m0 : Memory} (hargs : a = [0, ptr, n]) (hn2 : 2 ≤ n)
    (hr1 : r1 = n) (hp : HEAP ≤ p) (hend : p + A ≤ HEND) (hA : n ≤ A)
    (hacc : (m0.writeLE BUMP 8 (p + A)).accessible p n true = true) :
    (slicebytetostringSpec st).post (toyRt tys) a m0 p r1 r2
      (applyWrites (m0.writeLE BUMP 8 (p + A)) (copyWrites m0 p ptr n)) := by
  rw [hr1]
  simp only [slicebytetostringSpec, hargs, arg, List.getD_cons_succ, List.getD_cons_zero]
  have hcop := copied_copyWrites m0 (m0.writeLE BUMP 8 (p + A)) p ptr n
  have hpE : p + n ≤ HEND := by omega
  have hH : p + n ≤ 2 ^ 48 := by simp only [HEND, HEAP, HSIZE] at hpE hp ⊢; omega
  refine ⟨⟨by simp [strBytes], hH, fun _ => ?_, ?_⟩, Or.inr (Or.inr (Or.inr ⟨hn2, Or.inl rfl, inRanges_heap hp hpE⟩))⟩
  · rw [accessible_applyWrites]; exact acc_false hacc
  · simp only [strBytes]
    exact List.map_congr_left fun i hi => by rw [hcop i (List.mem_range.mp hi)]

end Janus.Contracts.LiveStub

/-- `RtLiveContract linked addr 4096 (toyR [] ok) (slicebytetostringSpec st) slicebytetostringLive` for the stub
`LiveStub.sbtsSeg addr n A`: `n` a size class (`roundupsize n true = n`), `n ≥ 2` and `n ≤ 88`, `A` a multiple of 16 with
`n ≤ A ≤ 64 n`; `hok : ∀ args, ok addr args → ∃ ptr, args = [0, ptr, n]` (no caller buffer). -/
syntax "janus_live_sbts " term:max term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus_live_sbts $n $A $hok) => `(tactic| (
      intro L b s hpc pre
      have pre0 := pre
      have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
      obtain ⟨hc1, hspec, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      obtain ⟨ptr, hargs⟩ := $hok _ hokx
      have hargs3 : argWords s 3 = [0, ptr, $n] := hargs
      have e1 : (s.regs 1).toNat = ptr := by
        have h1 := congrArg (fun l => l.getD 1 0) hargs3
        simpa [argWords, wordsFrom] using h1
      subst e1
      have hrs : Janus.Contracts.roundupsize $n true = $n := by decide
      have hK : Janus.Contracts.slicebytetostringLive.cost (argWords s 3) s.mem = $n := by
        simp only [Janus.Contracts.slicebytetostringLive, hargs3, Janus.Contracts.arg, List.getD_cons_succ, List.getD_cons_zero]
        exact hrs
      have hKb : $n ≤ b := by
        have h := hcostx
        simp only [Janus.Contracts.slicebytetostringLive, Janus.Contracts.slicebytetostringSpec, hargs3, Janus.Contracts.arg,
          List.getD_cons_succ, List.getD_cons_zero, hrs] at h
        exact h
      simp only [Janus.Contracts.slicebytetostringSpec, hargs3, Janus.Contracts.arg, List.getD_cons_succ, List.getD_cons_zero] at hspec
      obtain ⟨-, ⟨hsa, hsb⟩, -⟩ := hspec
      have hread := hsb (by decide)
      have hacB' := Janus.Contracts.LiveSat.bump_acc hinvx
      have hheap := Janus.Contracts.LiveStub.toy_heap_acc (ob := $n) (g := (s.regs 28).toNat) (L' := L) (tys := _) hinvx hKb
      have hbump := Janus.Contracts.LiveStub.toy_heap_bound (ob := $n) (g := (s.regs 28).toNat) (L' := L) (tys := _) hinvx hKb
      open Janus.Contracts.Toy in
        simp only [BUMP, Nat.reducePow] at hheap hacB' hbump
      generalize hgs : Janus.Contracts.slicebytetostringSpec _ = spX at *
      generalize hgl : Janus.Contracts.slicebytetostringLive = lsX at *
      change Janus.Tactic.ReachesRet _ _ s _
      janus_run
      subst hgs hgl
      open Janus.Contracts Janus.Tactic in
        refine Janus.Contracts.LiveStub.alloc_copy_finish (by decide) (K := $n) (A := $A)
          (wsf := fun p => Janus.Contracts.LiveStub.copyWrites s.mem p (s.regs 1).toNat $n) rfl
          (by simp [slicebytetostringSpec, hargs, hargs3, arg, bufWrites]) (by decide) (by decide) (by decide) (by decide)
          hK ?hfr ?hkp ?hws ?hpost pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      case hfr => intro r0; simp [Janus.Contracts.slicebytetostringLive, hargs, Janus.Contracts.arg, Janus.Contracts.range0, Janus.Tactic.setReg]
      case hkp => intro r0; simp [Janus.Contracts.slicebytetostringLive, hargs, Janus.Contracts.arg, Janus.Contracts.range0, Janus.Tactic.setReg]
      case hws => intro p w hw; have := Janus.Contracts.LiveStub.copyWrites_sub s.mem p (s.regs 1).toNat $n w hw; omega
      case hpost => intro p hp hend hacc; exact Janus.Contracts.LiveStub.sbts_hpost hargs3 (by decide) (by simp [Janus.Tactic.setReg]) hp hend (by omega) hacc
      all_goals first | rfl | (simp [Janus.Tactic.setReg, Janus.Contracts.Toy.BUMP]; done)))

namespace Janus.Contracts.LiveStubSbtsSat

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub
open Janus.Contracts.AllocSat (toy A0)

def okCopy : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [0, HEAP, 16]

theorem hokCopy : ∀ args, okCopy A0 args → ∃ ptr, args = [0, ptr, 16] := fun _ h => ⟨HEAP, h.2⟩

def Pc : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }
def linkedCopy : Program := Pc.link [sbtsSeg A0 16 16]

set_option maxHeartbeats 4000000 in
theorem sbtsCopy_impl (st : Nat) : RtLiveContract linkedCopy A0 4096 (toyR tys0 okCopy)
    (slicebytetostringSpec st) slicebytetostringLive := by
  janus_live_sbts 16 16 hokCopy

/-- The copying shape of `slicebytetostring` (a 16-byte string into a fresh block) is satisfiable: an implementation, a runtime and
a call state meeting the precondition, with a cost of 16 bytes. -/
theorem slicebytetostringLive_satisfiable_copy (st : Nat) : ∃ (impl : List Segment) (R : RtInv),
    RtLiveContract (Pc.link impl) A0 4096 R (slicebytetostringSpec st) slicebytetostringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      RtLivePre 4096 R (slicebytetostringSpec st) slicebytetostringLive A0 L b s ∧
      slicebytetostringLive.cost (argWords s (slicebytetostringSpec st).nargs) s.mem = 16 := by
  have ha : argWords (wst [0, HEAP, 16]) 3 = [0, HEAP, 16] := by decide
  have hn : (slicebytetostringSpec st).nargs = 3 := rfl
  refine ⟨[sbtsSeg A0 16 16], toyR tys0 okCopy, sbtsCopy_impl st, [], 0x400, wst [0, HEAP, 16], rfl,
    ⟨wst_wcallOK _ 3 (by omega), ?_, ?_, by trivial, wguard _ 3 (by omega),
      ⟨⟨rfl, ha⟩, wmem_inv 0, ?_, by simp, wwin _ 3 (by omega)⟩⟩, ?_⟩
  · simp only [slicebytetostringSpec, hn, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨Or.inl rfl, ⟨by decide, fun _ => by decide⟩, fun h => absurd rfl h⟩
  · intro x hx
    simp [slicebytetostringSpec, hn, ha, arg] at hx
    subst hx
    simp [calleeStack, wsp_eq, wspn, wsp, HEAP, hn]
    decide
  · simp only [slicebytetostringLive, hn, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    decide
  · simp only [slicebytetostringLive, hn, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    decide

end Janus.Contracts.LiveStubSbtsSat
