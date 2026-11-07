import Janus.Contracts.LiveStubConvTAmd64
import Janus.Contracts.LiveStubSbts

/-!
# `runtime.slicebytetostring` live, non-empty strings, at a program's own address (amd64)

The amd64 twin of `LiveStubSbts.lean` (read it for what is and is not witnessable): the stub copies the `n` bytes at `RBX`
into a fresh block of the toy bump allocator and returns `(block, n)` in `RAX, RBX`; tactic `janus64_live_sbts n A hok`,
`hok : ∀ args, ok addr args → ∃ ptr, args = [0, ptr, n]`.
-/

namespace Janus.Contracts.LiveStubAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy
open Janus.Contracts.LiveStub

set_option maxHeartbeats 2000000 in
/-- The return of an **allocating** stub (`BUMP` advanced by `A`, the stores `wsf p` inside the new box
`[p, p + K)`) meets the live contract of `sp`/`ls`. -/
theorem alloc_copy_finish64 {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr : Nat}
    {sp : RtSpec} {ls : LiveSpec} {K A : Nat} {wsf : Nat → List Wr}
    {L : List (Nat × Nat)} {b : Nat} {s fin : State}
    (hrw : sp.rtWrites = true) (hwr : sp.writes (argWords64 s sp.nargs) s.mem = [])
    (hA3 : A % 16 = 0) (hA1 : K ≤ A) (hA2 : A ≤ 64 * K) (hKpos : 0 < K)
    (hcost : ls.cost (argWords64 s sp.nargs) s.mem = K)
    (hfresh : ∀ r0, ls.fresh (argWords64 s sp.nargs) s.mem r0 (fin.regs 3).toNat (fin.regs 1).toNat = [(r0, r0 + K)])
    (hkeep : ∀ r0, ls.keep (argWords64 s sp.nargs) s.mem r0 (fin.regs 3).toNat (fin.regs 1).toNat = [])
    (hws : ∀ p, ∀ w ∈ wsf p, p ≤ w.1 ∧ w.1 + w.2.1 ≤ p + K)
    (hpost : ∀ p, HEAP ≤ p → p + A ≤ HEND →
      (s.mem.writeLE BUMP 8 (p + A)).accessible p K true = true →
      sp.post (toyRt tys) (argWords64 s sp.nargs) s.mem p (fin.regs 3).toNat (fin.regs 1).toNat
        (applyWrites (s.mem.writeLE BUMP 8 (p + A)) (wsf p)))
    (pre : RtLivePre64 4096 (toyR tys ok) sp ls addr L b s)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64)
    (h5 : fin.regs 5 = s.regs 5) (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15)
    (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr)
    (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8))
    (hmem : fin.mem = applyWrites (s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + A)) (wsf (s.mem.readLE BUMP 8))) :
    RtLivePost64 4096 (toyR tys ok) sp ls L b s fin := by
  obtain ⟨hcall, hspec, hreads, -, hroom, hok, hinv, hcostb, hLs, hWs⟩ := pre
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) := hinv
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
    by rw [← hm1]; exact Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)
  have hpHE : p + K ≤ HEND := by simp only [HEND, HEAP, HSIZE] at hend ⊢; omega
  have hBH : BUMP + 8 ≤ HEAP := by simp [BUMP, HEAP]
  refine ⟨BitVec.ofNat 64 p, fin.regs 3, fin.regs 1, fin.regs, fin.flags, fin.xmm, fin.ymmHi, fin.mem,
    fin.zmmHi, fin.kreg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Janus.Contracts.AllocSatAmd64.ret_of s fin [BitVec.ofNat 64 p, fin.regs 3, fin.regs 1]
      hrip h4 h5 h14 (by simpa using h0) (by simp) (by simp) hx hfs hdf hmx hx87 hfw
  · refine ⟨fun a k hout => ?_, fun a k w => ?_⟩
    · simp only [hrw, rtIf_true, hwr, List.append_nil, outside_append] at hout
      have hHB := outside_toyRt_heap_bump hout.1
      rw [hmem]
      refine Janus.Arm64.Memory.readLE_congr (fun i hi => ?_)
      rw [hbytes (a + i) (by omega), hbump (a + i) (by omega)]
    · rw [hmem, accessible_applyWrites, ← hm1, Janus.Arm64.Memory.accessible_writeLE]
  · rw [hpn]; rw [hmem]; exact hpost'
  · rw [hwr]
    refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨r, hr, r1, r2⟩ := hin
    have hA := hap r hr
    unfold Apart at hA
    rw [hmem, ← hlf.readLE a k ⟨r, hr, r1, r2⟩ trivial]
    refine Janus.Arm64.Memory.readLE_congr (fun i hi => ?_)
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


/-- The stub: load the `n` bytes at `[RBX]` into registers, take `A` bytes from the bump allocator, store them at the block
(`RAX`), return `(block, n)` (`mov ebx, n`). -/
def sbtsCode64 (n A : Nat) : List Nat :=
  ((chunkList n).mapIdx (fun j c => movMem true 3 c.2 c.1 (growReg j))).flatten ++
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x49, 0x8b, 0x01, 0x4c, 0x8d, 0x90] ++ le32 A ++
  [0x4d, 0x89, 0x11] ++
  ((chunkList n).mapIdx (fun j c => movMem false 0 c.2 c.1 (growReg j))).flatten ++
  [0xbb] ++ le32 n ++ [0xc3]

def sbtsSeg64 (addr n A : Nat) : Janus.Amd64.Segment := ⟨"live-stub.slicebytetostring", addr, sbtsCode64 n A⟩

end Janus.Contracts.LiveStubAmd64

syntax "janus64_live_sbts " term:max term:max term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_sbts $n $A $hok) => `(tactic| (
      intro L b s hpc pre
      have pre0 := pre
      have ⟨⟨hra, hal, h3, h4, h5⟩, _⟩ := pre
      obtain ⟨hc1, hspec, hc3, hc4, hc5, hokx, hinvx, hcostx, hLsx, hWsx⟩ := pre0
      obtain ⟨ptr, hargs⟩ := $hok _ hokx
      have hargs3 : argWords64 s 3 = [0, ptr, $n] := hargs
      have e1 : (s.regs 3).toNat = ptr := by
        have h1 := congrArg (fun l => l.getD 1 0) hargs3
        simpa [argWords64, wordsFrom, Janus.Amd64.GoABI.argReg, Janus.Amd64.GoABI.intArgRegs] using h1
      subst e1
      have hrs : Janus.Contracts.roundupsize $n true = $n := by decide
      have hK : Janus.Contracts.slicebytetostringLive.cost (argWords64 s 3) s.mem = $n := by
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
      have hheap := Janus.Contracts.LiveStub.toy_heap_acc (ob := $n) (g := (s.regs 14).toNat) (L' := L) (tys := _) hinvx hKb
      have hbump := Janus.Contracts.LiveStub.toy_heap_bound (ob := $n) (g := (s.regs 14).toNat) (L' := L) (tys := _) hinvx hKb
      have hap := Janus.Contracts.LiveSatAmd64.bump_apart64 hWsx
      have hapH := Janus.Contracts.LiveStubAmd64.toy_heap_apart64 (ob := $n) (g := (s.regs 14).toNat) (L := L) (tys := _)
        hinvx hKb hWsx
      open Janus.Contracts.Toy in
        simp only [BUMP, Nat.reducePow] at hheap hacB' hbump hapH
      generalize hgs : Janus.Contracts.slicebytetostringSpec _ = spX at *
      generalize hgl : Janus.Contracts.slicebytetostringLive = lsX at *
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      subst hgs hgl
      open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy in
        refine Janus.Contracts.LiveStubAmd64.alloc_copy_finish64 (by decide) (K := $n) (A := $A)
          (wsf := fun p => Janus.Contracts.LiveStub.copyWrites s.mem p (s.regs 3).toNat $n) rfl
          (by simp [slicebytetostringSpec, hargs, hargs3, arg, bufWrites]) (by decide) (by decide) (by decide) (by decide)
          hK ?hfr ?hkp ?hws ?hpost pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      case hfr => intro r0; simp [Janus.Contracts.slicebytetostringLive, hargs, Janus.Contracts.arg, Janus.Contracts.range0, Janus.Amd64.Tactic.setRegF]
      case hkp => intro r0; simp [Janus.Contracts.slicebytetostringLive, hargs, Janus.Contracts.arg, Janus.Contracts.range0, Janus.Amd64.Tactic.setRegF]
      case hws => intro p w hw; have := Janus.Contracts.LiveStub.copyWrites_sub s.mem p (s.regs 3).toNat $n w hw; omega
      case hpost => intro p hp hend hacc; exact Janus.Contracts.LiveStub.sbts_hpost hargs3 (by decide) (by simp [Janus.Amd64.Tactic.setRegF]) hp hend (by omega) hacc
      all_goals first | rfl | (simp [Janus.Amd64.Tactic.retAddrOf, Janus.Amd64.Tactic.setRegF, Janus.Contracts.Toy.BUMP]; done) | (simp; done) | ((try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl)))

namespace Janus.Contracts.LiveStubSbtsSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy
  Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64
open Janus.Contracts.AllocSatAmd64 (toy A0)

def okCopy : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [0, HEAP, 16]

theorem hokCopy : ∀ args, okCopy A0 args → ∃ ptr, args = [0, ptr, 16] := fun _ h => ⟨HEAP, h.2⟩

def Pc : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }
def linkedCopy : Janus.Amd64.Program := Pc.link [sbtsSeg64 A0 16 16]

set_option maxHeartbeats 4000000 in
theorem sbtsCopy_impl (st : Nat) : RtLiveContract64 linkedCopy A0 4096 (toyR LiveSat.tys0 okCopy)
    (slicebytetostringSpec st) slicebytetostringLive := by
  janus64_live_sbts 16 16 hokCopy

/-- The copying shape of `slicebytetostring` (a 16-byte string into a fresh block), amd64. -/
theorem slicebytetostringLive64_satisfiable_copy (st : Nat) : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    RtLiveContract64 (Pc.link impl) A0 4096 R (slicebytetostringSpec st) slicebytetostringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      RtLivePre64 4096 R (slicebytetostringSpec st) slicebytetostringLive A0 L b s ∧
      slicebytetostringLive.cost (argWords64 s (slicebytetostringSpec st).nargs) s.mem = 16 := by
  have ha : argWords64 (wst [0, HEAP, 16]) 3 = [0, HEAP, 16] := by
    have a0 : argReg 0 = 0 := rfl
    have a1 : argReg 1 = 3 := rfl
    have a2 : argReg 2 = 1 := rfl
    simp [argWords64, wordsFrom, a0, a1, a2]
    refine ⟨?_, ?_, ?_⟩ <;> decide
  have hn : (slicebytetostringSpec st).nargs = 3 := rfl
  refine ⟨[sbtsSeg64 A0 16 16], toyR LiveSat.tys0 okCopy, sbtsCopy_impl st, [], 0x400, wst [0, HEAP, 16], rfl,
    ⟨wcallOK64 _ 3 (by omega), ?_, ?_, by trivial, wguard64 _ 3 (by omega),
      ⟨⟨rfl, ha⟩, LiveSat.wmem_inv 0, ?_, by simp, wwin64 _ 3 (by omega)⟩⟩, ?_⟩
  · simp only [slicebytetostringSpec, hn, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨Or.inl rfl, ⟨by decide, fun _ => by decide⟩, fun h => absurd rfl h⟩
  · intro x hx
    simp [slicebytetostringSpec, hn, ha, arg] at hx
    subst hx
    simp [calleeStack64, w4, LiveSat.wsp, HEAP, hn]
  · simp only [slicebytetostringLive, hn, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    decide
  · simp only [slicebytetostringLive, hn, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    decide

end Janus.Contracts.LiveStubSbtsSatAmd64

namespace Janus.Contracts.LiveStubAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy

/-- The amd64 twin of `LiveStub.ret_nomem_finish`: a stub that changes only registers meets the live contract of any runtime. -/
theorem ret_nomem_finish64 {R : RtInv} {stack : Nat} {sp : RtSpec} {ls : LiveSpec} {L : List (Nat × Nat)} {b : Nat}
    {s fin : State} (hc : ls.cost (argWords64 s sp.nargs) s.mem = 0)
    (hf : ls.fresh (argWords64 s sp.nargs) s.mem (fin.regs 0).toNat (fin.regs 3).toNat (fin.regs 1).toNat = [])
    (hk : ls.keep (argWords64 s sp.nargs) s.mem (fin.regs 0).toNat (fin.regs 3).toNat (fin.regs 1).toNat = [])
    (hq : sp.post R.rt (argWords64 s sp.nargs) s.mem (fin.regs 0).toNat (fin.regs 3).toNat (fin.regs 1).toNat s.mem)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem))
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64)
    (h5 : fin.regs 5 = s.regs 5) (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15)
    (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr)
    (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw) (hmem : fin.mem = s.mem) :
    RtLivePost64 stack R sp ls L b s fin := by
  refine ⟨fin.regs 0, fin.regs 3, fin.regs 1, fin.regs, fin.flags, fin.xmm, fin.ymmHi, fin.mem, fin.zmmHi, fin.kreg,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Janus.Contracts.AllocSatAmd64.ret_of s fin [fin.regs 0, fin.regs 3, fin.regs 1]
      hrip h4 h5 h14 (by simp) (by simp) (by simp) hx hfs hdf hmx hx87 hfw
  · rw [hmem]; exact MemFrame.refl _ _
  · rw [hmem]; exact hq
  · rw [hmem]; exact LiveFrame.refl _ _ _
  · simp [hf, FreshFrom]
  · simp [liveAdds, hf, hk, LiveApart]
  · simp only [liveAdds, hf, hk, hc, List.append_nil, Nat.sub_zero]; rw [hmem]; exact hinv

end Janus.Contracts.LiveStubAmd64

/-- The amd64 twin of `janus_live_sbts_empty_buf`: the stub `MOV RBX, RCX; RET` (`[0x48, 0x89, 0xcb, 0xc3]`) at the contract address;
the empty string with any buffer (`RAX = buf`): `hok : ∀ args, ok a args → ∃ buf p, args = [buf, p, 0]`. -/
syntax "janus64_live_sbts_empty_buf " term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_sbts_empty_buf $hok) => `(tactic| (
      intro L b s hpc pre
      obtain ⟨⟨hra, hal, h3, h4, h5⟩, hspec, -, -, -, hokx, hinv, -⟩ := pre
      obtain ⟨buf, p, hargs⟩ := $hok _ hokx
      have hargs3 : argWords64 s 3 = [buf, p, 0] := hargs
      have e0 : (s.regs 0).toNat = buf := by
        have h1 := congrArg (fun l => l.getD 0 0) hargs3
        simpa [argWords64, wordsFrom, Janus.Amd64.GoABI.argReg, Janus.Amd64.GoABI.intArgRegs] using h1
      have e2 : (s.regs 1).toNat = 0 := by
        have h1 := congrArg (fun l => l.getD 2 0) hargs3
        simpa [argWords64, wordsFrom, Janus.Amd64.GoABI.argReg, Janus.Amd64.GoABI.intArgRegs] using h1
      simp only [Janus.Contracts.slicebytetostringSpec, hargs3, Janus.Contracts.arg, List.getD_cons_succ, List.getD_cons_zero] at hspec
      obtain ⟨hbuf, -, -⟩ := hspec
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus64_run
      refine Janus.Contracts.LiveStubAmd64.ret_nomem_finish64 ?_ ?_ ?_ ?_ hinv (by simp [Janus.Amd64.Tactic.retAddrOf])
        (by simp [Janus.Amd64.Tactic.setRegF]) (by simp [Janus.Amd64.Tactic.setRegF]) (by simp [Janus.Amd64.Tactic.setRegF])
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) rfl
      · simp [Janus.Contracts.slicebytetostringLive, hargs3, Janus.Contracts.arg, Janus.Contracts.SbtsLiveSat.roundupsize_zero']
      · simp [Janus.Contracts.slicebytetostringLive, hargs3, Janus.Contracts.arg, Janus.Amd64.Tactic.setRegF, e2]
      · simp [Janus.Contracts.slicebytetostringLive, hargs3, Janus.Contracts.arg, Janus.Contracts.range0, Janus.Amd64.Tactic.setRegF, e2]
      · have hb48 : buf ≤ 2 ^ 48 := by
          rcases hbuf with h | ⟨h, -⟩
          · omega
          · omega
        simp only [Janus.Contracts.slicebytetostringSpec, hargs3, Janus.Contracts.arg, List.getD_cons_succ, List.getD_cons_zero,
          Janus.Amd64.Tactic.setRegF]
        simp [Janus.Spec.strBytes, Janus.Contracts.StrOut, Janus.Contracts.StrAt, e0, e2, hb48]))
