import Janus.Contracts.ErrorfAmd64
import Janus.Contracts.ErrorfSat
import Janus.Contracts.PoolSatAmd64

/-!
# The `fmt.errorf` live contract is satisfiable (amd64)

The amd64 counterpart of `Janus.Contracts.ErrorfSat`: the same instance (the format `%w` alone and
the message bound `B = 0`), x86-64 code for the stub, a proof that it satisfies `ErrorfLive` of
`Janus.Contracts.ErrorfAmd64` for the toy runtime, and a call state satisfying the precondition.
-/

namespace Janus.Contracts.ErrorfSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts
  Janus.Contracts.Errorf Janus.Contracts.ErrorfAmd64 Janus.Contracts.Toy Janus.Contracts.LiveSat
  Janus.Contracts.LiveSatAmd64
open Janus.Contracts.ErrorfSat (tErr iErr tInt iWrap wr4 wr4_frame wr4_live wr4_view wr4_acc wr4_r0 wr4_r1 wr4_r2 wr4_r3
  eFP eSP eE eTxt ewmem ewframe ewargs ewinv ewcost okE)
open Janus.Contracts.PoolSatAmd64 (KeepsABI pool_ret)
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0 withCode)

/-- `mov r9d, BUMP; mov r11, [rcx+8]; mov rbx, [r9]; lea r10, [rbx+32]; mov [r9], r10;
mov qword [rbx], 0; mov qword [rbx+8], 0; mov qword [rbx+16], iErr; mov [rbx+24], r11;
mov eax, iWrap; ret`. -/
def code : List Nat :=
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x4c, 0x8b, 0x59, 0x08, 0x49, 0x8b, 0x19, 0x4c, 0x8d, 0x53, 0x20,
   0x4d, 0x89, 0x11, 0x48, 0xc7, 0x03, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00,
   0x48, 0xc7, 0x43, 0x10, 0x22, 0x22, 0x00, 0x00, 0x4c, 0x89, 0x5b, 0x18, 0xb8, 0x44, 0x44, 0x00, 0x00, 0xc3]

/-- The state `code` returns in. -/
def errFinal (s : State) : State :=
  { s with
    regs :=
      setRegF
        (setRegF
          (setRegF
            (setRegF (setRegF (setRegF s.regs 0 17476#64) 3 (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem 4194304 8))) 4
              (s.regs 4 + 8#64))
            9 4194304#64)
          10 (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem 4194304 8) + 32#64))
        11 (BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8)),
    rip := BitVec.ofNat 64 (Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 4)) 8),
    mem :=
      ((((Janus.Arm64.Memory.writeLE s.mem 4194304 8 (Janus.Arm64.Memory.readLE s.mem 4194304 8 + 32)).writeLE
                    (Janus.Arm64.Memory.readLE s.mem 4194304 8) 8 0).writeLE
                (Janus.Arm64.Memory.readLE s.mem 4194304 8 + 8) 8 0).writeLE
            (Janus.Arm64.Memory.readLE s.mem 4194304 8 + 16) 8 8738).writeLE
        (Janus.Arm64.Memory.readLE s.mem 4194304 8 + 24) 8
        (Janus.Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8) }

set_option maxRecDepth 20000 in
theorem code_run (s : State) (hpc : s.rip = BitVec.ofNat 64 A0) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (h48 : (s.regs 4).toNat + 8 ≤ 2 ^ 48) (hrs : s.mem.accessible (s.regs 4).toNat 8 false = true)
    (hacB : s.mem.accessible BUMP 8 true = true)
    (hH : s.mem.accessible HEAP HSIZE true = true) (hp1 : 268435456 ≤ s.mem.readLE 4194304 8)
    (hp2 : s.mem.readLE 4194304 8 + 32 ≤ 536870912)
    (hS : s.mem.accessible ((s.regs 1).toNat + 8) 8 false = true) (hS2 : (s.regs 1).toNat + 16 ≤ 2 ^ 48)
    (hR1 : (s.regs 4).toNat + 8 ≤ 4194304 ∨ 4194312 ≤ (s.regs 4).toNat)
    (hR2 : (s.regs 4).toNat + 8 ≤ 268435456 ∨ 536870912 ≤ (s.regs 4).toNat) :
    ReachesRet (withCode code) (retAddrOf s) s (fun s' => s' = errFinal s) := by
  janus64_run
  rfl

theorem errFinal_keeps (s : State) : KeepsABI s (errFinal s) := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [errFinal, retAddrOf]
  · simp [errFinal, setRegF]
  · simp [errFinal, setRegF]
  · simp [errFinal, setRegF]

set_option maxRecDepth 20000 in
theorem errorf_impl (ok : Nat → List Nat → Prop) :
    ErrorfLive (toy.link (at0 code)) A0 4096 (toyR tys0 ok) tErr iErr tInt iWrap 0 := by
  rw [link_at0]
  intro L b s hpc ⟨⟨hra, hal, hst, h8, hacc⟩, hguard, hargs, hreads, hok, hinv, hcost, hLs, hWs⟩
  obtain ⟨hsome, hsl, hsc, hF, hSl, hT0, hD0, hE, hTxt, hints, hlen, hB⟩ := hargs
  have hlen0 : (msgOf s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat).length = 0 := by omega
  have hcost32 : errorfCost s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat = 32 := by
    simp [errorfCost, hlen0, wrapBytes]
  rw [hcost32] at hcost
  have hinvT : toyInv tys0 b L (s.regs 14).toNat (view (toyRt tys0) L s.mem) := hinv
  obtain ⟨p, hpm, h1, h2, hendA, hfr, hlf, hap, hz, hacc', hinv'⟩ :=
    toy_alloc tysOK0 (A := 32) (K := 32) (by omega) (by omega) (by omega) hcost hinvT
  have hacB := bump_acc hinv
  have hH : s.mem.accessible HEAP HSIZE true = true := by
    obtain ⟨p', -, -, -, -, -, -, hac, -, -, -⟩ := hinvT
    rw [view_accessible] at hac; exact hac
  have hS : s.mem.accessible ((s.regs 1).toNat + 8) 8 false = true := by
    have h16 : 0 < 16 * (1 + nDec (segsOf s.mem (s.regs 0).toNat (s.regs 3).toNat)) := by omega
    rw [hsl] at hSl
    exact Janus.Arm64.Memory.accessible_mono _ (hSl.2 h16) (by omega) (by omega)
  have hS2 : (s.regs 1).toNat + 16 ≤ 2 ^ 48 := by
    rw [hsl] at hSl
    have := hSl.1
    omega
  have hrs : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega)
  have hpm' : s.mem.readLE 4194304 8 = p := hpm
  have hro : Outside (s.regs 4).toNat 8 (toyRt tys0) := by
    have h : Outside (s.regs 4).toNat ((s.regs 4).toNat + 8 - (s.regs 4).toNat) (toyRt tys0) :=
      hWs ((s.regs 4).toNat, (s.regs 4).toNat + 8) (by simp [liveWin64])
    rwa [Nat.add_sub_cancel_left] at h
  simp only [toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, HEAP, HEND, HSIZE, BUMP, WBUF,
    tyA, tyB, tyC, Nat.add_sub_cancel_left] at hro
  have hrun := code_run s hpc hra (by omega) hrs hacB hH (by simp only [HEAP] at h1; omega)
    (by simp only [HEND, HEAP, HSIZE] at hendA; omega) hS hS2 (by omega) (by omega)
  obtain ⟨k, s', hst', hpc', rfl⟩ := hrun
  refine ⟨k, errFinal s, hst', hpc', ?_⟩
  have hLp : ∀ r ∈ L, HEAP ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ p := by
    obtain ⟨p', hp', -, -, -, hL, -⟩ := hinvT
    have hp'p : p' = p := by
      rw [← hp', readLE_view (inRanges_bump tys0) (outside_live hL (by simp only [BUMP, HEAP]; omega))]; exact hpm
    intro r hr
    have := hL r hr
    omega
  have hmem : (errFinal s).mem = wr4 (s.mem.writeLE BUMP 8 (p + 32)) p 0 0 iErr
      (s.mem.readLE ((s.regs 1).toNat + 8) 8) := by
    simp only [errFinal, wr4, hpm']; rfl
  have hout : ∀ a, p ≤ a → Outside a 8 L := fun a ha => outside_live_above hLp ha
  have hobj : InRanges p 32 (L ++ [(p, p + 32)]) := ⟨(p, p + 32), by simp, Nat.le_refl _, Nat.le_refl _⟩
  have hrt : InRanges p 32 (toyRt tys0) := inRanges_heap h1 hendA
  unfold PoolAmd64.LiveRet
  refine ⟨(errFinal s).regs, (errFinal s).xmm, (errFinal s).ymmHi, (errFinal s).flags, (errFinal s).mem,
    (errFinal s).zmmHi, (errFinal s).kreg, pool_ret s _ (errFinal_keeps s), ?_, ?_, ?_⟩
  · rw [hmem]
    refine (hfr.trans (wr4_frame _ hrt _ _ _ _) (fun a n h => ⟨h, h⟩)).mono ?_
    intro a n h; simp only [outside_append] at h; exact h.1
  · rw [hmem]; exact (hlf.trans (wr4_live (LiveFrame.refl _ _ _) hout _ _ _ _) (fun _ _ h => h))
  · have hmsg : msgOf s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat = [] := List.length_eq_zero_iff.mp hlen0
    have hp64 : p < 2 ^ 64 := by simp only [HEND, HEAP, HSIZE] at hendA; omega
    have hr0 : ((errFinal s).regs 0).toNat = iWrap := by simp [errFinal, setRegF, iWrap]
    have hr1 : ((errFinal s).regs 3).toNat = p := by
      simp only [errFinal, setRegF]
      simp [hpm', Nat.mod_eq_of_lt hp64]
    have hAp : ∀ r ∈ liveWin64 s 4096 5, p + 32 ≤ r.1 ∨ r.2 ≤ p := by
      intro r hr
      have := (apart_win hrt hWs) r hr
      unfold Apart at this; omega
    show ErrorfPost (Env.mk tErr iErr tInt iWrap) (toyR tys0 ok) s.mem (s.regs 0).toNat (s.regs 3).toNat
      (s.regs 1).toNat (liveWin64 s 4096 5) L b (s.regs 14).toNat ((errFinal s).regs 0).toNat
      ((errFinal s).regs 3).toNat (errFinal s).mem
    rw [hr0, hr1, hmem]
    unfold ErrorfPost
    have hwb : wrapBytes = 32 := rfl
    simp only [hwb, wrapErrOffset]
    refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [HEND, HEAP, HSIZE] at hendA ⊢; omega
    · rw [wr4_acc]; exact hacc'
    · rw [wr4_r1, hlen0]
    · rw [hlen0, hmsg]; rfl
    · rw [hlen0]; refine ⟨?_, fun h => absurd h (by omega)⟩
      rw [wr4_r0]; simp
    · show (wr4 (s.mem.writeLE BUMP 8 (p + 32)) p 0 0 iErr (s.mem.readLE ((s.regs 1).toNat + 8) 8)).readLE (p + 16) 8 = iErr
      rw [wr4_r2]; decide
    · show (wr4 (s.mem.writeLE BUMP 8 (p + 32)) p 0 0 iErr (s.mem.readLE ((s.regs 1).toNat + 8) 8)).readLE (p + 24) 8 = _
      rw [wr4_r3, Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ _)]
      simp [operandD]
    · simp only [freshFrom_cons, freshFrom_nil, and_true, Nat.add_sub_cancel_left]; exact hap
    · exact hrt
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact outside_of_forall fun r' hr' => by have := hAp r' hr'; simp only [Nat.add_sub_cancel_left]; omega
    · rw [hlen0]; simp [range0]
    · rw [hcost32, hlen0]
      simp only [range0, if_true, List.append_nil]
      rw [wr4_view _ _ _ hobj]
      exact hinv'

/-! ## A call state that satisfies the whole precondition -/

def ewstate64 : State := { LiveSatAmd64.wst [eFP, 2, eSP, 1, 1] with mem := ewmem }

theorem ew64call : CallOK64 ewstate64 4096 5 := by
  obtain ⟨a, b, c, d, e⟩ := wcallOK64 [eFP, 2, eSP, 1, 1] 5 (by omega)
  have e4 : (ewstate64.regs 4).toNat = LiveSat.wsp := LiveSat.wspn
  refine ⟨?_, b, c, d, ?_⟩
  · show ewmem.readLE (ewstate64.regs 4).toNat 8 < _
    rw [e4, ewframe.readLE _ _ (by simp [LiveSat.wsp, CB, outside_cons, outside_nil])]
    have a' := a
    rw [LiveSatAmd64.wmem_eq, LiveSatAmd64.w4, LiveSat.wspn] at a'
    exact a'
  · show ewmem.accessible ((ewstate64.regs 4).toNat - 4096) _ true = true
    rw [e4, ewframe.accessible]
    have e' := e
    rw [LiveSatAmd64.wmem_eq, LiveSatAmd64.w4, LiveSat.wspn] at e'
    exact e'

theorem ew64guard : StackRoom64 ewstate64 4096 5 := by
  obtain ⟨⟨a, b, c⟩, d⟩ := wguard64 [eFP, 2, eSP, 1, 1] 5 (by omega)
  refine ⟨⟨a, ?_, ?_⟩, d⟩
  · show ewmem.accessible _ _ false = true
    rw [ewframe.accessible]; exact b
  · have e14 : (ewstate64.regs 14).toNat = LiveSat.wg := LiveSat.wgn
    show ewmem.readLE _ 8 + 4096 < _
    rw [ewframe.readLE _ _ (by
      show Outside ((ewstate64.regs 14).toNat + 16) 8 [(CB, CB + 0x100)]
      rw [e14]; simp [LiveSat.wg, CB, outside_cons, outside_nil])]; exact c

set_option maxRecDepth 100000 in
theorem ew64reads : ReadsOutside (errorfReads ewmem eFP 2 eSP) (liveWin64 ewstate64 4096 5) := by
  have : errorfReads ewmem eFP 2 eSP = [(eFP, 2), (eSP, 16), (eE, 16), (eTxt, 0)] := by decide
  rw [this]
  simp only [ReadsOutside, List.mem_cons, List.not_mem_nil, or_false]
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [liveWin64, calleeStack64, ewstate64, LiveSatAmd64.wst, LiveSat.wsp, eFP, eSP, eE, eTxt, CB, outside_cons, outside_nil]

theorem errorfLive_satisfiable : ∃ (R : RtInv) (tErr iErr tInt iWrap B : Nat) (impl : List Janus.Amd64.Segment),
    ErrorfLive (toy.link impl) A0 4096 R tErr iErr tInt iWrap B ∧
    ∃ (s : State) (L : List (Nat × Nat)) (b : Nat), s.rip = BitVec.ofNat 64 A0 ∧
      CallOK64 s 4096 5 ∧ StackRoom64 s 4096 5 ∧
      ArgsOK (Env.mk tErr iErr tInt iWrap) B s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat
        (s.regs 7).toNat (s.regs 6).toNat ∧
      ReadsOutside (errorfReads s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) (liveWin64 s 4096 5) ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat, (s.regs 7).toNat, (s.regs 6).toNat] L b
        (errorfCost s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat) (s.regs 14).toNat s.mem
        (liveWin64 s 4096 5) :=
  ⟨toyR tys0 okE, tErr, iErr, tInt, iWrap, 0, at0 code, errorf_impl okE, ewstate64, [], 0x400, rfl, ew64call, ew64guard,
    ewargs, ew64reads, ⟨⟨rfl, by decide⟩, ewinv (ewstate64.regs 14).toNat, ewcost, by simp, wwin64 [eFP, 2, eSP, 1, 1] 5 (by omega)⟩⟩

end Janus.Contracts.ErrorfSatAmd64
