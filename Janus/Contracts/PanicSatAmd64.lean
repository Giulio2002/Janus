import Janus.Contracts.PanicAmd64
import Janus.Contracts.PanicSat
import Janus.Contracts.IfaceModel

/-!
# The panic/defer/recover contracts are satisfiable (amd64)

As `Janus.Contracts.PanicSat` for the amd64 contracts of `Janus.Contracts.PanicAmd64`: the same
model `P0` (whose laws hold), x86-64 machine code (bytes from GNU `as`) at `A0` of a program with no
other code, proofs that it meets each contract, and a call state in each precondition.
-/

namespace Janus.Contracts.PanicSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts.PanicAmd64
open Janus (MemFrame InRanges Outside outside_cons outside_nil outside_append)
open Janus.Contracts.PanicSat (P0 P0_laws P0_priv P0_depth P0_env PANREC)

def toy : Janus.Amd64.Program := { segments := [], stubs := [], exitAddr := 0 }
def A0 : Nat := 0x100000
def at0 (bs : List Nat) : List Janus.Amd64.Segment := [{ name := "model", base := A0, bytes := bs }]
def withCode (bs : List Nat) : Janus.Amd64.Program := { segments := at0 bs, stubs := [], exitAddr := 0 }
theorem link_at0 (bs : List Nat) : toy.link (at0 bs) = withCode bs := rfl

def wg : Nat := 0x50000
def wsp : Nat := 0x48000

/-- The witness memory: the runtime range `[0x10000, 0x11000)` writable, a stack
`[0x40000, 0x50000)` writable (the return address at `[wsp]` is `0`), the goroutine readable. The
`gopanic` witness also has a pending open-coded defer in the caller's frame (`deferBits` `1` at
`wsp + 8 + 40`, the slot at `wsp + 8 + 48` holding the funcval `0x41000`, whose code word is
`0x300000`). -/
def wmem (pend : Bool) : Janus.Arm64.Memory :=
  ⟨fun a => if pend then
      (if a = wsp + 48 then 1 else if a = wsp + 57 then 0x10 else if a = wsp + 58 then 0x04
       else if a = 0x41002 then 0x30 else 0) else 0,
    [⟨0x10000, 0x1000, true⟩, ⟨0x40000, 0x10000, true⟩, ⟨0x50000, 0x100, false⟩]⟩

/-- The witness call state: `RSP = wsp`, `R14 = wg`, `RBP = wsp + 8`, `RAX = 1`. -/
def wstate (pend : Bool) : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg
      else if i = 5 then BitVec.ofNat 64 (wsp + 8) else if i = 0 then 1 else 0,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := wmem pend }

theorem wstate_pre (pend : Bool) (n : Nat) (hn : n ≤ 2) : PanicPre P0 n (wstate pend) := by
  have h4 : (wstate pend).regs 4 = BitVec.ofNat 64 wsp := rfl
  have h14 : (wstate pend).regs 14 = BitVec.ofNat 64 wg := rfl
  have hm : (wstate pend).mem = wmem pend := rfl
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · show (wstate pend).mem.accessible 0x10000 0x1000 true = true; rw [hm]; cases pend <;> decide
  · simp only [regG, stackguard0Offset, h14]; decide
  · simp only [regG, stackguard0Offset, h14, hm]; cases pend <;> decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, h14, h4, hm, P0_depth]
    cases pend <;> decide
  · simp only [h4]; decide
  · simp only [h4, P0_depth]; decide
  · simp only [h4]; simp [wsp]; omega
  · simp only [h4, hm, P0_depth, BitVec.toNat_ofNat]
    refine Janus.Arm64.Memory.accessible_mono _
      (show (wmem pend).accessible (wsp - 64) (64 + 8 + 8 * 2) true = true by cases pend <;> decide) ?_ ?_
    · simp [wsp]
    · simp [wsp]; omega
  · simp only [h4, hm]; cases pend <;> decide
  · simp only [h4, P0_depth, P0_priv, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]

/-- A model implementation's return as `PanicRet` (amd64). -/
theorem panicRet_of (P : PanicRuntime) (nargs : Nat) (s s' : Janus.Amd64.State)
    (hrip : s'.rip = retAddrOf s) (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase)
    (hdf : s'.df = s.df) (hmx : s'.mxcsr = s.mxcsr)
    (hfr : MemFrame s.mem s'.mem (P.priv ++ Contracts.MapAmd64.calleeStack s P.depth nargs))
    (henv : P.Env s'.mem) : PanicRet P nargs s s' := by
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, ?_, hfr, henv⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx ⊢
  subst hrip hfs hdf hmx
  congr
  · funext i
    simp only [Contracts.MapAmd64.keepABI]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  · funext i
    simp only [Contracts.MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx
    · rfl

/-! ## `RET`: the returning contracts -/

theorem ret_summary (n : Nat) :
    Summary (toy.link (at0 [0xc3])) A0 (PanicPre P0 n) (PanicRet P0 n) := by
  rw [link_at0]
  intro s hpc ⟨henv, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩
  janus64_run
  exact panicRet_of P0 n s _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) henv

theorem deferproc_satisfiable : ∃ (P : PanicRuntime) (impl : List Janus.Amd64.Segment), P.Laws ∧
    DeferprocContract (toy.link impl) A0 P ∧ ∃ s : Janus.Amd64.State,
      s.rip = BitVec.ofNat 64 A0 ∧ PanicPre P 1 s :=
  ⟨P0, _, P0_laws, ret_summary 1, wstate false, rfl, wstate_pre false 1 (by decide)⟩

theorem deferprocStack_satisfiable : ∃ (P : PanicRuntime) (impl : List Janus.Amd64.Segment), P.Laws ∧
    DeferprocStackContract (toy.link impl) A0 P ∧ ∃ s : Janus.Amd64.State,
      s.rip = BitVec.ofNat 64 A0 ∧ PanicPre P 1 s :=
  ⟨P0, _, P0_laws, ret_summary 1, wstate false, rfl, wstate_pre false 1 (by decide)⟩

theorem deferprocat_satisfiable : ∃ (P : PanicRuntime) (impl : List Janus.Amd64.Segment), P.Laws ∧
    DeferprocatContract (toy.link impl) A0 P ∧ ∃ s : Janus.Amd64.State,
      s.rip = BitVec.ofNat 64 A0 ∧ PanicPre P 2 s :=
  ⟨P0, _, P0_laws, ret_summary 2, wstate false, rfl, wstate_pre false 2 (by decide)⟩

theorem deferrangefunc_satisfiable : ∃ (P : PanicRuntime) (impl : List Janus.Amd64.Segment), P.Laws ∧
    DeferrangefuncContract (toy.link impl) A0 P ∧ ∃ s : Janus.Amd64.State,
      s.rip = BitVec.ofNat 64 A0 ∧ PanicPre P 0 s :=
  ⟨P0, _, P0_laws, ret_summary 0, wstate false, rfl, wstate_pre false 0 (by decide)⟩

theorem deferreturn_satisfiable : ∃ (P : PanicRuntime) (impl : List Janus.Amd64.Segment), P.Laws ∧
    DeferreturnContract (toy.link impl) A0 P ∧ ∃ s : Janus.Amd64.State,
      s.rip = BitVec.ofNat 64 A0 ∧ PanicPre P 0 s :=
  ⟨P0, _, P0_laws, ret_summary 0, wstate false, rfl, wstate_pre false 0 (by decide)⟩

/-! ## `gorecover` -/

/-- `mov $PANREC,%r10d; mov 24(%r10),%r11; test %r11,%r11; jz nil; mov 16(%r10),%r11;
cmp 8(%rbp),%r11; jne nil; mov (%r10),%rax; mov 8(%r10),%rbx; movq $1,32(%r10); ret;
nil: xor %eax,%eax; xor %ebx,%ebx; ret`. -/
def gorecoverCode : List Nat :=
  [0x41, 0xba, 0x00, 0x08, 0x01, 0x00, 0x4d, 0x8b, 0x5a, 0x18, 0x4d, 0x85, 0xdb, 0x74, 0x1a,
   0x4d, 0x8b, 0x5a, 0x10, 0x4c, 0x3b, 0x5d, 0x08, 0x75, 0x10, 0x49, 0x8b, 0x02, 0x49, 0x8b,
   0x5a, 0x08, 0x49, 0xc7, 0x42, 0x20, 0x01, 0x00, 0x00, 0x00, 0xc3, 0x31, 0xc0, 0x31, 0xdb,
   0xc3]

theorem gorecover_impl : GorecoverContract (toy.link (at0 gorecoverCode)) A0 P0 := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, hfp, hfp'⟩
  simp only [P0_env] at henv
  have hrd : s.mem.accessible PANREC 0x800 true = true :=
    Janus.Arm64.Memory.accessible_mono _ henv (by simp [PANREC]) (by simp [PANREC])
  simp only [PANREC] at hrd
  simp only [P0_depth, P0_priv, outside_cons, outside_nil, and_true] at hout hst hd1 hd2
  have hra' : (s.mem.writeLE 67616 8 1).readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint s.mem 1 (by omega)
  janus64_run
  · refine ⟨panicRet_of P0 0 s _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) henv, fun h => h,
      fun v rp hp _ _ => ?_⟩
    have := hp.1; simp only [PANREC, Nat.reduceAdd] at this; omega
  · refine ⟨panicRet_of P0 0 s _ (by simp [retAddrOf, hra']) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl
      (by simp only [P0_priv, Contracts.MapAmd64.calleeStack, P0_depth, List.cons_append,
        List.nil_append]; janus_frame)
      (by simp only [P0_env, Janus.Arm64.Memory.accessible_writeLE]; exact henv), fun hc => ?_,
      fun v rp hp _ _ => ?_⟩
    · have h1 : s.mem.readLE (PANREC + 24) 8 = 0 := hc
      simp only [PANREC, Nat.reduceAdd] at h1; omega
    · obtain ⟨-, h2, h3, -⟩ := hp
      simp only [PANREC, Nat.reduceAdd] at h2 h3
      have hl1 := Janus.Arm64.Memory.readLE_lt s.mem 67584 8
      have hl2 := Janus.Arm64.Memory.readLE_lt s.mem 67592 8
      refine ⟨by first | omega | (simp only [BitVec.toNat_ofNat]; omega) | (simp [setRegF]; omega),
        by first | omega | (simp only [BitVec.toNat_ofNat]; omega) | (simp [setRegF]; omega), ?_⟩
      show (Janus.Arm64.Memory.writeLE s.mem (PANREC + 32) 8 1).readLE (PANREC + 32) 8 = 1
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
  · refine ⟨panicRet_of P0 0 s _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) henv, fun hc => ?_,
      fun v rp hp _ hfp8 => ?_⟩
    · have h1 : s.mem.readLE (PANREC + 24) 8 = 0 := hc
      simp only [PANREC, Nat.reduceAdd] at h1; omega
    · obtain ⟨-, -, -, h4⟩ := hp
      simp only [PANREC, Nat.reduceAdd] at h4
      have := Janus.Arm64.Memory.readLE_lt s.mem 67600 8
      have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 5).toNat + 8) 8
      exfalso; omega

theorem gorecover_satisfiable : ∃ (P : PanicRuntime) (impl : List Janus.Amd64.Segment), P.Laws ∧
    GorecoverContract (toy.link impl) A0 P ∧ ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧
      (PanicPre P 0 s ∧ s.mem.accessible ((s.regs 5).toNat + 8) 8 false = true ∧
        (s.regs 5).toNat + 16 ≤ 2 ^ 48) :=
  ⟨P0, _, P0_laws, gorecover_impl, wstate false, rfl, wstate_pre false 0 (by decide), by decide,
    by decide⟩

/-! ## `gopanic` (recover case) -/

/-- `lea 8(%rsp),%r9; mov 48(%r9),%rdx; mov (%rdx),%r11; sub $40,%rsp; mov %r9,16(%rsp);
movb $0,40(%r9); mov $PANREC,%r10d; mov %rax,(%r10); mov %rbx,8(%r10); lea after(%rip),%r12;
mov %r12,16(%r10); movq $1,24(%r10); movq $0,32(%r10); call *%r11;
after: mov 16(%rsp),%r9; mov %r9,%rsp; mov $PANREC,%r10d; movq $0,24(%r10);
mov $0x100800,%r11d; jmp *%r11`. -/
def gopanicCode : List Nat :=
  [0x4c, 0x8d, 0x4c, 0x24, 0x08, 0x49, 0x8b, 0x51, 0x30, 0x4c, 0x8b, 0x1a, 0x48, 0x83, 0xec, 0x28,
   0x4c, 0x89, 0x4c, 0x24, 0x10, 0x41, 0xc6, 0x41, 0x28, 0x00, 0x41, 0xba, 0x00, 0x08, 0x01, 0x00,
   0x49, 0x89, 0x02, 0x49, 0x89, 0x5a, 0x08, 0x4c, 0x8d, 0x25, 0x17, 0x00, 0x00, 0x00, 0x4d, 0x89,
   0x62, 0x10, 0x49, 0xc7, 0x42, 0x18, 0x01, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x42, 0x20, 0x00, 0x00,
   0x00, 0x00, 0x41, 0xff, 0xd3, 0x4c, 0x8b, 0x4c, 0x24, 0x10, 0x4c, 0x89, 0xcc, 0x41, 0xba, 0x00,
   0x08, 0x01, 0x00, 0x49, 0xc7, 0x42, 0x18, 0x00, 0x00, 0x00, 0x00, 0x41, 0xbb, 0x00, 0x08, 0x10,
   0x00, 0x41, 0xff, 0xe3]

theorem gopanic_impl : GopanicRecoverContract (toy.link (at0 gopanicCode)) A0 P0 40 48 0x100800 := by
  rw [link_at0]
  intro s hpc ⟨⟨henv, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, hx0, hbits, hb1, hb2, hb3, hs1,
    hs2, hf1, hf2, hc2⟩
  simp only [P0_env, P0_depth, P0_priv, outside_cons, outside_nil, and_true] at henv hd1 hd2 hst hout hb3
  have hrd : s.mem.accessible PANREC 0x800 true = true :=
    Janus.Arm64.Memory.accessible_mono _ henv (by simp [PANREC]) (by simp [PANREC])
  simp only [PANREC] at hrd
  have hspl := (s.regs 4).isLt
  have e56 : (s.regs 4).toNat + 8 + 48 = (s.regs 4).toNat + 56 := by omega
  have e48 : (s.regs 4).toNat + 8 + 40 = (s.regs 4).toNat + 48 := by omega
  unfold GopanicRecoverCall
  rw [e56] at hs1 hs2 hf1 hf2 hc2 ⊢
  rw [e48] at hbits hb1 hb2 hb3 ⊢
  show ReachesRet _ _ s _
  janus64_run
  refine ⟨by omega, (by simp only [P0_depth]; omega), by omega, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [P0, PANREC, Nat.reduceAdd,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    exact ⟨trivial, by rw [h64]; exact Nat.mod_eq_of_lt (s.regs 0).isLt,
      by rw [h64]; exact Nat.mod_eq_of_lt (s.regs 3).isLt, trivial⟩
  · simp only [P0_env, Janus.Arm64.Memory.accessible_writeLE]; exact henv
  · simp only [P0_priv, P0_depth, List.cons_append, List.nil_append]
    janus_frame
  · intro c' hrip' h4' h14' h5' hx' hdf' hag henv' hrec
    obtain ⟨r', rip', fl', xm', m', yh', fs', df', mx'⟩ := c'
    simp only at hrip' h4' h14' h5' hx' hdf' hag henv' hrec ⊢
    have hrip'' : rip' = BitVec.ofNat 64 1048645 := by
      apply BitVec.eq_of_toNat_eq; rw [hrip']; rfl
    subst hrip'' hdf'
    have hwin' : m'.accessible ((s.regs 4).toNat - 48) 56 true = true := by
      rw [hag.1]; simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
    have hpr' : m'.accessible 67584 2048 true = true := by
      rw [hag.1]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hrd
    have h4n : (r' 4).toNat = (s.regs 4).toNat - 40 := by
      rw [h4', BitVec.toNat_sub]; simp; omega
    have hv : m'.readLE ((s.regs 4).toNat - 24) 8 = (s.regs 4).toNat + 8 := by
      rw [hag.readLE ⟨((s.regs 4).toNat - 48, (s.regs 4).toNat + 8), by simp, by omega, by omega⟩]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_self]
      have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [h64]; exact Nat.mod_eq_of_lt (by omega)
    show ReachesRet _ _ _ _
    janus64_run
    refine ⟨?_, h5', h14', hx', ?_, ?_, ?_⟩
    · rw [show (r' 4).toNat + 16 = (s.regs 4).toNat - 24 by omega, hv]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]; try omega
    · simp only [P0_priv, P0_depth, List.cons_append, List.nil_append]
      janus_frame
    · simp only [P0_env, Janus.Arm64.Memory.accessible_writeLE] at henv' ⊢; exact henv'
    · show (Janus.Arm64.Memory.writeLE m' (PANREC + 24) 8 0).readLE (PANREC + 24) 8 = 0
      rw [Janus.Arm64.Memory.readLE_writeLE_self]

theorem gopanic_satisfiable : ∃ (P : PanicRuntime) (impl : List Janus.Amd64.Segment)
    (bitsOff slotOff resume : Nat), P.Laws ∧
    GopanicRecoverContract (toy.link impl) A0 P bitsOff slotOff resume ∧
    ∃ s : Janus.Amd64.State, s.rip = BitVec.ofNat 64 A0 ∧ GopanicRecoverPre P bitsOff slotOff s := by
  refine ⟨P0, _, 40, 48, 0x100800, P0_laws, gopanic_impl, wstate true, rfl,
    wstate_pre true 2 (by decide), by decide, ?_, by decide, ?_, ?_, by decide, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [P0_priv, outside_cons, outside_nil, and_true]) <;> decide

end Janus.Contracts.PanicSatAmd64
