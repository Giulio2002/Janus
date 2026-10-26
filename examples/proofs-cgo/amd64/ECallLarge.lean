import Extracted

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI

namespace Proof

abbrev goFn : Nat := exportAddr Extracted.program "GoLarge"
abbrev gsL : Nat := 8192
/-- The `REP STOSQ` that zeroes the array. -/
abbrev stosSite : Nat := goFn + 0x55

def GoPre (a : W64) (u : State) : Prop :=
  StackGuardOK u 4712 ∧ gsL ≤ (u.regs 4).toNat ∧ (u.regs 4).toNat + 16 ≤ 2 ^ 48 ∧
    u.mem.accessible ((u.regs 4).toNat - gsL) (gsL + 16) true = true ∧
    Outside ((u.regs 14).toNat + 16) 8 [((u.regs 4).toNat - gsL, (u.regs 4).toNat + 16)] ∧
    a.toNat + 16 ≤ 2 ^ 48 ∧ u.mem.accessible a.toNat 16 true = true ∧
    Outside a.toNat 16 [((u.regs 4).toNat - gsL, (u.regs 4).toNat + 16)]

def GoPost (a : W64) (u u' : State) : Prop :=
  MemFrame (u.mem.writeLE (a.toNat + 8) 8 (3 * u.mem.readLE a.toNat 8)) u'.mem
    [((u.regs 4).toNat - gsL, (u.regs 4).toNat + 16)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem go_spec (a : W64) : EnsuresC Extracted.program Contract.none goFn [a] (GoPre a) (GoPost a) := by
  intro ret hret u hu ⟨⟨hg1, hg2, hg3⟩, hb, ha, hw, hgo, hab, haw, hao⟩
  simp only [outside_cons, outside_nil, and_true, gsL] at hgo hao hb hw
  simp only [stackguard0, regG, stackguard0Offset, GoABI.regSP] at hg1 hg2 hg3
  apply ReturnsC.of_reaches
  janus64_intro hu
  janus64_run until [janus_eval% stosSite]
  have h7 : (u.regs 4 - 4824#64) = BitVec.ofNat 64 ((u.regs 4).toNat - 4824) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  refine Reaches.repStos hret (c := janus_eval% stosSite) (len := 3) (w := 64) rfl rfl
    ((u.regs 4).toNat - 4824) 600 (by simpa using hu.df) (by simp [setRegF, h7]) (by simp [setRegF]) (by omega)
    (by exact Janus.Arm64.Memory.accessible_mono _ (by simpa using hw) (by omega) (by omega)) (by omega) ?_
  have hacc : ∀ b n w, (fillLE ((((Janus.Arm64.Memory.writeLE u.mem ((u.regs 4).toNat - 8) 8 (u.regs 5).toNat).writeLE
      ((u.regs 4).toNat + 8) 8 a.toNat).writeLE ((u.regs 4).toNat - 16) 8 (u.mem.readLE a.toNat 8 % 8)).writeLE
      ((u.regs 4).toNat - 24) 8 ((u.mem.readLE a.toNat 8 + 1) % 8)) ((u.regs 4).toNat - 4824) 8 0 600).accessible
      b n w = u.mem.accessible b n w := by
    intro b n w; rw [accessible_fillLE]; simp only [Janus.Arm64.Memory.accessible_writeLE]
  have hF := (hacc _ _ _).trans hw
  have hFa := (hacc _ _ _).trans haw
  janus64_run [readLE_fillLE_disjoint]
  unfold GoPost
  rw [show 3 * u.mem.readLE a.toNat 8 = u.mem.readLE a.toNat 8 +
    (u.mem.readLE a.toNat 8 + u.mem.readLE a.toNat 8) by omega]
  dsimp only
  have hv : ∀ m : Janus.Arm64.Memory, m.writeLE (a.toNat + 8) 8 (u.mem.readLE a.toNat 8 +
      (u.mem.readLE a.toNat 8 + u.mem.readLE a.toNat 8) % 18446744073709551616) =
      m.writeLE (a.toNat + 8) 8 (u.mem.readLE a.toNat 8 + (u.mem.readLE a.toNat 8 + u.mem.readLE a.toNat 8)) := by
    intro m
    rw [← Janus.Arm64.Memory.writeLE_mod m _ 8 (_ + _ % _),
      ← Janus.Arm64.Memory.writeLE_mod m _ 8 (u.mem.readLE a.toNat 8 + _)]
    congr 1; omega
  rw [hv]
  apply MemFrame.writeLE_both
  refine ⟨fun b n hb => ?_, fun b n w => ?_⟩
  · simp only [outside_cons, outside_nil, and_true, gsL] at hb
    have h8 := Nat.mod_lt (u.mem.readLE a.toNat 8) (show 0 < 8 by decide)
    have h8' := Nat.mod_lt (u.mem.readLE a.toNat 8 + 1) (show 0 < 8 by decide)
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      readLE_fillLE_disjoint _ _ _ _ _ _ _ (by omega)]
    simp (disch := omega) only [Janus.Tactic.readLE_writeLE_disjoint]
  · rw [Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE,
      Janus.Arm64.Memory.accessible_writeLE, hacc]

/-! ## The C side, under the callback assumption -/

abbrev rid : Nat := CData.addr Extracted.cdata "runtime_init_done"
abbrev ctxf : Nat := CData.addr Extracted.cdata "cgo_context_function"

/-- The C stack `e_calllarge` needs: its frames (down to the `cgocallback` stub at `RSP − 152`) and
`cgocallback`'s scratch. -/
abbrev win : Nat := 152 + cbStackScratch

/-- The frame `crosscall2` passes (`[RSP+16]` at `cgocallback`). -/
def frameOf (S : State) : Nat := S.mem.readLE ((S.regs 4).toNat + 16) 8

/-- The goroutine stack the callback gets: `gsL` bytes, under the readiness `H` of the runtime
memory `rt`. -/
def cbk (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) : Janus.FFI.CbStack := ⟨gsL, rt, H⟩

def G (k : Janus.FFI.CbStack) (S : State) : Prop :=
  CbStack S ∧ CbReady k Extracted.tls S ∧ frameOf S + 16 ≤ 2 ^ 48 ∧ S.mem.accessible (frameOf S) 16 true = true ∧
    Outside (frameOf S) 16 (cbClobber Extracted.tls S)

def E (S : State) : Janus.Arm64.Memory :=
  S.mem.writeLE (frameOf S + 8) 8 (3 * S.mem.readLE (frameOf S) 8)

def CPre (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (s : State) : Prop :=
  Extracted.program.DataLoaded s.mem ∧ CStack s win 8 ∧
  s.mem.accessible rid 4 false = true ∧ s.mem.readLE rid 4 = 2 ∧
  s.mem.accessible ctxf 8 false = true ∧ s.mem.readLE ctxf 8 = 0 ∧
  s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ 24 ≤ s.fsBase.toNat ∧ s.mem.accessible (s.fsBase.toNat + 40) 8 false = true ∧
  Outside rid 4 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside ctxf 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat + 40) 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 24) 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside ctxf 8 [(s.fsBase.toNat - 24, s.fsBase.toNat - 16)] ∧
  Outside rid 4 [(s.fsBase.toNat - 24, s.fsBase.toNat - 16)] ∧
  Outside ((s.regs 4).toNat - win) win rt ∧
  H [goFn, gsL] (s.mem.readLE (tlsGSlot Extracted.tls s.fsBase) 8) ((s.regs 4).toNat - 152)
    (Janus.Contracts.rtView rt s.mem)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem c_spec (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (x : W64) :
    CEnsuresC Extracted.program (CallbackSpec Extracted.tls goFn (G (cbk rt H)) E) Extracted.entry [x]
      (CPre rt H) (fun _ s' => s'.regs 0 = 3 * x) := by
  intro ret hret s hs hpre
  obtain ⟨hd, ⟨hal, hb, ha, hw⟩, hra, hrv, hca, hcv, hfb, hfl, hga, hro, hco, hgo, hto, hct, hrt, hrtw, hH⟩ := hpre
  have et1 : Extracted.tls.x64Off = janus_eval% Extracted.tls.x64Off := rfl
  have et2 : Extracted.tls.varOff "runtime.tlsg" = janus_eval% (Extracted.tls.varOff "runtime.tlsg") := rfl
  simp only [tlsGSlot, TLSImage.x64Addr, et1, et2] at hH
  simp only [win, cbStackScratch] at hrtw
  have hv : ∀ (m : Janus.Arm64.Memory) a n v, (s.regs 4).toNat - (152 + 16384) ≤ a → a + n ≤ (s.regs 4).toNat →
      Janus.Contracts.rtView rt (m.writeLE a n v) = Janus.Contracts.rtView rt m :=
    fun _ _ _ _ h1 h2 => Janus.Contracts.rtView_writeLE (Outside.of_sub hrtw h1 (by omega))
  have e1 : rid = janus_eval% rid := rfl
  have e2 : ctxf = janus_eval% ctxf := rfl
  rw [e1] at hra hrv hro hrt
  rw [e2] at hca hcv hco hct
  simp only [outside_cons, outside_nil, and_true, win, cbStackScratch] at hro hco hgo hto hb hw hct hrt
  simp only [CABI.regSP] at hal hb ha hw
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = x := hs.reg (i := 0) (by simp)
  simp only [Amd64.Program.withExit] at h_ret
  have hr47 : ret < 2 ^ 47 := hret.user
  apply ReturnsC.of_reaches
  janus64_data hd [hw]
  have hgf : goFn = janus_eval% goFn := rfl
  have h56 : ((s.regs 4).toNat - 56) % 16 = 0 := by omega
  janus64_run [h56]
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · janus64_simp
  · simp only [G, frameOf, cbClobber, CbStack, cbStackScratch, CbReady, cbk, tlsGSlot, TLSImage.x64Addr, et1, et2,
      outside_cons, outside_nil, and_true]
    simp (disch := omega) only [hv]
    janus64_simp
    rw [hgf] at hH
    exact ⟨⟨by omega, by omega, Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)⟩, hH, by omega,
      Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega), by omega, by omega, by omega⟩
  · rintro s' ⟨-, m, ⟨regs, flags, xmm, ymmHi, mx, rfl, hr4, hmx⟩, hmf⟩
    simp only [E, frameOf, cbClobber, cbStackScratch, tlsGSlot, TLSImage.x64Addr, et1, et2, setRegF_apply, ↓reduceIte,
      Nat.reduceEqDiff] at hmf
    have h152 : (s.regs 4 - 152#64).toNat = (s.regs 4).toNat - 152 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    rw [h152] at hmf
    simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff] at hr4
    have h144 : (s.regs 4 - 152#64 + 8) = s.regs 4 - 144#64 := by
      apply BitVec.eq_of_toNat_eq
      show ((s.regs 4 - 152#64) + 8#64).toNat = _
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [h144] at hr4
    have hregs : regs = setRegF regs 4 (s.regs 4 - 144#64) := by
      funext i; simp only [setRegF]; split <;> simp_all
    rw [hregs]
    apply ReturnsC.of_reaches
    janus64_run
    refine ⟨hmx, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega


/-! ## Composition: the Go function's theorem discharges the callback assumption -/

theorem frame_lt (S : State) : frameOf S < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Janus.Arm64.Memory.readLE_lt _ _ _) (by decide)

theorem refines (k : Janus.FFI.CbStack) (hk : k.size = gsL) :
    (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True) k).Refines
      (CallbackSpec Extracted.tls goFn (G k) E) := by
  refine CgoCallback.refines (fun a => go_spec a) (fun S hG => hG.1) (fun S hG => hG.2.1) ?_
    (fun _ _ => rfl) ?_ ?_
  · rintro S u ret ⟨-, -, hb, hacc, hout⟩ he -
    have hf : (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    have hst := he.goStack
    have hsep := he.stackSep _ _ _ hacc
    have hgo := he.gOff
    rw [hk] at hst hsep hgo
    obtain ⟨g1, g2, g3⟩ := hst
    simp only [outside_cons, outside_nil, and_true] at hsep hgo
    unfold GoPre
    rw [hf]
    refine ⟨he.guardOK (by rw [hk]; simp only [gsL, Janus.FFI.stackGuard]; decide), g1, g2, g3, ?_, hb,
      he.keptAcc _ _ _ ⟨hacc, hout⟩, ?_⟩
    · simp only [outside_cons, outside_nil, and_true, gsL, gStructSize] at hgo ⊢; omega
    · simp only [outside_cons, outside_nil, and_true, gsL]; omega
  · rintro S u ret u' ⟨-, -, hb, hacc, hout⟩ he - - hpost b hb' hbacc
    have hf : (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    unfold GoPost at hpost
    rw [hf] at hpost
    have hsep := he.stackSep _ _ _ hbacc
    rw [hk] at hsep
    have h1 := hpost.readLE b 1 hsep
    simp only [Janus.Arm64.Memory.readLE_one] at h1
    rw [BitVec.eq_of_toNat_eq h1, E, Janus.Arm64.Memory.bytes_writeLE, Janus.Arm64.Memory.bytes_writeLE]
    have hk8 : u.mem.readLE (frameOf S) 8 = S.mem.readLE (frameOf S) 8 :=
      he.kept _ _ ⟨Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hacc)
        (Nat.le_refl _) (by omega), Outside.of_sub hout (Nat.le_refl _) (by omega)⟩
    rw [hk8]
    split
    · rfl
    · have := he.kept b 1 ⟨hbacc, hb'⟩
      simp only [Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
  · rintro S ⟨-, -, hb, hacc, hout⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`e_calllarge` end to end** (amd64), under the trusted `cgocallback` contract only. -/
theorem correctness (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (x : W64) :
    CEnsuresC Extracted.program
      (CgoCallback Extracted.tls Extracted.program Contract.none (fun _ => True) (cbk rt H))
      Extracted.entry [x] (CPre rt H) (fun _ s' => s'.regs 0 = 3 * x) :=
  (c_spec rt H x).refine (refines _ rfl)

namespace Witness

/-- A byte of the program's read-only data, if `a` is in one of its objects. -/
def dbyte (a : Nat) : Option Nat :=
  Extracted.program.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

/-- Little-endian byte `j` of `v`. -/
def byteOf (v j : Nat) : Nat := v / 256 ^ j % 256

/-- The witness call: `RSP = SP0` (its slot holding `RET`, where there is no code), `FS = FS0`. -/
def SP0 : Nat := 0x1000008
def FS0 : Nat := 0x800000
def RET : Nat := 0x1000

def mem0 : Janus.Arm64.Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyte a).getD
      (if a = rid then 2 else if SP0 ≤ a ∧ a < SP0 + 8 then byteOf RET (a - SP0) else 0)),
    [⟨rid, 4, true⟩, ⟨ctxf, 8, true⟩, ⟨FS0 - 24, 8, true⟩, ⟨FS0 + 40, 8, false⟩,
     ⟨SP0 - win, win + 8, true⟩] ++
      Extracted.program.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def s0 : State :=
  { regs := fun i => if i = 7 then 7#64 else if i = 4 then BitVec.ofNat 64 SP0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 FS0 }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [7#64] s0 :=
  ⟨rfl, by decide +kernel, by decide, by intro i h; simp at h; subst h; rfl, by decide, rfl⟩

theorem data : Extracted.program.DataLoaded mem0 := by
  unfold Amd64.Program.DataLoaded; decide +kernel

set_option maxRecDepth 100000 in
theorem pre : CPre [] (fun _ _ _ _ => True) s0 := by
  refine ⟨data, ?_⟩
  repeat' (first | exact trivial | apply And.intro)
  all_goals first
    | decide +kernel
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | trivial

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (rt : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (x : W64) (ret : Nat) (s : State),
    RetAddr Extracted.program ret ∧ CCall (Extracted.program.withExit ret) Extracted.entry [x] s ∧
      CPre rt H s :=
  ⟨[], fun _ _ _ _ => True, 7#64, RET, s0, hret, call, pre⟩

end Witness

end Proof
