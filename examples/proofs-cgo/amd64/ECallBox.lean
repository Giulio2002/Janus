import Extracted

/-!
# `int64_t e_callbox(int64_t x)` (C, amd64) calls back into Go code that calls a Go function and
# allocates: C → Go → `runtime.newobject`, composed end to end

```c
int64_t e_callbox(int64_t x) { return GoBox(x); }
```
```go
type box struct{ v int64 }

//go:noinline
func newBox(v int64) *box { return &box{v} }      // runtime.newobject

//export GoBox
func GoBox(x C.int64_t) C.int64_t { return C.int64_t(newBox(int64(x)).v + 1) }
```

The x86-64 counterpart of the arm64 proof. `e_callbox` tail-calls `GoBox`, the C function cgo
generates for `//export GoBox` (as in `ECallGo`: `_cgo_wait_runtime_init_done`, the frame,
`crosscall2`, `_cgo_release_context`, the stack protector at `%fs:0x28`). `crosscall2` calls
`runtime.cgocallback`, which runs the Go side of the export, `_cgoexp_…_GoBox`, on the goroutine
stack: its stack check reads `stackguard0` through `R14 = g`, it calls `newBox` (another stack
check), which calls `runtime.newobject` for a fresh 8-byte cell and stores `x` in it;
`_cgoexp_…_GoBox` reads it back and stores `x + 1` in the frame's result slot.

**Guarantee (`correctness`).** For every `x`, every list `rt` of runtime-owned memory ranges,
every implementation of `runtime.newobject` meeting `NewobjectContract64` with readiness `Ha`,
and every readiness `Hc` of an 8192-byte goroutine stack (`cbk`): every System V call of
`e_callbox` in a state where the runtime is initialised, the guard `%fs:0x28` and Go's TLS `g`
slot are readable, the C stack has room for the frames and `cgocallback`, the C memory is not
runtime-owned (`rt`, `rtc`), and the runtime is ready for the callback (`Hc` at the stub), returns
`x + 1 (mod 2^64)` restoring the callee-saved state, **under the trusted contract `CgoCallback`**
whose readiness `R` is the allocator's readiness `Ha` at the `newobject` call (`ROK`). Every
instruction of the C code, `crosscall2`, `_cgoexp_…_GoBox` and `newBox` is executed by the model;
`newobject` is the contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Amd64.FFI Janus.Contracts

namespace Proof

abbrev goFn : Nat := exportAddr Extracted.program "GoBox"

/-- The goroutine stack the callback needs: the two Go frames, `newobject`'s 4096-byte window and
the spill slots, below 8192 with the stack-check margin. -/
abbrev gsBox : Nat := 8192

/-- The goroutine stack of the callback: `gsBox` bytes, under the readiness `H` of `rtc`. -/
def cbk (rtc : List (Nat × Nat)) (H : RtReady) : Janus.FFI.CbStack := ⟨gsBox, rtc, H⟩

/-- `box`'s type descriptor (`newBox`'s `LEA`), the extraction's first data object. -/
def boxType : Nat := dataBase Extracted.program 0

/-! ## The Go side -/

/-- The runtime's readiness at the Go entry: `box`'s type descriptor (Go read-only data, not C
memory: the C side does not grant it) is in place, the goroutine stack is apart from it and from
the runtime-owned memory, and the allocator is ready for the `newobject` call (`Ha` for
`[boxType]`, the `g`, `RSP - 56` (the two frames and the return address) and the runtime's view
of the memory), and `RSP` is 8-aligned (Go's stack pointers always are; the model of
`cgocallback` does not state it). -/
def ROK (rt : List (Nat × Nat)) (Ha : RtReady) (u : State) : Prop :=
  (u.regs 4).toNat % 8 = 0 ∧ TypeOK u.mem boxType ∧ typSize u.mem boxType = 8 ∧ typPtrBytes u.mem boxType = 0 ∧
    Outside boxType 16 [((u.regs 4).toNat - gsBox, (u.regs 4).toNat + 16)] ∧
    Outside ((u.regs 4).toNat - gsBox) (gsBox + 16) rt ∧
    Ha [boxType] (u.regs 14).toNat ((u.regs 4).toNat - 56) (rtView rt u.mem)

def GoPre (rt : List (Nat × Nat)) (Ha : RtReady) (a : W64) (u : State) : Prop :=
  StackGuardOK u 24 ∧ gsBox ≤ (u.regs 4).toNat ∧ (u.regs 4).toNat + 16 ≤ 2 ^ 48 ∧
    u.mem.accessible ((u.regs 4).toNat - gsBox) (gsBox + 16) true = true ∧
    Outside ((u.regs 14).toNat + 16) 8 [((u.regs 4).toNat - gsBox, (u.regs 4).toNat + 16)] ∧
    a.toNat + 16 ≤ 2 ^ 48 ∧ u.mem.accessible a.toNat 16 true = true ∧
    Outside a.toNat 16 [((u.regs 4).toNat - gsBox, (u.regs 4).toNat + 16)] ∧ Outside a.toNat 16 rt ∧
    ROK rt Ha u

/-- The frame's result slot holds `p0 + 1`; the rest of memory changes only inside the
runtime-owned ranges and the goroutine stack. -/
def GoPost (rt : List (Nat × Nat)) (a : W64) (u u' : State) : Prop :=
  MemFrame (u.mem.writeLE (a.toNat + 8) 8 (u.mem.readLE a.toNat 8 + 1)) u'.mem
    (rt ++ [((u.regs 4).toNat - gsBox, (u.regs 4).toNat + 16)])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem go_spec (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (Ha : RtReady)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 Ha) (a : W64) :
    EnsuresC (Extracted.program.link impl) Contract.none goFn [a] (GoPre rt Ha a) (GoPost rt a) := by
  intro ret hret u hu ⟨⟨hg1, hg2, hg3⟩, hb, ha, hw, hgo, hab, haw, hao, hart, hal, ⟨ht1, ht2⟩, hts, hpb,
    hto, hrto, hH⟩
  simp only [outside_cons, outside_nil, and_true, gsBox] at hgo hao hto hrto hb hw
  simp only [stackguard0, regG, stackguard0Offset, GoABI.regSP] at hg1 hg2 hg3
  janus_eval_nat h_bt : boxType
  rw [h_bt] at ht1 ht2 hts hpb hto hH
  simp only [typSize, typPtrBytes] at hts hpb
  apply ReturnsC.of_reaches
  janus64_intro hu
  janus64_run until [segAddr Extracted.program "example.com/cgo/cenv.newBox" + 0x1f] calls [hnew.pos]
  simp only [hts, hpb, beq_self_eq_true, reduceBlockSize] at *
  have hdj := InRanges.disjoint ‹InRanges _ 8 rt› hrto
  have hdf := InRanges.disjoint ‹InRanges _ 8 rt› hart
  janus64_run
  unfold GoPost
  apply MemFrame.writeLE_both
  have hf := ‹MemFrame _ _ (rt ++ _)›
  have hin := ‹InRanges _ 8 rt›
  refine ⟨fun b n hb => ?_, fun b n w => ?_⟩
  · simp only [outside_append, outside_cons, outside_nil, and_true, gsBox] at hb
    obtain ⟨hbr, hbw⟩ := hb
    have hd := InRanges.disjoint hin hbr
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hf.readLE b n (by
      simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨hbr, by omega, by omega⟩)]
    simp (disch := omega) only [Janus.Tactic.readLE_writeLE_disjoint]
  · rw [Arm64.Memory.accessible_writeLE, hf.accessible]
    simp only [Arm64.Memory.accessible_writeLE]

/-! ## The C side, under the callback assumption -/

abbrev rid : Nat := CData.addr Extracted.cdata "runtime_init_done"
abbrev ctxf : Nat := CData.addr Extracted.cdata "cgo_context_function"

/-- The C stack `e_calllarge` needs: its frames (down to the `cgocallback` stub at `RSP − 152`) and
`cgocallback`'s scratch. -/
abbrev win : Nat := 152 + cbStackScratch

/-- The frame `crosscall2` passes (`[RSP+16]` at `cgocallback`). -/
def frameOf (S : State) : Nat := S.mem.readLE ((S.regs 4).toNat + 16) 8

def G (rt : List (Nat × Nat)) (k : Janus.FFI.CbStack) (S : State) : Prop :=
  CbStack S ∧ CbReady k Extracted.tls S ∧ frameOf S + 16 ≤ 2 ^ 48 ∧ S.mem.accessible (frameOf S) 16 true = true ∧
    Outside (frameOf S) 16 (cbClobber Extracted.tls S) ∧ (∀ a n w, S.mem.accessible a n w = true → Outside a n rt)

def E (S : State) : Janus.Arm64.Memory :=
  S.mem.writeLE (frameOf S + 8) 8 (S.mem.readLE (frameOf S) 8 + 1)

/-- The extraction without `box`'s type descriptor: the read-only data the C side needs (the C
state does not grant the Go type descriptor; the Go side gets it from `ROK`). -/
def CProg : Amd64.Program :=
  { Extracted.program with data := Extracted.program.data.filter (·.base != boxType) }

def CPre (rt rtc : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (s : State) : Prop :=
  CProg.DataLoaded s.mem ∧ CStack s win 8 ∧
  s.mem.accessible rid 4 false = true ∧ s.mem.readLE rid 4 = 2 ∧
  s.mem.accessible ctxf 8 false = true ∧ s.mem.readLE ctxf 8 = 0 ∧
  s.fsBase.toNat + 48 ≤ 2 ^ 48 ∧ 24 ≤ s.fsBase.toNat ∧ s.mem.accessible (s.fsBase.toNat + 40) 8 false = true ∧
  Outside rid 4 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside ctxf 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat + 40) 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside (s.fsBase.toNat - 24) 8 [((s.regs 4).toNat - win, (s.regs 4).toNat + 8)] ∧
  Outside ctxf 8 [(s.fsBase.toNat - 24, s.fsBase.toNat - 16)] ∧
  Outside rid 4 [(s.fsBase.toNat - 24, s.fsBase.toNat - 16)] ∧
  (∀ a n w, s.mem.accessible a n w = true → Outside a n rt) ∧
  Outside ((s.regs 4).toNat - win) win rtc ∧
  H [goFn, gsBox] (s.mem.readLE (tlsGSlot Extracted.tls s.fsBase) 8) ((s.regs 4).toNat - 152)
    (Janus.Contracts.rtView rtc s.mem)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem c_spec (impl : List Amd64.Segment) (rt rtc : List (Nat × Nat)) (H : Janus.Contracts.RtReady) (x : W64) :
    CEnsuresC (Extracted.program.link impl) (CallbackSpec Extracted.tls goFn (G rt (cbk rtc H)) E) Extracted.entry [x]
      (CPre rt rtc H) (fun _ s' => s'.regs 0 = x + 1) := by
  intro ret hret s hs hpre
  obtain ⟨hd, ⟨hal, hb, ha, hw⟩, hra, hrv, hca, hcv, hfb, hfl, hga, hro, hco, hgo, hto, hct, hrt, hcrt, hrtw, hH⟩ := hpre
  have et1 : Extracted.tls.x64Off = janus_eval% Extracted.tls.x64Off := rfl
  have et2 : Extracted.tls.varOff "runtime.tlsg" = janus_eval% (Extracted.tls.varOff "runtime.tlsg") := rfl
  simp only [tlsGSlot, TLSImage.x64Addr, et1, et2] at hH
  simp only [win, cbStackScratch] at hrtw
  have hv : ∀ (m : Janus.Arm64.Memory) a n v, (s.regs 4).toNat - (152 + 16384) ≤ a → a + n ≤ (s.regs 4).toNat →
      Janus.Contracts.rtView rtc (m.writeLE a n v) = Janus.Contracts.rtView rtc m :=
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
      Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega), ⟨by omega, by omega, by omega⟩, hcrt⟩
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
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega


/-! ## Composition: the Go function's theorem discharges the callback assumption -/

theorem frame_lt (S : State) : frameOf S < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Janus.Arm64.Memory.readLE_lt _ _ _) (by decide)

theorem refines (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (Ha : RtReady)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 Ha) (rtc : List (Nat × Nat)) (Hc : RtReady) :
    (CgoCallback Extracted.tls (Extracted.program.link impl) Contract.none (ROK rt Ha) (cbk rtc Hc)).Refines
      (CallbackSpec Extracted.tls goFn (G rt (cbk rtc Hc)) E) := by
  refine CgoCallback.refines (fun a => go_spec impl rt Ha hnew a) (fun S hG => hG.1) (fun S hG => hG.2.1) ?_
    (fun _ _ => rfl) ?_ ?_
  · rintro S u ret ⟨-, -, hb, hacc, hout, hcrt⟩ he hR
    have hf : (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    have hst := he.goStack
    have hsep := he.stackSep _ _ _ hacc
    have hgo := he.gOff
    simp only [cbk, gsBox] at hst hsep hgo
    obtain ⟨g1, g2, g3⟩ := hst
    simp only [outside_cons, outside_nil, and_true] at hsep hgo
    unfold GoPre
    rw [hf]
    refine ⟨he.guardOK (by simp only [cbk, gsBox, Janus.FFI.stackGuard]; decide), g1, g2, g3, ?_, hb,
      he.keptAcc _ _ _ ⟨hacc, hout⟩, ?_, hcrt _ _ _ hacc, hR⟩
    · simp only [outside_cons, outside_nil, and_true, gsBox, gStructSize] at hgo ⊢; omega
    · simp only [outside_cons, outside_nil, and_true, gsBox]; omega
  · rintro S u ret u' ⟨-, -, hb, hacc, hout, hcrt⟩ he - - hpost b hb' hbacc
    have hf : (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 16) 8)).toNat = frameOf S := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (frame_lt S)
    unfold GoPost at hpost
    rw [hf] at hpost
    have hsep := he.stackSep _ _ _ hbacc
    simp only [cbk] at hsep
    have h1 := hpost.readLE b 1 (by
      simp only [outside_append]; exact ⟨hcrt _ _ _ hbacc, hsep⟩)
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
  · rintro S ⟨-, -, hb, hacc, hout, -⟩ b _ hna
    rw [E, Janus.Arm64.Memory.bytes_writeLE, ite_eq_right]
    intro ⟨h1, h2⟩
    have := Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (a := b) (n := 1) (by omega) (by omega)
    rw [this] at hna; cases hna

/-- **`e_callbox` end to end** (amd64): under the trusted `cgocallback` contract (with the
allocator's readiness `ROK rt Ha` at the Go entry) and the allocation contract `hnew`, for every
runtime memory `rt`, `rtc` and readinesses `Ha`, `Hc`, the call returns `x + 1`. -/
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (Ha : RtReady)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 Ha)
    (rtc : List (Nat × Nat)) (Hc : RtReady) (x : W64) :
    CEnsuresC (Extracted.program.link impl)
      (CgoCallback Extracted.tls (Extracted.program.link impl) Contract.none (ROK rt Ha) (cbk rtc Hc))
      Extracted.entry [x] (CPre rt rtc Hc) (fun _ s' => s'.regs 0 = x + 1) :=
  (c_spec impl rt rtc Hc x).refine (refines impl rt Ha hnew rtc Hc)


namespace Witness

open Janus.Contracts.AllocSat (heap HeapReady le_blockSize)
open Janus.Contracts.AllocSatAmd64 (heapCode ret_of)

/-! ### An allocator: `AllocSatAmd64`'s toy at `runtime.newobject`'s address -/

/-- `runtime.newobject`'s address. -/
abbrev cA : Nat := Extracted.program.contractAddr "runtime.newobject"
/-- The toy allocator (`MOV EAX, 0x10000`; `RET`: it returns `heap`) at that address. -/
def implAt : List Amd64.Segment := [{ name := "model", base := cA, bytes := heapCode }]
/-- The program linked with it, as a closed program. -/
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl
/-- The runtime-owned memory: the toy heap and `box`'s type descriptor. -/
def rtW : List (Nat × Nat) := [(heap, heap + 0x10000), (boxType, boxType + 16)]
/-- The allocator's readiness: the heap writable and zero, the request `[boxType]`, an 8-byte
type, all as the runtime sees them. -/
def HaW : RtReady := fun args _ _ v => HeapReady v ∧ args = [boxType] ∧ typSize v boxType = 8

theorem freshW {m : Janus.Arm64.Memory} {size round : Nat} (zero hdr : Bool)
    (hr : HeapReady (rtView rtW m)) (hsz : size ≤ round) (hround : round ≤ 32768) :
    Fresh rtW m heap size round zero hdr := by
  obtain ⟨hacc, hz⟩ := hr
  rw [rtView_accessible] at hacc
  have hz' := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rtW], Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨⟨(heap, heap + 0x10000), by simp [rtW], Nat.le_refl _, by simp only [heap]; omega⟩,
    by simp only [heap]; omega, Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    fun _ => by decide, fun _ _ => by decide, fun _ => fun i hi => hz' i (by omega), hsz⟩

theorem newobject_impl : NewobjectContract64 (Extracted.program.link implAt) cA rtW 4096 HaW := by
  rw [linked_eq]
  have hc : cA = janus_eval% cA := rfl
  intro s hpc ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, hargs, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  rw [hc] at hpc
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  · have hin : InRanges boxType 16 rtW := ⟨(boxType, boxType + 16), by simp [rtW], Nat.le_refl _, Nat.le_refl _⟩
    unfold typSize at hsz
    rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
    rw [show (BitVec.ofNat 64 heap).toNat = heap from rfl]
    have hsz' : typSize s.mem (s.regs 0).toNat ≤ 32768 := by
      unfold typSize; rw [hargs]; omega
    exact freshW _ _ hr (le_blockSize _ _) (blockSize_le_maxSmallSize _ _ (by simp only [maxSmallSize]; exact hsz'))

/-! ### The C call -/

/-- A byte of the C side's read-only data (`CProg`: without `box`'s type descriptor). -/
def dbyte (a : Nat) : Option Nat :=
  CProg.data.findSome? fun d =>
    if d.base ≤ a ∧ a < d.base + d.bytes.length then d.bytes[a - d.base]? else none

/-- Little-endian byte `j` of `v`. -/
def byteOf (v j : Nat) : Nat := v / 256 ^ j % 256

/-- The witness call: `RSP = SP0` (its slot holding `RET`, where there is no code), `FS = FS0`. -/
def SP0 : Nat := 0x1000008
def FS0 : Nat := 0x800000
def RET : Nat := 0x1000

def cregions : List Janus.Arm64.Region :=
  [⟨rid, 4, true⟩, ⟨ctxf, 8, true⟩, ⟨FS0 - 24, 8, true⟩, ⟨FS0 + 40, 8, false⟩,
     ⟨SP0 - win, win + 8, true⟩] ++
    CProg.data.map fun d => ⟨d.base, d.bytes.length, false⟩

def mem0 : Janus.Arm64.Memory :=
  ⟨fun a => BitVec.ofNat 8 ((dbyte a).getD
      (if a = rid then 2 else if SP0 ≤ a ∧ a < SP0 + 8 then byteOf RET (a - SP0) else 0)),
    cregions⟩

def s0 : State :=
  { regs := fun i => if i = 7 then 7#64 else if i = 4 then BitVec.ofNat 64 SP0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 FS0 }

theorem hret : RetAddr (Extracted.program.link implAt) RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall ((Extracted.program.link implAt).withExit RET) Extracted.entry [7#64] s0 :=
  ⟨rfl, by decide +kernel, by decide, by intro i h; simp at h; subst h; rfl, by decide, rfl⟩

theorem data : CProg.DataLoaded mem0 := by
  unfold Amd64.Program.DataLoaded; decide +kernel

/-- No C memory is runtime-owned: every region is apart from the toy heap and the type
descriptor. -/
theorem apart : ∀ r ∈ cregions, (r.base + r.size ≤ heap ∨ heap + 0x10000 ≤ r.base) ∧
    (r.base + r.size ≤ boxType ∨ boxType + 16 ≤ r.base) := by decide +kernel

theorem notRt : ∀ a n w, mem0.accessible a n w = true → Outside a n rtW := by
  intro a n w h
  obtain ⟨⟨r, hr, h1, h2, -, -⟩, -⟩ := (Janus.Arm64.Memory.accessible_iff mem0 a n w).1 h
  have := apart r hr
  simp only [rtW, outside_cons, outside_nil, and_true]
  omega

set_option maxRecDepth 100000 in
theorem pre : CPre rtW [] (fun _ _ _ _ => True) s0 := by
  refine ⟨data, ?_⟩
  repeat' (first | exact trivial | exact notRt | apply And.intro)
  all_goals first
    | decide +kernel
    | (simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | trivial

/-! ### A Go entry in which the runtime is ready (`ROK`) -/

/-- The Go entry's memory: the toy heap (writable, zero) and `box`'s type descriptor
(`Size_ = 8`, `PtrBytes = 0`), the goroutine stack at `USP`. -/
def USP : Nat := 0x2000000
def umem : Janus.Arm64.Memory :=
  ⟨fun a => if a = boxType then 8 else 0,
    [⟨heap, 0x10000, true⟩, ⟨boxType, 16, false⟩, ⟨USP - gsBox, gsBox + 16, true⟩]⟩

def u0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 USP else 0, rip := 0,
    flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := umem }

theorem rok : ROK rtW HaW u0 := by
  refine ⟨by decide +kernel, ⟨by decide, by decide +kernel⟩, by decide +kernel, by decide +kernel, ?_, ?_,
    ⟨⟨by decide +kernel, fun i hi => ?_⟩, rfl, by decide +kernel⟩⟩
  · simp only [outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [rtW, outside_cons, outside_nil, and_true]; decide +kernel
  · show (if _ then umem.bytes (heap + i) else 0) = 0
    split
    · show (if heap + i = boxType then (8 : Janus.Arm64.Byte) else 0) = 0
      have hb : boxType = janus_eval% boxType := rfl
      rw [if_neg (by rw [hb]; simp only [heap]; omega)]
    · rfl

/-- All hypotheses of `correctness` hold together: an allocator meeting the contract with its
readiness, the C call's precondition, and a Go entry where the callback's readiness `ROK` holds. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (Ha : RtReady)
    (rtc : List (Nat × Nat)) (Hc : RtReady) (x : W64) (ret : Nat) (s : State),
    NewobjectContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 Ha ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CCall ((Extracted.program.link impl).withExit ret) Extracted.entry [x] s ∧ CPre rt rtc Hc s ∧
    ∃ u, ROK rt Ha u :=
  ⟨implAt, rtW, HaW, [], fun _ _ _ _ => True, 7#64, RET, s0, newobject_impl, hret, call, pre, u0, rok⟩

end Witness
end Proof
