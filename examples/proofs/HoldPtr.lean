import Extracted

/-!
# `HoldPtr(x uint64) uint64`: a pointer into its own frame, held across a call that grows the stack (R7)

```go
func holdCallee(p *uint64, x uint64) { var buf [20]uint64; buf[x&15] = x; *p = buf[0] }
func pick(p, q *uint64, x uint64) *uint64 { if x&1 == 0 { return p }; return q }

func HoldPtr(x uint64) uint64 {
	var a [2]uint64
	a[0] = x
	a[1] = x + 1
	p := pick(&a[0], &a[1], x)
	holdCallee(p, x)
	return *p + a[0] + a[1]
}
```

`p = &a[x & 1]` is a pointer into `HoldPtr`'s own frame. The compiler keeps it in the frame slot
`48(RSP)` across the call of `holdCallee`, whose 176-byte frame grows the stack when it is small.
`copystack` then moves `HoldPtr`'s frame and adjusts every pointer into the old stack. Two of
them are this pointer: the slot `48(RSP)`, which `HoldPtr`'s locals map at the call marks
(`localMaps = [[false], [true]]` in `Extracted.frames`), and `holdCallee`'s spilled argument,
which its args map marks (`[true]`).

**Guarantee** (`correctness`). For every frame table that agrees with the binary's frame
records, every stack pool, runtime memory and readiness, and every runtime that meets the
`morestack` contract, `HoldPtr(x)` returns `hres x` on a goroutine stack of any size, whether the
stack grows in its own prologue or in the callee's. `hres x` is `*p + a[0] + a[1]` after the
callee stored `cval x` (`x` when `x & 15 = 0`, else `0`) at `a[x & 1]`.

**How.**
* `gcallee` is `holdCallee`'s grown summary. On the growth path (`cgrow`), the glue reloads `p`
  *adjusted*, so the callee's store reaches the moved array. `PostC` states the move of the
  caller's frames together with that store.
* `hroomH` reads the frame back after the call on the moved stack: `p` adjusted (`Moved.readLE_ptr`
  on the locals-map slot), `*p` the callee's store, the other element of `a` copied.
* `hgrow` covers `HoldPtr`'s own growth.

The witness (`Witness.callee_grows`) is a call whose frame fits but whose callee's does not.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Stack Janus.Contracts
  Janus.Contracts.Stack

namespace Proof


/-- `holdCallee`'s entry and its glue after the `morestack` call (`LDP 8(RSP), (R0, R1)`). -/
abbrev cE : Nat := janus_eval% (segAddr Extracted.program "example.com/basic.holdCallee")
abbrev cGlue : Nat := cE + 0x70

theorem cbody : ∀ t : State, t.pc = BitVec.ofNat 64 cE →
    (t.regs 30).toNat % 4 = 0 → (t.regs 30).toNat < 2 ^ 56 →
    (t.regs 28).toNat + 24 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 28).toNat + 16) 8 false = true →
    t.mem.readLE ((t.regs 28).toNat + 16) 8 + 48 < t.sp.toNat → t.sp.toNat % 16 = 0 →
    184 ≤ t.sp.toNat → t.sp.toNat ≤ 2 ^ 48 → t.mem.accessible (t.sp.toNat - 184) 176 true = true →
    t.regs 29 = t.sp - 8 →
    t.mem.accessible (t.regs 0).toNat 8 true = true → (t.regs 0).toNat + 8 ≤ 2 ^ 48 →
    (t.sp.toNat ≤ (t.regs 0).toNat ∨ (t.regs 0).toNat + 8 ≤ t.sp.toNat - 184) →
    ReachesRet Extracted.program (t.regs 30) t (fun t' => t'.sp = t.sp ∧ t'.regs 29 = t.regs 29 ∧
      t'.regs 28 = t.regs 28 ∧ t'.regs 18 = t.regs 18 ∧ t'.mem.regions = t.mem.regions ∧
      MemFrame t.mem t'.mem [(t.sp.toNat - 184, t.sp.toNat - 8), ((t.regs 0).toNat, (t.regs 0).toNat + 8)] ∧
      t'.mem.readLE (t.regs 0).toNat 8 = if (t.regs 1).toNat % 16 = 0 then (t.regs 1).toNat else 0) := by
  intro t hpc h1 h2 h3 h4 h5 h6 h7 h8 h9 hfp hp1 hp2 hp3
  have hlt : (t.regs 1).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  by_cases hz : (t.regs 1).toNat % 16 = 0
  · janus_run
    all_goals first | janus_frame | exact ⟨by janus_frame, by rw [if_pos hz]⟩
  · janus_run
    all_goals first | janus_frame | exact ⟨by janus_frame, by rw [if_neg hz]⟩

theorem cglue : ∀ t : State, t.pc = BitVec.ofNat 64 cGlue →
    t.mem.accessible (t.sp.toNat + 8) 16 false = true → t.sp.toNat + 24 ≤ 2 ^ 48 →
    t.sp.toNat % 16 = 0 →
    ReachesRet Extracted.program (BitVec.ofNat 64 cE) t (fun t' =>
      t'.pc = BitVec.ofNat 64 cE ∧ t'.sp = t.sp ∧ t'.mem = t.mem ∧
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat + 8) 8) ∧
      t'.regs 1 = BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat + 16) 8) ∧
      (∀ r, r ≠ 0 → r ≠ 1 → t'.regs r = t.regs r)) := by
  intro t hpc hacc hsp hal
  janus_run until [cE]
  all_goals first
    | (intro r h0 h1; simp [h0, h1])
    | exact ReachesRet.done rfl ⟨rfl, rfl, rfl, by simp [setReg], by simp [setReg],
        fun r h0 h1 => by simp [setReg, h0, h1]⟩

/-- The binary's frame record of `holdCallee`, at its glue: no frame, largest frame 176 bytes,
`p` a pointer argument (the args map `[true]`), no stack objects. -/
def CTable (FT : FrameTable) : Prop :=
  FT.valid cGlue = true ∧ FT.stop cGlue = false ∧ FT.injected cGlue = false ∧
  FT.spdelta cGlue = 0 ∧ FT.maxspd cGlue = 176 ∧ FT.args cGlue = [true] ∧ FT.objs cGlue = []

theorem ctable_of {FT : FrameTable} (h : FT.Agrees Extracted.frames) : CTable FT := by
  obtain ⟨a1, -, a3, a4, a5, a6, -, a8, a9⟩ :=
    h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) cGlue (by decide) (by decide)
  refine ⟨a1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a5] <;> rfl
  · rw [a6] <;> rfl
  · rw [a3] <;> rfl
  · rw [a4] <;> rfl
  · rw [a8] <;> rfl
  · rw [a9] <;> rfl

/-- At the glue, `holdCallee`'s frame (`SP = fp = sp`) marks its spilled pointer argument. -/
theorem cframe0 {FT : FrameTable} (hT : CTable FT) (sp a : Nat) :
    frameCls Arch.arm64 FT cGlue sp sp a = (a == sp + 8) := by
  obtain ⟨-, -, -, -, -, ha, ho⟩ := hT
  have hv : Arch.arm64.varp sp sp = sp := by simp [Arch.varp]
  simp only [frameCls, hv, Arch.argp, ho, ha, List.any_nil, Bool.or_false]
  have e1 : decide (sp + 8 = sp + 16) = false := decide_eq_false (by omega)
  have e2 : decide (Arch.arm64.minLocals + sp < sp) = false :=
    decide_eq_false (by unfold Arch.minLocals; omega)
  rw [e1, e2, Bool.false_and, Bool.false_and, Bool.false_or, Bool.false_or]
  simp only [bitsAt]
  by_cases e : a = sp + 8
  · subst e; simp
  · have : ¬ (((sp + 8 : Nat) : Int) ≤ (a : Int) ∧ (((a : Int) - ((sp + 8 : Nat) : Int)).toNat % 8 = 0) ∧
        (((a : Int) - ((sp + 8 : Nat) : Int)).toNat / 8 = 0)) := by omega
    cases h1 : decide (((sp + 8 : Nat) : Int) ≤ (a : Int)) <;>
      cases h2 : (((a : Int) - ((sp + 8 : Nat) : Int)).toNat % 8 == 0) <;> simp_all <;>
      (rw [List.getD_eq_getElem?_getD]; cases hj : [true][((a : Int) - ((sp + 8 : Nat) : Int)).toNat / 8]? <;>
        simp_all [List.getElem?_cons]) <;> omega

/-- The result of the callee: `buf[0]`, `x` when `x & 15 = 0`, else `0`. -/
def cval (x : Nat) : Nat := if x % 16 = 0 then x else 0

/-- The callee's environment: the frame table agrees with the binary's frame records, the laws of
every pclntab, and the stack pools apart from the runtime memory. -/
def Env (FT : FrameTable) (pool rt : List (Nat × Nat)) : Prop :=
  FT.Agrees Extracted.frames ∧ FT.InFrame Arch.arm64 ∧ FT.Aligned ∧ FT.CodeOutside pool ∧
    (∀ a n, InRanges a n pool → Outside a n rt)

/-- The precondition of a call `holdCallee(p, x)`: the goroutine stack, the caller's walk (its
maps do not mark the two argument slots), `p` an 8-aligned word of the caller's region of the
stack, the `maxstacksize` bound, the readiness. -/
def PreC (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s : State) : Prop :=
  ∃ lo hi, GStack s.mem (s.regs 28).toNat lo hi ∧ Outside (s.regs 28).toNat 24 pool ∧
    4096 ≤ lo ∧ lo + 8 ≤ s.sp.toNat ∧ s.sp.toNat + 24 ≤ hi ∧ hi ≤ 2 ^ 48 ∧
    lo % 16 = 0 ∧ hi % 16 = 0 ∧ s.sp.toNat % 16 = 0 ∧ s.regs 29 = s.sp - 8 ∧
    InRanges lo (hi - lo) pool ∧ PoolOK s.mem pool ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
    (∃ fs, Chain Arch.arm64 FT s.mem hi (s.regs 30).toNat s.sp.toNat none fs ∧
      (∀ f ∈ fs, f.sp = s.sp.toNat ∨ s.sp.toNat + 24 ≤ f.sp) ∧
      framesCls Arch.arm64 FT fs (s.sp.toNat + 8) = false ∧
      framesCls Arch.arm64 FT fs (s.sp.toNat + 16) = false) ∧
    (s.regs 0).toNat % 8 = 0 ∧ s.sp.toNat + 24 ≤ (s.regs 0).toNat ∧ (s.regs 0).toNat + 8 ≤ hi ∧
    2 * ((hi - s.sp.toNat) + 176 + 976) ≤ maxstacksize ∧
    H [] (s.regs 28).toNat 0 (rtView rt s.mem)

/-- What `holdCallee(p, x)` does, through a possible stack growth: it returns with the stack
`[lo, hi)` grown to `[lo', hi')`, `SP`/`X29` moved, the caller's frames moved (`Moved` along the
caller's walk, the argument slots and the word at `p` free), and `cval x` at the moved `p`. -/
def PostC (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s s' : State) : Prop :=
  ∃ lo hi lo' hi', GStack s.mem (s.regs 28).toNat lo hi ∧ GStack s'.mem (s.regs 28).toNat lo' hi' ∧
    hi - lo ≤ hi' - lo' ∧ 4096 ≤ lo' ∧ lo' % 16 = 0 ∧ hi' % 16 = 0 ∧ hi' ≤ 2 ^ 48 ∧
    InRanges lo' (hi' - lo') pool ∧
    s'.sp = BitVec.ofNat 64 (s.sp.toNat + hi' - hi) ∧
    s'.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 8 + hi' - hi) ∧
    s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
    (∀ fs, Chain Arch.arm64 FT s.mem hi (s.regs 30).toNat s.sp.toNat none fs →
      Moved (fun a => decide (a = s.sp.toNat - 8) || framesCls Arch.arm64 FT fs a) pool lo hi hi'
        (s.sp.toNat - 8) [(s.sp.toNat + 8, s.sp.toNat + 24), ((s.regs 0).toNat, (s.regs 0).toNat + 8)]
        s.mem s'.mem) ∧
    s'.mem.readLE ((s.regs 0).toNat + hi' - hi) 8 = cval (s.regs 1).toNat ∧
    MemFrame s.mem s'.mem (pool ++ rt) ∧ H [] (s.regs 28).toNat 0 (rtView rt s'.mem)

/-- `holdCallee` on a stack where its frame fits. -/
theorem croom (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (henv : Env FT pool rt) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 cE) (hp : PreC FT pool rt H s)
    (hroom : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 48 < s.sp.toNat) :
    GrownRet Extracted.program reloc (s.regs 30) s (PostC FT pool rt H s) := by
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hfp, hinp, hpok, hr4, hr48,
    ⟨fs, hch, hfsp, hc8, hc16⟩, hp8, hp1, hp2, hfit, hH⟩ := hp
  obtain ⟨-, -, -, -, hPA⟩ := henv
  have hgs' := hgs
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
  have hacc := hpok.accessible hinp
  have hspL : lo + 928 + 48 < s.sp.toNat := by rw [hgg] at hroom; exact hroom
  have hsp64 := s.sp.isLt
  obtain ⟨k, t, hst, hpc', hsp', h29', h28', h18', hreg, hmf, hv⟩ := cbody s hpc hr4 (by omega) hg24
    (Memory.accessible_mono _ hgacc (by omega) (by omega)) hroom hal3 (by omega) (by omega)
    (Memory.accessible_mono _ hacc (by omega) (by omega)) hfp
    (Memory.accessible_mono _ hacc (by omega) (by omega)) (by omega) (.inl (by omega))
  have hin : ∀ a n, lo ≤ a → a + n ≤ hi → InRanges a n pool := fun a n h1 h2 => hinp.sub h1 (by omega)
  have hmf' : MemFrame s.mem t.mem (pool ++ rt) := hmf.mono fun a n h => by
    simp only [outside_append] at h
    have e1 := InRanges.disjoint (hin (s.sp.toNat - 184) 176 (by omega) (by omega)) h.1
    have e2 := InRanges.disjoint (hin (s.regs 0).toNat 8 (by omega) (by omega)) h.1
    simp only [outside_cons, outside_nil, and_true]; omega
  refine .done hst hpc' ⟨lo, hi, lo, hi, hgs, GStack.of_frame hgs hmf ?_, Nat.le_refl _, h4k, hal1,
    hal2, hhi48, hinp, ?_, ?_, h28', h18', fun fs0 _ => ?_, by rw [Nat.add_sub_cancel]; exact hv, hmf', ?_⟩
  · have e1 := InRanges.disjoint (hin (s.sp.toNat - 184) 176 (by omega) (by omega)) hgo
    have e2 := InRanges.disjoint (hin (s.regs 0).toNat 8 (by omega) (by omega)) hgo
    simp only [outside_cons, outside_nil, and_true]; omega
  · rw [hsp', Nat.add_sub_cancel, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [h29', hfp, Nat.add_sub_cancel]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  · refine Moved.of_agree _ pool ⟨by omega, by omega⟩ h4k (by omega) (by omega) fun a h1 h2 hx => ?_
    simp only [outside_cons, outside_nil, and_true] at hx
    exact hmf.bytes (by simp only [outside_cons, outside_nil, and_true]; omega)
  · rw [rtView_eq_of_frame hmf hreg fun a ha => ?_]
    · exact hH
    · have e1 := InRanges.disjoint ha (hPA _ _ (hin (s.sp.toNat - 184) 176 (by omega) (by omega)))
      have e2 := InRanges.disjoint ha (hPA _ _ (hin (s.regs 0).toNat 8 (by omega) (by omega)))
      simp only [outside_cons, outside_nil, and_true]; omega

set_option maxHeartbeats 2000000 in
/-- `holdCallee`'s growth path: the contract moves the stack, the glue reloads `p` adjusted (a
pointer argument) and `x` copied, the frame now fits (`croom`), and the moves compose. -/
theorem cgrow (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (s : State) (lo hi : Nat) (hgs : GStack s.mem (s.regs 28).toNat lo hi)
    (hgo : Outside (s.regs 28).toNat 24 pool) (h4k : 4096 ≤ lo) (hlo : lo + 8 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 24 ≤ hi) (hhi48 : hi ≤ 2 ^ 48) (hal1 : lo % 16 = 0) (hal2 : hi % 16 = 0)
    (hal3 : s.sp.toNat % 16 = 0) (hfp : s.regs 29 = s.sp - 8) (hinp : InRanges lo (hi - lo) pool)
    (hpok : PoolOK s.mem pool) (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    (fs : List Frame) (hch : Chain Arch.arm64 FT s.mem hi (s.regs 30).toNat s.sp.toNat none fs)
    (hfsp : ∀ f ∈ fs, f.sp = s.sp.toNat ∨ s.sp.toNat + 24 ≤ f.sp)
    (hc8 : framesCls Arch.arm64 FT fs (s.sp.toNat + 8) = false)
    (hc16 : framesCls Arch.arm64 FT fs (s.sp.toNat + 16) = false)
    (hp8 : (s.regs 0).toNat % 8 = 0) (hp1 : s.sp.toNat + 24 ≤ (s.regs 0).toNat)
    (hp2 : (s.regs 0).toNat + 8 ≤ hi)
    (hfit : 2 * ((hi - s.sp.toNat) + 176 + 976) ≤ maxstacksize)
    (s_m : State) (hm : MorestackPre Extracted.program FT pool rt H (s.regs 28).toNat lo hi s_m)
    (hglue : s_m.regs 30 = BitVec.ofNat 64 cGlue) (hx3 : s_m.regs 3 = s.regs 30)
    (hsp_m : s_m.sp = s.sp) (h28 : s_m.regs 28 = s.regs 28) (h18 : s_m.regs 18 = s.regs 18)
    (hmem : s_m.mem = (s.mem.writeLE (s.sp.toNat + 8) 8 (s.regs 0).toNat).writeLE (s.sp.toNat + 16) 8
      (s.regs 1).toNat)
    (hchm : Chain Arch.arm64 FT s_m.mem hi (s_m.regs 30).toNat s_m.sp.toNat (some (s_m.regs 3).toNat)
      (⟨cGlue, s.sp.toNat, Arch.arm64.fp FT cGlue s.sp.toNat⟩ :: fs)) :
    ∃ s_r, reloc s_m s_r ∧ GrownRet Extracted.program reloc (s.regs 30) s_r (PostC FT pool rt H s) := by
  have henv' := henv
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
  have hT := ctable_of hA
  obtain ⟨s_r, lo1, hi1, hre, hgr⟩ := hms _ lo hi s_m hm
  refine ⟨s_r, hre, ?_⟩
  obtain ⟨hg1, hg2, h4k1, hal1', hal2', hhi48', hinp1, happ⟩ := hgr.grows
  have hroom := hgr.room
  have hT0 := hT
  obtain ⟨-, -, -, hspd, hmx, -, -⟩ := hT0
  have hgl : (s_m.regs 30).toNat = cGlue := by rw [hglue]; rfl
  rw [hgl, hmx, hsp_m] at hroom
  simp only [stackGuard] at hroom
  have hsp := s.sp.isLt
  have hspm : s_m.sp.toNat = s.sp.toNat := by rw [hsp_m]
  have hsp_r : s_r.sp.toNat = s.sp.toNat + hi1 - hi := by
    rw [hgr.sp, hspm, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hpok_r : PoolOK s_r.mem pool := hm.inPool.2.of_accessible hgr.frame.accessible
  have hacc_r : s_r.mem.accessible lo1 (hi1 - lo1) true = true := hpok_r.accessible hinp1
  obtain ⟨k, s_e, hst, hepc, -, hesp, hemem, he0, he1, her⟩ := cglue s_r (hgr.pc.trans hglue)
    (Memory.accessible_read_of_write _ (Memory.accessible_mono _ hacc_r (by omega) (by omega)))
    (by omega) (by omega)
  have he30 : s_e.regs 30 = s.regs 30 := by rw [her 30 (by decide) (by decide), hgr.lr, hx3]
  have he28 : s_e.regs 28 = s.regs 28 := by rw [her 28 (by decide) (by decide), hgr.gkeep.1, h28]
  have he18 : s_e.regs 18 = s.regs 18 := by rw [her 18 (by decide) (by decide), hgr.gkeep.2, h18]
  have he29 : s_e.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 8 + hi1 - hi) := by
    rw [her 29 (by decide) (by decide), hgr.regs 29 rfl, hm.fp, hspm]
  have hesp' : s_e.sp.toNat = s.sp.toNat + hi1 - hi := by rw [hesp, hsp_r]
  have hfp0 : Arch.arm64.fp FT cGlue s.sp.toNat = s.sp.toNat := by simp [Arch.fp, hspd]
  have hmA := hgr.moved _ hchm
  rw [hspm] at hmA
  have hclsA : ∀ a, moveCls FT s.sp.toNat (⟨cGlue, s.sp.toNat, Arch.arm64.fp FT cGlue s.sp.toNat⟩ :: fs) a =
      (decide (a = s.sp.toNat - 8) || (a == s.sp.toNat + 8) || framesCls Arch.arm64 FT fs a) := by
    intro a; simp only [moveCls, framesCls_cons, hfp0, cframe0 hT, Bool.or_assoc]
  -- the memory at the call
  have hmx0 : s_m.mem.readLE (s.sp.toNat + 8) 8 = (s.regs 0).toNat := by
    rw [hmem, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 0).isLt
  have hmx1 : s_m.mem.readLE (s.sp.toNat + 16) 8 = (s.regs 1).toNat := by
    rw [hmem, Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (s.regs 1).isLt
  -- the caller's walk, in the memory at the call and after the move
  have hfb := hch.bounds
  have hchs : Chain Arch.arm64 FT s_m.mem hi (s.regs 30).toNat s.sp.toNat none fs :=
    Chain.congr hch (by omega) fun f hf _ => by
      obtain ⟨h1, -⟩ := hfb f hf
      rw [hmem, Memory.readLE_writeLE_of_disjoint _ _ (by
          simp only [Arch.lrSlot]; rcases hfsp f hf with h | h <;> omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by
          simp only [Arch.lrSlot]; rcases hfsp f hf with h | h <;> omega)]
  have hche : Chain Arch.arm64 FT s_e.mem hi1 (s_e.regs 30).toNat s_e.sp.toNat none
      (fs.map (Frame.mv hi hi1)) := by
    rw [hemem, he30, hesp']
    exact hchs.moved hmA hCO hAl (by omega) (by omega) fun _ _ _ => trivial
  have hcl : ∀ a, hi ≤ a + hi1 → framesCls Arch.arm64 FT (fs.map (Frame.mv hi hi1)) (a + hi1 - hi) =
      framesCls Arch.arm64 FT fs a := fun a ha => hch.framesCls_mv (by omega) (by omega) ha
  -- the arguments read back: `p` adjusted, `x` copied
  have hp_e : (s_e.regs 0).toNat = (s.regs 0).toNat + hi1 - hi := by
    rw [he0, hsp_r, show s.sp.toNat + hi1 - hi + 8 = (s.sp.toNat + 8) + hi1 - hi by omega,
      hmA.readLE_ptr (by omega) (by omega) (by omega) (by rw [hclsA]; simp) trivial
        (by rw [hmx0]; omega) (by rw [hmx0]; omega), hmx0, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hx_e : (s_e.regs 1).toNat = (s.regs 1).toNat := by
    rw [he1, hsp_r, show s.sp.toNat + hi1 - hi + 16 = (s.sp.toNat + 16) + hi1 - hi by omega,
      hmA.readLE_scalar (by omega) (by omega) (fun j hj => by
        rw [show s.sp.toNat + 16 + j - (s.sp.toNat + 16 + j) % 8 = s.sp.toNat + 16 by omega, hclsA, hc16]
        simp; omega) trivial, hmx1, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (s.regs 1).isLt
  obtain ⟨-, -, hge3, hge4, hge5⟩ := hgr.gstack
  simp only [gStackguard0, stackGuard] at hge5
  -- the precondition on the new stack, which has room
  have hpe : PreC FT pool rt H s_e := by
    refine ⟨lo1, hi1, by rw [he28, hemem, ← h28, hm.greg]; exact hgr.gstack, by rw [he28]; exact hgo,
      h4k1, by omega, by omega, hhi48', hal1', hal2', by omega, ?_, hinp1, by rw [hemem]; exact hpok_r,
      by rw [he30]; exact hr4, by rw [he30]; exact hr48, ⟨_, hche, fun f hf => ?_, ?_, ?_⟩,
      by rw [hp_e]; omega, by rw [hp_e, hesp']; omega, by rw [hp_e]; omega,
      by rw [hesp', show hi1 - (s.sp.toNat + hi1 - hi) = hi - s.sp.toNat by omega]; exact hfit, ?_⟩
    · rw [he29, hesp]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, hsp_r, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · obtain ⟨f0, hf0, rfl⟩ := List.mem_map.1 hf
      obtain ⟨h1, -⟩ := hfb f0 hf0
      simp only [Frame.mv]; rw [hesp']; rcases hfsp f0 hf0 with h | h <;> omega
    · rw [hesp', show s.sp.toNat + hi1 - hi + 8 = (s.sp.toNat + 8) + hi1 - hi by omega, hcl _ (by omega)]
      exact hc8
    · rw [hesp', show s.sp.toNat + hi1 - hi + 16 = (s.sp.toNat + 16) + hi1 - hi by omega, hcl _ (by omega)]
      exact hc16
    · rw [he28, hemem, ← h28, hm.greg]; exact hgr.ready
  have hroome : s_e.mem.readLE ((s_e.regs 28).toNat + 16) 8 + 48 < s_e.sp.toNat := by
    rw [he28, hemem, ← h28, hm.greg, hge5, hesp']; omega
  refine GrownRet.of_steps hst ?_
  rw [← he30]
  refine (croom FT pool rt H reloc henv s_e hepc hpe hroome).mono fun s'' hq => ?_
  obtain ⟨loe, hie, lo2, hi2, hgse, hgs2, hsz, h4k2, hal12, hal22, hhi482, hinp2, hsp2, h292,
    h282, h182, hmB, hv2, hmf, hH2⟩ := hq
  obtain ⟨e1, e2⟩ := GStack.unique (by rw [he28, hemem, ← h28, hm.greg]; exact hgr.gstack) hgse
  subst e1 e2
  have esp : s_e.sp.toNat + hi2 - hi1 = s.sp.toNat + hi2 - hi := by rw [hesp']; omega
  have efp : s_e.sp.toNat - 8 + hi2 - hi1 = s.sp.toNat - 8 + hi2 - hi := by rw [hesp']; omega
  refine ⟨lo, hi, lo2, hi2, hgs, by rw [← he28]; exact hgs2, by omega, h4k2, hal12, hal22, hhi482, hinp2,
    by rw [hsp2, esp], by rw [h292, efp], by rw [h282, he28], by rw [h182, he18], ?_, ?_, ?_,
    by rw [← he28]; exact hH2⟩
  · intro fs0 hfs0
    rw [Chain.unique hfs0 hch]
    have hmB' := hmB _ hche
    rw [hesp', hemem, hp_e] at hmB'
    have hB : Moved (fun a => decide (a = s.sp.toNat + hi1 - hi - 8) ||
        framesCls Arch.arm64 FT (fs.map (Frame.mv hi hi1)) a) pool lo1 hi1 hi2
        (s.sp.toNat - 8 + hi1 - hi) [(s.sp.toNat + hi1 - hi + 8, s.sp.toNat + hi1 - hi + 24),
          ((s.regs 0).toNat + hi1 - hi, (s.regs 0).toNat + hi1 - hi + 8)] s_r.mem s''.mem := by
      rw [show s.sp.toNat - 8 + hi1 - hi = s.sp.toNat + hi1 - hi - 8 by omega]; exact hmB'
    have ex3al : ∀ r ∈ [(s.sp.toNat + 8, s.sp.toNat + 24), ((s.regs 0).toNat, (s.regs 0).toNat + 8)],
        r.1 % 8 = 0 ∧ r.2 % 8 = 0 := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp <;> omega
    have hA1 := (hmA.mono_ex' (ex' := [(s.sp.toNat + 8, s.sp.toNat + 24), ((s.regs 0).toNat, (s.regs 0).toNat + 8)])
      fun _ _ _ _ => trivial).cls_congr' (cls' := fun a => decide (a = s.sp.toNat - 8) ||
        framesCls Arch.arm64 FT fs a) ex3al fun a _ _ _ hx => by
      simp only [outside_cons, outside_nil, and_true] at hx
      rw [hclsA]
      have : (a == s.sp.toNat + 8) = false := by simp; omega
      rw [this, Bool.or_false]
    have hAB := hA1.trans' (ex₃ := [(s.sp.toNat + 8, s.sp.toNat + 24), ((s.regs 0).toNat, (s.regs 0).toNat + 8)]) hB
      (fun a ha _ => by
        rw [hcl a (by omega)]
        congr 1
        exact Bool.eq_iff_iff.2 (by simp only [decide_eq_true_eq]; omega))
      (by omega)
      (fun a k ha hx => ⟨hx, by
        simp only [outside_cons, outside_nil, and_true] at hx ⊢; omega⟩)
    refine hAB.congr_src fun a ha _ hx => ?_
    simp only [outside_cons, outside_nil, and_true] at hx
    rw [hmem, Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega)]
  · rw [show (s.regs 0).toNat + hi2 - hi = (s_e.regs 0).toNat + hi2 - hi1 by rw [hp_e]; omega, hv2, hx_e]
  · refine MemFrame.trans ?_ (hemem ▸ hmf) fun a k h => ⟨h, h⟩
    refine MemFrame.trans ?_ hgr.frame fun a k h => ⟨h, h⟩
    rw [hmem]
    exact ((MemFrame.refl s.mem _).writeLE_inRanges _ ((hinp.sub (by omega) (by omega)).append_left rt)).writeLE_inRanges _
      ((hinp.sub (by omega) (by omega)).append_left rt)

/-- **`holdCallee` through a possible stack growth, as a grown callee summary.** -/
theorem gcallee (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) :
    GSummary Extracted.program reloc cE (PreC FT pool rt H) (PostC FT pool rt H) := by
  intro s hpc hpre
  by_cases hroom : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 48 < s.sp.toNat
  · exact croom FT pool rt H reloc henv s hpc hpre hroom
  · have hpre' := hpre
    obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hfp, hinp, hpok, hr4, hr48,
      ⟨fs, hch, hfsp, hc8, hc16⟩, hp8, hp1, hp2, hfit, hH⟩ := hpre'
    have henv' := henv
    obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
    have hT := ctable_of hA
    have hT0 := hT
    obtain ⟨hv, hst, hinj, hspd, hmx, -, -⟩ := hT0
    have hgs' := hgs
    obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
    simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
    have hacc := hpok.accessible hinp
    have hfit1 : 2 * (hi - lo) ≤ maxstacksize := by
      have h' := hfit; have hr := hroom; rw [hgg] at hr; omega
    have hfit2 : 2 * ((hi - s.sp.toNat) + 176 + stackGuard) ≤ maxstacksize := by
      exact Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_left (by decide : stackGuard ≤ 976) _)) hfit
    obtain ⟨mm, hmm⟩ : ∃ mm, mm = (s.mem.writeLE (s.sp.toNat + 8) 8 (s.regs 0).toNat).writeLE
        (s.sp.toNat + 16) 8 (s.regs 1).toNat := ⟨_, rfl⟩
    have hfp0 : Arch.arm64.fp FT cGlue s.sp.toNat = s.sp.toNat := by simp [Arch.fp, hspd]
    have hcm : Chain Arch.arm64 FT mm hi (s.regs 30).toNat s.sp.toNat none fs :=
      Chain.congr hch (by omega) fun f hf _ => by
        obtain ⟨h1, -⟩ := hch.bounds f hf
        rw [hmm, Memory.readLE_writeLE_of_disjoint _ _ (by
            simp only [Arch.lrSlot]; rcases hfsp f hf with h | h <;> omega),
          Memory.readLE_writeLE_of_disjoint _ _ (by
            simp only [Arch.lrSlot]; rcases hfsp f hf with h | h <;> omega)]
    have hchain : Chain Arch.arm64 FT mm hi cGlue s.sp.toNat (some (s.regs 30).toNat)
        (⟨cGlue, s.sp.toNat, Arch.arm64.fp FT cGlue s.sp.toNat⟩ :: fs) := by
      refine .cons hv hst hinj (by omega) (by rw [hfp0]; omega) ?_
      rw [hfp0]; simpa [Arch.lrOf] using hcm
    apply GrownRet.of_reaches_stub
    janus_run
    rw [← hmm]
    have e30 : (BitVec.ofNat 64 cGlue).toNat = cGlue := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by decide)
    refine cgrow FT pool rt H reloc hms henv s lo hi hgs hgo h4k hlo hhi hhi48 hal1 hal2 hal3 hfp hinp
      hpok hr4 hr48 fs hch hfsp hc8 hc16 hp8 hp1 hp2 hfit _
      ⟨⟨"runtime.morestack_noctxt.abi0", rfl⟩, by simp [setReg, regG], ?_, hgo,
        ⟨h4k, hlo, show s.sp.toNat + 8 ≤ hi by omega, hhi48⟩, ⟨hal1, hal2, hal3⟩, ?_,
        ⟨hinp, hpok.of_accessible fun a k w => by
          rw [hmm, Memory.accessible_writeLE, Memory.accessible_writeLE]⟩,
        ⟨⟨cGlue, s.sp.toNat, Arch.arm64.fp FT cGlue s.sp.toNat⟩ :: fs, ?_⟩, ⟨hfit1, ?_⟩,
        ⟨hCO, hAl⟩, ?_⟩ ?_ ?_ rfl ?_ ?_ ?_ ?_
    · rw [hmm]
      exact GStack.writeLE (GStack.writeLE hgs hgo (hinp.sub (by omega) (by omega))) hgo
        (hinp.sub (by omega) (by omega))
    · show (s.regs 29).toNat = s.sp.toNat - 8
      rw [hfp, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · show Chain Arch.arm64 FT mm hi (BitVec.ofNat 64 cGlue).toNat s.sp.toNat
        (some ((setReg (setReg (setReg (setReg s.regs 3 (s.regs 30)) 16
          (BitVec.ofNat 64 (s.mem.readLE ((s.regs 28).toNat + 16) 8))) 17 (s.sp - 48))
          30 (BitVec.ofNat 64 cGlue)) 3).toNat) _
      rw [e30]; simpa [setReg_apply] using hchain
    · show 2 * ((hi - s.sp.toNat) + FT.maxspd (BitVec.ofNat 64 cGlue).toNat + stackGuard) ≤ maxstacksize
      rw [e30, hmx]; exact hfit2
    · show H [] _ 0 (rtView rt mm)
      rw [hmm, rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega)))]
      simpa [setReg, regG] using hH
    · simp [setReg] <;> rfl
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · exact hmm
    · show Chain Arch.arm64 FT mm hi (BitVec.ofNat 64 cGlue).toNat s.sp.toNat
        (some ((setReg (setReg (setReg (setReg s.regs 3 (s.regs 30)) 16
          (BitVec.ofNat 64 (s.mem.readLE ((s.regs 28).toNat + 16) 8))) 17 (s.sp - 48))
          30 (BitVec.ofNat 64 cGlue)) 3).toNat) _
      rw [e30]; simpa [setReg_apply] using hchain



theorem lsb (x : BitVec 64) : (x.getLsbD 0 == true) = true ↔ x.toNat % 2 = 1 := by
  simp [BitVec.getLsbD, Nat.testBit, Nat.one_and_eq_mod_two]

/-- `p = &a[x & 1]`, as returned by `pick`. -/
def pN (t : State) : Nat := if (t.regs 0).toNat % 2 = 0 then t.sp.toNat - 32 else t.sp.toNat - 24

/-- The memory at the `holdCallee` call: the frame push, the spilled `x`, `a = [x, x + 1]` and `p`. -/
def M1 (t : State) : Memory :=
  (((((t.mem.writeLE (t.sp.toNat - 64) 8 (t.regs 30).toNat).writeLE (t.sp.toNat - 72) 8
    (t.regs 29).toNat).writeLE (t.sp.toNat + 8) 8 (t.regs 0).toNat).writeLE (t.sp.toNat - 32) 8
    (t.regs 0).toNat).writeLE (t.sp.toNat - 24) 8 ((t.regs 0).toNat + 1)).writeLE (t.sp.toNat - 16) 8 (pN t)

theorem hpre : ∀ t : State, t.pc = BitVec.ofNat 64 Extracted.entry →
    (t.regs 28).toNat + 24 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 28).toNat + 16) 8 false = true →
    t.mem.readLE ((t.regs 28).toNat + 16) 8 < t.sp.toNat → t.sp.toNat % 16 = 0 →
    72 ≤ t.sp.toNat → t.sp.toNat + 16 ≤ 2 ^ 48 → t.mem.accessible (t.sp.toNat - 72) 88 true = true →
    ReachesRet Extracted.program (BitVec.ofNat 64 (Extracted.entry + 0x3c)) t (fun u =>
      u.sp = t.sp - 64 ∧ u.regs 1 = t.regs 0 ∧
      u.regs 0 = (if (t.regs 0).toNat % 2 = 0 then t.sp - 32 else t.sp - 24) ∧
      u.regs 29 = t.sp - 72 ∧ u.regs 28 = t.regs 28 ∧ u.regs 18 = t.regs 18 ∧ u.mem = M1 t) := by
  intro t hpc h3 h4 h5 h6 h7 h8 h9
  janus_run until [Extracted.entry + 0x3c]
  · have hx : (t.regs 0).toNat % 2 = 1 := (lsb _).1 (by assumption)
    exact ReachesRet.done rfl ⟨rfl, by simp [setReg], by simp [setReg, hx], by simp [setReg],
      by simp [setReg], by simp [setReg], by simp only [M1, pN, hx]; rfl⟩
  · have hx : (t.regs 0).toNat % 2 = 0 := by
      have h : ¬ (t.regs 0).toNat % 2 = 1 := fun h => hbr ((lsb _).2 h)
      omega
    exact ReachesRet.done rfl ⟨rfl, by simp [setReg], by simp [setReg, hx], by simp [setReg],
      by simp [setReg], by simp [setReg], by simp only [M1, pN, hx]; rfl⟩

theorem epi : ∀ t : State, t.pc = BitVec.ofNat 64 (Extracted.entry + 0x40) → t.sp.toNat % 16 = 0 →
    8 ≤ t.sp.toNat → t.sp.toNat + 64 ≤ 2 ^ 48 → t.mem.accessible (t.sp.toNat - 8) 64 false = true →
    t.mem.accessible (t.mem.readLE (t.sp.toNat + 48) 8) 8 false = true →
    t.mem.readLE (t.sp.toNat + 48) 8 + 8 ≤ 2 ^ 48 →
    t.mem.readLE t.sp.toNat 8 % 4 = 0 → t.mem.readLE t.sp.toNat 8 < 2 ^ 48 →
    ReachesRet Extracted.program (BitVec.ofNat 64 (t.mem.readLE t.sp.toNat 8)) t (fun t' =>
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat + 40) 8) +
        (BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat + 32) 8) +
          BitVec.ofNat 64 (t.mem.readLE (t.mem.readLE (t.sp.toNat + 48) 8) 8)) ∧
      t'.sp = t.sp + 64 ∧ t'.regs 29 = BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat - 8) 8) ∧
      t'.regs 28 = t.regs 28 ∧ t'.regs 18 = t.regs 18) := by
  intro t hpc h1 h2 h3 h4 h4' h4'' h5 h6
  janus_run


theorem blStep : ∀ u : State, u.pc = BitVec.ofNat 64 (Extracted.entry + 0x3c) →
    ReachesRet Extracted.program (BitVec.ofNat 64 cE) u (fun u' =>
      u'.regs = setReg u.regs 30 (BitVec.ofNat 64 (Extracted.entry + 0x40)) ∧ u'.sp = u.sp ∧
        u'.mem = u.mem) := by
  intro u hpc
  janus_step
  exact ReachesRet.done rfl ⟨rfl, rfl, rfl⟩

theorem glue : ∀ t : State, t.pc = BitVec.ofNat 64 (Extracted.entry + 0x6c) →
    t.mem.accessible (t.sp.toNat + 8) 8 false = true → t.sp.toNat + 16 ≤ 2 ^ 48 →
    t.sp.toNat % 16 = 0 →
    ReachesRet Extracted.program (BitVec.ofNat 64 Extracted.entry) t (fun t' =>
      t'.pc = BitVec.ofNat 64 Extracted.entry ∧ t'.sp = t.sp ∧ t'.mem = t.mem ∧
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE (t.sp.toNat + 8) 8) ∧
      (∀ r, r ≠ 0 → t'.regs r = t.regs r)) := by
  intro t hpc hacc hsp hal
  janus_run until [Extracted.entry]
  all_goals first
    | (intro r h0; simp [h0])
    | exact ReachesRet.done rfl ⟨rfl, rfl, rfl, by simp [setReg], fun r h0 => by simp [setReg, h0]⟩

/-- `HoldPtr`'s glue after its own `morestack` call, and the return pc of the `holdCallee` call. -/
abbrev hGlue : Nat := Extracted.entry + 0x6c
abbrev hRet : Nat := Extracted.entry + 0x40

/-- The binary's frame record of `HoldPtr`: at the glue no frame (largest frame 64 bytes), and at
the `holdCallee` call a 64-byte frame whose locals map marks the slot `48(RSP)` that holds `p`. -/
def HTable (FT : FrameTable) : Prop :=
  FT.valid hGlue = true ∧ FT.stop hGlue = false ∧ FT.injected hGlue = false ∧
  FT.spdelta hGlue = 0 ∧ FT.maxspd hGlue = 64 ∧ FT.args hGlue = [] ∧ FT.objs hGlue = [] ∧
  FT.valid hRet = true ∧ FT.stop hRet = false ∧ FT.injected hRet = false ∧
  FT.spdelta hRet = 64 ∧ FT.locals hRet = [true] ∧ FT.args hRet = [] ∧ FT.objs hRet = []

theorem htable_of {FT : FrameTable} (h : FT.Agrees Extracted.frames) : HTable FT := by
  obtain ⟨a1, -, a3, a4, a5, a6, -, a8, a9⟩ := h _ (List.mem_cons_self ..) hGlue (by decide) (by decide)
  obtain ⟨b1, -, b3, -, b5, b6, b7, b8, b9⟩ := h _ (List.mem_cons_self ..) hRet (by decide) (by decide)
  refine ⟨a1, ?_, ?_, ?_, ?_, ?_, ?_, b1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a5] <;> rfl
  · rw [a6] <;> rfl
  · rw [a3] <;> rfl
  · rw [a4] <;> rfl
  · rw [a8] <;> rfl
  · rw [a9] <;> rfl
  · rw [b5] <;> rfl
  · rw [b6] <;> rfl
  · rw [b3] <;> rfl
  · rw [b7] <;> rfl
  · rw [b8] <;> rfl
  · rw [b9] <;> rfl

/-- `HoldPtr`'s frame suspended at the `holdCallee` call (`SP = sp - 64`, `fp = sp`) marks its saved
frame pointer slot `sp - 8` and the slot `sp - 16` that holds `p`. -/
theorem bitsAt_single (b : Int) (a : Nat) : bitsAt b [true] a = decide ((a : Int) = b) := by
  unfold bitsAt
  by_cases h : (a : Int) = b
  · subst h; simp
  · rw [decide_eq_false h]
    cases h1 : decide (b ≤ (a : Int))
    · rfl
    · have hb : b ≤ a := by simpa using h1
      cases h2 : (((a : Int) - b).toNat % 8 == 0)
      · rfl
      · have h3 : ((a : Int) - b).toNat % 8 = 0 := by simpa using h2
        obtain ⟨j, hj⟩ : ∃ j, ((a : Int) - b).toNat / 8 = j + 1 :=
          ⟨((a : Int) - b).toNat / 8 - 1, by omega⟩
        simp only [Bool.true_and, hj]; rfl

theorem frameH {FT : FrameTable} (hT : HTable FT) {sp : Nat} (h64 : 64 ≤ sp) (a : Nat) :
    frameCls Arch.arm64 FT hRet (sp - 64) sp a = ((a == sp - 8) || (a == sp - 16)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hl, ha, ho⟩ := hT
  have hv : Arch.arm64.varp (sp - 64) sp = sp - 8 := by simp [Arch.varp]; omega
  simp only [frameCls, hv, Arch.argp, ho, hl, ha, List.any_nil, Bool.or_false, bitsAt_single]
  rw [decide_eq_true (show sp + 8 = sp - 8 + 16 by omega), Bool.true_and,
    decide_eq_true (show Arch.arm64.minLocals + (sp - 64) < sp - 8 by simp [Arch.minLocals]; omega),
    Bool.true_and]
  have hb : bitsAt (((sp + 8 : Nat) : Int)) [] a = false := by simp [bitsAt]
  rw [hb, Bool.or_false]
  congr 1
  rw [Bool.eq_iff_iff]; simp only [List.length_singleton, decide_eq_true_eq, beq_iff_eq]; omega

/-- `HoldPtr`'s result: `*p + a[0] + a[1]` after `holdCallee(p, x)` stored `v = cval x` at
`p = &a[x & 1]`. -/
def hres (x : BitVec 64) : BitVec 64 :=
  let v := BitVec.ofNat 64 (cval x.toNat)
  if x.toNat % 2 = 0 then (x + 1) + (v + v) else v + (x + v)

/-- The precondition of a call `HoldPtr(x)` (no room assumed). -/
def PreH (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s : State) : Prop :=
  ∃ lo hi, GStack s.mem (s.regs 28).toNat lo hi ∧ Outside (s.regs 28).toNat 24 pool ∧
    4096 ≤ lo ∧ lo + 8 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ hi ∧ hi ≤ 2 ^ 48 ∧
    lo % 16 = 0 ∧ hi % 16 = 0 ∧ s.sp.toNat % 16 = 0 ∧ s.regs 29 = s.sp - 8 ∧
    InRanges lo (hi - lo) pool ∧ PoolOK s.mem pool ∧
    (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
    (∃ fs, Chain Arch.arm64 FT s.mem hi (s.regs 30).toNat s.sp.toNat none fs ∧
      (∀ f ∈ fs, f.sp = s.sp.toNat ∨ s.sp.toNat + 16 ≤ f.sp) ∧
      framesCls Arch.arm64 FT fs (s.sp.toNat + 8) = false) ∧
    2 * ((hi - s.sp.toNat) + 64 + 176 + 976) ≤ maxstacksize ∧
    H [] (s.regs 28).toNat 0 (rtView rt s.mem)

/-- What `HoldPtr(x)` returns. -/
def PostH (s s' : State) : Prop := s'.regs 0 = hres (s.regs 0)

set_option maxHeartbeats 4000000 in
/-- `HoldPtr` on a stack whose prologue check falls through: it runs to the `holdCallee` call, the
callee may grow the stack — moving this frame — and the reads after the call find `p` adjusted
(the locals map marks its slot) and `*p` the callee's store at the moved `a[x & 1]`. -/
theorem hroomH (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (t : State) (hpc : t.pc = BitVec.ofNat 64 Extracted.entry)
    (hp : PreH FT pool rt H t) (hroom : t.mem.readLE ((t.regs 28).toNat + 16) 8 < t.sp.toNat) :
    GrownRet Extracted.program reloc (t.regs 30) t (PostH t) := by
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hfp, hinp, hpok, hr4, hr48,
    ⟨fs, hch, hfsp, hc8⟩, hfit, hH⟩ := hp
  have henv' := henv
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
  have hT := htable_of hA
  have hgs' := hgs
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
  have hacc := hpok.accessible hinp
  have hspL : lo + 928 < t.sp.toNat := by rw [hgg] at hroom; exact hroom
  have hsp64 := t.sp.isLt
  have hx0 := (t.regs 0).isLt
  have hx29 : (t.regs 29).toNat = t.sp.toNat - 8 := by
    rw [hfp, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  have hin : ∀ a k, lo ≤ a → a + k ≤ hi → InRanges a k pool := fun a k h1 h2 => hinp.sub h1 (by omega)
  obtain ⟨k1, u, hst1, hupc, hu_sp, hu1, hu0, hu29, hu28, hu18, hum⟩ := hpre t hpc hg24
    (Memory.accessible_mono _ hgacc (by omega) (by omega)) hroom hal3 (by omega) (by omega)
    (Memory.accessible_mono _ hacc (by omega) (by omega))
  obtain ⟨k2, v, hst2, hvpc, hvr, hvsp, hvm⟩ := blStep u hupc
  have hvmem : v.mem = M1 t := hvm.trans hum
  have hv0 : v.regs 0 = u.regs 0 := by rw [hvr]; simp [setReg]
  have hv1 : v.regs 1 = t.regs 0 := by rw [hvr]; simp [setReg, hu1]
  have hv28 : v.regs 28 = t.regs 28 := by rw [hvr]; simp [setReg, hu28]
  have hv29 : v.regs 29 = t.sp - 72 := by rw [hvr]; simp [setReg, hu29]
  have hv30 : v.regs 30 = BitVec.ofNat 64 hRet := by rw [hvr]; simp [setReg]
  have hvspn : v.sp.toNat = t.sp.toNat - 64 := by
    rw [hvsp, hu_sp, BitVec.toNat_sub, show (64 : BitVec 64).toNat = 64 from rfl]; omega
  have hpN : (v.regs 0).toNat = pN t := by
    rw [hv0, hu0]; unfold pN
    split <;> rw [BitVec.toNat_sub] <;> simp <;> omega
  have hpN1 : pN t = t.sp.toNat - 32 ∨ pN t = t.sp.toNat - 24 := by unfold pN; split <;> simp
  -- the memory at the call
  have hagM1 : ∀ a k, a + k ≤ t.sp.toNat - 72 ∨ t.sp.toNat - 8 ≤ a → a + k ≤ t.sp.toNat + 8 ∨
      t.sp.toNat + 16 ≤ a → (M1 t).readLE a k = t.mem.readLE a k := by
    intro a k h1 h2
    simp only [M1]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have haccM1 : ∀ a k w, (M1 t).accessible a k w = t.mem.accessible a k w := by
    intro a k w; simp only [M1, Memory.accessible_writeLE]
  have hM1lr : (M1 t).readLE (t.sp.toNat - 64) 8 = (t.regs 30).toNat := by
    simp only [M1]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (t.regs 30).isLt
  have hM1a0 : (M1 t).readLE (t.sp.toNat - 32) 8 = (t.regs 0).toNat := by
    simp only [M1]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt hx0
  have hM1a1 : (M1 t).readLE (t.sp.toNat - 24) 8 = ((t.regs 0).toNat + 1) % 2 ^ 64 := by
    simp only [M1]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self] <;> rfl
  have hM1p : (M1 t).readLE (t.sp.toNat - 16) 8 = pN t := by
    simp only [M1]; rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by rcases hpN1 with h | h <;> rw [h] <;> omega)
  have hgsM1 : GStack (M1 t) (t.regs 28).toNat lo hi := by
    simp only [M1]
    refine GStack.writeLE (GStack.writeLE (GStack.writeLE (GStack.writeLE (GStack.writeLE (GStack.writeLE hgs hgo
      (hin _ _ (by omega) (by omega))) hgo (hin _ _ (by omega) (by omega))) hgo (hin _ _ (by omega) (by omega)))
      hgo (hin _ _ (by omega) (by omega))) hgo (hin _ _ (by omega) (by omega))) hgo
      (hin _ _ (by omega) (by rcases hpN1 with h | h <;> omega))
  -- the walk at the call: this frame, then the caller's
  have hfb := hch.bounds
  have hchM1 : Chain Arch.arm64 FT (M1 t) hi (t.regs 30).toNat t.sp.toNat none fs :=
    Chain.congr hch (by omega) fun f hf _ => by
      obtain ⟨h1, -⟩ := hfb f hf
      simp only [Arch.lrSlot]
      exact hagM1 _ _ (by omega) (by rcases hfsp f hf with h | h <;> omega)
  have hT0 := hT
  obtain ⟨-, -, -, -, -, -, -, hTv', hTs', hTi', hTd', -, -, -⟩ := hT0
  have hfpF : Arch.arm64.fp FT hRet (t.sp.toNat - 64) = t.sp.toNat := by simp [Arch.fp, hTd']; omega
  have hchv : Chain Arch.arm64 FT v.mem hi hRet (t.sp.toNat - 64) none
      (⟨hRet, t.sp.toNat - 64, Arch.arm64.fp FT hRet (t.sp.toNat - 64)⟩ :: fs) := by
    rw [hvmem]
    refine .cons hTv' hTs' hTi' (by omega) (by rw [hfpF]; omega) ?_
    rw [hfpF]
    have : Arch.arm64.lrOf (M1 t) (t.sp.toNat - 64) t.sp.toNat none = (t.regs 30).toNat := by
      simp only [Arch.lrOf]; rw [if_pos (by omega), hM1lr]
    rw [this]; exact hchM1
  have hclsF : ∀ a, framesCls Arch.arm64 FT
      (⟨hRet, t.sp.toNat - 64, Arch.arm64.fp FT hRet (t.sp.toNat - 64)⟩ :: fs) a =
      (((a == t.sp.toNat - 8) || (a == t.sp.toNat - 16)) || framesCls Arch.arm64 FT fs a) := by
    intro a; simp only [framesCls_cons, hfpF]; rw [frameH hT (by omega)]
  -- the callee's precondition
  have hRetN : (BitVec.ofNat 64 hRet).toNat = hRet := by decide
  have hchv' : Chain Arch.arm64 FT v.mem hi (v.regs 30).toNat v.sp.toNat none
      (⟨hRet, t.sp.toNat - 64, Arch.arm64.fp FT hRet (t.sp.toNat - 64)⟩ :: fs) := by
    rw [hv30, hRetN, hvspn]; exact hchv
  have hfitv : 2 * ((hi - v.sp.toNat) + 176 + 976) ≤ maxstacksize := by
    rw [hvspn, show hi - (t.sp.toNat - 64) = hi - t.sp.toNat + 64 by omega]; omega
  have hpv : PreC FT pool rt H v := by
    refine ⟨lo, hi, by rw [hv28, hvmem]; exact hgsM1, by rw [hv28]; exact hgo, h4k, by omega,
      by omega, hhi48, hal1, hal2, by omega, ?_, hinp, by rw [hvmem]; exact hpok.of_accessible haccM1,
      by rw [hv30]; decide, by rw [hv30]; decide, ⟨_, hchv', fun f hf => ?_, ?_, ?_⟩,
      by rw [hpN]; rcases hpN1 with h | h <;> omega,
      by rw [hpN, hvspn]; rcases hpN1 with h | h <;> omega, by rw [hpN]; rcases hpN1 with h | h <;> omega,
      hfitv, ?_⟩
    · rw [hv29, hvsp, hu_sp]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, show (72 : BitVec 64).toNat = 72 from rfl,
        show (64 : BitVec 64).toNat = 64 from rfl, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · rcases List.mem_cons.1 hf with rfl | hf
      · left; rw [hvspn]
      · right; obtain ⟨h1, -⟩ := hfb f hf; rw [hvspn]; omega
    · rw [hvspn, hclsF, hch.framesCls_below hIF (by omega)]; simp; omega
    · rw [hvspn, hclsF, hch.framesCls_below hIF (by omega)]; simp; omega
    · rw [hv28, hvmem]; simp only [M1]
      rw [rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by rcases hpN1 with h | h <;> omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega)))]
      exact hH
  refine GrownRet.of_steps hst1 (GrownRet.of_steps hst2
    (GrownRet.call (gcallee FT pool rt H reloc hms henv) hvpc hpv fun w hwpc hw => ?_))
  obtain ⟨lov, hiv, lo', hi', hgsv, hgsw, hsz, h4k', hal1', hal2', hhi48', hinp', hwsp, hw29,
    hw28, hw18, hmv, hwv, hmf, hHw⟩ := hw
  rw [hv28, hvmem] at hgsv
  obtain ⟨e1, e2⟩ := GStack.unique hgsM1 hgsv
  subst e1 e2
  have hmvF := hmv _ hchv'
  rw [hvspn, hvmem, hpN] at hmvF
  rw [hpN, hv1] at hwv
  have hwspn : w.sp.toNat = t.sp.toNat - 64 + hi' - hi := by
    rw [hwsp, hvspn, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (show t.sp.toNat - 64 + hi' - hi < 2 ^ 64 by omega)
  have hgro := hmvF.grows
  have hcode := hCO _ hch.valid_head
  -- the frame read back on the (possibly moved) stack
  have rP : w.mem.readLE (w.sp.toNat + 48) 8 = pN t + hi' - hi := by
    rw [hwspn, show t.sp.toNat - 64 + hi' - hi + 48 = (t.sp.toNat - 16) + hi' - hi by omega,
      hmvF.readLE_ptr (by omega) (by omega) (by omega) (by rw [hclsF]; simp)
        (by simp only [outside_cons, outside_nil, and_true]; rcases hpN1 with h | h <;> omega)
        (by rw [hM1p]; rcases hpN1 with h | h <;> omega) (by rw [hM1p]; rcases hpN1 with h | h <;> omega),
      hM1p]
  have rLR : w.mem.readLE w.sp.toNat 8 = (t.regs 30).toNat := by
    rw [hwspn, show t.sp.toNat - 64 + hi' - hi = (t.sp.toNat - 64) + hi' - hi from rfl,
      hmvF.readLE_word_out (by omega) (by omega) (by omega)
        (by simp only [outside_cons, outside_nil, and_true]; rcases hpN1 with h | h <;> omega)
        (by rw [hM1lr]; exact hcode.1), hM1lr]
  have hscal : ∀ a, (a = t.sp.toNat - 32 ∨ a = t.sp.toNat - 24) → a ≠ pN t →
      w.mem.readLE (a + hi' - hi) 8 = (M1 t).readLE a 8 := by
    intro a ha hne
    have hpa : pN t + 8 ≤ a ∨ a + 8 ≤ pN t := by rcases hpN1 with h | h <;> rcases ha with h' | h' <;> omega
    exact hmvF.readLE_scalar (by omega) (by omega) (fun j hj => by
      rw [show a + j - (a + j) % 8 = a by omega, hclsF, hch.framesCls_below hIF (by omega)]
      simp; omega) (by simp only [outside_cons, outside_nil, and_true]; omega)
  -- the epilogue
  have hpok_w : PoolOK w.mem pool := hpok.of_accessible fun a k w' => by
    rw [hmf.accessible, hvmem, haccM1]
  have haccw : ∀ a k, lo' ≤ a → a + k ≤ hi' → w.mem.accessible a k false = true := fun a k h1 h2 =>
    Memory.accessible_read_of_write _ (hpok_w.accessible (hinp'.sub h1 (by omega)))
  obtain ⟨k3, x, hst3, hxpc, hx0', hxsp, hx29', hx28, hx18⟩ := epi w (hwpc.trans hv30)
    (by omega) (by omega) (by omega) (haccw _ _ (by omega) (by omega))
    (by rw [rP]; exact haccw _ _ (by rcases hpN1 with h | h <;> omega) (by rcases hpN1 with h | h <;> omega))
    (by rw [rP]; rcases hpN1 with h | h <;> omega) (by rw [rLR]; exact hr4) (by rw [rLR]; exact hr48)
  refine .done hst3 (by rw [hxpc, rLR, BitVec.ofNat_toNat, BitVec.setWidth_eq]) ?_
  show x.regs 0 = hres (t.regs 0)
  rw [hx0', rP, hwspn, show t.sp.toNat - 64 + hi' - hi + 40 = (t.sp.toNat - 24) + hi' - hi by omega,
    show t.sp.toNat - 64 + hi' - hi + 32 = (t.sp.toNat - 32) + hi' - hi by omega, hwv]
  unfold hres
  by_cases he : (t.regs 0).toNat % 2 = 0
  · have hp : pN t = t.sp.toNat - 32 := by unfold pN; rw [if_pos he]
    rw [← hp, hwv, hscal _ (.inr rfl) (by omega), hM1a1, if_pos he]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_add, Nat.mod_mod]; rfl
  · have hp : pN t = t.sp.toNat - 24 := by unfold pN; rw [if_neg he]
    rw [← hp, hwv, hscal _ (.inl rfl) (by omega), hM1a0, if_neg he, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- At its own glue, `HoldPtr`'s frame (`SP = fp = sp`, no pointer arguments) marks nothing. -/
theorem hframe0 {FT : FrameTable} (hT : HTable FT) (sp a : Nat) :
    frameCls Arch.arm64 FT hGlue sp sp a = false := by
  obtain ⟨-, -, -, -, -, ha, ho, -⟩ := hT
  have hv : Arch.arm64.varp sp sp = sp := by simp [Arch.varp]
  simp only [frameCls, hv, Arch.argp, ho, ha, List.any_nil, Bool.or_false]
  have e1 : decide (sp + 8 = sp + 16) = false := decide_eq_false (by omega)
  have e2 : decide (Arch.arm64.minLocals + sp < sp) = false :=
    decide_eq_false (by unfold Arch.minLocals; omega)
  rw [e1, e2, Bool.false_and, Bool.false_and, Bool.false_or]
  simp [bitsAt]

set_option maxHeartbeats 2000000 in
/-- `HoldPtr`'s own growth: the contract moves the stack, the glue reloads `x` (copied), and the
frame now fits, so `hroomH` applies on the larger stack. -/
theorem hgrow (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (s : State) (lo hi : Nat) (hgs : GStack s.mem (s.regs 28).toNat lo hi)
    (hgo : Outside (s.regs 28).toNat 24 pool) (h4k : 4096 ≤ lo) (hlo : lo + 8 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 16 ≤ hi) (hhi48 : hi ≤ 2 ^ 48) (hal1 : lo % 16 = 0) (hal2 : hi % 16 = 0)
    (hal3 : s.sp.toNat % 16 = 0) (hfp : s.regs 29 = s.sp - 8) (hinp : InRanges lo (hi - lo) pool)
    (hpok : PoolOK s.mem pool) (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48)
    (fs : List Frame) (hch : Chain Arch.arm64 FT s.mem hi (s.regs 30).toNat s.sp.toNat none fs)
    (hfsp : ∀ f ∈ fs, f.sp = s.sp.toNat ∨ s.sp.toNat + 16 ≤ f.sp)
    (hc8 : framesCls Arch.arm64 FT fs (s.sp.toNat + 8) = false)
    (hfit : 2 * ((hi - s.sp.toNat) + 64 + 176 + 976) ≤ maxstacksize)
    (s_m : State) (hm : MorestackPre Extracted.program FT pool rt H (s.regs 28).toNat lo hi s_m)
    (hglue : s_m.regs 30 = BitVec.ofNat 64 hGlue) (hx3 : s_m.regs 3 = s.regs 30)
    (hsp_m : s_m.sp = s.sp) (h28 : s_m.regs 28 = s.regs 28)
    (hmem : s_m.mem = s.mem.writeLE (s.sp.toNat + 8) 8 (s.regs 0).toNat)
    (hchm : Chain Arch.arm64 FT s_m.mem hi (s_m.regs 30).toNat s_m.sp.toNat (some (s_m.regs 3).toNat)
      (⟨hGlue, s.sp.toNat, Arch.arm64.fp FT hGlue s.sp.toNat⟩ :: fs)) :
    ∃ s_r, reloc s_m s_r ∧ GrownRet Extracted.program reloc (s.regs 30) s_r (PostH s) := by
  have henv' := henv
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
  have hT := htable_of hA
  obtain ⟨s_r, lo1, hi1, hre, hgr⟩ := hms _ lo hi s_m hm
  refine ⟨s_r, hre, ?_⟩
  obtain ⟨hg1, hg2, h4k1, hal1', hal2', hhi48', hinp1, happ⟩ := hgr.grows
  have hroom := hgr.room
  have hT0 := hT
  obtain ⟨-, -, -, hspd, hmx, -, -⟩ := hT0
  have hgl : (s_m.regs 30).toNat = hGlue := by rw [hglue]; rfl
  rw [hgl, hmx, hsp_m] at hroom
  simp only [stackGuard] at hroom
  have hsp := s.sp.isLt
  have hspm : s_m.sp.toNat = s.sp.toNat := by rw [hsp_m]
  have hsp_r : s_r.sp.toNat = s.sp.toNat + hi1 - hi := by
    rw [hgr.sp, hspm, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hpok_r : PoolOK s_r.mem pool := hm.inPool.2.of_accessible hgr.frame.accessible
  have hacc_r : s_r.mem.accessible lo1 (hi1 - lo1) true = true := hpok_r.accessible hinp1
  obtain ⟨k, s_e, hst, hepc, -, hesp, hemem, he0, her⟩ := glue s_r (hgr.pc.trans hglue)
    (Memory.accessible_read_of_write _ (Memory.accessible_mono _ hacc_r (by omega) (by omega)))
    (by omega) (by omega)
  have he30 : s_e.regs 30 = s.regs 30 := by rw [her 30 (by decide), hgr.lr, hx3]
  have he28 : s_e.regs 28 = s.regs 28 := by rw [her 28 (by decide), hgr.gkeep.1, h28]
  have he29 : s_e.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 8 + hi1 - hi) := by
    rw [her 29 (by decide), hgr.regs 29 rfl, hm.fp, hspm]
  have hesp' : s_e.sp.toNat = s.sp.toNat + hi1 - hi := by rw [hesp, hsp_r]
  have hfp0 : Arch.arm64.fp FT hGlue s.sp.toNat = s.sp.toNat := by simp [Arch.fp, hspd]
  have hmA := hgr.moved _ hchm
  rw [hspm] at hmA
  have hclsA : ∀ a, moveCls FT s.sp.toNat (⟨hGlue, s.sp.toNat, Arch.arm64.fp FT hGlue s.sp.toNat⟩ :: fs) a =
      (decide (a = s.sp.toNat - 8) || framesCls Arch.arm64 FT fs a) := by
    intro a; simp only [moveCls, framesCls_cons, hfp0, hframe0 hT, Bool.false_or]
  have hfb := hch.bounds
  have hchs : Chain Arch.arm64 FT s_m.mem hi (s.regs 30).toNat s.sp.toNat none fs :=
    Chain.congr hch (by omega) fun f hf _ => by
      rw [hmem, Memory.readLE_writeLE_of_disjoint _ _ (by
        simp only [Arch.lrSlot]; obtain ⟨h1, -⟩ := hfb f hf; rcases hfsp f hf with h | h <;> omega)]
  have hche : Chain Arch.arm64 FT s_e.mem hi1 (s_e.regs 30).toNat s_e.sp.toNat none
      (fs.map (Frame.mv hi hi1)) := by
    rw [hemem, he30, hesp']
    exact hchs.moved hmA hCO hAl (by omega) (by omega) fun _ _ _ => trivial
  have hx0e : (s_e.regs 0).toNat = (s.regs 0).toNat := by
    rw [he0, hsp_r, show s.sp.toNat + hi1 - hi + 8 = (s.sp.toNat + 8) + hi1 - hi by omega,
      hmA.readLE_scalar (by omega) (by omega) (fun j hj => by
        rw [show s.sp.toNat + 8 + j - (s.sp.toNat + 8 + j) % 8 = s.sp.toNat + 8 by omega, hclsA, hc8]
        simp; omega) trivial, hmem, Memory.readLE_writeLE_self, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)), Nat.mod_eq_of_lt (s.regs 0).isLt]
  have hcl : ∀ a, hi ≤ a + hi1 → framesCls Arch.arm64 FT (fs.map (Frame.mv hi hi1)) (a + hi1 - hi) =
      framesCls Arch.arm64 FT fs a := fun a ha => hch.framesCls_mv (by omega) (by omega) ha
  obtain ⟨-, -, hge3, hge4, hge5⟩ := hgr.gstack
  simp only [gStackguard0, stackGuard] at hge5
  have hpe : PreH FT pool rt H s_e := by
    refine ⟨lo1, hi1, by rw [he28, hemem, ← h28, hm.greg]; exact hgr.gstack, by rw [he28]; exact hgo, h4k1,
      by omega, by omega, hhi48', hal1', hal2', by omega, ?_, hinp1, by rw [hemem]; exact hpok_r,
      by rw [he30]; exact hr4, by rw [he30]; exact hr48, ⟨_, hche, fun f hf => ?_, ?_⟩,
      by rw [hesp', show hi1 - (s.sp.toNat + hi1 - hi) = hi - s.sp.toNat by omega]; exact hfit, ?_⟩
    · rw [he29, hesp]; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, hsp_r, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · obtain ⟨f0, hf0, rfl⟩ := List.mem_map.1 hf
      obtain ⟨h1, -⟩ := hfb f0 hf0
      simp only [Frame.mv]; rw [hesp']; rcases hfsp f0 hf0 with h | h <;> omega
    · rw [hesp', show s.sp.toNat + hi1 - hi + 8 = (s.sp.toNat + 8) + hi1 - hi by omega, hcl _ (by omega)]
      exact hc8
    · rw [he28, hemem, ← h28, hm.greg]; exact hgr.ready
  have hroome : s_e.mem.readLE ((s_e.regs 28).toNat + 16) 8 < s_e.sp.toNat := by
    rw [he28, hemem, ← h28, hm.greg, hge5, hesp']; omega
  refine GrownRet.of_steps hst ?_
  rw [← he30]
  refine (hroomH FT pool rt H reloc hms henv s_e hepc hpe hroome).mono fun s'' hq => ?_
  show s''.regs 0 = hres (s.regs 0)
  rw [hq, show s_e.regs 0 = s.regs 0 from BitVec.eq_of_toNat_eq hx0e]

/-- **`HoldPtr` through stack growths**: its own prologue may grow the stack, and so may the
callee's, which moves `HoldPtr`'s frame — the pointer it holds included. -/
theorem hmain (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (s : State) (hpc : s.pc = BitVec.ofNat 64 Extracted.entry)
    (hpre : PreH FT pool rt H s) :
    GrownRet Extracted.program reloc (s.regs 30) s (PostH s) := by
  by_cases hroom : s.mem.readLE ((s.regs 28).toNat + 16) 8 < s.sp.toNat
  · exact hroomH FT pool rt H reloc hms henv s hpc hpre hroom
  · have hpre' := hpre
    obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hfp, hinp, hpok, hr4, hr48,
      ⟨fs, hch, hfsp, hc8⟩, hfit, hH⟩ := hpre'
    have henv' := henv
    obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
    have hT := htable_of hA
    have hT0 := hT
    obtain ⟨hv, hst, hinj, hspd, hmx, -, -⟩ := hT0
    have hgs' := hgs
    obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
    simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
    have hacc := hpok.accessible hinp
    have hfit1 : 2 * (hi - lo) ≤ maxstacksize := by
      have h' := hfit; have hr := hroom; rw [hgg] at hr; omega
    have hfit2 : 2 * ((hi - s.sp.toNat) + 64 + stackGuard) ≤ maxstacksize :=
      Nat.le_trans (Nat.mul_le_mul_left 2 (show (hi - s.sp.toNat) + 64 + stackGuard ≤
        (hi - s.sp.toNat) + 64 + 176 + 976 by
          rw [Nat.add_assoc ((hi - s.sp.toNat) + 64) 176 976]; exact Nat.add_le_add_left (by decide) _)) hfit
    obtain ⟨mm, hmm⟩ : ∃ mm, mm = s.mem.writeLE (s.sp.toNat + 8) 8 (s.regs 0).toNat := ⟨_, rfl⟩
    have hfp0 : Arch.arm64.fp FT hGlue s.sp.toNat = s.sp.toNat := by simp [Arch.fp, hspd]
    have hcm : Chain Arch.arm64 FT mm hi (s.regs 30).toNat s.sp.toNat none fs :=
      Chain.congr hch (by omega) fun f hf _ => by
        rw [hmm, Memory.readLE_writeLE_of_disjoint _ _ (by
          simp only [Arch.lrSlot]; obtain ⟨h1, -⟩ := hch.bounds f hf; rcases hfsp f hf with h | h <;> omega)]
    have hchain : Chain Arch.arm64 FT mm hi hGlue s.sp.toNat (some (s.regs 30).toNat)
        (⟨hGlue, s.sp.toNat, Arch.arm64.fp FT hGlue s.sp.toNat⟩ :: fs) := by
      refine .cons hv hst hinj (by omega) (by rw [hfp0]; omega) ?_
      rw [hfp0]; simpa [Arch.lrOf] using hcm
    apply GrownRet.of_reaches_stub
    janus_run
    rw [← hmm]
    have e30 : (BitVec.ofNat 64 hGlue).toNat = hGlue := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by decide)
    refine hgrow FT pool rt H reloc hms henv s lo hi hgs hgo h4k hlo hhi hhi48 hal1 hal2 hal3 hfp hinp
      hpok hr4 hr48 fs hch hfsp hc8 hfit _
      ⟨⟨"runtime.morestack_noctxt.abi0", rfl⟩, by simp [setReg, regG], ?_, hgo,
        ⟨h4k, hlo, show s.sp.toNat + 8 ≤ hi by omega, hhi48⟩, ⟨hal1, hal2, hal3⟩, ?_,
        ⟨hinp, hpok.of_accessible fun a k w => by rw [hmm, Memory.accessible_writeLE]⟩,
        ⟨⟨hGlue, s.sp.toNat, Arch.arm64.fp FT hGlue s.sp.toNat⟩ :: fs, ?_⟩, ⟨hfit1, ?_⟩,
        ⟨hCO, hAl⟩, ?_⟩ ?_ ?_ rfl ?_ ?_ ?_
    · rw [hmm]; exact GStack.writeLE hgs hgo (hinp.sub (by omega) (by omega))
    · show (s.regs 29).toNat = s.sp.toNat - 8
      rw [hfp, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · show Chain Arch.arm64 FT mm hi (BitVec.ofNat 64 hGlue).toNat s.sp.toNat
        (some ((setReg (setReg (setReg s.regs 3 (s.regs 30)) 16
          (BitVec.ofNat 64 (s.mem.readLE ((s.regs 28).toNat + 16) 8))) 30 (BitVec.ofNat 64 hGlue)) 3).toNat) _
      rw [e30]; simpa [setReg_apply] using hchain
    · show 2 * ((hi - s.sp.toNat) + FT.maxspd (BitVec.ofNat 64 hGlue).toNat + stackGuard) ≤ maxstacksize
      rw [e30, hmx]; exact hfit2
    · show H [] _ 0 (rtView rt mm)
      rw [hmm, rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega)))]
      simpa [setReg, regG] using hH
    · simp [setReg] <;> rfl
    · simp [setReg]
    · simp [setReg]
    · exact hmm
    · show Chain Arch.arm64 FT mm hi (BitVec.ofNat 64 hGlue).toNat s.sp.toNat
        (some ((setReg (setReg (setReg s.regs 3 (s.regs 30)) 16
          (BitVec.ofNat 64 (s.mem.readLE ((s.regs 28).toNat + 16) 8))) 30 (BitVec.ofNat 64 hGlue)) 3).toNat) _
      rw [e30]; simpa [setReg_apply] using hchain

/-- **`HoldPtr` is correct on a stack of any size, stack growth included**: whether the stack
grows in its own prologue or in `holdCallee`'s — which moves `HoldPtr`'s frame and the pointer
`p` it holds there — it returns `*p + a[0] + a[1]` after the callee's store through `p`. -/
theorem correctness (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (x : BitVec 64) :
    EnsuresGrow Extracted.program reloc Extracted.entry [x] (PreH FT pool rt H)
      (fun _ s' => s'.regs 0 = hres x) := by
  intro ret hret s hs hpre
  janus_intro hs
  have hg := hmain FT pool rt H reloc hms henv s (by rw [h_pc]; rfl) hpre
  rw [h_lr] at hg
  refine ((hg.withExit hret.fetch_none fun st hst => hret.notStub st hst).toGrownReturns
    (by have := hret.user; omega)).mono fun s' h => ?_
  show s'.regs 0 = hres x
  rw [h, h_x0]

/-! ## The theorem is not vacuous -/

namespace Witness

open Janus.Contracts.StackSat

def ret : Nat := 0x200000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The witness frame table: the binary's frame records of `HoldPtr`, `pick` and `holdCallee`
(`Extracted.frames`, with their real pointer maps), and the caller, which stops the walk. -/
def extraT : FrameTable :=
  { valid := fun pc => pc == ret, entry := id, spdelta := fun _ => 0, maxspd := fun _ => 0,
    stop := fun pc => pc == ret, injected := fun _ => false, locals := fun _ => [],
    args := fun _ => [], objs := fun _ => [] }

def FTs : FrameTable := FrameTable.ofRecs Extracted.frames extraT

theorem agrees : FTs.Agrees Extracted.frames :=
  FrameTable.ofRecs_agrees _ _ fun r hr pc h1 h2 => by
    rcases List.mem_cons.1 hr with rfl | hr
    · exact List.find?_cons_of_pos (by simpa using And.intro h1 h2)
    rcases List.mem_cons.1 hr with rfl | hr
    · exact (List.find?_cons_of_neg (by simp at h1 h2 ⊢; omega)).trans
        (List.find?_cons_of_pos (by simpa using And.intro h1 h2))
    rcases List.mem_cons.1 hr with rfl | hr
    · exact (List.find?_cons_of_neg (by simp at h1 h2 ⊢; omega)).trans
        ((List.find?_cons_of_neg (by simp at h1 h2 ⊢; omega)).trans
          (List.find?_cons_of_pos (by simpa using And.intro h1 h2)))
    · simp at hr

theorem laws : FTs.Aligned ∧ FTs.InFrame Arch.arm64 :=
  FrameTable.ofRecs_laws_arm64 Extracted.frames extraT (fun r hr => by
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨rfl, by decide⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨rfl, by decide⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨rfl, by decide⟩
      · simp at hr)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem code : FTs.CodeOutside pool := by
  intro pc hv
  unfold FTs FrameTable.ofRecs at hv
  dsimp only at hv
  cases h : Extracted.frames.find? (fun r => decide (r.entry ≤ pc ∧ pc < r.entry + r.size)) with
  | none =>
    rw [h] at hv
    simp only [extraT, beq_iff_eq] at hv
    subst hv
    exact ⟨by simp only [pool, outside_cons, outside_nil, and_true]; decide, by decide⟩
  | some r =>
    have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    have hlt : pc < 0x91a00 := by
      rcases List.mem_cons.1 hm with rfl | hm
      · simp at hp; omega
      rcases List.mem_cons.1 hm with rfl | hm
      · simp at hp; omega
      rcases List.mem_cons.1 hm with rfl | hm
      · simp at hp; omega
      · simp at hm
    refine ⟨?_, by omega⟩
    simp only [pool, outside_cons, outside_nil, and_true, SL, SH, BL, BH]; omega

theorem env : Env FTs pool rt := by
  refine ⟨agrees, laws.2, laws.1, code, ?_⟩
  intro a n hin
  obtain ⟨r, hr, h1, h2⟩ := hin
  simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [rt, outside_cons, outside_nil, and_true]
  rcases hr with rfl | rfl <;> simp only [SL, SH, BL, BH, G0] at h1 h2 ⊢ <;> omega

/-- The stack pointer: 960 bytes above the small slot's bottom, so `HoldPtr`'s frame fits but
`holdCallee`'s does not. -/
def spw : Nat := SL + 960

/-- The call state `HoldPtr(16)` on the small 4 KiB stack of `StackSat`. -/
def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 G0 else if i = 29 then BitVec.ofNat 64 (spw - 8)
      else if i = 30 then BitVec.ofNat 64 ret else if i = 0 then 16#64 else 0,
    sp := BitVec.ofNat 64 spw, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [16#64] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

/-- `HoldPtr`'s frame fits, but `holdCallee`'s (called with `SP - 64`) does not: the stack grows
inside the callee, moving `HoldPtr`'s frame and the pointer `p` held in it. -/
theorem callee_grows : s0.mem.readLE ((s0.regs 28).toNat + 16) 8 < s0.sp.toNat ∧
    ¬ s0.mem.readLE ((s0.regs 28).toNat + 16) 8 + 48 < s0.sp.toNat - 64 := by
  have hg : (s0.regs 28).toNat = G0 := by decide
  rw [hg, show s0.mem = mem0 from rfl, mem0_desc.2.2, show s0.sp.toNat = spw by decide]
  decide

theorem pre : PreH FTs pool rt H s0 := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hg : (s0.regs 28).toNat = G0 := by decide
  have hsp : s0.sp.toNat = spw := by decide
  have h30 : (s0.regs 30).toNat = ret := by decide
  have el : FTs.locals ret = [] := rfl
  have ea : FTs.args ret = [] := rfl
  have eo : FTs.objs ret = [] := rfl
  have e : Arch.arm64.fp FTs ret spw = spw := by
    show spw + FTs.spdelta ret = spw; rw [show FTs.spdelta ret = 0 from rfl, Nat.add_zero]
  refine ⟨SL, SH, ?_, ?_, by decide, ?_, ?_, by decide, by decide, by decide, ?_, rfl,
    ⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_, by rw [h30]; decide, by rw [h30]; decide,
    ⟨[⟨ret, spw, spw⟩], ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hg]; exact ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩
  · rw [hg]; simp [pool, G0, SL, SH, BL, BH]
  · rw [hsp]; decide
  · rw [hsp]; decide
  · rw [hsp]; decide
  · intro r hr
    simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · rw [hsp, h30]
    have := Chain.stop (A := Arch.arm64) (FT := FTs) (m := s0.mem) (hi := SH) (pc := ret) (sp := spw)
      (lr0 := none) rfl rfl rfl (by decide) (by rw [e]; decide)
    rw [e] at this; exact this
  · intro f hf; simp at hf; subst hf; left; rw [hsp]
  · rw [hsp]
    simp only [framesCls_cons, framesCls_nil, Bool.or_false]
    simp [frameCls, el, ea, eo, bitsAt, Arch.varp, Arch.argp, Arch.minLocals]
  · rw [hsp]; decide
  · rw [hg]; refine ⟨rfl, .inl ⟨?_, ?_⟩⟩
    · rw [readLE_rtView hin0]; exact d1
    · rw [readLE_rtView hin8]; exact d2

/-- All hypotheses of `correctness` hold together, for a call whose callee grows the stack. -/
theorem nonvacuous : ∃ (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (ret : Nat) (s : State),
    MorestackContract Extracted.program FT pool rt H reloc ∧ Env FT pool rt ∧
    RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [16#64] s ∧
    PreH FT pool rt H s ∧ (s.mem.readLE ((s.regs 28).toNat + 16) 8 < s.sp.toNat ∧
      ¬ s.mem.readLE ((s.regs 28).toNat + 16) 8 + 48 < s.sp.toNat - 64) :=
  ⟨FTs, pool, rt, H, reloc FTs, ret, s0, contract _ FTs, env, hret, setup, pre, callee_grows⟩

/-- So the guarantee is reached: `HoldPtr(16)` — `holdCallee` grows the stack and stores `16`
through the adjusted pointer into the moved array — returns `17 + 16 + 16 = 49`. -/
theorem returns : GrownReturns (Extracted.program.withExit ret) (reloc FTs) s0
    (fun s' => s'.regs 0 = 49#64) :=
  (correctness FTs pool rt H (reloc FTs) (contract _ FTs) env 16#64 ret hret s0 setup pre).mono
    fun s' h => by rw [h]; rfl

end Witness

end Proof
