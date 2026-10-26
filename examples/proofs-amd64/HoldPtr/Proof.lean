import Janus
import Extracted

/-!
# `HoldPtr(x uint64) uint64` on amd64: a pointer into its own frame, held across a call that grows the stack (R7)

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

The amd64 counterpart of `examples/proofs/HoldPtr.lean`. `p = &a[x & 1]` points into `HoldPtr`'s
own frame; the compiler keeps it in the frame slot `40(SP)` across the call of `holdCallee`, whose
168-byte frame grows the stack when it is small. `copystack` then moves `HoldPtr`'s frame and
adjusts the pointers into the old stack, among them this one twice: the slot `40(SP)`, which
`HoldPtr`'s locals map at the call marks (`localMaps = [[false], [true]]` in `Extracted.frames`),
and `holdCallee`'s spilled argument `8(SP)`, which its args map marks (`[true]`).

**Guarantee** (`correctness`). For every frame table that agrees with the binary's frame records,
every stack pool, runtime memory and readiness, and every runtime that meets the amd64
`morestack` contract (`MorestackContract64`), `HoldPtr(x)` returns `hres x` on a goroutine stack
of any size, whether the stack grows in its own prologue or in the callee's. `hres x` is
`*p + a[0] + a[1]` after the callee stored `cval x` (`x` when `x & 15 = 0`, else `0`) at
`a[x & 1]`.

**How.**
* `gcallee` is `holdCallee`'s grown summary (`GSummary64`). On the growth path (`cgrow`) the glue
  reloads `p` *adjusted* (`Moved.readLE_ptr` on the args-map slot), so the callee's store reaches
  the moved array. `PostC` states the move of the caller's frames together with that store.
* `hroomH` reads the frame back after the call on the moved stack: `p` adjusted (the locals-map
  slot), `*p` the callee's store, the other element of `a` copied, the return address copied.
* `hgrow` covers `HoldPtr`'s own growth.

The witness (`Witness.callee_grows`) is a call whose frame fits but whose callee's does not.
-/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Stack
  Janus.Contracts Janus.Contracts.Stack Janus.Contracts.StackAmd64

namespace Proof

/-- `holdCallee`'s entry and its glue after the `morestack` call (`MOVQ 8(SP), AX`). -/
abbrev cE : Nat := janus_eval% (segAddr Extracted.program "example.com/basic.holdCallee")
abbrev cGlue : Nat := cE + 0x7a

/-- The result of the callee: `buf[0]`, `x` when `x & 15 = 0`, else `0`. -/
def cval (x : Nat) : Nat := if x % 16 = 0 then x else 0

/-- `holdCallee` on a stack with room: it zeroes `buf`, stores `x` at `buf[x & 15]` and `buf[0]`
through `p`, and returns. -/
theorem cbody : ∀ t : State, t.rip = BitVec.ofNat 64 cE →
    t.mem.accessible (t.regs 4).toNat 8 false = true → t.mem.readLE (t.regs 4).toNat 8 < 2 ^ 47 →
    (t.regs 14).toNat + 24 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 14).toNat + 16) 8 false = true →
    t.mem.readLE ((t.regs 14).toNat + 16) 8 + 40 < (t.regs 4).toNat →
    168 ≤ (t.regs 4).toNat → (t.regs 4).toNat + 8 ≤ 2 ^ 48 →
    t.mem.accessible ((t.regs 4).toNat - 168) 168 true = true → t.xmm 15 = 0 →
    t.mem.accessible (t.regs 0).toNat 8 true = true → (t.regs 0).toNat + 8 ≤ 2 ^ 48 →
    ((t.regs 4).toNat + 8 ≤ (t.regs 0).toNat ∨ (t.regs 0).toNat + 8 ≤ (t.regs 4).toNat - 168) →
    ReachesRet Extracted.program (retAddrOf t) t (fun t' => t'.regs 4 = t.regs 4 + 8 ∧
      t'.regs 5 = t.regs 5 ∧ t'.regs 14 = t.regs 14 ∧ t'.xmm 15 = t.xmm 15 ∧
      t'.mem.regions = t.mem.regions ∧
      MemFrame t.mem t'.mem [((t.regs 4).toNat - 168, (t.regs 4).toNat), ((t.regs 0).toNat, (t.regs 0).toNat + 8)] ∧
      t'.mem.readLE (t.regs 0).toNat 8 = cval (t.regs 3).toNat) := by
  intro t hpc h0 h0' h3 h4 h5 h7 h8 h9 hx15 hp1 hp2 hp3
  have hlt : (t.regs 3).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  by_cases hz : (t.regs 3).toNat % 16 = 0
  · janus64_run
    all_goals first | janus_frame | exact ⟨by janus_frame, by simp [cval, hz]⟩
  · janus64_run
    all_goals first | janus_frame | exact ⟨by janus_frame, by simp [cval, hz]⟩

/-- `holdCallee`'s glue (`MOVQ 8(SP), AX; MOVQ 16(SP), BX; JMP holdCallee`). -/
theorem cglue : ∀ t : State, t.rip = BitVec.ofNat 64 cGlue →
    t.mem.accessible ((t.regs 4).toNat + 8) 16 false = true → (t.regs 4).toNat + 24 ≤ 2 ^ 48 →
    ReachesRet Extracted.program (BitVec.ofNat 64 cE) t (fun t' =>
      t'.rip = BitVec.ofNat 64 cE ∧ t'.regs 4 = t.regs 4 ∧ t'.mem = t.mem ∧ t'.xmm = t.xmm ∧
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 8) 8) ∧
      t'.regs 3 = BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 16) 8) ∧
      (∀ r, r ≠ 0 → r ≠ 3 → t'.regs r = t.regs r)) := by
  intro t hpc hacc hsp
  janus64_run until [cE]
  intro r h0 h3; simp [h0, h3]

/-- `HoldPtr`'s glue after its own `morestack` call, the return pc of the `holdCallee` call, and
that of the `pick` call. -/
abbrev hGlue : Nat := Extracted.entry + 0x67
abbrev hRet : Nat := Extracted.entry + 0x45
abbrev pickRet : Nat := Extracted.entry + 0x33

/-- `pick`'s test `BTL $0, CX`. -/
theorem lsb32 (x : BitVec 64) : (BitVec.setWidth 32 x).getLsbD 0 = true ↔ x.toNat % 2 = 1 := by
  simp [BitVec.getLsbD, Nat.testBit, Nat.one_and_eq_mod_two]

/-- `p = &a[x & 1]`, as returned by `pick`. -/
def pN (t : State) : Nat := if (t.regs 0).toNat % 2 = 0 then (t.regs 4).toNat - 32 else (t.regs 4).toNat - 24

/-- The memory at the `holdCallee` call: the pushed `RBP`, the spilled `x`, `a = [x, x + 1]`, the
`pick` call's return address, `p`, and the `holdCallee` call's return address. -/
def M1 (t : State) : Memory :=
  ((((((t.mem.writeLE ((t.regs 4).toNat - 8) 8 (t.regs 5).toNat).writeLE ((t.regs 4).toNat + 8) 8
    (t.regs 0).toNat).writeLE ((t.regs 4).toNat - 32) 8 (t.regs 0).toNat).writeLE ((t.regs 4).toNat - 24) 8
    ((t.regs 0).toNat + 1)).writeLE ((t.regs 4).toNat - 64) 8 pickRet).writeLE ((t.regs 4).toNat - 16) 8
    (pN t)).writeLE ((t.regs 4).toNat - 64) 8 hRet

/-- `HoldPtr` from its entry to `holdCallee`'s entry, through the `pick` call. -/
theorem hpre : ∀ t : State, t.rip = BitVec.ofNat 64 Extracted.entry →
    (t.regs 14).toNat + 24 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 14).toNat + 16) 8 false = true →
    t.mem.readLE ((t.regs 14).toNat + 16) 8 < (t.regs 4).toNat →
    64 ≤ (t.regs 4).toNat → (t.regs 4).toNat + 16 ≤ 2 ^ 48 →
    t.mem.accessible ((t.regs 4).toNat - 64) 80 true = true →
    ReachesRet Extracted.program (BitVec.ofNat 64 cE) t (fun u =>
      u.regs 4 = t.regs 4 - 64 ∧ u.regs 0 = BitVec.ofNat 64 (pN t) ∧ u.regs 3 = t.regs 0 ∧
      u.regs 5 = t.regs 4 - 8 ∧ u.regs 14 = t.regs 14 ∧ u.xmm = t.xmm ∧ u.mem = M1 t) := by
  intro t hpc h3 h4 h5 h7 h8 h9
  janus64_run until [cE]
  · have hx : (t.regs 0).toNat % 2 = 1 := (lsb32 _).1 (by assumption)
    have hp : pN t = (t.regs 4).toNat - 24 := by simp only [pN, hx]; rfl
    refine ⟨?_, by simp only [M1, hp]; rfl⟩
    rw [hp]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := (t.regs 4).isLt; omega
  · have hx : (t.regs 0).toNat % 2 = 0 := by
      have h : ¬ (t.regs 0).toNat % 2 = 1 := fun h => (by assumption : ¬ _) ((lsb32 _).2 h)
      omega
    have hp : pN t = (t.regs 4).toNat - 32 := by simp only [pN, hx]; rfl
    refine ⟨?_, by simp only [M1, hp]; rfl⟩
    rw [hp]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := (t.regs 4).isLt; omega

/-- After the `holdCallee` call: `*p + a[0] + a[1]`, pop the frame and `RBP`, return. -/
theorem epi : ∀ t : State, t.rip = BitVec.ofNat 64 hRet →
    (t.regs 4).toNat + 64 ≤ 2 ^ 48 → t.mem.accessible ((t.regs 4).toNat + 24) 40 false = true →
    t.mem.accessible (t.mem.readLE ((t.regs 4).toNat + 40) 8) 8 false = true →
    t.mem.readLE ((t.regs 4).toNat + 40) 8 + 8 ≤ 2 ^ 48 →
    t.mem.readLE ((t.regs 4).toNat + 56) 8 < 2 ^ 47 →
    ReachesRet Extracted.program (BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 56) 8)) t (fun t' =>
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE (t.mem.readLE ((t.regs 4).toNat + 40) 8) 8) +
        BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 24) 8) +
        BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 32) 8) ∧
      t'.regs 4 = t.regs 4 + 64 ∧ t'.regs 5 = BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 48) 8) ∧
      t'.regs 14 = t.regs 14) := by
  intro t hpc h1 h2 h3 h4 h5
  janus64_run

/-- `HoldPtr`'s glue (`MOVQ 8(SP), AX; JMP HoldPtr`). -/
theorem glue : ∀ t : State, t.rip = BitVec.ofNat 64 hGlue →
    t.mem.accessible ((t.regs 4).toNat + 8) 8 false = true → (t.regs 4).toNat + 16 ≤ 2 ^ 48 →
    ReachesRet Extracted.program (BitVec.ofNat 64 Extracted.entry) t (fun t' =>
      t'.rip = BitVec.ofNat 64 Extracted.entry ∧ t'.regs 4 = t.regs 4 ∧ t'.mem = t.mem ∧ t'.xmm = t.xmm ∧
      t'.regs 0 = BitVec.ofNat 64 (t.mem.readLE ((t.regs 4).toNat + 8) 8) ∧
      (∀ r, r ≠ 0 → t'.regs r = t.regs r)) := by
  intro t hpc hacc hsp
  janus64_run until [Extracted.entry]
  all_goals first
    | (intro r h0; simp [h0])
    | exact ReachesRet.done rfl ⟨rfl, by simp [setRegF], rfl, rfl, by simp [setRegF],
        fun r h0 => by simp [setRegF, h0]⟩

/-- The binary's frame record of `holdCallee`, at its glue: no frame, largest frame 168 bytes,
`p` a pointer argument (the args map `[true]`), no stack objects. -/
def CTable (FT : FrameTable) : Prop :=
  FT.valid cGlue = true ∧ FT.stop cGlue = false ∧ FT.injected cGlue = false ∧
  FT.spdelta cGlue = 0 ∧ FT.maxspd cGlue = 168 ∧ FT.args cGlue = [true] ∧ FT.objs cGlue = []

/-- `CTable`, read off the binary's frame record of `holdCallee`. -/
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

/-- A one-word bitmap marks exactly its base. -/
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

/-- At the glue, `holdCallee`'s frame (`RSP = r`, `fp = r + 8`) marks its spilled pointer argument. -/
theorem cframe0 {FT : FrameTable} (hT : CTable FT) (r a : Nat) :
    frameCls Arch.amd64 FT cGlue r (r + 8) a = (a == r + 8) := by
  obtain ⟨-, -, -, -, -, ha, ho⟩ := hT
  have hv : Arch.amd64.varp r (r + 8) = r := by simp [Arch.varp]
  simp only [frameCls, hv, Arch.argp, ho, ha, List.any_nil, Bool.or_false, bitsAt_single]
  have e1 : decide (r + 8 = r + 16) = false := decide_eq_false (by omega)
  have e2 : decide (Arch.amd64.minLocals + r < r) = false :=
    decide_eq_false (by unfold Arch.minLocals; omega)
  rw [e1, e2, Bool.false_and, Bool.false_and, Bool.false_or, Bool.false_or]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, beq_iff_eq]; omega

/-- The environment: the frame table agrees with the binary's frame records, the laws of every
pclntab, and the stack pools apart from the runtime memory. -/
def Env (FT : FrameTable) (pool rt : List (Nat × Nat)) : Prop :=
  FT.Agrees Extracted.frames ∧ FT.InFrame Arch.amd64 ∧ FT.Aligned ∧ FT.CodeOutside pool ∧
    (∀ a n, InRanges a n pool → Outside a n rt)

/-- A frame pointer the move can adjust: into the stack, or outside every stack. -/
def BPOK (pool : List (Nat × Nat)) (lo hi v : Nat) : Prop := (lo ≤ v ∧ v < hi) ∨ Outside v 1 pool

/-- No move adjusts nothing. -/
theorem adjustWord_same (lo hi v : Nat) : adjustWord lo hi hi v = v := by
  simp only [adjustWord]; split <;> omega

/-- Two moves adjust a frame pointer as one. -/
theorem adjustWord_trans {pool : List (Nat × Nat)} {lo hi lo1 hi1 hi2 v : Nat}
    (hin : InRanges lo (hi - lo) pool) (hin1 : InRanges lo1 (hi1 - lo1) pool) (hsz : hi - lo ≤ hi1 - lo1)
    (hlh : lo ≤ hi) (hlh1 : lo1 ≤ hi1) (hv : BPOK pool lo hi v) :
    adjustWord lo1 hi1 hi2 (adjustWord lo hi hi1 v) = adjustWord lo hi hi2 v := by
  rcases hv with ⟨h1, h2⟩ | hout
  · have e1 : adjustWord lo hi hi1 v = v + hi1 - hi := by simp only [adjustWord]; exact if_pos ⟨h1, h2⟩
    have e2 : adjustWord lo hi hi2 v = v + hi2 - hi := by simp only [adjustWord]; exact if_pos ⟨h1, h2⟩
    rw [e1, e2]; simp only [adjustWord]; rw [if_pos ⟨by omega, by omega⟩]; omega
  · have hn : ¬ (lo ≤ v ∧ v < hi) := fun ⟨h1, h2⟩ => by
      have := InRanges.disjoint (InRanges.sub hin (a := v) (n := 1) h1 (by omega)) hout; omega
    have hn1 : ¬ (lo1 ≤ v ∧ v < hi1) := fun ⟨h1, h2⟩ => by
      have := InRanges.disjoint (InRanges.sub hin1 (a := v) (n := 1) h1 (by omega)) hout; omega
    have e1 : adjustWord lo hi hi1 v = v := by simp only [adjustWord]; exact if_neg hn
    have e2 : adjustWord lo hi hi2 v = v := by simp only [adjustWord]; exact if_neg hn
    rw [e1, e2]; simp only [adjustWord]; exact if_neg hn1

/-- `BPOK` survives a move. -/
theorem BPOK.mv {pool : List (Nat × Nat)} {lo hi lo1 hi1 v : Nat}
    (hin : InRanges lo (hi - lo) pool) (hsz : hi - lo ≤ hi1 - lo1) (hlh : lo ≤ hi) (hlh1 : lo1 ≤ hi1)
    (hv : BPOK pool lo hi v) : BPOK pool lo1 hi1 (adjustWord lo hi hi1 v) := by
  rcases hv with ⟨h1, h2⟩ | hout
  · left
    have e1 : adjustWord lo hi hi1 v = v + hi1 - hi := by simp only [adjustWord]; exact if_pos ⟨h1, h2⟩
    rw [e1]; omega
  · right
    have hn : ¬ (lo ≤ v ∧ v < hi) := fun ⟨h1, h2⟩ => by
      have := InRanges.disjoint (InRanges.sub hin (a := v) (n := 1) h1 (by omega)) hout; omega
    have e1 : adjustWord lo hi hi1 v = v := by simp only [adjustWord]; exact if_neg hn
    rw [e1]; exact hout

/-- An adjusted word is still a 64-bit value. -/
theorem adjustWord_lt {lo hi hi' v : Nat} (hv : v < 2 ^ 64) (hh : hi' ≤ 2 ^ 48) :
    adjustWord lo hi hi' v < 2 ^ 64 := by
  simp only [adjustWord]; split <;> omega

/-- The precondition of a call `holdCallee(p, x)`: the goroutine stack, the caller's `RBP`, the
return address, `X15 = 0`, the caller's walk (its return-address slots above the argument slots,
which its maps do not mark), `p` an 8-aligned word of the caller's region of the stack, the
`maxstacksize` bound, the readiness. -/
def PreC (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s : State) : Prop :=
  ∃ lo hi, GStack s.mem (s.regs 14).toNat lo hi ∧ Outside (s.regs 14).toNat 24 pool ∧
    4096 ≤ lo ∧ lo + 8 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 24 ≤ hi ∧ hi ≤ 2 ^ 48 ∧
    lo % 16 = 0 ∧ hi % 16 = 0 ∧ (s.regs 4).toNat % 8 = 0 ∧
    InRanges lo (hi - lo) pool ∧ PoolOK s.mem pool ∧ BPOK pool lo hi (s.regs 5).toNat ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0 ∧
    (∃ fs, Chain Arch.amd64 FT s.mem hi (s.mem.readLE (s.regs 4).toNat 8) ((s.regs 4).toNat + 8) none fs ∧
      (∀ f ∈ fs, FT.stop f.pc = false → (s.regs 4).toNat + 24 ≤ f.fp - 8) ∧
      framesCls Arch.amd64 FT fs ((s.regs 4).toNat + 8) = false ∧
      framesCls Arch.amd64 FT fs ((s.regs 4).toNat + 16) = false) ∧
    (s.regs 0).toNat % 8 = 0 ∧ (s.regs 4).toNat + 24 ≤ (s.regs 0).toNat ∧ (s.regs 0).toNat + 8 ≤ hi ∧
    2 * ((hi - (s.regs 4).toNat) + 168 + stackGuard) ≤ maxstacksize ∧
    H [] (s.regs 14).toNat 0 (rtView rt s.mem)

/-- What `holdCallee(p, x)` does, through a possible stack growth: it returns with the stack
`[lo, hi)` grown to `[lo', hi')`, `RSP` popped and moved, `RBP` adjusted, the caller's frames moved
(the argument slots and the word at `p` free), and `cval x` at the moved `p`. -/
def PostC (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s s' : State) : Prop :=
  ∃ lo hi lo' hi', GStack s.mem (s.regs 14).toNat lo hi ∧ GStack s'.mem (s.regs 14).toNat lo' hi' ∧
    hi - lo ≤ hi' - lo' ∧ 4096 ≤ lo' ∧ lo' % 16 = 0 ∧ hi' % 16 = 0 ∧ hi' ≤ 2 ^ 48 ∧
    InRanges lo' (hi' - lo') pool ∧
    s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat + 8 + hi' - hi) ∧
    s'.regs 5 = BitVec.ofNat 64 (adjustWord lo hi hi' (s.regs 5).toNat) ∧
    s'.regs 14 = s.regs 14 ∧
    (∀ fs, Chain Arch.amd64 FT s.mem hi (s.mem.readLE (s.regs 4).toNat 8) ((s.regs 4).toNat + 8) none fs →
      Moved (framesCls Arch.amd64 FT fs) pool lo hi hi' ((s.regs 4).toNat + 8)
        [((s.regs 4).toNat + 8, (s.regs 4).toNat + 24), ((s.regs 0).toNat, (s.regs 0).toNat + 8)]
        s.mem s'.mem) ∧
    s'.mem.readLE ((s.regs 0).toNat + hi' - hi) 8 = cval (s.regs 3).toNat ∧
    MemFrame s.mem s'.mem (pool ++ rt) ∧ H [] (s.regs 14).toNat 0 (rtView rt s'.mem)

/-- `holdCallee` on a stack where its frame fits. -/
theorem croom (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (henv : Env FT pool rt) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 cE) (hp : PreC FT pool rt H s)
    (hroom : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 40 < (s.regs 4).toNat) :
    GrownRet64 Extracted.program reloc (retAddrOf s) s (PostC FT pool rt H s) := by
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hbp, hr47, hx15,
    ⟨fs, hch, hfsp, hc8, hc16⟩, hp8, hp1, hp2, hfit, hH⟩ := hp
  obtain ⟨-, -, -, -, hPA⟩ := henv
  have hgs' := hgs
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
  have hacc := hpok.accessible hinp
  have hspL : lo + 928 + 40 < (s.regs 4).toNat := by rw [hgg] at hroom; exact hroom
  have hsp64 := (s.regs 4).isLt
  obtain ⟨k, t, hst, hpc', h4', h5', h14', -, hreg, hmf, hv⟩ := cbody s hpc
    (Arm64.Memory.accessible_read_of_write _ (Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))) hr47
    hg24 (Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)) hroom (by omega) (by omega)
    (Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hx15
    (Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) (by omega) (.inl (by omega))
  have hin : ∀ a n, lo ≤ a → a + n ≤ hi → InRanges a n pool := fun a n h1 h2 => hinp.sub h1 (by omega)
  have hmf' : MemFrame s.mem t.mem (pool ++ rt) := hmf.mono fun a n h => by
    simp only [outside_append] at h
    have e1 := InRanges.disjoint (hin ((s.regs 4).toNat - 168) 168 (by omega) (by omega)) h.1
    have e2 := InRanges.disjoint (hin (s.regs 0).toNat 8 (by omega) (by omega)) h.1
    simp only [outside_cons, outside_nil, and_true]; omega
  refine .done hst hpc' ⟨lo, hi, lo, hi, hgs, GStack.of_frame hgs hmf ?_, Nat.le_refl _, h4k, hal1,
    hal2, hhi48, hinp, ?_, ?_, h14', fun fs0 _ => ?_, by rw [Nat.add_sub_cancel]; exact hv, hmf', ?_⟩
  · have e1 := InRanges.disjoint (hin ((s.regs 4).toNat - 168) 168 (by omega) (by omega)) hgo
    have e2 := InRanges.disjoint (hin (s.regs 0).toNat 8 (by omega) (by omega)) hgo
    simp only [outside_cons, outside_nil, and_true]; omega
  · rw [h4']; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  · rw [h5', adjustWord_same, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · refine Moved.of_agree _ pool ⟨by omega, by omega⟩ h4k (by omega) (by omega) fun a h1 h2 hx => ?_
    simp only [outside_cons, outside_nil, and_true] at hx
    exact hmf.bytes (by simp only [outside_cons, outside_nil, and_true]; omega)
  · rw [rtView_eq_of_frame hmf hreg fun a ha => ?_]
    · exact hH
    · have e1 := InRanges.disjoint ha (hPA _ _ (hin ((s.regs 4).toNat - 168) 168 (by omega) (by omega)))
      have e2 := InRanges.disjoint ha (hPA _ _ (hin (s.regs 0).toNat 8 (by omega) (by omega)))
      simp only [outside_cons, outside_nil, and_true]; omega

/-- The memory at `holdCallee`'s `morestack` call: `p`, `x` spilled to `8(SP)`, `16(SP)`, the glue
address `v` pushed at `-8(SP)`. -/
abbrev stubMemC (s : State) (v : Nat) : Memory :=
  ((s.mem.writeLE ((s.regs 4).toNat + 8) 8 (s.regs 0).toNat).writeLE ((s.regs 4).toNat + 16) 8
    (s.regs 3).toNat).writeLE ((s.regs 4).toNat - 8) 8 v

set_option maxHeartbeats 4000000 in
/-- `holdCallee`'s growth path, from the `morestack` stub state `S`: the contract moves the stack,
the glue reloads `p` adjusted (a pointer argument) and `x` copied, the frame now fits (`croom`), and
the moves compose. -/
theorem cgrow (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (s : State) (hp : PreC FT pool rt H s)
    (hnoroom : ¬ s.mem.readLE ((s.regs 14).toNat + 16) 8 + 40 < (s.regs 4).toNat)
    (S : State) (hstub : ∃ name, Extracted.program.stubAt S.rip.toNat = some ⟨name, S.rip.toNat, .morestack⟩)
    (h4 : S.regs 4 = s.regs 4 - 8) (h5 : S.regs 5 = s.regs 5) (h14 : S.regs 14 = s.regs 14)
    (hmem : S.mem = stubMemC s cGlue) :
    ∃ s_r, reloc S s_r ∧ GrownRet64 Extracted.program reloc (retAddrOf s) s_r (PostC FT pool rt H s) := by
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hbp, hr47, hx15,
    ⟨fs, hch, hfsp, hc8, hc16⟩, hp8, hp1, hp2, hfit, hH⟩ := hp
  have henv' := henv
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
  have hT := ctable_of hA
  have hT0 := hT
  obtain ⟨hv, hst, hinj, hspd, hmx, -, -⟩ := hT0
  have hgs' := hgs
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero] at hglo hghi hgg
  rw [hgg] at hnoroom
  simp only [stackGuard] at hnoroom
  have hsp := (s.regs 4).isLt
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 8 := by
    rw [h4, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  have hgw : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 24 ≤ (s.regs 14).toNat := by
    have := InRanges.disjoint (InRanges.sub hinp (a := (s.regs 4).toNat - 8) (n := 32) (by omega) (by omega)) hgo
    omega
  have hrdm : ∀ a k, (a + k ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat ≤ a) →
      (a + k ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 24 ≤ a) → S.mem.readLE a k = s.mem.readLE a k := by
    intro a k h1 h2
    rw [hmem, stubMemC, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have haccm : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w := by
    intro a k w; rw [hmem, stubMemC, Arm64.Memory.accessible_writeLE, Arm64.Memory.accessible_writeLE,
      Arm64.Memory.accessible_writeLE]
  have hglue : gluePcOf S = cGlue := by
    simp only [gluePcOf, regSP]
    rw [hS4, hmem, stubMemC, Arm64.Memory.readLE_writeLE_self]; rfl
  have hfspS : fspOf S = (s.regs 4).toNat := by simp only [fspOf, regSP]; rw [hS4]; omega
  have hSp : S.mem.readLE ((s.regs 4).toNat + 8) 8 = (s.regs 0).toNat := by
    rw [hmem, stubMemC, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 0).isLt
  have hSx : S.mem.readLE ((s.regs 4).toNat + 16) 8 = (s.regs 3).toNat := by
    rw [hmem, stubMemC, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 3).isLt
  have hfb := hch.bounds
  have hchs : Chain Arch.amd64 FT S.mem hi (s.mem.readLE (s.regs 4).toNat 8) ((s.regs 4).toNat + 8) none fs :=
    Chain.congr hch (by omega) fun f hf hstp => by
      have := hfsp f hf hstp
      simp only [Arch.lrSlot]; exact hrdm _ _ (by omega) (by omega)
  have hfp0 : Arch.amd64.fp FT cGlue (s.regs 4).toNat = (s.regs 4).toNat + 8 := by
    simp [Arch.fp, hspd]
  have hchain : Chain Arch.amd64 FT S.mem hi cGlue (s.regs 4).toNat none
      (⟨cGlue, (s.regs 4).toNat, (s.regs 4).toNat + 8⟩ :: fs) := by
    have hlr : Arch.amd64.lrOf S.mem (s.regs 4).toNat ((s.regs 4).toNat + 8) none =
        s.mem.readLE (s.regs 4).toNat 8 := by
      simp only [Arch.lrOf, Nat.add_sub_cancel]; exact hrdm _ _ (by omega) (by omega)
    have := Chain.cons (A := Arch.amd64) (FT := FT) (m := S.mem) (hi := hi) (pc := cGlue)
      (sp := (s.regs 4).toNat) (lr0 := none) (fs := fs) hv hst hinj (by omega) (by rw [hfp0]; omega)
      (by rw [hfp0, hlr]; exact hchs)
    rw [hfp0] at this; exact this
  have hclsA : ∀ a, framesCls Arch.amd64 FT (⟨cGlue, (s.regs 4).toNat, (s.regs 4).toNat + 8⟩ :: fs) a =
      ((a == (s.regs 4).toNat + 8) || framesCls Arch.amd64 FT fs a) := by
    intro a; simp only [framesCls_cons, cframe0 hT]
  have hfit1 : 2 * (hi - lo) ≤ maxstacksize :=
    Nat.le_trans (by simp only [stackGuard] at hfit ⊢; omega) hfit
  have hm : MorestackPre64 Extracted.program FT pool rt H (s.regs 14).toNat lo hi S := by
    refine ⟨hstub, by simp only [regG]; rw [h14], ?_, hgo, ?_, ?_, ⟨hinp, hpok.of_accessible haccm⟩,
      ?_, ?_, ⟨hCO, hAl⟩, ?_⟩
    · refine ⟨hg24, by rw [haccm]; exact hgacc, ?_, ?_, ?_⟩ <;>
        simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero] <;>
        rw [hrdm _ _ (by omega) (by omega)]
      · exact hglo
      · exact hghi
      · exact hgg
    · simp only [regSP]; rw [hS4]; omega
    · simp only [regSP]; rw [hS4]; omega
    · rw [hglue, hfspS]; exact ⟨_, hchain⟩
    · rw [hglue, hfspS, hmx]; exact ⟨hfit1, hfit⟩
    · rw [hmem, stubMemC, rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega)))]
      exact hH
  obtain ⟨s_r, lo1, hi1, hre, hgr⟩ := hms _ lo hi S hm
  refine ⟨s_r, hre, ?_⟩
  obtain ⟨hg1, hg2, h4k1, hal1', hal2', hhi48', hinp1, happ⟩ := hgr.grows
  have hroom := hgr.room
  rw [hglue, hmx, hfspS] at hroom
  simp only [stackGuard] at hroom
  have hsp_r : (s_r.regs 4).toNat = (s.regs 4).toNat + hi1 - hi := by
    rw [show s_r.regs 4 = s_r.regs regSP from rfl, hgr.sp, hfspS, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hpok_r : PoolOK s_r.mem pool := hm.inPool.2.of_accessible hgr.frame.accessible
  have hacc_r : s_r.mem.accessible lo1 (hi1 - lo1) true = true := hpok_r.accessible hinp1
  have hpc_r : s_r.rip = BitVec.ofNat 64 cGlue := by rw [hgr.pc, retAddrOf, ← hglue]
  -- the glue
  obtain ⟨k, s_e, hstg, hepc, -, he4, hemem, hexm, he0, he3, her⟩ := cglue s_r hpc_r
    (Arm64.Memory.accessible_read_of_write _ (Arm64.Memory.accessible_mono _ hacc_r (by omega) (by omega)))
    (by omega)
  have he14 : s_e.regs 14 = s.regs 14 := by
    rw [her 14 (by decide) (by decide), show s_r.regs 14 = s_r.regs regG from rfl, hgr.gkeep, h14]
  have he5 : s_e.regs 5 = BitVec.ofNat 64 (adjustWord lo hi hi1 (s.regs 5).toNat) := by
    rw [her 5 (by decide) (by decide), show s_r.regs 5 = s_r.regs regFP from rfl, hgr.fp,
      show S.regs regFP = S.regs 5 from rfl, h5]
  have he4n : (s_e.regs 4).toNat = (s.regs 4).toNat + hi1 - hi := by rw [he4, hsp_r]
  -- the move
  have hmA := hgr.moved _ (by rw [hglue, hfspS]; exact hchain)
  rw [hfspS] at hmA
  have hcode := hCO _ hch.valid_head
  have hra : s_e.mem.readLE (s_e.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hemem, he4n, hmA.readLE_word_out (by omega) (by omega) (by omega) trivial
      (by rw [hrdm _ _ (by omega) (by omega)]; exact hcode.1), hrdm _ _ (by omega) (by omega)]
  have hche : Chain Arch.amd64 FT s_e.mem hi1 (s_e.mem.readLE (s_e.regs 4).toNat 8) ((s_e.regs 4).toNat + 8)
      none (fs.map (Frame.mv hi hi1)) := by
    rw [hra, hemem, he4n, show (s.regs 4).toNat + hi1 - hi + 8 = ((s.regs 4).toNat + 8) + hi1 - hi by omega]
    exact hchs.moved hmA hCO hAl (by omega) (by omega) fun _ _ _ => trivial
  have hcl : ∀ a, hi ≤ a + hi1 → framesCls Arch.amd64 FT (fs.map (Frame.mv hi hi1)) (a + hi1 - hi) =
      framesCls Arch.amd64 FT fs a := fun a ha => hch.framesCls_mv (by omega) (by omega) ha
  -- the arguments read back: `p` adjusted, `x` copied
  have hp_e : (s_e.regs 0).toNat = (s.regs 0).toNat + hi1 - hi := by
    rw [he0, hsp_r, show (s.regs 4).toNat + hi1 - hi + 8 = ((s.regs 4).toNat + 8) + hi1 - hi by omega,
      hmA.readLE_ptr (by omega) (by omega) (by omega) (by rw [hclsA]; simp) trivial
        (by rw [hSp]; omega) (by rw [hSp]; omega), hSp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hx_e : (s_e.regs 3).toNat = (s.regs 3).toNat := by
    rw [he3, hsp_r, show (s.regs 4).toNat + hi1 - hi + 16 = ((s.regs 4).toNat + 16) + hi1 - hi by omega,
      hmA.readLE_scalar (by omega) (by omega) (fun j hj => by
        rw [show (s.regs 4).toNat + 16 + j - ((s.regs 4).toNat + 16 + j) % 8 = (s.regs 4).toNat + 16 by omega,
          hclsA, hc16]; simp) trivial, hSx, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (s.regs 3).isLt
  obtain ⟨-, -, hge3, hge4, hge5⟩ := hgr.gstack
  simp only [gStackguard0, stackGuard] at hge5
  have hgse : GStack s_e.mem (s_e.regs 14).toNat lo1 hi1 := by rw [he14, hemem]; exact hgr.gstack
  -- the precondition on the new stack, which has room
  have hpe : PreC FT pool rt H s_e := by
    refine ⟨lo1, hi1, hgse, by rw [he14]; exact hgo, h4k1, by omega, by omega, hhi48', hal1', hal2',
      by omega, hinp1, by rw [hemem]; exact hpok_r, ?_, by rw [hra]; exact hr47,
      by rw [hexm]; exact hgr.zero, ⟨_, hche, fun f hf hstp => ?_, ?_, ?_⟩,
      by rw [hp_e]; omega, by rw [hp_e, he4n]; omega, by rw [hp_e]; omega, ?_, ?_⟩
    · rw [he5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (adjustWord_lt (s.regs 5).isLt hhi48')]
      exact BPOK.mv hinp (by omega) (by omega) (by omega) hbp
    · obtain ⟨f0, hf0, rfl⟩ := List.mem_map.1 hf
      obtain ⟨h1, h2, -⟩ := hfb f0 hf0
      have := hfsp f0 hf0 hstp
      simp only [Frame.mv]; rw [he4n]; omega
    · rw [he4n, show (s.regs 4).toNat + hi1 - hi + 8 = ((s.regs 4).toNat + 8) + hi1 - hi by omega,
        hcl _ (by omega)]
      exact hc8
    · rw [he4n, show (s.regs 4).toNat + hi1 - hi + 16 = ((s.regs 4).toNat + 16) + hi1 - hi by omega,
        hcl _ (by omega)]
      exact hc16
    · rw [he4n, show hi1 - ((s.regs 4).toNat + hi1 - hi) = hi - (s.regs 4).toNat by omega]; exact hfit
    · rw [he14, hemem]; exact hgr.ready
  have hroome : s_e.mem.readLE ((s_e.regs 14).toNat + 16) 8 + 40 < (s_e.regs 4).toNat := by
    rw [he14, hemem, hge5, he4n]; omega
  have hret_e : retAddrOf s_e = retAddrOf s := by rw [retAddrOf, retAddrOf, hra]
  refine GrownRet64.of_steps hstg ?_
  rw [← hret_e]
  refine (croom FT pool rt H reloc henv s_e hepc hpe hroome).mono fun s'' hq => ?_
  obtain ⟨loe, hie, lo2, hi2, hgse', hgs2, hsz, h4k2, hal12, hal22, hhi482, hinp2, hsp2, h52,
    h142, hmB, hv2, hmf, hH2⟩ := hq
  obtain ⟨e1, e2⟩ := GStack.unique hgse hgse'
  subst e1 e2
  refine ⟨lo, hi, lo2, hi2, hgs, by rw [← he14]; exact hgs2, by omega, h4k2, hal12, hal22, hhi482, hinp2,
    ?_, ?_, by rw [h142, he14], ?_, ?_, ?_, by rw [← he14]; exact hH2⟩
  · rw [hsp2, he4n]; congr 1; omega
  · rw [h52, he5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (adjustWord_lt (s.regs 5).isLt hhi48'),
      adjustWord_trans hinp hinp1 (by omega) (by omega) (by omega) hbp]
  · intro fs0 hfs0
    rw [Chain.unique hfs0 hch]
    have hmB' := hmB _ hche
    rw [he4n, hemem, hp_e] at hmB'
    have hB : Moved (framesCls Arch.amd64 FT (fs.map (Frame.mv hi hi1))) pool lo1 hi1 hi2
        (((s.regs 4).toNat + 8) + hi1 - hi) [((s.regs 4).toNat + hi1 - hi + 8, (s.regs 4).toNat + hi1 - hi + 24),
          ((s.regs 0).toNat + hi1 - hi, (s.regs 0).toNat + hi1 - hi + 8)] s_r.mem s''.mem := by
      rw [show (s.regs 4).toNat + 8 + hi1 - hi = (s.regs 4).toNat + hi1 - hi + 8 by omega]; exact hmB'
    have ex3al : ∀ r ∈ [((s.regs 4).toNat + 8, (s.regs 4).toNat + 24), ((s.regs 0).toNat, (s.regs 0).toNat + 8)],
        r.1 % 8 = 0 ∧ r.2 % 8 = 0 := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp <;> omega
    have hA1 := ((hmA.mono_base (base' := (s.regs 4).toNat + 8) (by omega) (by omega) (by omega)).mono_ex'
      (ex' := [((s.regs 4).toNat + 8, (s.regs 4).toNat + 24), ((s.regs 0).toNat, (s.regs 0).toNat + 8)])
      fun _ _ _ _ => trivial).cls_congr' (cls' := framesCls Arch.amd64 FT fs) ex3al fun a _ _ _ hx => by
        simp only [outside_cons, outside_nil, and_true] at hx
        rw [hclsA]
        have : (a == (s.regs 4).toNat + 8) = false := by simp; omega
        rw [this, Bool.false_or]
    have hAB := hA1.trans' (ex₃ := [((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
        ((s.regs 0).toNat, (s.regs 0).toNat + 8)]) hB
      (fun a ha _ => hcl a (by omega))
      (by omega)
      (fun a k ha hx => ⟨hx, by simp only [outside_cons, outside_nil, and_true] at hx ⊢; omega⟩)
    refine hAB.congr_src fun a ha _ hx => ?_
    simp only [outside_cons, outside_nil, and_true] at hx
    rw [hmem, stubMemC, Arm64.Memory.bytes_writeLE_outside _ (by omega),
      Arm64.Memory.bytes_writeLE_outside _ (by omega), Arm64.Memory.bytes_writeLE_outside _ (by omega)]
  · rw [show (s.regs 0).toNat + hi2 - hi = (s_e.regs 0).toNat + hi2 - hi1 by rw [hp_e]; omega, hv2, hx_e]
  · refine MemFrame.trans ?_ (hemem ▸ hmf) fun a k h => ⟨h, h⟩
    refine MemFrame.trans ?_ hgr.frame fun a k h => ⟨h, h⟩
    rw [hmem, stubMemC]
    exact (((MemFrame.refl s.mem _).writeLE_inRanges _ ((hinp.sub (by omega) (by omega)).append_left rt)).writeLE_inRanges _
      ((hinp.sub (by omega) (by omega)).append_left rt)).writeLE_inRanges _
      ((hinp.sub (by omega) (by omega)).append_left rt)

/-- **`holdCallee` through a possible stack growth, as a grown callee summary.** -/
theorem gcallee (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) :
    GSummary64 Extracted.program reloc cE (PreC FT pool rt H) (PostC FT pool rt H) := by
  intro s hpc hpre
  by_cases hroom : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 40 < (s.regs 4).toNat
  · exact croom FT pool rt H reloc henv s hpc hpre hroom
  · have hpre' := hpre
    obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hbp, hr47, hx15,
      -, hp8, hp1, hp2, hfit, hH⟩ := hpre'
    obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs
    simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
    have hacc := hpok.accessible hinp
    have hroom' : ¬ lo + 928 + 40 < (s.regs 4).toNat := by rw [hgg] at hroom; exact hroom
    apply GrownRet64.of_reaches_stub
    janus64_run
    exact cgrow FT pool rt H reloc hms henv s hpre hroom _ ⟨_, rfl⟩ (by simp [setRegF])
      (by simp [setRegF]) (by simp [setRegF]) rfl

/-- The binary's frame record of `HoldPtr`: at the glue no frame (largest frame 56 bytes), and at
the `holdCallee` call a 56-byte frame whose locals map marks the slot `40(SP)` that holds `p`. -/
def HTable (FT : FrameTable) : Prop :=
  FT.valid hGlue = true ∧ FT.stop hGlue = false ∧ FT.injected hGlue = false ∧
  FT.spdelta hGlue = 0 ∧ FT.maxspd hGlue = 56 ∧ FT.args hGlue = [] ∧ FT.objs hGlue = [] ∧
  FT.valid hRet = true ∧ FT.stop hRet = false ∧ FT.injected hRet = false ∧
  FT.spdelta hRet = 56 ∧ FT.locals hRet = [true] ∧ FT.args hRet = [] ∧ FT.objs hRet = []

/-- `HTable`, read off the binary's frame record of `HoldPtr`. -/
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

/-- `HoldPtr`'s frame suspended at the `holdCallee` call (`RSP = r - 56`, `fp = r + 8`) marks its
saved `RBP` slot `r - 8` and the slot `r - 16` that holds `p`. -/
theorem frameH {FT : FrameTable} (hT : HTable FT) {r : Nat} (h64 : 64 ≤ r) (a : Nat) :
    frameCls Arch.amd64 FT hRet (r - 56) (r + 8) a = ((a == r - 8) || (a == r - 16)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hl, ha, ho⟩ := hT
  have hv : Arch.amd64.varp (r - 56) (r + 8) = r - 8 := by simp [Arch.varp]; omega
  simp only [frameCls, hv, Arch.argp, ho, hl, ha, List.any_nil, Bool.or_false, bitsAt_single]
  rw [decide_eq_true (show r + 8 = r - 8 + 16 by omega), Bool.true_and,
    decide_eq_true (show Arch.amd64.minLocals + (r - 56) < r - 8 by simp [Arch.minLocals]; omega),
    Bool.true_and]
  have hb : bitsAt (((r + 8 : Nat) : Int)) [] a = false := by simp [bitsAt]
  rw [hb, Bool.or_false]
  congr 1
  rw [Bool.eq_iff_iff]; simp only [List.length_singleton, decide_eq_true_eq, beq_iff_eq]; omega

/-- At its own glue, `HoldPtr`'s frame (no pointer arguments) marks nothing. -/
theorem hframe0 {FT : FrameTable} (hT : HTable FT) (r a : Nat) :
    frameCls Arch.amd64 FT hGlue r (r + 8) a = false := by
  obtain ⟨-, -, -, -, -, ha, ho, -⟩ := hT
  have hv : Arch.amd64.varp r (r + 8) = r := by simp [Arch.varp]
  simp only [frameCls, hv, Arch.argp, ho, ha, List.any_nil, Bool.or_false]
  have e1 : decide (r + 8 = r + 16) = false := decide_eq_false (by omega)
  have e2 : decide (Arch.amd64.minLocals + r < r) = false :=
    decide_eq_false (by unfold Arch.minLocals; omega)
  rw [e1, e2, Bool.false_and, Bool.false_and, Bool.false_or]
  simp [bitsAt]

/-- `HoldPtr`'s result: `*p + a[0] + a[1]` after `holdCallee(p, x)` stored `v = cval x` at
`p = &a[x & 1]`. -/
def hres (x : BitVec 64) : BitVec 64 :=
  let v := BitVec.ofNat 64 (cval x.toNat)
  if x.toNat % 2 = 0 then v + v + (x + 1) else v + x + v

/-- The precondition of a call `HoldPtr(x)` (no room assumed). -/
def PreH (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady) (s : State) : Prop :=
  ∃ lo hi, GStack s.mem (s.regs 14).toNat lo hi ∧ Outside (s.regs 14).toNat 24 pool ∧
    4096 ≤ lo ∧ lo + 8 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 16 ≤ hi ∧ hi ≤ 2 ^ 48 ∧
    lo % 16 = 0 ∧ hi % 16 = 0 ∧ (s.regs 4).toNat % 8 = 0 ∧
    InRanges lo (hi - lo) pool ∧ PoolOK s.mem pool ∧ BPOK pool lo hi (s.regs 5).toNat ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0 ∧
    (∃ fs, Chain Arch.amd64 FT s.mem hi (s.mem.readLE (s.regs 4).toNat 8) ((s.regs 4).toNat + 8) none fs ∧
      (∀ f ∈ fs, FT.stop f.pc = false → (s.regs 4).toNat + 16 ≤ f.fp - 8) ∧
      framesCls Arch.amd64 FT fs ((s.regs 4).toNat + 8) = false) ∧
    2 * ((hi - (s.regs 4).toNat) + 64 + 168 + stackGuard) ≤ maxstacksize ∧
    H [] (s.regs 14).toNat 0 (rtView rt s.mem)

/-- What `HoldPtr(x)` returns. -/
def PostH (s s' : State) : Prop := s'.regs 0 = hres (s.regs 0)

set_option maxHeartbeats 4000000 in
/-- `HoldPtr` on a stack whose prologue check falls through: it runs to the `holdCallee` call, the
callee may grow the stack — moving this frame — and the reads after the call find `p` adjusted
(the locals map marks its slot) and `*p` the callee's store at the moved `a[x & 1]`. -/
theorem hroomH (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (t : State) (hpc : t.rip = BitVec.ofNat 64 Extracted.entry)
    (hp : PreH FT pool rt H t) (hroom : t.mem.readLE ((t.regs 14).toNat + 16) 8 < (t.regs 4).toNat) :
    GrownRet64 Extracted.program reloc (retAddrOf t) t (PostH t) := by
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hbp, hr47, hx15,
    ⟨fs, hch, hfsp, hc8⟩, hfit, hH⟩ := hp
  have henv' := henv
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
  have hT := htable_of hA
  have hgs' := hgs
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
  have hacc := hpok.accessible hinp
  have hspL : lo + 928 < (t.regs 4).toNat := by rw [hgg] at hroom; exact hroom
  have hsp64 := (t.regs 4).isLt
  have hx0 := (t.regs 0).isLt
  have hin : ∀ a k, lo ≤ a → a + k ≤ hi → InRanges a k pool := fun a k h1 h2 => hinp.sub h1 (by omega)
  obtain ⟨k1, u, hst1, hupc, hu4, hu0, hu3, hu5, hu14, hux, hum⟩ := hpre t hpc hg24
    (Arm64.Memory.accessible_mono _ hgacc (by omega) (by omega)) hroom (by omega) (by omega)
    (Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
  have hpN1 : pN t = (t.regs 4).toNat - 32 ∨ pN t = (t.regs 4).toNat - 24 := by unfold pN; split <;> simp
  have hu4n : (u.regs 4).toNat = (t.regs 4).toNat - 64 := by
    rw [hu4, BitVec.toNat_sub, show (64 : BitVec 64).toNat = 64 from rfl]; omega
  have hu0n : (u.regs 0).toNat = pN t := by
    rw [hu0, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases hpN1 with h | h <;> omega)
  -- the memory at the call
  have hagM1 : ∀ a k, (a + k ≤ (t.regs 4).toNat - 64 ∨ (t.regs 4).toNat ≤ a) →
      (a + k ≤ (t.regs 4).toNat + 8 ∨ (t.regs 4).toNat + 16 ≤ a) → (M1 t).readLE a k = t.mem.readLE a k := by
    intro a k h1 h2
    have := hpN1
    simp only [M1]
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have haccM1 : ∀ a k w, (M1 t).accessible a k w = t.mem.accessible a k w := by
    intro a k w; simp only [M1, Arm64.Memory.accessible_writeLE]
  have hM1ra : (M1 t).readLE ((t.regs 4).toNat - 64) 8 = hRet := by
    simp only [M1]; rw [Arm64.Memory.readLE_writeLE_self]; rfl
  have hM1a0 : (M1 t).readLE ((t.regs 4).toNat - 32) 8 = (t.regs 0).toNat := by
    simp only [M1]
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt hx0
  have hM1a1 : (M1 t).readLE ((t.regs 4).toNat - 24) 8 = ((t.regs 0).toNat + 1) % 2 ^ 64 := by
    simp only [M1]
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_self] <;> rfl
  have hM1p : (M1 t).readLE ((t.regs 4).toNat - 16) 8 = pN t := by
    simp only [M1]
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by rcases hpN1 with h | h <;> rw [h] <;> omega)
  have hM1r : (M1 t).readLE (t.regs 4).toNat 8 = t.mem.readLE (t.regs 4).toNat 8 :=
    hagM1 _ _ (by omega) (by omega)
  have hgsM1 : GStack (M1 t) (t.regs 14).toNat lo hi := by
    simp only [M1]
    refine GStack.writeLE (GStack.writeLE (GStack.writeLE (GStack.writeLE (GStack.writeLE (GStack.writeLE
      (GStack.writeLE hgs hgo (hin _ _ (by omega) (by omega))) hgo (hin _ _ (by omega) (by omega))) hgo
      (hin _ _ (by omega) (by omega))) hgo (hin _ _ (by omega) (by omega))) hgo (hin _ _ (by omega) (by omega)))
      hgo (hin _ _ (by omega) (by rcases hpN1 with h | h <;> omega))) hgo (hin _ _ (by omega) (by omega))
  -- the walk at the call: this frame, then the caller's
  have hfb := hch.bounds
  have hchM1 : Chain Arch.amd64 FT (M1 t) hi (t.mem.readLE (t.regs 4).toNat 8) ((t.regs 4).toNat + 8) none fs :=
    Chain.congr hch (by omega) fun f hf hstp => by
      have := hfsp f hf hstp
      simp only [Arch.lrSlot]; exact hagM1 _ _ (by omega) (by omega)
  have hT0 := hT
  obtain ⟨-, -, -, -, -, -, -, hTv', hTs', hTi', hTd', -, -, -⟩ := hT0
  have hfpF : Arch.amd64.fp FT hRet ((t.regs 4).toNat - 56) = (t.regs 4).toNat + 8 := by
    simp [Arch.fp, hTd']; omega
  have hchv : Chain Arch.amd64 FT (M1 t) hi hRet ((t.regs 4).toNat - 56) none
      (⟨hRet, (t.regs 4).toNat - 56, (t.regs 4).toNat + 8⟩ :: fs) := by
    have hlr : Arch.amd64.lrOf (M1 t) ((t.regs 4).toNat - 56) ((t.regs 4).toNat + 8) none =
        t.mem.readLE (t.regs 4).toNat 8 := by
      simp only [Arch.lrOf, Nat.add_sub_cancel]; exact hM1r
    have := Chain.cons (A := Arch.amd64) (FT := FT) (m := M1 t) (hi := hi) (pc := hRet)
      (sp := (t.regs 4).toNat - 56) (lr0 := none) (fs := fs) hTv' hTs' hTi' (by omega)
      (by rw [hfpF]; omega) (by rw [hfpF, hlr]; exact hchM1)
    rw [hfpF] at this; exact this
  have hclsF : ∀ a, framesCls Arch.amd64 FT (⟨hRet, (t.regs 4).toNat - 56, (t.regs 4).toNat + 8⟩ :: fs) a =
      (((a == (t.regs 4).toNat - 8) || (a == (t.regs 4).toNat - 16)) || framesCls Arch.amd64 FT fs a) := by
    intro a; simp only [framesCls_cons]; rw [frameH hT (by omega)]
  -- the callee's precondition
  have hchv' : Chain Arch.amd64 FT u.mem hi (u.mem.readLE (u.regs 4).toNat 8) ((u.regs 4).toNat + 8) none
      (⟨hRet, (t.regs 4).toNat - 56, (t.regs 4).toNat + 8⟩ :: fs) := by
    rw [hu4n, hum, hM1ra, show (t.regs 4).toNat - 64 + 8 = (t.regs 4).toNat - 56 by omega]; exact hchv
  have hpv : PreC FT pool rt H u := by
    refine ⟨lo, hi, by rw [hu14, hum]; exact hgsM1, by rw [hu14]; exact hgo, h4k, by omega,
      by omega, hhi48, hal1, hal2, by omega, hinp, by rw [hum]; exact hpok.of_accessible haccM1,
      ?_, ?_, by rw [hux]; exact hx15, ⟨_, hchv', fun f hf hstp => ?_, ?_, ?_⟩,
      by rw [hu0n]; rcases hpN1 with h | h <;> omega,
      by rw [hu0n, hu4n]; rcases hpN1 with h | h <;> omega, by rw [hu0n]; rcases hpN1 with h | h <;> omega,
      ?_, ?_⟩
    · left; rw [hu5, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
    · rw [hu4n, hum, hM1ra]; decide
    · rw [hu4n]
      rcases List.mem_cons.1 hf with rfl | hf
      · simp only; omega
      · have := hfsp f hf hstp; omega
    · rw [hu4n, show (t.regs 4).toNat - 64 + 8 = (t.regs 4).toNat - 56 by omega, hclsF,
        hch.framesCls_below hIF (by omega)]
      simp; omega
    · rw [hu4n, show (t.regs 4).toNat - 64 + 16 = (t.regs 4).toNat - 48 by omega, hclsF,
        hch.framesCls_below hIF (by omega)]
      simp; omega
    · rw [hu4n, show hi - ((t.regs 4).toNat - 64) = hi - (t.regs 4).toNat + 64 by omega]
      exact Nat.le_trans (Nat.le_of_eq (by omega)) hfit
    · rw [hu14, hum]; simp only [M1]
      rw [rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by rcases hpN1 with h | h <;> omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hin _ _ (by omega) (by omega)))]
      exact hH
  refine GrownRet64.of_steps hst1 (GrownRet64.call (gcallee FT pool rt H reloc hms henv) hupc hpv
    fun w hwpc hw => ?_)
  obtain ⟨lov, hiv, lo', hi', hgsv, hgsw, hsz, h4k', hal1', hal2', hhi48', hinp', hw4, hw5,
    hw14, hmv, hwv, hmf, hHw⟩ := hw
  rw [hu14, hum] at hgsv
  obtain ⟨e1, e2⟩ := GStack.unique hgsM1 hgsv
  subst e1 e2
  have hmvF := hmv _ hchv'
  rw [hu4n, hum, hu0n, show (t.regs 4).toNat - 64 + 8 = (t.regs 4).toNat - 56 by omega] at hmvF
  rw [hu0n, hu3] at hwv
  have hw4n : (w.regs 4).toNat = (t.regs 4).toNat - 56 + hi' - hi := by
    rw [hw4, hu4n, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hwpc' : w.rip = BitVec.ofNat 64 hRet := by rw [hwpc, retAddrOf, hu4n, hum, hM1ra]
  have hgro := hmvF.grows
  have hcode := hCO _ hch.valid_head
  have hexo : ∀ a, (a + 8 ≤ pN t ∨ pN t + 8 ≤ a) → (t.regs 4).toNat - 40 ≤ a →
      Outside a 8 [((t.regs 4).toNat - 56, (t.regs 4).toNat - 64 + 24), (pN t, pN t + 8)] := by
    intro a h1 h2; simp only [outside_cons, outside_nil, and_true]; omega
  -- the frame read back on the (possibly moved) stack
  have rP : w.mem.readLE ((w.regs 4).toNat + 40) 8 = pN t + hi' - hi := by
    rw [hw4n, show (t.regs 4).toNat - 56 + hi' - hi + 40 = ((t.regs 4).toNat - 16) + hi' - hi by omega,
      hmvF.readLE_ptr (by omega) (by omega) (by omega) (by rw [hclsF]; simp)
        (hexo _ (by rcases hpN1 with h | h <;> omega) (by omega))
        (by rw [hM1p]; rcases hpN1 with h | h <;> omega) (by rw [hM1p]; rcases hpN1 with h | h <;> omega),
      hM1p]
  have rRA : w.mem.readLE ((w.regs 4).toNat + 56) 8 = t.mem.readLE (t.regs 4).toNat 8 := by
    rw [hw4n, show (t.regs 4).toNat - 56 + hi' - hi + 56 = (t.regs 4).toNat + hi' - hi by omega,
      hmvF.readLE_word_out (by omega) (by omega) (by omega)
        (hexo _ (by rcases hpN1 with h | h <;> omega) (by omega)) (by rw [hM1r]; exact hcode.1), hM1r]
  have hscal : ∀ a, (a = (t.regs 4).toNat - 32 ∨ a = (t.regs 4).toNat - 24) → a ≠ pN t →
      w.mem.readLE (a + hi' - hi) 8 = (M1 t).readLE a 8 := by
    intro a ha hne
    have hpa : pN t + 8 ≤ a ∨ a + 8 ≤ pN t := by rcases hpN1 with h | h <;> rcases ha with h' | h' <;> omega
    exact hmvF.readLE_scalar (by omega) (by omega) (fun j hj => by
      rw [show a + j - (a + j) % 8 = a by omega, hclsF, hch.framesCls_below hIF (by omega)]
      simp; omega) (hexo _ (by omega) (by omega))
  -- the epilogue
  have hpok_w : PoolOK w.mem pool := hpok.of_accessible fun a k w' => by
    rw [hmf.accessible, hum, haccM1]
  have haccw : ∀ a k, lo' ≤ a → a + k ≤ hi' → w.mem.accessible a k false = true := fun a k h1 h2 =>
    Arm64.Memory.accessible_read_of_write _ (hpok_w.accessible (hinp'.sub h1 (by omega)))
  obtain ⟨k3, x, hst3, hxpc, hx0', hx4, hx5, hx14⟩ := epi w hwpc' (by omega)
    (haccw _ _ (by omega) (by omega))
    (by rw [rP]; exact haccw _ _ (by rcases hpN1 with h | h <;> omega) (by rcases hpN1 with h | h <;> omega))
    (by rw [rP]; rcases hpN1 with h | h <;> omega) (by rw [rRA]; exact hr47)
  refine .done hst3 (by rw [hxpc, rRA]; rfl) ?_
  show x.regs 0 = hres (t.regs 0)
  rw [hx0', rP, hw4n, show (t.regs 4).toNat - 56 + hi' - hi + 24 = ((t.regs 4).toNat - 32) + hi' - hi by omega,
    show (t.regs 4).toNat - 56 + hi' - hi + 32 = ((t.regs 4).toNat - 24) + hi' - hi by omega, hwv]
  by_cases he : (t.regs 0).toNat % 2 = 0
  · have hp : pN t = (t.regs 4).toNat - 32 := by unfold pN; rw [if_pos he]
    rw [← hp, hwv, hscal _ (.inr rfl) (by omega), hM1a1]
    have e : BitVec.ofNat 64 (((t.regs 0).toNat + 1) % 2 ^ 64) = t.regs 0 + 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_add, Nat.mod_mod]; rfl
    rw [e]; simp only [hres, if_pos he]
  · have hp : pN t = (t.regs 4).toNat - 24 := by unfold pN; rw [if_neg he]
    rw [← hp, hwv, hscal _ (.inl rfl) (by omega), hM1a0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [hres, if_neg he]

/-- The memory at `HoldPtr`'s own `morestack` call: `x` spilled, the glue address `v` pushed. -/
abbrev stubMemH (s : State) (v : Nat) : Memory :=
  (s.mem.writeLE ((s.regs 4).toNat + 8) 8 (s.regs 0).toNat).writeLE ((s.regs 4).toNat - 8) 8 v

set_option maxHeartbeats 4000000 in
/-- `HoldPtr`'s own growth: the contract moves the stack, the glue reloads `x` (copied), and the
frame now fits, so `hroomH` applies on the larger stack. -/
theorem hgrow (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (s : State) (hp : PreH FT pool rt H s)
    (hnoroom : ¬ s.mem.readLE ((s.regs 14).toNat + 16) 8 < (s.regs 4).toNat)
    (S : State) (hstub : ∃ name, Extracted.program.stubAt S.rip.toNat = some ⟨name, S.rip.toNat, .morestack⟩)
    (h4 : S.regs 4 = s.regs 4 - 8) (h5 : S.regs 5 = s.regs 5) (h14 : S.regs 14 = s.regs 14)
    (hmem : S.mem = stubMemH s hGlue) :
    ∃ s_r, reloc S s_r ∧ GrownRet64 Extracted.program reloc (retAddrOf s) s_r (PostH s) := by
  obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hbp, hr47, hx15,
    ⟨fs, hch, hfsp, hc8⟩, hfit, hH⟩ := hp
  have henv' := henv
  obtain ⟨hA, hIF, hAl, hCO, hPA⟩ := henv'
  have hT := htable_of hA
  have hT0 := hT
  obtain ⟨hv, hst, hinj, hspd, hmx, -, -⟩ := hT0
  have hgs' := hgs
  obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs'
  simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero] at hglo hghi hgg
  rw [hgg] at hnoroom
  simp only [stackGuard] at hnoroom
  have hsp := (s.regs 4).isLt
  have hS4 : (S.regs 4).toNat = (s.regs 4).toNat - 8 := by
    rw [h4, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  have hgw : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 16 ≤ (s.regs 14).toNat := by
    have := InRanges.disjoint (InRanges.sub hinp (a := (s.regs 4).toNat - 8) (n := 24) (by omega) (by omega)) hgo
    omega
  have hrdm : ∀ a k, (a + k ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat ≤ a) →
      (a + k ≤ (s.regs 4).toNat + 8 ∨ (s.regs 4).toNat + 16 ≤ a) → S.mem.readLE a k = s.mem.readLE a k := by
    intro a k h1 h2
    rw [hmem, stubMemH, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have haccm : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w := by
    intro a k w; rw [hmem, stubMemH, Arm64.Memory.accessible_writeLE, Arm64.Memory.accessible_writeLE]
  have hglue : gluePcOf S = hGlue := by
    simp only [gluePcOf, regSP]
    rw [hS4, hmem, stubMemH, Arm64.Memory.readLE_writeLE_self]; rfl
  have hfspS : fspOf S = (s.regs 4).toNat := by simp only [fspOf, regSP]; rw [hS4]; omega
  have hfb := hch.bounds
  have hchs : Chain Arch.amd64 FT S.mem hi (s.mem.readLE (s.regs 4).toNat 8) ((s.regs 4).toNat + 8) none fs :=
    Chain.congr hch (by omega) fun f hf hstp => by
      have := hfsp f hf hstp
      simp only [Arch.lrSlot]; exact hrdm _ _ (by omega) (by omega)
  have hfp0 : Arch.amd64.fp FT hGlue (s.regs 4).toNat = (s.regs 4).toNat + 8 := by
    simp [Arch.fp, hspd]
  have hchain : Chain Arch.amd64 FT S.mem hi hGlue (s.regs 4).toNat none
      (⟨hGlue, (s.regs 4).toNat, (s.regs 4).toNat + 8⟩ :: fs) := by
    have hlr : Arch.amd64.lrOf S.mem (s.regs 4).toNat ((s.regs 4).toNat + 8) none =
        s.mem.readLE (s.regs 4).toNat 8 := by
      simp only [Arch.lrOf, Nat.add_sub_cancel]; exact hrdm _ _ (by omega) (by omega)
    have := Chain.cons (A := Arch.amd64) (FT := FT) (m := S.mem) (hi := hi) (pc := hGlue)
      (sp := (s.regs 4).toNat) (lr0 := none) (fs := fs) hv hst hinj (by omega) (by rw [hfp0]; omega)
      (by rw [hfp0, hlr]; exact hchs)
    rw [hfp0] at this; exact this
  have hclsA : ∀ a, framesCls Arch.amd64 FT (⟨hGlue, (s.regs 4).toNat, (s.regs 4).toNat + 8⟩ :: fs) a =
      framesCls Arch.amd64 FT fs a := by
    intro a; simp only [framesCls_cons, hframe0 hT, Bool.false_or]
  have hfit1 : 2 * (hi - lo) ≤ maxstacksize :=
    Nat.le_trans (by simp only [stackGuard] at hfit ⊢; omega) hfit
  have hm : MorestackPre64 Extracted.program FT pool rt H (s.regs 14).toNat lo hi S := by
    refine ⟨hstub, by simp only [regG]; rw [h14], ?_, hgo, ?_, ?_, ⟨hinp, hpok.of_accessible haccm⟩,
      ?_, ?_, ⟨hCO, hAl⟩, ?_⟩
    · refine ⟨hg24, by rw [haccm]; exact hgacc, ?_, ?_, ?_⟩ <;>
        simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero] <;>
        rw [hrdm _ _ (by omega) (by omega)]
      · exact hglo
      · exact hghi
      · exact hgg
    · simp only [regSP]; rw [hS4]; omega
    · simp only [regSP]; rw [hS4]; omega
    · rw [hglue, hfspS]; exact ⟨_, hchain⟩
    · rw [hglue, hfspS, hmx]; exact ⟨hfit1, Nat.le_trans (by omega) hfit⟩
    · rw [hmem, stubMemH, rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega))),
        rtView_writeLE (hPA _ _ (hinp.sub (by omega) (by omega)))]
      exact hH
  obtain ⟨s_r, lo1, hi1, hre, hgr⟩ := hms _ lo hi S hm
  refine ⟨s_r, hre, ?_⟩
  obtain ⟨hg1, hg2, h4k1, hal1', hal2', hhi48', hinp1, happ⟩ := hgr.grows
  have hroom := hgr.room
  rw [hglue, hmx, hfspS] at hroom
  simp only [stackGuard] at hroom
  have hsp_r : (s_r.regs 4).toNat = (s.regs 4).toNat + hi1 - hi := by
    rw [show s_r.regs 4 = s_r.regs regSP from rfl, hgr.sp, hfspS, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hpok_r : PoolOK s_r.mem pool := hm.inPool.2.of_accessible hgr.frame.accessible
  have hacc_r : s_r.mem.accessible lo1 (hi1 - lo1) true = true := hpok_r.accessible hinp1
  have hpc_r : s_r.rip = BitVec.ofNat 64 hGlue := by rw [hgr.pc, retAddrOf, ← hglue]
  obtain ⟨k, s_e, hstg, hepc, -, he4, hemem, hexm, he0, her⟩ := glue s_r hpc_r
    (Arm64.Memory.accessible_read_of_write _ (Arm64.Memory.accessible_mono _ hacc_r (by omega) (by omega)))
    (by omega)
  have he14 : s_e.regs 14 = s.regs 14 := by rw [her 14 (by decide), show s_r.regs 14 = s_r.regs regG from rfl,
    hgr.gkeep, h14]
  have he5 : s_e.regs 5 = BitVec.ofNat 64 (adjustWord lo hi hi1 (s.regs 5).toNat) := by
    rw [her 5 (by decide), show s_r.regs 5 = s_r.regs regFP from rfl, hgr.fp, show S.regs regFP = S.regs 5 from rfl, h5]
  have he4n : (s_e.regs 4).toNat = (s.regs 4).toNat + hi1 - hi := by rw [he4, hsp_r]
  have hmA := hgr.moved _ (by rw [hglue, hfspS]; exact hchain)
  rw [hfspS] at hmA
  have hcode := hCO _ hch.valid_head
  have hra : s_e.mem.readLE (s_e.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hemem, he4n, hmA.readLE_word_out (by omega) (by omega) (by omega) trivial
      (by rw [hrdm _ _ (by omega) (by omega)]; exact hcode.1), hrdm _ _ (by omega) (by omega)]
  have hche : Chain Arch.amd64 FT s_e.mem hi1 (s_e.mem.readLE (s_e.regs 4).toNat 8) ((s_e.regs 4).toNat + 8)
      none (fs.map (Frame.mv hi hi1)) := by
    rw [hra, hemem, he4n, show (s.regs 4).toNat + hi1 - hi + 8 = ((s.regs 4).toNat + 8) + hi1 - hi by omega]
    exact hchs.moved hmA hCO hAl (by omega) (by omega) fun _ _ _ => trivial
  have hcl : ∀ a, hi ≤ a + hi1 → framesCls Arch.amd64 FT (fs.map (Frame.mv hi hi1)) (a + hi1 - hi) =
      framesCls Arch.amd64 FT fs a := fun a ha => hch.framesCls_mv (by omega) (by omega) ha
  have hx0e : (s_e.regs 0).toNat = (s.regs 0).toNat := by
    rw [he0, hsp_r, show (s.regs 4).toNat + hi1 - hi + 8 = ((s.regs 4).toNat + 8) + hi1 - hi by omega,
      hmA.readLE_scalar (by omega) (by omega) (fun j hj => by
        rw [show (s.regs 4).toNat + 8 + j - ((s.regs 4).toNat + 8 + j) % 8 = (s.regs 4).toNat + 8 by omega,
          hclsA, hc8]) trivial, hmem, stubMemH, Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)), Nat.mod_eq_of_lt (s.regs 0).isLt]
  obtain ⟨-, -, hge3, hge4, hge5⟩ := hgr.gstack
  simp only [gStackguard0, stackGuard] at hge5
  have hgse : GStack s_e.mem (s_e.regs 14).toNat lo1 hi1 := by rw [he14, hemem]; exact hgr.gstack
  have hpe : PreH FT pool rt H s_e := by
    refine ⟨lo1, hi1, hgse, by rw [he14]; exact hgo, h4k1, by omega, by omega, hhi48', hal1', hal2',
      by omega, hinp1, by rw [hemem]; exact hpok_r, ?_, by rw [hra]; exact hr47, by rw [hexm]; exact hgr.zero,
      ⟨_, hche, fun f hf hstp => ?_, ?_⟩, ?_, ?_⟩
    · rw [he5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (adjustWord_lt (s.regs 5).isLt hhi48')]
      exact BPOK.mv hinp (by omega) (by omega) (by omega) hbp
    · obtain ⟨f0, hf0, rfl⟩ := List.mem_map.1 hf
      obtain ⟨h1, h2, -⟩ := hfb f0 hf0
      have := hfsp f0 hf0 hstp
      simp only [Frame.mv]; rw [he4n]; omega
    · rw [he4n, show (s.regs 4).toNat + hi1 - hi + 8 = ((s.regs 4).toNat + 8) + hi1 - hi by omega,
        hcl _ (by omega)]
      exact hc8
    · rw [he4n, show hi1 - ((s.regs 4).toNat + hi1 - hi) = hi - (s.regs 4).toNat by omega]; exact hfit
    · rw [he14, hemem]; exact hgr.ready
  have hroome : s_e.mem.readLE ((s_e.regs 14).toNat + 16) 8 < (s_e.regs 4).toNat := by
    rw [he14, hemem, hge5, he4n]; omega
  have hret_e : retAddrOf s_e = retAddrOf s := by rw [retAddrOf, retAddrOf, hra]
  refine GrownRet64.of_steps hstg ?_
  rw [← hret_e]
  refine (hroomH FT pool rt H reloc hms henv s_e hepc hpe hroome).mono fun s'' hq => ?_
  show s''.regs 0 = hres (s.regs 0)
  rw [hq, show s_e.regs 0 = s.regs 0 from BitVec.eq_of_toNat_eq hx0e]

/-- **`HoldPtr` through stack growths**: its own prologue may grow the stack, and so may the
callee's, which moves `HoldPtr`'s frame — the pointer it holds included. -/
theorem hmain (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (s : State) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry)
    (hpre : PreH FT pool rt H s) :
    GrownRet64 Extracted.program reloc (retAddrOf s) s (PostH s) := by
  by_cases hroom : s.mem.readLE ((s.regs 14).toNat + 16) 8 < (s.regs 4).toNat
  · exact hroomH FT pool rt H reloc hms henv s hpc hpre hroom
  · have hpre' := hpre
    obtain ⟨lo, hi, hgs, hgo, h4k, hlo, hhi, hhi48, hal1, hal2, hal3, hinp, hpok, hbp, hr47, hx15, -,
      hfit, hH⟩ := hpre'
    obtain ⟨hg24, hgacc, hglo, hghi, hgg⟩ := hgs
    simp only [gStackLo, gStackHi, gStackguard0, Nat.add_zero, stackGuard] at hglo hghi hgg
    have hacc := hpok.accessible hinp
    have hroom' : ¬ lo + 928 < (s.regs 4).toNat := by rw [hgg] at hroom; exact hroom
    apply GrownRet64.of_reaches_stub
    janus64_run
    exact hgrow FT pool rt H reloc hms henv s hpre hroom _ ⟨_, rfl⟩ (by simp [setRegF])
      (by simp [setRegF]) (by simp [setRegF]) rfl

/-- **`HoldPtr` is correct on a stack of any size, stack growth included** (amd64). -/
theorem correctness (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (hms : MorestackContract64 Extracted.program FT pool rt H reloc)
    (henv : Env FT pool rt) (x : BitVec 64) :
    EnsuresGrow64 Extracted.program reloc Extracted.entry [x] (PreH FT pool rt H)
      (fun _ s' => s'.regs 0 = hres x) := by
  intro ret hret s hs hpre
  janus64_intro hs
  have hg := hmain FT pool rt H reloc hms henv s (by rw [h_rip]; rfl) hpre
  rw [retAddrOf, h_ret] at hg
  refine ((hg.withExit hret.fetch_none fun st hst => hret.notStub st hst).toGrownReturns
    (by have := hret.user; omega)).mono fun s' h => ?_
  show s'.regs 0 = hres x
  rw [h, h_a0]

/-! ## The theorem is not vacuous -/

namespace Witness

open Janus.Contracts.StackSat (G0 SL SH BL BH pool rt H mem0 mem0_desc)
open Janus.Contracts.StackSatAmd64 (reloc contract64)

/-- The caller's return address. -/
def ret : Nat := 0x200000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

/-- The witness frame table: the binary's frame records of `HoldPtr`, `pick` and `holdCallee`
(with their real pointer maps), and the caller, which stops the walk. -/
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

theorem laws : FTs.Aligned ∧ FTs.InFrame Arch.amd64 :=
  FrameTable.ofRecs_laws_amd64 Extracted.frames extraT (fun r hr => by
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨rfl, by decide⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨rfl, by decide⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨rfl, by decide⟩
      · simp at hr)
    (fun _ => rfl) (fun _ => rfl)

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
    have hlt : pc < 2 ^ 32 := by
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

/-- The memory: `StackSat`'s, with the return address at `[RSP]`. -/
def memw : Memory := mem0.writeLE spw 8 ret

/-- The call state `HoldPtr(16)` on the small 4 KiB stack of `StackSat` (`RBP = 0`). -/
def s0 : State :=
  { regs := fun i => if i = 14 then BitVec.ofNat 64 G0 else if i = 4 then BitVec.ofNat 64 spw
      else if i = 0 then 16#64 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := memw }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [16#64] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem memw_desc : memw.readLE G0 8 = SL ∧ memw.readLE (G0 + 8) 8 = SH ∧
    memw.readLE (G0 + 16) 8 = SL + stackGuard := by
  obtain ⟨d1, d2, d3⟩ := mem0_desc
  refine ⟨?_, ?_, ?_⟩ <;> unfold memw <;>
    rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by left; decide)] <;> assumption

/-- `HoldPtr`'s frame fits, but `holdCallee`'s (called with `RSP - 64`) does not: the stack grows
inside the callee, moving `HoldPtr`'s frame and the pointer `p` held in it. -/
theorem callee_grows : s0.mem.readLE ((s0.regs 14).toNat + 16) 8 < (s0.regs 4).toNat ∧
    ¬ s0.mem.readLE ((s0.regs 14).toNat + 16) 8 + 40 < (s0.regs 4).toNat - 64 := by
  have hg : (s0.regs 14).toNat = G0 := by decide
  rw [hg, show s0.mem = memw from rfl, memw_desc.2.2, show (s0.regs 4).toNat = spw by decide]
  decide

theorem pre : PreH FTs pool rt H s0 := by
  obtain ⟨d1, d2, d3⟩ := memw_desc
  have hin0 : InRanges G0 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hin8 : InRanges (G0 + 8) 8 rt := ⟨(G0, G0 + 24), List.mem_singleton_self _, by simp, by simp⟩
  have hg : (s0.regs 14).toNat = G0 := by decide
  have hsp : (s0.regs 4).toNat = spw := by decide
  have hr : s0.mem.readLE spw 8 = ret := by decide
  refine ⟨SL, SH, ?_, ?_, by decide, ?_, ?_, by decide, by decide, by decide, ?_,
    ⟨(SL, SH), by simp [pool], Nat.le_refl _, by decide⟩, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hg]; exact ⟨by decide, by decide, by simp only [gStackLo, Nat.add_zero]; exact d1, d2, d3⟩
  · rw [hg]; simp [pool, G0, SL, SH, BL, BH]
  · rw [hsp]; decide
  · rw [hsp]; decide
  · rw [hsp]; decide
  · intro r hr
    simp only [pool, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  · right; rw [show (s0.regs 5).toNat = 0 by decide]
    simp only [pool, outside_cons, outside_nil, and_true]; decide
  · rw [hsp, hr]; decide
  · have el : FTs.locals ret = [] := rfl
    have ea : FTs.args ret = [] := rfl
    have eo : FTs.objs ret = [] := rfl
    have e : Arch.amd64.fp FTs ret (spw + 8) = spw + 16 := by
      show spw + 8 + FTs.spdelta ret + 8 = spw + 16; rw [show FTs.spdelta ret = 0 from rfl]
    refine ⟨[⟨ret, spw + 8, spw + 16⟩], ?_, ?_, ?_⟩
    · rw [hsp, hr]
      have := Chain.stop (A := Arch.amd64) (FT := FTs) (m := s0.mem) (hi := SH) (pc := ret) (sp := spw + 8)
        (lr0 := none) rfl rfl rfl (by decide) (by rw [e]; decide)
      rw [e] at this; exact this
    · intro f hf hst; simp at hf; subst hf; exact absurd hst (by decide)
    · rw [hsp]; simp [frameCls, el, ea, eo, bitsAt, Arch.varp, Arch.argp, Arch.minLocals]
  · rw [hsp]; decide
  · rw [hg]; refine ⟨rfl, .inl ⟨?_, ?_⟩⟩
    · rw [readLE_rtView hin0]; exact d1
    · rw [readLE_rtView hin8]; exact d2

/-- All hypotheses of `correctness` hold together, for a call whose callee grows the stack. -/
theorem nonvacuous : ∃ (FT : FrameTable) (pool rt : List (Nat × Nat)) (H : RtReady)
    (reloc : State → State → Prop) (ret : Nat) (s : State),
    MorestackContract64 Extracted.program FT pool rt H reloc ∧ Env FT pool rt ∧
    RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [16#64] s ∧
    PreH FT pool rt H s ∧ (s.mem.readLE ((s.regs 14).toNat + 16) 8 < (s.regs 4).toNat ∧
      ¬ s.mem.readLE ((s.regs 14).toNat + 16) 8 + 40 < (s.regs 4).toNat - 64) :=
  ⟨FTs, pool, rt, H, reloc FTs, ret, s0, contract64 _ FTs, env, hret, setup, pre, callee_grows⟩

/-- So the guarantee is reached: `HoldPtr(16)` — `holdCallee` grows the stack and stores `16`
through the adjusted pointer into the moved array — returns `16 + 16 + 17 = 49`. -/
theorem returns : GrownReturns64 (Extracted.program.withExit ret) (reloc FTs) s0
    (fun s' => s'.regs 0 = 49#64) :=
  (correctness FTs pool rt H (reloc FTs) (contract64 _ FTs) env 16#64 ret hret s0 setup pre).mono
    fun s' h => by rw [h]; rfl

end Witness

end Proof
