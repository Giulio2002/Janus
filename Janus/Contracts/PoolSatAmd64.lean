import Janus.Contracts.PoolAmd64
import Janus.Contracts.PoolSat
import Janus.Contracts.LiveSatAmd64

/-!
# The `sync.Pool` live contracts are satisfiable (amd64)

For `PoolGetLive` and `PoolPutLive` of `Janus.Contracts.PoolAmd64`: machine code placed at the
address `A0` of a program with no other code, a proof by symbolic execution that it satisfies the
contract for the toy bump-allocator runtime `toyR` of `Janus.Contracts.LiveToy`, and a call state
that satisfies the whole precondition. As on arm64, `Get` always returns nil and `Put` drops its
argument. The file also holds the amd64 `growslice(p, 1, 0, 1, et)` toy the `sync.Pool` examples'
witnesses need (`growslice8_impl64`).
-/

namespace Janus.Contracts.PoolSatAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.PoolAmd64 Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveSatAmd64
open Janus.Contracts.Pool (PoolShape SliceObj dropAll mem_dropAll NewSame)
open Janus.Contracts.PoolSat (toyInv_drop)
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0 withCode)

/-- `Get` returning nil: `xor eax, eax; xor ebx, ebx; ret`. -/
def getCode : List Nat := [0x31, 0xc0, 0x31, 0xdb, 0xc3]
/-- `Put` dropping its argument: `ret`. -/
def putCode : List Nat := [0xc3]

/-- What a callee that returns normally keeps: `RET` to the return address with `RSP + 8`, `RBP`,
`R14`, `X15`, `FS`, the direction flag, `MXCSR` and the x87 state. -/
def KeepsABI (s s' : State) : Prop :=
  s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8#64 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
    s'.xmm 15 = s.xmm 15 ∧ s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
    s'.x87 = s.x87 ∧ s'.fpucw = s.fpucw

/-- The result of `getCode`. -/
def GetPost (s s' : State) : Prop :=
  s'.regs 0 = 0#64 ∧ s'.regs 3 = 0#64 ∧ s'.mem = s.mem ∧ KeepsABI s s'

/-- The result of `putCode`. -/
def PutPost (s s' : State) : Prop := s'.mem = s.mem ∧ KeepsABI s s'

/-- A return that keeps the ABI is a pool call's return state. -/
theorem pool_ret (s s' : State) (hk : KeepsABI s s') :
    s' = { s with regs := MapAmd64.keepABI s.regs s'.regs, xmm := MapAmd64.keepX15 s.xmm s'.xmm,
                  ymmHi := s'.ymmHi, flags := s'.flags, mem := s'.mem, rip := retAddrOf s,
                  zmmHi := s'.zmmHi, kreg := s'.kreg } := by
  obtain ⟨hrip, h4, h5, h14, hx, hfs, hdf, hmx, hx87, hfw⟩ := hk
  obtain ⟨r, rip, fl, xmm, mem, yh, fs, df, mx, x8, fw, zh, kr⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx hx87 hfw ⊢
  subst hrip hfs hdf hmx hx87 hfw
  have e1 : MapAmd64.keepABI s.regs r = r := by
    funext i
    simp only [MapAmd64.keepABI_apply]
    split
    · rename_i hi; subst hi; exact h4.symm
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · rfl
  have e2 : MapAmd64.keepX15 s.xmm xmm = xmm := by
    funext i
    simp only [MapAmd64.keepX15]
    split
    · rename_i hi; subst hi; exact hx.symm
    · rfl
  simp only [e1, e2]

set_option maxRecDepth 10000 in
/-- Every code that runs to the return with `GetPost` meets `PoolGetLive`. -/
theorem poolGetLive_of_run (tys : Tys) (p : Janus.Amd64.Program)
    (addr : Nat) (ok : Nat → List Nat → Prop) (T : Nat) (Sh : PoolShape)
    (hrun : ∀ s : State, s.rip = BitVec.ofNat 64 addr → s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 →
      (s.regs 4).toNat + 8 ≤ 2 ^ 48 → s.mem.accessible (s.regs 4).toNat 8 false = true →
      ReachesRet p (retAddrOf s) s (GetPost s)) :
    PoolGetLive p addr 4096 (toyR tys ok) T Sh := by
  intro L b s hpc ⟨⟨hra, hal, hst, h8, hacc⟩, _, _, _, hinv, _, _, _⟩
  have hrs : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega)
  obtain ⟨k, s', hst', hpc', hr0, hr3, hmem, habi⟩ := hrun s hpc hra (by omega) hrs
  refine ⟨k, s', hst', hpc', ?_⟩
  unfold LiveRet
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, s'.zmmHi, s'.kreg, pool_ret s s' habi, ?_, ?_, ?_, ?_⟩
  · rw [hmem]; exact MemFrame.refl _ _
  · rw [hmem]; exact LiveFrame.refl _ _ _
  · rw [hmem]; rfl
  · exact Or.inl ⟨by rw [hr0]; rfl, by rw [hr3]; rfl, by rw [hmem]; exact hinv⟩

set_option maxRecDepth 10000 in
/-- Every code that runs to the return with `PutPost` meets `PoolPutLive`. -/
theorem poolPutLive_of_run (tys : Tys) (hty : TysOK tys) (p : Janus.Amd64.Program) (addr : Nat)
    (ok : Nat → List Nat → Prop) (T : Nat) (Sh : PoolShape)
    (hrun : ∀ s : State, s.rip = BitVec.ofNat 64 addr → s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 →
      (s.regs 4).toNat + 8 ≤ 2 ^ 48 → s.mem.accessible (s.regs 4).toNat 8 false = true →
      ReachesRet p (retAddrOf s) s (PutPost s)) :
    PoolPutLive p addr 4096 (toyR tys ok) T Sh := by
  intro L b rs s hpc ⟨⟨hra, hal, hst, h8, hacc⟩, _, _, _, hsub, _, hinv, _, _, _⟩
  have hrs : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega)
  obtain ⟨k, s', hst', hpc', hmem, habi⟩ := hrun s hpc hra (by omega) hrs
  refine ⟨k, s', hst', hpc', ?_⟩
  unfold LiveRet
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, s'.zmmHi, s'.kreg, pool_ret s s' habi, ?_, ?_, ?_, ?_⟩
  · rw [hmem]; exact MemFrame.refl _ _
  · rw [hmem]; exact LiveFrame.refl _ _ _
  · rw [hmem]; rfl
  · rw [hmem]
    exact toyInv_drop hty (g := (s.regs 14).toNat) (fun r h => mem_dropAll h) hinv

set_option maxRecDepth 10000 in
theorem getCode_run : ∀ s : State, s.rip = BitVec.ofNat 64 A0 → s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 →
    (s.regs 4).toNat + 8 ≤ 2 ^ 48 → s.mem.accessible (s.regs 4).toNat 8 false = true →
    ReachesRet (withCode getCode) (retAddrOf s) s (GetPost s) := by
  intro s hpc hra h48 hrs
  janus64_run
  exact ⟨by simp [setRegF], by simp [setRegF], rfl, by simp [retAddrOf], by simp [setRegF], by simp [setRegF],
    by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 10000 in
theorem putCode_run : ∀ s : State, s.rip = BitVec.ofNat 64 A0 → s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 →
    (s.regs 4).toNat + 8 ≤ 2 ^ 48 → s.mem.accessible (s.regs 4).toNat 8 false = true →
    ReachesRet (withCode putCode) (retAddrOf s) s (PutPost s) := by
  intro s hpc hra h48 hrs
  janus64_run
  exact ⟨rfl, by simp [retAddrOf], by simp [setRegF], by simp [setRegF], by simp [setRegF], rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem poolGetLive_impl (ok : Nat → List Nat → Prop) (T : Nat) (Sh : PoolShape) :
    PoolGetLive (toy.link (at0 getCode)) A0 4096 (toyR tys0 ok) T Sh := by
  rw [link_at0]; exact poolGetLive_of_run tys0 _ _ ok T Sh getCode_run

theorem poolPutLive_impl (ok : Nat → List Nat → Prop) (T : Nat) (Sh : PoolShape) :
    PoolPutLive (toy.link (at0 putCode)) A0 4096 (toyR tys0 ok) T Sh := by
  rw [link_at0]; exact poolPutLive_of_run tys0 tysOK0 _ _ ok T Sh putCode_run

/-- The pool struct of the witnesses (its 40 bytes read as zero). -/
def POOL : Nat := 0x30100

def okPool : Nat → List Nat → Prop := fun _ args => args = [POOL]

/-- The witness call state of `Get`/`Put`: the pool in `RAX`, `T` in `RBX`. -/
def pstate : State := wst [POOL, 0x77]

set_option maxRecDepth 10000 in
theorem pstate_pre (n : Nat) (hn : n = 1 ∨ n = 3) :
    CallOK64 pstate 4096 n ∧ StackRoom64 pstate 4096 n ∧
      LiveAt (toyR tys0 okPool) A0 [(pstate.regs 0).toNat] [] 0x400 0 (pstate.regs 14).toNat pstate.mem
        (liveWin64 pstate 4096 n) := by
  have h0 : (pstate.regs 0).toNat = POOL := wr0 _ (by decide)
  refine ⟨wcallOK64 _ n (by omega), wguard64 _ n (by omega), ?_, wmem_inv (pstate.regs 14).toNat, by omega, by simp,
    wwin64 _ n (by omega)⟩
  rw [h0]; exact rfl

theorem pstate_new : pstate.mem.readLE ((pstate.regs 0).toNat + newOffset) 8 = 0 := by
  have h0 : (pstate.regs 0).toNat = POOL := wr0 _ (by decide)
  rw [h0]; unfold newOffset; decide

theorem poolGetLive_satisfiable : ∃ (R : RtInv) (T : Nat) (Sh : PoolShape) (impl : List Janus.Amd64.Segment),
    PoolGetLive (toy.link impl) A0 4096 R T Sh ∧
    ∃ (s : State) (L : List (Nat × Nat)) (b : Nat), s.rip = BitVec.ofNat 64 A0 ∧
      CallOK64 s 4096 1 ∧ StackRoom64 s 4096 1 ∧ s.mem.readLE ((s.regs 0).toNat + newOffset) 8 = 0 ∧
      LiveAt R A0 [(s.regs 0).toNat] L b 0 (s.regs 14).toNat s.mem (liveWin64 s 4096 1) :=
  ⟨toyR tys0 okPool, 0x77, SliceObj 8, at0 getCode, poolGetLive_impl okPool 0x77 (SliceObj 8), pstate, [], 0x400,
    rfl, (pstate_pre 1 (Or.inl rfl)).1, (pstate_pre 1 (Or.inl rfl)).2.1, pstate_new,
    (pstate_pre 1 (Or.inl rfl)).2.2⟩

theorem poolPutLive_satisfiable : ∃ (R : RtInv) (T : Nat) (Sh : PoolShape) (impl : List Janus.Amd64.Segment),
    PoolPutLive (toy.link impl) A0 4096 R T Sh ∧
    ∃ (s : State) (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)), s.rip = BitVec.ofNat 64 A0 ∧
      CallOK64 s 4096 3 ∧ StackRoom64 s 4096 3 ∧ (s.regs 3).toNat = T ∧ Sh s.mem (s.regs 1).toNat rs ∧
      (∀ r ∈ rs, r ∈ L) ∧
      LiveAt R A0 [(s.regs 0).toNat] L b 0 (s.regs 14).toNat s.mem (liveWin64 s 4096 3) :=
  ⟨toyR tys0 okPool, 0x77, fun _ _ rs => rs = [], at0 putCode, poolPutLive_impl okPool 0x77 _, pstate, [], 0x400, [],
    rfl, (pstate_pre 3 (Or.inr rfl)).1, (pstate_pre 3 (Or.inr rfl)).2.1, by decide, rfl, fun _ h => h,
    (pstate_pre 3 (Or.inr rfl)).2.2⟩

end Janus.Contracts.PoolSatAmd64
