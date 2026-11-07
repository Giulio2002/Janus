import Janus.Contracts.LiveStubSliceAmd64
import Janus.Contracts.LiveStubMemmoveUpto

/-!
# A variable-size live `memmove` stub (amd64): `memmove(dst = RAX, src = RBX, n = RCX)` for every `1 ≤ n ≤ N` (U-MEMMOVE-UPTO)

The amd64 twin of `LiveStubMemmoveUpto.lean`: a compare chain (`CMP RCX, k ; JE Lk` with a 32-bit displacement, `k = 1 … N`)
dispatches to the straight-line copy of exactly `k` bytes (`memmoveCodeN k`). `N ≤ 127` (an 8-bit immediate).
Tactic: `janus64_live_memmove_upto N hok`, `hok : ∀ args, ok a args → ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ N`.
-/

namespace Janus.Contracts.LiveStubAmd64

open Janus Janus.Amd64 Janus.Contracts

/-- `CMP RCX, k` (8-bit immediate, `k < 128`): 4 bytes. -/
def cmpRcx (k : Nat) : List Nat := [0x48, 0x83, 0xf9, k]

/-- `JE rel32` by `off` bytes forward from the end of the instruction: 6 bytes. -/
def jeFwd (off : Nat) : List Nat := [0x0f, 0x84] ++ [off % 256, off / 256 % 256, off / 65536 % 256, off / 16777216 % 256]

/-- Where the copy of exactly `k` bytes starts, in bytes from the segment base (10 bytes of chain per size, then one `RET`). -/
def blockStart64 (N k : Nat) : Nat := 10 * N + 1 + ((List.range (k - 1)).map fun j => (memmoveCodeN (j + 1)).length).sum

def memmoveUptoCode64 (N : Nat) : List Nat :=
  (List.range N).flatMap (fun j => cmpRcx (j + 1) ++ jeFwd (blockStart64 N (j + 1) - (10 * j + 10))) ++ [0xc3] ++
  ((List.range N).map fun j => memmoveCodeN (j + 1)).flatten

def memmoveUptoSeg64 (addr N : Nat) : Janus.Amd64.Segment := ⟨"live-stub.memmove", addr, memmoveUptoCode64 N⟩

end Janus.Contracts.LiveStubAmd64

/-- `MemmoveLive64 linked a 4096 (toyR [] ok)` for `LiveStubAmd64.memmoveUptoSeg64 a N`; `hok : ∀ args, ok a args → ∃ q p k,
args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ N`. -/
syntax "janus64_live_memmove_upto " num term:max : tactic
set_option hygiene false in
macro_rules
  | `(tactic| janus64_live_memmove_upto $N:num $ok) => `(tactic| (
      intro L b s hpc pre
      obtain ⟨⟨_, ⟨hra, hal, h3, h4, h5⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4, hd5⟩⟩ := pre
      obtain ⟨q0, p0, k, hargs, hk1, hk2⟩ := $ok _ hLm.1
      simp only [List.cons.injEq, and_true] at hargs
      have hn : (s.regs 1).toNat = k := hargs.2.2
      have hr1 : s.regs 1 = BitVec.ofNat 64 k := BitVec.eq_of_toNat_eq (by rw [hn]; simp; omega)
      rw [hn] at hs2 hd2 hd4 hd5
      have hap : Apart (s.regs 0).toNat k (s.regs 4).toNat 8 := by
        have h := hd5; simp only [outside_cons, outside_nil, and_true] at h; exact h
      change Janus.Amd64.Tactic.ReachesRet _ _ s _
      janus_split_k 1 $N (
        (janus64_run [hr1]; (try rw [hn]);
         open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
           Janus.Contracts.LiveStub Janus.Contracts.LiveStubAmd64 in
           refine liveMemRet_writes64 (copyWrites s.mem (s.regs 0).toNat (s.regs 3).toNat _)
             (copyWrites_sub _ _ _ _) (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
             (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl ?_ hd4 hLm.2.1 ?_;
         all_goals first
           | exact Janus.Contracts.LiveStub.copied_copyWrites _ _ _ _ _
           | ((try simp only [Janus.Contracts.LiveStub.readLE_mod_of_le, Nat.reducePow, Nat.reduceLeDiff]); rfl)))))
