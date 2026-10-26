import Janus.Contracts.LiveSat
import Janus.Contracts.LiveAmd64
import Janus.Contracts.AllocSatAmd64

/-!
# The live amd64 contracts are satisfiable

The amd64 counterpart of `Janus.Contracts.LiveSat`: x86-64 code for the bump-allocator toy of
`Janus.Contracts.LiveToy`, with its invariant `toyInv`, and a call state for every live contract
(`<contract>_satisfiable`, round 9 SAT row). The allocators here read the request's size from
the type descriptor, like the arm64 `…D` allocators (`LiveSat`), so the examples' witnesses reuse
them with descriptors in read-only data.
-/

namespace Janus.Contracts.LiveSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat
open Janus (MemFrame InRanges Outside outside_cons outside_nil)
open Janus.Contracts.AllocSatAmd64 (toy A0 at0 link_at0 ret_of)

/-- What every bump-allocating amd64 contract returns (one result register `RAX`): from the
invariant. `fin` is the state the code returns in; its fields are the hypotheses. -/
theorem bump_ret64 {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {K A stack nargs cost round b : Nat}
    {L : List (Nat × Nat)} {s : State} (hA : A % 16 = 0) (hKA : K ≤ A) (hA2 : A ≤ 64 * K) (hc : cost = K)
    (hr : round = K) (hb : K ≤ b)
    (hinv : (toyR tys ok).inv b L (s.regs 14).toNat (view (toyR tys ok).rt L s.mem))
    (hWs : LiveSep (liveWin64 s stack nargs) (toyR tys ok).rt)
    (res : W64 → List W64) (fin : State)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64) (h5 : fin.regs 5 = s.regs 5)
    (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase)
    (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (hres : ∀ p, s.mem.readLE BUMP 8 = p →
      fin.regs 0 = (res (BitVec.ofNat 64 p)).getD 0 (fin.regs 0) ∧
      fin.regs 3 = (res (BitVec.ofNat 64 p)).getD 1 (fin.regs 3) ∧
      fin.regs 1 = (res (BitVec.ofNat 64 p)).getD 2 (fin.regs 1) ∧
      fin.mem = s.mem.writeLE BUMP 8 (p + A))
    {Q : Memory → Nat → Prop}
    (hQ : ∀ p, HEAP ≤ p → p % 16 = 0 → p + K ≤ HEND →
      ZeroBytes (s.mem.writeLE BUMP 8 (p + A)) p K →
      (s.mem.writeLE BUMP 8 (p + A)).accessible p K true = true → ApartAll p K L →
      Q (s.mem.writeLE BUMP 8 (p + A)) p) :
    LiveAllocRet64 (toyR tys ok) stack nargs res L b cost round s fin Q := by
  rw [hc, hr]
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) := hinv
  obtain ⟨p, hpm, h1, h2, hendA, hfr, hlf, hap, hz, hacc, hinv'⟩ := toy_alloc hty hA hKA hA2 hb hinvT
  have hp : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; simp only [HEND] at hendA; omega
  obtain ⟨e0, e3, e1, hm⟩ := hres p hpm
  have hfin := AllocSatAmd64.ret_of s fin (res (BitVec.ofNat 64 p)) hrip h4 h5 h14 e0 e3 e1 hx hfs hdf hmx hx87 hfw
  rw [hm] at hfin
  have hWs' : LiveSep (calleeStack64 s stack nargs) (toyR tys ok).rt := fun r hr =>
    hWs r (by simp [liveWin64, hr])
  refine ⟨BitVec.ofNat 64 p, fin.regs, fin.flags, fin.xmm, fin.ymmHi, s.mem.writeLE BUMP 8 (p + A), fin.zmmHi, fin.kreg,
    hfin, ?_, hlf, ?_, ?_, ?_⟩
  · exact hfr.mono fun a n h => by simp only [outside_append] at h ⊢; exact h.1
  · simp only [hp]; exact hQ p h1 h2 (by omega) hz hacc hap
  · simp only [hp]; exact apart_win (inRanges_heap (by omega) (by omega : p + K ≤ HEND)) hWs
  · simp only [hp]; exact hinv'


/-- `mov r9d, BUMP; mov rcx,[rax]; imul rcx,rcx,64; mov rax,[r9]; lea r10,[rax+rcx]; mov [r9],r10; ret`:
`newobject` for any type; the advance is `64·Size_`. -/
def newobjectCodeD : List Nat :=
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x48, 0x8b, 0x08, 0x48, 0x6b, 0xc9, 0x40, 0x49, 0x8b, 0x01,
   0x4c, 0x8d, 0x14, 0x08, 0x4d, 0x89, 0x11, 0xc3]

theorem finish_newobjectD {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr b : Nat}
    {L : List (Nat × Nat)} {s : State} (fin : State)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64) (h5 : fin.regs 5 = s.regs 5)
    (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase)
    (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8))
    (hmem : fin.mem = s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + s.mem.readLE (s.regs 0).toNat 8 * 64 % 2 ^ 64))
    (pre : NewobjectPre64 4096 s ∧ StackRoom64 s 4096 1 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat] L b (newobjectRound64 s) (s.regs 14).toNat s.mem
        (liveWin64 s 4096 1)) :
    LiveAllocRet64 (toyR tys ok) 4096 1 (fun ptr => [ptr]) L b (newobjectRound64 s) (newobjectRound64 s) s fin
      fun m ptr => 0 < typSize s.mem (s.regs 0).toNat →
        newobjectObj64 (toyR tys ok).rt s m ptr ∧ ApartAll ptr (newobjectRound64 s) L := by
  obtain ⟨⟨-, -, hmax⟩, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  simp only [typSize, maxAlloc] at hmax
  have hmod : s.mem.readLE (s.regs 0).toNat 8 * 64 % 2 ^ 64 = 64 * s.mem.readLE (s.regs 0).toNat 8 := by omega
  have hK : newobjectRound64 s ≤ 64 * s.mem.readLE (s.regs 0).toNat 8 := blockSize_le64 _ _
  have hKX : s.mem.readLE (s.regs 0).toNat 8 ≤ newobjectRound64 s := AllocSat.le_blockSize _ _
  refine bump_ret64 hty (A := 64 * s.mem.readLE (s.regs 0).toNat 8) (by omega) hK (by omega) rfl rfl hcost hinv hWs _ fin
    hrip h4 h5 h14 hx hfs hdf hmx hx87 hfw (fun p hp => ⟨?_, by simp, by simp, ?_⟩)
    (fun p h1 h2' hend hz hacc hap _ => ⟨toy_fresh h1 h2' hend hz hacc _ hKX _ _, hap⟩)
  · rw [h0, hp]; simp
  · rw [hmem, hmod, hp]

set_option maxRecDepth 20000 in
theorem newobjectD_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    NewobjectLiveContract64 (toy.link (at0 newobjectCodeD)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  have hWs := pre.2.2.2.2.2.2
  have hret : Outside (s.regs 4).toNat 8 (toyRt tys) := by
    have h := hWs ((s.regs 4).toNat, (s.regs 4).toNat + 8) (by simp [liveWin64])
    simp only [Nat.add_sub_cancel_left] at h
    exact h
  have hap : Apart 4194304 8 (s.regs 4).toNat 8 := ((inRanges_bump tys).apart hret).symm
  janus64_run
  exact finish_newobjectD hty _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp [setRegF, BUMP]) (by simp [BUMP]) pre


def makesliceCodeD : List Nat :=
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x48, 0x8b, 0x10, 0x48, 0x0f, 0xaf, 0xd1, 0x48, 0x6b, 0xd2, 0x40,
   0x49, 0x8b, 0x01, 0x4c, 0x8d, 0x14, 0x10, 0x4d, 0x89, 0x11, 0xc3]
def mallocgcCodeD : List Nat :=
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x48, 0x6b, 0xd0, 0x40, 0x49, 0x8b, 0x01, 0x4c, 0x8d, 0x14, 0x10,
   0x4d, 0x89, 0x11, 0xc3]

theorem finish_makesliceD {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr b : Nat}
    {L : List (Nat × Nat)} {s : State} (fin : State)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64) (h5 : fin.regs 5 = s.regs 5)
    (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase)
    (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8))
    (hmem : fin.mem = s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 +
      s.mem.readLE (s.regs 0).toNat 8 * (s.regs 1).toNat * 64 % 2 ^ 64))
    (pre : MakeslicePre64 4096 s ∧ StackRoom64 s 4096 3 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (makesliceRound64 s)
        (s.regs 14).toNat s.mem (liveWin64 s 4096 3)) :
    LiveAllocRet64 (toyR tys ok) 4096 3 (fun ptr => [ptr]) L b (makesliceRound64 s) (makesliceRound64 s) s fin
      fun m ptr => 0 < typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat →
        makesliceObj64 (toyR tys ok).rt s m ptr ∧ ApartAll ptr (makesliceRound64 s) L := by
  obtain ⟨⟨-, -, -, -, hmax⟩, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  simp only [typSize, maxAlloc] at hmax
  have hmod : s.mem.readLE (s.regs 0).toNat 8 * (s.regs 1).toNat * 64 % 2 ^ 64 =
      64 * (s.mem.readLE (s.regs 0).toNat 8 * (s.regs 1).toNat) := by
    generalize s.mem.readLE (s.regs 0).toNat 8 * (s.regs 1).toNat = X at hmax ⊢
    omega
  have hK : makesliceRound64 s ≤ 64 * (s.mem.readLE (s.regs 0).toNat 8 * (s.regs 1).toNat) := blockSize_le64 _ _
  have hKX : s.mem.readLE (s.regs 0).toNat 8 * (s.regs 1).toNat ≤ makesliceRound64 s := AllocSat.le_blockSize _ _
  refine bump_ret64 hty (A := 64 * (s.mem.readLE (s.regs 0).toNat 8 * (s.regs 1).toNat)) (by omega) hK (by omega)
    rfl rfl hcost hinv hWs _ fin hrip h4 h5 h14 hx hfs hdf hmx hx87 hfw (fun p hp => ⟨?_, by simp, by simp, ?_⟩)
    (fun p h1 h2' hend hz hacc hap _ => ⟨toy_fresh h1 h2' hend hz hacc _ hKX _ _, hap⟩)
  · rw [h0, hp]; simp
  · rw [hmem, hmod, hp]

theorem finish_mallocgcD {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr b : Nat}
    {L : List (Nat × Nat)} {s : State} (fin : State)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64) (h5 : fin.regs 5 = s.regs 5)
    (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase)
    (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8))
    (hmem : fin.mem = s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + (s.regs 0).toNat * 64 % 2 ^ 64))
    (pre : MallocgcPre64 4096 s ∧ StackRoom64 s 4096 3 ∧
      LiveAt (toyR tys ok) addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s)
        (s.regs 14).toNat s.mem (liveWin64 s 4096 3)) :
    LiveAllocRet64 (toyR tys ok) 4096 3 (fun ptr => [ptr]) L b (mallocgcRound64 s) (mallocgcRound64 s) s fin
      fun m ptr => 0 < (s.regs 0).toNat →
        mallocgcObj64 (toyR tys ok).rt s m ptr ∧ ApartAll ptr (mallocgcRound64 s) L := by
  obtain ⟨⟨-, hmax, -⟩, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  simp only [maxAlloc] at hmax
  have hmod : (s.regs 0).toNat * 64 % 2 ^ 64 = 64 * (s.regs 0).toNat := by omega
  have hK : mallocgcRound64 s ≤ 64 * (s.regs 0).toNat := blockSize_le64 _ _
  have hKX : (s.regs 0).toNat ≤ mallocgcRound64 s := AllocSat.le_blockSize _ _
  refine bump_ret64 hty (A := 64 * (s.regs 0).toNat) (by omega) hK (by omega) rfl rfl hcost hinv hWs _ fin
    hrip h4 h5 h14 hx hfs hdf hmx hx87 hfw (fun p hp => ⟨?_, by simp, by simp, ?_⟩)
    (fun p h1 h2' hend hz hacc hap _ => ⟨toy_fresh h1 h2' hend hz hacc _ hKX _ _, hap⟩)
  · rw [h0, hp]; simp
  · rw [hmem, hmod, hp]

/-- The facts a run of an allocator at `RSP` needs: the return slot is outside `rt`, hence apart from
the bump cell. -/
theorem bump_apart64 {tys : Tys} {ok : Nat → List Nat → Prop} {s : State} {n : Nat}
    (hWs : LiveSep (liveWin64 s 4096 n) (toyR tys ok).rt) : Apart 4194304 8 (s.regs 4).toNat 8 := by
  have h := hWs ((s.regs 4).toNat, (s.regs 4).toNat + 8) (by simp [liveWin64])
  simp only [Nat.add_sub_cancel_left] at h
  exact ((inRanges_bump tys).apart h).symm

set_option maxRecDepth 20000 in
theorem makesliceD_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    MakesliceLiveContract64 (toy.link (at0 makesliceCodeD)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
  obtain ⟨hT1, hT2⟩ := hq6
  have hap := bump_apart64 pre.2.2.2.2.2.2
  janus64_run
  exact finish_makesliceD hty _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp [setRegF, BUMP]) (by simp [BUMP]) pre

set_option maxRecDepth 20000 in
theorem mallocgcD_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) :
    MallocgcLiveContract64 (toy.link (at0 mallocgcCodeD)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨hra, hal, h3, h4, h5⟩, hq6, hq7⟩ := pre.1
  have hap := bump_apart64 pre.2.2.2.2.2.2
  janus64_run
  exact finish_mallocgcD hty _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp [setRegF, BUMP]) (by simp [BUMP]) pre


/-! ### `growslice` -/

/-- `mov r9d, BUMP; mov rax,[r9]; lea r10,[rax+16]; mov [r9],r10; mov ecx, 2; ret`. -/
def growCode16 : List Nat :=
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x49, 0x8b, 0x01, 0x4c, 0x8d, 0x50, 0x10, 0x4d, 0x89, 0x11,
   0xb9, 0x02, 0x00, 0x00, 0x00, 0xc3]

theorem finish_growslice {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {addr b : Nat}
    {L : List (Nat × Nat)} {s : State} (fin : State)
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64) (h5 : fin.regs 5 = s.regs 5)
    (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase)
    (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (h0 : fin.regs 0 = BitVec.ofNat 64 (s.mem.readLE BUMP 8)) (h3 : fin.regs 3 = s.regs 3)
    (h1 : fin.regs 1 = 2#64)
    (hmem : fin.mem = s.mem.writeLE BUMP 8 (s.mem.readLE BUMP 8 + 16))
    (hok' : ∀ args, ok addr args → ∃ p et, args = [p, 2, 0, 2, et])
    (pre : GrowslicePre64 4096 s ∧ StackRoom64 s 4096 5 ∧
      LiveAt (toyR tys ok) addr (growsliceArgs64 s) L b (growsliceRound64 s) (s.regs 14).toNat s.mem
        (liveWin64 s 4096 5)) :
    LiveAllocRet64 (toyR tys ok) 4096 5
      (fun ptr => [ptr, s.regs 3, BitVec.ofNat 64 (growCap8 (s.regs 3).toNat (s.regs 1).toNat)])
      L b (growsliceRound64 s) (growsliceRound64 s) s fin fun m ptr =>
        growsliceObj64 (toyR tys ok).rt s m ptr ∧ ApartAll ptr (growsliceRound64 s) L := by
  obtain ⟨-, -, hok, hinv, hcost, hLs, hWs⟩ := pre
  obtain ⟨p0, et, hargs⟩ := hok' _ hok
  simp only [growsliceArgs64, List.cons.injEq, and_true] at hargs
  obtain ⟨-, e3, e1, e7, -⟩ := hargs
  have hg : growCap8 2 0 = 2 := by decide
  have hR : growsliceRound64 s = 16 := by simp only [growsliceRound64, e3, e1, hg]
  rw [hR] at hcost ⊢
  refine bump_ret64 hty (A := 16) (by omega) (by omega) (by omega) rfl rfl hcost hinv hWs _ fin
    hrip h4 h5 h14 hx hfs hdf hmx hx87 hfw (fun p hp => ⟨?_, ?_, ?_, ?_⟩)
    (fun p h1' h2' hend hz hacc hap => ⟨?_, hap⟩)
  · rw [h0, hp]; simp
  · simp [h3]
  · simp only [e3, e1, hg]; simpa using h1
  · rw [hmem, hp]
  · simp only [growsliceObj64, e3, e1, e7, hg]
    refine ⟨toy_fresh h1' h2' hend hz hacc _ (by omega) _ _, fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩

set_option maxRecDepth 20000 in
theorem growslice16_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ p et, args = [p, 2, 0, 2, et]) :
    GrowsliceLiveContract64 (toy.link (at0 growCode16)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  have hacB' := bump_acc pre.2.2.2.1
  have ⟨⟨⟨hra, hal, h3, h4, h5⟩, _, _, _, _, _, _, _⟩, _⟩ := pre.1
  have hap := bump_apart64 pre.2.2.2.2.2.2
  janus64_run
  exact finish_growslice hty _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp [setRegF, BUMP]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [BUMP]) hok' pre


/-! ### The write barrier -/

/-- `mov r11d, WBUF; ret`. -/
def wbCode : List Nat := [0x41, 0xbb, 0x00, 0x01, 0x40, 0x00, 0xc3]

theorem wb_post64 {tys : Tys} (hty : TysOK tys) {ok : Nat → List Nat → Prop} {n b : Nat} (hn : n ≤ 8)
    {L : List (Nat × Nat)} {s : State} {fin : State}
    (hinv : (toyR tys ok).inv b L (s.regs 14).toNat (view (toyR tys ok).rt L s.mem))
    (hWs : LiveSep [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] (toyR tys ok).rt)
    (hrip : fin.rip = retAddrOf s)
    (hregs : ∀ i, fin.regs i = if i = 4 then s.regs 4 + 8#64 else if i = 11 then 4194560#64 else s.regs i)
    (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df)
    (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (hmem : fin.mem = s.mem) :
    ∃ (buf : W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
        (zh : Nat → BitVec 256) (kr : Nat → W64),
      fin = wbRetX64 s buf f x yh m zh kr ∧
      MemFrame s.mem m ((toyR tys ok).rt ++ [((s.regs 4).toNat - 4096, (s.regs 4).toNat)]) ∧ LiveFrame s.mem m L [] ∧
      WbSlots (toyR tys ok).rt m buf.toNat n ∧ ApartAll buf.toNat (8 * n) L ∧
      Apart buf.toNat (8 * n) ((s.regs 4).toNat - 4096)
        ((s.regs 4).toNat + 8 - ((s.regs 4).toNat - 4096)) ∧
      InvSlots (toyR tys ok) b L (s.regs 14).toNat (toyR tys ok).rt m buf.toNat n := by
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) := hinv
  have hb : (4194560#64 : W64).toNat = WBUF := by decide
  have ⟨p, _, _, _, _, hL, _, _, _, hacW, _⟩ := hinvT
  refine ⟨4194560#64, fin.flags, fin.xmm, fin.ymmHi, s.mem, fin.zmmHi, fin.kreg, ?_, MemFrame.refl _ _,
    LiveFrame.refl _ _ _, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx, x8, fw, zh, kr⟩ := fin
    simp only at hrip hregs hx hfs hdf hmx hx87 hfw hmem ⊢
    subst hrip hfs hdf hmx hx87 hfw hmem
    simp only [wbRetX64, State.mk.injEq, and_true, true_and]
    constructor
    · funext i; exact hregs i
    · funext i
      split
      · rename_i hi; subst hi; exact hx
      · rfl
  · rw [hb]
    refine ⟨inRanges_wbuf hn, by simp [WBUF]; omega, ?_, by decide⟩
    rw [← view_accessible (toyRt tys) L s.mem]
    exact Janus.Arm64.Memory.accessible_mono _ hacW (Nat.le_refl _) (by omega)
  · rw [hb]
    intro r hr
    have := hL r hr
    show WBUF + 8 * n ≤ r.1 ∨ r.1 + (r.2 - r.1) ≤ WBUF
    simp only [WBUF, HEAP] at *; omega
  · rw [hb]
    have := apart_win (inRanges_wbuf hn) hWs
    simpa only [apartAll_cons, apartAll_nil, and_true] using this
  · rw [hb]
    intro v' hf
    exact toyInv.frame hty hn hinvT hf

set_option maxRecDepth 20000 in
theorem wb_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop) (n : Nat) (hn : n ≤ 8) :
    WbLiveContract64 (toy.link (at0 wbCode)) A0 4096 (toyR tys ok) n := by
  rw [link_at0]
  intro L b s hpc pre
  have ⟨hra, hal, h3, h4, h5⟩ := pre.1
  janus64_run
  exact wb_post64 hty hn pre.2.2.1 pre.2.2.2.2 (by simp [retAddrOf])
    (by intro i; simp only [setRegF]; by_cases h4 : i = 4 <;> by_cases h11 : i = 11 <;> simp [h4, h11]) (by simp) rfl rfl (by simp) rfl rfl rfl


/-! ### The `RtSpec` contracts: `slicebytetostringtmp` (allocates nothing) -/

def okRt : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [0, 0]

/-- A call that returns with nothing changed meets `RtLivePost64` when the spec's postcondition holds
of the unchanged memory and the call costs and adds nothing. -/
theorem rt_post_nochange64 {R : RtInv} {stack : Nat} {sp : RtSpec} {ls : LiveSpec} {L : List (Nat × Nat)} {b : Nat}
    {s fin : State}
    (hc : ls.cost (argWords64 s sp.nargs) s.mem = 0)
    (hf : ls.fresh (argWords64 s sp.nargs) s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat = [])
    (hk : ls.keep (argWords64 s sp.nargs) s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat = [])
    (hq : sp.post R.rt (argWords64 s sp.nargs) s.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat s.mem)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem))
    (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64) (h5 : fin.regs 5 = s.regs 5)
    (h14 : fin.regs 14 = s.regs 14) (h0 : fin.regs 0 = s.regs 0) (h3 : fin.regs 3 = s.regs 3)
    (h1 : fin.regs 1 = s.regs 1) (hx : fin.xmm 15 = s.xmm 15) (hfs : fin.fsBase = s.fsBase)
    (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr) (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (hmem : fin.mem = s.mem) :
    RtLivePost64 stack R sp ls L b s fin := by
  have hfin := AllocSatAmd64.ret_of s fin [s.regs 0, s.regs 3, s.regs 1] hrip h4 h5 h14
    (by simp [h0]) (by simp [h3]) (by simp [h1]) hx hfs hdf hmx hx87 hfw
  rw [hmem] at hfin
  refine ⟨s.regs 0, s.regs 3, s.regs 1, fin.regs, fin.flags, fin.xmm, fin.ymmHi, s.mem, fin.zmmHi, fin.kreg,
    hfin, MemFrame.refl _ _, hq, LiveFrame.refl _ _ _, ?_, ?_, ?_⟩
  · simp [hf, FreshFrom]
  · simp [liveAdds, hf, hk, LiveApart]
  · simp only [liveAdds, hf, hk, hc, List.append_nil, Nat.sub_zero]; exact hinv

set_option maxRecDepth 20000 in
theorem rt_impl (tys : Tys) (hty : TysOK tys) :
    RtLiveContract64 (toy.link (at0 [0xc3])) A0 4096 (toyR tys okRt) slicebytetostringtmpSpec
      slicebytetostringtmpLive := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨hra, hal, h3, h4, h5⟩, _, _, _, _, hok, hinv, _⟩ := pre
  janus64_run
  have ha : argWords64 s 2 = [0, 0] := (hok.2 : argWords64 s 2 = [0, 0])
  have ha' := ha
  simp [argWords64, wordsFrom] at ha'
  refine rt_post_nochange64 rfl rfl rfl ?_ hinv (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) rfl rfl (by simp) rfl rfl rfl
  have e0 : (s.regs 0).toNat = 0 := ha'.1
  have e1 : (s.regs 3).toNat = 0 := ha'.2
  simp only [slicebytetostringtmpSpec, ha, e0, e1]
  simp [Janus.Spec.strBytes]


/-! ### Copies and clears -/

/-- A call that stores one word at `dst` (a live object or caller memory outside `R.rt`) and
otherwise only changes registers meets `LiveMemRet64`. -/
theorem liveMemRet_store64 {R : RtInv} {d nargs b dst v : Nat} {L : List (Nat × Nat)} {s fin : State}
    {P : Memory → Prop} (hrip : fin.rip = retAddrOf s) (h4 : fin.regs 4 = s.regs 4 + 8#64)
    (h5 : fin.regs 5 = s.regs 5) (h14 : fin.regs 14 = s.regs 14) (hx : fin.xmm 15 = s.xmm 15)
    (hfs : fin.fsBase = s.fsBase) (hdf : fin.df = s.df) (hmx : fin.mxcsr = s.mxcsr)
    (hx87 : fin.x87 = s.x87) (hfw : fin.fpucw = s.fpucw)
    (hmem : fin.mem = s.mem.writeLE dst 8 v) (hdst : InRanges dst 8 L ∨ Outside dst 8 R.rt)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) (hP : P (s.mem.writeLE dst 8 v)) :
    LiveMemRet64 R d nargs [(dst, dst + 8)] L b s fin P := by
  obtain ⟨junk, f, x, yh, m, zh, kr, hs⟩ := retState64_intro (res := []) hrip h4 h5 h14 hx hfs hdf hmx
    (by simp) (by simp) (by simp) hx87 hfw
  have hm : m = s.mem.writeLE dst 8 v := by
    have := congrArg State.mem hs
    simp only [retState64] at this
    rw [← hmem]; exact this.symm ▸ rfl
  refine ⟨junk, f, x, yh, m, zh, kr, hs, ?_, ⟨fun a n hin hout => ?_⟩, ?_, ?_⟩
  · rw [hm]
    refine MemFrame.of_writeLE s.mem v (r := (dst, dst + 8)) ?_ (Nat.le_refl _) (Nat.le_refl _)
    simp
  · rw [hm]
    have := MemFrame.outside_mem hout (r := (dst, dst + 8)) (by simp)
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  · rw [hm]
    rcases hdst with h | h
    · rw [view_writeLE_live h]; exact hinv
    · rw [view_writeLE_out h]; exact hinv
  · rw [hm]; exact hP

def memmoveCode : List Nat := [0x48, 0x8b, 0x13, 0x48, 0x89, 0x10, 0xc3]
def memclrCode : List Nat := [0x48, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc3]
def typedmemmoveCode : List Nat := [0x48, 0x8b, 0x11, 0x48, 0x89, 0x13, 0xc3]
def typedmemclrCode : List Nat := [0x48, 0xc7, 0x03, 0x00, 0x00, 0x00, 0x00, 0xc3]

set_option maxRecDepth 20000 in
theorem memmove8_impl (tys : Tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ d sr, args = [d, sr, 8]) :
    MemmoveLive64 (toy.link (at0 memmoveCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨hra, hal, h3, h4, h5⟩, _⟩, hLm, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4, hd5⟩⟩ := pre
  obtain ⟨d0, s0, hargs⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have h8 : (s.regs 1).toNat = 8 := hargs.2.2
  rw [h8] at hs2 hd2
  rw [h8] at hd4 hd5
  have hap : Apart (s.regs 0).toNat 8 (s.regs 4).toNat 8 := by
    have h := hd5; simp only [outside_cons, outside_nil, and_true] at h; exact h
  janus64_run
  rw [h8]
  refine liveMemRet_store64 (v := s.mem.readLE (s.regs 3).toNat 8) (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp) hd4 hLm.2.1 ?_
  intro i hi
  exact IfaceModel.bytes_writeLE_readLE _ _ _ _ _ hi


set_option maxRecDepth 20000 in
theorem memclr8_impl (tys : Tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ d, args = [d, 8]) :
    MemclrNoHeapPointersLive64 (toy.link (at0 memclrCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨hra, hal, h3, h4, h5⟩, _⟩, hLm, ⟨hd1, hd2, hd3, hd4, hd5⟩⟩ := pre
  obtain ⟨d0, hargs⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have h8 : (s.regs 3).toNat = 8 := hargs.2
  rw [h8] at hd2 hd4 hd5
  have hap : Apart (s.regs 0).toNat 8 (s.regs 4).toNat 8 := by
    have h := hd5; simp only [outside_cons, outside_nil, and_true] at h; exact h
  janus64_run
  rw [h8]
  exact liveMemRet_store64 (v := 0) (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp) hd4 hLm.2.1 (zeroed_store _ _)

set_option maxRecDepth 20000 in
theorem memclrHasPointers8_impl (tys : Tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ d, args = [d, 8]) :
    MemclrHasPointersLive64 (toy.link (at0 memclrCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨hra, hal, h3, h4, h5⟩, _⟩, hLm, _, _, ⟨hd1, hd2, hd3, hd4, hd5⟩⟩ := pre
  obtain ⟨d0, hargs⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have h8 : (s.regs 3).toNat = 8 := hargs.2
  rw [h8] at hd2 hd4 hd5
  have hap : Apart (s.regs 0).toNat 8 (s.regs 4).toNat 8 := by
    have h := hd5; simp only [outside_cons, outside_nil, and_true] at h; exact h
  janus64_run
  rw [h8]
  exact liveMemRet_store64 (v := 0) (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp) hd4 hLm.2.1 (zeroed_store _ _)

set_option maxRecDepth 20000 in
theorem typedmemmove8_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ t ∈ tys, ∃ d sr, args = [t.1, d, sr] ∧ t.2.1 = 8) :
    TypedMemmoveLive64 (toy.link (at0 typedmemmoveCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨hra, hal, h3, h4, h5⟩, _⟩, hLm, hty0, hty1, ⟨hs1, hs2, hs3⟩, ⟨hd1, hd2, hd3, hd4, hd5⟩⟩ := pre
  obtain ⟨t, ht, d0, s0, hargs, ht8⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) := hLm.2.1
  have h8t : typSize s.mem (s.regs 0).toNat = 8 := by rw [hargs.1]; exact typ8_size hty hinvT ht ht8
  have h8 : s.mem.readLE (s.regs 0).toNat 8 = 8 := h8t
  rw [h8t] at hs2 hd2 hd4 hd5
  have hap : Apart (s.regs 3).toNat 8 (s.regs 4).toNat 8 := by
    have h := hd5; simp only [outside_cons, outside_nil, and_true] at h; exact h
  janus64_run
  try rw [h8]
  refine liveMemRet_store64 (v := s.mem.readLE (s.regs 1).toNat 8) (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp) hd4 hLm.2.1 ?_
  intro i hi
  exact IfaceModel.bytes_writeLE_readLE _ _ _ _ _ hi

set_option maxRecDepth 20000 in
theorem typedmemclr8_impl (tys : Tys) (hty : TysOK tys) (ok : Nat → List Nat → Prop)
    (hok' : ∀ args, ok A0 args → ∃ t ∈ tys, ∃ d, args = [t.1, d] ∧ t.2.1 = 8) :
    TypedMemclrLive64 (toy.link (at0 typedmemclrCode)) A0 4096 (toyR tys ok) := by
  rw [link_at0]
  intro L b s hpc pre
  obtain ⟨⟨_, ⟨hra, hal, h3, h4, h5⟩, _⟩, hLm, hty0, hty1, ⟨hd1, hd2, hd3, hd4, hd5⟩⟩ := pre
  obtain ⟨t, ht, d0, hargs, ht8⟩ := hok' _ hLm.1
  simp only [List.cons.injEq, and_true] at hargs
  have hinvT : toyInv tys b L (s.regs 14).toNat (view (toyRt tys) L s.mem) := hLm.2.1
  have h8t : typSize s.mem (s.regs 0).toNat = 8 := by rw [hargs.1]; exact typ8_size hty hinvT ht ht8
  have h8 : s.mem.readLE (s.regs 0).toNat 8 = 8 := h8t
  rw [h8t] at hd2 hd4 hd5
  have hap : Apart (s.regs 3).toNat 8 (s.regs 4).toNat 8 := by
    have h := hd5; simp only [outside_cons, outside_nil, and_true] at h; exact h
  janus64_run
  try rw [h8]
  exact liveMemRet_store64 (v := 0) (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp) (by simp) (by simp) (by simp) rfl rfl (by simp) hd4 hLm.2.1 (zeroed_store _ _)


/-! ## The witness world (amd64) -/

/-- The witness call state with argument words `l` in `RAX, RBX, RCX, RDI, RSI`. -/
def wst (l : List Nat) : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg
      else if i = 0 then BitVec.ofNat 64 (l.getD 0 0) else if i = 3 then BitVec.ofNat 64 (l.getD 1 0)
      else if i = 1 then BitVec.ofNat 64 (l.getD 2 0) else if i = 7 then BitVec.ofNat 64 (l.getD 3 0)
      else if i = 6 then BitVec.ofNat 64 (l.getD 4 0) else 0,
    rip := BitVec.ofNat 64 A0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := wmem }

theorem w4 (l : List Nat) : (wst l).regs 4 = BitVec.ofNat 64 wsp := by simp [wst]
theorem w14 (l : List Nat) : (wst l).regs 14 = BitVec.ofNat 64 wg := by simp [wst]
theorem wmem_eq (l : List Nat) : (wst l).mem = wmem := rfl
theorem wx15 (l : List Nat) : (wst l).xmm 15 = 0 := rfl
theorem wdf (l : List Nat) : (wst l).df = false := rfl

theorem wcallOK64 (l : List Nat) (n : Nat) (hn : n ≤ 5) : CallOK64 (wst l) 4096 n := by
  have hw : wmem.accessible (wsp - 4096) (4096 + 8 + 8 * 5) true = true := by decide
  simp only [CallOK64, w4, wmem_eq, wspn]
  refine ⟨by decide, by decide, by decide, by simp [wsp]; omega, ?_⟩
  exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem wguard64 (l : List Nat) (n : Nat) (hn : n ≤ 5) : StackRoom64 (wst l) 4096 n := by
  simp only [StackRoom64, GuardOK64, w14, w4, wmem_eq, wspn, wgn, calleeStack64]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true, wsp, wg]
  omega

theorem wwin64 (l : List Nat) (n : Nat) (hn : n ≤ 5) :
    LiveSep (liveWin64 (wst l) 4096 n) (toyRt tys0) := by
  intro x hx
  simp only [liveWin64, calleeStack64, w4, wspn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (rfl | rfl) | rfl <;>
    simp only [toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, wsp, HEAP, HEND, BUMP, WBUF,
      tyA, tyB, tyC] <;> omega

theorem wwb64 (l : List Nat) :
    LiveSep [(((wst l).regs 4).toNat - 4096, ((wst l).regs 4).toNat + 8)] (toyRt tys0) := by
  intro x hx
  simp only [w4, wspn, List.mem_singleton] at hx
  rw [hx]
  simp only [toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, wsp, HEAP, HEND, BUMP, WBUF,
    tyA, tyB, tyC]
  omega

theorem wguardE64 (l : List Nat) (n : Nat) (hn : n ≤ 5) : MemPre64 4096 n (wst l) := by
  have hw : wmem.accessible (wsp - 4096) (4096 + 8 + 8 * 5) true = true := by decide
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, w14, wgn]; decide
  · simp only [regG, stackguard0Offset, w14, wgn, wmem_eq]; decide
  · simp only [stackguard0, regG, regSP, stackguard0Offset, w14, w4, wgn, wspn, wmem_eq]; decide
  · simp only [w4, wspn]; decide
  · simp only [w4, wspn]; decide
  · simp only [w4, wspn]; simp [wsp]; omega
  · simp only [w4, wspn, wmem_eq]
    exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)
  · rfl
  · rfl
  · simp only [w4, wspn, wmem_eq]; decide
  · simp only [w14, w4, wgn, wspn, MemAmd64.calleeStack, MapAmd64.calleeStack, outside_cons, outside_nil, and_true]
    simp only [wsp, wg]
    omega


theorem wr0 (l : List Nat) (h : l.getD 0 0 < 2 ^ 64) : ((wst l).regs 0).toNat = l.getD 0 0 := by
  show (BitVec.ofNat 64 (l.getD 0 0)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem wr3 (l : List Nat) (h : l.getD 1 0 < 2 ^ 64) : ((wst l).regs 3).toNat = l.getD 1 0 := by
  show (BitVec.ofNat 64 (l.getD 1 0)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
theorem wr1 (l : List Nat) (h : l.getD 2 0 < 2 ^ 64) : ((wst l).regs 1).toNat = l.getD 2 0 := by
  show (BitVec.ofNat 64 (l.getD 2 0)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

def okNew : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyA]

theorem newobjectLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    NewobjectLiveContract64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      NewobjectPre64 4096 s ∧ StackRoom64 s 4096 1 ∧
      LiveAt R A0 [(s.regs 0).toNat] L b (newobjectRound64 s) (s.regs 14).toNat s.mem (liveWin64 s 4096 1) ∧
      0 < typSize s.mem (s.regs 0).toNat := by
  have h0 : ((wst [tyA]).regs 0).toNat = tyA := wr0 _ (by decide)
  refine ⟨at0 newobjectCodeD, toyR tys0 okNew, newobjectD_impl tys0 tysOK0 okNew, [], 0x400, wst [tyA], rfl,
    ⟨wcallOK64 _ 1 (by omega), by rw [h0, wmem_eq]; exact wTypeOK, by rw [h0, wmem_eq]; decide⟩,
    wguard64 _ 1 (by omega), ⟨by rw [h0]; exact ⟨rfl, rfl⟩, wmem_inv 0, by simp only [newobjectRound64, h0, wmem_eq]; decide,
      by simp, wwin64 _ 1 (by omega)⟩, by rw [h0, wmem_eq]; decide⟩

def okMake : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyB, 2, 2]

theorem makesliceLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    MakesliceLiveContract64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      MakeslicePre64 4096 s ∧ StackRoom64 s 4096 3 ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (makesliceRound64 s)
        (s.regs 14).toNat s.mem (liveWin64 s 4096 3) ∧
      0 < typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat := by
  have h0 : ((wst [tyB, 2, 2]).regs 0).toNat = tyB := wr0 _ (by decide)
  have h3 : ((wst [tyB, 2, 2]).regs 3).toNat = 2 := wr3 _ (by decide)
  have h1 : ((wst [tyB, 2, 2]).regs 1).toNat = 2 := wr1 _ (by decide)
  refine ⟨at0 makesliceCodeD, toyR tys0 okMake, makesliceD_impl tys0 tysOK0 okMake, [], 0x400, wst [tyB, 2, 2], rfl,
    ⟨wcallOK64 _ 3 (by omega), by rw [h0, wmem_eq]; exact ⟨by decide, by decide⟩, by rw [h3, h1]; decide,
      by rw [h1]; decide, by rw [h0, h1, wmem_eq]; decide⟩,
    wguard64 _ 3 (by omega), ⟨by rw [h0, h3, h1]; exact ⟨rfl, rfl⟩, wmem_inv 0,
      by simp only [makesliceRound64, h0, h1, wmem_eq]; decide, by simp, wwin64 _ 3 (by omega)⟩,
    by rw [h0, h1, wmem_eq]; decide⟩

def okMalloc : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [16, tyB, 1]
def okScan : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [16, tyC, 1]
def okTiny : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [8, tyB, 1]

theorem mallocgcLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    MallocgcLiveContract64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      MallocgcPre64 4096 s ∧ StackRoom64 s 4096 3 ∧
      LiveAt R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s)
        (s.regs 14).toNat s.mem (liveWin64 s 4096 3) ∧
      0 < (s.regs 0).toNat := by
  have h0 : ((wst [16, tyB, 1]).regs 0).toNat = 16 := wr0 _ (by decide)
  have h3 : ((wst [16, tyB, 1]).regs 3).toNat = tyB := wr3 _ (by decide)
  have h1 : ((wst [16, tyB, 1]).regs 1).toNat = 1 := wr1 _ (by decide)
  refine ⟨at0 mallocgcCodeD, toyR tys0 okMalloc, mallocgcD_impl tys0 tysOK0 okMalloc, [], 0x400, wst [16, tyB, 1], rfl,
    ⟨wcallOK64 _ 3 (by omega), by rw [h0]; decide, Or.inr ⟨by rw [h3, wmem_eq]; exact ⟨by decide, by decide⟩,
      fun h => by rw [h1]; revert h; rw [h3, wmem_eq]; decide⟩⟩,
    wguard64 _ 3 (by omega), ⟨by rw [h0, h3, h1]; exact ⟨rfl, rfl⟩, wmem_inv 0,
      by simp only [mallocgcRound64, h0, h3, wmem_eq]; decide, by simp, wwin64 _ 3 (by omega)⟩, by rw [h0]; decide⟩


def okGrow : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [HEAP, 2, 0, 2, tyB]

theorem growsliceLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    GrowsliceLiveContract64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      GrowslicePre64 4096 s ∧ StackRoom64 s 4096 5 ∧
      LiveAt R A0 (growsliceArgs64 s) L b (growsliceRound64 s) (s.regs 14).toNat s.mem (liveWin64 s 4096 5) := by
  have h0 : ((wst [HEAP, 2, 0, 2, tyB]).regs 0).toNat = HEAP := wr0 _ (by decide)
  have h3 : ((wst [HEAP, 2, 0, 2, tyB]).regs 3).toNat = 2 := wr3 _ (by decide)
  have h1 : ((wst [HEAP, 2, 0, 2, tyB]).regs 1).toNat = 0 := wr1 _ (by decide)
  have h7 : ((wst [HEAP, 2, 0, 2, tyB]).regs 7).toNat = 2 := by
    show (BitVec.ofNat 64 2).toNat = 2; decide
  have h6 : ((wst [HEAP, 2, 0, 2, tyB]).regs 6).toNat = tyB := by
    show (BitVec.ofNat 64 tyB).toNat = tyB; decide
  refine ⟨at0 growCode16, toyR tys0 okGrow, growslice16_impl tys0 tysOK0 okGrow ?_, [], 0x400,
    wst [HEAP, 2, 0, 2, tyB], rfl,
    ⟨⟨wcallOK64 _ 5 (by omega), by rw [h6, wmem_eq]; exact ⟨by decide, by decide⟩, by rw [h6, wmem_eq]; decide,
      by rw [h6, wmem_eq]; decide, by rw [h7, h3]; decide, by rw [h3, h7, h1]; decide, by rw [h1, h3]; decide,
      by rw [h3]; decide⟩, fun h => absurd h (by rw [h3, h7]; decide)⟩,
    wguard64 _ 5 (by omega), ⟨by simp only [growsliceArgs64, h0, h3, h1, h7, h6]; exact ⟨rfl, rfl⟩, wmem_inv 0,
      by simp only [growsliceRound64, h3, h1]; decide, by simp, wwin64 _ 5 (by omega)⟩⟩
  rintro args ⟨-, rfl⟩
  exact ⟨HEAP, tyB, rfl⟩

theorem mallocgcSmallNoScanSCLive64_satisfiable : ∃ (n : Nat) (impl : List Janus.Amd64.Segment) (R : RtInv),
    MallocgcSmallNoScanSCLiveContract64 n (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (MallocgcPre64 4096 s ∧ StackRoom64 s 4096 3 ∧
        LiveAt R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s)
          (s.regs 14).toNat s.mem (liveWin64 s 4096 3)) ∧
      NoScanArgs n s.mem (s.regs 0).toNat (s.regs 3).toNat := by
  have h0 : ((wst [16, tyB, 1]).regs 0).toNat = 16 := wr0 _ (by decide)
  have h3 : ((wst [16, tyB, 1]).regs 3).toNat = tyB := wr3 _ (by decide)
  have h1 : ((wst [16, tyB, 1]).regs 1).toNat = 1 := wr1 _ (by decide)
  refine ⟨2, at0 mallocgcCodeD, toyR tys0 okMalloc, (mallocgcD_impl tys0 tysOK0 okMalloc).smallNoScanSC, [], 0x400,
    wst [16, tyB, 1], rfl, ⟨⟨wcallOK64 _ 3 (by omega), by rw [h0]; decide, Or.inr ⟨by rw [h3, wmem_eq]; exact ⟨by decide, by decide⟩,
      fun h => by rw [h1]; revert h; rw [h3, wmem_eq]; decide⟩⟩,
    wguard64 _ 3 (by omega), ⟨by rw [h0, h3, h1]; exact ⟨rfl, rfl⟩, wmem_inv 0,
      by simp only [mallocgcRound64, h0, h3, wmem_eq]; decide, by simp, wwin64 _ 3 (by omega)⟩⟩, ?_⟩
  unfold NoScanArgs; rw [h0, h3, wmem_eq]; exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem mallocgcSmallScanNoHeaderSCLive64_satisfiable : ∃ (n : Nat) (impl : List Janus.Amd64.Segment) (R : RtInv),
    MallocgcSmallScanNoHeaderSCLiveContract64 n (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (MallocgcPre64 4096 s ∧ StackRoom64 s 4096 3 ∧
        LiveAt R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s)
          (s.regs 14).toNat s.mem (liveWin64 s 4096 3)) ∧
      ScanArgs n s.mem (s.regs 0).toNat (s.regs 3).toNat := by
  have h0 : ((wst [16, tyC, 1]).regs 0).toNat = 16 := wr0 _ (by decide)
  have h3 : ((wst [16, tyC, 1]).regs 3).toNat = tyC := wr3 _ (by decide)
  have h1 : ((wst [16, tyC, 1]).regs 1).toNat = 1 := wr1 _ (by decide)
  refine ⟨2, at0 mallocgcCodeD, toyR tys0 okScan, (mallocgcD_impl tys0 tysOK0 okScan).smallScanNoHeaderSC, [], 0x400,
    wst [16, tyC, 1], rfl, ⟨⟨wcallOK64 _ 3 (by omega), by rw [h0]; decide, Or.inr ⟨by rw [h3, wmem_eq]; exact ⟨by decide, by decide⟩,
      fun h => by rw [h1]; revert h; rw [h3, wmem_eq]; decide⟩⟩,
    wguard64 _ 3 (by omega), ⟨by rw [h0, h3, h1]; exact ⟨rfl, rfl⟩, wmem_inv 0,
      by simp only [mallocgcRound64, h0, h3, wmem_eq]; decide, by simp, wwin64 _ 3 (by omega)⟩⟩, ?_⟩
  unfold ScanArgs; rw [h0, h3, wmem_eq]; exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem mallocgcTinySizeLive64_satisfiable : ∃ (n : Nat) (impl : List Janus.Amd64.Segment) (R : RtInv),
    MallocgcTinySizeLiveContract64 n (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      (MallocgcPre64 4096 s ∧ StackRoom64 s 4096 3 ∧
        LiveAt R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s)
          (s.regs 14).toNat s.mem (liveWin64 s 4096 3)) ∧
      TinyArgs n s.mem (s.regs 0).toNat (s.regs 3).toNat := by
  have h0 : ((wst [8, tyB, 1]).regs 0).toNat = 8 := wr0 _ (by decide)
  have h3 : ((wst [8, tyB, 1]).regs 3).toNat = tyB := wr3 _ (by decide)
  have h1 : ((wst [8, tyB, 1]).regs 1).toNat = 1 := wr1 _ (by decide)
  refine ⟨8, at0 mallocgcCodeD, toyR tys0 okTiny, (mallocgcD_impl tys0 tysOK0 okTiny).tinySize, [], 0x400,
    wst [8, tyB, 1], rfl, ⟨⟨wcallOK64 _ 3 (by omega), by rw [h0]; decide, Or.inr ⟨by rw [h3, wmem_eq]; exact ⟨by decide, by decide⟩,
      fun h => by rw [h1]; revert h; rw [h3, wmem_eq]; decide⟩⟩,
    wguard64 _ 3 (by omega), ⟨by rw [h0, h3, h1]; exact ⟨rfl, rfl⟩, wmem_inv 0,
      by simp only [mallocgcRound64, h0, h3, wmem_eq]; decide, by simp, wwin64 _ 3 (by omega)⟩⟩, ?_⟩
  unfold TinyArgs; rw [h0, h3, wmem_eq]; exact ⟨by decide, by decide, by decide, by decide, by decide⟩


def okWb (n : Nat) : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [n]

theorem wbLive64_satisfiable : ∃ (n : Nat) (impl : List Janus.Amd64.Segment) (R : RtInv),
    WbLiveContract64 (toy.link impl) A0 4096 R n ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧ CallOK64 s 4096 0 ∧
      R.ok A0 [n] ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
      LiveSep L [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] ∧
      LiveSep [((s.regs 4).toNat - 4096, (s.regs 4).toNat + 8)] R.rt :=
  ⟨2, at0 wbCode, toyR tys0 (okWb 2), wb_impl tys0 tysOK0 _ 2 (by omega), [], 0x400, wst [], rfl,
    wcallOK64 _ 0 (by omega), ⟨rfl, rfl⟩, wmem_inv 0, by simp, wwb64 _⟩

def okRtArgs : Nat → List Nat → Prop := okRt

theorem rtLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (sp : RtSpec) (ls : LiveSpec),
    RtLiveContract64 (toy.link impl) A0 4096 R sp ls ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      RtLivePre64 4096 R sp ls A0 L b s := by
  refine ⟨at0 [0xc3], toyR tys0 okRt, _, _, rt_impl tys0 tysOK0, [], 0x400, wst [0, 0], rfl,
    wcallOK64 _ 2 (by omega), ⟨by decide, by decide⟩, ?_, by trivial, wguard64 _ 2 (by omega),
    ⟨⟨rfl, by decide⟩, wmem_inv 0, by decide, by simp, wwin64 _ 2 (by omega)⟩⟩
  intro x hx
  have a0 : argReg 0 = 0 := rfl
  have a1 : argReg 1 = 3 := rfl
  simp [slicebytetostringtmpSpec, argWords64, wordsFrom, wst, a0, a1] at hx
  subst hx
  simp [calleeStack64, w4, wsp]


/-! ### Copies and clears: the witnesses -/

def okMove : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [CB, CB + 0x100, 8]
def okClr : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [CB, 8]
def okTMove : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyB, CB, CB + 0x100]
def okTClr : Nat → List Nat → Prop := fun a args => a = A0 ∧ args = [tyB, CB]

theorem cb_out_win64 (l : List Nat) (k : Nat) (hk : k ≤ 5) (a n : Nat) (h1 : CB ≤ a) :
    Outside a n (calleeStack64 (wst l) 4096 k) := by
  simp only [calleeStack64, w4, wspn, outside_cons, outside_nil, and_true]
  simp only [wsp, CB] at *
  omega

theorem cb_out_ret64 (l : List Nat) (a n : Nat) (h1 : CB ≤ a) :
    Outside a n [(((wst l).regs 4).toNat, ((wst l).regs 4).toNat + 8)] := by
  simp only [w4, wspn, outside_cons, outside_nil, and_true]
  simp only [wsp, CB] at *
  omega

theorem cb_out_inputwin (l : List Nat) (k : Nat) (hk : k ≤ 5) (a n : Nat) (h1 : CB ≤ a) :
    Outside a n (MemAmd64.calleeStack (wst l) 4096 k) := by
  simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, w4, wspn, outside_cons, outside_nil, and_true]
  simp only [wsp, CB] at *
  omega


theorem memmoveLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    MemmoveLive64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      MemPre64 4096 3 s ∧
      LiveMemAt64 R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s 4096 3) ∧
      MemAmd64.Input s 4096 3 (s.regs 3).toNat (s.regs 1).toNat ∧
      LiveDest64 R L s 4096 3 (s.regs 0).toNat (s.regs 1).toNat := by
  have h0 : ((wst [CB, CB + 0x100, 8]).regs 0).toNat = CB := wr0 _ (by decide)
  have h3 : ((wst [CB, CB + 0x100, 8]).regs 3).toNat = CB + 0x100 := wr3 _ (by decide)
  have h1 : ((wst [CB, CB + 0x100, 8]).regs 1).toNat = 8 := wr1 _ (by decide)
  refine ⟨at0 memmoveCode, toyR tys0 okMove, memmove8_impl tys0 okMove ?_, [], 0x400, wst [CB, CB + 0x100, 8], rfl,
    wguardE64 _ 3 (by omega), ⟨by rw [h0, h3, h1]; exact ⟨rfl, rfl⟩, wmem_inv 0, by simp, wwin64 _ 3 (by omega)⟩,
    ⟨by rw [h3, h1]; decide, by rw [h3, h1, wmem_eq]; decide, by rw [h3]; exact cb_out_inputwin _ 3 (by omega) _ _ (by decide)⟩,
    ⟨by rw [h0, h1]; decide, by rw [h0, h1, wmem_eq]; decide, by rw [h0]; exact cb_out_win64 _ 3 (by omega) _ _ (by decide),
      Or.inr (by rw [h0]; exact cb_out_rt _ _ (by decide)), by rw [h0]; exact cb_out_ret64 _ _ _ (by decide)⟩⟩
  rintro args ⟨-, rfl⟩
  exact ⟨CB, CB + 0x100, rfl⟩

theorem memclrNoHeapPointersLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    MemclrNoHeapPointersLive64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      MemPre64 4096 2 s ∧
      LiveMemAt64 R A0 [(s.regs 0).toNat, (s.regs 3).toNat] L b s (liveWin64 s 4096 2) ∧
      LiveDest64 R L s 4096 2 (s.regs 0).toNat (s.regs 3).toNat := by
  have h0 : ((wst [CB, 8]).regs 0).toNat = CB := wr0 _ (by decide)
  have h3 : ((wst [CB, 8]).regs 3).toNat = 8 := wr3 _ (by decide)
  refine ⟨at0 memclrCode, toyR tys0 okClr, memclr8_impl tys0 okClr ?_, [], 0x400, wst [CB, 8], rfl,
    wguardE64 _ 2 (by omega), ⟨by rw [h0, h3]; exact ⟨rfl, rfl⟩, wmem_inv 0, by simp, wwin64 _ 2 (by omega)⟩,
    ⟨by rw [h0, h3]; decide, by rw [h0, h3, wmem_eq]; decide, by rw [h0]; exact cb_out_win64 _ 2 (by omega) _ _ (by decide),
      Or.inr (by rw [h0]; exact cb_out_rt _ _ (by decide)), by rw [h0]; exact cb_out_ret64 _ _ _ (by decide)⟩⟩
  rintro args ⟨-, rfl⟩
  exact ⟨CB, rfl⟩

theorem memclrHasPointersLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    MemclrHasPointersLive64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      MemPre64 4096 2 s ∧
      LiveMemAt64 R A0 [(s.regs 0).toNat, (s.regs 3).toNat] L b s (liveWin64 s 4096 2) ∧
      (s.regs 0).toNat % 8 = 0 ∧ (s.regs 3).toNat % 8 = 0 ∧
      LiveDest64 R L s 4096 2 (s.regs 0).toNat (s.regs 3).toNat := by
  have h0 : ((wst [CB, 8]).regs 0).toNat = CB := wr0 _ (by decide)
  have h3 : ((wst [CB, 8]).regs 3).toNat = 8 := wr3 _ (by decide)
  refine ⟨at0 memclrCode, toyR tys0 okClr, memclrHasPointers8_impl tys0 okClr ?_, [], 0x400, wst [CB, 8], rfl,
    wguardE64 _ 2 (by omega), ⟨by rw [h0, h3]; exact ⟨rfl, rfl⟩, wmem_inv 0, by simp, wwin64 _ 2 (by omega)⟩,
    by rw [h0]; decide, by rw [h3],
    ⟨by rw [h0, h3]; decide, by rw [h0, h3, wmem_eq]; decide, by rw [h0]; exact cb_out_win64 _ 2 (by omega) _ _ (by decide),
      Or.inr (by rw [h0]; exact cb_out_rt _ _ (by decide)), by rw [h0]; exact cb_out_ret64 _ _ _ (by decide)⟩⟩
  rintro args ⟨-, rfl⟩
  exact ⟨CB, rfl⟩

theorem typedMemmoveLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    TypedMemmoveLive64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      MemPre64 4096 3 s ∧
      LiveMemAt64 R A0 [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s 4096 3) ∧
      TypeOK s.mem (s.regs 0).toNat ∧ Outside (s.regs 0).toNat 16 (calleeStack64 s 4096 3) ∧
      MemAmd64.Input s 4096 3 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat) ∧
      LiveDest64 R L s 4096 3 (s.regs 3).toNat (typSize s.mem (s.regs 0).toNat) := by
  have h0 : ((wst [tyB, CB, CB + 0x100]).regs 0).toNat = tyB := wr0 _ (by decide)
  have h3 : ((wst [tyB, CB, CB + 0x100]).regs 3).toNat = CB := wr3 _ (by decide)
  have h1 : ((wst [tyB, CB, CB + 0x100]).regs 1).toNat = CB + 0x100 := wr1 _ (by decide)
  have hsz : typSize (wst [tyB, CB, CB + 0x100]).mem ((wst [tyB, CB, CB + 0x100]).regs 0).toNat = 8 := by
    rw [h0, wmem_eq]; decide
  refine ⟨at0 typedmemmoveCode, toyR tys0 okTMove, typedmemmove8_impl tys0 tysOK0 okTMove ?_, [], 0x400,
    wst [tyB, CB, CB + 0x100], rfl, wguardE64 _ 3 (by omega),
    ⟨by rw [h0, h3, h1]; exact ⟨rfl, rfl⟩, wmem_inv 0, by simp, wwin64 _ 3 (by omega)⟩,
    by rw [h0, wmem_eq]; exact ⟨by decide, by decide⟩, ?_,
    ⟨by rw [h1, hsz]; decide, by rw [h1, hsz, wmem_eq]; decide, by rw [h1]; exact cb_out_inputwin _ 3 (by omega) _ _ (by decide)⟩,
    ⟨by rw [h3, hsz]; decide, by rw [h3, hsz, wmem_eq]; decide, by rw [h3]; exact cb_out_win64 _ 3 (by omega) _ _ (by decide),
      Or.inr (by rw [h3]; exact cb_out_rt _ _ (by decide)), by rw [h3]; exact cb_out_ret64 _ _ _ (by decide)⟩⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨(tyB, 8, 0), by simp [tys0], CB, CB + 0x100, rfl, rfl⟩
  · rw [h0]
    simp only [calleeStack64, w4, wspn, outside_cons, outside_nil, and_true, tyB, wsp]
    decide

theorem typedMemclrLive64_satisfiable : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv),
    TypedMemclrLive64 (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.rip = BitVec.ofNat 64 A0 ∧
      MemPre64 4096 2 s ∧
      LiveMemAt64 R A0 [(s.regs 0).toNat, (s.regs 3).toNat] L b s (liveWin64 s 4096 2) ∧
      TypeOK s.mem (s.regs 0).toNat ∧ Outside (s.regs 0).toNat 16 (calleeStack64 s 4096 2) ∧
      LiveDest64 R L s 4096 2 (s.regs 3).toNat (typSize s.mem (s.regs 0).toNat) := by
  have h0 : ((wst [tyB, CB]).regs 0).toNat = tyB := wr0 _ (by decide)
  have h3 : ((wst [tyB, CB]).regs 3).toNat = CB := wr3 _ (by decide)
  have hsz : typSize (wst [tyB, CB]).mem ((wst [tyB, CB]).regs 0).toNat = 8 := by
    rw [h0, wmem_eq]; decide
  refine ⟨at0 typedmemclrCode, toyR tys0 okTClr, typedmemclr8_impl tys0 tysOK0 okTClr ?_, [], 0x400,
    wst [tyB, CB], rfl, wguardE64 _ 2 (by omega),
    ⟨by rw [h0, h3]; exact ⟨rfl, rfl⟩, wmem_inv 0, by simp, wwin64 _ 2 (by omega)⟩,
    by rw [h0, wmem_eq]; exact ⟨by decide, by decide⟩, ?_,
    ⟨by rw [h3, hsz]; decide, by rw [h3, hsz, wmem_eq]; decide, by rw [h3]; exact cb_out_win64 _ 2 (by omega) _ _ (by decide),
      Or.inr (by rw [h3]; exact cb_out_rt _ _ (by decide)), by rw [h3]; exact cb_out_ret64 _ _ _ (by decide)⟩⟩
  · rintro args ⟨-, rfl⟩
    exact ⟨(tyB, 8, 0), by simp [tys0], CB, rfl, rfl⟩
  · rw [h0]
    simp only [calleeStack64, w4, wspn, outside_cons, outside_nil, and_true, tyB, wsp]
    decide

end Janus.Contracts.LiveSatAmd64
