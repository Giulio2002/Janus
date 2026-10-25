import Janus
import Extracted

/-!
# `InsertK24(m map[[24]byte]uint64, k *[24]byte, v uint64)` sets `m[*k] = v` (amd64)

As on arm64, under the generic `MapVarAmd64.AssignG` for 24-byte keys of regular memory
(`KeyRegular`) and 8-byte values, with a readiness predicate `H` at entry (`RSP` of the call
`40` bytes below the entry's).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
  Janus.Contracts.MapVarAmd64 Janus.Spec.Type
open Janus.Contracts.MapVar (KeyRegular keyAt keyType SlotHoldsN)
open Janus.Contracts (RtReady rtView rtView_writeLE readLE_rtView Ready64)

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x1b)

/-- The return address the call at `Extracted.entry + 0x22` pushes. -/
def ret27 : Nat := Extracted.entry + 0x27

/-- The stack window of `InsertK24` and the runtime call (amd64). -/
def window {K V : Type} (M : MapModel K V) (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - (M.depth + 40), (s.regs 4).toNat + 32)]

/-- The precondition. -/
def pre (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8))) (H : RtReady) (m kp : BitVec 64)
    (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) (s : State) : Prop :=
  CallerOK M s 40 32 ∧ M.Typ mapType ∧ KeyRegular (rtView M.priv s.mem) mapType 24 ∧
    m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
    kp.toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat 24 false = true ∧
    Outside kp.toNat 24 (window M s) ∧
    H [mapType, m.toNat, kp.toNat, s.mem.readLE kp.toNat 24] (s.regs 14).toNat ((s.regs 4).toNat - 40)
      (rtView M.priv s.mem)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8)))
    (hl : M.Laws) (H : RtReady) (hasn : AssignG (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign") 24 8 M H)
    (m kp v : BitVec 64) (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp, v] (pre M H m kp f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set (keyAt s.mem kp.toNat 24) v) ∧
        M.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs ⟨hc, hty, hreg, hm0, hmap, hkb, hka, hko, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH hreg
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  simp only [window, outside_cons, outside_nil, and_true] at hko
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapassign"]
  have hfw : MemFrame s.mem (((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) + 24) 8 v.toNat).writeLE
      (BitVec.toNat (s.regs 4) - 40) 8 ret27)
      [((s.regs 4).toNat - (M.depth + 40), (s.regs 4).toNat + 32)] := by janus_frame
  janus_eval_nat hR : ret27
  simp only [hR] at hfw
  have hk := hfw.readLE kp.toNat 24 (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, ?_, by simpa [setRegF] using hm0, ?_,
      ⟨?_, ?_, ?_⟩, ?_⟩ ?_
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    simpa using hreg
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simpa [setRegF] using hkb
  · simpa [setRegF, hfw.accessible] using hka
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, calleeStack, hsp40, outside_cons,
      outside_nil, and_true]
    omega
  · simp only [Ready64, setRegF, reduceIte, Nat.reduceEqDiff, hsp40, hk]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    simpa using hH
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, keyAt, hk] at hset
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := Janus.InRanges.disjoint hin (Outside.of_sub hout (a := (s.regs 4).toNat - (M.depth + 40))
      (n := M.depth + 40 + 32) (by omega) (by omega))
    janus64_run
    simp only [keyAt]
    exact ⟨(hset v).1, (hset v).2.1⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: `MCW ck24` (`MapModel0.MC` with 24-byte keys, whose private memory also holds the
key-type word of the real `mapType`), a witness memory `mmemK` (`mmem64` with that word pointing
to a 24-byte regular-memory key type `KT24`), the readiness `MapModel0.HAssign`, the code
`k24Code` (load the key, `used = 1`, store the key, return the slot `MP + 32`) behind a `JMP` at
the contract's address, and a call inserting the 24 bytes at `VAL` into the empty map `MP`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64

/-- The key type of the witness: `Size_ = 24`, `TFlag = TFlagRegularMemory`. -/
def KT24 : Nat := 0x10d00

/-- The model's private memory: `priv0` and the key-type word of `mapType`. -/
def privW : List (Nat × Nat) := priv0 ++ [(mapType + 48, mapType + 56)]

/-- The value of the cell (`8` bytes at `MP + 32`) under its key `ck.get m`. -/
def cellW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Janus.Arm64.Memory) : AMap K (BitVec (8 * 8)) :=
  fun k => if k = ck.get m then some (BitVec.ofNat (8 * 8) (m.readLE (MP + 32) 8)) else none

/-- `MapModel0.MC` with `8`-byte values and the private memory `privW`. -/
def MCW {K : Type} [DecidableEq K] (ck : CellKey K) : MapModel K (BitVec (8 * 8)) where
  Rep m mp f := mp = MP ∧ m.accessible MP 56 true = true ∧ m.readLE (MP + 48) 8 = 1 ∧
    ((m.readLE MP 8 = 0 ∧ f = AMap.empty) ∨ (m.readLE MP 8 = 1 ∧ f = cellW ck m))
  Iter _ _ _ _ _ := False
  Typ _ := True
  Env m _ := ZEnv m
  priv := privW
  depth := 64

theorem agreesW {m m' : Janus.Arm64.Memory} (ha : Agrees m m' privW) : Agrees m m' priv0 :=
  ⟨ha.1, fun a h => ha.2 a (h.append_left _)⟩

theorem inPrivW {a n : Nat} (h1 : 0x10000 ≤ a) (h2 : a + n ≤ 0x11000) : InRanges a n privW :=
  (inPriv0 h1 h2).append_left _

theorem keys_cellW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Janus.Arm64.Memory) :
    Keys (cellW ck m) [ck.get m] :=
  ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun k => by
    simp only [List.mem_singleton, cellW]; split <;> simp_all⟩

theorem MCW_laws {K : Type} [DecidableEq K] (ck : CellKey K) : (MCW ck).Laws where
  rep_frame m m' mp f h ha := by
    have ha0 := agreesW ha
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hu : m'.readLE MP 8 = m.readLE MP 8 := readLE_of_agrees ha0 (by decide) (by decide)
    have hc : cellW ck m' = cellW ck m := by
      funext k
      simp only [cellW, ck.frame m m' ha0, readLE_of_agrees ha0 (a := MP + 32) (n := 8) (by decide) (by decide)]
    refine ⟨h1, by rw [ha.accessible]; exact h2,
      (readLE_of_agrees ha0 (by decide) (by decide)).trans h3, ?_⟩
    rw [hu, hc]; exact h4
  iter_frame _ _ _ _ _ _ h _ := h.elim
  env_frame m m' _ h ha := ZEnv.frame h (agreesW ha)
  len m mp f h := by
    obtain ⟨rfl, h2, -, h4⟩ := h
    refine ⟨Janus.Arm64.Memory.accessible_mono _ (Janus.Contracts.IfaceModel.acc_read_of_write h2) (Nat.le_refl _) (by decide),
      by decide, fun ks hk => ?_⟩
    rcases h4 with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
    · rw [hu, hk.eq_nil_of_empty]; rfl
    · rw [hu, hk.length_eq (keys_cellW ck m)]; rfl
  finite m mp f h := by
    obtain ⟨-, -, -, h4⟩ := h
    rcases h4 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨[], keys_empty⟩
    · exact ⟨_, keys_cellW ck m⟩

/-- An assignment's readiness in `MCW` (amd64): the map is empty. -/
theorem mcw_empty {K : Type} [DecidableEq K] {ck : CellKey K} {s : State} {f : AMap K (BitVec (8 * 8))}
    (hrep : (MCW ck).Rep s.mem (s.regs 3).toNat f) (args : List Nat)
    (hH : Ready64 HAssign (MCW ck).priv args s) :
    (s.regs 3).toNat = MP ∧ s.mem.accessible MP 56 true = true ∧ s.mem.readLE (MP + 48) 8 = 1 ∧
      f = AMap.empty := by
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have h0 : s.mem.readLE MP 8 = 0 := by
    have := hH; simp only [Ready64, HAssign, MCW] at this
    rwa [readLE_rtView (inPrivW (a := MP) (n := 8) (by decide) (by decide))] at this
  refine ⟨hmp, hacc, hal, ?_⟩
  rcases hu with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · omega

/-- What an `MCW` assignment returns (as `MapModel0.cell_assign`). -/
theorem cell_assignW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Janus.Arm64.Memory) (k : K) (g : W64)
    (hacc : m.accessible MP 56 true = true) (hal : m.readLE (MP + 48) 8 = 1) (hu : m.readLE MP 8 = 1)
    (hk : ∀ v, ck.get (m.writeLE (MP + 32) 8 v) = k) (hze : ZEnv m) :
    Janus.Contracts.MapAmd64.AssignSlot 8 (MCW ck) MP AMap.empty k g (MP + 32) m := by
  refine ⟨Janus.Arm64.Memory.accessible_mono _ hacc (by decide) (by decide), inPrivW (by decide) (by decide),
    fun v => ⟨?_, hze.writeLE _ (by decide), fun mp' _ hne h => absurd h.1 hne⟩⟩
  have hv : v.toNat % 256 ^ 8 = v.toNat :=
    Nat.mod_eq_of_lt (by have := v.isLt; rwa [Nat.pow_mul] at this)
  have e : (AMap.empty : AMap K (BitVec (8 * 8))).set k v = cellW ck (m.writeLE (MP + 32) 8 v.toNat) := by
    funext k'
    simp only [AMap.set, cellW, hk, Janus.Arm64.Memory.readLE_writeLE_self, hv,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    split <;> rfl
  rw [e]
  exact ⟨rfl, by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hacc,
    by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal,
    Or.inr ⟨by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hu, rfl⟩⟩


/-- The cell's key: the 24 bytes at `MP + 8`. -/
def ck24 : CellKey (BitVec (8 * 24)) where
  get m := BitVec.ofNat (8 * 24) (m.readLE (MP + 8) 24)
  frame m m' ha := by rw [readLE_of_agrees ha (by decide) (by decide)]

/-- `mov $0x10800, %edx; mov (%rcx), %rsi; mov 8(%rcx), %rdi; mov 16(%rcx), %r8;
movq $1, (%rdx); mov %rsi, 8(%rdx); mov %rdi, 16(%rdx); mov %r8, 24(%rdx); lea 32(%rdx), %rax;
ret`: load the key, `used = 1`, store the key, return the slot `MP + 32`. -/
def k24Code : List Nat :=
  [0xba, 0x00, 0x08, 0x01, 0x00, 0x48, 0x8b, 0x31, 0x48, 0x8b, 0x79, 0x08, 0x4c, 0x8b, 0x41, 0x10,
   0x48, 0xc7, 0x02, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0x72, 0x08, 0x48, 0x89, 0x7a, 0x10, 0x4c,
   0x89, 0x42, 0x18, 0x48, 0x8d, 0x42, 0x20, 0xc3]

theorem assignG_implW : AssignG (toy.link (at0 k24Code)) A0 24 8 (MCW ck24) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal4, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, -, hm0, hrep, ⟨hkb, hka, hko⟩, hH⟩ := hpre
  obtain ⟨hmp, hacc, hal, rfl⟩ := mcw_empty hrep _ hH
  have hk0 : s.mem.accessible (s.regs 1).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hka (Nat.le_refl _) (by omega)
  have hk8 : s.mem.accessible ((s.regs 1).toNat + 8) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hka (by omega) (by omega)
  have hk16 : s.mem.accessible ((s.regs 1).toNat + 16) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hka (by omega) (by omega)
  simp only [MP] at hacc
  have hout' := hout
  simp only [MCW, privW, priv0, outside_append, outside_cons, outside_nil, and_true] at hout'
  janus64_run
  have hfr : MemFrame s.mem ((((Janus.Arm64.Memory.writeLE s.mem 67584 8 1).writeLE 67592 8
      (s.mem.readLE (BitVec.toNat (s.regs 1)) 8)).writeLE 67600 8
      (s.mem.readLE (BitVec.toNat (s.regs 1) + 8) 8)).writeLE 67608 8
      (s.mem.readLE (BitVec.toNat (s.regs 1) + 16) 8)) (rtWrites (MCW ck24) s 3 ++ []) := by
    simp only [rtWrites, Janus.Contracts.MapAmd64.calleeStack, MCW, privW, priv0, List.append_nil,
      List.cons_append, List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67600 : Nat) = MP + 16 from rfl, show (67608 : Nat) = MP + 24 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hsplit : ∀ (m : Janus.Arm64.Memory) (a : Nat), m.readLE a 24 =
      m.readLE a 8 + 256 ^ 8 * (m.readLE (a + 8) 8 + 256 ^ 8 * m.readLE (a + 16) 8) := by
    intro m a
    rw [show (24 : Nat) = 8 + 16 from rfl, Janus.Arm64.Memory.readLE_add, show (16 : Nat) = 8 + 8 from rfl,
      Janus.Arm64.Memory.readLE_add, Nat.add_assoc]
  have hlt : ∀ (a : Nat), s.mem.readLE a 8 % 256 ^ 8 = s.mem.readLE a 8 :=
    fun a => Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ _)
  refine Janus.Contracts.MapStr.mapReturn64_of (MCW ck24) 3 [] _ s _ _ (by simp [retAddrOf])
    (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl hfr
    ((((hze.writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  refine cell_assignW ck24 _ _ (s.regs 14)
    (by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc)
    (by simp (disch := decide) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hal)
    (by simp (disch := decide) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint];
        rw [Janus.Arm64.Memory.readLE_writeLE_self])
    (fun v => ?_)
    ((((hze.writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide))
  show BitVec.ofNat (8 * 24) (Janus.Arm64.Memory.readLE _ (MP + 8) 24) =
    BitVec.ofNat (8 * 24) (s.mem.readLE _ 24)
  rw [hsplit, hsplit s.mem]
  simp (disch := decide) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    show MP + 8 + 8 = MP + 16 from rfl, show MP + 8 + 16 = MP + 24 from rfl,
    Janus.Arm64.Memory.readLE_writeLE_self, hlt, Nat.add_assoc]

def cAddr : Nat := Extracted.program.contractAddr "runtime.mapassign"

def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := k24Code }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : AssignG (Extracted.program.link implAt) cAddr 24 8 (MCW ck24) HAssign := by
  have hA : AssignG (Extracted.program.link implAt) A0 24 8 (MCW ck24) HAssign := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (assignG_implW f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The witness memory: `mmem64`, the key type `KT24`, and the key-type word of `mapType`
(read-only, holding `KT24`). -/
def mmemK : Janus.Arm64.Memory :=
  ⟨fun a => if a = mapType + 49 then 0x0d else if a = mapType + 50 then 0x01
      else if a = KT24 then 24 else if a = KT24 + 20 then 8 else mmem64.bytes a,
    mmem64.regions ++ [⟨mapType + 48, 8, false⟩]⟩

def mv : BitVec 64 := BitVec.ofNat 64 MP
def kp : BitVec 64 := BitVec.ofNat 64 VAL
def v : BitVec 64 := 42#64

/-- The witness call state: `InsertK24(MP, VAL, 42)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 3 then kp else if i = 1 then v
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmemK }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kp, v] s0 :=
  ⟨rfl, by janus_eval_nat hT : mapType; simp only [s0, mmemK, hT]; decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem pre0 : pre (MCW ck24) HAssign mv kp AMap.empty s0 := by
  janus_eval_nat hT : mapType
  have hR : ∀ a n, 0x10000 ≤ a → a + n ≤ 0x11000 → (rtView (MCW ck24).priv mmemK).readLE a n = mmemK.readLE a n :=
    fun a n h1 h2 => readLE_rtView ((inPriv0 h1 h2).append_left _)
  have hW : (rtView (MCW ck24).priv mmemK).readLE (mapType + 48) 8 = KT24 := by
    rw [readLE_rtView ⟨(mapType + 48, mapType + 56), by simp [MCW, privW], Nat.le_refl _, Nat.le_refl _⟩]
    simp only [mmemK, KT24, hT]; decide
  refine ⟨⟨?_, ⟨by decide, ?_, ?_⟩, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩, trivial,
    ⟨?_, ?_⟩, by decide, ⟨rfl, ?_, ?_, Or.inl ⟨?_, rfl⟩⟩, by decide, ?_, ?_, ?_⟩
  all_goals first
    | (unfold KeyRegular keyType tySize isRegularMemory tyTFlag; rw [hW, hR _ _ (by decide) (by decide)]
       try rw [hR _ _ (by decide) (by decide)]
       simp only [mmemK, KT24, hT]; decide)
    | (simp only [s0, MCW, privW, priv0, window, Ready64, HAssign, Janus.Spec.Disjoint, ZEnv, mmemK, hT,
        outside_cons, outside_nil, outside_append, and_true, regG, regSP, stackguard0Offset,
        Janus.Arm64.Memory.accessible, Janus.Arm64.Memory.readLE]; decide)

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8)))
    (H : RtReady) (ret : Nat) (s : State) (m kp v : BitVec 64)
    (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))),
    M.Laws ∧ AssignG (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign") 24 8 M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, kp, v] s ∧
    pre M H m kp f s :=
  ⟨implAt, MCW _, HAssign, ret, s0, mv, kp, v, AMap.empty, MCW_laws _, model, hret, setup, pre0⟩

/-- So the guarantee is reached: the map now holds the key's 24 bytes with `42`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (MCW ck24).Rep s'.mem MP (AMap.empty.set (keyAt mmemK VAL 24) 42#64) :=
  correctness implAt (MCW _) (MCW_laws _) HAssign model mv kp v AMap.empty ret hret s0 setup pre0
    |>.mono fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
