import Extracted

/-!
# `InsertK24(m map[[24]byte]uint64, k *[24]byte, v uint64)` sets `m[*k] = v` (arm64)

**Guarantee.** For every model `M` of the map runtime, every readiness predicate `H` and every
generic `mapassign` satisfying `MapVar.AssignG` for 24-byte keys and 8-byte values, every
non-nil map `m` holding `f`, and every call state in which the map type's key type is 24 bytes
of regular memory (`KeyRegular`: the type's hash is the seeded byte hash, its equality compares
the bytes), the key `*k` is readable and outside the stack window, and the runtime is ready for
the call (`H`): the call returns and memory represents `f` with the key's 24 bytes
(`MapVar.keyAt`) mapped to `v`, the runtime environment intact. A nil map is not covered
(`mapassign` panics).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapStr Janus.Spec.Type

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x28) (segWord Extracted.program "example.com/basic.InsertK24" 10)
    (segWord Extracted.program "example.com/basic.InsertK24" 11) 0

/-- The stack window of `InsertK24` and the runtime call. -/
def window {K V : Type} (M : MapModel K V) (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - (M.depth + 48), s.sp.toNat + 32)]

/-- The precondition. -/
def pre (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8))) (H : RtReady) (m kp : BitVec 64)
    (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) (s : State) : Prop :=
  CallerOK M s 48 32 ∧ M.Typ mapType ∧ KeyRegular (rtView M.priv s.mem) mapType 24 ∧
    m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
    kp.toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat 24 false = true ∧
    Outside kp.toNat 24 (window M s) ∧
    H [mapType, m.toNat, kp.toNat, s.mem.readLE kp.toNat 24] (s.regs 28).toNat (s.sp.toNat - 48)
      (rtView M.priv s.mem)

theorem correctness (impl : List Segment) (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8)))
    (hl : M.Laws) (H : RtReady) (hasn : AssignG (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign") 24 8 M H)
    (m kp v : BitVec 64) (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp, v] (pre M H m kp f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set (keyAt s.mem kp.toNat 24) v) ∧
        M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hty, hreg, hm0, hmap, hkb, hka, hko, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH hreg
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  simp only [window, outside_cons, outside_nil, and_true] at hko
  janus_run until [Extracted.program.contractAddr "runtime.mapassign"]
  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
  have hfw : MemFrame s.mem (((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE
      (BitVec.toNat s.sp - 56) 8 (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 24) 8 v.toNat)
      [(s.sp.toNat - (M.depth + 48), s.sp.toNat + 32)] := by janus_frame
  have hk := hfw.readLE kp.toNat 24 (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp; omega) rfl (by simp [setReg]) (by simp [setReg]) (by decide)
      (by decide), by simpa [setReg] using hty, ?_, by simpa [setReg] using hm0, ?_, ⟨?_, ?_, ?_⟩, ?_⟩ ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    simpa using hreg
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simpa [setReg] using hkb
  · simpa [setReg, hfw.accessible] using hka
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, calleeStack, hsp, outside_cons,
      outside_nil, and_true]
    omega
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff, hk]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    rw [hsp]
    simpa using hH
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := InRanges.disjoint hin (Outside.of_sub hout (a := s.sp.toNat - (M.depth + 48))
      (n := M.depth + 48 + 32) (by omega) (by omega))
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, keyAt, hk] at hset
    simp only [keyAt]
    exact ⟨(hset v).1, (hset v).2.1⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model with 24-byte keys (`MCW ck24`: `MapModel0.MC`, one map of at most one entry at `MP`,
the key's 24 bytes at `MP + 8`, the value at `MP + 32`, with a private memory that also holds
the key-type word of the real `mapType` descriptor), a witness memory in which that word points
to a key type `KT24` of 24 bytes of regular memory, the readiness `MapModel0.HAssign` (the map
is empty), code meeting `AssignG` for them (`k24Code`: load the key, `used = 1`, store the key,
return the slot `MP + 32`), and a call state inserting the 24 bytes at `VAL` into the empty
non-nil map `MP`: `correctness` applies (`returns`). -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSat

/-- The key type of the witness: `Size_ = 24`, `TFlag = TFlagRegularMemory`. -/
def KT24 : Nat := 0x10d00

/-- The model's private memory: `priv0` and the key-type word of `mapType`. -/
def privW : List (Nat × Nat) := priv0 ++ [(mapType + 48, mapType + 56)]

/-- The value of the cell (`8` bytes at `MP + 32`) under its key `ck.get m`. -/
def cellW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) : AMap K (BitVec (8 * 8)) :=
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

theorem agreesW {m m' : Memory} (ha : Agrees m m' privW) : Agrees m m' priv0 :=
  ⟨ha.1, fun a h => ha.2 a (h.append_left _)⟩

theorem inPrivW {a n : Nat} (h1 : 0x10000 ≤ a) (h2 : a + n ≤ 0x11000) : InRanges a n privW :=
  (inPriv0 h1 h2).append_left _

theorem keys_cellW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) :
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
    refine ⟨Memory.accessible_mono _ (IfaceModel.acc_read_of_write h2) (Nat.le_refl _) (by decide),
      by decide, fun ks hk => ?_⟩
    rcases h4 with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
    · rw [hu, hk.eq_nil_of_empty]; rfl
    · rw [hu, hk.length_eq (keys_cellW ck m)]; rfl
  finite m mp f h := by
    obtain ⟨-, -, -, h4⟩ := h
    rcases h4 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨[], keys_empty⟩
    · exact ⟨_, keys_cellW ck m⟩

/-- An assignment's readiness in `MCW` (`MapModel0.HAssign` on `privW`): the map is empty. -/
theorem mcw_empty {K : Type} [DecidableEq K] {ck : CellKey K} {s : State} {f : AMap K (BitVec (8 * 8))}
    (hrep : (MCW ck).Rep s.mem (s.regs 1).toNat f) (args : List Nat)
    (hH : Ready HAssign (MCW ck).priv args s) :
    (s.regs 1).toNat = MP ∧ s.mem.accessible MP 56 true = true ∧ s.mem.readLE (MP + 48) 8 = 1 ∧
      f = AMap.empty := by
  obtain ⟨hmp, hacc, hal, hu⟩ := hrep
  have h0 : s.mem.readLE MP 8 = 0 := by
    have := hH; simp only [Ready, HAssign, MCW] at this
    rwa [readLE_rtView (inPrivW (a := MP) (n := 8) (by decide) (by decide))] at this
  refine ⟨hmp, hacc, hal, ?_⟩
  rcases hu with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · omega

/-- What an `MCW` assignment returns (as `MapModel0.cell_assign`). -/
theorem cell_assignW {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) (k : K) (g : W64)
    (hacc : m.accessible MP 56 true = true) (hal : m.readLE (MP + 48) 8 = 1) (hu : m.readLE MP 8 = 1)
    (hk : ∀ v, ck.get (m.writeLE (MP + 32) 8 v) = k) (hze : ZEnv m) :
    Map.AssignSlot 8 (MCW ck) MP AMap.empty k g (MP + 32) m := by
  refine ⟨Memory.accessible_mono _ hacc (by decide) (by decide), inPrivW (by decide) (by decide),
    fun v => ⟨?_, hze.writeLE _ (by decide), fun mp' _ hne h => absurd h.1 hne⟩⟩
  have hv : v.toNat % 256 ^ 8 = v.toNat :=
    Nat.mod_eq_of_lt (by have := v.isLt; rwa [Nat.pow_mul] at this)
  have e : (AMap.empty : AMap K (BitVec (8 * 8))).set k v = cellW ck (m.writeLE (MP + 32) 8 v.toNat) := by
    funext k'
    simp only [AMap.set, cellW, hk, Memory.readLE_writeLE_self, hv,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    split <;> rfl
  rw [e]
  exact ⟨rfl, by rw [Memory.accessible_writeLE]; exact hacc,
    by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal,
    Or.inr ⟨by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hu, rfl⟩⟩


/-- The cell's key: the 24 bytes at `MP + 8`. -/
def ck24 : CellKey (BitVec (8 * 24)) where
  get m := BitVec.ofNat (8 * 24) (m.readLE (MP + 8) 24)
  frame m m' ha := by rw [readLE_of_agrees ha (by decide) (by decide)]

/-- `movz x4, #0x800; movk x4, #1, lsl #16; ldr x5, [x2]; ldr x6, [x2, #8]; ldr x7, [x2, #16];
movz x8, #1; str x8, [x4]; str x5, [x4, #8]; str x6, [x4, #16]; str x7, [x4, #24];
add x0, x4, #32; ret`: load the key, `used = 1`, store the key, return the slot `MP + 32`. -/
def k24Code : List Nat :=
  [0xd2810004, 0xf2a00024, 0xf9400045, 0xf9400446, 0xf9400847, 0xd2800028, 0xf9000088,
   0xf9000485, 0xf9000886, 0xf9000c87, 0x91008080, 0xd65f03c0]

theorem assignG_implW : AssignG (toy.link (at0 k24Code)) A0 24 8 (MCW ck24) HAssign := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, -, hm0, hrep, ⟨hkb, hka, hko⟩, hH⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  obtain ⟨hmp, hacc, hal, rfl⟩ := mcw_empty hrep _ hH
  have hk0 : s.mem.accessible (s.regs 2).toNat 8 false = true :=
    Memory.accessible_mono _ hka (Nat.le_refl _) (by omega)
  have hk8 : s.mem.accessible ((s.regs 2).toNat + 8) 8 false = true :=
    Memory.accessible_mono _ hka (by omega) (by omega)
  have hk16 : s.mem.accessible ((s.regs 2).toNat + 16) 8 false = true :=
    Memory.accessible_mono _ hka (by omega) (by omega)
  simp only [MP] at hacc
  janus_run
  have hfr : MemFrame s.mem ((((s.mem.writeLE 67584 8 1).writeLE 67592 8
      (s.mem.readLE (BitVec.toNat (s.regs 2)) 8)).writeLE 67600 8
      (s.mem.readLE (BitVec.toNat (s.regs 2) + 8) 8)).writeLE 67608 8
      (s.mem.readLE (BitVec.toNat (s.regs 2) + 16) 8)) (rtWrites (MCW ck24) s 3 ++ []) := by
    simp only [rtWrites, calleeStack, MCW, privW, priv0, List.append_nil, List.cons_append,
      List.nil_append]
    janus_frame
  simp only [show (67584 : Nat) = MP from rfl, show (67592 : Nat) = MP + 8 from rfl,
    show (67600 : Nat) = MP + 16 from rfl, show (67608 : Nat) = MP + 24 from rfl,
    show (67616 : Nat) = MP + 32 from rfl] at hacc hfr ⊢
  have hsplit : ∀ (m : Memory) (a : Nat), m.readLE a 24 =
      m.readLE a 8 + 256 ^ 8 * (m.readLE (a + 8) 8 + 256 ^ 8 * m.readLE (a + 16) 8) := by
    intro m a
    rw [show (24 : Nat) = 8 + 16 from rfl, Memory.readLE_add, show (16 : Nat) = 8 + 8 from rfl,
      Memory.readLE_add, Nat.add_assoc]
  have hlt : ∀ (a : Nat), s.mem.readLE a 8 % 256 ^ 8 = s.mem.readLE a 8 :=
    fun a => Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)
  refine MapSat.mapReturn_of (MCW ck24) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl hfr
    ((((hze.writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide))
    (fun mp' _ hne h => absurd (h.1.trans hmp.symm) hne) ?_
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat, hmp]
  refine cell_assignW ck24 _ _ (s.regs 28)
    (by simp only [Memory.accessible_writeLE]; exact hacc)
    (by simp (disch := decide) only [Memory.readLE_writeLE_of_disjoint]; exact hal)
    (by simp (disch := decide) only [Memory.readLE_writeLE_of_disjoint]; rw [Memory.readLE_writeLE_self])
    (fun v => ?_)
    ((((hze.writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide)).writeLE _ (by decide))
  show BitVec.ofNat (8 * 24) (Memory.readLE _ (MP + 8) 24) = BitVec.ofNat (8 * 24) (s.mem.readLE _ 24)
  rw [hsplit, hsplit s.mem]
  simp (disch := decide) only [Memory.readLE_writeLE_of_disjoint, show MP + 8 + 8 = MP + 16 from rfl,
    show MP + 8 + 16 = MP + 24 from rfl, Memory.readLE_writeLE_self, hlt, Nat.add_assoc]

/-- `runtime.mapassign`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.mapassign"

/-- The branch at the contract's address and the model code. -/
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := k24Code }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : AssignG (Extracted.program.link implAt) cAddr 24 8 (MCW ck24) HAssign := by
  have hA : AssignG (Extracted.program.link implAt) A0 24 8 (MCW ck24) HAssign := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (assignG_implW f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The witness memory: `mmem`, the key type `KT24`, and the key-type word of `mapType`
(read-only, holding `KT24`). -/
def mmemK : Memory :=
  ⟨fun a => if a = mapType + 49 then 0x0d else if a = mapType + 50 then 0x01
      else if a = KT24 then 24 else if a = KT24 + 20 then 8 else mmem.bytes a,
    mmem.regions ++ [⟨mapType + 48, 8, false⟩]⟩

/-- The map `MP`, the key pointer `VAL` and the value. -/
def mv : BitVec 64 := BitVec.ofNat 64 MP
def kp : BitVec 64 := BitVec.ofNat 64 VAL
def v : BitVec 64 := 42#64

/-- The witness call state: `InsertK24(MP, VAL, 42)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 1 then kp else if i = 2 then v
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mmemK }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kp, v] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem pre0 : pre (MCW ck24) HAssign mv kp AMap.empty s0 := by
  janus_eval_nat hT : mapType
  have hR : ∀ a n, 0x10000 ≤ a → a + n ≤ 0x11000 → (rtView (MCW ck24).priv mmemK).readLE a n = mmemK.readLE a n :=
    fun a n h1 h2 => readLE_rtView ((inPriv0 h1 h2).append_left _)
  have hW : (rtView (MCW ck24).priv mmemK).readLE (mapType + 48) 8 = KT24 := by
    rw [readLE_rtView ⟨(mapType + 48, mapType + 56), by simp [MCW, privW], Nat.le_refl _, Nat.le_refl _⟩]
    simp only [mmemK, KT24, hT]; decide
  refine ⟨⟨?_, ⟨by decide, ?_, ?_⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩, trivial,
    ⟨?_, ?_⟩, by decide, ⟨rfl, ?_, ?_, Or.inl ⟨?_, rfl⟩⟩, by decide, ?_, ?_, ?_⟩
  all_goals first
    | (unfold KeyRegular keyType tySize isRegularMemory tyTFlag; rw [hW, hR _ _ (by decide) (by decide)]
       try rw [hR _ _ (by decide) (by decide)]
       simp only [mmemK, KT24, hT]; decide)
    | (simp only [s0, MCW, privW, priv0, window, Ready, HAssign, Disjoint, ZEnv, mmemK, hT, outside_cons, outside_nil,
        outside_append, and_true, regG, stackguard0Offset, Memory.accessible, Memory.readLE]; decide)

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8)))
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
