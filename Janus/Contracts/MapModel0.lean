import Janus.Contracts.MapVar
import Janus.Contracts.MapStr
import Janus.Contracts.EqHashModel

/-!
# Models of the map runtime, for the non-vacuity of its contracts

Every map contract (`Janus.Contracts.Map`, `MapVar`, `MapStr` and their amd64 files) is a
hypothesis of the theorems that use it, so each comes with a proof that it **is** satisfiable
(`Janus.Contracts.MapSat`, `MapVarSat`, `MapStrSat` and their `…SatAmd64` files): a model
satisfying `MapModel.Laws`, machine code proved to meet the contract for it, and a call state
satisfying the contract's whole precondition (`audit/round9/sat_check.py`, row SAT). This file
gives the models and the witness memory; the code and the proofs are per ISA.

The models are small worlds, not descriptions of the Go runtime. All their memory is the range
`priv0 = [0x10000, 0x11000)` (`IfaceModel`'s runtime range):

* `ME K`: the one non-nil map is the header at `MP`, always **empty** (`used = 0`); the zero
  value is the 8 zero bytes at `ZS`; an iterator has at most one key left (`Iter`, independent
  of memory). Every read-only entry point (lookups, `delete` of an absent key, `clear`,
  iteration) is met by code that returns `ZS` and `false`, or stores the end of the iteration.
* `MC ck`: the one map at `MP` holds **at most one entry**: `used` (`0` or `1`) at `MP`, the key
  at `MP + 8` (as `ck` reads it back), the 8-byte value at `MP + 32`, and an `alive` word at
  `MP + 48` that must be `1`. It meets the `mapassign*` contracts (store the key, set `used = 1`,
  return `MP + 32`) when the map is empty, and `makemap*` (set `alive`, `used = 0`, return `MP`)
  when no map is alive yet: that is the readiness predicate `H` of the witness (round 9 C1).

The witness memory `mmem` is `EqHashModel.wmem` plus: a map type descriptor `TY` whose key type
`KT` is 8 bytes of regular memory (`KeyRegular`), the map header (alive, empty), and an 8-byte
string key at `SK` in the runtime's memory.
-/

namespace Janus.Contracts.MapModel0

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Map Janus.Spec.Type Janus.Contracts
  Janus.Contracts.MapVar

/-! ## Addresses -/

/-- The runtime's memory of every model. -/
def priv0 : List (Nat × Nat) := [(0x10000, 0x11000)]
/-- The map header. -/
def MP : Nat := 0x10800
/-- The 8-byte zero value. -/
def ZS : Nat := 0x10900
/-- A map type descriptor (its key type pointer at `TY + 48`). -/
def TY : Nat := 0x10a00
/-- Its key type: `Size_ = 8`, `TFlag = TFlagRegularMemory`. -/
def KT : Nat := 0x10b00
/-- An 8-byte string key in the runtime's memory. -/
def SK : Nat := 0x10c00
/-- An iterator struct (user data). -/
def IT : Nat := 0x30900

theorem inPriv0 {a n : Nat} (h1 : 0x10000 ≤ a) (h2 : a + n ≤ 0x11000) : InRanges a n priv0 :=
  ⟨(0x10000, 0x11000), by simp [priv0], h1, h2⟩

theorem readLE_of_agrees {m m' : Memory} (h : Agrees m m' priv0) {a n : Nat} (h1 : 0x10000 ≤ a)
    (h2 : a + n ≤ 0x11000) : m'.readLE a n = m.readLE a n := h.readLE (inPriv0 h1 h2)

/-- The zero value is readable and zero. -/
def ZEnv (m : Memory) : Prop := m.accessible ZS 8 false = true ∧ m.readLE ZS 8 = 0

theorem ZEnv.frame {m m' : Memory} (h : ZEnv m) (ha : Agrees m m' priv0) : ZEnv m' :=
  ⟨by rw [ha.accessible]; exact h.1, (readLE_of_agrees ha (by decide) (by decide)).trans h.2⟩

/-! ## `ME`: one empty map -/

/-- The model with one, empty, non-nil map at `MP` (see the module documentation). -/
def ME (K : Type) : MapModel K (BitVec 64) where
  Rep m mp f := mp = MP ∧ f = AMap.empty ∧ m.accessible MP 8 false = true ∧ m.readLE MP 8 = 0
  Iter _ _ _ _ ks := ks.length ≤ 1
  Typ _ := True
  Env m _ := ZEnv m
  priv := priv0
  depth := 64

@[simp] theorem ME_priv (K : Type) : (ME K).priv = priv0 := rfl
@[simp] theorem ME_depth (K : Type) : (ME K).depth = 64 := rfl

theorem ME_laws (K : Type) : (ME K).Laws where
  rep_frame m m' mp f h ha := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, by rw [ha.accessible]; exact h3,
      (readLE_of_agrees ha (by decide) (by decide)).trans h4⟩
  iter_frame _ _ _ _ _ _ h _ := h
  env_frame m m' _ h ha := ZEnv.frame h ha
  len m mp f h := by
    obtain ⟨rfl, rfl, h3, h4⟩ := h
    exact ⟨h3, by decide, fun ks hk => by rw [h4, hk.eq_nil_of_empty]; rfl⟩
  finite m mp f h := by
    obtain ⟨-, rfl, -, -⟩ := h
    exact ⟨[], keys_empty⟩

/-- Every map value of `ME` is empty. -/
theorem ME_empty {K : Type} {m : Memory} {mp : Nat} {f : AMap K (BitVec 64)}
    (h : IsMap (ME K) m mp f) : f = AMap.empty := by
  unfold IsMap at h
  split at h
  · exact h
  · exact h.2.1

theorem erase_empty {K V : Type} [DecidableEq K] (k : K) : (AMap.empty : AMap K V).erase k = AMap.empty := by
  funext k'; simp [AMap.erase, AMap.empty]

/-- A map value of `ME` stays one when memory outside `priv0` changes. -/
theorem ME_isMap_frame {K : Type} {m m' : Memory} {mp : Nat} {f : AMap K (BitVec 64)}
    (h : IsMap (ME K) m mp f) (ha : Agrees m m' priv0) : IsMap (ME K) m' mp f :=
  IsMap.frame (ME_laws K) h ha

/-! ## `MC`: one map with at most one entry -/

/-- How a cell model reads its key back from memory: a function of the runtime's memory only. -/
structure CellKey (K : Type) where
  get : Memory → K
  frame : ∀ m m', Agrees m m' priv0 → get m' = get m

/-- The contents of the cell: the key `ck.get m` with the value at `MP + 32`. -/
def cellMap {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) : AMap K (BitVec 64) :=
  fun k => if k = ck.get m then some (BitVec.ofNat 64 (m.readLE (MP + 32) 8)) else none

/-- The cell model (see the module documentation). -/
def MC {K : Type} [DecidableEq K] (ck : CellKey K) : MapModel K (BitVec 64) where
  Rep m mp f := mp = MP ∧ m.accessible MP 56 true = true ∧ m.readLE (MP + 48) 8 = 1 ∧
    ((m.readLE MP 8 = 0 ∧ f = AMap.empty) ∨ (m.readLE MP 8 = 1 ∧ f = cellMap ck m))
  Iter _ _ _ _ _ := False
  Typ _ := True
  Env m _ := ZEnv m
  priv := priv0
  depth := 64

@[simp] theorem MC_priv {K : Type} [DecidableEq K] (ck : CellKey K) : (MC ck).priv = priv0 := rfl
@[simp] theorem MC_depth {K : Type} [DecidableEq K] (ck : CellKey K) : (MC ck).depth = 64 := rfl

theorem keys_cell {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) :
    Keys (cellMap ck m) [ck.get m] :=
  ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun k => by
    simp only [List.mem_singleton, cellMap]; split <;> simp_all⟩

theorem cellMap_frame {K : Type} [DecidableEq K] (ck : CellKey K) {m m' : Memory}
    (ha : Agrees m m' priv0) : cellMap ck m' = cellMap ck m := by
  funext k
  simp only [cellMap, ck.frame m m' ha, readLE_of_agrees ha (a := MP + 32) (n := 8) (by decide) (by decide)]

theorem MC_laws {K : Type} [DecidableEq K] (ck : CellKey K) : (MC ck).Laws where
  rep_frame m m' mp f h ha := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hu : m'.readLE MP 8 = m.readLE MP 8 := readLE_of_agrees ha (by decide) (by decide)
    refine ⟨h1, by rw [ha.accessible]; exact h2,
      (readLE_of_agrees ha (by decide) (by decide)).trans h3, ?_⟩
    rw [hu, cellMap_frame ck ha]; exact h4
  iter_frame _ _ _ _ _ _ h _ := h.elim
  env_frame m m' _ h ha := ZEnv.frame h ha
  len m mp f h := by
    obtain ⟨rfl, h2, -, h4⟩ := h
    refine ⟨Memory.accessible_mono _ (IfaceModel.acc_read_of_write h2) (Nat.le_refl _) (by decide),
      by decide, fun ks hk => ?_⟩
    rcases h4 with ⟨hu, rfl⟩ | ⟨hu, rfl⟩
    · rw [hu, hk.eq_nil_of_empty]; rfl
    · rw [hu, hk.length_eq (keys_cell ck m)]; rfl
  finite m mp f h := by
    obtain ⟨-, -, -, h4⟩ := h
    rcases h4 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨[], keys_empty⟩
    · exact ⟨_, keys_cell ck m⟩

/-- The readiness of an assignment in `MC`: the map is empty. -/
def HAssign : RtReady := fun _ _ _ v => v.readLE MP 8 = 0

/-- The readiness of a map creation in `MC`: no map is alive yet, and the header is writable. -/
def HMake : RtReady := fun _ _ _ v => v.readLE (MP + 48) 8 = 0 ∧ v.accessible MP 56 true = true

/-! ### The key decoders -/

/-- The cell's key as a 64-bit word (`_fast64`, `_fast64ptr`, and generic 8-byte keys). -/
def ck64 : CellKey (BitVec 64) where
  get m := BitVec.ofNat 64 (m.readLE (MP + 8) 8)
  frame m m' ha := by rw [readLE_of_agrees ha (by decide) (by decide)]

/-- The cell's key as a 32-bit word (`_fast32`). -/
def ck32 : CellKey (BitVec 32) where
  get m := BitVec.ofNat 32 (m.readLE (MP + 8) 4)
  frame m m' ha := by rw [readLE_of_agrees ha (by decide) (by decide)]

/-- The cell's key as a string's content (`_faststr`): the pointer at `MP + 8`, the length at
`MP + 16`, the bytes as the runtime's memory holds them. -/
def ckStr : CellKey (Nat × Nat) where
  get m := (m.readLE (MP + 16) 8, (rtView priv0 m).readLE (m.readLE (MP + 8) 8) (m.readLE (MP + 16) 8))
  frame m m' ha := by
    have e : ∀ a n, (rtView priv0 m').readLE a n = (rtView priv0 m).readLE a n := fun a n =>
      readLE_congr n a fun j _ => by
        show (if _ then m'.bytes (a + j) else 0) = (if _ then m.bytes (a + j) else 0)
        split
        · rename_i hx
          obtain ⟨r, hr, hx⟩ := List.any_eq_true.1 hx
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
          exact ha.2 _ ⟨r, hr, hx.1, by omega⟩
        · rfl
    rw [e, readLE_of_agrees ha (a := MP + 8) (by decide) (by decide),
      readLE_of_agrees ha (a := MP + 16) (by decide) (by decide)]

/-! ## The witness memory -/

/-- The non-zero bytes of the witness memory: `EqHashModel.wtable`, `TY.Key = KT`, `KT`'s size
and flag, the alive word of `MP`, and the string key at `SK`. -/
def mtable : List (Nat × Nat) :=
  EqHashModel.wtable ++
  [ (TY + 48, 0x00), (TY + 49, 0x0b), (TY + 50, 0x01),
    (KT, 8), (KT + 20, 8),
    (MP + 48, 1),
    (SK, 0x41), (SK + 1, 0x42), (SK + 2, 0x43), (SK + 3, 0x44) ]

/-- The witness memory: `mtable` in `IfaceModel.wmem`'s regions. -/
def mmem : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((mtable.lookup a).getD 0), IfaceModel.wmem.regions⟩

/-- The amd64 witness memory: `mmem` with the return address `wret` at `[wsp]`. -/
def mmem64 : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((((IfaceModel.wsp + 2, 0x20) :: mtable).lookup a).getD 0),
    IfaceModel.wmem.regions⟩

theorem mmem_zenv : ZEnv mmem := ⟨by decide, by decide⟩
theorem mmem64_zenv : ZEnv mmem64 := ⟨by decide, by decide⟩

theorem mmem64_ret : mmem64.readLE IfaceModel.wsp 8 = IfaceModel.wret := by decide

/-- In the witness memory the map at `MP` is `ME`'s empty map. -/
theorem mmem_rep (K : Type) : (ME K).Rep mmem MP AMap.empty := ⟨rfl, rfl, by decide, by decide⟩
theorem mmem64_rep (K : Type) : (ME K).Rep mmem64 MP AMap.empty := ⟨rfl, rfl, by decide, by decide⟩

/-- ... and `MC`'s empty, alive map. -/
theorem mmem_repC {K : Type} [DecidableEq K] (ck : CellKey K) : (MC ck).Rep mmem MP AMap.empty :=
  ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩
theorem mmem64_repC {K : Type} [DecidableEq K] (ck : CellKey K) : (MC ck).Rep mmem64 MP AMap.empty :=
  ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩

theorem readLE_rtView0 {m : Memory} {a n : Nat} (h1 : 0x10000 ≤ a) (h2 : a + n ≤ 0x11000) :
    (rtView priv0 m).readLE a n = m.readLE a n := readLE_rtView (inPriv0 h1 h2)

theorem keyRegular_mmem : KeyRegular (rtView priv0 mmem) TY 8 := by
  unfold KeyRegular keyType tySize isRegularMemory tyTFlag
  rw [readLE_rtView0 (a := TY + 48) (by decide) (by decide),
    show mmem.readLE (TY + 48) 8 = KT by decide,
    readLE_rtView0 (a := KT) (by decide) (by decide), readLE_rtView0 (a := KT + 20) (by decide) (by decide)]
  decide

theorem keyRegular_mmem64 : KeyRegular (rtView priv0 mmem64) TY 8 := by
  unfold KeyRegular keyType tySize isRegularMemory tyTFlag
  rw [readLE_rtView0 (a := TY + 48) (by decide) (by decide),
    show mmem64.readLE (TY + 48) 8 = KT by decide,
    readLE_rtView0 (a := KT) (by decide) (by decide), readLE_rtView0 (a := KT + 20) (by decide) (by decide)]
  decide

theorem hAssign_mmem (args : List Nat) (g sp : Nat) : HAssign args g sp (rtView priv0 mmem) := by
  show (rtView priv0 mmem).readLE MP 8 = 0
  rw [readLE_rtView0 (by decide) (by decide)]; decide

theorem hAssign_mmem64 (args : List Nat) (g sp : Nat) : HAssign args g sp (rtView priv0 mmem64) := by
  show (rtView priv0 mmem64).readLE MP 8 = 0
  rw [readLE_rtView0 (by decide) (by decide)]; decide

/-- The witness memory with no map alive (for `makemap*`). -/
def mmemDead : Memory := mmem.writeLE (MP + 48) 8 0
def mmem64Dead : Memory := mmem64.writeLE (MP + 48) 8 0

theorem hMake_dead (args : List Nat) (g sp : Nat) : HMake args g sp (rtView priv0 mmemDead) := by
  refine ⟨?_, by rw [rtView_accessible]; decide⟩
  rw [readLE_rtView0 (by decide) (by decide)]; unfold mmemDead
  rw [Memory.readLE_writeLE_self]

theorem hMake_dead64 (args : List Nat) (g sp : Nat) : HMake args g sp (rtView priv0 mmem64Dead) := by
  refine ⟨?_, by rw [rtView_accessible]; decide⟩
  rw [readLE_rtView0 (by decide) (by decide)]; unfold mmem64Dead
  rw [Memory.readLE_writeLE_self]

/-! ## Facts the model implementations use -/

theorem ZEnv.writeLE {m : Memory} (h : ZEnv m) {a n : Nat} (v : Nat) (ha : a + n ≤ ZS ∨ ZS + 8 ≤ a) :
    ZEnv (m.writeLE a n v) :=
  ⟨by rw [Memory.accessible_writeLE]; exact h.1, by rw [Memory.readLE_writeLE_of_disjoint _ _ ha.symm]; exact h.2⟩

/-- A cell holding one entry is `MC`'s map holding `cellMap`. -/
theorem MC_rep_cell {K : Type} [DecidableEq K] (ck : CellKey K) {m : Memory}
    (hacc : m.accessible MP 56 true = true) (hal : m.readLE (MP + 48) 8 = 1) (hu : m.readLE MP 8 = 1) :
    (MC ck).Rep m MP (cellMap ck m) := ⟨rfl, hacc, hal, Or.inr ⟨hu, rfl⟩⟩

theorem set_empty_cell {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) (k : K) (v : BitVec 64)
    (hk : ck.get m = k) (hv : m.readLE (MP + 32) 8 = v.toNat) :
    (AMap.empty : AMap K (BitVec 64)).set k v = cellMap ck m := by
  funext k'
  simp only [AMap.set, cellMap, hk, hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  split <;> rfl

/-- What every `MC` assignment returns: after the code has set `used = 1` and stored the key
(so that `ck` reads back `k` whatever is stored at the value slot), the value slot `MP + 32`
meets `AssignSlot` for the empty map. -/
theorem cell_assign {K : Type} [DecidableEq K] (ck : CellKey K) (m : Memory) (k : K) (g : W64)
    (hacc : m.accessible MP 56 true = true) (hal : m.readLE (MP + 48) 8 = 1) (hu : m.readLE MP 8 = 1)
    (hk : ∀ v, ck.get (m.writeLE (MP + 32) 8 v) = k) (hze : ZEnv m) :
    Map.AssignSlot 8 (MC ck) MP AMap.empty k g (MP + 32) m := by
  refine ⟨Memory.accessible_mono _ hacc (by decide) (by decide), inPriv0 (by decide) (by decide),
    fun v => ⟨?_, hze.writeLE _ (by decide), fun mp' _ hne h => absurd h.1 hne⟩⟩
  have e := set_empty_cell ck (m.writeLE (MP + 32) 8 v.toNat) k v (hk _)
    (by rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt v.isLt)
  rw [e]
  exact MC_rep_cell ck (by rw [Memory.accessible_writeLE]; exact hacc)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hal)
    (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by decide)]; exact hu)

/-- The `MC` map after a creation: alive and empty. -/
theorem MC_rep_new {K : Type} [DecidableEq K] (ck : CellKey K) {m : Memory}
    (hacc : m.accessible MP 56 true = true) (hal : m.readLE (MP + 48) 8 = 1) (hu : m.readLE MP 8 = 0) :
    (MC ck).Rep m MP AMap.empty := ⟨rfl, hacc, hal, Or.inl ⟨hu, rfl⟩⟩

/-- No map of `MC` exists while the alive word is `0`. -/
theorem MC_none {K : Type} [DecidableEq K] (ck : CellKey K) {m : Memory} (h : m.readLE (MP + 48) 8 = 0)
    (mp : Nat) (f : AMap K (BitVec 64)) : ¬ (MC ck).Rep m mp f := fun hr => by
  have := hr.2.2.1; omega

end Janus.Contracts.MapModel0
