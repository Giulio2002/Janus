import Janus.Contracts.Panic
import Janus.Contracts.IfaceModel

/-!
# A model of the panic runtime, for the non-vacuity of its contracts

The panic/defer/recover contracts (`Janus.Contracts.Panic`, `Janus.Contracts.PanicAmd64`) are
hypotheses of the theorems that use them; a hypothesis no code can meet would make such a
theorem vacuous. `P0 T rpA` is a model of the panic runtime whose laws hold (`P0_laws`): its
bookkeeping is a small table in its private memory `[0x10000, 0x11000)`, which model code
(`Janus.Contracts.PanicSat`, `PanicSatAmd64`) maintains exactly as the contracts say; the function
table `T` (the binary's `Extracted.funcs`) is stored there too, for the model `gopanic`/`Goexit`
to look frames up in, and `rpA` is the return point of the model's deferred calls.

Layout (`B = 0x10000`):

| Address | Content |
| --- | --- |
| `B + 0x00` | `npan`, the number of `_panic` entries (at most 8) |
| `B + 0x08` | `ndef`, the number of `_defer` records (at most 8) |
| `B + 0x10`, `+0x18`, `+0x20` | the saved open-coded state: a flag, the `deferBits` address, the slots |
| `B + 0x28` | the number of function-table entries |
| `B + 0x100 + 32 i` | panic entry `i` (the top is `npan - 1`): type word, data word, start `SP`, flags (bit 0 `goexit`, bit 1 `recovered`) |
| `B + 0x200 + 96 i` | defer record `i`: `sp`, token (`0`: none), converted flag, `n`, then `n ≤ 8` funcvals, oldest first |
| `B + 0x500 + 56 i` | function-table entry `i`: entry, size, frame, deferreturn, has open-coded defers, the two offsets |

A record with token `0` (a `deferproc`/`deferprocStack` record) or with the converted flag set
reads as one plain record per funcval, newest first; any other record is a range-over-func
record with its token. -/

namespace Janus.Contracts.PanicModel

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Map Janus.Contracts.Panic

/-! ## Addresses and fields -/

/-- A distinct non-zero type word for each runtime-error kind. -/
def errTyp : ErrKind → Nat
  | .bounds => 0x20008 | .divide => 0x20010 | .shift => 0x20018 | .overflow => 0x20020
  | .float => 0x20028 | .mem => 0x20030 | .simdImm => 0x20038 | .dottype => 0x20040
  | .makeslice => 0x20048 | .unsafeOp => 0x20050 | .wrap => 0x20058 | .rangeState => 0x20060

abbrev B : Nat := 0x10000

/-- A 64-bit word of `m`. -/
abbrev rd (m : Memory) (a : Nat) : Nat := m.readLE a 8

abbrev npan (m : Memory) : Nat := rd m B
abbrev ndef (m : Memory) : Nat := rd m (B + 8)
abbrev panAt (i : Nat) : Nat := B + 0x100 + 32 * i
abbrev recAt (i : Nat) : Nat := B + 0x200 + 96 * i
abbrev tabAt (i : Nat) : Nat := B + 0x500 + 56 * i

/-- Panic entry `i`. -/
def decPan (m : Memory) (i : Nat) : PanicRec :=
  { arg := ⟨rd m (panAt i), rd m (panAt i + 8)⟩, start := rd m (panAt i + 16),
    goexit := rd m (panAt i + 24) % 2 == 1, recovered := rd m (panAt i + 24) / 2 % 2 == 1 }

/-- Entries `k - 1` down to `0`. -/
def panList (m : Memory) : Nat → List PanicRec
  | 0 => []
  | k + 1 => decPan m k :: panList m k

def recSp (m : Memory) (i : Nat) : Nat := rd m (recAt i)
def recTok (m : Memory) (i : Nat) : Nat := rd m (recAt i + 8)
def recConv (m : Memory) (i : Nat) : Nat := rd m (recAt i + 16)
def recN (m : Memory) (i : Nat) : Nat := rd m (recAt i + 24)
def recFn (m : Memory) (i j : Nat) : Nat := rd m (recAt i + 32 + 8 * j)

/-- Funcvals `j - 1` down to `0` of record `i` (newest first). -/
def recFns (m : Memory) (i : Nat) : Nat → List Nat
  | 0 => []
  | j + 1 => recFn m i j :: recFns m i j

/-- Record `i` as the runtime's chain reads it. -/
def decRec (m : Memory) (i : Nat) : List DeferRec :=
  if recTok m i = 0 ∨ recConv m i ≠ 0 then
    (recFns m i (min (recN m i) 8)).map (fun f => ({ sp := recSp m i, fns := [f] } : DeferRec))
  else [{ sp := recSp m i, fns := recFns m i (min (recN m i) 8), token := some (recTok m i) }]

/-- Records `k - 1` down to `0`. -/
def recList (m : Memory) : Nat → List DeferRec
  | 0 => []
  | k + 1 => decRec m k ++ recList m k

/-- The least free funcval capacity of records `0 … k - 1` (8 if there are none). -/
def capMin (m : Memory) : Nat → Nat
  | 0 => 8
  | k + 1 => min (8 - recN m k) (capMin m k)

/-- Function-table entry `i` encodes `f`. -/
def TabEntry (m : Memory) (i : Nat) (f : FuncInfo) : Prop :=
  rd m (tabAt i) = f.entry ∧ rd m (tabAt i + 8) = f.size ∧ rd m (tabAt i + 16) = f.frame ∧
    rd m (tabAt i + 24) = f.deferreturn ∧
    rd m (tabAt i + 32) = (if f.openDefer.isSome then 1 else 0) ∧
    rd m (tabAt i + 40) = ((f.openDefer.map (·.1)).getD 0) ∧
    rd m (tabAt i + 48) = ((f.openDefer.map (·.2)).getD 0)

/-- The function table in `m` is `T`. -/
def TableOK (m : Memory) (T : List FuncInfo) : Prop :=
  T.length ≤ 16 ∧ rd m (B + 0x28) = T.length ∧ ∀ i (h : i < T.length), TabEntry m i T[i]

/-- The model's invariant: its memory writable, at most 8 panic entries and 8 records, each with
at most 8 funcvals, a plain or converted record never empty, the function table `T`. -/
@[irreducible] def Env0 (T : List FuncInfo) (m : Memory) : Prop :=
  m.accessible B 0x1000 true = true ∧ npan m ≤ 8 ∧ ndef m ≤ 8 ∧
    (∀ i, i < ndef m → recN m i ≤ 8 ∧ ((recTok m i = 0 ∨ recConv m i ≠ 0) → 1 ≤ recN m i)) ∧
    TableOK m T

@[irreducible] def panics0 (m : Memory) : List PanicRec := panList m (min (npan m) 8)
@[irreducible] def defers0 (m : Memory) : List DeferRec := recList m (min (ndef m) 8)
@[irreducible] def saved0 (m : Memory) : Option (Nat × Nat) :=
  if rd m (B + 0x10) = 0 then none else some (rd m (B + 0x18), rd m (B + 0x20))
@[irreducible] def room0 (m : Memory) : Nat := min (8 - npan m) (min (8 - ndef m) (capMin m (min (ndef m) 8)))

/-- The model of the panic runtime. -/
def P0 (T : List FuncInfo) (rpA : Nat) : PanicRuntime where
  err k := ⟨errTyp k, 0⟩
  priv := [(B, B + 0x1000)]
  depth := 256
  Env := Env0 T
  panics m _ := panics0 m
  defers m _ := defers0 m
  saved m _ := saved0 m
  rp _ _ := rpA
  room m _ := room0 m
  wrapper _ := False

/-! ## The laws -/

theorem rd_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) {a : Nat} (h1 : B ≤ a)
    (h2 : a + 8 ≤ B + 0x1000) : rd m' a = rd m a :=
  h.readLE ⟨(B, B + 0x1000), by simp, h1, h2⟩

theorem decPan_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) {i : Nat} (hi : i < 8) :
    decPan m' i = decPan m i := by
  simp only [decPan, panAt]
  rw [rd_agree h (by simp [B]; omega) (by simp [B]; omega), rd_agree h (by simp [B]; omega) (by simp [B]; omega),
    rd_agree h (by simp [B]; omega) (by simp [B]; omega), rd_agree h (by simp [B]; omega) (by simp [B]; omega)]

theorem panList_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) :
    ∀ k, k ≤ 8 → panList m' k = panList m k
  | 0, _ => rfl
  | k + 1, hk => by simp only [panList, decPan_agree h (by omega : k < 8), panList_agree h k (by omega)]

theorem recFields_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) {i : Nat} (hi : i < 8) :
    recSp m' i = recSp m i ∧ recTok m' i = recTok m i ∧ recConv m' i = recConv m i ∧
      recN m' i = recN m i := by
  simp only [recSp, recTok, recConv, recN, recAt]
  refine ⟨rd_agree h (by simp [B]; omega) (by simp [B]; omega), rd_agree h (by simp [B]; omega) (by simp [B]; omega),
    rd_agree h (by simp [B]; omega) (by simp [B]; omega), rd_agree h (by simp [B]; omega) (by simp [B]; omega)⟩

theorem recFns_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) {i : Nat} (hi : i < 8) :
    ∀ j, j ≤ 8 → recFns m' i j = recFns m i j
  | 0, _ => rfl
  | j + 1, hj => by
    simp only [recFns, recFn, recAt]
    rw [rd_agree h (by simp [B]; omega) (by simp [B]; omega), recFns_agree h hi j (by omega)]

theorem decRec_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) {i : Nat} (hi : i < 8) :
    decRec m' i = decRec m i := by
  obtain ⟨h1, h2, h3, h4⟩ := recFields_agree h hi
  simp only [decRec, h1, h2, h3, h4, recFns_agree h hi _ (Nat.min_le_right _ _)]

theorem recList_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) :
    ∀ k, k ≤ 8 → recList m' k = recList m k
  | 0, _ => rfl
  | k + 1, hk => by simp only [recList, decRec_agree h (by omega : k < 8), recList_agree h k (by omega)]

theorem capMin_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) :
    ∀ k, k ≤ 8 → capMin m' k = capMin m k
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [capMin, (recFields_agree h (by omega : k < 8)).2.2.2, capMin_agree h k (by omega)]

theorem tableOK_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) {T : List FuncInfo}
    (ht : TableOK m T) : TableOK m' T := by
  obtain ⟨hl, hn, he⟩ := ht
  refine ⟨hl, by rw [rd_agree h (by simp [B]) (by simp [B])]; exact hn, fun i hi => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := he i hi
  have hb : ∀ k, k ≤ 48 → rd m' (tabAt i + k) = rd m (tabAt i + k) := fun k hk =>
    rd_agree h (by simp only [tabAt, B]; omega) (by simp only [tabAt, B]; omega)
  exact ⟨by rw [show tabAt i = tabAt i + 0 from rfl, hb 0 (by omega)]; exact e1,
    by rw [hb 8 (by omega)]; exact e2, by rw [hb 16 (by omega)]; exact e3,
    by rw [hb 24 (by omega)]; exact e4, by rw [hb 32 (by omega)]; exact e5,
    by rw [hb 40 (by omega)]; exact e6, by rw [hb 48 (by omega)]; exact e7⟩

theorem npan_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) : npan m' = npan m :=
  rd_agree h (by simp [B]) (by simp [B])

theorem ndef_agree {m m' : Memory} (h : Agrees m m' [(B, B + 0x1000)]) : ndef m' = ndef m :=
  rd_agree h (by simp [B]) (by simp [B])

theorem env0_agree {T : List FuncInfo} {m m' : Memory} (h : Env0 T m) (ha : Agrees m m' [(B, B + 0x1000)]) :
    Env0 T m' := by
  unfold Env0 at h ⊢
  obtain ⟨hacc, hp, hd, hr, ht⟩ := h
  refine ⟨?_, ?_, ?_, fun i hi => ?_, tableOK_agree ha ht⟩
  · rw [ha.1]; exact hacc
  · rw [npan_agree ha]; exact hp
  · rw [ndef_agree ha]; exact hd
  · rw [ndef_agree ha] at hi
    obtain ⟨-, h2, h3, h4⟩ := recFields_agree ha (by omega : i < 8)
    rw [h2, h3, h4]; exact hr i hi

theorem P0_priv (T : List FuncInfo) (rpA : Nat) : (P0 T rpA).priv = [(B, B + 0x1000)] := rfl
theorem P0_panics (T : List FuncInfo) (rpA : Nat) (m : Memory) (g : Nat) :
    (P0 T rpA).panics m g = panics0 m := rfl
theorem P0_defers (T : List FuncInfo) (rpA : Nat) (m : Memory) (g : Nat) :
    (P0 T rpA).defers m g = defers0 m := rfl
theorem P0_saved (T : List FuncInfo) (rpA : Nat) (m : Memory) (g : Nat) :
    (P0 T rpA).saved m g = saved0 m := rfl
theorem P0_room (T : List FuncInfo) (rpA : Nat) (m : Memory) (g : Nat) :
    (P0 T rpA).room m g = room0 m := rfl
theorem P0_rp (T : List FuncInfo) (rpA : Nat) (m : Memory) (g : Nat) :
    (P0 T rpA).rp m g = rpA := rfl
theorem P0_depth (T : List FuncInfo) (rpA : Nat) : (P0 T rpA).depth = 256 := rfl
theorem P0_wrapper (T : List FuncInfo) (rpA : Nat) (pc : Nat) : (P0 T rpA).wrapper pc = False := rfl
theorem P0_env (T : List FuncInfo) (rpA : Nat) (m : Memory) : (P0 T rpA).Env m = Env0 T m := rfl

theorem P0_laws (T : List FuncInfo) (rpA : Nat) : (P0 T rpA).Laws where
  err_typ_ne k := by cases k <;> simp [P0, errTyp]
  err_inj k k' hk := by
    have : ((P0 T rpA).err k).typ = ((P0 T rpA).err k').typ := by rw [hk]
    cases k <;> cases k' <;> first | rfl | (simp only [P0, errTyp] at this; omega)
  depth_pos := by show 0 < 256; decide
  env_frame m m' h ha := env0_agree h ha
  panics_frame m m' g ha := by
    rw [P0_panics, P0_panics]; unfold panics0; rw [npan_agree ha]; exact panList_agree ha _ (Nat.min_le_right _ _)
  defers_frame m m' g ha := by
    rw [P0_defers, P0_defers]; unfold defers0; rw [ndef_agree ha]; exact recList_agree ha _ (Nat.min_le_right _ _)
  saved_frame m m' g ha := by
    rw [P0_saved, P0_saved]; unfold saved0; rw [rd_agree ha (by simp [B]) (by simp [B]), rd_agree ha (by simp [B]) (by simp [B]),
      rd_agree ha (by simp [B]) (by simp [B])]
  rp_frame _ _ _ _ := rfl
  room_frame m m' g ha := by
    rw [P0_room, P0_room]; unfold room0; rw [npan_agree ha, ndef_agree ha, capMin_agree ha _ (Nat.min_le_right _ _)]

/-! ## Stores and the decoders

A store that misses the fields a decoder reads leaves the decoded value alone; with
`simp (disch := omega)` these turn the model code's final memory (a chain of `writeLE`) into the
bookkeeping it denotes. -/

section writes
variable {m : Memory} {a n v : Nat}

theorem rd_w (h : b + 8 ≤ a ∨ a + n ≤ b) : rd (m.writeLE a n v) b = rd m b :=
  m.readLE_writeLE_of_disjoint v h

theorem decPan_w (h : a + n ≤ panAt i ∨ panAt i + 32 ≤ a) : decPan (m.writeLE a n v) i = decPan m i := by
  unfold panAt at h
  simp only [decPan, panAt]
  rw [rd_w (by omega), rd_w (by omega), rd_w (by omega), rd_w (by omega)]

theorem panList_w : ∀ k, (a + n ≤ panAt 0 ∨ panAt k ≤ a) → panList (m.writeLE a n v) k = panList m k
  | 0, _ => rfl
  | k + 1, h => by
    show decPan (m.writeLE a n v) k :: panList (m.writeLE a n v) k = decPan m k :: panList m k
    rw [decPan_w (i := k) (by unfold panAt at h ⊢; omega), panList_w k (by unfold panAt at h ⊢; omega)]

theorem recFns_w (i : Nat) (h : a + n ≤ recAt i + 32 ∨ recAt i + 96 ≤ a) :
    ∀ j, j ≤ 8 → recFns (m.writeLE a n v) i j = recFns m i j
  | 0, _ => rfl
  | j + 1, hj => by
    show rd (m.writeLE a n v) (recAt i + 32 + 8 * j) :: recFns (m.writeLE a n v) i j =
      rd m (recAt i + 32 + 8 * j) :: recFns m i j
    rw [rd_w (by unfold recAt at h ⊢; omega), recFns_w i h j (by omega)]

theorem decRec_w (h : a + n ≤ recAt i ∨ recAt i + 96 ≤ a) : decRec (m.writeLE a n v) i = decRec m i := by
  have e1 : recSp (m.writeLE a n v) i = recSp m i := rd_w (by unfold recAt at h ⊢; omega)
  have e2 : recTok (m.writeLE a n v) i = recTok m i := rd_w (by unfold recAt at h ⊢; omega)
  have e3 : recConv (m.writeLE a n v) i = recConv m i := rd_w (by unfold recAt at h ⊢; omega)
  have e4 : recN (m.writeLE a n v) i = recN m i := rd_w (by unfold recAt at h ⊢; omega)
  have e5 := recFns_w (m := m) (a := a) (n := n) (v := v) i (h.elim (fun h => Or.inl (by omega)) (fun h => Or.inr h)) _
    (Nat.min_le_right (recN m i) 8)
  simp only [decRec, e1, e2, e3, e4, e5]

theorem recList_w : ∀ k, (a + n ≤ recAt 0 ∨ recAt k ≤ a) → recList (m.writeLE a n v) k = recList m k
  | 0, _ => rfl
  | k + 1, h => by
    show decRec (m.writeLE a n v) k ++ recList (m.writeLE a n v) k = decRec m k ++ recList m k
    rw [decRec_w (i := k) (by unfold recAt at h ⊢; omega), recList_w k (by unfold recAt at h ⊢; omega)]

theorem capMin_w : ∀ k, (a + n ≤ recAt 0 ∨ recAt k ≤ a) → capMin (m.writeLE a n v) k = capMin m k
  | 0, _ => rfl
  | k + 1, h => by
    show min (8 - rd (m.writeLE a n v) (recAt k + 24)) (capMin (m.writeLE a n v) k) =
      min (8 - rd m (recAt k + 24)) (capMin m k)
    rw [rd_w (by unfold recAt at h ⊢; omega), capMin_w k (by unfold recAt at h ⊢; omega)]

theorem tableOK_w {T : List FuncInfo} (h : a + n ≤ B + 0x28 ∨ (B + 0x30 ≤ a ∧ a + n ≤ tabAt 0) ∨ tabAt 16 ≤ a)
    (ht : TableOK m T) : TableOK (m.writeLE a n v) T := by
  obtain ⟨hl, hn, he⟩ := ht
  refine ⟨hl, by rw [rd_w (by unfold tabAt at h; unfold B at h ⊢; omega)]; exact hn, fun i hi => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := he i hi
  have hb : ∀ k, k ≤ 48 → rd (m.writeLE a n v) (tabAt i + k) = rd m (tabAt i + k) := fun k hk =>
    rd_w (by unfold tabAt B at h ⊢; omega)
  exact ⟨by rw [show tabAt i = tabAt i + 0 from rfl, hb 0 (by omega)]; exact e1,
    by rw [hb 8 (by omega)]; exact e2, by rw [hb 16 (by omega)]; exact e3,
    by rw [hb 24 (by omega)]; exact e4, by rw [hb 32 (by omega)]; exact e5,
    by rw [hb 40 (by omega)]; exact e6, by rw [hb 48 (by omega)]; exact e7⟩

theorem readLE_writeLE_same' {a n v b : Nat} (h : b = a) : (m.writeLE a n v).readLE b n = v % 256 ^ n := by
  rw [h]; exact m.readLE_writeLE_self a n v

theorem panList_succ (m : Memory) (k : Nat) : panList m (k + 1) = decPan m k :: panList m k := rfl
theorem recList_succ (m : Memory) (k : Nat) : recList m (k + 1) = decRec m k ++ recList m k := rfl
theorem recFns_succ (m : Memory) (i j : Nat) : recFns m i (j + 1) = recFn m i j :: recFns m i j := rfl
theorem capMin_succ (m : Memory) (k : Nat) : capMin m (k + 1) = min (8 - recN m k) (capMin m k) := rfl
theorem panics0_eq (m : Memory) : panics0 m = panList m (min (npan m) 8) := by unfold panics0; rfl
theorem defers0_eq (m : Memory) : defers0 m = recList m (min (ndef m) 8) := by unfold defers0; rfl
theorem saved0_eq (m : Memory) : saved0 m =
    if rd m (B + 0x10) = 0 then none else some (rd m (B + 0x18), rd m (B + 0x20)) := by unfold saved0; rfl
theorem room0_eq (m : Memory) : room0 m = min (8 - npan m) (min (8 - ndef m) (capMin m (min (ndef m) 8))) := by
  unfold room0; rfl

end writes

end Janus.Contracts.PanicModel
