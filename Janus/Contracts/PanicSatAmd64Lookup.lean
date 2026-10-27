import Janus.Contracts.PanicSatAmd64EntrySegs


/-!
# The amd64 model engine's table search

The search of the model's function table for the function containing the return address
(`seg_lookup`) and `lookup_found`, which takes the machine from the start of the search to the first
loop head, with the loop's frame written.
-/

namespace Janus.Contracts.PanicSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.PanicAmd64 Janus.Contracts.PanicModel
open Janus.Contracts.Panic (DeferMode Frame Item fnItems recItems openItems frameItems frameKeep bitsWin)
open Janus.Contracts.PanicSat (modeCode curItems topBit)
open Janus.Spec.Map

theorem rr_bind {p : Program} {t1 t2 : W64} {s : State} {Q1 Q2 : State → Prop}
    (h : ReachesRet p t1 s Q1) (hk : ∀ s', s'.rip = t1 → Q1 s' → ReachesRet p t2 s' Q2) : ReachesRet p t2 s Q2 := by
  obtain ⟨k, s', hk1, hpc, hq⟩ := h
  obtain ⟨k', s'', hk2, hpc2, hq2⟩ := hk s' hpc hq
  exact ⟨k + k', s'', hk1.trans hk2, hpc2, hq2⟩

theorem find_eq (T : List FuncInfo) (pc : Nat) :
    FuncInfo.find T pc = T.find? (fun f => decide (f.entry ≤ pc ∧ pc < f.entry + f.size)) := rfl

/-- The model's search of the function table for the function containing `ra`. -/
theorem seg_lookup (T : List FuncInfo) (ra : Nat) (hra : ra < 2 ^ 64) (hT : ∀ f ∈ T, f.entry + f.size < 2 ^ 64)
    (fi : FuncInfo) :
    ∀ (r i : Nat) (c : State), i + r = T.length → c.rip = BitVec.ofNat 64 (E + 0x245) →
      c.regs 9 = BitVec.ofNat 64 r → c.regs 10 = BitVec.ofNat 64 (tabAt i) → c.regs 1 = BitVec.ofNat 64 ra →
      TableOK c.mem T → c.mem.accessible B 0x1000 true = true →
      (T.drop i).find? (fun f => decide (f.entry ≤ ra ∧ ra < f.entry + f.size)) = some fi →
      ReachesRet qE (BitVec.ofNat 64 (E + 0x26a)) c (fun d => d.mem = c.mem ∧ d.regs 4 = c.regs 4 ∧
        d.regs 5 = c.regs 5 ∧ d.regs 14 = c.regs 14 ∧ d.xmm 15 = c.xmm 15 ∧ d.df = c.df ∧
        d.regs 7 = c.regs 7 ∧
        ∃ j, j < T.length ∧ T[j]? = some fi ∧ d.regs 10 = BitVec.ofNat 64 (tabAt j) ∧
          d.regs 0 = BitVec.ofNat 64 fi.entry)
  | 0, i, c, hlen, hpc, h9, h10, h1, htab, hB, hf => by
    have : T.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [this] at hf; simp at hf
  | r + 1, i, c, hlen, hpc, h9, h10, h1, htab, hB, hf => by
    have hi : i < T.length := by omega
    have hb1 : (1 : BitVec 64).toNat = 1 := rfl
    have hb56 : (56 : BitVec 64).toNat = 56 := rfl
    obtain ⟨hl16, hnt, htE⟩ := htab
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := htE i hi
    have hdrop : T.drop i = T[i] :: T.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hTi := hT T[i] (List.getElem_mem hi)
    have hr64 : r + 1 < 2 ^ 64 := by omega
    have hptr : tabAt i + 16 ≤ 2 ^ 48 := by simp only [tabAt, B]; omega
    have hacc : c.mem.accessible (tabAt i) 16 false = true :=
      Janus.Arm64.Memory.accessible_sub _ hB (Or.inl rfl) (by simp only [tabAt, B]; omega) (by simp only [tabAt, B]; omega)
    refine rr_bind (seg_lk_cbz c r hpc h9 hr64) fun c1 hpc1 hq1 => ?_
    obtain ⟨hm1, hrg1, hx1, hdf1⟩ := hq1
    have he' : c1.mem.readLE (tabAt i) 8 = T[i].entry := by rw [hm1]; exact e1
    have hs' : c1.mem.readLE (tabAt i + 8) 8 = T[i].size := by rw [hm1]; exact e2
    have h10' : c1.regs 10 = BitVec.ofNat 64 (tabAt i) := by rw [hrg1]; exact h10
    have h1' : c1.regs 1 = BitVec.ofNat 64 ra := by rw [hrg1]; exact h1
    have hacc' : c1.mem.accessible (tabAt i) 16 false = true := by rw [hm1]; exact hacc
    by_cases hpred : T[i].entry ≤ ra ∧ ra < T[i].entry + T[i].size
    · refine rr_bind (seg_lk_found c1 (tabAt i) T[i].entry T[i].size ra hpc1 h10' h1' hptr hacc' he' hs' hTi hra
        hpred.1 hpred.2) fun d hpcd hqd => ?_
      obtain ⟨hmd, hd4, hd5, hd14, hdx, hddf, hd7, h10d, h0d⟩ := hqd
      have hfi : T[i] = fi := by
        rw [hdrop] at hf
        simp only [List.find?_cons, decide_eq_true hpred, Option.some.injEq] at hf
        exact hf
      refine ReachesRet.done hpcd ⟨by rw [hmd, hm1], ?_, ?_, ?_, ?_, ?_, ?_, i, hi, ?_, h10d, ?_⟩
      · rw [hd4, hrg1]
      · rw [hd5, hrg1]
      · rw [hd14, hrg1]
      · rw [hdx, hx1]
      · rw [hddf, hdf1]
      · rw [hd7, hrg1]
      · rw [List.getElem?_eq_getElem hi, hfi]
      · rw [h0d, hfi]
    · have hpredf : decide (T[i].entry ≤ ra ∧ ra < T[i].entry + T[i].size) = false := decide_eq_false hpred
      refine rr_bind (seg_lk_next c1 (tabAt i) T[i].entry T[i].size ra hpc1 h10' h1' hptr hacc' he' hs' hTi hra
        (by omega)) fun c2 hpc2 hq2 => ?_
      obtain ⟨hm2, hd4, hd5, hd14, hdx, hddf, hd7, h92, h102, h12⟩ := hq2
      have hf' : (T.drop (i + 1)).find? (fun f => decide (f.entry ≤ ra ∧ ra < f.entry + f.size)) = some fi := by
        rw [hdrop] at hf
        simp only [List.find?_cons, hpredf] at hf
        exact hf
      have h9' : c2.regs 9 = BitVec.ofNat 64 r := by
        rw [h92, hrg1, h9]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have h10'' : c2.regs 10 = BitVec.ofNat 64 (tabAt (i + 1)) := by
        rw [h102, hrg1, h10]; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, tabAt, B]; omega
      have ih := seg_lookup T ra hra hT fi r (i + 1) c2 (by omega) hpc2 h9' h10'' (by rw [h12, hrg1]; exact h1)
        (by rw [hm2, hm1]; exact ⟨hl16, hnt, htE⟩) (by rw [hm2, hm1]; exact hB) hf'
      refine reachesRet_mono ih fun d hd => ?_
      obtain ⟨hmd, hd4', hd5', hd14', hdx', hddf', hd7', j, hj, hTj, h10d, h0d⟩ := hd
      refine ⟨by rw [hmd, hm2, hm1], ?_, ?_, ?_, ?_, ?_, ?_, j, hj, hTj, h10d, h0d⟩
      · rw [hd4', hd4, hrg1]
      · rw [hd5', hd5, hrg1]
      · rw [hd14', hd14, hrg1]
      · rw [hdx', hdx, hx1]
      · rw [hddf', hddf, hdf1]
      · rw [hd7', hd7, hrg1]

/-- What the model's table search needs of the function table (amd64: code addresses below `2^47`). -/
def TOK (T : List FuncInfo) : Prop :=
  ∀ f ∈ T, f.entry + f.size < 2 ^ 64 ∧ f.entry + f.deferreturn < 2 ^ 47 ∧
    f.frame < 2 ^ 48 ∧ ∀ o ∈ f.openDefer, 8 ≤ f.frame ∧ o.1 ≤ f.frame - 8 ∧ o.2 ≤ f.frame - 8


section lf
variable {p : Program}

set_option maxHeartbeats 0 in
/-- From the start of the table search to the loop head: the function containing the return
address is found and the loop's frame is written. -/
theorem lookup_found (hp : EngineAt p) (T : List FuncInfo) (hT : TOK T) {mode : DeferMode} (hm : mode ≠ .ret)
    (s1 : State) (fi : FuncInfo) (hpc : s1.rip = BitVec.ofNat 64 eLookup) (henv : Env0 T s1.mem)
    (hal : (s1.regs 4).toNat % 8 = 0) (hsp : (s1.regs 4).toNat + 8 ≤ 2 ^ 48) (h104 : 104 ≤ (s1.regs 4).toNat)
    (hacc : s1.mem.accessible ((s1.regs 4).toNat - 104) 104 true = true)
    (hra : s1.mem.accessible (s1.regs 4).toNat 8 false = true)
    (hfind : FuncInfo.find T (s1.mem.readLE (s1.regs 4).toNat 8) = some fi)
    (hmode : s1.regs 7 = BitVec.ofNat 64 (modeCode mode))
    (hba : fi.openDefer.isSome → s1.mem.accessible (fi.bitsAt ((s1.regs 4).toNat + 8)) 1 false = true) :
    ∃ k c, Janus.Amd64.Program.Steps p s1 k c ∧ c.rip = BitVec.ofNat 64 eLH ∧
      c.regs 4 = BitVec.ofNat 64 ((s1.regs 4).toNat - 96) ∧ c.regs 5 = s1.regs 5 ∧ c.regs 14 = s1.regs 14 ∧
      c.xmm 15 = s1.xmm 15 ∧ c.df = s1.df ∧
      MemFrame s1.mem c.mem [((s1.regs 4).toNat - 96, (s1.regs 4).toNat - 32)] ∧
      FrameMem c.mem (Janus.Contracts.PanicAmd64.frameOf fi ((s1.regs 4).toNat + 8) s1.mem) mode
        (if (Janus.Contracts.PanicAmd64.frameOf fi ((s1.regs 4).toNat + 8) s1.mem).openAt.isSome then 1 else 0) 0 := by
  have htab := henv.table
  have hB := henv.acc
  obtain ⟨hl16, hnt, htE⟩ := htab
  have hra64 : (s1.mem.readLE (s1.regs 4).toNat 8) < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt s1.mem (s1.regs 4).toNat 8
    have h : (256:Nat)^8 = 2^64 := by decide
    omega
  obtain ⟨k1, s2, hk1, hpc2, hq1⟩ := reachesRet_transfer hp (seg_lk_entry s1 hpc hB hra hsp)
  obtain ⟨hm2, hs4, hs5, hs14, hsx, hsdf, hs7, hs1, hs9, hs10⟩ := hq1
  have hlk := seg_lookup T (s1.mem.readLE (s1.regs 4).toNat 8) hra64 (fun f hf => (hT f hf).1) fi T.length 0 s2
    (by omega) hpc2 (by rw [hs9]; exact congrArg _ hnt) hs10 hs1 (by rw [hm2]; exact ⟨hl16, hnt, htE⟩)
    (by rw [hm2]; exact hB) (by rw [find_eq] at hfind; exact hfind)
  obtain ⟨k2, s3, hk2, hpc3, hq3⟩ := reachesRet_transfer hp hlk
  obtain ⟨hm3, h34, h35, h314, h3x, h3df, h37, j, hj, hTj, h103, h03⟩ := hq3
  have hTjfi : T[j] = fi := by
    rw [List.getElem?_eq_getElem hj] at hTj; exact Option.some.inj hTj
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := htE j hj
  rw [hTjfi] at e1 e2 e3 e4 e5 e6 e7
  have hfiT : fi ∈ T := by rw [← hTjfi]; exact List.getElem_mem hj
  obtain ⟨t1, t2, t4, t5⟩ := hT fi hfiT
  have hsm : s3.mem = s1.mem := by rw [hm3, hm2]
  have hspn : (s3.regs 4).toNat = (s1.regs 4).toNat := by rw [h34, hs4]
  have h7 : s3.regs 7 = BitVec.ofNat 64 (modeCode mode) := by rw [h37, hs7, hmode]
  have h7n : (s3.regs 7).toNat = modeCode mode := by
    rw [h7, BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; cases mode <;> simp [modeCode]
  have hfr : s3.mem.readLE (tabAt j + 16) 8 = fi.frame := by rw [hsm]; exact e3
  have hdr : s3.mem.readLE (tabAt j + 24) 8 = fi.deferreturn := by rw [hsm]; exact e4
  have hj16 : j < 16 := by omega
  have hacc3 : s3.mem.accessible ((s3.regs 4).toNat - 104) 104 true = true := by rw [hsm, hspn]; exact hacc
  have hB3 : s3.mem.accessible B 0x1000 true = true := by rw [hsm]; exact hB
  have hf64 : (s3.regs 4).toNat + 8 + fi.frame < 2 ^ 64 := by rw [hspn]; omega
  have hd64 : fi.entry + fi.deferreturn < 2 ^ 64 := by omega
  have hent : fi.entry < 2 ^ 64 := by omega
  have e96 : (s1.regs 4).toNat + 8 - 104 = (s1.regs 4).toNat - 96 := by omega
  have hc5' : ∀ c : State, c.regs 5 = s3.regs 5 → c.regs 5 = s1.regs 5 := fun c h => by rw [h, h35, hs5]
  cases hod : fi.openDefer with
  | none =>
    have hop : s3.mem.readLE (tabAt j + 32) 8 = 0 := by rw [hsm]; have := e5; rw [hod] at this; simpa using this
    obtain ⟨k3, c, hk3, -, hq⟩ := reachesRet_transfer hp (seg_found_noopen s3 j fi.frame fi.deferreturn fi.entry hpc3 h103 h03
      (by rw [hspn]; exact hal) (by rw [hspn]; exact hsp) (by rw [hspn]; exact h104) hacc3 hB3 hj16 hfr hdr hop hf64 hd64 hent)
    obtain ⟨hcpc, hc4, hc5, hc14, hcx, hcdf, hmf, w0, w8, w16, w24, w32⟩ := hq
    rw [hspn] at hc4 hmf w0 w8 w16 w24 w32
    refine ⟨k1 + k2 + k3, c, (hk1.trans hk2).trans hk3, hcpc, hc4, by rw [hc5, h35, hs5], by rw [hc14, h314, hs14],
      by rw [hcx, h3x, hsx], by rw [hcdf, h3df, hsdf], by rw [← hsm]; rw [hspn] at *; exact hmf, ?_⟩
    have hF : (Janus.Contracts.PanicAmd64.frameOf fi ((s1.regs 4).toNat + 8) s1.mem).openAt = none := by
      simp [Janus.Contracts.PanicAmd64.frameOf, Janus.Contracts.Panic.frameOf, hod]
    have hph : (if (Janus.Contracts.PanicAmd64.frameOf fi ((s1.regs 4).toNat + 8) s1.mem).openAt.isSome then 1 else 0) = 0 := by
      rw [hF]; rfl
    rw [hph]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hm, fun h => absurd rfl h⟩
    · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104) 8 = (s1.regs 4).toNat + 8
      rw [e96]; exact w0
    · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 8) 8 = (s1.regs 4).toNat + 8 + fi.frame
      rw [e96]; exact w8
    · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 16) 8 = fi.entry + fi.deferreturn
      rw [e96]; exact w16
    · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 24) 8 = modeCode mode
      rw [e96, ← h7n]; exact w24
    · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 32) 8 = 0
      rw [e96]; exact w32
    · intro ba sa h; rw [hF] at h; cases h
  | some o =>
    obtain ⟨o1, o2⟩ := o
    have hop : s3.mem.readLE (tabAt j + 32) 8 = 1 := by rw [hsm]; have := e5; rw [hod] at this; simpa using this
    have ho1 : s3.mem.readLE (tabAt j + 40) 8 = o1 := by rw [hsm]; have := e6; rw [hod] at this; simpa using this
    have ho2 : s3.mem.readLE (tabAt j + 48) 8 = o2 := by rw [hsm]; have := e7; rw [hod] at this; simpa using this
    obtain ⟨hf8, hf1, hf2⟩ := t5 (o1, o2) (by rw [hod]; rfl)
    have hbaa := hba (by rw [hod]; rfl)
    have hbitsAt : fi.bitsAt ((s1.regs 4).toNat + 8) = (s1.regs 4).toNat + fi.frame - o1 := by
      simp only [FuncInfo.bitsAt, FuncInfo.varp, hod, Option.map_some, Option.getD_some]; omega
    have hslotsAt : fi.slotsAt ((s1.regs 4).toNat + 8) = (s1.regs 4).toNat + fi.frame - o2 := by
      simp only [FuncInfo.slotsAt, FuncInfo.varp, hod, Option.map_some, Option.getD_some]; omega
    rw [hbitsAt] at hbaa
    have hbaa3 : s3.mem.accessible ((s3.regs 4).toNat + fi.frame - o1) 1 false = true := by rw [hsm, hspn]; exact hbaa
    obtain ⟨b, hb⟩ : ∃ b, s1.mem.readLE ((s1.regs 4).toNat + fi.frame - o1) 1 = b := ⟨_, rfl⟩
    have hb3 : s3.mem.readLE ((s3.regs 4).toNat + fi.frame - o1) 1 = b := by rw [hsm, hspn]; exact hb
    have hphd : (b = 0 ∧ (if b = 0 then 0 else 1) = 0) ∨ (b ≠ 0 ∧ (if b = 0 then 0 else 1) = 1) := by
      by_cases hb0 : b = 0 <;> simp [hb0]
    obtain ⟨k3, c, hk3, -, hq⟩ := reachesRet_transfer hp (seg_found_open s3 j fi.frame fi.deferreturn fi.entry o1 o2 b
      (if b = 0 then 0 else 1) hpc3 h103 h03 (by rw [hspn]; exact hal) (by rw [hspn]; exact hsp) (by rw [hspn]; exact h104)
      hacc3 hB3 hj16 hfr hdr hop ho1 ho2 hf64 hd64 hent hf8 hf1 hf2 hbaa3 hb3 hphd)
    obtain ⟨hcpc, hc4, hc5, hc14, hcx, hcdf, hmf, w0, w8, w16, w24, w32, w40, w48⟩ := hq
    rw [hspn] at hc4 hmf w0 w8 w16 w24 w32 w40 w48
    refine ⟨k1 + k2 + k3, c, (hk1.trans hk2).trans hk3, hcpc, hc4, by rw [hc5, h35, hs5], by rw [hc14, h314, hs14],
      by rw [hcx, h3x, hsx], by rw [hcdf, h3df, hsdf], by rw [← hsm]; rw [hspn] at *; exact hmf, ?_⟩
    have hF : (Janus.Contracts.PanicAmd64.frameOf fi ((s1.regs 4).toNat + 8) s1.mem).openAt =
        (if b = 0 then none else some ((s1.regs 4).toNat + fi.frame - o1, (s1.regs 4).toNat + fi.frame - o2)) := by
      simp only [Janus.Contracts.PanicAmd64.frameOf, Janus.Contracts.Panic.frameOf, hod, hbitsAt, hslotsAt, hb]
    by_cases hb0 : b = 0
    · have hF0 : (Janus.Contracts.PanicAmd64.frameOf fi ((s1.regs 4).toNat + 8) s1.mem).openAt = none := by
        rw [hF, if_pos hb0]
      have hph : (if (Janus.Contracts.PanicAmd64.frameOf fi ((s1.regs 4).toNat + 8) s1.mem).openAt.isSome then 1 else 0) = 0 := by
        rw [hF0]; rfl
      rw [hph]
      have w32' : c.mem.readLE ((s1.regs 4).toNat - 96 + 32) 8 = 0 := by rw [w32, if_pos hb0]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hm, fun h => absurd rfl h⟩
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104) 8 = (s1.regs 4).toNat + 8
        rw [e96]; exact w0
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 8) 8 = (s1.regs 4).toNat + 8 + fi.frame
        rw [e96]; exact w8
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 16) 8 = fi.entry + fi.deferreturn
        rw [e96]; exact w16
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 24) 8 = modeCode mode
        rw [e96, ← h7n]; exact w24
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 32) 8 = 0
        rw [e96]; exact w32'
      · intro ba sa h; rw [hF0] at h; cases h
    · have hF1 : (Janus.Contracts.PanicAmd64.frameOf fi ((s1.regs 4).toNat + 8) s1.mem).openAt =
          some ((s1.regs 4).toNat + fi.frame - o1, (s1.regs 4).toNat + fi.frame - o2) := by rw [hF, if_neg hb0]
      have hph : (if (Janus.Contracts.PanicAmd64.frameOf fi ((s1.regs 4).toNat + 8) s1.mem).openAt.isSome then 1 else 0) = 1 := by
        rw [hF1]; rfl
      rw [hph]
      have w32' : c.mem.readLE ((s1.regs 4).toNat - 96 + 32) 8 = 1 := by rw [w32, if_neg hb0]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hm, fun _ => by rw [hF1]; rfl⟩
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104) 8 = (s1.regs 4).toNat + 8
        rw [e96]; exact w0
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 8) 8 = (s1.regs 4).toNat + 8 + fi.frame
        rw [e96]; exact w8
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 16) 8 = fi.entry + fi.deferreturn
        rw [e96]; exact w16
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 24) 8 = modeCode mode
        rw [e96, ← h7n]; exact w24
      · show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 32) 8 = 1
        rw [e96]; exact w32'
      · intro ba sa h
        rw [hF1] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 40) 8 = _ ∧ c.mem.readLE ((s1.regs 4).toNat + 8 - 104 + 48) 8 = _
        rw [e96]; exact ⟨w40, w48⟩

end lf

end Janus.Contracts.PanicSatAmd64
