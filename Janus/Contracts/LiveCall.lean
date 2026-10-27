import Janus.Contracts.Live
import Janus.Contracts.Pool

/-!
# Call-site tools for the live contracts

Small lemmas for the proofs of functions that call live contracts from a stack window `[lo, hi)`
they own (the `sync.Pool` example proofs use them).
-/

namespace Janus.Contracts

open Janus Janus.Arm64 Janus.Contracts

/-- A callee's stack window (arm64) inside the caller's window `[lo, hi)` is apart from the live
set when the caller's window is. -/
theorem LiveSep.callee {L : List (Nat × Nat)} {lo hi : Nat} {s : State} {stack nargs : Nat}
    (h : LiveSep L [(lo, hi)]) (h1 : lo ≤ s.sp.toNat - stack) (h2 : s.sp.toNat + 8 + 8 * nargs ≤ hi) :
    LiveSep L (calleeStack s stack nargs) := by
  intro r hr
  have := h r hr
  simp only [calleeStack, outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- ... and outside the runtime's ranges when the caller's window is. -/
theorem LiveSep.calleeRt {rt : List (Nat × Nat)} {lo hi : Nat} {s : State} {stack nargs : Nat}
    (h : LiveSep [(lo, hi)] rt) (h1 : lo ≤ s.sp.toNat - stack) (h2 : s.sp.toNat + 8 + 8 * nargs ≤ hi) :
    LiveSep (calleeStack s stack nargs) rt := by
  intro r hr
  have := h (lo, hi) (List.mem_singleton_self _)
  simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Outside.of_sub this (by simp <;> omega) (by simp <;> omega)

/-- `dropAll` of a list extended by the dropped ranges, when none of them is in the list. -/
theorem dropAll_append_self {L rs : List (Nat × Nat)} (h : ∀ r ∈ L, r ∉ rs) :
    Janus.Contracts.Pool.dropAll (L ++ rs) rs = L := by
  simp only [Janus.Contracts.Pool.dropAll, List.filter_append]
  have h1 : L.filter (fun r => !rs.contains r) = L := by
    rw [List.filter_eq_self]
    intro r hr
    simpa using h r hr
  have h2 : rs.filter (fun r => !rs.contains r) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r hr
    simp [hr]
  rw [h1, h2, List.append_nil]

/-- A fresh range of positive length is not in the live set. -/
theorem notMem_of_apartAll {L : List (Nat × Nat)} {a n : Nat} (hn : 0 < n) (h : ApartAll a n L) :
    (a, a + n) ∉ L := by
  intro hm
  have := h _ hm
  simp only [Apart] at this
  omega

theorem outside_of_forall {a n : Nat} {ws : List (Nat × Nat)}
    (h : ∀ r ∈ ws, a + n ≤ r.1 ∨ r.2 ≤ a) : Outside a n ws := by
  induction ws with
  | nil => trivial
  | cons r ws ih =>
    obtain ⟨lo, hi⟩ := r
    exact ⟨h _ (List.mem_cons_self ..), ih fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

/-- A byte inside the runtime's ranges is outside a window that is apart from them. -/
theorem outside_of_inRs {rt ws : List (Nat × Nat)} {a : Nat} (h : inRs rt a = true)
    (hws : LiveSep ws rt) : Outside a 1 ws := by
  obtain ⟨q, hq, hq1⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq1
  refine outside_of_forall fun r hr => ?_
  have := MemFrame.outside_mem (hws r hr) hq
  omega

/-- A frame whose ranges are each apart from the runtime's ranges or inside the live set does not
change the bytes of the view. -/
theorem view_bytes_of_frame {rt L ws : List (Nat × Nat)} {m m' : Memory} (h : MemFrame m m' ws)
    (hws : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) rt ∨ InRanges r.1 (r.2 - r.1) L) (a : Nat) :
    (view rt L m').bytes a = (view rt L m).bytes a := by
  simp only [view]
  by_cases hc : ∃ r ∈ ws, r.1 ≤ a ∧ a < r.2
  · obtain ⟨r, hr, h1, h2⟩ := hc
    rcases hws r hr with ho | hin
    · have := inRs_of_outside ho (x := a) h1 (by omega)
      simp [this]
    · have := inRs_of_inRanges hin (x := a) h1 (by omega)
      simp [this]
  · have hout : Outside a 1 ws := outside_of_forall fun r hr => by
      by_cases hh : r.1 ≤ a ∧ a < r.2
      · exact absurd ⟨r, hr, hh.1, hh.2⟩ hc
      · omega
    have := h.readLE a 1 hout
    simp only [Memory.readLE_one] at this
    have e : m'.bytes a = m.bytes a := BitVec.eq_of_toNat_eq this
    simp only [e]

/-- The runtime's invariant survives a frame whose ranges are each apart from `R.rt` or inside
the live set (a function's own stack window; the live objects it writes). -/
theorem RtInv.inv_frame' {R : RtInv} {b g : Nat} {L ws : List (Nat × Nat)} {m m' : Memory}
    (h : MemFrame m m' ws)
    (hws : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt ∨ InRanges r.1 (r.2 - r.1) L)
    (hi : R.inv b L g (view R.rt L m)) : R.inv b L g (view R.rt L m') :=
  R.ext b L g _ _ (view_bytes_of_frame h hws) (fun a n w => h.accessible a n w) hi

/-- ... for a window apart from `R.rt`. -/
theorem RtInv.inv_frame {R : RtInv} {b g : Nat} {L ws : List (Nat × Nat)} {m m' : Memory}
    (h : MemFrame m m' ws) (hws : LiveSep ws R.rt) (hi : R.inv b L g (view R.rt L m)) :
    R.inv b L g (view R.rt L m') :=
  RtInv.inv_frame' h (fun r hr => Or.inl (hws r hr)) hi

/-- A read in the function's window that the callee's window does not cover is unchanged by the
call. -/
theorem keep_read {rt cs : List (Nat × Nat)} {m m' : Memory} {lo hi x k : Nat}
    (hwrt : LiveSep [(lo, hi)] rt) (hfr : MemFrame m m' (rt ++ cs)) (h1 : lo ≤ x) (h2 : x + k ≤ hi)
    (hcs : Outside x k cs) : m'.readLE x k = m.readLE x k :=
  hfr.readLE _ _ (by
    simp only [outside_append]
    exact ⟨Outside.of_sub (hwrt _ (List.mem_singleton_self _)) h1 (by simp only; omega), hcs⟩)

end Janus.Contracts

namespace Janus

/-- A frame that writes outside `L` is a live frame. -/
theorem LiveFrame.of_memFrame {m m' : Janus.Arm64.Memory} {L ws : List (Nat × Nat)} {rs : List (Nat × Nat)}
    (h : MemFrame m m' rs) (ho : ∀ a n, InRanges a n L → Outside a n rs) : LiveFrame m m' L ws :=
  ⟨fun a n hin _ => h.readLE a n (ho a n hin)⟩

/-- A frame widened by more ranges. -/
theorem MemFrame.widen {m m' : Janus.Arm64.Memory} {ws : List (Nat × Nat)} (h : MemFrame m m' ws)
    (ws' : List (Nat × Nat)) : MemFrame m m' (ws' ++ ws) :=
  h.mono fun a n hh => by simp only [outside_append] at hh; exact hh.2

end Janus

namespace Janus.Contracts

open Janus Janus.Arm64 Janus.Contracts

/-- A frame that writes only in `ws`, apart from the live set, keeps the live objects. -/
theorem LiveFrame.of_win {L ws ex : List (Nat × Nat)} {m m' : Memory} (h : MemFrame m m' ws)
    (hws : LiveSep L ws) : LiveFrame m m' L ex :=
  LiveFrame.of_memFrame h fun a n hin => by
    obtain ⟨r, hr, h1, h2⟩ := hin
    exact Outside.of_sub (hws r hr) h1 (by omega)

/-- **The precondition of a live call** (arm64) made from a function that owns the stack window
`[lo, hi)` and keeps `g`'s stack-guard word outside the runtime: the call state `S` has `SP` `fr`
bytes below the function's entry `SP`, has changed memory only in `R.rt` and the window since the
state `s` at which the guard and the window were checked, and the invariant holds for `S.mem`.
Everything the standard preconditions (`CallOK`, `StackRoom`, `LiveAt`) ask for follows. -/
theorem call_pre (R : RtInv) (L : List (Nat × Nat)) (b cost : Nat) (addr : Nat) (args : List Nat)
    {s S : State} {lo hi stack nargs fr : Nat}
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + (stack + fr) < s.sp.toNat)
    (hgo : Outside ((s.regs 28).toNat + 16) 8 ((lo, hi) :: R.rt))
    (hfr : MemFrame s.mem S.mem (R.rt ++ [(lo, hi)])) (hg : S.regs 28 = s.regs 28)
    (hsp : S.sp.toNat + fr = s.sp.toNat) (hal : S.sp.toNat % 16 = 0)
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (h8 : 8 ≤ stack) (hstk : stack ≤ S.sp.toNat)
    (hlo : lo ≤ S.sp.toNat - stack) (hhi : S.sp.toNat + 8 + 8 * nargs ≤ hi) (hhi48 : hi ≤ 2 ^ 48)
    (hacc : s.mem.accessible lo (hi - lo) true = true)
    (hwrt : LiveSep [(lo, hi)] R.rt) (hwL : LiveSep L [(lo, hi)])
    (hok : R.ok addr args) (hinv : R.inv b L (S.regs 28).toNat (view R.rt L S.mem)) (hcost : cost ≤ b) :
    CallOK S stack nargs ∧ StackRoom S stack nargs ∧
      LiveAt R addr args L b cost (S.regs 28).toNat S.mem (calleeStack S stack nargs) := by
  have hgw : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ [(lo, hi)]) := by
    simp only [outside_cons, outside_append, outside_nil, and_true] at hgo ⊢
    exact ⟨hgo.2, hgo.1⟩
  refine ⟨⟨h30a, h30b, hal, hstk, h8, by omega, ?_⟩, ⟨?_, ?_⟩,
    hok, hinv, hcost, LiveSep.callee hwL hlo hhi, LiveSep.calleeRt hwrt hlo hhi⟩
  · rw [hfr.accessible]
    exact Memory.accessible_mono _ hacc (by omega) (by omega)
  · unfold Janus.Spec.GuardOK
    rw [hg]
    refine ⟨hg1, ?_, ?_⟩
    · rw [hfr.accessible]; exact hg2
    · rw [hfr.readLE _ _ hgw]; omega
  · rw [hg]
    simp only [calleeStack, outside_cons, outside_nil, and_true]
    simp only [outside_cons, outside_nil, and_true] at hgo
    omega

/-- A live set outside a window is outside any window inside it. -/
theorem LiveSep.sub_win {L : List (Nat × Nat)} {lo hi lo' hi' : Nat} (h : LiveSep L [(lo, hi)])
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : LiveSep L [(lo', hi')] := fun r hr => by
  have := h r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- A window apart from the runtime is so for the windows inside it. -/
theorem LiveSep.sub_win_rt {rt : List (Nat × Nat)} {lo hi lo' hi' : Nat} (h : LiveSep [(lo, hi)] rt)
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) (h3 : lo' ≤ hi') : LiveSep [(lo', hi')] rt := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  have := h _ (List.mem_singleton_self _)
  simp only at this ⊢
  exact Outside.of_sub this h1 (by omega)

/-- A frame that keeps the live objects of `L'` except in `ws` keeps those of `L ⊆ L'` outright when
`L` is outside `ws`. -/
theorem LiveFrame.of_sep {m m' : Memory} {L L' ws : List (Nat × Nat)} (h : LiveFrame m m' L' ws)
    (hs : LiveSep L ws) (hsub : ∀ r ∈ L, r ∈ L') : LiveFrame m m' L [] :=
  ⟨fun a n hin _ => by
    obtain ⟨r, hr, h1, h2⟩ := hin
    exact h.readLE a n ⟨r, hsub r hr, h1, h2⟩ (Outside.of_sub (hs r hr) h1 (by omega))⟩

/-- A range inside the runtime's ranges that is outside a list is outside any range inside it. -/
theorem outside_of_inRanges_rt {a n : Nat} {rt ex : List (Nat × Nat)} (h : Outside a n rt)
    (hex : ∀ x ∈ ex, InRanges x.1 (x.2 - x.1) rt) : Outside a n ex := by
  apply outside_of_forall
  intro x hx
  obtain ⟨r, hr, h1, h2⟩ := hex x hx
  have := MemFrame.outside_mem h hr
  omega

/-- `call_pre`'s conclusion for a live memory function (`memclrNoHeapPointers`, ...): its
`Mem.EqPre` and `LiveMemAt`. -/
theorem memPre_of {R : RtInv} {S : State} {stack nargs : Nat} {addr : Nat} {args : List Nat}
    {L : List (Nat × Nat)} {b : Nat}
    (h : CallOK S stack nargs ∧ StackRoom S stack nargs ∧
      LiveAt R addr args L b 0 (S.regs 28).toNat S.mem (calleeStack S stack nargs)) :
    Mem.EqPre stack nargs S ∧ LiveMemAt R addr args L b S (calleeStack S stack nargs) :=
  ⟨⟨(Janus.Spec.guardOK_iff _ _).1 h.2.1.1, h.1, h.2.1.2⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end Janus.Contracts
