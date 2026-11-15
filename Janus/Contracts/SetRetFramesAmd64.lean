import Janus.Contracts.MapAmd64
import Janus.Contracts.PanicAmd64
import Janus.Contracts.IfaceAmd64
import Janus.Contracts.MemAmd64
import Janus.Contracts.HashAmd64
import Janus.Contracts.InstrumentCallsAmd64
import Janus.Contracts.Live

/-!
# The return slot and the runtime models (amd64, `janus64_pre_setRet`)

`State.setRet` writes only `[RSP, RSP + 8)`. A precondition that keeps that slot outside a model's private memory
(`Outside RSP 8 X.priv`, which the stack window of every `CallerOK` does) has its `X.Env` / `X.panics` / `X.defers` / ...
facts about the call state preserved by installing the return address: the models' frame laws, at the memory the write
leaves in agreement. `janus64_pre_setRet` uses these as conditional `simp` lemmas (`hl : X.Laws` and the `Outside` fact are
found in the context); the map models' are in `Janus.Contracts.MapAmd64`.
-/

namespace Janus.Contracts.SetRetFramesAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Spec Janus.Spec.Map

theorem agrees_setRet {s : State} {ret : Nat} {rs : List (Nat × Nat)} (h : Outside (s.regs 4).toNat 8 rs) :
    Agrees s.mem (s.setRet ret).mem rs :=
  agrees_writeLE s.mem ret h

theorem mem_env_setRet {M : Janus.Contracts.Mem.MemModel} (hl : M.Laws) {s : State} {ret : Nat} (g : W64)
    (h : Outside (s.regs 4).toNat 8 M.priv) : M.Env (s.setRet ret).mem g = M.Env s.mem g :=
  propext ⟨fun he => hl.env_frame _ _ _ he (agrees_setRet h).symm, fun he => hl.env_frame _ _ _ he (agrees_setRet h)⟩

theorem iface_env_setRet {R : Janus.Spec.Type.IfaceModel} (hl : R.Laws) {s : State} {ret : Nat} (g : W64)
    (h : Outside (s.regs 4).toNat 8 R.priv) : R.Env (s.setRet ret).mem g = R.Env s.mem g :=
  propext ⟨fun he => hl.env_frame _ _ _ he (agrees_setRet h).symm, fun he => hl.env_frame _ _ _ he (agrees_setRet h)⟩

theorem hash_env_setRet {H : Janus.Contracts.Hash.HashModel} (hl : H.Laws) {s : State} {ret : Nat} (g : W64)
    (h : Outside (s.regs 4).toNat 8 H.priv) : H.Env (s.setRet ret).mem g = H.Env s.mem g :=
  propext ⟨fun he => hl.env_frame _ _ _ he (agrees_setRet h).symm, fun he => hl.env_frame _ _ _ he (agrees_setRet h)⟩

theorem rt_env_setRet {E : Janus.Contracts.Instrument.RtEnv} (hl : E.Laws) {s : State} {ret : Nat} (g : W64)
    (h : Outside (s.regs 4).toNat 8 E.priv) : E.Env (s.setRet ret).mem g = E.Env s.mem g :=
  propext ⟨fun he => hl.env_frame _ _ _ he (agrees_setRet h).symm, fun he => hl.env_frame _ _ _ he (agrees_setRet h)⟩

section Panic

variable {P : PanicRuntime} (hl : P.Laws) {s : State} {ret : Nat}
include hl

theorem panic_env_setRet (h : Outside (s.regs 4).toNat 8 P.priv) : P.Env (s.setRet ret).mem = P.Env s.mem :=
  propext ⟨fun he => hl.env_frame _ _ he (agrees_setRet h).symm, fun he => hl.env_frame _ _ he (agrees_setRet h)⟩

theorem panic_panics_setRet (g : Nat) (h : Outside (s.regs 4).toNat 8 P.priv) :
    P.panics (s.setRet ret).mem g = P.panics s.mem g := hl.panics_frame _ _ g (agrees_setRet h)

theorem panic_defers_setRet (g : Nat) (h : Outside (s.regs 4).toNat 8 P.priv) :
    P.defers (s.setRet ret).mem g = P.defers s.mem g := hl.defers_frame _ _ g (agrees_setRet h)

theorem panic_saved_setRet (g : Nat) (h : Outside (s.regs 4).toNat 8 P.priv) :
    P.saved (s.setRet ret).mem g = P.saved s.mem g := hl.saved_frame _ _ g (agrees_setRet h)

theorem panic_rp_setRet (g : Nat) (h : Outside (s.regs 4).toNat 8 P.priv) :
    P.rp (s.setRet ret).mem g = P.rp s.mem g := hl.rp_frame _ _ g (agrees_setRet h)

theorem panic_room_setRet (g : Nat) (h : Outside (s.regs 4).toNat 8 P.priv) :
    P.room (s.setRet ret).mem g = P.room s.mem g := hl.room_frame _ _ g (agrees_setRet h)

theorem panic_calm_setRet (g : Nat) (h : Outside (s.regs 4).toNat 8 P.priv) :
    P.Calm (s.setRet ret).mem g = P.Calm s.mem g := by
  unfold PanicRuntime.Calm; rw [hl.panics_frame _ _ g (agrees_setRet h)]

end Panic

/-- A live-set separation from a window that covers the return slot puts the slot outside the separated ranges
(`janus_outside_slot`, with `LiveSep [win] rt`). -/
theorem liveSep_outside {L win : List (Nat × Nat)} (h : Janus.Contracts.LiveSep L win) {lo hi a n : Nat}
    (hm : (lo, hi) ∈ L) (h1 : lo ≤ a) (h2 : a + n ≤ hi) : Outside a n win :=
  Janus.Outside.of_sub (h _ hm) h1 (by omega)

end Janus.Contracts.SetRetFramesAmd64
