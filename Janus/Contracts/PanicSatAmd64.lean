import Janus.Contracts.PanicAmd64
import Janus.Contracts.PanicSatDecode

/-!
# The panic/defer/recover contracts are satisfiable (amd64)

Model code for the panic runtime `PanicModel.P0` (one segment, the "engine", at `E = 0x300000`,
with an entry for each runtime function), proved to meet every amd64 panic contract of
`Janus.Contracts.PanicAmd64` in **every** program that contains the engine (`EngineAt`): a contract
address holds a five-byte stub (`jmp rel32`) jumping to the engine. The engine is the x86-64 twin
of the arm64 one (`PanicSat`); its source is `docs/model/panic_model_amd64.s`. The `Witness`
sections of the examples instantiate this for their own linked program.
-/

namespace Janus.Contracts.PanicSatAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.PanicAmd64 Janus.Contracts.PanicModel

/-! ## The engine -/

-- the amd64 types (the enclosing namespace `Janus` would otherwise resolve these to the arm64 ones)
abbrev Program := Janus.Amd64.Program
abbrev State := Janus.Amd64.State
abbrev Segment := Janus.Amd64.Segment

def engineCode : List Nat :=
  [0x41, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x4d, 0x8b, 0x08, 0x4d, 0x8d, 0x90, 0x00, 0x01, 0x00, 0x00,
   0x4d, 0x89, 0xcb, 0x49, 0xc1, 0xe3, 0x05, 0x4d, 0x01, 0xda, 0x49, 0x89, 0x02, 0x49, 0x89, 0x5a,
   0x08, 0x4c, 0x8d, 0x5c, 0x24, 0x08, 0x4d, 0x89, 0x5a, 0x10, 0x49, 0xc7, 0x42, 0x18, 0x00, 0x00,
   0x00, 0x00, 0x49, 0x83, 0xc1, 0x01, 0x4d, 0x89, 0x08, 0x31, 0xff, 0xe9, 0xf0, 0x01, 0x00, 0x00,
   0x41, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x4d, 0x8b, 0x08, 0x4d, 0x8d, 0x90, 0x00, 0x01, 0x00, 0x00,
   0x4d, 0x89, 0xcb, 0x49, 0xc1, 0xe3, 0x05, 0x4d, 0x01, 0xda, 0x49, 0xc7, 0x02, 0x00, 0x00, 0x00,
   0x00, 0x49, 0xc7, 0x42, 0x08, 0x00, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0x5c, 0x24, 0x08, 0x4d, 0x89,
   0x5a, 0x10, 0x49, 0xc7, 0x42, 0x18, 0x01, 0x00, 0x00, 0x00, 0x49, 0x83, 0xc1, 0x01, 0x4d, 0x89,
   0x08, 0xbf, 0x01, 0x00, 0x00, 0x00, 0xe9, 0xa5, 0x01, 0x00, 0x00, 0x41, 0xb8, 0x00, 0x00, 0x01,
   0x00, 0x4c, 0x8d, 0x5c, 0x24, 0x08, 0x49, 0x8b, 0x70, 0x10, 0x4d, 0x8b, 0x60, 0x18, 0x4d, 0x8b,
   0x68, 0x20, 0x49, 0xc7, 0x40, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xec, 0x60, 0x4c, 0x89,
   0x1c, 0x24, 0x4c, 0x89, 0x5c, 0x24, 0x08, 0x48, 0xc7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00,
   0x48, 0xc7, 0x44, 0x24, 0x18, 0x02, 0x00, 0x00, 0x00, 0x48, 0x89, 0x74, 0x24, 0x20, 0x4c, 0x89,
   0x64, 0x24, 0x28, 0x4c, 0x89, 0x6c, 0x24, 0x30, 0x48, 0xc7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00,
   0x00, 0xe9, 0xff, 0x01, 0x00, 0x00, 0x41, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x4d, 0x8b, 0x08, 0x4d,
   0x85, 0xc9, 0x74, 0x3e, 0x49, 0x83, 0xe9, 0x01, 0x4d, 0x8d, 0x90, 0x00, 0x01, 0x00, 0x00, 0x4d,
   0x89, 0xcb, 0x49, 0xc1, 0xe3, 0x05, 0x4d, 0x01, 0xda, 0x49, 0x8b, 0x42, 0x18, 0x83, 0xe0, 0x03,
   0x75, 0x20, 0x48, 0x8b, 0x4d, 0x08, 0x48, 0x8d, 0x15, 0x6c, 0x02, 0x00, 0x00, 0x48, 0x39, 0xd1,
   0x75, 0x10, 0x49, 0xc7, 0x42, 0x18, 0x02, 0x00, 0x00, 0x00, 0x49, 0x8b, 0x02, 0x49, 0x8b, 0x5a,
   0x08, 0xc3, 0x31, 0xc0, 0x31, 0xdb, 0xc3, 0x41, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x4d, 0x8b, 0x48,
   0x08, 0x4d, 0x6b, 0xd1, 0x60, 0x4f, 0x8d, 0x94, 0x02, 0x00, 0x02, 0x00, 0x00, 0x4c, 0x8d, 0x5c,
   0x24, 0x08, 0x4d, 0x89, 0x1a, 0x49, 0xc7, 0x42, 0x08, 0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x42,
   0x10, 0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x42, 0x18, 0x01, 0x00, 0x00, 0x00, 0x49, 0x89, 0x42,
   0x20, 0x49, 0x83, 0xc1, 0x01, 0x4d, 0x89, 0x48, 0x08, 0xc3, 0x48, 0x8b, 0x40, 0x18, 0x41, 0xb8,
   0x00, 0x00, 0x01, 0x00, 0x4d, 0x8b, 0x48, 0x08, 0x4d, 0x6b, 0xd1, 0x60, 0x4f, 0x8d, 0x94, 0x02,
   0x00, 0x02, 0x00, 0x00, 0x4c, 0x8d, 0x5c, 0x24, 0x08, 0x4d, 0x89, 0x1a, 0x49, 0xc7, 0x42, 0x08,
   0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x42, 0x10, 0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x42, 0x18,
   0x01, 0x00, 0x00, 0x00, 0x49, 0x89, 0x42, 0x20, 0x49, 0x83, 0xc1, 0x01, 0x4d, 0x89, 0x48, 0x08,
   0xc3, 0x41, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x4d, 0x8b, 0x48, 0x08, 0x4d, 0x6b, 0xd1, 0x60, 0x4f,
   0x8d, 0x94, 0x02, 0x00, 0x02, 0x00, 0x00, 0x4c, 0x8d, 0x5c, 0x24, 0x08, 0x4d, 0x89, 0x1a, 0x4d,
   0x89, 0x52, 0x08, 0x49, 0xc7, 0x42, 0x10, 0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x42, 0x18, 0x00,
   0x00, 0x00, 0x00, 0x49, 0x83, 0xc1, 0x01, 0x4d, 0x89, 0x48, 0x08, 0xb8, 0x01, 0x00, 0x00, 0x00,
   0x4c, 0x89, 0xd3, 0xc3, 0x41, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x4d, 0x8b, 0x48, 0x08, 0x49, 0x83,
   0xe9, 0x01, 0x4d, 0x6b, 0xd1, 0x60, 0x4f, 0x8d, 0x94, 0x02, 0x00, 0x02, 0x00, 0x00, 0x4d, 0x8b,
   0x5a, 0x18, 0x4b, 0x89, 0x44, 0xda, 0x20, 0x49, 0x83, 0xc3, 0x01, 0x4d, 0x89, 0x5a, 0x18, 0xc3,
   0x48, 0x8b, 0x0c, 0x24, 0x41, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x4d, 0x8b, 0x48, 0x28, 0x4d, 0x8d,
   0x90, 0x00, 0x05, 0x00, 0x00, 0x4d, 0x85, 0xc9, 0x74, 0x1e, 0x49, 0x8b, 0x02, 0x48, 0x39, 0xc1,
   0x72, 0x0c, 0x49, 0x8b, 0x52, 0x08, 0x48, 0x01, 0xc2, 0x48, 0x39, 0xd1, 0x72, 0x0c, 0x49, 0x83,
   0xc2, 0x38, 0x49, 0x83, 0xe9, 0x01, 0xeb, 0xdd, 0xeb, 0xfe, 0x4c, 0x8d, 0x5c, 0x24, 0x08, 0x49,
   0x8b, 0x52, 0x10, 0x4c, 0x01, 0xda, 0x49, 0x8b, 0x72, 0x18, 0x48, 0x01, 0xc6, 0x4d, 0x8b, 0x4a,
   0x20, 0x45, 0x31, 0xe4, 0x45, 0x31, 0xed, 0x45, 0x31, 0xff, 0x4d, 0x85, 0xc9, 0x74, 0x27, 0x48,
   0x8d, 0x42, 0xf8, 0x49, 0x8b, 0x4a, 0x28, 0x49, 0x89, 0xc5, 0x49, 0x29, 0xcd, 0x49, 0x8b, 0x4a,
   0x30, 0x49, 0x89, 0xc7, 0x49, 0x29, 0xcf, 0x41, 0x0f, 0xb6, 0x4d, 0x00, 0x85, 0xc9, 0x74, 0x06,
   0x41, 0xbc, 0x01, 0x00, 0x00, 0x00, 0x48, 0x83, 0xec, 0x60, 0x4c, 0x89, 0x1c, 0x24, 0x48, 0x89,
   0x54, 0x24, 0x08, 0x48, 0x89, 0x74, 0x24, 0x10, 0x48, 0x89, 0x7c, 0x24, 0x18, 0x4c, 0x89, 0x64,
   0x24, 0x20, 0x4c, 0x89, 0x6c, 0x24, 0x28, 0x4c, 0x89, 0x7c, 0x24, 0x30, 0x48, 0xc7, 0x44, 0x24,
   0x38, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x85, 0xc0, 0x74, 0x2a, 0x48,
   0x8b, 0x4c, 0x24, 0x28, 0x0f, 0xb6, 0x11, 0x85, 0xd2, 0x74, 0x13, 0x0f, 0xbd, 0xf2, 0x0f, 0xb3,
   0xf2, 0x88, 0x11, 0x4c, 0x8b, 0x44, 0x24, 0x30, 0x49, 0x8b, 0x14, 0xf0, 0xeb, 0x75, 0x48, 0xc7,
   0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0xeb, 0xcc, 0x41, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x4d,
   0x8b, 0x48, 0x08, 0x4d, 0x85, 0xc9, 0x0f, 0x84, 0x10, 0x01, 0x00, 0x00, 0x4d, 0x8d, 0x51, 0xff,
   0x4d, 0x6b, 0xd2, 0x60, 0x4f, 0x8d, 0x94, 0x02, 0x00, 0x02, 0x00, 0x00, 0x49, 0x8b, 0x02, 0x48,
   0x3b, 0x04, 0x24, 0x0f, 0x85, 0xf3, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x42, 0x10, 0x01, 0x00, 0x00,
   0x00, 0x49, 0x8b, 0x42, 0x18, 0x48, 0x85, 0xc0, 0x74, 0x1c, 0x48, 0x83, 0xe8, 0x01, 0x49, 0x89,
   0x42, 0x18, 0x49, 0x8b, 0x54, 0xc2, 0x20, 0x48, 0x85, 0xc0, 0x75, 0x17, 0x49, 0x83, 0xe9, 0x01,
   0x4d, 0x89, 0x48, 0x08, 0xeb, 0x0d, 0x49, 0x83, 0xe9, 0x01, 0x4d, 0x89, 0x48, 0x08, 0xe9, 0x62,
   0xff, 0xff, 0xff, 0x4c, 0x8b, 0x0a, 0x41, 0xff, 0xd1, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x85,
   0xc0, 0x0f, 0x85, 0x4e, 0xff, 0xff, 0xff, 0x41, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x4d, 0x8b, 0x08,
   0x49, 0x83, 0xe9, 0x01, 0x4d, 0x8d, 0x90, 0x00, 0x01, 0x00, 0x00, 0x4d, 0x89, 0xcb, 0x49, 0xc1,
   0xe3, 0x05, 0x4d, 0x01, 0xda, 0x49, 0x8b, 0x42, 0x18, 0xa9, 0x02, 0x00, 0x00, 0x00, 0x0f, 0x84,
   0x21, 0xff, 0xff, 0xff, 0x48, 0x8b, 0x34, 0x24, 0x4d, 0x8b, 0x08, 0x4d, 0x85, 0xc9, 0x74, 0x23,
   0x49, 0x83, 0xe9, 0x01, 0x4d, 0x8d, 0x90, 0x00, 0x01, 0x00, 0x00, 0x4d, 0x89, 0xcb, 0x49, 0xc1,
   0xe3, 0x05, 0x4d, 0x01, 0xda, 0x49, 0x8b, 0x42, 0x10, 0x48, 0x39, 0xf0, 0x77, 0x05, 0x4d, 0x89,
   0x08, 0xeb, 0xd5, 0x49, 0xc7, 0x40, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x44, 0x24, 0x20,
   0x48, 0x85, 0xc0, 0x74, 0x21, 0x48, 0x8b, 0x4c, 0x24, 0x28, 0x0f, 0xb6, 0x11, 0x85, 0xd2, 0x74,
   0x15, 0x49, 0xc7, 0x40, 0x10, 0x01, 0x00, 0x00, 0x00, 0x49, 0x89, 0x48, 0x18, 0x48, 0x8b, 0x54,
   0x24, 0x30, 0x49, 0x89, 0x50, 0x20, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x54, 0x24, 0x08,
   0x48, 0x83, 0xea, 0x08, 0x48, 0x89, 0xf4, 0x48, 0x89, 0xd5, 0xff, 0xe0, 0x48, 0x8b, 0x44, 0x24,
   0x18, 0x48, 0x83, 0xf8, 0x02, 0x74, 0x11, 0x48, 0x8b, 0x4c, 0x24, 0x08, 0x48, 0x89, 0xcc, 0x48,
   0x8d, 0x05, 0x33, 0xff, 0xff, 0xff, 0xff, 0xe0, 0x48, 0x83, 0xc4, 0x60, 0xc3]

abbrev E : Nat := 0x300000
/-- Entry points (offsets in `docs/model/panic_model_amd64.s`). -/
abbrev eGopanic : Nat := E
abbrev eGoexit : Nat := E + 0x40
abbrev eDeferreturn : Nat := E + 0x8b
abbrev eGorecover : Nat := E + 0xe6
abbrev eDeferproc : Nat := E + 0x137
abbrev eDeferprocStack : Nat := E + 0x17a
abbrev eDeferrangefunc : Nat := E + 0x1c1
abbrev eDeferprocat : Nat := E + 0x204
abbrev eLookup : Nat := E + 0x230
abbrev eLH : Nat := E + 0x2e5
abbrev eCall : Nat := E + 0x383
abbrev eFin : Nat := E + 0x43c
/-- The return point of every deferred call the model makes. -/
abbrev RPa : Nat := E + 0x389

def engineSeg : Segment := { name := "panic-model", base := E, bytes := engineCode }

/-- The engine alone, as a closed program for the symbolic executor. -/
def qE : Program := { segments := [engineSeg], stubs := [], exitAddr := 0 }

/-- `p` contains the engine: every byte window of it is fetched, with no stub and no exit there. -/
def EngineAt (p : Program) : Prop :=
  ∀ pc w, qE.fetch pc = some w → p.fetch pc = some w ∧ p.stubAt pc = none ∧ pc ≠ p.exitAddr

theorem steps_transfer {p : Program} (hp : EngineAt p) {s s' : State} {k : Nat}
    (h : Janus.Amd64.Program.Steps qE s k s') : Janus.Amd64.Program.Steps p s k s' := by
  induction h with
  | refl => exact .refl _
  | step _ _ hf hst _ ih =>
    obtain ⟨h1, h2, h3⟩ := hp _ _ hf
    exact .step h3 h2 h1 hst ih

theorem reachesRet_transfer {p : Program} (hp : EngineAt p) {ret : W64} {s : State}
    {Q : State → Prop} (h : ReachesRet qE ret s Q) : ReachesRet p ret s Q := by
  obtain ⟨k, s', hk, h1, h2⟩ := h
  exact ⟨k, s', steps_transfer hp hk, h1, h2⟩

/-- The stub placed at a contract address `A` for the engine entry `tgt`: `jmp rel32`. -/
def stubCode (A tgt : Nat) : List Nat :=
  let rel := (tgt + 2 ^ 32 - (A + 5)) % 2 ^ 32
  [0xe9, rel % 256, rel / 256 % 256, rel / 65536 % 256, rel / 16777216 % 256]

/-- The model `U`: a state at the deferred calls' return point with `RSP = b` and `R14 = g`. -/
def U0 (u : State) (g b : Nat) : Prop :=
  u.rip = BitVec.ofNat 64 RPa ∧ u.regs 4 = BitVec.ofNat 64 b ∧ u.regs 14 = BitVec.ofNat 64 g

/-- A model routine's return as `PanicRet`. -/
theorem panicRet_of (P : PanicRuntime) (nargs : Nat) (s s' : State) (hrip : s'.rip = retAddrOf s)
    (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hmx : s'.mxcsr = s.mxcsr)
    (hfr : MemFrame s.mem s'.mem (P.priv ++ MapAmd64.calleeStack s P.depth nargs)) (henv : P.Env s'.mem) :
    PanicRet P nargs s s' := by
  refine ⟨s'.regs, s'.xmm, s'.ymmHi, s'.flags, s'.mem, ?_, hfr, henv⟩
  obtain ⟨r, rip, fl, x, m, yh, fsb, df, mx⟩ := s'
  dsimp only at hrip h4 h5 h14 hx hfs hdf hmx ⊢
  subst hrip hfs hdf hmx
  congr 1
  · funext i
    by_cases h : i = 4
    · subst h; simp [MapAmd64.keepABI_apply, h4]
    · by_cases h' : i = 5 ∨ i = 14
      · rcases h' with rfl | rfl <;> simp [MapAmd64.keepABI_apply, h5, h14]
      · simp [MapAmd64.keepABI_apply, h, h']
  · funext i
    by_cases h : i = 15
    · subst h; simp [MapAmd64.keepX15_apply, hx]
    · simp [MapAmd64.keepX15_apply, h]

theorem room0_pos' {m : Memory} (h : 0 < room0 m) : npan m < 8 ∧ ndef m < 8 ∧ 0 < capMin m (min (ndef m) 8) := by
  unfold room0 at h; omega

set_option maxHeartbeats 0 in
theorem deferproc_run {p : Program} (hp : EngineAt p) (T : List FuncInfo) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 eDeferproc) (hpre : PanicAmd64.PanicPre (P0 T RPa) 1 s) (hroom : 0 < room0 s.mem) :
    ReachesRet p (retAddrOf s) s (fun s' => PanicAmd64.PanicRet (P0 T RPa) 1 s s' ∧
      defers0 s'.mem = { sp := fspOf s, fns := [(s.regs 0).toNat] } :: defers0 s.mem ∧
      Panic.KeepsBut (P0 T RPa) (gOf s) 1 s.mem s'.mem) := by
  apply reachesRet_transfer hp
  obtain ⟨henv, -, hal, hd, h8, hwin, hx, hdf, hra, hout⟩ := hpre
  rw [P0_env] at henv
  have henv' := henv
  unfold Env0 at henv'
  obtain ⟨hB, hnp, hnd, hrec, htab⟩ := henv'
  obtain ⟨-, hnd8, -⟩ := room0_pos' hroom
  have hnd : s.mem.readLE 65544 8 < 8 := hnd8
  have hmul : (BitVec.ofNat 64 (s.mem.readLE 65544 8) * 96#64).toNat = s.mem.readLE 65544 8 * 96 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := s.mem.readLE 65544 8) (by omega)]; omega
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  simp only [P0_priv, P0_depth, outside_cons, outside_nil, and_true, B] at hout hd h8 hwin
  janus64_run [hmul]
  generalize hk : s.mem.readLE 65544 8 = k at *
  have hk' : ndef s.mem = k := hk
  refine ⟨panicRet_of _ 1 s _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) (by rfl) (by simp [hdf]) (by rfl)
    ?_ ?_, ?_, ?_⟩
  · rw [P0_priv, P0_depth]; simp only [B, MapAmd64.calleeStack, List.cons_append, List.nil_append]; janus_frame
  · rw [P0_env]; unfold Env0; dsimp only
    refine ⟨by simpa using hB, ?_, ?_, fun i hi => ?_, ?_⟩
    · simp only [npan, rd, B]; model_simp; exact hnp
    · simp only [ndef, rd, B]; model_simp; omega
    · simp only [ndef, rd, B, recN, recTok, recConv, recAt] at hi ⊢
      model_simp at hi
      rw [Nat.mod_eq_of_lt (by omega)] at hi
      by_cases hik : i = k
      · subst hik; model_simp; omega
      · have hik' : i < k := by omega
        have := hrec i (by rw [hk']; omega)
        simp only [recN, recTok, recConv, recAt, rd, B] at this
        model_simp; exact this
    · repeat' first | apply tableOK_w | exact htab
      all_goals (simp only [tabAt, B, Nat.reduceAdd, Nat.reduceMul]; omega)
  · rw [defers0_eq, defers0_eq, hk']
    try simp only [ndef, rd, B]
    try model_simp
    rw [Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), recList_succ]
    try model_simp
    unfold decRec
    simp only [recTok, recConv, recN, recSp, rd, recAt, B]
    try model_simp
    simp only [true_or, ite_true, show min 1 8 = 1 from rfl, recFns_succ, recFn, rd, recAt, B,
      show PanicModel.recFns _ k 0 = [] from rfl]
    try model_simp
    simp only [Nat.mod_eq_of_lt (BitVec.isLt _), List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    have hm : (BitVec.toNat (s.regs 4) + 8) % 18446744073709551616 = BitVec.toNat (s.regs 4) + 8 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hm]
  · refine ⟨?_, ?_, rfl, ?_⟩
    · rw [P0_panics, P0_panics, panics0_eq, panics0_eq]; simp only [npan, rd, B]; model_simp
    · rw [P0_saved, P0_saved, saved0_eq, saved0_eq]; simp only [rd, B]; model_simp
    · rw [P0_room, P0_room, room0_eq, room0_eq, hk']; simp only [npan, ndef, rd, B]
      model_simp
      rw [Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega : k + 1 ≤ 8), Nat.min_eq_left (by omega : k ≤ 8),
        capMin_succ]
      model_simp
      simp only [recN, rd, recAt, B]
      model_simp
      omega

set_option maxHeartbeats 0 in
theorem deferprocStack_run {p : Program} (hp : EngineAt p) (T : List FuncInfo) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 eDeferprocStack) (hpre : PanicAmd64.PanicPre (P0 T RPa) 1 s) (hroom : 0 < room0 s.mem)
    (hd : (s.regs 0).toNat + 48 ≤ 2 ^ 48) (hda : s.mem.accessible (s.regs 0).toNat 48 true = true)
    (hdo : Outside (s.regs 0).toNat 48 (P0 T RPa).priv) :
    ReachesRet p (retAddrOf s) s (fun s' => PanicAmd64.PanicRet (P0 T RPa) 1 s s' ∧
      defers0 s'.mem = { sp := fspOf s, fns := [s.mem.readLE ((s.regs 0).toNat + 24) 8] } :: defers0 s.mem ∧
      Panic.KeepsBut (P0 T RPa) (gOf s) 1 s.mem s'.mem) := by
  apply reachesRet_transfer hp
  obtain ⟨henv, -, hal, hd, h8, hwin, hx, hdf, hra, hout⟩ := hpre
  rw [P0_env] at henv
  have henv' := henv
  unfold Env0 at henv'
  obtain ⟨hB, hnp, hnd, hrec, htab⟩ := henv'
  obtain ⟨-, hnd8, -⟩ := room0_pos' hroom
  have hnd : s.mem.readLE 65544 8 < 8 := hnd8
  have hmul : (BitVec.ofNat 64 (s.mem.readLE 65544 8) * 96#64).toNat = s.mem.readLE 65544 8 * 96 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := s.mem.readLE 65544 8) (by omega)]; omega
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  have hdr : s.mem.accessible ((s.regs 0).toNat + 24) 8 false = true :=
    Janus.Contracts.IfaceModel.acc_read_of_write (Janus.Arm64.Memory.accessible_mono _ hda (by omega) (by omega))
  simp only [P0_priv, P0_depth, outside_cons, outside_nil, and_true, B] at hout hd h8 hwin
  janus64_run [hmul]
  generalize hk : s.mem.readLE 65544 8 = k at *
  have hk' : ndef s.mem = k := hk
  refine ⟨panicRet_of _ 1 s _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) (by rfl) (by simp [hdf]) (by rfl)
    ?_ ?_, ?_, ?_⟩
  · rw [P0_priv, P0_depth]; simp only [B, MapAmd64.calleeStack, List.cons_append, List.nil_append]; janus_frame
  · rw [P0_env]; unfold Env0; dsimp only
    refine ⟨by simpa using hB, ?_, ?_, fun i hi => ?_, ?_⟩
    · simp only [npan, rd, B]; model_simp; exact hnp
    · simp only [ndef, rd, B]; model_simp; omega
    · simp only [ndef, rd, B, recN, recTok, recConv, recAt] at hi ⊢
      model_simp at hi
      rw [Nat.mod_eq_of_lt (by omega)] at hi
      by_cases hik : i = k
      · subst hik; model_simp; omega
      · have hik' : i < k := by omega
        have := hrec i (by rw [hk']; omega)
        simp only [recN, recTok, recConv, recAt, rd, B] at this
        model_simp; exact this
    · repeat' first | apply tableOK_w | exact htab
      all_goals (simp only [tabAt, B, Nat.reduceAdd, Nat.reduceMul]; omega)
  · rw [defers0_eq, defers0_eq, hk']
    try simp only [ndef, rd, B]
    try model_simp
    rw [Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), recList_succ]
    try model_simp
    unfold decRec
    simp only [recTok, recConv, recN, recSp, rd, recAt, B]
    try model_simp
    simp only [true_or, ite_true, show min 1 8 = 1 from rfl, recFns_succ, recFn, rd, recAt, B,
      show PanicModel.recFns _ k 0 = [] from rfl]
    try model_simp
    simp only [Nat.mod_eq_of_lt (BitVec.isLt _), List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    have hm : (BitVec.toNat (s.regs 4) + 8) % 18446744073709551616 = BitVec.toNat (s.regs 4) + 8 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hm, Nat.mod_eq_of_lt (lt_of_lt_of_eq (Janus.Arm64.Memory.readLE_lt _ _ 8) (by decide))]
  · refine ⟨?_, ?_, rfl, ?_⟩
    · rw [P0_panics, P0_panics, panics0_eq, panics0_eq]; simp only [npan, rd, B]; model_simp
    · rw [P0_saved, P0_saved, saved0_eq, saved0_eq]; simp only [rd, B]; model_simp
    · rw [P0_room, P0_room, room0_eq, room0_eq, hk']; simp only [npan, ndef, rd, B]
      model_simp
      rw [Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega : k + 1 ≤ 8), Nat.min_eq_left (by omega : k ≤ 8),
        capMin_succ]
      model_simp
      simp only [recN, rd, recAt, B]
      model_simp
      omega

set_option maxHeartbeats 0 in
theorem deferrangefunc_run {p : Program} (hp : EngineAt p) (T : List FuncInfo) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 eDeferrangefunc) (hpre : PanicAmd64.PanicPre (P0 T RPa) 0 s)
    (hroom : 0 < room0 s.mem) :
    ReachesRet p (retAddrOf s) s (fun s' => PanicAmd64.PanicRet (P0 T RPa) 0 s s' ∧ (s'.regs 0).toNat ≠ 0 ∧
      defers0 s'.mem = { sp := fspOf s, fns := [], token := some (s'.regs 3).toNat } :: defers0 s.mem ∧
      Panic.KeepsBut (P0 T RPa) (gOf s) 1 s.mem s'.mem) := by
  apply reachesRet_transfer hp
  obtain ⟨henv, -, hal, hd, h8, hwin, hx, hdf, hra, hout⟩ := hpre
  rw [P0_env] at henv
  have henv' := henv
  unfold Env0 at henv'
  obtain ⟨hB, hnp, hnd, hrec, htab⟩ := henv'
  obtain ⟨-, hnd8, -⟩ := room0_pos' hroom
  have hnd : s.mem.readLE 65544 8 < 8 := hnd8
  have hmul : (BitVec.ofNat 64 (s.mem.readLE 65544 8) * 96#64).toNat = s.mem.readLE 65544 8 * 96 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := s.mem.readLE 65544 8) (by omega)]; omega
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  simp only [P0_priv, P0_depth, outside_cons, outside_nil, and_true, B] at hout hd h8 hwin
  janus64_run [hmul]
  generalize hk : s.mem.readLE 65544 8 = k at *
  have hk' : ndef s.mem = k := hk
  refine ⟨panicRet_of _ 0 s _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) (by rfl)
    (by simp [hdf]) (by rfl) ?_ ?_, ?_, ?_⟩
  · rw [P0_priv, P0_depth]; simp only [B, MapAmd64.calleeStack, List.cons_append, List.nil_append]; janus_frame
  · rw [P0_env]; unfold Env0; dsimp only
    refine ⟨by simpa using hB, ?_, ?_, fun i hi => ?_, ?_⟩
    · simp only [npan, rd, B]; model_simp; exact hnp
    · simp only [ndef, rd, B]; model_simp; omega
    · simp only [ndef, rd, B, recN, recTok, recConv, recAt] at hi ⊢
      model_simp at hi
      rw [Nat.mod_eq_of_lt (by omega)] at hi
      by_cases hik : i = k
      · subst hik; model_simp; omega
      · have hik' : i < k := by omega
        have := hrec i (by rw [hk']; omega)
        simp only [recN, recTok, recConv, recAt, rd, B] at this
        model_simp; exact this
    · repeat' first | apply tableOK_w | exact htab
      all_goals (simp only [tabAt, B, Nat.reduceAdd, Nat.reduceMul]; omega)
  · rw [defers0_eq, defers0_eq, hk']
    try simp only [ndef, rd, B]
    try model_simp
    rw [Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), recList_succ]
    try model_simp
    unfold decRec
    simp only [recTok, recConv, recN, recSp, rd, recAt, B]
    try model_simp
    have hne : k * 96 + 66048 ≠ 0 := by omega
    simp only [hne, false_or, ne_eq, not_true_eq_false, or_false, ite_false, show min 0 8 = 0 from rfl,
      show PanicModel.recFns _ k 0 = [] from rfl, Nat.mod_eq_of_lt (BitVec.isLt _), List.cons_append,
      List.nil_append]
    have hm : (k * 96 + 66048) % 18446744073709551616 = k * 96 + 66048 := Nat.mod_eq_of_lt (by omega)
    have hm2 : (BitVec.toNat (s.regs 4) + 8) % 18446744073709551616 = BitVec.toNat (s.regs 4) + 8 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hm, hm2, if_neg hne]
    rfl
  · refine ⟨?_, ?_, rfl, ?_⟩
    · rw [P0_panics, P0_panics, panics0_eq, panics0_eq]; simp only [npan, rd, B]; model_simp
    · rw [P0_saved, P0_saved, saved0_eq, saved0_eq]; simp only [rd, B]; model_simp
    · rw [P0_room, P0_room, room0_eq, room0_eq, hk']; simp only [npan, ndef, rd, B]
      model_simp
      rw [Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega : k + 1 ≤ 8), Nat.min_eq_left (by omega : k ≤ 8),
        capMin_succ]
      model_simp
      simp only [recN, rd, recAt, B]
      model_simp
      omega

/-- The top record of a chain that starts with a range-over-func record is a raw record with a
token and no converted flag. -/
theorem top_group {T : List FuncInfo} {m : Memory} (henv : Env0 T m) {r : DeferRec} {rest : List DeferRec}
    {t : Nat} (h : defers0 m = r :: rest) (ht : r.token = some t) :
    ∃ j, ndef m = j + 1 ∧ recTok m j ≠ 0 ∧ recConv m j = 0 ∧
      r = { sp := recSp m j, fns := recFns m j (min (recN m j) 8), token := some (recTok m j) } ∧
      rest = recList m j := by
  unfold Env0 at henv
  obtain ⟨-, -, hnd, hrec, -⟩ := henv
  rw [defers0_eq] at h
  cases hk : ndef m with
  | zero => rw [hk] at h; simp [recList] at h
  | succ j =>
    rw [hk, Nat.min_eq_left (by omega), recList_succ] at h
    have hj := hrec j (by omega)
    unfold decRec at h
    split at h
    · rename_i hc
      have h1 := hj.2 hc
      obtain ⟨n, hn⟩ : ∃ n, min (recN m j) 8 = n + 1 := ⟨min (recN m j) 8 - 1, by omega⟩
      rw [hn, recFns_succ] at h
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      rw [← h.1] at ht; simp at ht
    · rename_i hc
      simp only [not_or, ne_eq, Decidable.not_not] at hc
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact ⟨j, rfl, hc.1, hc.2, h.1.symm, h.2.symm⟩

set_option maxHeartbeats 0 in
theorem deferprocat_run {p : Program} (hp : EngineAt p) (T : List FuncInfo) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 eDeferprocat) (hpre : PanicAmd64.PanicPre (P0 T RPa) 2 s) (hroom : 0 < room0 s.mem)
    (htop : ∃ r rest, defers0 s.mem = r :: rest ∧ r.token = some (s.regs 1).toNat) :
    ReachesRet p (retAddrOf s) s (fun s' => PanicAmd64.PanicRet (P0 T RPa) 2 s s' ∧
      (∀ r rest, defers0 s.mem = r :: rest →
        defers0 s'.mem = { r with fns := (s.regs 0).toNat :: r.fns } :: rest) ∧
      Panic.KeepsBut (P0 T RPa) (gOf s) 1 s.mem s'.mem) := by
  apply reachesRet_transfer hp
  obtain ⟨henv, -, hal, hd, h8, hwin, hx, hdf, hra, hout⟩ := hpre
  rw [P0_env] at henv
  obtain ⟨r, rest, hdr, hrt⟩ := htop
  obtain ⟨j, hj, htok, hconv, hr, hrest⟩ := top_group henv hdr hrt
  have henv' := henv
  unfold Env0 at henv'
  obtain ⟨hB, hnp, hnd, hrec, htab⟩ := henv'
  have hcap := (room0_pos' hroom).2.2
  rw [hj, Nat.min_eq_left (by omega), capMin_succ] at hcap
  have hnj : recN s.mem j < 8 := by omega
  have hjn : s.mem.readLE 65544 8 = j + 1 := hj
  have hnj' : s.mem.readLE (j * 96 + 66072) 8 < 8 := by
    rw [show j * 96 + 66072 = 66048 + 96 * j + 24 by omega]; exact hnj
  have hj8 : j < 8 := by omega
  have hmul : (BitVec.ofNat 64 (j + 1) - 1#64) = BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  have hmul2 : (BitVec.ofNat 64 j * 96#64).toNat = j * 96 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  simp only [P0_priv, P0_depth, outside_cons, outside_nil, and_true, B] at hout hd h8 hwin
  janus64_run [hjn, hmul, hmul2]
  generalize hn : s.mem.readLE (j * 96 + 66072) 8 = n at *
  have hn' : recN s.mem j = n := by simp only [recN, rd, recAt, B]; rw [← hn]; congr 1; omega
  refine ⟨panicRet_of _ 2 s _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) (by rfl)
    (by simp [hdf]) (by rfl) ?_ ?_, ?_, ?_⟩
  · rw [P0_priv, P0_depth]; simp only [B, MapAmd64.calleeStack, List.cons_append, List.nil_append]; janus_frame
  · rw [P0_env]; unfold Env0; dsimp only
    refine ⟨by simpa using hB, ?_, ?_, fun i hi => ?_, ?_⟩
    · simp only [npan, rd, B]; model_simp; exact hnp
    · simp only [ndef, rd, B]; model_simp; exact hnd
    · simp only [ndef, rd, B, recN, recTok, recConv, recAt] at hi ⊢
      model_simp at hi
      by_cases hij : i = j
      · subst hij; model_simp; omega
      · have := hrec i (by simp only [ndef, rd, B]; omega)
        simp only [recN, recTok, recConv, recAt, rd, B] at this
        have hij' : i < j := by omega
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact this
    · repeat' first | apply tableOK_w | exact htab
      all_goals (simp only [tabAt, B, Nat.reduceAdd, Nat.reduceMul]; omega)
  · intro r' rest' hdr'
    rw [hdr] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    rw [hr, hrest, defers0_eq]
    try simp only [ndef, rd, B]
    try model_simp
    rw [hjn, Nat.min_eq_left (by omega), recList_succ]
    rw [recList_w (k := j) (by simp only [recAt, B]; omega), recList_w (k := j) (by simp only [recAt, B]; omega)]
    simp only [show j * 96 + 66048 + n * 8 + 32 = j * 96 + (66080 + n * 8) by omega]
    unfold decRec
    have e1 : recTok ((s.mem.writeLE (j * 96 + (66080 + n * 8)) 8 (BitVec.toNat (s.regs 0))).writeLE
        (j * 96 + 66072) 8 (n + 1)) j = recTok s.mem j := by
      simp only [recTok, rd, recAt, B]; model_simp
    have e2 : recConv ((s.mem.writeLE (j * 96 + (66080 + n * 8)) 8 (BitVec.toNat (s.regs 0))).writeLE
        (j * 96 + 66072) 8 (n + 1)) j = recConv s.mem j := by
      simp only [recConv, rd, recAt, B]; model_simp
    have e3 : recSp ((s.mem.writeLE (j * 96 + (66080 + n * 8)) 8 (BitVec.toNat (s.regs 0))).writeLE
        (j * 96 + 66072) 8 (n + 1)) j = recSp s.mem j := by
      simp only [recSp, rd, recAt, B]; model_simp
    have e4 : recN ((s.mem.writeLE (j * 96 + (66080 + n * 8)) 8 (BitVec.toNat (s.regs 0))).writeLE
        (j * 96 + 66072) 8 (n + 1)) j = n + 1 := by
      simp only [recN, rd, recAt, B]; model_simp; omega
    have e5 : PanicModel.recFns ((s.mem.writeLE (j * 96 + (66080 + n * 8)) 8 (BitVec.toNat (s.regs 0))).writeLE
        (j * 96 + 66072) 8 (n + 1)) j (n + 1) = (s.regs 0).toNat :: PanicModel.recFns s.mem j n := by
      rw [recFns_succ, recFns_w j (by simp only [recAt, B]; omega) n (by omega),
        recFns_slot j (by simp only [recAt, B]; omega)]
      simp only [recFn, rd, recAt, B]; model_simp
      rw [Nat.mod_eq_of_lt (BitVec.isLt _)]
    rw [e1, e2, e3, e4, hn', Nat.min_eq_left (by omega : n + 1 ≤ 8), Nat.min_eq_left (by omega : n ≤ 8), e5]
    simp only [htok, hconv, false_or, ne_eq, not_true_eq_false, ite_false, List.cons_append, List.nil_append]
  · refine ⟨?_, ?_, rfl, ?_⟩
    · rw [P0_panics, P0_panics, panics0_eq, panics0_eq]; simp only [npan, rd, B]; model_simp
    · rw [P0_saved, P0_saved, saved0_eq, saved0_eq]; simp only [rd, B]; model_simp
    · rw [P0_room, P0_room, room0_eq, room0_eq]; simp only [npan, ndef, rd, B]
      model_simp
      rw [hjn, Nat.min_eq_left (by omega : j + 1 ≤ 8), capMin_succ, capMin_succ,
        capMin_w (k := j) (by simp only [recAt, B]; omega), capMin_w (k := j) (by simp only [recAt, B]; omega), hn']
      simp only [recN, rd, recAt, B]
      model_simp
      omega



set_option maxHeartbeats 0 in
theorem and3 (v : Nat) (h : BitVec.setWidth 32 (BitVec.ofNat 64 v) &&& 3#32 = 0#32) : v % 4 = 0 := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  have h3 : (3 : Nat) = 2 ^ 2 - 1 := by decide
  simp at this
  rw [h3, Nat.and_two_pow_sub_one_eq_mod] at this
  omega

theorem and3' (v : Nat) (h : ¬ BitVec.setWidth 32 (BitVec.ofNat 64 v) &&& 3#32 = 0#32) : v % 4 ≠ 0 := by
  intro hv
  apply h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have h3 : (3 : Nat) = 2 ^ 2 - 1 := by decide
  simp
  rw [h3, Nat.and_two_pow_sub_one_eq_mod]
  omega

set_option maxHeartbeats 0 in
theorem gorecover_run {p : Program} (hp : EngineAt p) (T : List FuncInfo) :
    PanicAmd64.GorecoverContract p eGorecover (P0 T RPa) := by
  intro s hpc ⟨hpre, hfp, hfp'⟩
  apply reachesRet_transfer hp
  obtain ⟨henv, -, hal, hd, h8, hwin, hx, hdf, hra, hout⟩ := hpre
  rw [P0_env] at henv
  have henv' := henv
  unfold Env0 at henv'
  obtain ⟨hB, hnp, hnd, hrec, htab⟩ := henv'
  have hnp' : s.mem.readLE 65536 8 ≤ 8 := hnp
  have hB' : s.mem.accessible 65536 4096 true = true := hB
  simp only [P0_priv, P0_depth, outside_cons, outside_nil, and_true, B] at hout hd h8 hwin
  have hrpl : s.mem.readLE (s.regs 5).toNat 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 5).toNat 8; simpa using this
  janus64_run
  · -- no panic: nil
    have h0 : panics0 s.mem = [] := panics0_nil (by simpa using ‹s.mem.readLE 65536 8 = 0›)
    refine ⟨panicRet_of _ 0 s _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) (by rfl)
      (by simp [hdf]) (by rfl) (MemFrame.refl _ _) (by rw [P0_env]; exact henv), Nat.le_refl _,
      fun _ => trivial, fun r rs h => ?_⟩
    rw [P0_panics, h0] at h; cases h
  all_goals
    generalize hnp : s.mem.readLE 65536 8 = np at *
    obtain ⟨k, rfl⟩ : ∃ k, np = k + 1 := ⟨np - 1, by omega⟩
    have hk8 : k < 8 := by omega
    have htop : panics0 s.mem = decPan s.mem k :: panList s.mem k := panics0_top hnp hk8
    simp only [Nat.add_sub_cancel] at *
  · -- recover
    have hflag := and3 _ ‹BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (65792 + k * 32 + 24) 8)) &&& 3#32 = 0#32›
    have hw : panAt 0 ≤ 65792 + k * 32 + 24 ∧ 65792 + k * 32 + 24 + 8 ≤ panAt 8 := by
      simp only [panAt, B]; omega
    have htop' : panics0 (s.mem.writeLE (65792 + k * 32 + 24) 8 2) =
        { decPan s.mem k with recovered := true } :: panList s.mem k := by
      rw [panics0_top (k := k) (by simp only [npan, rd, B]; model_simp; exact hnp) hk8,
        panList_w k (by simp only [panAt, B]; omega)]
      congr 1
      simp only [decPan, panAt, rd, B, Nat.mul_comm 32 k, Nat.reduceAdd]
      model_simp
      simp [hflag]
      omega
    refine ⟨panicRet_of _ 0 s _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) (by rfl)
      (by simp [hdf]) (by rfl) ?_ ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · rw [P0_priv, P0_depth]; simp only [B, MapAmd64.calleeStack, List.cons_append, List.nil_append]; janus_frame
    · rw [P0_env]; exact env0_wpan hw henv
    · rw [P0_defers, P0_defers]; exact defers0_wpan hw
    · rw [P0_saved, P0_saved]; exact saved0_wpan hw
    · rw [P0_room, P0_room, room0_wpan hw]; exact Nat.le_refl _
    · rintro (h | ⟨r, rs, h, hr⟩)
      · rw [P0_panics, htop] at h; cases h
      · rw [P0_panics, htop] at h; obtain ⟨rfl, rfl⟩ := List.cons.inj h
        simp only [decPan, panAt, rd, B, Nat.mul_comm 32 k, Nat.reduceAdd] at hr; exfalso
        rcases hr with hr | hr <;> simp at hr <;> omega
    · intro r rs h _ _ _ _
      rw [P0_panics, htop] at h; obtain ⟨rfl, rfl⟩ := List.cons.inj h
      refine ⟨by simp [decPan, panAt, Nat.mul_comm 32 k], by simp [decPan, panAt, Nat.mul_comm 32 k], ?_⟩
      rw [P0_panics, htop']
  · -- the caller is not the running deferred call: nil
    refine ⟨panicRet_of _ 0 s _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) (by rfl)
      (by simp [hdf]) (by rfl) (MemFrame.refl _ _) (by rw [P0_env]; exact henv), Nat.le_refl _,
      fun _ => trivial, ?_⟩
    intro r rs _ _ _ _ hrp
    exfalso
    have hrp' : s.mem.readLE ((s.regs 5).toNat + 8) 8 = 3146633 := hrp
    apply ‹¬(18446744073706404983 + s.mem.readLE ((s.regs 5).toNat + 8) 8) % 18446744073709551616 = 0›
    omega
  · -- a Goexit or an already recovered panic: nil
    have hflag := and3' _ ‹¬BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (65792 + k * 32 + 24) 8)) &&& 3#32 = 0#32›
    refine ⟨panicRet_of _ 0 s _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) (by simp) (by rfl)
      (by simp [hdf]) (by rfl) (MemFrame.refl _ _) (by rw [P0_env]; exact henv), Nat.le_refl _,
      fun _ => trivial, ?_⟩
    intro r rs h hg hr _ _
    rw [P0_panics, htop] at h; obtain ⟨rfl, rfl⟩ := List.cons.inj h
    simp only [decPan, panAt, rd, B, Nat.mul_comm 32 k, Nat.reduceAdd] at hg hr
    exfalso; simp at hg hr; omega


end Janus.Contracts.PanicSatAmd64
