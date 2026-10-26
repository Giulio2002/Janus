import Janus.Contracts.MallocSC
import Janus.Contracts.AllocAmd64

/-!
# The size-specialised allocator (`GOEXPERIMENT=sizespecializedmalloc`, amd64)

The amd64 versions of `Janus.Contracts.MallocSC` (`RAX = size`, `RBX = typ`, `RCX = needzero`),
on `MallocgcContract64`.
-/

namespace Janus.Contracts

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Spec

def MallocgcSCPre64 (args : Janus.Arm64.Memory → Nat → Nat → Prop) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) (s : State) : Prop :=
  (MallocgcPre64 stack s ∧ Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s) ∧
    args s.mem (s.regs 0).toNat (s.regs 3).toNat

/-- **`runtime.mallocgcSmallNoScanSC<n>`** (amd64). -/
def MallocgcSmallNoScanSCContract64 (n : Nat) (p : Janus.Amd64.Program) (addr : Nat)
    (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady) : Prop :=
  Summary p addr (MallocgcSCPre64 (NoScanArgs n) rt stack H)
    (fun s s' => AllocRet64 rt stack 3 (fun ptr => [ptr]) s s' (mallocgcObj64 rt s))

/-- **`runtime.mallocgcSmallScanNoHeaderSC<n>`** (amd64). -/
def MallocgcSmallScanNoHeaderSCContract64 (n : Nat) (p : Janus.Amd64.Program) (addr : Nat)
    (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady) : Prop :=
  Summary p addr (MallocgcSCPre64 (ScanArgs n) rt stack H)
    (fun s s' => AllocRet64 rt stack 3 (fun ptr => [ptr]) s s' (mallocgcObj64 rt s))

/-- **`runtime.mallocgcTinySize<n>`** (amd64). -/
def MallocgcTinySizeContract64 (n : Nat) (p : Janus.Amd64.Program) (addr : Nat)
    (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady) : Prop :=
  Summary p addr (MallocgcSCPre64 (TinyArgs n) rt stack H)
    (fun s s' => AllocRet64 rt stack 3 (fun ptr => [ptr]) s s' (mallocgcObj64 rt s))

theorem MallocgcContract64.smallNoScanSC {n : Nat} {p : Janus.Amd64.Program} {addr : Nat}
    {rt : List (Nat × Nat)} {stack : Nat} {H : RtReady} (h : MallocgcContract64 p addr rt stack H) :
    MallocgcSmallNoScanSCContract64 n p addr rt stack H :=
  Summary.mono h (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3⟩ =>
    ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3 (by have := hp.2.1; omega)⟩

theorem MallocgcContract64.smallScanNoHeaderSC {n : Nat} {p : Janus.Amd64.Program} {addr : Nat}
    {rt : List (Nat × Nat)} {stack : Nat} {H : RtReady} (h : MallocgcContract64 p addr rt stack H) :
    MallocgcSmallScanNoHeaderSCContract64 n p addr rt stack H :=
  Summary.mono h (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3⟩ =>
    ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3 hp.2.1⟩

theorem MallocgcContract64.tinySize {n : Nat} {p : Janus.Amd64.Program} {addr : Nat}
    {rt : List (Nat × Nat)} {stack : Nat} {H : RtReady} (h : MallocgcContract64 p addr rt stack H) :
    MallocgcTinySizeContract64 n p addr rt stack H :=
  Summary.mono h (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3⟩ =>
    ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3 (by obtain ⟨h0, -, hs, -⟩ := hp.2; omega)⟩

end Janus.Contracts
