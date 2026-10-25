import Janus.GoABI0
import Janus.Amd64.GoABI0
import Janus.Tactic
import Janus.Amd64

/-!
# Proof automation for ABI0 (Go assembly) on both ISAs

* `janus_intro0 hs` (arm64) turns `hs : GoABI0.CallSetup0 p entry [a₀, …] nres s` into
  `h_pc : s.pc = …`, `h_lr : s.regs 30 = …` (the return address), `h_al : s.sp.toNat % 16 = 0`,
  the argument words `h_rd_arg<i> : s.mem.readLE (s.sp.toNat + 8(i+1)) 8 = aᵢ.toNat`, and the frame
  `h_fb : s.sp.toNat + 8(n+1) ≤ 2^48`, `h_facc : s.mem.accessible (s.sp.toNat + 8) (8n) true =
  true` with `n = length + nres` (offsets as literals). The `h_rd…` names make the argument
  facts rewrite rules of `janus_run`/`janus_simp` (`Janus.Tactic.stateHyps`), so the loads of
  the arguments from the frame (`MOVD x+0(FP), R0` is `ldr x0, [sp, #8]`) yield `aᵢ` itself.
* `janus64_intro0 hs` (amd64) does the same for `Amd64.GoABI0.CallSetup0`: `h_rip`, `h_ret`
  (the return address at `[RSP]`), `h_df`, `h_rd_arg<i>`, `h_fb`, and `h_facc` (the return slot
  and the frame: `s.mem.accessible (s.regs 4).toNat (8(n+1)) true = true`).

The post-processing simp sets reduce the ABI0 vocabulary of a goal left after symbolic execution:
`results0` and `wordsAt` unfold to the explicit list of frame words, and on amd64 `ABIReturn0`
to its equations. `ABIReturn0` on arm64 is `GoABI.ABIReturn`, which `janus_run` already
discharges.

Composition needs nothing ABI0-specific: a callee is used at a direct ABI0 call, or at the
`BL`/`CALL` of an ABI wrapper, through its `Summary` (or `Summary0`) with `janus_run calls [h]`
/ `janus64_run calls [h]`; on amd64 the re-entry sequence after the call (`XORPS X15, X15`,
`MOVQ FS:-8, R14`) is executed like any other instruction, from the `GoABI.TlsG` facts.
-/

namespace Janus.MemFrame

open Janus.Arm64

/-! ## Memory frames of ABI0 callees

An ABI0 callee returns its results in memory, so its `Summary0` describes the memory it returns
with, typically as `MemFrame e m rs`: `m` agrees with the expected memory `e` (the call state's
memory with the result words written) outside the scratch ranges `rs` (the frames the callee and
its own callees push below `SP`). These lemmas prove such a frame for the final memory of the
callee's symbolic run, with `MemFrame.writeLE` (a store inside `rs`) and
`MemFrame.writeLE_both` (`Janus.FFI`: the same store on both sides). (`rs` should not be the empty list: write a leaf callee's scratch range as
`[(SP, SP)]`; the `MemFrame` read rule with an empty list is not used by `simp`.) -/

variable {m m' : Memory} {rs : List (Nat × Nat)}

/-- The same value written at the same address: equal memories frame each other (for a
`writeLE` whose value is written in two equal forms, e.g. `2 * x % 2^64` and `x + x`). -/
theorem writeLE_congr (h : MemFrame m m' rs) (a k : Nat) {v v' : Nat} (hv : v = v') :
    MemFrame (m.writeLE a k v) (m'.writeLE a k v') rs := hv ▸ h.writeLE_both a k v

end Janus.MemFrame

namespace Janus.Tactic

open Lean Meta Elab Tactic

attribute [janus_post] GoABI0.results0 GoABI0.wordsAt_succ GoABI0.wordsAt_zero

/-- Assert `name : ty` proved by `pf` (whose type is defeq to `ty`) in `g`. -/
private def assertHyp (g : MVarId) (name : Name) (ty pf : Expr) : MetaM MVarId := g.withContext do
  let pf ← mkExpectedTypeHint pf ty
  let (_, g') ← (← g.assert name ty pf).intro1P
  return g'

/-- `base + k` for a numeral `k` (`base` itself when `k = 0`). -/
private def addLit (base : Expr) (k : Nat) : MetaM Expr :=
  if k == 0 then pure base else mkAppM ``HAdd.hAdd #[base, mkNatLit k]

/-- From `hs : GoABI0.CallSetup0 p entry [a₀, …] nres s`, add `h_pc`, `h_lr`, `h_al`,
`h_rd_arg<i> : s.mem.readLE (s.sp.toNat + 8(i+1)) 8 = aᵢ.toNat`, `h_fb` and `h_facc` (see the module
doc). For a call with a symbolic return address (`p = Program.withExit p₀ ret`) `h_lr` is
`s.regs 30 = BitVec.ofNat 64 ret` and `hret : RetAddr p₀ ret` must be in the context. -/
elab "janus_intro0 " h:ident : tactic => withMainContext do
  let hE ← elabTerm h none
  let ty ← whnfR (← instantiateMVars (← inferType hE))
  let (``GoABI0.CallSetup0, #[prog, entry, args, nres, s]) := ty.getAppFnArgs |
    throwError "janus_intro0: expected a `GoABI0.CallSetup0` hypothesis"
  let some (_, elemsL) := (← instantiateMVars args).listLit? |
    throwError "janus_intro0: the argument list must be a list literal"
  let elems := elemsL.toArray
  let some entryN ← evalNat entry | throwError "janus_intro0: cannot evaluate the entry address"
  let some nresN ← evalNat nres | throwError "janus_intro0: cannot evaluate the number of results"
  let mode ← exitMode prog
  let exitE ← match mode with
    | some (base, retE) => discard <| findRetAddr base retE; pure retE
    | none =>
      let some exitN ← evalNat (← mkAppM ``Program.exitAddr #[prog]) |
        throwError "janus_intro0: cannot evaluate the exit address"
      pure (mkNatLit exitN)
  let bv (e : Expr) : Expr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) e
  let mut g ← getMainGoal
  g ← assertHyp g `h_pc (← mkEq (← mkAppM ``Arm64.State.pc #[s]) (bv (mkNatLit entryN)))
    (← mkAppM ``GoABI0.CallSetup0.pc #[hE])
  g ← g.withContext do
    assertHyp g `h_lr (← mkEq (mkApp (← mkAppM ``Arm64.State.regs #[s]) (mkNatLit 30)) (bv exitE))
      (← mkAppM ``GoABI0.CallSetup0.lr #[hE])
  let spN ← mkAppM ``BitVec.toNat #[← mkAppM ``Arm64.State.sp #[s]]
  let mem ← mkAppM ``Arm64.State.mem #[s]
  g ← g.withContext do
    assertHyp g `h_al (← mkEq (← mkAppM ``HMod.hMod #[spN, mkNatLit 16]) (mkNatLit 0))
      (← mkAppM ``GoABI0.CallSetup0.spAligned #[hE])
  for i in [0:elems.size] do
    g ← g.withContext do
      let lhs ← mkAppM ``Arm64.Memory.readLE #[mem, ← addLit spN (8 + 8 * i), mkNatLit 8]
      let tyI ← mkEq lhs (← mkAppM ``BitVec.toNat #[elems[i]!])
      let lenLt ← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[args]]
      let pf ← mkAppOptM ``GoABI0.CallSetup0.arg
        #[none, none, none, none, none, hE, mkNatLit i, ← mkDecideProof lenLt]
      assertHyp g (Name.mkSimple s!"h_rd_arg{i}") tyI pf
  let n := elems.size + nresN
  g ← g.withContext do
    let fbTy ← mkAppM ``LE.le #[← addLit spN (8 + 8 * n),
      ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 48]]
    assertHyp g `h_fb fbTy (← mkAppM ``GoABI0.CallSetup0.frame_bound #[hE])
  g ← g.withContext do
    let acc ← mkAppM ``Arm64.Memory.accessible
      #[mem, ← addLit spN 8, mkNatLit (8 * n), mkConst ``Bool.true]
    assertHyp g `h_facc (← mkEq acc (mkConst ``Bool.true))
      (← mkAppM ``GoABI0.CallSetup0.frame_accessible #[hE])
  replaceMainGoal [g]

end Janus.Tactic

namespace Janus.Amd64.Tactic

open Lean Meta Elab Lean.Elab.Tactic

attribute [janus64_post] Amd64.GoABI0.results0 Amd64.GoABI0.wordsAt_succ
  Amd64.GoABI0.wordsAt_zero Amd64.GoABI0.abiReturn0_iff

private def assertHyp (g : MVarId) (name : Name) (ty pf : Expr) : MetaM MVarId := g.withContext do
  let pf ← mkExpectedTypeHint pf ty
  let (_, g') ← (← g.assert name ty pf).intro1P
  return g'

private def addLit (base : Expr) (k : Nat) : MetaM Expr :=
  if k == 0 then pure base else mkAppM ``HAdd.hAdd #[base, mkNatLit k]

/-- From `hs : Amd64.GoABI0.CallSetup0 p entry [a₀, …] nres s`, add `h_rip`, `h_ret`
(`s.mem.readLE (s.regs 4).toNat 8 = ret`), `h_df`, `h_rd_arg<i> : s.mem.readLE ((s.regs 4).toNat +
8(i+1)) 8 = aᵢ.toNat`, `h_fb` and `h_facc`. For `p = Program.withExit p₀ ret` the hypothesis
`hret : RetAddr p₀ ret` must be in the context. -/
elab "janus64_intro0 " h:ident : tactic => withMainContext do
  let hE ← elabTerm h none
  let ty ← whnfR (← instantiateMVars (← inferType hE))
  let (``Amd64.GoABI0.CallSetup0, #[prog, entry, args, nres, s]) := ty.getAppFnArgs |
    throwError "janus64_intro0: expected an `Amd64.GoABI0.CallSetup0` hypothesis"
  let some (_, elemsL) := (← instantiateMVars args).listLit? |
    throwError "janus64_intro0: the argument list must be a list literal"
  let elems := elemsL.toArray
  let some entryN ← evalNat entry | throwError "janus64_intro0: cannot evaluate the entry address"
  let some nresN ← evalNat nres |
    throwError "janus64_intro0: cannot evaluate the number of results"
  let mode ← exitMode prog
  let exitE ← match mode with
    | some (base, retE) => discard <| findRetAddr base retE; pure retE
    | none =>
      let some exitN ← evalNat (← mkAppM ``Program.exitAddr #[prog]) |
        throwError "janus64_intro0: cannot evaluate the exit address"
      pure (mkNatLit exitN)
  let bv (n : Nat) : Expr := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)
  let mut g ← getMainGoal
  g ← assertHyp g `h_rip (← mkEq (← mkAppM ``State.rip #[s]) (bv entryN))
    (← mkAppM ``Amd64.GoABI0.CallSetup0.rip #[hE])
  let rspN ← mkAppM ``BitVec.toNat #[mkApp (← mkAppM ``State.regs #[s]) (mkNatLit 4)]
  let mem ← mkAppM ``State.mem #[s]
  g ← g.withContext do
    assertHyp g `h_ret (← mkEq (← mkAppM ``Janus.Arm64.Memory.readLE #[mem, rspN, mkNatLit 8]) exitE)
      (← mkAppM ``Amd64.GoABI0.CallSetup0.ret #[hE])
  g ← g.withContext do
    assertHyp g `h_df (← mkEq (← mkAppM ``State.df #[s]) (mkConst ``Bool.false))
      (← mkAppM ``Amd64.GoABI0.CallSetup0.df #[hE])
  for i in [0:elems.size] do
    g ← g.withContext do
      let lhs ← mkAppM ``Janus.Arm64.Memory.readLE #[mem, ← addLit rspN (8 + 8 * i), mkNatLit 8]
      let tyI ← mkEq lhs (← mkAppM ``BitVec.toNat #[elems[i]!])
      let lenLt ← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[args]]
      let pf ← mkAppOptM ``Amd64.GoABI0.CallSetup0.arg
        #[none, none, none, none, none, hE, mkNatLit i, ← mkDecideProof lenLt]
      assertHyp g (Name.mkSimple s!"h_rd_arg{i}") tyI pf
  let n := elems.size + nresN
  g ← g.withContext do
    let fbTy ← mkAppM ``LE.le #[← addLit rspN (8 + 8 * n),
      ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 48]]
    assertHyp g `h_fb fbTy (← mkAppM ``Amd64.GoABI0.CallSetup0.frame_bound #[hE])
  g ← g.withContext do
    let acc ← mkAppM ``Janus.Arm64.Memory.accessible
      #[mem, rspN, mkNatLit (8 + 8 * n), mkConst ``Bool.true]
    assertHyp g `h_facc (← mkEq acc (mkConst ``Bool.true))
      (← mkAppM ``Amd64.GoABI0.CallSetup0.frame_accessible #[hE])
  replaceMainGoal [g]

end Janus.Amd64.Tactic
