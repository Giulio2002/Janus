import Janus.Contracts.Sat
import Janus.Contracts.SatAmd64

/-!
# Non-vacuity of the `RtSpec` contracts (`RtContract`, `RtContract64`)

`RtContract`/`RtContract64` (`Janus.Contracts.Rt`) turn each string and slice spec
(`Janus/Contracts/String.lean`, `Slice.lean`, `WriteBarrier.lean`'s `wbZero`/`wbMove`) into a
`Summary`. `rt_satisfiable` (arm64) and `rt64_satisfiable` (amd64) collect the per-spec witnesses
of `Janus.Contracts.Sat` and `Janus.Contracts.SatAmd64`: for each spec, runtime-owned ranges, a
readiness predicate, code meeting the contract, and a call state meeting its precondition, all
kernel-checked.

`decoderuneSpec` and `countrunesSpec` hold for every input without a readiness predicate, so no
constant toy meets them: their witness is the runtime's own code, proved to meet them in
`examples/proofs/SumRunes.lean` and `examples/proofs/RuneLen.lean` (`decoderune_satisfiable`,
`countrunes_satisfiable` there; `runtime_correctness` uses them) and the amd64 counterparts.
-/

namespace Janus.Contracts.RtSat

open Janus Janus.Contracts

/-- Every arm64 string/slice `RtContract` of this branch is satisfiable. -/
theorem rt_satisfiable :
  (∀ k, k ≤ 7 → Sat.Satisfiable (concatstringSpec k)) ∧
  (∀ k, k ≤ 7 → Sat.Satisfiable (concatbyteSpec k)) ∧
  Sat.Satisfiable concatstringsSpec ∧
  Sat.Satisfiable concatbytesSpec ∧
  Sat.Satisfiable slicebytetostringSpec ∧
  Sat.Satisfiable slicebytetostringtmpSpec ∧
  Sat.Satisfiable stringtoslicebyteSpec ∧
  Sat.Satisfiable stringtosliceruneSpec ∧
  Sat.Satisfiable slicerunetostringSpec ∧
  Sat.Satisfiable intstringSpec ∧
  Sat.Satisfiable gostringSpec ∧
  Sat.Satisfiable gostringnSpec ∧
  Sat.Satisfiable gobytesSpec ∧
  Sat.Satisfiable growsliceSpec ∧
  Sat.Satisfiable growsliceNoAliasSpec ∧
  Sat.Satisfiable growsliceBufSpec ∧
  Sat.Satisfiable growsliceBufNoAliasSpec ∧
  Sat.Satisfiable makeslicecopySpec ∧
  Sat.Satisfiable moveSliceSpec ∧
  Sat.Satisfiable moveSliceNoScanSpec ∧
  Sat.Satisfiable moveSliceNoCapSpec ∧
  Sat.Satisfiable moveSliceNoCapNoScanSpec ∧
  Sat.Satisfiable slicecopySpec ∧
  Sat.Satisfiable typedslicecopySpec ∧
  Sat.Satisfiable wbZeroSpec ∧
  Sat.Satisfiable wbMoveSpec :=
  ⟨Sat.concatstring_satisfiable, Sat.concatbyte_satisfiable, Sat.concatstrings_satisfiable, Sat.concatbytes_satisfiable, Sat.slicebytetostring_satisfiable, Sat.slicebytetostringtmp_satisfiable, Sat.stringtoslicebyte_satisfiable, Sat.stringtoslicerune_satisfiable, Sat.slicerunetostring_satisfiable, Sat.intstring_satisfiable, Sat.gostring_satisfiable, Sat.gostringn_satisfiable, Sat.gobytes_satisfiable, Sat.growslice_satisfiable, Sat.growsliceNoAlias_satisfiable, Sat.growsliceBuf_satisfiable, Sat.growsliceBufNoAlias_satisfiable, Sat.makeslicecopy_satisfiable, Sat.moveSlice_satisfiable, Sat.moveSliceNoScan_satisfiable, Sat.moveSliceNoCap_satisfiable, Sat.moveSliceNoCapNoScan_satisfiable, Sat.slicecopy_satisfiable, Sat.typedslicecopy_satisfiable, Sat.wbZero_satisfiable, Sat.wbMove_satisfiable⟩

/-- Every amd64 string/slice `RtContract64` of this branch is satisfiable. -/
theorem rt64_satisfiable :
  (∀ k, k ≤ 7 → SatAmd64.Satisfiable (concatstringSpec k)) ∧
  (∀ k, k ≤ 7 → SatAmd64.Satisfiable (concatbyteSpec k)) ∧
  SatAmd64.Satisfiable concatstringsSpec ∧
  SatAmd64.Satisfiable concatbytesSpec ∧
  SatAmd64.Satisfiable slicebytetostringSpec ∧
  SatAmd64.Satisfiable slicebytetostringtmpSpec ∧
  SatAmd64.Satisfiable stringtoslicebyteSpec ∧
  SatAmd64.Satisfiable stringtosliceruneSpec ∧
  SatAmd64.Satisfiable slicerunetostringSpec ∧
  SatAmd64.Satisfiable intstringSpec ∧
  SatAmd64.Satisfiable gostringSpec ∧
  SatAmd64.Satisfiable gostringnSpec ∧
  SatAmd64.Satisfiable gobytesSpec ∧
  SatAmd64.Satisfiable growsliceSpec ∧
  SatAmd64.Satisfiable growsliceNoAliasSpec ∧
  SatAmd64.Satisfiable growsliceBufSpec ∧
  SatAmd64.Satisfiable growsliceBufNoAliasSpec ∧
  SatAmd64.Satisfiable makeslicecopySpec ∧
  SatAmd64.Satisfiable moveSliceSpec ∧
  SatAmd64.Satisfiable moveSliceNoScanSpec ∧
  SatAmd64.Satisfiable moveSliceNoCapSpec ∧
  SatAmd64.Satisfiable moveSliceNoCapNoScanSpec ∧
  SatAmd64.Satisfiable slicecopySpec ∧
  SatAmd64.Satisfiable typedslicecopySpec ∧
  SatAmd64.Satisfiable wbZeroSpec ∧
  SatAmd64.Satisfiable wbMoveSpec :=
  ⟨SatAmd64.concatstring_satisfiable, SatAmd64.concatbyte_satisfiable, SatAmd64.concatstrings_satisfiable, SatAmd64.concatbytes_satisfiable, SatAmd64.slicebytetostring_satisfiable, SatAmd64.slicebytetostringtmp_satisfiable, SatAmd64.stringtoslicebyte_satisfiable, SatAmd64.stringtoslicerune_satisfiable, SatAmd64.slicerunetostring_satisfiable, SatAmd64.intstring_satisfiable, SatAmd64.gostring_satisfiable, SatAmd64.gostringn_satisfiable, SatAmd64.gobytes_satisfiable, SatAmd64.growslice_satisfiable, SatAmd64.growsliceNoAlias_satisfiable, SatAmd64.growsliceBuf_satisfiable, SatAmd64.growsliceBufNoAlias_satisfiable, SatAmd64.makeslicecopy_satisfiable, SatAmd64.moveSlice_satisfiable, SatAmd64.moveSliceNoScan_satisfiable, SatAmd64.moveSliceNoCap_satisfiable, SatAmd64.moveSliceNoCapNoScan_satisfiable, SatAmd64.slicecopy_satisfiable, SatAmd64.typedslicecopy_satisfiable, SatAmd64.wbZero_satisfiable, SatAmd64.wbMove_satisfiable⟩

end Janus.Contracts.RtSat
