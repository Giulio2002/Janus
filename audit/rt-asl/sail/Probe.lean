import RtProbe
open RtProbe RtProbe.Functions

def runProbe (v : BitVec 8) : Int :=
  match (probe v).run default with
  | .ok r _ => r
  | .error _ _ => -999999

#eval do
  let mut out : Array String := #[]
  for i in [0:256] do
    let v : BitVec 8 := BitVec.ofNat 8 i
    out := out ++ #[s!"probe {runProbe v}", s!"onebit {onebit v}", s!"va {va v}", s!"vd {vd v}", s!"vg {vg v}",
      s!"vh {vh v}", s!"vc {vc v}", s!"ve {ve v}", s!"vb {vb v}", s!"vf {vf v}", s!"vcat {vcat v}"]
  out := out ++ #[s!"rtz {rtz 18446744073709551615 7}", s!"rtz {rtz (-9223372036854775808) (-1)}",
    s!"rtz {rtz (-9223372036854775807) 3}", s!"rtz {rtz 18446744073709551557 18446744073709551533}",
    s!"rtz {rtz (-7) 2}", s!"rtz {rtz 7 (-2)}", s!"rtz {rtz 1234567890123456789012345 97}",
    s!"rpow {rpow 2 (-3)}", s!"rpow {rpow 3 5}", s!"rpow {rpow (-2) (-1)}"]
  out := out ++ #[s!"rsq {rsq 4 1}", s!"rsq {rsq 9 4}", s!"rsq {rsq 2 1}", s!"rsq {rsq 1 2}", s!"rsq {rsq 1 3}", s!"rsq {rsq 100000000000000000001 1}", s!"rsq {rsq 1000000000000000000000000000000 7}", s!"rsq {rsq 1 10000000000000000000000000}", s!"rsq {rsq 1 1267650600228229401496703205376}", s!"rsq {rsq 3 2535301200456458802993406410752}", s!"rsq {rsq 1606938044258990275541962092341162602522202993782792835301377 1}", s!"rsq {rsq 123456789 1000}", s!"rsq {rsq 5 1}", s!"rsq {rsq 7 3}", s!"rsq {rsq 144 25}", s!"rsq {rsq 1 1}", s!"rsq {rsq 99 100}", s!"rsq {rsq 4503599627370497 4503599627370496}", s!"rsq {rsq 81129638414606681695789005144065 81129638414606681695789005144064}", s!"rsq {rsq 17 1}", s!"rsq {rsq 1 10000000000000000000000000000000000000000}", s!"rsq {rsq 31415926535 10000000000}", s!"rsq {rsq 999999999999999999 1000000000000000000}", s!"rsq {rsq 2 12157665459056928801}", s!"rsq {rsq 221073919720733357899776 1}", s!"rsq {rsq 221073919720733357899777 1}", s!"rsq {rsq 3 4}", s!"rsq {rsq 1 4}", s!"rsq {rsq 1152921504606846976 3}", s!"rsq {rsq 100000000000000000000000000000000000000000000000007 13}"]
  IO.println (String.intercalate "\n" out.toList)
