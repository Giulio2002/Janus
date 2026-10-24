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
  IO.println (String.intercalate "\n" out.toList)
