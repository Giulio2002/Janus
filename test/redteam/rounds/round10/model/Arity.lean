import Janus
/-! Round 10 V2/V3: every allocating runtime contract takes a readiness predicate `H : RtReady`
(required at the call, not handed back). This file only elaborates against the fixed framework. -/
open Janus Janus.Contracts Janus.Spec.Type Janus.Spec.Map

#check (Janus.Contracts.Map.Assign : Janus.Program → Nat → MapModel (BitVec 64) (BitVec 64) → RtReady → Prop)
#check (@Janus.Contracts.Map.MakeSmall (BitVec 64) (BitVec 64) : Janus.Program → Nat → MapModel (BitVec 64) (BitVec 64) → RtReady → Prop)
#check (Janus.Contracts.MapAmd64.Assign : Janus.Amd64.Program → Nat → MapModel (BitVec 64) (BitVec 64) → RtReady → Prop)
#check (@Janus.Contracts.MapAmd64.MakeSmall (BitVec 64) (BitVec 64) : Janus.Amd64.Program → Nat → MapModel (BitVec 64) (BitVec 64) → RtReady → Prop)
#check (Janus.Contracts.Iface.ConvT : Janus.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.Iface.ConvTnoptr : Janus.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.Iface.ConvT16 : Janus.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.Iface.ConvT32 : Janus.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.Iface.ConvT64 : Janus.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.Iface.ConvTstring : Janus.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.Iface.ConvTslice : Janus.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.Iface.TypeAssert : Janus.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.Iface.InterfaceSwitch : Janus.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.IfaceAmd64.ConvT : Janus.Amd64.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.IfaceAmd64.ConvTnoptr : Janus.Amd64.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.IfaceAmd64.ConvT16 : Janus.Amd64.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.IfaceAmd64.ConvT32 : Janus.Amd64.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.IfaceAmd64.ConvT64 : Janus.Amd64.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.IfaceAmd64.ConvTstring : Janus.Amd64.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.IfaceAmd64.ConvTslice : Janus.Amd64.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.IfaceAmd64.TypeAssert : Janus.Amd64.Program → Nat → IfaceModel → RtReady → Prop)
#check (Janus.Contracts.IfaceAmd64.InterfaceSwitch : Janus.Amd64.Program → Nat → IfaceModel → RtReady → Prop)
