package main

import "example.com/basic"

// The map examples (examples/basic/maps.go): kept alive through Keep, which main prints.
func init() {
	Keep = append(Keep, basic.Lookup, basic.Insert, basic.InsertGet, basic.Delete,
		basic.SumValues, basic.CountKeys, basic.LookupKey16, basic.NewMap, basic.ClearMap)
}
