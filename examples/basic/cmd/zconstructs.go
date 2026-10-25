package main

import "example.com/basic"

// The language-construct examples (examples/basic/zconstructs.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.Triangle, basic.GotoSum, basic.Find2D, basic.RowsWith, basic.Log2,
		basic.TotalMeters, basic.TotalFeet, basic.Fact, basic.SumBelow, basic.ReverseArray,
		basic.DivMod10, basic.SwapBig, basic.Compose, basic.DotBoth, basic.BitMerge,
		basic.Shifts, basic.MinMax, basic.ClearArray, basic.IterSum, basic.Sum3, basic.AlignUp,
		basic.Slice3, basic.Slice2, basic.Mod, basic.IncTwice, basic.MakeAdder)
}
