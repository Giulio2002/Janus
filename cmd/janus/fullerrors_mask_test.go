package main

import "testing"

// Regression (FV-SD, fv-uint256 SetFromDecimal): with --full-errors, the rerun of the proof module after a failed
// Lake build reported only "object file ... of module SfdTopI does not exist" and replaced the build's real failure.
func TestFullRerunUsable(t *testing.T) {
	missing := "stage/p/lean/Fv256/Amd64/SetFromDecimal.lean:1:0: error: object file 'stage/p/lean/.lake/build/lib/lean/Fv256/Amd64/SfdTopI.olean' of module Fv256.Amd64.SfdTopI does not exist\n"
	buildKilled := "error: Fv256.Amd64.SfdTeSum0: Lean exited with code 137\nerror: build failed\n"
	buildLean := "stage/p/lean/Fv256/Amd64/SfdTeSum0.lean:10:2: error: maximum recursion depth has been reached\n"
	real := "stage/p/lean/Fv256/Amd64/SetFromDecimal.lean:12:4: error: unsolved goals\n"
	cases := []struct {
		name, build, full string
		want              bool
	}{
		{"rerun only misses an olean", buildKilled, missing, false},
		{"rerun misses an olean, build has Lean error", buildLean, missing, false},
		{"rerun has no errors, build has", buildLean, "warning: x\n", false},
		{"rerun reproduces a real error", buildLean, real, true},
		{"build itself missing-olean", missing, missing, true},
	}
	for _, c := range cases {
		if got := fullRerunUsable(c.build, c.full); got != c.want {
			t.Errorf("%s: fullRerunUsable = %v, want %v", c.name, got, c.want)
		}
	}
}
