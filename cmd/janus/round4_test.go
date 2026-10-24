package main

import "testing"

// Round 4 D3: report text must not carry terminal control sequences.
func TestTermSafe(t *testing.T) {
	for in, want := range map[string]string{
		"Proof.a\nb":           "Proof.a\nb",
		"x\x1b[2Ky":            "x\\u{1b}[2Ky",
		"x\ry":                 "x\\u{d}y",
		"a‮b":                  "a\\u{202e}b",
		"(256 : BitVec 8) ≠ 0": "(256 : BitVec 8) ≠ 0",
	} {
		if got := termSafe(in); got != want {
			t.Errorf("termSafe(%q) = %q, want %q", in, got, want)
		}
	}
}
