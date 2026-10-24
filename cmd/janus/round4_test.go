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
		// round 7 H1: every format (Cf) character, not only overrides and isolates
		"a\u202bb\u202cc": "a\\u{202b}b\\u{202c}c", "o\u200b": "o\\u{200b}", "x\u200fy": "x\\u{200f}y",
		"∀ (ο : BitVec 64)": "∀ (ο : BitVec 64)",
	} {
		if got := termSafe(in); got != want {
			t.Errorf("termSafe(%q) = %q, want %q", in, got, want)
		}
	}
}
