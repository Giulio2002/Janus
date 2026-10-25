// Prints the Lean test vectors of JanusTests/String.lean, computed by the Go runtime itself:
//
//	GOTOOLCHAIN=go1.26.0 go run -ldflags=-checklinkname=0 . > vectors.txt
package main

import (
	"fmt"
	"math/rand"
	"strings"
	_ "unsafe"
)

//go:linkname decoderune runtime.decoderune
func decoderune(s string, k int) (rune, int)

//go:linkname countrunes runtime.countrunes
func countrunes(s string) int

func lst(b []byte) string {
	p := make([]string, len(b))
	for i, x := range b { p[i] = fmt.Sprint(x) }
	return "[" + strings.Join(p, ", ") + "]"
}
func runesOf(s string) string {
	var p []string
	for _, r := range s { p = append(p, fmt.Sprint(uint32(r))) }
	return "[" + strings.Join(p, ", ") + "]"
}

func main() {
	var cases [][]byte
	for b := 0; b < 256; b++ { cases = append(cases, []byte{byte(b)}) }
	edges := []byte{0x00, 0x41, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xED, 0xEF, 0xF0, 0xF4, 0xF5, 0xF7, 0xF8, 0xFF}
	leads := []byte{0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1, 0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xF7}
	for _, a := range leads { for _, b := range edges { cases = append(cases, []byte{a, b}) } }
	for _, a := range leads { for _, b := range edges { for _, c := range []byte{0x41, 0x80, 0xBF, 0xC0} {
		cases = append(cases, []byte{a, b, c}) } } }
	for _, a := range []byte{0xF0, 0xF1, 0xF4, 0xF5, 0xF7} { for _, b := range []byte{0x80, 0x8F, 0x90, 0xBF, 0x41} {
		for _, c := range []byte{0x80, 0xBF, 0x41} { for _, d := range []byte{0x80, 0xBF, 0x41, 0xC0} {
			cases = append(cases, []byte{a, b, c, d}) } } } }
	r := rand.New(rand.NewSource(1))
	for i := 0; i < 300; i++ {
		n := r.Intn(12)
		b := make([]byte, n)
		for j := range b {
			switch r.Intn(3) {
			case 0: b[j] = byte(r.Intn(128))
			case 1: b[j] = byte(0x80 + r.Intn(64))
			default: b[j] = byte(0xC0 + r.Intn(64))
			}
		}
		cases = append(cases, b)
	}
	for _, s := range []string{"héllo, 世界 🌍", "\xed\xa0\x80", "\xf4\x90\x80\x80", "a\xc3", "\xe2\x82\xac\xe2\x82"} {
		cases = append(cases, []byte(s))
	}
	var rl, dl, cl, il []string
	for _, c := range cases {
		rl = append(rl, fmt.Sprintf("(%s, %s)", lst(c), runesOf(string(c))))
		for k := 0; k <= len(c); k++ {
			rr, pos := decoderune(string(c), k)
			dl = append(dl, fmt.Sprintf("(%s, %d, %d, %d)", lst(c), k, uint32(rr), pos))
		}
		cl = append(cl, fmt.Sprintf("(%s, %d)", lst(c), countrunes(string(c))))
	}
	// encoderune through string(v) for int64 v (runtime.intstring)
	vals := []int64{0, 0x41, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xD800, 0xDBFF, 0xDC00, 0xDFFF, 0xE000, 0xFFFD, 0xFFFF,
		0x10000, 0x10FFFF, 0x110000, 0x7FFFFFFF, -1, -0x80000000, 0x80000000, 0x100000041, -0x80000001, 1 << 40}
	for i := 0; i < 200; i++ {
		vals = append(vals, int64(r.Intn(0x120000)))
	}
	for _, v := range vals {
		il = append(il, fmt.Sprintf("(%d, %s)", uint64(v), lst([]byte(stringOf(v)))))
	}
	chunks("range", "List (List Nat × List Nat)", "`(bytes, runes)`: `for range` over the bytes", rl,
		"runes b == r", "(b, r)")
	chunks("decode", "List (List Nat × Nat × Nat × Nat)", "`(bytes, k, rune, pos)`: `runtime.decoderune(s, k)`", dl,
		"decodeRune b k == (r, p)", "(b, k, r, p)")
	chunks("count", "List (List Nat × Nat)", "`(bytes, n)`: `runtime.countrunes(s)`", cl,
		"countRunes b == n", "(b, n)")
	chunks("int", "List (Nat × List Nat)", "`(v, bytes)`: `string(v)` for an `int64` `v` (`runtime.intstring`)", il,
		"encodeRune (intRune (BitVec.ofNat 64 v)) == b", "(v, b)")
}

// chunks prints the vectors as definitions of at most 100 entries, each with its kernel check.
func chunks(name, ty, doc string, xs []string, check, pat string) {
	for c := 0; c*100 < len(xs); c++ {
		hi := (c + 1) * 100
		if hi > len(xs) {
			hi = len(xs)
		}
		fmt.Printf("\n/-- %s, by the Go 1.26 runtime (part %d). -/\ndef %s%d : %s := [\n  %s]\n", doc, c, name, c, ty,
			strings.Join(xs[c*100:hi], ",\n  "))
		fmt.Printf("example : %s%d.all (fun %s => %s) = true := by decide +kernel\n", name, c, pat, check)
	}
}

//go:noinline
func stringOf(v int64) string { return string(v) } //nolint
