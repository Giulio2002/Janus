// Command rtprint is the Go side of the rt-print differential test (audit/rt-print/run.sh).
//
// It generates a deterministic list of test cases from a seed and, for each case, prints ONE
// line with the builtin println (runtime/print.go, written to stderr by the runtime itself):
//
//	println(id, value)    ->  "<id> <value>\n"
//
// (plus a few multi-operand / print-without-ln shapes, see below). On stdout it writes the
// case list, one case per line, which audit/rt-print/Diff.lean reads to produce the expected
// stderr bytes from the Lean spec Janus.Spec.Print. Case kinds and their fields (hex):
//
//	u V        println(id, uint64(V))
//	i V        println(id, int64(V))
//	b V        println(id, V != 0)
//	h V        println(id, uintptr(V))                  printuint (NOT printhex: walk/builtin.go
//	                                                    sends uintptr to printuint; printhex is
//	                                                    only for the runtime's own `hex` type)
//	p V        println(id, unsafe.Pointer(uintptr(V)))  printpointer = printhex
//	d V        println(id, math.Float64frombits(V))
//	f V        println(id, math.Float32frombits(V))
//	c RE IM    println(id, complex(f64 RE, f64 IM))
//	k RE IM    println(id, complex(f32 RE, f32 IM))
//	s HEX      println(id, string(bytes))               "-" for the empty string
//	l P L C    println(id, []byte with header {P, L, C})
//	e T D      println(id, any with words {T, D})       printeface
//	I T D      println(id, interface{M()} {T, D})       printiface
//	M I F B S  println(id, int64(I), float64 F, B != 0, string S)
//	P F G      print(id, "\t", float64 F, float32 G, "\n")
//
// The garbage collector is switched off (and run.sh sets GODEBUG=invalidptr=0) because the
// pointer-typed cases carry fabricated addresses (kept outside the Go heap range, see safePtr).
//
// Usage: rtprint [-seed S] [-n N]   (N = random float64 bit patterns; the other random counts
// scale with it).
package main

import (
	"bufio"
	"flag"
	"fmt"
	"math"
	"math/rand/v2"
	"os"
	"runtime/debug"
	"strconv"
	"unsafe"
)

var (
	out *bufio.Writer
	id  int
	rng *rand.Rand
)

type iface interface{ M() }

func next() int { i := id; id++; return i }

func caseU(v uint64) { fmt.Fprintf(out, "u %x\n", v); println(next(), v) }
func caseI(v uint64) { fmt.Fprintf(out, "i %x\n", v); println(next(), int64(v)) }
func caseB(v bool) {
	n := 0
	if v {
		n = 1
	}
	fmt.Fprintf(out, "b %x\n", n)
	println(next(), v)
}
func caseH(v uint64) { fmt.Fprintf(out, "h %x\n", v); println(next(), uintptr(v)) }

//go:noinline
func caseP(v uint64) {
	v = safePtr(v)
	fmt.Fprintf(out, "p %x\n", v)
	println(next(), unsafe.Pointer(uintptr(v)))
}
func caseD(v uint64) { fmt.Fprintf(out, "d %x\n", v); println(next(), math.Float64frombits(v)) }
func caseF(v uint32) { fmt.Fprintf(out, "f %x\n", v); println(next(), math.Float32frombits(v)) }
func caseC(re, im uint64) {
	fmt.Fprintf(out, "c %x %x\n", re, im)
	println(next(), complex(math.Float64frombits(re), math.Float64frombits(im)))
}
func caseK(re, im uint32) {
	fmt.Fprintf(out, "k %x %x\n", re, im)
	println(next(), complex(math.Float32frombits(re), math.Float32frombits(im)))
}
func hexStr(s string) string {
	if s == "" {
		return "-"
	}
	return fmt.Sprintf("%x", s)
}
func caseS(s string) { fmt.Fprintf(out, "s %s\n", hexStr(s)); println(next(), s) }

type sliceHdr struct {
	p    uintptr
	l, c int
}

//go:noinline
func caseL(p, l, c uint64) {
	p = safePtr(p)
	fmt.Fprintf(out, "l %x %x %x\n", p, l, c)
	h := sliceHdr{uintptr(p), int(l), int(c)}
	s := *(*[]byte)(unsafe.Pointer(&h))
	println(next(), s)
}

//go:noinline
func caseE(t, d uint64) {
	t, d = safePtr(t), safePtr(d)
	fmt.Fprintf(out, "e %x %x\n", t, d)
	w := [2]uintptr{uintptr(t), uintptr(d)}
	e := *(*any)(unsafe.Pointer(&w))
	println(next(), e)
}

//go:noinline
func caseIface(t, d uint64) {
	t, d = safePtr(t), safePtr(d)
	fmt.Fprintf(out, "I %x %x\n", t, d)
	w := [2]uintptr{uintptr(t), uintptr(d)}
	e := *(*iface)(unsafe.Pointer(&w))
	println(next(), e)
}
func caseM(i, f uint64, b bool, s string) {
	n := 0
	if b {
		n = 1
	}
	fmt.Fprintf(out, "M %x %x %x %s\n", i, f, n, hexStr(s))
	println(next(), int64(i), math.Float64frombits(f), b, s)
}
func caseP2(f uint64, g uint32) {
	fmt.Fprintf(out, "P %x %x\n", f, g)
	print(next(), "\t", math.Float64frombits(f), math.Float32frombits(g), "\n")
}

// safePtr keeps a fabricated address outside [0xc000000000, 0xc000000000 + 2^40) (the Go
// heap/stack arena hint on linux), so a stack copy cannot mistake it for a pointer into the
// stack being moved and rewrite it. Small values (< 4096) are fine with GODEBUG=invalidptr=0.
func safePtr(v uint64) uint64 {
	if v >= 0xc000000000 && v < 0xc000000000+1<<40 {
		v |= 1 << 63
	}
	return v
}

// --- value pools -----------------------------------------------------------------------------

func f64bits(s string) uint64 {
	f, err := strconv.ParseFloat(s, 64)
	if err != nil && f == 0 {
		return 0
	}
	return math.Float64bits(f)
}
func f32bits(s string) uint32 {
	f, err := strconv.ParseFloat(s, 32)
	if err != nil && f == 0 {
		return 0
	}
	return math.Float32bits(float32(f))
}

func special64() []uint64 {
	v := []uint64{
		0, 1 << 63, 0x7ff0000000000000, 0xfff0000000000000,
		0x7ff8000000000000, 0xfff8000000000000, 0x7ff0000000000001, 0x7ff4000000000000,
		0x7fffffffffffffff, 0xffffffffffffffff, 0x7ff8000000000001,
		1, 2, 3, 0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001, 0x7fefffffffffffff,
		0x3ff0000000000000, 0x3fe0000000000000, 0x4000000000000000,
	}
	for _, s := range []string{"1e21", "1e20", "1e-4", "1e-5", "1e6", "1e5", "999999", "999999.5",
		"9999995", "100000", "123456", "1234567", "0.0001", "0.00001", "0.000123", "0.0000123",
		"9.999999999999999e20", "9.999999999999999e-5", "5e-324", "2.2250738585072014e-308",
		"1.7976931348623157e308", "0.1", "0.2", "0.3", "1.5", "2.5", "123.456", "3.141592653589793",
		"9007199254740992", "9007199254740993", "9007199254740991", "4503599627370496.5",
		"1e23", "8.41e21", "5e-310", "1e-320", "4.9406564584124654e-324"} {
		b := f64bits(s)
		for d := -3; d <= 3; d++ {
			v = append(v, b+uint64(d))
		}
	}
	return v
}

func special32() []uint32 {
	v := []uint32{
		0, 1 << 31, 0x7f800000, 0xff800000, 0x7fc00000, 0xffc00000, 0x7f800001, 0x7fa00000,
		0x7fffffff, 0xffffffff, 1, 2, 3, 0x007fffff, 0x00800000, 0x00800001, 0x7f7fffff,
		0x3f800000, 0x39800000, 0xb9800000,
	}
	for _, s := range []string{"1e21", "1e-4", "1e-5", "1e6", "1e5", "999999", "999999.5",
		"9999995", "100000", "123456", "1234567", "0.0001", "0.00001", "1e-45", "1.1754944e-38",
		"3.4028235e38", "0.1", "0.2", "0.3", "16777216", "16777217", "33554434", "2097152.25",
		"3.1415927", "1e10", "1e38", "1e-38", "7e-45"} {
		b := f32bits(s)
		for d := -3; d <= 3; d++ {
			v = append(v, b+uint32(d))
		}
	}
	return v
}

// interesting ints: 0, ±1, powers of 2 and 10 and their neighbours, extremes.
func specialInts() []uint64 {
	v := []uint64{0, 1, math.MaxUint64, 1 << 63, 1<<63 - 1, 1<<63 + 1}
	for k := 0; k < 64; k++ {
		p := uint64(1) << k
		v = append(v, p-1, p, p+1, -p, -p+1)
	}
	p := uint64(1)
	for k := 0; k < 20; k++ {
		v = append(v, p-1, p, p+1, -p, -(p - 1), p*9, p*99/10)
		p *= 10
	}
	return v
}

// randBitsLen returns a random integer with a uniformly random bit length.
func randBitsLen() uint64 {
	n := rng.IntN(65)
	if n == 0 {
		return 0
	}
	return rng.Uint64()>>(64-n) | 1<<(n-1)
}

func randString() string {
	n := rng.IntN(12)
	rs := make([]rune, 0, n)
	for range n {
		var r rune
		switch rng.IntN(5) {
		case 0, 1:
			r = rune(0x20 + rng.IntN(0x5f))
		case 2:
			r = rune(rng.IntN(0x20)) // controls (but not '\n', which would split the line)
			if r == '\n' {
				r = '\t'
			}
		case 3:
			r = rune(0x80 + rng.IntN(0x800-0x80))
		default:
			r = rune(0x800 + rng.IntN(0x10ffff-0x800))
			if r >= 0xd800 && r < 0xe000 {
				r = 0xfffd
			}
		}
		rs = append(rs, r)
	}
	return string(rs)
}

// niceDecimal64 is k*10^e for a random k of 1..17 digits, parsed (round to nearest even).
func niceDecimal64() uint64 {
	nd := 1 + rng.IntN(17)
	k := rng.Int64N(pow10(nd)) + 1
	e := rng.IntN(650) - 340
	return f64bits(fmt.Sprintf("%de%d", k, e))
}
func niceDecimal32() uint32 {
	nd := 1 + rng.IntN(9)
	k := rng.Int64N(pow10(nd)) + 1
	e := rng.IntN(95) - 55
	return f32bits(fmt.Sprintf("%de%d", k, e))
}
func pow10(n int) int64 {
	p := int64(1)
	for range n {
		p *= 10
	}
	return p
}

func main() {
	seed := flag.Uint64("seed", 1, "PRNG seed")
	n := flag.Int("n", 200000, "random float64 bit patterns (other random counts scale with it)")
	flag.Parse()
	debug.SetGCPercent(-1)
	rng = rand.New(rand.NewPCG(*seed, 0x9e3779b97f4a7c15))
	out = bufio.NewWriterSize(os.Stdout, 1<<20)
	defer out.Flush()
	N := *n

	// ---- integers, bools, hex, pointers
	for _, v := range specialInts() {
		caseU(v)
		caseI(v)
		caseH(v)
		caseP(v)
	}
	for range N / 8 {
		caseU(randBitsLen())
		caseI(randBitsLen())
		caseI(-randBitsLen())
		caseH(randBitsLen())
		caseP(randBitsLen())
	}
	caseB(true)
	caseB(false)

	// ---- strings
	for _, s := range []string{"", " ", "a", "hello, world", "\t", "\x00", "\x7f", "é", "日本語", "\U0001F600", "\\\"", "%v%d"} {
		caseS(s)
	}
	for range N / 20 {
		caseS(randString())
	}

	// ---- slices and interfaces
	ints := specialInts()
	for range N / 20 {
		pick := func() uint64 {
			if rng.IntN(2) == 0 {
				return ints[rng.IntN(len(ints))]
			}
			return randBitsLen()
		}
		caseL(pick(), pick(), pick())
		caseE(pick(), pick())
		caseIface(pick(), pick())
	}
	caseL(0, 0, 0)
	caseE(0, 0)
	caseIface(0, 0)

	// ---- float64
	sp64 := special64()
	for _, v := range sp64 {
		caseD(v)
	}
	// every exponent (both signs) with edge and random significands; mantissa 0 covers every
	// power of two, i.e. every Dragonbox shorter-interval case.
	for exp := uint64(0); exp < 2048; exp++ {
		for _, m := range []uint64{0, 1, 2, 3, 1 << 51, 1<<52 - 1, 1<<52 - 2, rng.Uint64() >> 12, rng.Uint64() >> 12} {
			caseD(exp<<52 | m)
			caseD(1<<63 | exp<<52 | m)
		}
	}
	for p := -345; p <= 310; p++ {
		b := f64bits(fmt.Sprintf("1e%d", p))
		for d := -2; d <= 2; d++ {
			caseD(b + uint64(d))
		}
		caseD(f64bits(fmt.Sprintf("5e%d", p)))
		caseD(f64bits(fmt.Sprintf("2.5e%d", p)))
	}
	for i := 0; i <= 20000; i++ {
		caseD(math.Float64bits(float64(i)))
		caseD(math.Float64bits(float64(i) + 0.5))
		caseD(math.Float64bits(float64(i) / 64))
	}
	for k := int64(-2000); k <= 2000; k++ {
		caseD(math.Float64bits(float64(1<<53 + k)))
		caseD(math.Float64bits(1e21 + float64(k)*131072))
		caseD(math.Float64bits(1e-4) + uint64(k))
		caseD(math.Float64bits(1e-5) + uint64(k))
		caseD(math.Float64bits(1e6) + uint64(k))
	}
	for range N {
		caseD(rng.Uint64())
	}
	for range N / 2 {
		caseD(uint64(rng.IntN(2048))<<52 | rng.Uint64()>>12 | uint64(rng.IntN(2))<<63)
		caseD(niceDecimal64())
		caseD(math.Float64bits(float64(int64(randBitsLen()))))
	}

	// ---- float32
	sp32 := special32()
	for _, v := range sp32 {
		caseF(v)
	}
	for exp := uint32(0); exp < 256; exp++ {
		for _, m := range []uint32{0, 1, 2, 3, 1 << 22, 1<<23 - 1, 1<<23 - 2, rng.Uint32() >> 9, rng.Uint32() >> 9} {
			caseF(exp<<23 | m)
			caseF(1<<31 | exp<<23 | m)
		}
	}
	for p := -46; p <= 39; p++ {
		b := f32bits(fmt.Sprintf("1e%d", p))
		for d := -2; d <= 2; d++ {
			caseF(b + uint32(d))
		}
		caseF(f32bits(fmt.Sprintf("5e%d", p)))
		caseF(f32bits(fmt.Sprintf("2.5e%d", p)))
	}
	// contiguous runs: around 1.0, around 2^-12, the bottom of the subnormals, 2^21 (ties)
	for _, base := range []uint32{0x3f800000 - 4096, 0x39800000 - 4096, 0, 0x4a000000} {
		for d := uint32(0); d < 8192; d++ {
			caseF(base + d)
		}
	}
	for range N {
		caseF(rng.Uint32())
	}
	for range N / 2 {
		caseF(uint32(rng.IntN(256))<<23 | rng.Uint32()>>9 | uint32(rng.IntN(2))<<31)
		caseF(niceDecimal32())
		caseF(math.Float32bits(float32(int32(randBitsLen()))))
	}

	// ---- complex
	for _, re := range sp64[:24] {
		for _, im := range sp64[:24] {
			caseC(re, im)
		}
	}
	for _, re := range sp32[:24] {
		for _, im := range sp32[:24] {
			caseK(re, im)
		}
	}
	for range N / 10 {
		caseC(rng.Uint64(), rng.Uint64())
		caseC(sp64[rng.IntN(len(sp64))], niceDecimal64())
		caseK(rng.Uint32(), rng.Uint32())
		caseK(sp32[rng.IntN(len(sp32))], niceDecimal32())
	}

	// ---- multi-operand println and print without ln
	for range N / 20 {
		caseM(randBitsLen(), rng.Uint64(), rng.IntN(2) == 0, randString())
		caseP2(rng.Uint64(), rng.Uint32())
	}
}
