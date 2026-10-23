package basic

import "math/bits"

//go:noinline
func Add(x, y uint64) uint64 { return x + y }

//go:noinline
func Max(x, y uint64) uint64 {
	if x > y {
		return x
	}
	return y
}

//go:noinline
func Add128(xh, xl, yh, yl uint64) (uint64, uint64) {
	lo, c := bits.Add64(xl, yl, 0)
	hi, _ := bits.Add64(xh, yh, c)
	return hi, lo
}

//go:noinline
func Mul64(x, y uint64) (uint64, uint64) { return bits.Mul64(x, y) }

//go:noinline
func Sum(xs []uint64) uint64 {
	var s uint64
	for _, x := range xs {
		s += x
	}
	return s
}

//go:noinline
func Get(xs []uint64, i int) uint64 { return xs[i] }

//go:noinline
func Add256(z, x, y *[4]uint64) {
	var c uint64
	z[0], c = bits.Add64(x[0], y[0], 0)
	z[1], c = bits.Add64(x[1], y[1], c)
	z[2], c = bits.Add64(x[2], y[2], c)
	z[3], _ = bits.Add64(x[3], y[3], c)
}
