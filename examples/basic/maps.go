package basic

// The functions below use Go maps. The compiler lowers map operations to calls into the
// runtime's Swiss-table implementation (internal/runtime/maps); the proofs treat those runtime
// functions as contracts (docs/RUNTIME-CONTRACTS.md, "Maps").

// Lookup returns m[k] and whether k is present (the zero value and false if it is not, or if m
// is nil).
//
//go:noinline
func Lookup(m map[uint64]uint64, k uint64) (uint64, bool) {
	v, ok := m[k]
	return v, ok
}

// Insert sets m[k] = v. It panics if m is nil.
//
//go:noinline
func Insert(m map[uint64]uint64, k, v uint64) { m[k] = v }

// InsertGet sets m[k] = v and reads m[k] back.
//
//go:noinline
func InsertGet(m map[uint64]uint64, k, v uint64) uint64 {
	m[k] = v
	return m[k]
}

// Delete removes k from m (nothing happens if k is absent or m is nil).
//
//go:noinline
func Delete(m map[uint64]uint64, k uint64) { delete(m, k) }

// SumValues returns the sum (mod 2^64) of the values of m, in the map's (randomised)
// iteration order.
//
//go:noinline
func SumValues(m map[uint64]uint64) uint64 {
	var s uint64
	for _, v := range m {
		s += v
	}
	return s
}

// CountKeys returns len(m).
//
//go:noinline
func CountKeys(m map[uint64]uint64) int { return len(m) }

// LookupKey16 returns m[*k] and whether *k is present, for 16-byte array keys (the generic
// map access path).
//
//go:noinline
func LookupKey16(m map[[16]byte]uint64, k *[16]byte) (uint64, bool) {
	v, ok := m[*k]
	return v, ok
}

// NewMap returns a new, empty map (make with no size hint).
//
//go:noinline
func NewMap() map[uint64]uint64 { return make(map[uint64]uint64) }

// ClearMap removes every entry of m (nothing happens if m is nil).
//
//go:noinline
func ClearMap(m map[uint64]uint64) { clear(m) }
