package basic

// The functions below use interfaces: boxing a value into an interface, type assertions, type
// switches and interface comparison. The compiler lowers them to calls of the Go 1.26 runtime
// (runtime/iface.go, runtime/alg.go) and to inline probes of the type-assertion and
// interface-switch caches; the proofs treat the runtime functions as contracts
// (docs/RUNTIME-CONTRACTS.md, "Interfaces").

// Box boxes x into an empty interface (runtime.convT64).
//
//go:noinline
func Box(x uint64) any { return x }

// AsHasher asserts that x holds a Hasher (the comma-ok form): the inline cache probe and
// runtime.typeAssert.
//
//go:noinline
func AsHasher(x any) (Hasher, bool) {
	h, ok := x.(Hasher)
	return h, ok
}

// Classify reports which case of a type switch x takes: 0 for nil, 1 for uint64, 2 for string,
// 3 for a Hasher, 4 for anything else (the concrete cases inline, the interface case through
// the interface-switch cache and runtime.interfaceSwitch).
//
//go:noinline
func Classify(x any) uint64 {
	switch x.(type) {
	case nil:
		return 0
	case uint64:
		return 1
	case string:
		return 2
	case Hasher:
		return 3
	default:
		return 4
	}
}

// Equal compares two interface values (runtime.efaceeq when the dynamic types agree).
//
//go:noinline
func Equal(a, b any) bool { return a == b }
