package basic

// The functions below panic, defer and recover. The compiler lowers them to calls of the Go 1.26
// panic runtime (runtime/panic.go: gopanic, gorecover, deferproc, deferreturn, panicBounds) and
// to inline open-coded defers; a nil dereference faults and the runtime's signal handler turns
// the fault into a call of runtime.sigpanic. The proofs treat the runtime functions as contracts
// (docs/RUNTIME-CONTRACTS.md, "Panics, defer, recover").

// Cell is a heap cell for LoadField.
type Cell struct{ V uint64 }

// PanicIf panics with the interface value e when x > 10 and returns x + 1 otherwise. The panic
// value is passed straight to runtime.gopanic (e is already an interface), so no boxing.
//
//go:noinline
func PanicIf(x uint64, e any) uint64 {
	if x > 10 {
		panic(e)
	}
	return x + 1
}

// DeferInc returns x, and a deferred closure (open-coded) increments *p on the way out.
//
//go:noinline
func DeferInc(p *uint64, x uint64) uint64 {
	defer func() { *p++ }()
	return x
}

// RecoverSet returns x for x <= 10; for x > 10 it panics, and the deferred closure recovers the
// panic and sets the named result to 7, so the call returns 7.
//
//go:noinline
func RecoverSet(x uint64) (r uint64) {
	defer func() {
		if recover() != nil {
			r = 7
		}
	}()
	if x > 10 {
		panic(x)
	}
	return x
}

// IndexAt returns xs[i]; out of range it panics with a runtime boundsError.
//
//go:noinline
func IndexAt(xs []uint64, i int) uint64 { return xs[i] }

// LoadField returns c.V; for c == nil the load faults and the runtime panics with its
// nil-dereference error (through runtime.sigpanic).
//
//go:noinline
func LoadField(c *Cell) uint64 { return c.V }

// DeferLoop defers n calls of f (in a loop, so with heap defer records: runtime.deferproc) and
// runs them on return (runtime.deferreturn).
//
//go:noinline
func DeferLoop(f func(), n int) {
	for i := 0; i < n; i++ {
		defer f()
	}
}

// Counter returns a closure that increments *p.
//
//go:noinline
func Counter(p *uint64) func() { return func() { *p++ } }
