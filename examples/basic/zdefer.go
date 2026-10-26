package basic

import "runtime"

// The functions below exercise the rest of the Go 1.26 panic/defer runtime (runtime/panic.go):
// several pending deferred calls in one frame (open-coded with several deferBits bits, and stack
// and heap _defer records in one frame), nested panics, recover() during a nested panic,
// runtime.Goexit, and a defer inside a range-over-func loop body (deferrangefunc, deferprocat).
// The proofs treat the runtime functions as pinned contracts (docs/RUNTIME-CONTRACTS.md,
// "Panics, defer, recover").

// DeferOrder has three open-coded defers (deferBits bits 0, 1 and 2). They run in LIFO order:
// on the normal return (x <= 10) the function itself calls them at its exit, on panic(e)
// (x > 10) runtime.gopanic calls them; either way *p ends as ((*p*10+3)*10+2)*10+1.
//
//go:noinline
func DeferOrder(p *uint64, x uint64, e any) uint64 {
	defer func() { *p = *p*10 + 1 }()
	defer func() { *p = *p*10 + 2 }()
	defer func() { *p = *p*10 + 3 }()
	if x > 10 {
		panic(e)
	}
	return x
}

// DeferMid has three open-coded defers, the middle one recovers. On panic(e) the runtime calls
// the third (it adds 3), then the second, which recovers; the frame resumes at its deferreturn
// call, and runtime.deferreturn calls the first (it multiplies by 10), still pending in deferBits.
// The call returns 1 with *p = (*p+3)*10.
//
//go:noinline
func DeferMid(p *uint64, e any) (r uint64) {
	defer func() { *p = *p * 10 }()
	defer func() {
		if recover() != nil {
			r = 1
		}
	}()
	defer func() { *p = *p + 3 }()
	panic(e)
}

// Acc is the package variable DeferMix and RangeDefer's deferred calls update (their deferred
// functions capture nothing, so no closure is allocated).
var Acc uint64

// accAdd2 appends the digit 2 to Acc.
//
//go:noinline
func accAdd2() { Acc = Acc*10 + 2 }

// accAdd1 appends the digit 1 to Acc.
//
//go:noinline
func accAdd1() { Acc = Acc*10 + 1 }

// DeferMix mixes a stack _defer record (the defer outside the loop: runtime.deferprocStack) and
// heap records (the defer in the loop: runtime.deferproc) in one frame; a loop defer disables
// open-coding for the whole function. runtime.deferreturn (on return) or runtime.gopanic (on
// panic(e), x > 10) runs them in LIFO order: the two heap records, then the stack record, so Acc
// ends as ((Acc*10+2)*10+2)*10+1.
//
//go:noinline
func DeferMix(x uint64, e any) uint64 {
	defer accAdd1()
	for i := 0; i < 2; i++ {
		defer accAdd2()
	}
	if x > 10 {
		panic(e)
	}
	return x
}

// NestedPanic: panic(e1) runs the second deferred call, which panics with e2 while e1 is
// unwinding; e2 replaces e1 (it aborts it), runs the remaining deferred call (*p = 1) and leaves
// the frame. The call panics with e2, and the goroutine's panic chain is e2 on top of the aborted e1
// (unrecovered, Go 1.26 prints both: "panic: e1\n\tpanic: e2").
//
//go:noinline
func NestedPanic(p *uint64, e1, e2 any) {
	defer func() { *p = 1 }()
	defer func() { panic(e2) }()
	panic(e1)
}

// NestedRecover: as NestedPanic, but the remaining deferred call recovers; recover() returns
// the nested panic's value e2 (it is called directly by the deferred call the e2 panic runs),
// which recovers both panics, and the call returns 7.
//
//go:noinline
func NestedRecover(e1, e2 any) (r uint64) {
	defer func() {
		if recover() != nil {
			r = 7
		}
	}()
	defer func() { panic(e2) }()
	panic(e1)
}

// GoexitDefer calls runtime.Goexit: the deferred call runs, its recover() returns nil (a
// Goexit is not a panic, it cannot be recovered), so it adds 1 to *p; then the goroutine
// terminates: GoexitDefer never returns, and the store after Goexit never happens.
//
//go:noinline
func GoexitDefer(p *uint64) {
	defer func() {
		if recover() != nil {
			*p = 99
		} else {
			*p = *p + 1
		}
	}()
	runtime.Goexit()
	*p = 5
}

// count2 is a range-over-func iterator yielding 1 and 2.
//
//go:noinline
func count2(yield func(uint64) bool) {
	if !yield(1) {
		return
	}
	yield(2)
}

// RangeDefer defers a call in the body of a range-over-func loop. The defer belongs to
// RangeDefer's frame, not the body closure's: RangeDefer gets a token from
// runtime.deferrangefunc, the body records each deferred call on it with runtime.deferprocat,
// and RangeDefer's exit (runtime.deferreturn) runs them in LIFO order: Acc ends as
// (Acc*10+2)*10+1.
//
//go:noinline
func RangeDefer() {
	for x := range count2 {
		if x == 1 {
			defer accAdd1()
		} else {
			defer accAdd2()
		}
	}
}
