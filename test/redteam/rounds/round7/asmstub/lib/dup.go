//go:build janusdup

package lib

import _ "unsafe"

// Round 7 G1d (built only with -tags janusdup): a //go:linkname push gives a second function
// symbol named exactly runtime.morestack_noctxt.abi0, the name of a real runtime stub.
//
//go:noinline
//go:linkname dupMorestack runtime.morestack_noctxt.abi0
func dupMorestack() uint64 { return 7 }

// Dup keeps dupMorestack alive.
func Dup() uint64 { return dupMorestack() }
