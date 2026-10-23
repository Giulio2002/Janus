// Command geth-vm-arm64 keeps go-ethereum's core/vm opcode implementations (opAdd, opSub, ...,
// opExp) alive as real, unmodified function bodies, so that Janus can extract and verify them.
//
// The opcode functions are unexported. They are referenced from the per-fork jump tables
// (newFrontierInstructionSet ... newOsakaInstructionSet), which the exported
// vm.LookupInstructionSet builds. Calling it with rules derived from os.Args makes every
// table constructor reachable, so the linker keeps every opcode function they store, compiled
// exactly as in any other importer of github.com/ethereum/go-ethereum/core/vm.
package main

import (
	"fmt"
	"os"

	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/params"
)

func main() {
	// Every fork flag depends on the command line, so no constructor is provably dead.
	on := func(i int) bool { return len(os.Args) > i && os.Args[i] == "1" }
	rules := params.Rules{
		IsHomestead: on(1), IsEIP150: on(2), IsEIP155: on(3), IsEIP158: on(4),
		IsByzantium: on(5), IsConstantinople: on(6), IsPetersburg: on(7), IsIstanbul: on(8),
		IsBerlin: on(9), IsLondon: on(10), IsMerge: on(11), IsShanghai: on(12),
		IsCancun: on(13), IsPrague: on(14), IsOsaka: on(15), IsAmsterdam: on(16), IsBogota: on(17),
	}
	jt, err := vm.LookupInstructionSet(rules)
	defined := 0
	for _, op := range jt {
		if op != nil && op.HasCost() {
			defined++
		}
	}
	fmt.Println("opcodes with a cost:", defined, err)
}
