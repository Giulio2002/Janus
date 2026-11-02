// Command bitscan keeps the bit-scan example functions alive in the linked binary (see
// examples/basic/cmd).
package main

import (
	"os"

	"example.com/basic/bitscan"
)

// Keep references every example function as a func value.
var Keep = []any{bitscan.BitLen64, bitscan.TrailingZeros64, bitscan.ByteLen, bitscan.BitLen32}

func main() {
	n := uint64(len(os.Args))
	println(len(Keep), bitscan.BitLen64(n), bitscan.TrailingZeros64(n), bitscan.ByteLen(n), bitscan.BitLen32(uint32(n)))
}
