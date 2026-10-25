// Command cmd is the example binary of package sse (artifacts/examples-amd64-sse).
package main

import (
	"fmt"
	"hash/crc32"

	"example.com/basic/sse"
)

func main() {
	var b [32]byte
	b[17] = 'x'
	var q [16]byte
	copy(q[:], "0123456789abcdef")
	fmt.Println(sse.Index32(&b, 'x'), sse.CRC32C16(0, &q) == crc32.Update(0, crc32.MakeTable(crc32.Castagnoli), q[:]))
}
