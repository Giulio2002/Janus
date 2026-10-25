// Command cmd is the example binary of package avx512 (artifacts/examples-amd64-avx512).
package main

import (
	"fmt"

	"example.com/basic/avx512"
)

func main() {
	var b [64]byte
	b[41] = 'x'
	fmt.Println(avx512.Search64(&b[0], 8, 'x'), avx512.Search64(&b[0], 5, 'x'), avx512.Search64(&b[0], 6, 'x'))
}
