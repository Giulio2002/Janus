// Command sys keeps every kernel example alive in the linked binary (janus extract needs the
// functions; the linker drops unreachable ones) and calls each once.
package main

import (
	"os"

	"example.com/sys"
)

func main() {
	n, _ := sys.WriteOut([]byte("hello\n"))
	println(n, sys.Pid() > 0, sys.NowNano() > 0, sys.MustNonNeg(int64(len(os.Args))))
}
