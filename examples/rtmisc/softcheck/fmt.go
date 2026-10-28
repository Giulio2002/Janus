package softcheck

import "fmt"

func fmtCase(op byte, f, g, want, got uint64) string {
	return fmt.Sprintf("%#016x %c %#016x: IEEE %#016x, runtime %#016x", f, op, g, want, got)
}
