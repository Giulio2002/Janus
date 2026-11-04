package stubdemo

// Push is append(s, b) for a byte slice: runtime.growslice when the slice is full, then a store.
//
//go:noinline
func Push(s []byte, b byte) []byte {
	return append(s, b)
}

// CopyBytes is copy(dst, src): runtime.memmove of min(len(dst), len(src)) bytes.
//
//go:noinline
func CopyBytes(dst, src []byte) int {
	return copy(dst, src)
}

// Zero is clear(s): runtime.memclrNoHeapPointers.
//
//go:noinline
func Zero(s []byte) {
	clear(s)
}
