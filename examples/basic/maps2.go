package basic

// The functions below exercise the map runtime entry points of work package R3
// (Janus/Contracts/MapVar.lean, MapStr.lean and their amd64 files): string keys
// (_faststr), generic keys hashed and compared by the key type's functions ([24]byte),
// 4-byte keys (_fast32), pointer keys (_fast64ptr), make with a size hint (makemap) and
// iteration.

// LookupS returns m[k] (0 if absent or m is nil): runtime.mapaccess1_faststr.
//
//go:noinline
func LookupS(m map[string]uint64, k string) uint64 { return m[k] }

// InsertS sets m[k] = v (m non-nil): runtime.mapassign_faststr.
//
//go:noinline
func InsertS(m map[string]uint64, k string, v uint64) { m[k] = v }

// DeleteS removes k from m: runtime.mapdelete_faststr.
//
//go:noinline
func DeleteS(m map[string]uint64, k string) { delete(m, k) }

// LookupK24 returns m[*k] for 24-byte array keys: the generic runtime.mapaccess1, which hashes
// the key with the map type's hasher and compares with the key type's equality.
//
//go:noinline
func LookupK24(m map[[24]byte]uint64, k *[24]byte) uint64 { return m[*k] }

// InsertK24 sets m[*k] = v (m non-nil): the generic runtime.mapassign.
//
//go:noinline
func InsertK24(m map[[24]byte]uint64, k *[24]byte, v uint64) { m[*k] = v }

// Has32 returns m[k] for a map[uint32]bool: runtime.mapaccess1_fast32.
//
//go:noinline
func Has32(m map[uint32]bool, k uint32) bool { return m[k] }

// Set32 sets m[k] = true (m non-nil): runtime.mapassign_fast32.
//
//go:noinline
func Set32(m map[uint32]bool, k uint32) { m[k] = true }

// PNode is a pointer-keyed map's key type.
type PNode struct{ X uint64 }

// InsertPtr sets m[p] = v (m non-nil): runtime.mapassign_fast64ptr.
//
//go:noinline
func InsertPtr(m map[*PNode]uint64, p *PNode, v uint64) { m[p] = v }

// LookupPtr returns m[p]: runtime.mapaccess1_fast64 (pointer keys are 8 bytes).
//
//go:noinline
func LookupPtr(m map[*PNode]uint64, p *PNode) uint64 { return m[p] }

// MakeHint returns make(map[uint64]uint64, n): runtime.makemap (the hint is not a constant).
//
//go:noinline
func MakeHint(n int) map[uint64]uint64 { return make(map[uint64]uint64, n) }
