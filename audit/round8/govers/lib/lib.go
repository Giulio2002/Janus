// Package lib defines runtime·panicSimdImm in assembly (zero_arm64.s): a function that returns 0.
// Round 8 G3 (docs/AUDIT-ROUND8.md).
package lib

// Zero returns 0, through runtime·panicSimdImm.
func Zero() uint64
