import Janus.Spec.Map

/-!
# `sync.Pool`: the layout compiled code depends on (Go 1.26)

The vocabulary of the `sync.Pool` contracts (`Janus.Contracts.Pool`, arm64, and
`Janus.Contracts.PoolAmd64`). Both ISAs use `Janus.Arm64.Memory`, so everything here is
ISA-independent.

`type Pool struct { noCopy noCopy; local unsafe.Pointer; localSize uintptr; victim
unsafe.Pointer; victimSize uintptr; New func() any }` (`sync/pool.go`): 40 bytes, `New` at offset
32 (`noCopy` is empty). Compiled callers only take the pool's address (`&stackPool`); the fields
are read and written by `Get` and `Put` alone, except `New`, which the program sets. The
contracts name `New` because `Get` calls it when it finds nothing and it is set (arbitrary Go
code): `PoolGetLive` requires it nil.
-/

namespace Janus.Spec.Pool

/-- The size of a `sync.Pool` value (Go 1.26, both 64-bit ISAs). -/
def poolBytes : Nat := 40

/-- The offset of `Pool.New` (a func value; nil when `0`). -/
def newOffset : Nat := 32

end Janus.Spec.Pool
