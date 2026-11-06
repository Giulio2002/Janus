// This file is named to sort after the others, so that adding it left the addresses of the
// earlier example functions unchanged (some audit fixtures name them).

package basic

import (
	"errors"
	"fmt"
)

// The function below wraps a sentinel with fmt.Errorf and the format the uint256 library uses.
// Its proofs treat fmt.errorf as a contract (Janus/Contracts/Errorf.lean, ErrorfAmd64.lean): the printer
// is not extracted. The operands are constants, so they are boxed in read-only data (no convT64 call).

// errBadLen is the sentinel the error wraps.
var errBadLen = errors.New("bad length")

// ErrWrap returns fmt.Errorf("%w: have %d, want %d bytes", errBadLen, 64, 32).
//
//go:noinline
func ErrWrap() error {
	return fmt.Errorf("%w: have %d, want %d bytes", errBadLen, 64, 32)
}
