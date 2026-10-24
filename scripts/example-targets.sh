#!/usr/bin/env bash
# Print the extra `janus extract` arguments of an examples/basic function, one per line: the
# dynamic call targets its theorem states (docs/PROOFS.md, "Dynamic calls"). Nothing for most
# functions. Used by scripts/verify-examples.sh and scripts/build-examples-amd64.sh.
case "$1" in
  HashWith) # the static itabs of the two Hasher implementations
    printf '%s\n' --targets \
      'go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher,go:itab.*example.com/basic.RotHasher,example.com/basic.Hasher' ;;
  MapSum) # the closure AffineSum passes to it
    printf '%s\n' --targets example.com/basic.AffineSum.func1 ;;
esac
