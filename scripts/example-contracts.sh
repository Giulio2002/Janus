# Sourced by scripts/verify-examples.sh: the symbol an example proves things about (default
# example.com/basic.<Name>). The extraction arguments are in scripts/example-targets.sh.
example_symbol() {
  case "$1" in
    MallocFast) echo runtime.mallocgc ;;
    # a runtime function verified on its own (examples/proofs/MapAccess1Small.lean)
    MapAccess1Small) echo runtime.mapaccess1_fast64 ;;
    # runtime functions proved to meet their contracts (Janus/Contracts/WriteBarrier.lean)
    WriteBarrier) echo runtime.gcWriteBarrier1 ;;
    *) echo "example.com/basic.$1" ;;
  esac
}
