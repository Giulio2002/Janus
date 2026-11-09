# Sourced by scripts/verify-examples.sh: the symbol an example proves things about (default
# example.com/basic.<Name>). The extraction arguments are in scripts/example-targets.sh.
example_symbol() {
  case "$1" in
    MallocFast) echo runtime.mallocgc ;;
    # a runtime function verified on its own (examples/proofs/MapAccess1Small.lean)
    MapAccess1Small) echo runtime.mapaccess1_fast64 ;;
    # the compiler-generated hash and equality functions of a struct key (examples/basic/rteq.go)
    HashFKey) echo 'type:.hash.example.com/basic.FKey' ;;
    EqFKey) echo 'type:.eq.example.com/basic.FKey' ;;
    # the runtime's equality, hashing and typed-memory functions, verified on their own
    Alg*|Mbar*) runtime_symbol "$1" ;;
    # runtime functions proved to meet their contracts (Janus/Contracts/WriteBarrier.lean)
    WriteBarrier) echo runtime.gcWriteBarrier1 ;;
    *) echo "example.com/basic.$1" ;;
  esac
}

# The runtime functions of runtime/alg.go and runtime/mbarrier.go (and memequal) whose machine
# code a proof verifies (examples/proofs/Alg*.lean, Mbar*.lean; examples/proofs-amd64/Alg*/,
# Mbar*/), by example name. AlgMemequal and AlgMemequalVarlen (internal/bytealg/equal_*.s) are arm64
# only: on amd64 both run memeqbody, which reads up to 7 bytes around a short input.
runtime_examples="AlgMemequal0 AlgMemequal8 AlgMemequal16 AlgMemequal32 AlgMemequal64 AlgMemequal128
  AlgF32equal AlgF64equal AlgC64equal AlgC128equal AlgStrequal AlgInterequal
  AlgNilinterequal AlgMemhash0 AlgMemhash8 AlgMemhash16 AlgMemhash128 AlgMemhashVarlen AlgF32hash
  AlgF64hash AlgC64hash AlgC128hash AlgInterhash AlgNilinterhash MbarTypedmemmove MbarTypedmemclr
  MbarMemclrHasPointers"
runtime_examples_arm64_only="AlgMemequal AlgMemequalVarlen"

# runtime_symbol NAME: the runtime function an Alg*/Mbar* example verifies.
runtime_symbol() {
  case "$1" in
    AlgMemequal) echo runtime.memequal ;;
    AlgMemequalVarlen) echo runtime.memequal_varlen ;;
    AlgMemhashVarlen) echo runtime.memhash_varlen ;;
    MbarTypedmemmove) echo runtime.typedmemmove ;;
    MbarTypedmemclr) echo runtime.typedmemclr ;;
    MbarMemclrHasPointers) echo runtime.memclrHasPointers ;;
    Alg*) local n=${1#Alg}; echo "runtime.$(echo "${n:0:1}" | tr 'A-Z' 'a-z')${n:1}" ;;
  esac
}
