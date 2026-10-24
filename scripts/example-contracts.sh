# Sourced by scripts/verify-examples.sh: the symbol an example proves things about (default
# example.com/basic.<Name>). The extraction arguments are in scripts/example-targets.sh.
example_symbol() {
  case "$1" in
    MallocFast) echo runtime.mallocgc ;;
    *) echo "example.com/basic.$1" ;;
  esac
}
