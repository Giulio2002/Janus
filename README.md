# Janus

Machine-checked proofs about **compiled Go**, against the arm64 machine code the Go compiler
actually emitted — not the source, not an IR.

Janus is named after the two-faced Roman god of doorways: one face looks at the Go program you
wrote, the other at the instructions that run. The compiler is not trusted; the theorem is about
the bytes in the binary.

> Status: early work in progress.

## Design

```
Go source ──go build (GOARCH=arm64)──▶ ELF binary
                                          │
                     janus extract: copy raw instruction words
                     of the selected function + reachable callees
                                          ▼
                     Extracted.lean (words, addresses) + identity.json (SHA-256)
                                          │
 AArch64 model in Lean ──────────────────▶├──◀── your theorem + proof
 (decoder + semantics, checked memory)    ▼
                     janus verify: re-extract & compare, kernel check, axiom audit
                                          ▼
                                     verified.json
```

* **Decoding happens in Lean.** The extractor only copies 32-bit words out of `.text`; it does
  not translate them. Its output is re-derived from the binary and compared on every verify.
* **Memory is checked.** Every load and store must fall inside a caller-provided allocation, or
  execution faults. Go runtime panic stubs (bounds checks, nil, divide) are named outcomes, so
  "this function never panics" is a provable statement.
* **The Go calling convention (ABIInternal) is explicit**: arguments and results in `X0`–`X15`.

Trusted: the Lean AArch64 model (differentially tested against qemu), the ELF word copy, and the
Lean kernel. Not trusted: the Go compiler, linker, and any source-level reasoning.
