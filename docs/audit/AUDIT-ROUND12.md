# Round 12: the ELF loader's view

Hole (red-team 11b, O1): `validateSegments` accepted a section once the first `PT_LOAD` covered
it; a later overlapping `PT_LOAD` (appended page, 7th program header) is what the loader maps,
so the binary ran `SUB` while `janus verify` printed `Verified` for "Add returns x+y".

Fix: `cmd/janus/elfview.go`. The loader map (table order, later wins) is built from the `PT_LOAD`
table; overlapping, malformed (`filesz > memsz`, misaligned) and writable+executable segments are
rejected; every extracted byte is read through the map; every section's `sh_offset` bytes are
compared with the loader's bytes at `sh_addr`; plus load-time patching (DT_TEXTREL, relocations
into code or rodata), RELRO and symbol-range checks. The exact list and the out-of-scope
assumptions are in docs/SOUNDNESS.md "ELF loader semantics".

Rows (`audit/round12/run-round12.sh`, both ISAs on the Add example): O1 overlap with 4 KiB and
64 KiB `p_align`, a 16-byte unaligned overlap and (arm64) segments disjoint at 4 KiB that share a 64 KiB page (each also run under qemu to show the overlapping
mapping really executes), H1 section header at another file offset, H2 `filesz > memsz`, H3 W+X,
H4 misaligned, C1 the unmodified binary still verifies, D1 the synthetic-ELF unit tests
(`cmd/janus/elfview_test.go`: relocations into code/rodata, IRELATIVE, DT_TEXTREL, DF_TEXTREL,
DT_REL, RELRO, symbol ranges, duplicate symbols, init_array warnings).
