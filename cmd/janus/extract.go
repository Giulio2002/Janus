package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"regexp"
	"strings"
)

const extractorVersion = "0.2.0"

const defaultMaxFunctions = 64

// Segment is one copied function.
type Segment struct {
	Name  string
	Base  uint64
	Size  uint64 // symbol size, including padding
	Words []uint32
	Bytes []byte // amd64: the raw bytes of [Base, Base+Size) (Words is empty)
}

// StubKind mirrors Janus.StubKind.
type StubKind string

const (
	stubPanic     StubKind = "panic"
	stubMorestack StubKind = "morestack"
	// stubExternal: a function outside the extracted code whose effect a theorem states as an
	// explicit contract (Janus.StubKind.external, see Janus/FFI.lean): the cgo boundary.
	stubExternal StubKind = "external"
)

type Stub struct {
	Name string
	Addr uint64
	Kind StubKind
}

// Unresolved is a direct branch whose target is in no known function; it is not copied.
type Unresolved struct {
	From   uint64
	Target uint64
}

// Contract is a function named by --contract: direct calls to it are not followed, and its
// address is recorded in Program.contracts. Its behaviour is whatever the theorem's contract
// hypotheses (a `Summary` of the program linked with arbitrary code) say; without one, control
// reaching it faults with noCode, exactly as for any other address without extracted code.
type Contract struct {
	Name string
	Addr uint64
	// Pinned: the name is one of runtimeContractStubs and the function's code was checked
	// against the pinned code of the Go runtime's function of that name (checkContractPin).
	Pinned bool
}

type Extraction struct {
	Bin       *Binary
	Entry     Func
	Contracts []Contract // discovery order
	// ContractPatterns are the --contract patterns, as given (recorded in identity.json so
	// that check regenerates the same extraction).
	ContractPatterns []string
	Segments         []Segment // entry first, then breadth-first discovery order
	Stubs            []Stub    // discovery order
	Unresolved       []Unresolved
	// Dynamic targets: --targets as given, and every function added because an indirect call
	// may reach it (see dynamic.go). Omitted: direct calls deliberately not followed.
	Targets  []string
	Dynamic  []DynTarget
	Omitted  []OmittedCall
	Data     []DataSeg     // read-only objects the code references, sorted by address
	DataRefs []DataRef     // detected references, in code order
	Skipped  []SkippedData // references whose target is not copied (writable, code, ...)
	// BuildModes are the accepted instrumented build modes (buildmode.go), recorded in
	// identity.json; nil for an ordinary build.
	BuildModes []string
	// The C environment (cenv.go): writable C data objects the C code references, and the TLS
	// image when an extracted function reads the thread pointer.
	CData []CData
	TLS   *tlsImage
	// Writable globals named by --global (globals.go): their link-time images, recorded in
	// Program.globals; GlobalPatterns are the patterns as given (recorded in identity.json).
	GlobalPatterns []string
	Globals        []GlobalSeg
	Lean           []byte
}

// Round 7 G1: the runtime functions Janus treats as stubs, by their exact linked (ELF .symtab)
// names. A name alone does not identify package runtime: any package may define a Go-assembly
// TEXT symbol `runtime·panicX` or push one with `//go:linkname f runtime.panicX` (neither needs
// -checklinkname=0), and round 6 classified every `runtime.panic*`/`runtime.morestack*` name
// without '/' as a stub, so an ordinary function that returns (or panics) was taken for a panic
// (or morestack) stub. The lists below are exactly the functions of that kind that the go1.26
// runtime defines for linux/arm64 and linux/amd64 (`go tool nm` on the runtime archive of
// go1.26.0 and go1.26.10, both architectures; minus panicCheck1/2, which return, and
// morestackc, a fatal throw that only runtime code calls). Because the runtime itself defines
// each of them, another definition with the same name and ABI is a link error ("duplicated
// definition of symbol"), and one with the other ABI is linked under a mangled name
// (`runtime.panicdivide.abi0`), which is not on the list. That argument needs the go1.26
// runtime, the ELF symbol table (the pclntab does not record the ABI, so names there are not
// mangled), and a name that occurs once (`//go:linkname f runtime.morestack_noctxt.abi0`
// gives a second symbol with exactly that name). Round 8 (G3): "the go1.26 runtime" was read
// from build info, which `-ldflags=-X runtime.buildVersion=...` sets, and a binary linked by a
// release whose runtime lacks a listed name can carry an ordinary function under it. So
// `classifyStub` no longer reads the Go version: it checks the symbol table, uniqueness, and
// the function's code and pclntab entry against the pins of stubpins_gen.go (stubpin.go).
var (
	runtimePanicStubs = map[string]bool{
		"runtime.gopanic": true, "runtime.goPanicIndex": true, "runtime.goPanicIndexU": true,
		"runtime.goPanicSlice3Acap": true, "runtime.goPanicSlice3AcapU": true,
		"runtime.goPanicSlice3Alen": true, "runtime.goPanicSlice3AlenU": true,
		"runtime.goPanicSlice3B": true, "runtime.goPanicSlice3BU": true,
		"runtime.goPanicSlice3C": true, "runtime.goPanicSlice3CU": true,
		"runtime.goPanicSliceAcap": true, "runtime.goPanicSliceAcapU": true,
		"runtime.goPanicSliceAlen": true, "runtime.goPanicSliceAlenU": true,
		"runtime.goPanicSliceB": true, "runtime.goPanicSliceBU": true,
		"runtime.goPanicSliceConvert": true,
		"runtime.panicBounds":         true, "runtime.panicBounds32": true, "runtime.panicBounds32X": true,
		"runtime.panicBounds64": true, "runtime.panicdivide": true, "runtime.panicdottypeE": true,
		"runtime.panicdottypeI": true, "runtime.panicfloat": true, "runtime.panicmakeslicecap": true,
		"runtime.panicmakeslicelen": true, "runtime.panicmem": true, "runtime.panicmemAddr": true,
		"runtime.panicnildottype": true, "runtime.panicoverflow": true,
		"runtime.panicrangestate": true, "runtime.panicshift": true, "runtime.panicSimdImm": true,
		"runtime.panicunsafeslicelen": true, "runtime.panicunsafeslicelen1": true,
		"runtime.panicunsafeslicenilptr": true, "runtime.panicunsafeslicenilptr1": true,
		"runtime.panicunsafestringlen": true, "runtime.panicunsafestringnilptr": true,
		"runtime.panicwrap": true,
	}
	// morestack and morestack_noctxt are ABI0 assembly; the linker names them with ".abi0".
	runtimeMorestackStubs = map[string]bool{
		"runtime.morestack.abi0": true, "runtime.morestack_noctxt.abi0": true,
	}
	// The cgo boundary (Janus/FFI.lean): runtime.cgocall (the Go -> C call: stack switch to g0,
	// entersyscall/exitsyscall, the C call through asmcgocall), _cgo_topofstack (Go assembly the
	// C side of a cgo call calls), runtime.cgoUse and runtime.cgoKeepAlive (only on the dead
	// `if _Cgo_always_false` branch of cgo wrappers; cgoKeepAlive with `#cgo noescape`, both
	// throw if called). Their effects are the trusted contracts of Janus.FFI.
	// runtime.cgocallback.abi0 is the C -> Go direction (//export): crosscall2, which the
	// cgo-generated C wrapper of an exported Go function calls, calls it to re-enter Go
	// (Janus.FFI.CgoCallback).
	runtimeExternalStubs = map[string]bool{
		"runtime.cgocall": true, "_cgo_topofstack": true, "_cgo_topofstack.abi0": true,
		"runtime.cgoUse": true, "runtime.cgoKeepAlive": true, "runtime.cgocallback.abi0": true,
	}
)

// runtimeContractStubs are the runtime functions whose behaviour a framework contract library
// states (Janus/Contracts/Iface.lean, IfaceAmd64.lean: the interface runtime of Go 1.26;
// Janus/Contracts/Mem.lean, Hash.lean and their amd64 files: equality, hashing and typed memory;
// Janus/Contracts/Map.lean, MapVar.lean, MapStr.lean and their amd64 files: the map runtime; and
// rtmiscContractStubs below, added at init). When a
// --contract pattern matches one, the extractor pins it like a stub (checkContractPin): the
// pclntab names it in package runtime, in the toolchain's file, and its normalized code is the
// runtime's (stubpins_gen.go). A binary whose function of that name is not the runtime's is an
// extraction error, so a theorem's contract hypothesis is about the Go runtime's own code. The
// functions they call (mallocgc, getitab, typedmemmove, the types' equality functions, ...)
// are identified by name only, as for the pinned helpers.
var runtimeContractStubs = map[string]bool{
	"runtime.convT": true, "runtime.convTnoptr": true, "runtime.convT16": true,
	"runtime.convT32": true, "runtime.convT64": true, "runtime.convTstring": true,
	"runtime.convTslice": true, "runtime.assertE2I": true, "runtime.assertE2I2": true,
	"runtime.typeAssert": true, "runtime.interfaceSwitch": true, "runtime.efaceeq": true,
	"runtime.ifaceeq": true,
	// equality (Janus/Contracts/Mem.lean, MemAmd64.lean)
	"runtime.memequal": true, "runtime.memequal0": true, "runtime.memequal8": true,
	"runtime.memequal16": true, "runtime.memequal32": true, "runtime.memequal64": true,
	"runtime.memequal128": true, "runtime.memequal_varlen": true, "runtime.f32equal": true,
	"runtime.f64equal": true, "runtime.c64equal": true, "runtime.c128equal": true,
	"runtime.strequal": true, "runtime.interequal": true, "runtime.nilinterequal": true,
	// typed memory and the functions it calls (Mem.lean, MemAmd64.lean)
	"runtime.typedmemmove": true, "runtime.typedmemclr": true, "runtime.memclrHasPointers": true,
	"runtime.memmove": true, "runtime.memclrNoHeapPointers": true,
	"runtime.bulkBarrierPreWrite": true,
	// hashing (Janus/Contracts/Hash.lean, HashAmd64.lean)
	"runtime.memhash": true, "runtime.memhash0": true, "runtime.memhash8": true,
	"runtime.memhash16": true, "runtime.memhash32": true, "runtime.memhash64": true,
	"runtime.memhash128": true, "runtime.memhash_varlen": true, "runtime.strhash": true,
	"runtime.f32hash": true, "runtime.f64hash": true, "runtime.c64hash": true,
	"runtime.c128hash": true, "runtime.interhash": true, "runtime.nilinterhash": true,
	"runtime.rand": true, // (typehash is not pinned: its jump table makes its normalized code differ between programs)
	// the map runtime (Janus/Contracts/Map.lean, MapVar.lean, MapStr.lean and their amd64 files)
	"runtime.makemap": true, "runtime.makemap_small": true, "runtime.mapclear": true,
	"runtime.mapIterStart": true, "runtime.mapIterNext": true,
	"runtime.mapaccess1": true, "runtime.mapaccess2": true, "runtime.mapassign": true,
	"runtime.mapdelete": true, "runtime.mapaccess1_fat": true, "runtime.mapaccess2_fat": true,
	"runtime.mapaccess1_fast32": true, "runtime.mapaccess2_fast32": true,
	"runtime.mapassign_fast32": true, "runtime.mapdelete_fast32": true,
	"runtime.mapaccess1_fast64": true, "runtime.mapaccess2_fast64": true,
	"runtime.mapassign_fast64": true, "runtime.mapdelete_fast64": true,
	"runtime.mapassign_fast64ptr": true,
	"runtime.mapaccess1_faststr":  true, "runtime.mapaccess2_faststr": true,
	"runtime.mapassign_faststr": true, "runtime.mapdelete_faststr": true,
}

// runtimePanicContractStubs are the panic/defer/recover runtime functions whose behaviour a
// framework contract library states (Janus/Contracts/Panic.lean, PanicAmd64.lean: the panic
// runtime of Go 1.26). They are not followed by default (runtime.gopanic is also a panic stub,
// runtime.deferreturn is omitted, the others would pull in the scheduler). A --contract pattern
// that matches one turns it into a pinned contract (checkContractPin, like runtimeContractStubs):
// a direct branch to it is not followed, its code is not copied, and a theorem states its effect
// as a Summary / GoReturns hypothesis (docs/RUNTIME-CONTRACTS.md, "Panics, defer, recover").
// Without a matching --contract they keep their default meaning (gopanic a panic stub, the rest
// ordinary code or the omitted deferreturn).
var runtimePanicContractStubs = map[string]bool{
	"runtime.gopanic": true, "runtime.gorecover": true, "runtime.deferproc": true,
	"runtime.deferprocStack": true, "runtime.deferreturn": true, "runtime.deferprocat": true,
	"runtime.deferrangefunc": true, "runtime.sigpanic": true,
}

// rtmiscContractStubs are the further runtime functions a framework contract library describes
// (docs/RUNTIME-CONTRACTS.md, "Remaining runtime"): the -d=checkptr checks and the cgo pointer
// checks (Janus/Contracts/InstrumentCalls*.lean) and the size-specialised allocator entry points of
// GOEXPERIMENT=sizespecializedmalloc (Janus/Contracts/MallocSC*.lean). They are pinned like the
// interface contracts (checkContractPin) and belong to runtimeContractStubs.
var rtmiscContractStubs = map[string]bool{
	"runtime.checkptrAlignment": true, "runtime.checkptrArithmetic": true,
	"runtime.cgoCheckPointer": true, "runtime.cgoCheckResult": true,
	"runtime.mallocgcSmallNoScanSC2": true, "runtime.mallocgcSmallNoScanSC3": true,
	"runtime.mallocgcSmallNoScanSC4": true, "runtime.mallocgcSmallNoScanSC5": true,
	"runtime.mallocgcSmallNoScanSC6": true, "runtime.mallocgcSmallNoScanSC7": true,
	"runtime.mallocgcSmallNoScanSC8": true, "runtime.mallocgcSmallNoScanSC9": true,
	"runtime.mallocgcSmallNoScanSC10": true, "runtime.mallocgcSmallNoScanSC11": true,
	"runtime.mallocgcSmallNoScanSC12": true, "runtime.mallocgcSmallNoScanSC13": true,
	"runtime.mallocgcSmallNoScanSC14": true, "runtime.mallocgcSmallNoScanSC15": true,
	"runtime.mallocgcSmallNoScanSC16": true, "runtime.mallocgcSmallNoScanSC17": true,
	"runtime.mallocgcSmallNoScanSC18": true, "runtime.mallocgcSmallNoScanSC19": true,
	"runtime.mallocgcSmallNoScanSC20": true, "runtime.mallocgcSmallNoScanSC21": true,
	"runtime.mallocgcSmallNoScanSC22": true, "runtime.mallocgcSmallNoScanSC23": true,
	"runtime.mallocgcSmallNoScanSC24": true, "runtime.mallocgcSmallNoScanSC25": true,
	"runtime.mallocgcSmallNoScanSC26": true, "runtime.mallocgcSmallScanNoHeaderSC1": true,
	"runtime.mallocgcSmallScanNoHeaderSC2": true, "runtime.mallocgcSmallScanNoHeaderSC3": true,
	"runtime.mallocgcSmallScanNoHeaderSC4": true, "runtime.mallocgcSmallScanNoHeaderSC5": true,
	"runtime.mallocgcSmallScanNoHeaderSC6": true, "runtime.mallocgcSmallScanNoHeaderSC7": true,
	"runtime.mallocgcSmallScanNoHeaderSC8": true, "runtime.mallocgcSmallScanNoHeaderSC9": true,
	"runtime.mallocgcSmallScanNoHeaderSC10": true, "runtime.mallocgcSmallScanNoHeaderSC11": true,
	"runtime.mallocgcSmallScanNoHeaderSC12": true, "runtime.mallocgcSmallScanNoHeaderSC13": true,
	"runtime.mallocgcSmallScanNoHeaderSC14": true, "runtime.mallocgcSmallScanNoHeaderSC15": true,
	"runtime.mallocgcSmallScanNoHeaderSC16": true, "runtime.mallocgcSmallScanNoHeaderSC17": true,
	"runtime.mallocgcSmallScanNoHeaderSC18": true, "runtime.mallocgcSmallScanNoHeaderSC19": true,
	"runtime.mallocgcSmallScanNoHeaderSC20": true, "runtime.mallocgcSmallScanNoHeaderSC21": true,
	"runtime.mallocgcSmallScanNoHeaderSC22": true, "runtime.mallocgcSmallScanNoHeaderSC23": true,
	"runtime.mallocgcSmallScanNoHeaderSC24": true, "runtime.mallocgcSmallScanNoHeaderSC25": true,
	"runtime.mallocgcSmallScanNoHeaderSC26": true, "runtime.mallocgcTinySize1": true,
	"runtime.mallocgcTinySize2": true, "runtime.mallocgcTinySize3": true,
	"runtime.mallocgcTinySize4": true, "runtime.mallocgcTinySize5": true,
	"runtime.mallocgcTinySize6": true, "runtime.mallocgcTinySize7": true,
	"runtime.mallocgcTinySize8": true, "runtime.mallocgcTinySize9": true,
	"runtime.mallocgcTinySize10": true, "runtime.mallocgcTinySize11": true,
	"runtime.mallocgcTinySize12": true, "runtime.mallocgcTinySize13": true,
	"runtime.mallocgcTinySize14": true, "runtime.mallocgcTinySize15": true,
}

func init() {
	for n := range rtmiscContractStubs {
		runtimeContractStubs[n] = true
	}
}

// allocContractStubs are the allocation, slice and write-barrier entry points a framework contract
// library describes (Janus/Contracts/Alloc.lean, AllocAmd64.lean: MallocgcContract,
// NewobjectContract, MakesliceContract, GrowsliceContract and their amd64 forms; the
// gcWriteBarrierN entries, whose fast path the examples execute and which a write-barrier
// contract may leave out with --contract 'runtime.gcWriteBarrier*'). They belong to
// runtimeContractStubs (added at init), so a --contract that names one is pinned to the
// runtime's code like memmove (checkContractPin), not trusted by name.
var allocContractStubs = map[string]bool{
	"runtime.mallocgc": true, "runtime.newobject": true, "runtime.makeslice": true,
	"runtime.growslice":       true,
	"runtime.gcWriteBarrier1": true, "runtime.gcWriteBarrier2": true, "runtime.gcWriteBarrier3": true,
	"runtime.gcWriteBarrier4": true, "runtime.gcWriteBarrier5": true, "runtime.gcWriteBarrier6": true,
	"runtime.gcWriteBarrier7": true, "runtime.gcWriteBarrier8": true,
}

func init() {
	for n := range allocContractStubs {
		runtimeContractStubs[n] = true
	}
}

// stubKind classifies a linked symbol name as a runtime stub (name only; see classifyStub for
// the checks that make the name trustworthy).
func stubKind(name string) (StubKind, bool) {
	switch {
	case runtimeMorestackStubs[name]:
		return stubMorestack, true
	case runtimePanicStubs[name]:
		return stubPanic, true
	case runtimeExternalStubs[name]:
		return stubExternal, true
	}
	return "", false
}

// cgoFnVarRE matches the Go variable cgo generates for each C function a package calls
// (`var _cgo_<hash>_Cfunc_<name> = unsafe.Pointer(&__cgofn__cgo_<hash>_Cfunc_<name>)`): it holds
// the address of the C wrapper of the same name, which runtime.cgocall calls.
var cgoFnVarRE = regexp.MustCompile(`(?:^|\.)(_cgo_[0-9a-f]+_Cfunc_[A-Za-z0-9_]+)$`)

// cgoWrapperRoots returns the C wrappers whose function-pointer variables the code at refs
// loads. Following them is reachability (untrusted, like branch following): it only decides
// that the C code is copied too, so that a theorem can run it.
func cgoWrapperRoots(b *Binary, refs []DataRef) []Func {
	var out []Func
	for _, r := range refs {
		sym, ok, _ := b.dataSymbolAt(r.Target)
		if !ok {
			continue
		}
		m := cgoFnVarRE.FindStringSubmatch(sym.Name)
		if m == nil {
			continue
		}
		if f, err := b.lookup(m[1]); err == nil {
			out = append(out, f)
		}
	}
	return out
}

// stubLike reports whether name looks like a runtime stub under any ABI suffix (used only to
// give a useful diagnostic when classifyStub cannot authenticate one).
func stubLike(name string) bool {
	n := strings.TrimSuffix(name, ".abi0")
	_, ok1 := stubKind(n)
	_, ok2 := stubKind(n + ".abi0")
	return ok1 || ok2 || kernelStubAnyArch(n) || kernelStubAnyArch(n+".abi0")
}

// stubLikeFor is stubLike for a binary of architecture goarch (the vDSO stubs differ per
// architecture: kernel.go).
func stubLikeFor(goarch, name string) bool {
	n := strings.TrimSuffix(name, ".abi0")
	_, ok1 := stubKindFor(goarch, n)
	_, ok2 := stubKindFor(goarch, n+".abi0")
	return ok1 || ok2
}

// classifyStub decides whether the function g, the target of a direct branch, is a runtime
// stub. It is one only if its name is on the lists above, its names come from the ELF symbol
// table, no other function has the same name (round 7 G1), and its code and pclntab entry are
// those of the runtime function of that name in a pinned toolchain (round 8 G3, stubpin.go).
// The build-info Go version plays no part. A listed name that fails a check is an error, never
// a stub and never code: extracting the runtime function as code would give a different, much
// larger program, and taking another function for a stub would model it by an outcome it does
// not have.
func (b *Binary) classifyStub(g Func) (StubKind, bool, error) {
	k, ok := stubKindFor(b.GOARCH, g.Name)
	if !ok {
		if b.SymbolSource != "symtab" && stubLikeFor(b.GOARCH, g.Name) {
			return "", false, &diag{
				Msg:   fmt.Sprintf("the code calls %s, but %s has no ELF symbol table, and function names from the pclntab do not record the ABI, so Janus cannot tell the runtime's %s from a function of another package that only has that name (round 7 G1)", g.Name, b.Path, g.Name),
				Stage: "code extraction",
				Next:  "Rebuild without stripping the symbol table (no -ldflags=-s).",
			}
		}
		return "", false, nil
	}
	if b.SymbolSource != "symtab" {
		return "", false, &diag{
			Msg:   fmt.Sprintf("the code calls %s, but %s has no ELF symbol table, so Janus cannot confirm it is the runtime's (round 7 G1)", g.Name, b.Path),
			Stage: "code extraction",
			Next:  "Rebuild without stripping the symbol table (no -ldflags=-s).",
		}
	}
	n := 0
	for _, f := range b.Funcs {
		if f.Name == g.Name {
			n++
		}
	}
	if n != 1 {
		return "", false, &diag{
			Msg:   fmt.Sprintf("the code calls %s, but %s defines %d functions with that name, so the runtime's cannot be told from the others (round 7 G1: //go:linkname can push a second symbol with a runtime stub's name)", g.Name, b.Path, n),
			Stage: "code extraction",
			Next:  "Remove the //go:linkname or assembly definition that reuses a runtime function's name.",
		}
	}
	b.stubMu.Lock()
	defer b.stubMu.Unlock()
	if v, ok := b.stubCache[g.Addr]; ok {
		return v.kind, v.ok, v.err
	}
	v := stubVerdict{kind: k, ok: true}
	if err := b.checkStubPin(g, map[uint64]bool{}); err != nil {
		v = stubVerdict{err: &diag{
			Msg: fmt.Sprintf("the code calls %s at 0x%x, a runtime stub's name, but that function is not the Go runtime's %s: %v. Janus models a stub call as its outcome (%s) only when the function's code is the runtime's (round 8 G3), so it neither treats it as a stub nor verifies it as code",
				g.Name, g.Addr, g.Name, err, k),
			Stage: "code extraction",
			Next:  "If the binary was built by a Go toolchain Janus does not pin yet (" + stubPinToolchains + "), add it to scripts/gen-stubpins.sh and regenerate cmd/janus/stubpins_gen.go; otherwise remove the function that reuses a runtime function's name.",
		}}
	}
	if b.stubCache == nil {
		b.stubCache = map[uint64]stubVerdict{}
	}
	b.stubCache[g.Addr] = v
	return v.kind, v.ok, v.err
}

// extract copies sym and every function reachable from it by direct branches.
func extract(binPath, sym string, maxFunctions int, contracts ...string) (*Extraction, error) {
	b, err := loadBinary(binPath)
	if err != nil {
		return nil, err
	}
	return extractWith(b, sym, maxFunctions, contracts)
}

func extractFrom(b *Binary, sym string, maxFunctions int) (*Extraction, error) {
	return extractWith(b, sym, maxFunctions, nil)
}

// contractMatcher matches function names against --contract glob patterns: `*` matches any
// run of characters (including `.` and `/`), `?` any one character, everything else itself.
// A name matches with or without its `.abi0`/`.abiinternal` suffix.
type contractMatcher struct {
	pats []string
	res  []*regexp.Regexp
}

func newContractMatcher(pats []string) (*contractMatcher, error) {
	m := &contractMatcher{pats: pats}
	for _, p := range pats {
		if p == "" {
			return nil, usageErr("--contract needs a non-empty symbol or glob pattern")
		}
		var sb strings.Builder
		sb.WriteString("^")
		for _, r := range p {
			switch r {
			case '*':
				sb.WriteString(".*")
			case '?':
				sb.WriteString(".")
			default:
				sb.WriteString(regexp.QuoteMeta(string(r)))
			}
		}
		sb.WriteString("$")
		m.res = append(m.res, regexp.MustCompile(sb.String()))
	}
	return m, nil
}

func (m *contractMatcher) match(name string) bool {
	if m == nil {
		return false
	}
	n := strings.TrimSuffix(strings.TrimSuffix(name, ".abi0"), ".abiinternal")
	for _, re := range m.res {
		if re.MatchString(name) || re.MatchString(n) {
			return true
		}
	}
	return false
}

// contractTarget records g as a contract (once) if it matches; true if the branch to it must
// not be followed. Stubs keep their stub meaning (checked by the caller first). A function of
// runtimeContractStubs is pinned to the runtime's code (checkContractPin); an error if it is not
// the runtime's.
func (x *Extraction) contractTarget(m *contractMatcher, seen map[uint64]bool, g Func) (bool, error) {
	if !m.match(g.Name) {
		return false, nil
	}
	if !seen[g.Addr] {
		seen[g.Addr] = true
		c := Contract{Name: g.Name, Addr: g.Addr}
		if runtimeContractStubs[g.Name] || runtimePanicContractStubs[g.Name] {
			if err := x.Bin.checkContractPin(g); err != nil {
				return true, err
			}
			c.Pinned = true
		}
		x.Contracts = append(x.Contracts, c)
	}
	return true, nil
}

// extractArm64Func copies one arm64 function and lists its direct branches.
func extractArm64Func(b *Binary, f Func) (Segment, []Unresolved, error) {
	ws, err := b.words(f)
	if err != nil {
		return Segment{}, nil, err
	}
	var brs []Unresolved
	for i, w := range ws {
		pc := f.Addr + 4*uint64(i)
		if t, ok := branchTarget(w, pc); ok {
			brs = append(brs, Unresolved{From: pc, Target: t})
		}
	}
	return Segment{Name: f.Name, Base: f.Addr, Size: f.Size, Words: ws}, brs, nil
}

func leanString(s string) string {
	var sb strings.Builder
	sb.WriteByte('"')
	for _, r := range s {
		switch {
		case r == '"' || r == '\\':
			sb.WriteByte('\\')
			sb.WriteRune(r)
		case r < 0x20 || r == 0x7f:
			fmt.Fprintf(&sb, "\\x%02x", r)
		default:
			sb.WriteRune(r)
		}
	}
	sb.WriteByte('"')
	return sb.String()
}

const wordsPerLine = 8

// Lean elaborates one large list literal with deep recursion: around 3000 words in a single
// definition exceed the default maxRecDepth. Programs up to inlineWordLimit words are written
// with all segments inline in `segments`; larger ones get one definition per segment.
const (
	inlineWordLimit  = 2048
	segmentWordLimit = 1024 // above this, a segment definition raises maxRecDepth
)

const bytesPerLine = 16

func writeDataSegment(sb *strings.Builder, d DataSeg, indent string) {
	fmt.Fprintf(sb, "{ name := %s, base := 0x%x, bytes := [", leanString(d.Name), d.Base)
	multi := len(d.Bytes) > bytesPerLine
	for j, v := range d.Bytes {
		if j > 0 {
			sb.WriteString(",")
			if !(multi && j%bytesPerLine == 0) {
				sb.WriteString(" ")
			}
		}
		if multi && j%bytesPerLine == 0 {
			sb.WriteString("\n" + indent + "    ")
		}
		fmt.Fprintf(sb, "0x%02x", v)
	}
	sb.WriteString("] }")
}

func writeSegment(sb *strings.Builder, s Segment, indent string) {
	fmt.Fprintf(sb, "{ name := %s, base := 0x%x, words := [", leanString(s.Name), s.Base)
	multi := len(s.Words) > wordsPerLine
	for j, w := range s.Words {
		if j > 0 {
			sb.WriteString(",")
			if !(multi && j%wordsPerLine == 0) {
				sb.WriteString(" ")
			}
		}
		if multi && j%wordsPerLine == 0 {
			sb.WriteString("\n" + indent + "    ")
		}
		fmt.Fprintf(sb, "0x%08x", w)
	}
	sb.WriteString("] }")
}

// renderLean produces Extracted.lean. The output is a pure function of the extraction, so
// `janus check` can compare it byte for byte.
func renderLean(x *Extraction) []byte {
	var sb strings.Builder
	sb.WriteString("import Janus\n\n")
	fmt.Fprintf(&sb, "/-! Generated by `janus extract` %s from `%s` (%s, %s).\n", extractorVersion, x.Entry.Name, x.Bin.MainModule, x.Bin.GoVersion)
	sb.WriteString("Do not edit: `janus check` regenerates this file from the binary and compares it byte for byte.\n")
	sb.WriteString("The binary's SHA-256 is recorded in `identity.json`. -/\n\n")
	sb.WriteString("namespace Extracted\nopen Janus\n\n")
	total := 0
	for _, s := range x.Segments {
		total += len(s.Words)
	}
	if total <= inlineWordLimit {
		sb.WriteString("def segments : List Segment := [")
		for i, s := range x.Segments {
			if i > 0 {
				sb.WriteString(",")
			}
			sb.WriteString("\n  ")
			writeSegment(&sb, s, "  ")
		}
		sb.WriteString(" ]\n\n")
	} else {
		for i, s := range x.Segments {
			if len(s.Words) > segmentWordLimit {
				sb.WriteString("set_option maxRecDepth 100000 in\n")
			}
			fmt.Fprintf(&sb, "def seg%d : Segment :=\n  ", i)
			writeSegment(&sb, s, "  ")
			sb.WriteString("\n\n")
		}
		sb.WriteString("def segments : List Segment := [")
		for i := range x.Segments {
			if i > 0 {
				sb.WriteString(",")
				if i%wordsPerLine != 0 {
					sb.WriteString(" ")
				}
			}
			if i%wordsPerLine == 0 {
				sb.WriteString("\n  ")
			}
			fmt.Fprintf(&sb, "seg%d", i)
		}
		sb.WriteString(" ]\n\n")
	}
	sb.WriteString("def stubs : List Stub := [")
	for i, st := range x.Stubs {
		if i > 0 {
			sb.WriteString(",")
		}
		fmt.Fprintf(&sb, "\n  { name := %s, addr := 0x%x, kind := .%s }", leanString(st.Name), st.Addr, st.Kind)
	}
	if len(x.Stubs) > 0 {
		sb.WriteString(" ")
	}
	sb.WriteString("]\n\n")
	sb.WriteString("def exitAddr : Nat := 0\n\n")
	writeProgram(&sb, x, "Program")
	writeCEnv(&sb, x)
	fmt.Fprintf(&sb, "def entry : Nat := 0x%x\n\n", x.Entry.Addr)
	sb.WriteString("end Extracted\n")
	return []byte(sb.String())
}

// writeContracts renders `def contracts` (only when there are contracts, so extractions
// without --contract are byte-identical to earlier ones).
func writeContracts(sb *strings.Builder, cs []Contract) {
	sb.WriteString("def contracts : List (String × Nat) := [")
	for i, c := range cs {
		if i > 0 {
			sb.WriteString(",")
		}
		fmt.Fprintf(sb, "\n  (%s, 0x%x)", leanString(c.Name), c.Addr)
	}
	sb.WriteString(" ]\n\n")
}

// writeProgram renders the data and contract lists (if any) and `def program`.
func writeProgram(sb *strings.Builder, x *Extraction, ty string) {
	fields := "segments := segments, stubs := stubs, exitAddr := exitAddr"
	if len(x.Data) > 0 {
		writeData(sb, x.Data)
		fields += ", data := data"
	}
	if len(x.Contracts) > 0 {
		writeContracts(sb, x.Contracts)
		fields += ", contracts := contracts"
	}
	if len(x.Globals) > 0 {
		writeGlobals(sb, x.Globals)
		fields += ", globals := globals"
	}
	if len(x.Data) == 0 && len(x.Contracts) == 0 && len(x.Globals) == 0 {
		fmt.Fprintf(sb, "def program : %s := { %s }\n\n", ty, fields)
		return
	}
	fmt.Fprintf(sb, "def program : %s :=\n  { %s }\n\n", ty, fields)
}

// writeData renders `def data`, inline when small, else one definition per object (like
// large code segments).
func writeData(sb *strings.Builder, data []DataSeg) {
	total := 0
	for _, d := range data {
		total += len(d.Bytes)
	}
	if total <= inlineWordLimit {
		sb.WriteString("def data : List DataSegment := [")
		for i, d := range data {
			if i > 0 {
				sb.WriteString(",")
			}
			sb.WriteString("\n  ")
			writeDataSegment(sb, d, "  ")
		}
		sb.WriteString(" ]\n\n")
		return
	}
	for i, d := range data {
		if len(d.Bytes) > segmentWordLimit {
			sb.WriteString("set_option maxRecDepth 100000 in\n")
		}
		fmt.Fprintf(sb, "def data%d : DataSegment :=\n  ", i)
		writeDataSegment(sb, d, "  ")
		sb.WriteString("\n\n")
	}
	sb.WriteString("def data : List DataSegment := [")
	for i := range data {
		if i > 0 {
			sb.WriteString(",")
			if i%wordsPerLine != 0 {
				sb.WriteString(" ")
			}
		}
		if i%wordsPerLine == 0 {
			sb.WriteString("\n  ")
		}
		fmt.Fprintf(sb, "data%d", i)
	}
	sb.WriteString(" ]\n\n")
}

func sha256Hex(b []byte) string {
	s := sha256.Sum256(b)
	return hex.EncodeToString(s[:])
}
