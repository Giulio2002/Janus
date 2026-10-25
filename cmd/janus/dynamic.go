package main

// Dynamic call targets: code an indirect call (BLR/BR on arm64, CALL reg on amd64) may reach.
//
// The target of an indirect call is a register value, which a static sweep cannot follow. The
// extractor copies the code it may reach anyway, so that a theorem stating which code a call
// reaches (an interface's dynamic type, a closure's function) can be proved by running it.
// Like reachability, this is untrusted: it only decides what to copy. A target that is not
// copied makes the call fault (noCode) in the model, so a proof through it is impossible; an
// extra target only adds code no theorem has to mention.
//
// Targets come from
//
//   - --targets SYM,...: functions, static itabs (go:itab.*T,I: every fun[k] slot) and static
//     funcvals (*·f: the function word), named explicitly;
//   - inference: a code address the extracted code computes (ADRP+ADD / LEA of a function entry:
//     a closure or method value built by the code itself, e.g. `pkg.F.func1` or `pkg.T.M-fm`),
//     and the itabs and funcvals in the read-only data the extracted code loads. Only references
//     made by functions outside the standard library are used (see inferFrom).
//
// Each added target is recorded in identity.json (dynamicTargets) with how it was found.
//
// runtime.deferreturn is never followed: a function with open-coded defers calls it only from
// the exit block the runtime resumes at after a recovered panic, which is out of scope
// (docs/SOUNDNESS.md). It is recorded in identity.json (omittedCalls); reaching it in the model
// faults (noCode), so heap-allocated defer records (whose normal exits call it) are unsupported.

import (
	"encoding/binary"
	"fmt"
	"slices"
	"sort"
	"strings"
)

// DynTarget is one function added because an indirect call may reach it.
type DynTarget struct {
	Name string
	Addr uint64
	Via  string // "targets" (--targets), "itab", "funcval", "code-address"
	From string // the itab or funcval symbol, or the address of the instruction computing the address
}

// OmittedCall is a direct call that is deliberately not followed.
type OmittedCall struct {
	From   uint64
	Target uint64
	Name   string
	Reason string
}

// omittedCallees are the functions whose direct calls are not followed, and why.
var omittedCallees = map[string]string{
	"runtime.deferreturn": "open-coded defer exit after a recovered panic (out of scope); heap-allocated defer records are unsupported",
}

const (
	itabFunOffset = 24 // offset of fun[0] in internal/abi.ITab on 64-bit targets
	funcvalSuffix = "·f"
	itabPrefix    = "go:itab."
)

// dataSymbol returns the data symbol named name.
func (b *Binary) dataSymbol(name string) (Func, bool) {
	for _, s := range b.dataSyms {
		if s.Name == name {
			return s, true
		}
	}
	return Func{}, false
}

// readWord is the 64-bit little-endian word at addr in an allocated, non-writable section
// with contents.
func (b *Binary) readWord(addr uint64) (uint64, bool) {
	sec, ok := b.sectionOf(addr)
	if !ok || sec.Writable || sec.NoBits || addr+8 > sec.End() {
		return 0, false
	}
	return binary.LittleEndian.Uint64(sec.data[addr-sec.Addr:]), true
}

// codeWords are the function addresses a static itab or funcval holds.
func (b *Binary) codeWords(sym Func) (via string, addrs []uint64, ok bool) {
	switch {
	case strings.HasPrefix(sym.Name, itabPrefix):
		for off := uint64(itabFunOffset); off+8 <= sym.Size; off += 8 {
			if w, ok := b.readWord(sym.Addr + off); ok && w != 0 {
				addrs = append(addrs, w)
			}
		}
		return "itab", addrs, true
	case strings.HasSuffix(sym.Name, funcvalSuffix) && sym.Size >= 8:
		if w, ok := b.readWord(sym.Addr); ok && w != 0 {
			addrs = append(addrs, w)
		}
		return "funcval", addrs, true
	}
	return "", nil, false
}

// reacher is the breadth-first copy of the code reachable from the entry and the dynamic
// targets.
type reacher struct {
	b        *Binary
	x        *Extraction
	maxF     int
	seen     map[uint64]bool
	stubSeen map[uint64]bool
	dynSeen  map[string]bool
	queue    []Func
	scan     func(*Binary, Func) (Segment, []Unresolved, error)
	// --contract: calls to matching functions are not followed (extract.go)
	cm           *contractMatcher
	contractSeen map[uint64]bool
	// err is the first stub-classification error (round 7 G1), reported by drain and extractWith.
	err error
}

func (r *reacher) addStub(g Func, k StubKind) {
	if !r.stubSeen[g.Addr] {
		r.stubSeen[g.Addr] = true
		r.x.Stubs = append(r.x.Stubs, Stub{Name: g.Name, Addr: g.Addr, Kind: k})
	}
}

// addTarget queues the function at addr as a dynamic target; ok is false if addr is not a
// function entry.
func (r *reacher) addTarget(addr uint64, via, from string) bool {
	g, ok := r.b.containing(addr)
	if !ok || g.Addr != addr {
		return false
	}
	key := g.Name + "\x00" + via + "\x00" + from
	if !r.dynSeen[key] {
		r.dynSeen[key] = true
		r.x.Dynamic = append(r.x.Dynamic, DynTarget{Name: g.Name, Addr: g.Addr, Via: via, From: from})
	}
	// A --contract on a panic/defer/recover runtime function (runtime.gopanic, deferproc, ...)
	// turns it into a pinned contract before its default stub/omit/follow meaning applies.
	if r.cm.match(g.Name) && runtimePanicContractStubs[g.Name] {
		if isContract, err := r.x.contractTarget(r.cm, r.contractSeen, g); isContract {
			if err != nil && r.err == nil {
				r.err = err
			}
			return true
		}
	}
	k, isStub, err := r.b.classifyStub(g)
	if err != nil {
		if r.err == nil {
			r.err = err
		}
		return true
	}
	if isStub {
		r.addStub(g, k)
		return true
	}
	if isContract, err := r.x.contractTarget(r.cm, r.contractSeen, g); isContract {
		if err != nil && r.err == nil {
			r.err = err
		}
		return true
	}
	if !r.seen[g.Addr] {
		r.seen[g.Addr] = true
		r.queue = append(r.queue, g)
	}
	return true
}

func (r *reacher) tooMany() error {
	var names []string
	for _, s := range r.x.Segments {
		names = append(names, s.Name)
	}
	for _, q := range r.queue {
		names = append(names, q.Name)
	}
	if len(names) > 20 {
		names = append(names[:20], fmt.Sprintf("... and %d more", len(names)-20))
	}
	return &diag{
		Msg: fmt.Sprintf("%s reaches more than %d functions by direct branches:\n    %s",
			r.x.Entry.Name, r.maxF, strings.Join(names, "\n    ")),
		Stage: "code extraction",
		Next:  "Raise the limit with --max-functions N if this is intended, or extract a smaller function.",
	}
}

// drain copies every queued function and what it reaches by direct branches.
func (r *reacher) drain() error {
	if r.err != nil {
		return r.err
	}
	for len(r.queue) > 0 {
		f := r.queue[0]
		r.queue = r.queue[1:]
		seg, brs, err := r.scan(r.b, f)
		if err != nil {
			return &diag{Msg: err.Error(), Stage: "code extraction", Next: "Report this binary layout to the Janus maintainers."}
		}
		r.x.Segments = append(r.x.Segments, seg)
		r.addInsnStubs(seg) // SVC/SYSCALL, environment reads and traps inside it (kernel.go)
		for _, br := range brs {
			t := br.Target
			if t >= f.Addr && t < f.End() {
				continue
			}
			g, ok := r.b.containing(t)
			if !ok {
				r.x.Unresolved = append(r.x.Unresolved, br)
				continue
			}
			if r.cm.match(g.Name) && runtimePanicContractStubs[g.Name] {
				if isContract, err := r.x.contractTarget(r.cm, r.contractSeen, g); isContract {
					if err != nil {
						return err
					}
					continue
				}
			}
			k, isStub, err := r.b.classifyStub(g)
			if err != nil {
				return err
			}
			if isStub {
				r.addStub(g, k)
				continue
			}
			if isContract, err := r.x.contractTarget(r.cm, r.contractSeen, g); isContract {
				if err != nil {
					return err
				}
				continue
			}
			if why, ok := omittedCallees[g.Name]; ok {
				r.x.Omitted = append(r.x.Omitted, OmittedCall{From: br.From, Target: t, Name: g.Name, Reason: why})
				continue
			}
			if !r.seen[g.Addr] {
				r.seen[g.Addr] = true
				r.queue = append(r.queue, g)
			}
		}
		// the C wrappers of the cgo function-pointer variables the function loads (FFI)
		for _, g := range cgoWrapperRoots(r.b, segmentDataRefs(r.b, seg)) {
			if _, isStub := stubKindFor(r.b.GOARCH, g.Name); isStub || r.seen[g.Addr] {
				continue
			}
			if isContract, err := r.x.contractTarget(r.cm, r.contractSeen, g); isContract {
				if err != nil {
					return err
				}
				continue
			}
			r.seen[g.Addr] = true
			r.queue = append(r.queue, g)
		}
		if len(r.x.Segments)+len(r.queue) > r.maxF {
			return r.tooMany()
		}
	}
	return nil
}

// segmentDataRefs are the data references of one copied function.
func segmentDataRefs(b *Binary, s Segment) []DataRef {
	if b.GOARCH == "amd64" {
		return amd64DataRefs(sweepAmd64(s.Bytes, s.Base))
	}
	return dataRefs(s.Words, s.Base)
}

// extractWith copies sym, the dynamic targets named in targets, and everything reachable from
// them by direct branches or inferred dynamic targets (see the file comment).
func extractWith(b *Binary, sym string, maxFunctions int, contracts []string, targets ...string) (*Extraction, error) {
	entry, err := b.lookup(sym)
	if err != nil {
		return nil, err
	}
	if stubLikeFor(b.GOARCH, entry.Name) {
		return nil, &diag{Msg: fmt.Sprintf("%s is a runtime stub, not a function Janus extracts", entry.Name),
			Stage: "function selection", Next: "Select a Go function that calls the stub instead."}
	}
	cm, err := newContractMatcher(contracts)
	if err != nil {
		return nil, err
	}
	if cm.match(entry.Name) {
		return nil, &diag{Msg: fmt.Sprintf("%s matches a --contract pattern; the entry function cannot be a contract", entry.Name),
			Stage: "function selection", Next: "Drop the --contract pattern that matches the entry, or extract a caller of it."}
	}
	if len(contracts) == 0 {
		cm = nil
	}
	x := &Extraction{Bin: b, Entry: entry, Targets: targets, ContractPatterns: contracts}
	r := &reacher{b: b, x: x, maxF: maxFunctions, cm: cm, contractSeen: map[uint64]bool{}, seen: map[uint64]bool{entry.Addr: true},
		stubSeen: map[uint64]bool{}, dynSeen: map[string]bool{}, queue: []Func{entry}, scan: extractArm64Func}
	if b.GOARCH == "amd64" {
		r.scan = extractAmd64Func
	}
	// --targets: functions, itabs and funcvals by name
	var extra []DataRef
	for _, t := range targets {
		if f, err := b.lookup(t); err == nil {
			r.addTarget(f.Addr, "targets", "")
			continue
		}
		ds, ok := b.dataSymbol(t)
		if !ok {
			return nil, &diag{Msg: fmt.Sprintf("--targets: %q is neither a function nor a data symbol of %s", t, b.Path),
				Stage: "function selection",
				Next:  "Name a function, a static itab (go:itab.*T,I) or a static funcval (...·f) exactly as janus list or go tool nm prints it."}
		}
		if _, _, ok := b.codeWords(ds); !ok {
			return nil, &diag{Msg: fmt.Sprintf("--targets: data symbol %q is not a static itab (go:itab.*) or funcval (*·f)", t),
				Stage: "function selection", Next: "Name a function, a static itab or a static funcval."}
		}
		if sec, ok := b.sectionOf(ds.Addr); !ok || sec.Writable || sec.NoBits {
			return nil, &diag{Msg: fmt.Sprintf("--targets: %q is not in a read-only section; its content is not fixed by the binary", t),
				Stage: "function selection", Next: "Name a static itab or funcval in .rodata."}
		}
		extra = append(extra, DataRef{From: 0, Target: ds.Addr, Kind: "target"})
	}
	for {
		if err := r.drain(); err != nil {
			return nil, err
		}
		x.DataRefs = nil
		for _, s := range x.Segments {
			x.DataRefs = append(x.DataRefs, segmentDataRefs(b, s)...)
		}
		x.Data, x.Skipped = collectData(b, x.DataRefs, extra...)
		before := len(r.queue)
		// itabs and funcvals among the copied read-only data that user code (or --targets) refers to
		var eligible []uint64
		for _, ref := range x.DataRefs {
			if r.inferFrom(ref.From) {
				eligible = append(eligible, ref.Target)
			}
		}
		for _, e := range extra {
			eligible = append(eligible, e.Target)
		}
		for _, d := range x.Data {
			i := sort.Search(len(b.dataSyms), func(i int) bool { return b.dataSyms[i].Addr >= d.Base })
			for ; i < len(b.dataSyms) && b.dataSyms[i].Addr < d.Base+uint64(len(d.Bytes)); i++ {
				ds := b.dataSyms[i]
				if ds.End() > d.Base+uint64(len(d.Bytes)) || !slices.ContainsFunc(eligible, func(a uint64) bool { return a >= ds.Addr && a < ds.End() }) {
					continue
				}
				if via, addrs, ok := b.codeWords(ds); ok {
					for _, a := range addrs {
						r.addTarget(a, via, ds.Name)
					}
				}
			}
		}
		// code addresses computed by user code
		for _, s := range x.Skipped {
			if s.Reason == "code" && r.inferFrom(s.From) {
				r.addTarget(s.Target, "code-address", hex0x(s.From))
			}
		}
		if len(r.queue) == before {
			break
		}
		if len(x.Segments)+len(r.queue) > r.maxF {
			return nil, r.tooMany()
		}
	}
	if r.err != nil {
		return nil, r.err
	}
	if b.GOARCH == "amd64" {
		x.Lean = renderLeanAmd64(x)
	} else {
		x.Lean = renderLean(x)
	}
	return x, nil
}

// inferFrom reports whether references made by the instruction at pc are used to infer dynamic
// targets: only those in functions outside the standard library (package main, or a package
// path whose first element contains a dot). The runtime's own indirect calls (systemstack
// closures, ...) are not followed unless named with --targets: they would copy most of the
// runtime into every extraction that reaches it.
func (r *reacher) inferFrom(pc uint64) bool {
	f, ok := r.b.containing(pc)
	return ok && !isStdSymbol(f.Name)
}

// isStdSymbol reports whether a function symbol belongs to a standard-library package.
func isStdSymbol(name string) bool {
	if k := strings.IndexAny(name, "[("); k >= 0 {
		name = name[:k]
	}
	i := strings.LastIndex(name, "/")
	rest := name[i+1:]
	j := strings.Index(rest, ".")
	if j < 0 {
		return true
	}
	pkg := name[:i+1+j]
	if pkg == "main" {
		return false
	}
	first, _, _ := strings.Cut(pkg, "/")
	return !strings.Contains(first, ".")
}

// splitTopLevel splits v at the commas outside brackets and parentheses.
func splitTopLevel(v string) []string {
	var parts []string
	depth, start := 0, 0
	for i, c := range v {
		switch c {
		case '[', '(':
			depth++
		case ']', ')':
			depth--
		case ',':
			if depth == 0 {
				parts = append(parts, v[start:i])
				start = i + 1
			}
		}
	}
	return append(parts, v[start:])
}

// parseTargets splits a --targets value at the commas outside brackets. An itab's name contains
// a comma of its own (go:itab.*T,I), so a go:itab. element takes the next element with it.
func parseTargets(v string) []string {
	parts := splitTopLevel(v)
	var out []string
	for i := 0; i < len(parts); i++ {
		t := strings.TrimSpace(parts[i])
		if strings.HasPrefix(t, itabPrefix) && len(splitTopLevel(t)) == 1 && i+1 < len(parts) {
			i++
			t += "," + strings.TrimSpace(parts[i])
		}
		if t != "" {
			out = append(out, t)
		}
	}
	return out
}
