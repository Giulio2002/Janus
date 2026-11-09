package main

// Criterion 2: the runtime entry points the Go 1.26 compiler can emit calls to, by category,
// against what Janus has for each of them on main and the unmerged branches.

import (
	"debug/elf"
	"flag"
	"fmt"
	"go/build"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
)

type entry struct {
	Name, Category, Source string
	Linked                 []string          // configurations whose std test binaries link it
	Defined                []string          // GOARCHes (linux) whose runtime source defines it
	Status                 map[string]string // branch -> status
}

var (
	builtinFuncRe = regexp.MustCompile(`(?m)^func ([A-Za-z0-9_]+)\(`)
	lookupRe      = regexp.MustCompile(`LookupRuntime(?:Func|Var|ABI)?\("([A-Za-z0-9_]+)"`)
	// names chosen into a variable that is then passed to LookupRuntime* (walk, ssagen, compare)
	assignRe       = regexp.MustCompile(`\b(?:name|fnname|fn|iterInit|iterNext|buf|funcName)\s*:?=\s*"([A-Za-z0-9_]+)"`)
	objRe          = regexp.MustCompile(`"runtime\.([A-Za-z0-9_]+)"`)
	runtimeRe      = regexp.MustCompile(`runtime\.([A-Za-z_][A-Za-z0-9_]*)`)
	contractFlagRe = regexp.MustCompile(`--contract runtime\.([A-Za-z0-9_]+)`)
	// A contract file may name its entry point without the "runtime." prefix: `makeslice(et, len, cap)`
	// or `growslice` in a doc comment, or the assembler spelling runtime·name. Only names that are
	// entry points are taken (checked against entries by the caller), so ordinary words in backticks
	// are not mistaken for contracts.
	bareRe = regexp.MustCompile("`(?:runtime[.\u00b7])?([A-Za-z_][A-Za-z0-9_]*)[`(]|runtime\u00b7([A-Za-z_][A-Za-z0-9_]*)")
)

// specNames lists the entry points a contract file names: runtime.NAME anywhere, and the bare
// spellings of bareRe when NAME is a known entry point.
func specNames(src string, entries map[string]*entry) []string {
	seen := map[string]bool{}
	var out []string
	add := func(n string) {
		if n != "" && !seen[n] {
			seen[n] = true
			out = append(out, n)
		}
	}
	for _, m := range runtimeRe.FindAllStringSubmatch(src, -1) {
		add(m[1])
	}
	for _, m := range bareRe.FindAllStringSubmatch(src, -1) {
		for _, n := range m[1:] {
			if _, ok := entries[n]; ok {
				add(n)
			}
		}
	}
	return out
}

func category(n string) string {
	has := func(p ...string) bool {
		for _, x := range p {
			if strings.HasPrefix(n, x) {
				return true
			}
		}
		return false
	}
	switch {
	case has("chan", "makechan", "closechan", "select", "block", "newproc", "goschedguarded", "gopark", "race", "lock", "unlock") && !has("printlock", "printunlock"):
		return "concurrency (excluded)"
	case has("printlock", "printunlock", "print"):
		return "print (println builtin)"
	case has("morestack"):
		return "stack growth"
	case has("gcWriteBarrier", "writeBarrier", "wbZero", "wbMove"):
		return "write barrier"
	case has("panic", "goPanic", "gopanic", "gorecover", "throw", "deferproc", "deferreturn", "deferrangefunc", "recover", "sigpanic"):
		return "panic/recover/defer"
	case strings.Contains(n, "map") && !has("mapinitnoop"):
		return "map"
	case has("growslice", "makeslice", "moveSlice", "slicecopy", "typedslicecopy", "unsafeslice", "checkptr"):
		return "slice/growslice"
	case has("newobject", "mallocgc", "new"):
		return "alloc"
	case has("concat", "cmpstring", "intstring", "slicebyte", "slicerune", "stringtoslice", "decoderune", "countrunes", "strmin", "strmax", "unsafestring", "rawstring"):
		return "string"
	case has("convT", "assert", "typeAssert", "interfaceSwitch", "ifaceeq", "efaceeq", "getitab"):
		return "interface/type assertion"
	case has("memhash", "strhash", "f32hash", "f64hash", "c64hash", "c128hash", "interhash", "nilinterhash", "typehash", "rand", "aeshash"):
		return "hashing/rand"
	case has("memequal", "memmove", "memclr", "typedmem", "f32equal", "f64equal", "c64equal", "c128equal", "strequal", "interequal", "nilinterequal", "duff", "memcmp", "bulkBarrier"):
		return "memory/equality"
	case has("arm64Has", "x86Has", "armHas", "loong64Has", "riscv64Has"):
		return "CPU feature flags (variables)"
	case has("fadd", "fsub", "fmul", "fdiv", "feq", "fge", "fgt", "fint", "udiv", "wasm"):
		return "conversion/soft arithmetic"
	case has("float", "int64", "uint64", "int32", "uint32", "complex128div", "fmin", "fmax", "fintto", "fuint", "f32to", "f64to", "uint64to", "int64to", "float64to", "float32to", "ui"):
		return "conversion/soft arithmetic"
	case has("cgo", "asmcgocall", "_cgo", "cgocall", "cgoCheck", "crosscall"):
		return "cgo"
	case has("msan", "asan", "libfuzzer", "coverage", "addCovMeta", "racefunc"):
		return "instrumentation (msan/asan/fuzz/cover)"
	case has("arenas"):
		return "alloc"
	}
	return "misc"
}

// Janus code that exercises the real runtime function in a proved example rather than
// assuming a contract for it (docs/AMD64.md, docs/PROOFS.md and the examples' proofs).
var executedOnMain = map[string]string{
	"memmove":              "executed (CopyBlock, CopyBlock512)",
	"memclrNoHeapPointers": "executed (ClearWords)",
	"memequal":             "executed (A64Equal64 / Equal64)",
}
var executedOnBranch = map[string]map[string]string{
	"agent/alloc": {"gcWriteBarrier2": "executed fast path (SetNext; wbBufFlush contract)", "mallocgc": "contract + MallocFast proof of the real fast path (arm64)"},
	"agent/maps":  {"mapaccess1_fast64": "contract + MapAccess1Small proof of the real code"},
}

func gitShow(repo, branch, path string) string {
	out, err := exec.Command("git", "-C", repo, "show", branch+":"+path).Output()
	if err != nil {
		return ""
	}
	return string(out)
}

func gitFiles(repo, branch string) []string {
	out, err := exec.Command("git", "-C", repo, "ls-tree", "-r", "--name-only", branch).Output()
	if err != nil {
		die("git ls-tree %s: %v", branch, err)
	}
	return strings.Split(strings.TrimSpace(string(out)), "\n")
}

func cmdRuntime(args []string) {
	fs := flag.NewFlagSet("runtime", flag.ExitOnError)
	goroot := fs.String("goroot", "", "GOROOT of the pinned toolchain")
	repo := fs.String("repo", ".", "Janus repository")
	branches := fs.String("branches", "main", "branches, space separated")
	outPath := fs.String("o", "runtime.tsv", "TSV output")
	bins := fs.String("bins", "", "comma-separated binaries whose symbol tables tell which entry points are linked (cfg=path)")
	fs.Parse(args)
	src := filepath.Join(*goroot, "src")
	entries := map[string]*entry{}
	add := func(n, source string) {
		if n == "" {
			return
		}
		if e := entries[n]; e != nil {
			if !strings.Contains(e.Source, source) {
				e.Source += "," + source
			}
			return
		}
		entries[n] = &entry{Name: n, Category: category(n), Source: source, Status: map[string]string{}}
	}
	b, err := os.ReadFile(filepath.Join(src, "cmd/compile/internal/typecheck/_builtin/runtime.go"))
	if err != nil {
		die("%v", err)
	}
	for _, m := range builtinFuncRe.FindAllStringSubmatch(string(b), -1) {
		add(m[1], "builtin")
	}
	add("writeBarrier", "builtin")
	// runtime symbols, for validating names picked up heuristically
	linked := map[string]map[string]bool{}
	var cfgs []string
	for _, cb := range strings.Split(*bins, ",") {
		if cb == "" {
			continue
		}
		cfg, p, _ := strings.Cut(cb, "=")
		if linked[cfg] == nil {
			cfgs = append(cfgs, cfg)
			linked[cfg] = map[string]bool{}
		}
		paths, _ := filepath.Glob(p)
		for _, p := range paths {
			f, err := elf.Open(p)
			if err != nil {
				die("%v", err)
			}
			syms, _ := f.Symbols()
			for _, s := range syms {
				if n, ok := strings.CutPrefix(s.Name, "runtime."); ok {
					linked[cfg][strings.TrimSuffix(n, ".abi0")] = true
				}
			}
			f.Close()
		}
	}
	anyLinked := func(n string) bool {
		for _, c := range cfgs {
			if linked[c][n] {
				return true
			}
		}
		return false
	}
	for _, dir := range []string{"ssagen", "walk", "reflectdata", "compare", "noder", "typecheck", "ssa", "staticinit", "escape", "inline", "pkginit"} {
		files, _ := filepath.Glob(filepath.Join(src, "cmd/compile/internal", dir, "*.go"))
		for _, fp := range files {
			if strings.HasSuffix(fp, "_test.go") || strings.HasSuffix(fp, "builtin.go") {
				continue
			}
			b, _ := os.ReadFile(fp)
			for _, m := range lookupRe.FindAllStringSubmatch(string(b), -1) {
				add(m[1], dir)
			}
			if dir == "ssagen" || dir == "walk" || dir == "compare" || dir == "reflectdata" {
				for _, m := range assignRe.FindAllStringSubmatch(string(b), -1) {
					if anyLinked(m[1]) || len(cfgs) == 0 {
						add(m[1], dir)
					}
				}
			}
			if dir == "ssa" {
				// rewrite rules / lowering that name runtime functions (e.g. memequal variants)
				for _, m := range objRe.FindAllStringSubmatch(string(b), -1) {
					add(m[1], "ssa")
				}
			}
		}
	}
	// fmt.Sprintf families in ssagen: expand from the symbol tables
	for _, pre := range []string{"mallocgcSmallNoScanSC", "mallocgcSmallScanNoHeaderSC", "mallocgcTinySize"} {
		for _, c := range cfgs {
			for n := range linked[c] {
				if strings.HasPrefix(n, pre) {
					add(n, "ssagen")
				}
			}
		}
	}
	// the assembler back ends: prologue morestack calls, duff devices, TLS
	for _, fp := range []string{"cmd/internal/obj/arm64/obj7.go", "cmd/internal/obj/x86/obj6.go", "cmd/internal/obj/arm64/asm7.go", "cmd/internal/obj/x86/asm6.go"} {
		b, _ := os.ReadFile(filepath.Join(src, fp))
		for _, m := range objRe.FindAllStringSubmatch(string(b), -1) {
			if !strings.HasSuffix(m[1], "landingpad") && m[1] != "sehtramp" {
				add(m[1], "obj")
			}
		}
	}
	// cgo: what cmd/cgo-generated code calls
	for _, fp := range []string{"cmd/cgo/out.go"} {
		b, _ := os.ReadFile(filepath.Join(src, fp))
		for _, m := range regexp.MustCompile(`runtime\.(cgo[A-Za-z0-9_]*|_cgo_[A-Za-z0-9_]*)`).FindAllStringSubmatch(string(b), -1) {
			add(m[1], "cgo")
		}
		for _, m := range regexp.MustCompile(`_cgo_runtime_([A-Za-z0-9_]+)`).FindAllStringSubmatch(string(b), -1) {
			add(m[1], "cgo")
		}
	}
	for _, e := range entries {
		for _, c := range cfgs {
			if linked[c][e.Name] {
				e.Linked = append(e.Linked, c)
			}
		}
	}
	// which names the linux/arm64 and linux/amd64 runtime defines at all (build-constraint aware)
	for _, ga := range []string{"arm64", "amd64"} {
		ctx := build.Default
		ctx.GOOS, ctx.GOARCH, ctx.GOROOT, ctx.CgoEnabled = "linux", ga, *goroot, true
		def := map[string]bool{}
		dir := filepath.Join(src, "runtime")
		files, _ := os.ReadDir(dir)
		for _, fe := range files {
			n := fe.Name()
			if !(strings.HasSuffix(n, ".go") || strings.HasSuffix(n, ".s")) || strings.HasSuffix(n, "_test.go") {
				continue
			}
			if ok, err := ctx.MatchFile(dir, n); err != nil || !ok {
				continue
			}
			b, _ := os.ReadFile(filepath.Join(dir, n))
			for _, m := range regexp.MustCompile(`(?m)^func ([A-Za-z0-9_]+)\(|^TEXT runtime·([A-Za-z0-9_]+)[(<]|^var ([A-Za-z0-9_]+)\b`).FindAllStringSubmatch(string(b), -1) {
				def[m[1]+m[2]+m[3]] = true
			}
		}
		for _, e := range entries {
			if def[e.Name] {
				e.Defined = append(e.Defined, ga)
			}
		}
	}

	// what each branch has
	brs := strings.Fields(*branches)
	for _, br := range brs {
		have := map[string]string{}
		for _, f := range gitFiles(*repo, br) {
			isSpec := strings.HasPrefix(f, "Janus/Contracts/") || f == "Janus/FFI.lean" || f == "Janus/Amd64/FFI.lean"
			if isSpec && strings.HasSuffix(f, ".lean") {
				src := gitShow(*repo, br, f)
				for _, n := range specNames(src, entries) {
					if have[n] == "" {
						have[n] = "contract (" + strings.TrimPrefix(f, "Janus/") + ")"
					}
				}
			}
		}
		for _, m := range contractFlagRe.FindAllStringSubmatch(gitShow(*repo, br, "scripts/example-contracts.sh"), -1) {
			if have[m[1]] == "" {
				have[m[1]] = "proof-local contract (--contract in an example)"
			}
		}
		ex := gitShow(*repo, br, "cmd/janus/extract.go")
		if i := strings.Index(ex, "runtimePanicStubs = map[string]bool{"); i >= 0 {
			j := strings.Index(ex[i:], "\n\t}")
			for _, m := range runtimeRe.FindAllStringSubmatch(ex[i:i+j], -1) {
				if have[m[1]] == "" {
					have[m[1]] = "stub (.panic)"
				}
			}
		}
		for _, n := range []string{"morestack", "morestack_noctxt"} {
			if strings.Contains(ex, "runtime."+n+".abi0") && have[n] == "" {
				have[n] = "stub (.morestack)"
			}
		}
		if strings.Contains(ex, "runtime.deferreturn") && have["deferreturn"] == "" {
			have["deferreturn"] = "omitted (reached only after recover)"
		}
		for n, s := range executedOnMain {
			if have[n] == "" {
				have[n] = s
			}
		}
		for n, s := range executedOnBranch[br] {
			if have[n] == "" || strings.HasPrefix(have[n], "proof-local") {
				have[n] = s
			}
		}
		for _, e := range entries {
			if s := have[e.Name]; s != "" {
				e.Status[br] = s
			}
		}
	}

	var names []string
	for n := range entries {
		names = append(names, n)
	}
	sort.Slice(names, func(i, j int) bool {
		a, b := entries[names[i]], entries[names[j]]
		if a.Category != b.Category {
			return a.Category < b.Category
		}
		return a.Name < b.Name
	})
	var tsv strings.Builder
	tsv.WriteString("name\tcategory\tsource\tlinked\tdefined\t" + strings.Join(brs, "\t") + "\n")
	type cs struct{ total, linkedN, have, haveMain int }
	cats := map[string]*cs{}
	var catOrder []string
	for _, n := range names {
		e := entries[n]
		c := cats[e.Category]
		if c == nil {
			c = &cs{}
			cats[e.Category] = c
			catOrder = append(catOrder, e.Category)
		}
		c.total++
		if len(e.Linked) > 0 || len(cfgs) == 0 {
			c.linkedN++
		}
		any := false
		for _, br := range brs {
			if e.Status[br] != "" {
				any = true
			}
		}
		if any {
			c.have++
		}
		if e.Status["main"] != "" {
			c.haveMain++
		}
		fmt.Fprintf(&tsv, "%s\t%s\t%s\t%s\t%s", e.Name, e.Category, e.Source, strings.Join(e.Linked, ","), strings.Join(e.Defined, ","))
		for _, br := range brs {
			fmt.Fprintf(&tsv, "\t%s", e.Status[br])
		}
		tsv.WriteString("\n")
	}
	os.WriteFile(*outPath, []byte(tsv.String()), 0o644)

	fmt.Printf("## runtime entry points: %d names\n\n| category | entry points | linked on arm64/amd64 | with something on main | on main or a branch |\n|---|---:|---:|---:|---:|\n", len(names))
	sort.Strings(catOrder)
	tot := cs{}
	for _, k := range catOrder {
		c := cats[k]
		fmt.Printf("| %s | %d | %d | %d | %d |\n", k, c.total, c.linkedN, c.haveMain, c.have)
		tot.total += c.total
		tot.linkedN += c.linkedN
		tot.have += c.have
		tot.haveMain += c.haveMain
	}
	fmt.Printf("| **total** | %d | %d | %d | %d |\n\n", tot.total, tot.linkedN, tot.haveMain, tot.have)
	fmt.Printf("### Covered (status per branch)\n\n| entry point | category | %s |\n|---|---|%s\n", strings.Join(brs, " | "), strings.Repeat("---|", len(brs)))
	for _, n := range names {
		e := entries[n]
		row := ""
		any := false
		for _, br := range brs {
			s := e.Status[br]
			if s != "" {
				any = true
			}
			row += " " + s + " |"
		}
		if any {
			fmt.Printf("| `%s` | %s |%s\n", n, e.Category, row)
		}
	}
	covered := func(e *entry) bool {
		for _, br := range brs {
			if e.Status[br] != "" {
				return true
			}
		}
		return false
	}
	list := func(title string, keep func(e *entry) bool) {
		fmt.Printf("\n### %s\n\n", title)
		cur, n := "", 0
		for _, nm := range names {
			e := entries[nm]
			if covered(e) || !keep(e) {
				continue
			}
			if e.Category != cur {
				if cur != "" {
					fmt.Println()
				}
				cur = e.Category
				fmt.Printf("* **%s**:", cur)
			}
			fmt.Printf(" `%s`", nm)
			n++
		}
		fmt.Printf("\n\n(%d)\n", n)
	}
	list("Missing, linked by the std test binaries (arm64 or amd64)", func(e *entry) bool { return len(e.Linked) > 0 })
	list("Missing, defined by the linux/arm64 or amd64 runtime but not linked by std (constructs std does not use, cgo user code, GOEXPERIMENTs, instrumented builds)",
		func(e *entry) bool { return len(e.Linked) == 0 && len(e.Defined) > 0 })
	fmt.Printf("\n### Not applicable: emitted only for other GOARCHes (no linux/arm64 or amd64 definition)\n\n")
	for _, nm := range names {
		e := entries[nm]
		if len(e.Linked) == 0 && len(e.Defined) == 0 && !covered(e) {
			fmt.Printf(" `%s`", nm)
		}
	}
	fmt.Println()
}
