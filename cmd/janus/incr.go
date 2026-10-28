package main

// The incremental merge gate's skip records (docs/TESTING.md "Incremental gate", docs/SOUNDNESS.md
// "Incremental gate records").
//
//	janus incr check   [spec flags]   print SKIP (a record of a PASS with exactly these inputs) or RUN
//	janus incr record  [spec flags] --pre-key K --rc N --wall S   record a PASS (rc 0, inputs unchanged)
//	janus incr explain [spec flags]   print every component of the key with its hash
//
// An item (one proof file with its extraction, a package, or a whole gate lane) is skipped ONLY on an
// exact match of the key of a previous PASS record. The key is the SHA-256 of the named components
// below, each a content hash of every input of the item:
//
//	item        id, kind and the item's own arguments (the theorems it checks, extraction options)
//	env         every environment variable that can change an item's outcome (JANUS_*, LEAN*, LAKE*, ...)
//	verifier    the content identity of the janus build that decides the verdict (verifierid.go; the
//	            Go side: the embedded Lean framework is keyed per item below, by what the item imports)
//	toolchain   the Lean toolchain: version string, lean and leanchecker bytes, the library files
//	fw:*        the framework the item is checked against (embedded in the binary, and/or a checkout):
//	            lakefile.toml, lake-manifest.json, lean-toolchain; the TRANSITIVE import closure of the
//	            item's modules computed from the actual `import` lines, every module's source and its
//	            compiled module data (.olean ...); and the auditor (its sources, closure, modules and
//	            the compiled janus-audit executable)
//	proof/pkg/art/file/pin/script   the proof files, package directories, extraction directories
//	            (Extracted.lean, identity.json, the binary named there, hashed), other inputs
//	            (binaries), pins and the gate scripts and libraries that ran the item, by content
//	tree, host  (lanes) every non-excluded file of the working tree, and the machine
//
// Anything that cannot be read, parsed or hashed makes the item unkeyed, which is a miss: it runs.
// Records are authenticated with an HMAC under the per-user key of the result cache (resultcache.go);
// a record that is missing, unparsable, truncated, tampered with, forged, copied from another key or
// not a PASS is a miss, never a skip. Only `record` writes records, and only for a run that
// succeeded (--rc 0) whose key, recomputed after the run, equals the key before it.

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode"
	"unicode/utf8"

	janus "github.com/Giulio2002/Janus"
)

const (
	incrSchema    = 1
	incrKeyHeader = "janus-incr-key-v1"
)

func init() {
	extraCommands["incr"] = cmdIncr
}

// incrSpec names the inputs of one item. Paths are relative to Root (default: the working directory).
type incrSpec struct {
	ID, Kind string
	Root     string
	FW       []string // "embedded", "dir:PATH"
	Proofs   []string
	Pkgs     []string
	Arts     []string
	Files    []string
	Pins     []string
	Scripts  []string
	Args     []string
	Virtual  []string // modules the item generates itself from its hashed inputs (WrongAdd's Extracted)
	Tree     string   // a lane: every non-excluded file of this git working tree
	TreeExcl []string
	Host     bool // the machine is an input (lanes whose result can depend on the hardware)
	Full     bool // the full verifier identity (Go and the embedded Lean) instead of the Go-only one
	NoFW     bool // a lane: no per-item framework closure
}

type incrComp struct {
	Name, Hash, Note string
	Lines            []string // the detail behind Hash (explain --verbose)
	Err              error
}

// incrCtx is everything the key reads from the machine; the tests replace the fields.
type incrCtx struct {
	root     string
	environ  []string
	verifier func(full bool) (string, error)
	embedded func() (*framework, error)
	loadDir  func(dir string) (*framework, error)
	build    func(fw *framework) (string, error) // the framework build root (holds .lake)
	tchain   func(root string) (*toolchain, error)
	host     func() string
	memo     map[string]string
}

func newIncrCtx(root string) *incrCtx {
	return &incrCtx{
		root:    root,
		environ: os.Environ(),
		verifier: func(full bool) (string, error) {
			comp, why := verifierComponentScope(currentBuild(), executableSha, full)
			if comp == "" {
				return "", fmt.Errorf("no verifier identity: %s", why)
			}
			return comp, nil
		},
		embedded: func() (*framework, error) {
			fw := &framework{Source: "embedded"}
			var err error
			if fw.Files, err = readFramework(janus.Framework); err != nil {
				return nil, err
			}
			fw.Sha256 = frameworkSha(fw.Files)
			fw.Toolchain = strings.TrimSpace(string(fw.Files["lean-toolchain"]))
			return fw, nil
		},
		loadDir: func(dir string) (*framework, error) { return loadFramework(dir) },
		build: func(fw *framework) (string, error) {
			if fw.Source == "directory" {
				return fw.Dir, nil
			}
			return filepath.Join(cacheRoot(), "v1", "framework", fw.Sha256[:24]), nil
		},
		tchain: func(root string) (*toolchain, error) {
			lake, err := findLake()
			if err != nil {
				return nil, err
			}
			return findToolchain(lake, root)
		},
		host: func() string {
			h, _ := os.Hostname()
			cpu := ""
			if b, err := os.ReadFile("/proc/cpuinfo"); err == nil {
				for _, l := range strings.Split(string(b), "\n") {
					if strings.HasPrefix(l, "model name") || strings.HasPrefix(l, "Model") || strings.HasPrefix(l, "CPU part") {
						cpu = l
						break
					}
				}
			}
			return fmt.Sprintf("%s %s/%s %s", h, runtime.GOOS, runtime.GOARCH, cpu)
		},
		memo: map[string]string{},
	}
}

func (c *incrCtx) abs(p string) string {
	if filepath.IsAbs(p) {
		return filepath.Clean(p)
	}
	return filepath.Join(c.root, p)
}

// fileSha is the SHA-256 of a regular file (followed through symbolic links), memoized per process.
func (c *incrCtx) fileSha(p string) (string, error) {
	a := c.abs(p)
	if s, ok := c.memo[a]; ok {
		return s, nil
	}
	f, err := os.Open(a)
	if err != nil {
		return "", err
	}
	defer f.Close()
	st, err := f.Stat()
	if err != nil {
		return "", err
	}
	if !st.Mode().IsRegular() {
		return "", fmt.Errorf("%s is not a regular file", p)
	}
	h := sha256.New()
	if _, err := io.Copy(h, f); err != nil {
		return "", err
	}
	s := hex.EncodeToString(h.Sum(nil))
	c.memo[a] = s
	return s, nil
}

// ---------------------------------------------------------------- the environment

// incrEnvSkip are the variables that only name where output goes or how many things run at once; they
// cannot turn a failing check into a passing one (an out-of-memory or a timeout is a failure).
var incrEnvSkip = map[string]bool{
	"JANUS_JOBS": true, "JANUS_LANES": true, "JANUS_LANE_JOBS": true, "JANUS_POOL_DIR": true,
	"JANUS_EXAMPLES_SUMMARY": true, "JANUS_EXAMPLES_PREBUILT": true, "JANUS_PRINT_SNAPSHOT": true,
	"JANUS_GATE_PG": true, "JANUS_GATE_PREBUILT": true, "JANUS_GATE_FORCE": true, "JANUS_GATE_INCREMENTAL": true,
	"JANUS_SPEED_BASELINE": true, "JANUS_INCR": true, "JANUS_INCR_RECORD": true, "JANUS_INCR_EXPLAIN": true,
	"JANUS_INCR_NOTE": true, "JANUS_INCR_PRECHECK": true, "JANUS_GATE_T0": true, "JANUS_MEMGUARD_CGROUP": true, "JANUS_PRECHECK_JOBS": true, "JANUS_GOTEST_PARALLEL": true, "JANUS_AUDIT_BIN": true, "JANUS_AUDIT_PREBUILT": true,
	"GOCACHE": true, "GOMODCACHE": true, "GOPATH": true, "GOTMPDIR": true, "GOENV": true,
}

func incrEnvRelevant(name string) bool {
	if incrEnvSkip[name] {
		return false
	}
	for _, p := range []string{"JANUS_", "LEAN", "LAKE", "ELAN", "GO", "CGO_", "MEMCAP", "MEMGUARD", "ASL_", "KEEP", "SAIL", "QEMU", "TMPDIR"} {
		if strings.HasPrefix(name, p) {
			return true
		}
	}
	return false
}

// incrEnvLines are the relevant variables as sorted NAME=value lines.
func incrEnvLines(environ []string) []string {
	var ls []string
	for _, kv := range environ {
		i := strings.IndexByte(kv, '=')
		if i <= 0 {
			continue
		}
		if incrEnvRelevant(kv[:i]) {
			ls = append(ls, kv)
		}
	}
	sort.Strings(ls)
	return ls
}

func (c *incrCtx) getenv(name string) string {
	v := ""
	for _, kv := range c.environ {
		if strings.HasPrefix(kv, name+"=") {
			v = kv[len(name)+1:]
		}
	}
	return v
}

// ---------------------------------------------------------------- Lean imports

// leanImports returns the modules a Lean source imports: the header (optional `prelude`, then
// `import` lines with their modifiers), comments skipped, ending at the first other token. A header
// it cannot read exactly is an error (the item is then unkeyed).
func leanImports(src []byte) ([]string, error) {
	s := string(src)
	i := 0
	skip := func() error {
		for i < len(s) {
			switch {
			case s[i] == ' ' || s[i] == '\t' || s[i] == '\n' || s[i] == '\r':
				i++
			case strings.HasPrefix(s[i:], "--"):
				for i < len(s) && s[i] != '\n' {
					i++
				}
			case strings.HasPrefix(s[i:], "/-"):
				depth := 0
				for {
					switch {
					case i >= len(s):
						return fmt.Errorf("unterminated block comment in the header")
					case strings.HasPrefix(s[i:], "/-"):
						depth++
						i += 2
					case strings.HasPrefix(s[i:], "-/"):
						depth--
						i += 2
					default:
						i++
					}
					if depth == 0 {
						break
					}
				}
			default:
				return nil
			}
		}
		return nil
	}
	word := func() string {
		j := i
		for j < len(s) {
			r, n := utf8.DecodeRuneInString(s[j:])
			if r == utf8.RuneError || unicode.IsSpace(r) || strings.HasPrefix(s[j:], "--") || strings.HasPrefix(s[j:], "/-") {
				break
			}
			j += n
		}
		w := s[i:j]
		i = j
		return w
	}
	var mods []string
	if err := skip(); err != nil {
		return nil, err
	}
	save := i
	if w := word(); w != "prelude" {
		i = save
	}
	for {
		if err := skip(); err != nil {
			return nil, err
		}
		start := i
		w := word()
		for w == "public" || w == "meta" || w == "private" {
			if err := skip(); err != nil {
				return nil, err
			}
			w = word()
		}
		if w != "import" {
			i = start
			return mods, nil
		}
		if err := skip(); err != nil {
			return nil, err
		}
		m := word()
		if m == "all" || m == "runtime" {
			// a modifier if another word follows on the same line, else a module of that name
			k := i
			for k < len(s) && (s[k] == ' ' || s[k] == '\t') {
				k++
			}
			if k < len(s) && s[k] != '\n' && s[k] != '\r' && !strings.HasPrefix(s[k:], "--") && !strings.HasPrefix(s[k:], "/-") {
				i = k
				m = word()
			}
		}
		if m == "" || strings.ContainsAny(m, "«»/\\\"") || strings.HasPrefix(m, ".") || strings.HasSuffix(m, ".") || strings.Contains(m, "..") {
			return nil, fmt.Errorf("cannot read the module name %q in an import", m)
		}
		mods = append(mods, m)
	}
}

// ---------------------------------------------------------------- the import closure

type incrProvider struct {
	name  string
	read  func(rel string) ([]byte, bool) // rel: slash path of the .lean file
	isFW  bool
	olean func(mod string) ([]string, error) // module data lines (framework only)
}

// closure resolves the transitive imports of the root sources.
func (c *incrCtx) closure(roots []string, rootSrc map[string][]byte, provs []incrProvider, needOlean func(mod string) bool, virtual ...string) (lines []string, err error) {
	virt := map[string]bool{}
	for _, v := range virtual {
		virt[v] = true
	}
	type item struct {
		mod string
		src []byte
		pv  *incrProvider
	}
	seen := map[string]bool{}
	var queue []item
	var out []string
	for _, r := range roots {
		out = append(out, fmt.Sprintf("root %s %s", r, sha256Hex(rootSrc[r])))
		mods, err := leanImports(rootSrc[r])
		if err != nil {
			return nil, fmt.Errorf("%s: %v", r, err)
		}
		for _, m := range mods {
			if !seen[m] {
				seen[m] = true
				queue = append(queue, item{mod: m})
			}
		}
	}
	for len(queue) > 0 {
		it := queue[0]
		queue = queue[1:]
		if isCoreModule(it.mod) {
			out = append(out, "core "+it.mod)
			continue
		}
		if virt[it.mod] {
			out = append(out, "virtual "+it.mod)
			continue
		}
		rel := strings.ReplaceAll(it.mod, ".", "/") + ".lean"
		var found []int
		var src []byte
		for k := range provs {
			if b, ok := provs[k].read(rel); ok {
				found = append(found, k)
				src = b
			}
		}
		if len(found) == 0 {
			return nil, fmt.Errorf("module %s is imported but found in no source root (not the framework, the item's package or its extraction)", it.mod)
		}
		if len(found) > 1 {
			return nil, fmt.Errorf("module %s is ambiguous: it exists in %s and %s", it.mod, provs[found[0]].name, provs[found[1]].name)
		}
		pv := &provs[found[0]]
		line := fmt.Sprintf("mod %s %s src=%s", it.mod, pv.name, sha256Hex(src))
		if pv.isFW && (needOlean == nil || needOlean(it.mod)) {
			ol, err := pv.olean(it.mod)
			if err != nil {
				return nil, err
			}
			line += " data=" + strings.Join(ol, ",")
		}
		out = append(out, line)
		mods, err := leanImports(src)
		if err != nil {
			return nil, fmt.Errorf("%s: %v", rel, err)
		}
		for _, m := range mods {
			if !seen[m] {
				seen[m] = true
				queue = append(queue, item{mod: m})
			}
		}
	}
	sort.Strings(out)
	return out, nil
}

func (c *incrCtx) dirProvider(dir string) incrProvider {
	return incrProvider{name: "dir " + dir, read: func(rel string) ([]byte, bool) {
		b, err := os.ReadFile(filepath.Join(c.abs(dir), filepath.FromSlash(rel)))
		return b, err == nil
	}}
}

// fwProvider reads module sources from the framework's own files and module data from its build.
func (c *incrCtx) fwProvider(fw *framework, buildRoot string) incrProvider {
	lib := filepath.Join(buildRoot, ".lake", "build", "lib", "lean")
	return incrProvider{name: "framework(" + fw.Source + ")", isFW: true,
		read: func(rel string) ([]byte, bool) {
			b, ok := fw.Files[rel]
			return b, ok
		},
		olean: func(mod string) ([]string, error) {
			base := filepath.Join(lib, filepath.FromSlash(strings.ReplaceAll(mod, ".", "/")))
			var ls []string
			for _, e := range moduleDataExts {
				if _, err := os.Lstat(base + e); err != nil {
					if e == ".olean" {
						return nil, fmt.Errorf("module %s has no compiled module data %s (the framework is not built)", mod, displayPath(base+e))
					}
					continue
				}
				s, err := c.fileSha(base + e)
				if err != nil {
					return nil, fmt.Errorf("module %s: %v", mod, err)
				}
				ls = append(ls, e+":"+s)
			}
			return ls, nil
		}}
}

// ---------------------------------------------------------------- directories and extractions

// skipDirName: build outputs and VCS data are not inputs.
func incrSkipDir(name string) bool { return name == ".lake" || name == ".git" }

// hashDir hashes every regular file of dir (relative path and bytes) except those skip rejects.
func (c *incrCtx) hashDir(dir string, skip func(rel string, d fs.DirEntry) bool, content func(rel string, b []byte) ([]byte, error)) ([]string, error) {
	base := c.abs(dir)
	var ls []string
	err := filepath.WalkDir(base, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(base, p)
		rel = filepath.ToSlash(rel)
		if rel == "." {
			return nil
		}
		if d.IsDir() {
			if incrSkipDir(d.Name()) || (skip != nil && skip(rel, d)) {
				return fs.SkipDir
			}
			return nil
		}
		if skip != nil && skip(rel, d) {
			return nil
		}
		if d.Type()&fs.ModeSymlink != 0 {
			t, err := os.Readlink(p)
			if err != nil {
				return err
			}
			ls = append(ls, "link "+rel+" -> "+t)
			return nil
		}
		if !d.Type().IsRegular() {
			return fmt.Errorf("%s is neither a regular file nor a link", rel)
		}
		b, err := os.ReadFile(p)
		if err != nil {
			return err
		}
		if content != nil {
			if b, err = content(rel, b); err != nil {
				return err
			}
		}
		ls = append(ls, "file "+rel+" "+sha256Hex(b))
		return nil
	})
	if err != nil {
		return nil, err
	}
	sort.Strings(ls)
	return ls, nil
}

// incrNormalIdentity removes the extraction's own location ("binary") from identity.json: it names where
// the extraction lives, not what it is (the binary's SHA-256 is "binarySha256").
func incrNormalIdentity(b []byte) ([]byte, error) {
	var m map[string]any
	if err := json.Unmarshal(b, &m); err != nil {
		return nil, fmt.Errorf("identity.json is not valid JSON: %v", err)
	}
	delete(m, "binary")
	return json.Marshal(m)
}

// artLines hashes an extraction directory: its files except the verifier's own outputs, identity.json
// normalized, and the binary identity.json names (read and hashed, and required to be the binary the
// identity says it is).
func (c *incrCtx) artLines(dir string) ([]string, error) {
	ls, err := c.hashDir(dir, func(rel string, d fs.DirEntry) bool {
		return rel == "verified.json" || rel == "verify.log" || rel == "verified" || strings.HasPrefix(rel, "verified/") ||
			strings.HasSuffix(rel, ".lock") || strings.HasSuffix(rel, ".olean") || strings.HasSuffix(rel, ".ilean")
	}, func(rel string, b []byte) ([]byte, error) {
		if rel == "identity.json" {
			return incrNormalIdentity(b)
		}
		return b, nil
	})
	if err != nil {
		return nil, err
	}
	idb, err := os.ReadFile(filepath.Join(c.abs(dir), "identity.json"))
	if err != nil {
		return nil, fmt.Errorf("no extraction: %v", err)
	}
	if _, err := os.Stat(filepath.Join(c.abs(dir), "Extracted.lean")); err != nil {
		return nil, fmt.Errorf("no extraction: %v", err)
	}
	var id struct {
		Binary       string `json:"binary"`
		BinarySha256 string `json:"binarySha256"`
	}
	if err := json.Unmarshal(idb, &id); err != nil || id.Binary == "" || id.BinarySha256 == "" {
		return nil, fmt.Errorf("identity.json names no binary")
	}
	bp := id.Binary
	if !filepath.IsAbs(bp) {
		bp = filepath.Join(c.abs(dir), bp)
	}
	got, err := c.fileSha(bp)
	if err != nil {
		return nil, fmt.Errorf("the binary named by identity.json: %v", err)
	}
	if got != id.BinarySha256 {
		return nil, fmt.Errorf("the binary %s has SHA-256 %s, not the %s of identity.json", id.Binary, got, id.BinarySha256)
	}
	return append(ls, "binary "+got), nil
}

// ---------------------------------------------------------------- the working tree (lanes)

func (c *incrCtx) treeLines(dir string, excl []string) ([]string, error) {
	cmd := exec.Command("git", "-C", c.abs(dir), "ls-files", "-z", "-c", "-o", "--exclude-standard")
	out, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("git ls-files: %v", err)
	}
	var ls []string
	seen := map[string]bool{}
	for _, p := range strings.Split(string(out), "\x00") {
		if p == "" || seen[p] {
			continue
		}
		seen[p] = true
		skip := false
		for _, e := range excl {
			if strings.HasSuffix(e, "/") && strings.HasPrefix(p, e) || p == e || strings.HasPrefix(e, "*") && strings.HasSuffix(p, e[1:]) {
				skip = true
			}
		}
		if skip {
			continue
		}
		fp := filepath.Join(c.abs(dir), p)
		st, err := os.Lstat(fp)
		if err != nil {
			ls = append(ls, "absent "+p) // tracked and deleted
			continue
		}
		switch {
		case st.Mode()&fs.ModeSymlink != 0:
			t, err := os.Readlink(fp)
			if err != nil {
				return nil, err
			}
			ls = append(ls, "link "+p+" -> "+t)
		case st.Mode().IsRegular():
			s, err := c.fileSha(fp)
			if err != nil {
				return nil, err
			}
			ls = append(ls, fmt.Sprintf("file %s %s %o", p, s, st.Mode().Perm()&0o111))
		default:
			ls = append(ls, "special "+p)
		}
	}
	sort.Strings(ls)
	return ls, nil
}

// ---------------------------------------------------------------- the key

func hashLines(ls []string) string {
	h := sha256.New()
	for _, l := range ls {
		fmt.Fprintf(h, "%d %s\n", len(l), l)
	}
	return hex.EncodeToString(h.Sum(nil))
}

func okComp(name, note string, lines []string) incrComp {
	return incrComp{Name: name, Hash: hashLines(lines), Note: note, Lines: lines}
}
func errComp(name string, err error) incrComp { return incrComp{Name: name, Err: err} }

// compute returns the components of sp and, when every one could be established, the key.
func (c *incrCtx) compute(sp *incrSpec) (string, []incrComp) {
	var comps []incrComp
	add := func(x incrComp) { comps = append(comps, x) }
	add(okComp("schema", "", []string{incrKeyHeader, fmt.Sprint(incrSchema)}))
	add(okComp("item", sp.ID+" ("+sp.Kind+")", append(append([]string{"id " + sp.ID, "kind " + sp.Kind}, prefixed("arg ", sp.Args)...), prefixed("virtual ", sp.Virtual)...)))
	envl := incrEnvLines(c.environ)
	add(okComp("env", fmt.Sprintf("%d variables", len(envl)), envl))
	if v, err := c.verifier(sp.Full); err != nil {
		add(errComp("verifier", err))
	} else {
		add(okComp("verifier", v, []string{v}))
	}
	if sp.Host {
		add(okComp("host", "", []string{c.host()}))
	}
	// the framework side
	if !sp.NoFW {
		fwModes := sp.FW
		if len(fwModes) == 0 {
			fwModes = []string{"embedded"}
		}
		for _, m := range fwModes {
			c.fwComps(sp, m, add)
		}
	} else if tc, err := c.tchainOf(); err != nil {
		add(errComp("toolchain", err))
	} else {
		add(c.toolchainComp("toolchain", tc))
	}
	for _, f := range sp.Proofs {
		if s, err := c.fileSha(f); err != nil {
			add(errComp("proof:"+f, err))
		} else {
			add(okComp("proof:"+f, "", []string{"proof " + f + " " + s}))
		}
	}
	for _, d := range sp.Pkgs {
		if ls, err := c.hashDir(d, nil, nil); err != nil {
			add(errComp("pkg:"+d, err))
		} else {
			add(okComp("pkg:"+d, fmt.Sprintf("%d files", len(ls)), ls))
		}
	}
	for _, d := range sp.Arts {
		if ls, err := c.artLines(d); err != nil {
			add(errComp("art:"+d, err))
		} else {
			add(okComp("art:"+d, fmt.Sprintf("%d entries", len(ls)), ls))
		}
	}
	for _, kv := range []struct {
		pfx string
		fs  []string
	}{{"file:", sp.Files}, {"pin:", sp.Pins}, {"script:", sp.Scripts}} {
		for _, f := range kv.fs {
			if s, err := c.fileSha(f); err != nil {
				add(errComp(kv.pfx+f, err))
			} else {
				add(okComp(kv.pfx+f, "", []string{f + " " + s}))
			}
		}
	}
	if sp.Tree != "" {
		if ls, err := c.treeLines(sp.Tree, sp.TreeExcl); err != nil {
			add(errComp("tree", err))
		} else {
			add(okComp("tree", fmt.Sprintf("%d files (excluding %s)", len(ls), strings.Join(sp.TreeExcl, " ")), ls))
		}
	}
	h := sha256.New()
	fmt.Fprintf(h, "%s\n", incrKeyHeader)
	for _, x := range comps {
		if x.Err != nil {
			return "", comps
		}
		fmt.Fprintf(h, "%s %s\n", x.Name, x.Hash)
	}
	return hex.EncodeToString(h.Sum(nil)), comps
}

func prefixed(p string, ls []string) []string {
	var o []string
	for _, l := range ls {
		o = append(o, p+l)
	}
	return o
}

func (c *incrCtx) tchainOf() (*toolchain, error) {
	return c.tchain(c.root)
}

func (c *incrCtx) toolchainComp(name string, tc *toolchain) incrComp {
	if !tc.hasChecker {
		return errComp(name, fmt.Errorf("the toolchain has no leanchecker (the kernel replay would be skipped)"))
	}
	return okComp(name, tc.version, []string{"version " + tc.version, "id " + tc.cacheID(), "lean " + tc.lean, "leanchecker " + tc.leanchecker})
}

func (c *incrCtx) fwComps(sp *incrSpec, mode string, add func(incrComp)) {
	var fw *framework
	var err error
	switch {
	case mode == "embedded":
		if c.getenv("JANUS_ROOT") != "" {
			add(errComp("fw:"+mode, fmt.Errorf("JANUS_ROOT is set: the verifier would use a checkout instead of the embedded framework")))
			return
		}
		fw, err = c.embedded()
	case strings.HasPrefix(mode, "dir:"):
		fw, err = c.loadDir(c.abs(strings.TrimPrefix(mode, "dir:")))
	default:
		err = fmt.Errorf("unknown framework mode %q", mode)
	}
	if err != nil {
		add(errComp("fw:"+mode, err))
		return
	}
	root, err := c.build(fw)
	if err != nil {
		add(errComp("fw:"+mode, err))
		return
	}
	tc, err := c.tchain(root)
	if err != nil {
		add(errComp("toolchain:"+mode, err))
	} else {
		add(c.toolchainComp("toolchain:"+mode, tc))
	}
	add(okComp("fw:"+mode+":config", fw.Source+" "+fw.Toolchain, []string{
		"lakefile.toml " + sha256Hex(fw.Files["lakefile.toml"]),
		"lake-manifest.json " + sha256Hex(fw.Files["lake-manifest.json"]),
		"lean-toolchain " + sha256Hex(fw.Files["lean-toolchain"]),
	}))
	fp := c.fwProvider(fw, root)
	// the item's modules
	roots := map[string][]byte{}
	var rootNames []string
	addRoot := func(name string, b []byte) { roots[name] = b; rootNames = append(rootNames, name) }
	provs := []incrProvider{fp}
	// The auditor's clean environment always imports the whole `Janus` library, whatever the proof imports
	// (Janus/Tools/Audit.lean, `cleanEnv`): so every verdict depends on its closure.
	addRoot("implicit: the auditor's clean environment imports Janus", []byte("import Janus\n"))
	for _, f := range sp.Proofs {
		b, err := os.ReadFile(c.abs(f))
		if err != nil {
			add(errComp("fw:"+mode+":closure", err))
			return
		}
		addRoot("proof "+f, b)
	}
	for _, d := range append(append([]string{}, sp.Pkgs...), sp.Arts...) {
		provs = append(provs, c.dirProvider(d))
		var leans []string
		_ = filepath.WalkDir(c.abs(d), func(p string, e fs.DirEntry, err error) error {
			if err == nil && e.IsDir() && incrSkipDir(e.Name()) {
				return fs.SkipDir
			}
			if err == nil && !e.IsDir() && strings.HasSuffix(p, ".lean") {
				leans = append(leans, p)
			}
			return nil
		})
		sort.Strings(leans)
		for _, p := range leans {
			b, err := os.ReadFile(p)
			if err != nil {
				add(errComp("fw:"+mode+":closure", err))
				return
			}
			rel, _ := filepath.Rel(c.abs(d), p)
			addRoot("local "+d+"/"+filepath.ToSlash(rel), b)
		}
	}
	if len(rootNames) > 0 {
		ls, err := c.closure(rootNames, roots, provs, nil, sp.Virtual...)
		if err != nil {
			add(errComp("fw:"+mode+":closure", err))
		} else {
			add(okComp("fw:"+mode+":closure", fmt.Sprintf("%d lines", len(ls)), ls))
		}
	}
	// the auditor: its sources, closure and compiled modules, and the compiled executable
	ar := map[string][]byte{}
	var an []string
	for _, m := range []string{"Janus.Tools.Audit", "Janus.Tools.AuditMain"} {
		b, ok := fw.Files[strings.ReplaceAll(m, ".", "/")+".lean"]
		if !ok {
			add(errComp("fw:"+mode+":auditor", fmt.Errorf("the framework has no %s", m)))
			return
		}
		ar[m] = b
		an = append(an, m)
	}
	als, err := c.closure(an, ar, []incrProvider{fp}, func(m string) bool { return m != "Janus.Tools.AuditMain" })
	if err != nil {
		add(errComp("fw:"+mode+":auditor", err))
		return
	}
	exe, err := c.fileSha(auditExePath(root))
	if err != nil {
		add(errComp("fw:"+mode+":auditor", fmt.Errorf("the compiled auditor: %v", err)))
		return
	}
	add(okComp("fw:"+mode+":auditor", "janus-audit "+exe[:12], append(als, "janus-audit "+exe)))
}

// ---------------------------------------------------------------- records

type incrRecord struct {
	Schema   int     `json:"schema"`
	Key      string  `json:"key"`
	ID       string  `json:"id"`
	Kind     string  `json:"kind"`
	Result   string  `json:"result"`
	Started  string  `json:"started"`
	Finished string  `json:"finished"`
	Wall     float64 `json:"wallSeconds"`
	Host     string  `json:"host"`
	Commit   string  `json:"commit"`
	Verifier string  `json:"verifier"`
}

type incrEntry struct {
	Key  string          `json:"key"`
	Body json.RawMessage `json:"body"`
	MAC  string          `json:"mac"`
}

func incrDir() string { return filepath.Join(resultCacheDir(), ".incr") }

func incrPath(key string) string { return filepath.Join(incrDir(), key[:2], key+".json") }

func incrMAC(hk []byte, key string, body []byte) string {
	m := hmac.New(sha256.New, hk)
	fmt.Fprintf(m, "janus-incr-record-v1\n%s\n", key)
	m.Write(body)
	return hex.EncodeToString(m.Sum(nil))
}

func validKey(key string) bool {
	if len(key) != 64 {
		return false
	}
	for _, r := range key {
		if !(r >= '0' && r <= '9' || r >= 'a' && r <= 'f') {
			return false
		}
	}
	return true
}

// incrLookup returns the authentic PASS record for key, else nil and why not.
func incrLookup(key string) (*incrRecord, string) {
	if !validKey(key) {
		return nil, "no key"
	}
	b, err := readPrivateFile(incrPath(key), false)
	if err != nil {
		if os.IsNotExist(err) {
			return nil, "no record"
		}
		return nil, "unreadable record: " + err.Error()
	}
	hk, err := resultHMACKey()
	if err != nil {
		return nil, "no cache key: " + err.Error()
	}
	var e incrEntry
	dec := json.NewDecoder(bytes.NewReader(b))
	dec.DisallowUnknownFields()
	if err := dec.Decode(&e); err != nil {
		return nil, "unparsable record: " + err.Error()
	}
	if _, err := dec.Token(); err != io.EOF {
		return nil, "unparsable record: trailing data"
	}
	if e.Key != key {
		return nil, "record belongs to another key"
	}
	if !hmac.Equal([]byte(e.MAC), []byte(incrMAC(hk, key, e.Body))) {
		return nil, "record fails authentication"
	}
	var r incrRecord
	bd := json.NewDecoder(bytes.NewReader(e.Body))
	bd.DisallowUnknownFields()
	if err := bd.Decode(&r); err != nil {
		return nil, "unparsable record body: " + err.Error()
	}
	if r.Schema != incrSchema || r.Key != key || r.Result != "pass" {
		return nil, "record is not a PASS of this key"
	}
	return &r, ""
}

func incrStore(key string, r *incrRecord) error {
	if !validKey(key) {
		return fmt.Errorf("no key")
	}
	hk, err := resultHMACKey()
	if err != nil {
		return err
	}
	body, err := json.Marshal(r)
	if err != nil {
		return err
	}
	b, _ := json.Marshal(incrEntry{Key: key, Body: body, MAC: incrMAC(hk, key, body)})
	p := incrPath(key)
	if err := os.MkdirAll(filepath.Dir(p), 0o700); err != nil {
		return err
	}
	return writeFileAtomic(p, b)
}

func incrDrop(key string) {
	if validKey(key) {
		_ = os.Remove(incrPath(key))
	}
}

// ---------------------------------------------------------------- the command

func parseIncrFlags(args []string) (sp *incrSpec, opts map[string]string, err error) {
	sp = &incrSpec{}
	opts = map[string]string{}
	need := func(i int) (string, error) {
		if i+1 >= len(args) {
			return "", fmt.Errorf("%s needs a value", args[i])
		}
		return args[i+1], nil
	}
	for i := 0; i < len(args); i++ {
		a := args[i]
		switch a {
		case "--host":
			sp.Host = true
			continue
		case "--full-verifier":
			sp.Full = true
			continue
		case "--no-fw":
			sp.NoFW = true
			continue
		case "--verbose":
			opts["verbose"] = "1"
			continue
		}
		v, err := need(i)
		if err != nil {
			return nil, nil, err
		}
		i++
		switch a {
		case "--id":
			sp.ID = v
		case "--kind":
			sp.Kind = v
		case "--root":
			sp.Root = v
		case "--fw":
			sp.FW = append(sp.FW, v)
		case "--proof":
			sp.Proofs = append(sp.Proofs, v)
		case "--pkg":
			sp.Pkgs = append(sp.Pkgs, v)
		case "--art":
			sp.Arts = append(sp.Arts, v)
		case "--file":
			sp.Files = append(sp.Files, v)
		case "--pin":
			sp.Pins = append(sp.Pins, v)
		case "--script":
			sp.Scripts = append(sp.Scripts, v)
		case "--arg":
			sp.Args = append(sp.Args, v)
		case "--virtual":
			sp.Virtual = append(sp.Virtual, v)
		case "--tree":
			sp.Tree = v
		case "--tree-exclude":
			sp.TreeExcl = append(sp.TreeExcl, v)
		case "--pre-key", "--rc", "--wall", "--started":
			opts[strings.TrimPrefix(a, "--")] = v
		default:
			return nil, nil, fmt.Errorf("unknown flag %s", a)
		}
	}
	if sp.ID == "" {
		return nil, nil, fmt.Errorf("--id is required")
	}
	if strings.ContainsAny(sp.ID, "\t\n") {
		return nil, nil, fmt.Errorf("--id must not contain a tab or newline")
	}
	for _, a := range sp.Args {
		if strings.ContainsAny(a, "\n") {
			return nil, nil, fmt.Errorf("--arg must not contain a newline")
		}
	}
	return sp, opts, nil
}

func firstErr(comps []incrComp) error {
	for _, x := range comps {
		if x.Err != nil {
			return fmt.Errorf("%s: %v", x.Name, x.Err)
		}
	}
	return nil
}

func oneLine(s string) string {
	return strings.Join(strings.Fields(strings.ReplaceAll(s, "\t", " ")), " ")
}

var incrNow = time.Now

func cmdIncr(args []string, stdout, stderr io.Writer) error {
	if len(args) == 0 {
		return fmt.Errorf("usage: janus incr check|record|explain --id ID [--kind K] [--fw embedded|dir:PATH] [--proof F] [--pkg D] [--art D] [--file F] [--pin F] [--script F] [--arg A] [--tree D --tree-exclude P] [--host]")
	}
	sub := args[0]
	sp, opts, err := parseIncrFlags(args[1:])
	if err != nil {
		return err
	}
	root := sp.Root
	if root == "" {
		root, _ = os.Getwd()
	}
	return runIncr(newIncrCtx(root), sub, sp, opts, stdout)
}

func runIncr(c *incrCtx, sub string, sp *incrSpec, opts map[string]string, stdout io.Writer) error {
	key, comps := c.compute(sp)
	switch sub {
	case "check":
		if key == "" {
			fmt.Fprintf(stdout, "NOKEY\t\t%s\n", oneLine(firstErr(comps).Error()))
			return nil
		}
		r, why := incrLookup(key)
		if r == nil {
			fmt.Fprintf(stdout, "RUN\t%s\t%s\n", key, why)
			return nil
		}
		fmt.Fprintf(stdout, "SKIP\t%s\t%s\t%s\t%s\t%.1f\n", key, oneLine(r.Finished), oneLine(r.Host), oneLine(r.Commit), r.Wall)
		return nil
	case "record":
		rc, err := strconv.Atoi(opts["rc"])
		if err != nil {
			return fmt.Errorf("record needs --rc N")
		}
		pre := opts["pre-key"]
		if rc != 0 {
			// a failed run is never a pass, and a pass recorded earlier for these inputs is stale evidence
			// of a flaky or environment-dependent item: drop it
			incrDrop(pre)
			incrDrop(key)
			fmt.Fprintf(stdout, "NOTRECORDED\tthe run failed (rc %d); no record is kept for its key\n", rc)
			return nil
		}
		if key == "" {
			fmt.Fprintf(stdout, "NOTRECORDED\tinputs cannot be keyed: %s\n", oneLine(firstErr(comps).Error()))
			return nil
		}
		if pre == "" || pre != key {
			fmt.Fprintf(stdout, "NOTRECORDED\tthe inputs changed during the run (or were not keyed before it)\n")
			return nil
		}
		wall, _ := strconv.ParseFloat(opts["wall"], 64)
		vid, _ := c.verifier(sp.Full)
		now := incrNow().UTC()
		r := &incrRecord{Schema: incrSchema, Key: key, ID: sp.ID, Kind: sp.Kind, Result: "pass",
			Started: opts["started"], Finished: now.Format(time.RFC3339), Wall: wall, Host: hostName(), Commit: gitDescribe(c.root), Verifier: vid}
		if err := incrStore(key, r); err != nil {
			fmt.Fprintf(stdout, "NOTRECORDED\tcannot write the record: %s\n", oneLine(err.Error()))
			return nil
		}
		fmt.Fprintf(stdout, "RECORDED\t%s\n", key)
		return nil
	case "explain":
		fmt.Fprintf(stdout, "item %s (%s)\n", sp.ID, sp.Kind)
		for _, x := range comps {
			if x.Err != nil {
				fmt.Fprintf(stdout, "  %-34s UNHASHABLE: %s\n", x.Name, oneLine(x.Err.Error()))
				continue
			}
			fmt.Fprintf(stdout, "  %-34s %s  %s\n", x.Name, x.Hash, x.Note)
			if opts["verbose"] != "" {
				for _, l := range x.Lines {
					fmt.Fprintf(stdout, "      %s\n", l)
				}
			}
		}
		if key == "" {
			fmt.Fprintf(stdout, "key: none (%s): the item always runs\n", oneLine(firstErr(comps).Error()))
			return nil
		}
		fmt.Fprintf(stdout, "key: %s\n", key)
		if r, why := incrLookup(key); r != nil {
			fmt.Fprintf(stdout, "record: PASS of %s on %s at %s (%.1fs): the item would be SKIPPED in an incremental run\n", r.Finished, r.Host, r.Commit, r.Wall)
		} else {
			fmt.Fprintf(stdout, "record: none (%s): the item would RUN\n", why)
		}
		return nil
	}
	return fmt.Errorf("unknown incr command %q", sub)
}

func hostName() string {
	h, err := os.Hostname()
	if err != nil {
		return "?"
	}
	return h
}

// gitDescribe is informational (it is not part of the key): the short commit of dir, "+dirty" if the
// tree differs from it.
func gitDescribe(dir string) string {
	out, err := exec.Command("git", "-C", dir, "rev-parse", "--short=12", "HEAD").Output()
	if err != nil {
		return "unknown"
	}
	c := strings.TrimSpace(string(out))
	if st, err := exec.Command("git", "-C", dir, "status", "--porcelain", "--untracked-files=no").Output(); err == nil && len(bytes.TrimSpace(st)) > 0 {
		c += "+dirty"
	}
	return c
}
