package main

// Olean provenance of a consumer package (round 15a).
//
// Lake builds the consumer's modules inside the sandbox, where the untrusted lakefile and every
// elaborated module can write the build directory: a planted olean (with a forged trace, or
// written after the build by the lakefile that `lake query` runs again) is indistinguishable from
// a built one. The audit, the kernel replay and the pins would then judge an environment that is
// not the one the hashed SOURCE defines, while the report (and a cached result keyed on the source)
// attests the source.
//
// So the oleans the audit and the replay use are Janus's own. For the theorem's consumer import
// closure, in dependency order, janus runs `lean -o` itself, sandboxed, on the hashed source (a
// trusted copy of the snapshot that no sandboxed process can write), with the package's leanOptions,
// into a per-module scratch directory; the olean is copied into a janus-owned directory that
// no sandboxed process can write (it is a protected mount), and only that directory is on the search
// path from then on. Lake's oleans for those modules are never read. The warm path is a record in
// the trusted olean store (an HMAC'd entry keyed by the toolchain, the framework build, the module,
// its source hash, its options and the hashes of its own imports, hence transitively of its whole
// closure): the stored bytes are re-hashed on use, so no compile is repeated for an unchanged module.
//
// Only configurations the strict TOML subset of lakefiletoml.go understands (the ones the result
// cache accepts) can be compiled this way, because janus must know every option Lake would pass.
// Others are reported "unchecked" and are refused unless --allow-unchecked-provenance is given.

import (
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync/atomic"
)

const (
	provChecked   = "checked"
	provUnchecked = "unchecked"
)

// ownCompiles counts the compiles janus ran itself (tests: a warm run runs none).
var ownCompiles atomic.Int64

// provPkg is one package whose modules janus compiles.
type provPkg struct {
	name    string // "" for the consumer, else the dependency's name
	files   map[string][]byte
	srcDirs []string // slash paths relative to the package ("" or "." = the package root), cleaned
	dopts   []string // -Dname=value arguments from [leanOptions]
	src     string   // trusted copy of files
	lib     string   // janus-owned olean directory
	synced  bool
}

// compileConfig extracts what Lake would pass to `lean` for a package of the strict subset: the
// source directories and the -D options. ok is false for any configuration outside the subset.
func compileConfig(files map[string][]byte, config string) (srcDirs, dopts []string, ok bool) {
	if !lakefileCacheable(files, config) {
		return nil, nil, false
	}
	pairs, ok := parseLakefileToml(string(files[config]))
	if !ok {
		return nil, nil, false
	}
	top := ""
	libDirs := map[string]bool{}
	for _, p := range pairs {
		switch {
		case p.table == "leanOptions":
			v := p.raw
			switch {
			case p.isStr:
				v = p.str
			case v == "true" || v == "false":
			default:
				v = strings.ReplaceAll(strings.TrimPrefix(v, "+"), "_", "")
				if _, err := strconv.ParseInt(v, 10, 64); err != nil {
					return nil, nil, false
				}
			}
			dopts = append(dopts, "-D"+p.key+"="+v)
		case p.key == "srcDir":
			if p.table == "" {
				top = path.Clean(p.str)
			} else if p.table == "lean_lib" || p.table == "lean_exe" {
				libDirs[path.Clean(p.str)] = true
			}
		}
	}
	set := map[string]bool{top: true}
	for d := range libDirs {
		set[d] = true
	}
	for d := range set {
		if d == "." {
			d = ""
		}
		srcDirs = append(srcDirs, d)
	}
	sort.Strings(srcDirs)
	return dedup(srcDirs), dopts, true
}

// parseImports reads the import header of a Lean source: `module`, `prelude`, and the `import`
// commands with their modifiers. ok is false for anything it does not understand (an unterminated
// comment, a non-ASCII or guillemet module name).
func parseImports(src []byte) (imports []string, ok bool) {
	s := string(src)
	i := 0
	skip := func() bool {
		for i < len(s) {
			switch {
			case s[i] == ' ' || s[i] == '\t' || s[i] == '\n' || s[i] == '\r':
				i++
			case strings.HasPrefix(s[i:], "--"):
				for i < len(s) && s[i] != '\n' {
					i++
				}
			case strings.HasPrefix(s[i:], "/-") && !strings.HasPrefix(s[i:], "/--") && !strings.HasPrefix(s[i:], "/-!"):
				depth := 0
				for {
					switch {
					case i >= len(s):
						return false
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
				return true
			}
		}
		return true
	}
	isWord := func(c byte) bool {
		return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' || c == '_' || c == '.' || c == '\''
	}
	word := func() string {
		st := i
		for i < len(s) && isWord(s[i]) {
			i++
		}
		return s[st:i]
	}
	for {
		if !skip() {
			return nil, false
		}
		if i >= len(s) {
			return imports, true
		}
		if s[i] >= 0x80 || s[i] == '\xc2' {
			return nil, false
		}
		w := word()
		switch w {
		case "module", "prelude":
			continue
		case "import":
			for {
				if !skip() {
					return nil, false
				}
				if i >= len(s) || s[i] >= 0x80 || s[i] == '\xc2' {
					return nil, false
				}
				m := word()
				if m == "" {
					return nil, false
				}
				if m == "public" || m == "meta" || m == "all" {
					continue
				}
				if strings.HasPrefix(m, ".") || strings.HasSuffix(m, ".") || strings.Contains(m, "..") {
					return nil, false
				}
				imports = append(imports, m)
				break
			}
		default:
			return imports, true // the header ended
		}
	}
}

// ownBuild compiles the closure of the requested modules.
type ownBuild struct {
	ws       *consumerWS
	pkgs     []*provPkg
	dir      string
	janusLib string
	done     map[string]*ownMod
	busy     map[string]bool
	hits     int
	compiled int
}

type ownMod struct {
	sha string // of the olean janus holds
	rel string // source path inside the package
	pkg *provPkg
}

// newOwnBuild prepares the compile of the consumer package; it returns the reason when some
// package is outside the strict subset (the provenance is then "unchecked").
func newOwnBuild(ws *consumerWS, pkg *consumerPkg) (*ownBuild, string) {
	ob := &ownBuild{ws: ws, dir: ws.ownDir(), janusLib: ws.janusLib(), done: map[string]*ownMod{}, busy: map[string]bool{}}
	add := func(name string, files map[string][]byte, config string) string {
		sd, do, ok := compileConfig(files, config)
		if !ok {
			who := "the consumer package"
			if name != "" {
				who = "the dependency " + name
			}
			return fmt.Sprintf("%s has a Lake configuration (%s) outside the strict lakefile.toml subset janus can reproduce", who, config)
		}
		tag := "root"
		if name != "" {
			tag = "deps/" + name
		}
		ob.pkgs = append(ob.pkgs, &provPkg{name: name, files: files, srcDirs: sd, dopts: do,
			src: filepath.Join(ob.dir, "src", filepath.FromSlash(tag)), lib: filepath.Join(ob.dir, "lib", filepath.FromSlash(tag))})
		return ""
	}
	if why := add("", pkg.Files, pkg.Lakefile); why != "" {
		return nil, why
	}
	for _, d := range pkg.Deps {
		if why := add(d.Info.Name, d.Files, d.Config); why != "" {
			return nil, why
		}
	}
	return ob, ""
}

// locate finds the package and source path of module m among the packages' hashed files.
func (ob *ownBuild) locate(m string) (*provPkg, string, string, int) {
	var hp *provPkg
	var hrel, hroot string
	n := 0
	for _, p := range ob.pkgs {
		for _, sd := range p.srcDirs {
			rel := path.Join(sd, strings.ReplaceAll(m, ".", "/")+".lean")
			if _, ok := p.files[rel]; ok {
				hp, hrel, hroot = p, rel, sd
				n++
			}
		}
	}
	return hp, hrel, hroot, n
}

func (ob *ownBuild) externalOlean(m string) bool {
	rel := strings.ReplaceAll(m, ".", "/") + ".olean"
	for _, d := range []string{ob.janusLib, ob.ws.tc.libDir} {
		if _, err := os.Stat(filepath.Join(d, filepath.FromSlash(rel))); err == nil {
			return true
		}
	}
	return false
}

func provDiag(msg string) error {
	return &diag{Invalid: true, Stage: "olean provenance", Msg: msg,
		Next: "Fix the module, or use a plain lakefile.toml; --allow-unchecked-provenance accepts oleans janus did not build itself (the report then says so)."}
}

func (ob *ownBuild) leanPath() string {
	dirs := []string{}
	for _, p := range ob.pkgs {
		dirs = append(dirs, p.lib)
	}
	return ob.ws.tc.leanPathEnv(append(dirs, ob.janusLib)...)
}

// ensure makes janus's own olean of module m (and of its consumer/dependency imports) current and
// returns its record. rel, when not empty, must be the module's source path.
func (ob *ownBuild) ensure(m, rel string) (*ownMod, error) {
	if om, ok := ob.done[m]; ok {
		if rel != "" && om.rel != rel {
			return nil, provDiag(fmt.Sprintf("module %s is the file %s, not %s", m, om.rel, rel))
		}
		return om, nil
	}
	if ob.busy[m] {
		return nil, provDiag("import cycle through " + m)
	}
	ob.busy[m] = true
	defer delete(ob.busy, m)
	pkg, srel, sroot, n := ob.locate(m)
	if n == 0 {
		return nil, provDiag(fmt.Sprintf("module %s is not a source file of the consumer package or its dependencies", m))
	}
	if n > 1 {
		return nil, provDiag(fmt.Sprintf("module %s is defined by more than one source file", m))
	}
	if ob.externalOlean(m) {
		return nil, provDiag(fmt.Sprintf("module %s is also provided by the framework or the toolchain", m))
	}
	if rel != "" && srel != rel {
		return nil, provDiag(fmt.Sprintf("module %s is the file %s, not %s", m, srel, rel))
	}
	srcBytes := pkg.files[srel]
	imps, ok := parseImports(srcBytes)
	if !ok {
		return nil, provDiag(fmt.Sprintf("cannot read the import header of %s", srel))
	}
	var own []string
	for _, imp := range imps {
		if _, _, _, c := ob.locate(imp); c > 0 {
			om, err := ob.ensure(imp, "")
			if err != nil {
				return nil, err
			}
			own = append(own, imp+" "+om.sha)
			continue
		}
		if !ob.externalOlean(imp) {
			return nil, provDiag(fmt.Sprintf("%s imports %s, which is neither a module of the packages nor of the framework or the toolchain", srel, imp))
		}
	}
	sort.Strings(own)
	if err := syncTreeOwn(pkg); err != nil {
		return nil, wsDiag(err)
	}
	key := ob.moduleKey(pkg, m, srel, srcBytes, own)
	oleanPath := filepath.Join(pkg.lib, filepath.FromSlash(strings.ReplaceAll(m, ".", "/"))+".olean")
	if err := os.MkdirAll(filepath.Dir(oleanPath), 0o755); err != nil {
		return nil, wsDiag(err)
	}
	var data []byte
	if ob.ws.replayCache {
		if d, ok := oleanStoreGet(key); ok {
			data = d
			ob.hits++
		}
	}
	if data == nil {
		work := filepath.Join(ob.ws.Dir, "ownwork")
		_ = os.RemoveAll(work)
		if err := os.MkdirAll(work, 0o755); err != nil {
			return nil, wsDiag(err)
		}
		out := filepath.Join(work, "out.olean")
		argv := []string{ob.ws.tc.lean, "--root=" + filepath.Join(pkg.src, filepath.FromSlash(sroot)), "-o", out}
		argv = append(argv, pkg.dopts...)
		argv = append(argv, filepath.Join(pkg.src, filepath.FromSlash(srel)))
		ownCompiles.Add(1)
		ob.compiled++
		lp := ob.leanPath()
		o, err := runLeanProtected(ob.ws.sb, ob.ws.tc, work, nil, ob.ws.protected(true), lp, argv...)
		if err != nil {
			return nil, &diag{Invalid: true, Stage: "olean provenance",
				Msg:  fmt.Sprintf("janus's own compile of %s (the hashed source, the package's options) failed, although the Lake build succeeded:\n%s", m, summarizeLeanErrors(o, 2000)),
				Next: "Check the module for code that behaves differently outside Lake (include_str of a file outside the snapshot, an option set by the lakefile)."}
		}
		data, err = os.ReadFile(out)
		if err != nil || len(data) == 0 {
			return nil, provDiag(fmt.Sprintf("janus's own compile of %s produced no olean", m))
		}
		_ = os.RemoveAll(work)
		if ob.ws.replayCache {
			oleanStorePut(key, data)
		}
	}
	if err := os.WriteFile(oleanPath, data, 0o644); err != nil {
		return nil, wsDiag(err)
	}
	om := &ownMod{sha: sha256Hex(data), rel: srel, pkg: pkg}
	ob.done[m] = om
	return om, nil
}

// syncTreeOwn writes the trusted copy of a package's hashed files (once per build).
func syncTreeOwn(p *provPkg) error {
	if p.synced {
		return nil
	}
	if err := syncTree(p.src, p.files, func(string) bool { return false }); err != nil {
		return err
	}
	p.synced = true
	return nil
}

func (ob *ownBuild) moduleKey(pkg *provPkg, m, rel string, src []byte, own []string) string {
	h := sha256.New()
	fmt.Fprintf(h, "janus-own-olean-v1\n%q\n%s\n", ob.ws.tc.cacheID(), pinsDigest(ob.ws.pins.want))
	fmt.Fprintf(h, "package %q\nmodule %q\nsource %q %s\nopts %q\nimports %q\n", pkg.name, m, rel, sha256Hex(src), pkg.dopts, own)
	return hex.EncodeToString(h.Sum(nil))
}

// libs returns the consumer's and the dependencies' janus-owned olean directories (created).
func (ob *ownBuild) libs() (string, map[string]string, error) {
	deps := map[string]string{}
	for _, p := range ob.pkgs {
		if err := os.MkdirAll(p.lib, 0o755); err != nil {
			return "", nil, err
		}
		if p.name != "" {
			deps[p.name] = p.lib
		}
	}
	return ob.pkgs[0].lib, deps, nil
}

// reset empties the owned olean directories (a run starts from nothing; the store refills them).
func (ob *ownBuild) reset() error {
	// the whole directory: a sandboxed Lake build may have created entries (even links) here before it existed
	if err := os.RemoveAll(ob.dir); err != nil {
		return err
	}
	_ = os.RemoveAll(filepath.Join(ob.ws.Dir, "ownwork"))
	for _, p := range ob.pkgs {
		if err := os.MkdirAll(p.lib, 0o755); err != nil {
			return err
		}
	}
	return os.MkdirAll(ob.dir, 0o755)
}

// ownDir is the janus-owned directory of a workspace: no sandboxed process may write it.
func (ws *consumerWS) ownDir() string { return filepath.Join(ws.Dir, "own") }

// ---- the trusted olean store ----

func oleanStoreDir() string { return filepath.Join(cacheRoot(), "v1", "oleans") }

type oleanEntry struct {
	Key string `json:"key"`
	Sha string `json:"sha256"`
	MAC string `json:"mac"`
}

func oleanMAC(hk []byte, key, sha string) string {
	m := hmac.New(sha256.New, hk)
	fmt.Fprintf(m, "janus-olean-entry-v1\n%q\n%q\n", key, sha)
	return hex.EncodeToString(m.Sum(nil))
}

// oleanStoreGet returns the stored olean of key if its entry is authentic and the bytes match.
func oleanStoreGet(key string) ([]byte, bool) {
	if len(key) < 3 {
		return nil, false
	}
	dir := filepath.Join(oleanStoreDir(), key[:2])
	b, err := readPrivateFile(filepath.Join(dir, key+".json"), false)
	if err != nil {
		return nil, false
	}
	var e oleanEntry
	hk, err := resultHMACKey()
	if err != nil || json.Unmarshal(b, &e) != nil || e.Key != key || !hmac.Equal([]byte(e.MAC), []byte(oleanMAC(hk, key, e.Sha))) {
		return nil, false
	}
	data, err := readPrivateFile(filepath.Join(dir, key+".olean"), false)
	if err != nil || sha256Hex(data) != e.Sha {
		return nil, false
	}
	touchHit(filepath.Join(dir, key+".json"))
	return data, true
}

// oleanStorePut records a freshly compiled olean (data first, then the authenticating entry).
func oleanStorePut(key string, data []byte) {
	if len(key) < 3 {
		return
	}
	hk, err := resultHMACKey()
	if err != nil {
		return
	}
	dir := filepath.Join(oleanStoreDir(), key[:2])
	if os.MkdirAll(dir, 0o755) != nil {
		return
	}
	sha := sha256Hex(data)
	if writeFileAtomic(filepath.Join(dir, key+".olean"), data) != nil {
		return
	}
	e, _ := json.Marshal(oleanEntry{Key: key, Sha: sha, MAC: oleanMAC(hk, key, sha)})
	_ = writeFileAtomic(filepath.Join(dir, key+".json"), e)
}
