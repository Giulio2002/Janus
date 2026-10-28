package main

// The verifier identity: the result cache's name for "the code that decides a verdict".
//
// The result cache (resultcache.go) used to key on the SHA-256 of the janus executable. Every
// checkout builds its own executable, so identical items from different branches never shared a
// hit. The identity below is instead a content hash of everything the executable is built from,
// computed by the executable itself from data the Go toolchain embedded at build time:
//
//   - the Go source of this module that the command is built from: every .go file of the
//     repository root and of cmd/janus (framework.go, GoSources), plus go.mod and go.sum, as
//     go:embed read them from the tree being built (so an edited, added or overlaid file is in);
//   - the Lean framework and the JanusASL package, as embedded (Framework, ASL);
//   - the dependency modules the binary was linked with (debug.ReadBuildInfo: path, version and
//     the go.sum content hash of each), which must agree with the embedded go.sum;
//   - the Go toolchain version and every recorded build setting (GOOS, GOARCH and their levels,
//     tags, ldflags, gcflags, asmflags, trimpath, race/msan/asan, GOEXPERIMENT, GODEBUG
//     defaults, cgo flags, buildmode, compiler);
//   - the result-cache schema version.
//
// Anything that cannot be established exactly makes verifierComponent fall back to the SHA-256
// of the executable's bytes (the previous key): no build information, a test binary, `go run`,
// a build from a modified VCS tree, replaced/unsummed/vendored dependencies, a compiler other
// than gc, cgo enabled (its C compiler is not recorded in the build information), an embedded
// source set that is incomplete or inconsistent with the build information, or a binary whose
// own file cannot be read. A fallback is never less strict than before, only less shareable.

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"io/fs"
	"os"
	"runtime"
	"runtime/debug"
	"sort"
	"strings"
	"sync"
	"testing"

	janus "github.com/Giulio2002/Janus"
)

// resultCacheSchema is bumped whenever the meaning of a cached entry or of the key changes.
const resultCacheSchema = 2

const verifierIDVersion = "janus-verifier-id-v1"

// buildSnapshot is everything the identity is computed from; production uses currentBuild, the
// tests construct their own.
type buildSnapshot struct {
	Info      *debug.BuildInfo // nil: unavailable
	Sources   fs.FS            // go.mod, go.sum, *.go, cmd/janus/*.go
	Framework fs.FS
	ASL       fs.FS
	Testing   bool // a `go test` binary
	// RuntimeVersion is runtime.Version() of the running executable; it must equal the toolchain
	// version recorded by the build.
	RuntimeVersion string
}

func currentBuild() buildSnapshot {
	bi, ok := debug.ReadBuildInfo()
	if !ok {
		bi = nil
	}
	return buildSnapshot{Info: bi, Sources: janus.GoSources, Framework: janus.Framework, ASL: janus.ASL, Testing: testing.Testing(), RuntimeVersion: runtime.Version()}
}

// identityFile is a source file of the Go build, as hashed.
func identityGoFile(p string) bool {
	return !strings.HasSuffix(p, "_test.go") && (strings.HasSuffix(p, ".go") || p == "go.mod" || p == "go.sum")
}

func hashPut(h io.Writer, tag string, b []byte) {
	fmt.Fprintf(h, "%s %d\n", tag, len(b))
	h.Write(b)
	h.Write([]byte{'\n'})
}

// hashTree adds every regular file of fsys (sorted by path) that keep selects.
func hashTree(h io.Writer, tag string, fsys fs.FS, keep func(string) bool) (int, error) {
	if fsys == nil {
		return 0, fmt.Errorf("%s: missing", tag)
	}
	var paths []string
	err := fs.WalkDir(fsys, ".", func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.Type().IsRegular() && (keep == nil || keep(p)) {
			paths = append(paths, p)
		}
		return nil
	})
	if err != nil {
		return 0, fmt.Errorf("%s: %v", tag, err)
	}
	sort.Strings(paths)
	for _, p := range paths {
		b, err := fs.ReadFile(fsys, p)
		if err != nil {
			return 0, fmt.Errorf("%s: %v", tag, err)
		}
		fmt.Fprintf(h, "%s %s %s\n", tag, p, sha256Hex(b))
	}
	return len(paths), nil
}

// sourceMarkers must be among the embedded sources, or the embed is not the one of this module.
var sourceMarkers = []string{"go.mod", "go.sum", "framework.go", "cmd/janus/main.go", "cmd/janus/verifierid.go", "cmd/janus/resultcache.go"}

// verifierIdentity returns the content identity of the build b, or the reason it cannot be
// established exactly (the caller then uses the executable's hash).
func verifierIdentity(b buildSnapshot) (string, error) { return verifierIdentityScope(b, true) }

// verifierIdentityScope is verifierIdentity with the Lean trees optional. With lean=false the
// identity covers the Go side only (the Go sources, the dependencies, the build settings), not
// the embedded Lean framework and JanusASL: the incremental gate (incr.go) keys the Lean side
// itself, per item, by the transitive import closure of what the item imports, so that an edit
// of a framework module the item does not import does not change its key. The two identities
// are distinct strings (a Go-only identity never equals a full one).
func verifierIdentityScope(b buildSnapshot, lean bool) (string, error) {
	if b.Testing {
		return "", fmt.Errorf("a test binary")
	}
	bi := b.Info
	if bi == nil {
		return "", fmt.Errorf("no build information")
	}
	if bi.Path != "github.com/Giulio2002/Janus/cmd/janus" || bi.Main.Path != "github.com/Giulio2002/Janus" {
		return "", fmt.Errorf("not built as the janus command of its module (package %q, module %q)", bi.Path, bi.Main.Path)
	}
	if !strings.HasPrefix(bi.GoVersion, "go") && !strings.HasPrefix(bi.GoVersion, "devel") {
		return "", fmt.Errorf("unknown Go version %q", bi.GoVersion)
	}
	if bi.GoVersion != b.RuntimeVersion {
		return "", fmt.Errorf("Go version %q differs from the runtime's %q", bi.GoVersion, b.RuntimeVersion)
	}
	settings := map[string]string{}
	for _, s := range bi.Settings {
		if _, dup := settings[s.Key]; dup {
			return "", fmt.Errorf("duplicate build setting %s", s.Key)
		}
		settings[s.Key] = s.Value
	}
	if settings["vcs.modified"] == "true" {
		return "", fmt.Errorf("built from a modified VCS tree")
	}
	if settings["-compiler"] != "gc" {
		return "", fmt.Errorf("compiler %q is not gc", settings["-compiler"])
	}
	if settings["CGO_ENABLED"] != "0" {
		return "", fmt.Errorf("cgo is enabled (CGO_ENABLED=%q; its C compiler is not recorded in the build information)", settings["CGO_ENABLED"])
	}
	if settings["GOOS"] == "" || settings["GOARCH"] == "" {
		return "", fmt.Errorf("GOOS/GOARCH not recorded")
	}

	h := sha256.New()
	scope := "full"
	if !lean {
		scope = "go-only"
	}
	fmt.Fprintf(h, "%s\nscope %s\nschema %d\ngo %s\npath %s\nmain %s\n", verifierIDVersion, scope, resultCacheSchema, bi.GoVersion, bi.Path, bi.Main.Path)
	keys := make([]string, 0, len(settings))
	for k := range settings {
		if k == "vcs" || strings.HasPrefix(k, "vcs.") {
			continue // revision and time differ between identical sources; modified was checked
		}
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		hashPut(h, "setting "+k, []byte(settings[k]))
	}

	// The embedded sources.
	if b.Sources == nil {
		return "", fmt.Errorf("no embedded sources")
	}
	for _, m := range sourceMarkers {
		if fi, err := fs.Stat(b.Sources, m); err != nil || !fi.Mode().IsRegular() {
			return "", fmt.Errorf("embedded sources lack %s", m)
		}
	}
	gomod, _ := fs.ReadFile(b.Sources, "go.mod")
	gosum, _ := fs.ReadFile(b.Sources, "go.sum")
	if mod := goModModule(gomod); mod != bi.Main.Path {
		return "", fmt.Errorf("embedded go.mod declares module %q, the build's main module is %q", mod, bi.Main.Path)
	}
	sums := map[string]bool{}
	for _, l := range strings.Split(string(gosum), "\n") {
		if f := strings.Fields(l); len(f) == 3 {
			sums[f[0]+" "+f[1]+" "+f[2]] = true
		}
	}
	for _, d := range bi.Deps {
		m := d
		if d.Replace != nil {
			m = d.Replace
		}
		if m.Sum == "" || m.Version == "" || strings.HasPrefix(m.Path, ".") || strings.HasPrefix(m.Path, "/") {
			return "", fmt.Errorf("dependency %s has no content hash (replaced by a local path, vendored or in a workspace)", d.Path)
		}
		if !sums[m.Path+" "+m.Version+" "+m.Sum] {
			return "", fmt.Errorf("dependency %s %s %s is not in the embedded go.sum", m.Path, m.Version, m.Sum)
		}
		fmt.Fprintf(h, "dep %s %s %s => %s %s %s\n", d.Path, d.Version, d.Sum, m.Path, m.Version, m.Sum)
	}
	if _, err := hashTree(h, "src", b.Sources, identityGoFile); err != nil {
		return "", err
	}
	if !lean {
		return hex.EncodeToString(h.Sum(nil)), nil
	}
	if n, err := hashTree(h, "framework", b.Framework, nil); err != nil || n == 0 {
		return "", fmt.Errorf("embedded Lean framework unreadable or empty (%v)", err)
	}
	if n, err := hashTree(h, "asl", b.ASL, nil); err != nil || n == 0 {
		return "", fmt.Errorf("embedded JanusASL unreadable or empty (%v)", err)
	}
	return hex.EncodeToString(h.Sum(nil)), nil
}

func goModModule(gomod []byte) string {
	for _, l := range bytes.Split(gomod, []byte("\n")) {
		f := strings.Fields(string(l))
		if len(f) == 2 && f[0] == "module" {
			return strings.Trim(f[1], `"`)
		}
	}
	return ""
}

// verifierComponentFor is the key component for build b: "src:<identity>", or "exe:<sha>" of the
// executable's bytes when the identity cannot be established, or "" when neither can (no cache).
// why is the reason for a fallback.
func verifierComponentFor(b buildSnapshot, exeSha func() string) (comp, why string) {
	return verifierComponentScope(b, exeSha, true)
}

// verifierComponentScope is verifierComponentFor for the full (lean=true) or the Go-only identity.
// The fallback is the executable's bytes in both cases: they cover the embedded Lean as well, so
// a fallback is never less strict.
func verifierComponentScope(b buildSnapshot, exeSha func() string, lean bool) (comp, why string) {
	if os.Getenv("JANUS_VERIFIER_ID") == "exe" {
		why = "JANUS_VERIFIER_ID=exe"
	} else if id, err := verifierIdentityScope(b, lean); err == nil {
		return "src:" + id, ""
	} else {
		why = err.Error()
	}
	if sha := exeSha(); sha != "" {
		return "exe:" + sha, why
	}
	return "", why
}

var (
	verifierOnce sync.Once
	verifierComp string
	verifierWhy  string
)

// verifierComponent is the (cached) component of the running executable.
func verifierComponent() string {
	verifierOnce.Do(func() { verifierComp, verifierWhy = verifierComponentFor(currentBuild(), executableSha) })
	return verifierComp
}

func resetVerifierCache() { verifierOnce = sync.Once{}; verifierComp, verifierWhy = "", "" }

func init() {
	extraCommands["verifier-id"] = func(args []string, stdout, stderr io.Writer) error {
		c := verifierComponent()
		if c == "" {
			c = "none"
		}
		fmt.Fprintln(stdout, c)
		if verifierWhy != "" {
			fmt.Fprintf(stderr, "janus: source identity unavailable (%s); the result cache keys on the executable's bytes\n", verifierWhy)
		}
		return nil
	}
}
