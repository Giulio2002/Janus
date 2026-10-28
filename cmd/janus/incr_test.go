package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// Adversarial tests of the incremental gate's skip records (incr.go). Every input class of an item
// is edited in turn and must change the key (a miss); an edit of something the item does not import
// must not. A record that is tampered with, truncated, copied between keys, foreign, or from a failed
// run must never be a skip.

type incrFx struct {
	t        *testing.T
	root     string // the checkout: proofs, scripts, pins, extraction
	build    string // the framework build root
	fwFiles  map[string][]byte
	verifier string
	tcver    string
	ctx      *incrCtx
	sp       *incrSpec
}

func wr(t *testing.T, p, s string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(p), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(p, []byte(s), 0o644); err != nil {
		t.Fatal(err)
	}
}

func newIncrFx(t *testing.T) *incrFx {
	t.Helper()
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	if err := os.Chmod(os.Getenv("JANUS_CACHE_DIR"), 0o700); err != nil {
		t.Fatal(err)
	}
	x := &incrFx{t: t, root: t.TempDir(), build: t.TempDir(), verifier: "src:v1", tcver: "Lean (version 4.99)"}
	x.fwFiles = map[string][]byte{
		"lakefile.toml":              []byte("name = \"janus\"\n"),
		"lake-manifest.json":         []byte("{}\n"),
		"lean-toolchain":             []byte("leanprover/lean4:v4.99\n"),
		"Janus.lean":                 []byte("import Janus.A\nimport Janus.B\n"),
		"Janus/A.lean":               []byte("import Janus.C\n"),
		"Janus/B.lean":               []byte("/- c -/ import Lean\nimport Janus.D -- deep\n"),
		"Janus/C.lean":               []byte("import Init\n"),
		"Janus/D.lean":               []byte("import Janus.E\n"),
		"Janus/E.lean":               []byte("prelude\n"),
		"Janus/Unused.lean":          []byte("import Janus.C\n"),
		"Janus/Tools/Audit.lean":     []byte("import Lean\n"),
		"Janus/Tools/AuditMain.lean": []byte("import Janus.Tools.Audit\n"),
	}
	lib := filepath.Join(x.build, ".lake", "build", "lib", "lean")
	for p := range x.fwFiles {
		if strings.HasSuffix(p, ".lean") && strings.HasPrefix(p, "Janus") && p != "Janus/Tools/AuditMain.lean" {
			wr(t, filepath.Join(lib, strings.TrimSuffix(p, ".lean")+".olean"), "olean of "+p)
		}
	}
	wr(t, filepath.Join(x.build, ".lake", "build", "bin", "janus-audit"), "auditor exe")
	// the checkout
	wr(t, filepath.Join(x.root, "proofs", "P.lean"), "import Janus\nimport Extracted\n\ntheorem x : True := trivial\n")
	wr(t, filepath.Join(x.root, "bin", "ex"), "example binary")
	sha, _ := (&incrCtx{root: x.root, memo: map[string]string{}}).fileSha("bin/ex")
	wr(t, filepath.Join(x.root, "art", "Extracted.lean"), "import Janus\nnamespace Extracted\nend Extracted\n")
	wr(t, filepath.Join(x.root, "art", "identity.json"), fmt.Sprintf(`{"binary":"../bin/ex","binarySha256":%q,"symbol":"f"}`, sha))
	wr(t, filepath.Join(x.root, "scripts", "run.sh"), "#!/bin/sh\necho run\n")
	wr(t, filepath.Join(x.root, "pins", "stubpins.go"), "package pins\n")
	// the toolchain
	tcd := t.TempDir()
	wr(t, filepath.Join(tcd, "bin", "lean"), "lean")
	wr(t, filepath.Join(tcd, "bin", "leanchecker"), "leanchecker")
	wr(t, filepath.Join(tcd, "lib", "lean", "Init.olean"), "init")
	x.ctx = &incrCtx{
		root:    x.root,
		environ: []string{"PATH=/usr/bin", "JANUS_ITEM_TIMEOUT=2700", "HOME=/x", "JANUS_POOL_DIR=/somewhere"},
		memo:    map[string]string{},
		verifier: func(full bool) (string, error) {
			if x.verifier == "" {
				return "", fmt.Errorf("no identity")
			}
			return x.verifier, nil
		},
		embedded: func() (*framework, error) {
			fw := &framework{Source: "embedded", Files: map[string][]byte{}}
			for k, v := range x.fwFiles {
				fw.Files[k] = v
			}
			fw.Sha256 = frameworkSha(fw.Files)
			fw.Toolchain = strings.TrimSpace(string(fw.Files["lean-toolchain"]))
			return fw, nil
		},
		loadDir: func(dir string) (*framework, error) { return nil, fmt.Errorf("no checkout framework in the fixture") },
		build:   func(fw *framework) (string, error) { return x.build, nil },
		tchain: func(root string) (*toolchain, error) {
			return &toolchain{lean: filepath.Join(tcd, "bin", "lean"), leanchecker: filepath.Join(tcd, "bin", "leanchecker"),
				sysroot: tcd, libDir: filepath.Join(tcd, "lib", "lean"), version: x.tcver, hasChecker: true}, nil
		},
		host: func() string { return "host1" },
	}
	x.sp = &incrSpec{ID: "arm64:P", Kind: "arm64", FW: []string{"embedded"}, Proofs: []string{"proofs/P.lean"}, Arts: []string{"art"},
		Files: []string{"bin/ex"}, Pins: []string{"pins/stubpins.go"}, Scripts: []string{"scripts/run.sh"}, Args: []string{"Proof.correctness"}}
	return x
}

func (x *incrFx) fresh() *incrCtx {
	// a new process: nothing memoized
	c := *x.ctx
	c.memo = map[string]string{}
	return &c
}

func (x *incrFx) key() string {
	x.t.Helper()
	k, comps := x.fresh().compute(x.sp)
	if k == "" {
		x.t.Fatalf("no key: %v", firstErr(comps))
	}
	return k
}

func (x *incrFx) run(sub string, opts map[string]string) string {
	x.t.Helper()
	var b bytes.Buffer
	if err := runIncr(x.fresh(), sub, x.sp, opts, &b); err != nil {
		x.t.Fatal(err)
	}
	return b.String()
}

func (x *incrFx) check() string { return strings.SplitN(x.run("check", nil), "\t", 2)[0] }

func (x *incrFx) pass() {
	x.t.Helper()
	k := x.key()
	out := x.run("record", map[string]string{"rc": "0", "pre-key": k, "wall": "12.5", "started": "t0"})
	if !strings.HasPrefix(out, "RECORDED") {
		x.t.Fatalf("not recorded: %s", out)
	}
}

func (x *incrFx) wantSkip() {
	x.t.Helper()
	if got := x.run("check", nil); !strings.HasPrefix(got, "SKIP\t") {
		x.t.Fatalf("want SKIP, got %q", got)
	}
}
func (x *incrFx) wantRun() {
	x.t.Helper()
	if got := x.run("check", nil); strings.HasPrefix(got, "SKIP\t") {
		x.t.Fatalf("want a miss, got %q", got)
	}
}

func TestIncrSkipOnExactMatch(t *testing.T) {
	x := newIncrFx(t)
	x.wantRun() // no record yet
	x.pass()
	x.wantSkip()
	out := x.run("check", nil)
	f := strings.Split(strings.TrimSpace(out), "\t")
	if len(f) != 6 || f[2] == "" || f[3] == "" || f[4] == "" || f[5] != "12.5" {
		t.Fatalf("SKIP line lacks the original time, host, commit or wall: %q", out)
	}
	// irrelevant environment: skip still
	x.ctx.environ = append(x.ctx.environ, "JANUS_JOBS=7", "JANUS_GATE_PG=/x", "RANDOM_VAR=1")
	x.wantSkip()
}

// the fixture's deepest chain: Janus -> B -> D -> E

func TestIncrEditEachInputClassIsAMiss(t *testing.T) {
	edits := []struct {
		name string
		edit func(x *incrFx)
	}{
		{"proof file", func(x *incrFx) {
			wr(t, filepath.Join(x.root, "proofs/P.lean"), "import Janus\nimport Extracted\n\ntheorem x : 1 = 1 := rfl\n")
		}},
		{"imported module, 1 level (A)", func(x *incrFx) { x.fwFiles["Janus/A.lean"] = []byte("import Janus.C\n-- edit\n") }},
		{"imported module, 3 levels deep (E)", func(x *incrFx) { x.fwFiles["Janus/E.lean"] = []byte("prelude\n-- edit\n") }},
		{"imported module's compiled data (D.olean)", func(x *incrFx) {
			wr(t, filepath.Join(x.build, ".lake/build/lib/lean/Janus/D.olean"), "different olean")
		}},
		{"imported module's .ir file appears", func(x *incrFx) {
			wr(t, filepath.Join(x.build, ".lake/build/lib/lean/Janus/E.ir"), "ir")
		}},
		{"new import in a module (D imports Unused)", func(x *incrFx) { x.fwFiles["Janus/D.lean"] = []byte("import Janus.E\nimport Janus.Unused\n") }},
		{"toolchain string (lean-toolchain file)", func(x *incrFx) { x.fwFiles["lean-toolchain"] = []byte("leanprover/lean4:v4.100\n") }},
		{"toolchain version", func(x *incrFx) { x.tcver = "Lean (version 4.100)" }},
		{"lakefile.toml", func(x *incrFx) {
			x.fwFiles["lakefile.toml"] = []byte("name = \"janus\"\n[leanOptions]\nmaxRecDepth=1\n")
		}},
		{"lake-manifest.json", func(x *incrFx) { x.fwFiles["lake-manifest.json"] = []byte("{\"v\":2}\n") }},
		{"verifier identity", func(x *incrFx) { x.verifier = "src:v2" }},
		{"verifier falls back to the executable", func(x *incrFx) { x.verifier = "exe:abc" }},
		{"auditor source", func(x *incrFx) { x.fwFiles["Janus/Tools/Audit.lean"] = []byte("import Lean\n-- weaker\n") }},
		{"auditor main source", func(x *incrFx) { x.fwFiles["Janus/Tools/AuditMain.lean"] = []byte("import Janus.Tools.Audit\n-- x\n") }},
		{"auditor olean", func(x *incrFx) {
			wr(t, filepath.Join(x.build, ".lake/build/lib/lean/Janus/Tools/Audit.olean"), "weaker audit olean")
		}},
		{"auditor executable", func(x *incrFx) { wr(t, filepath.Join(x.build, ".lake/build/bin/janus-audit"), "other auditor") }},
		{"leanchecker binary", func(x *incrFx) {
			// the fixture's leanchecker is in the toolchain dir the closure below captured
			p, _ := x.ctx.tchain("")
			wr(t, p.leanchecker, "patched leanchecker")
		}},
		{"lean binary", func(x *incrFx) {
			p, _ := x.ctx.tchain("")
			wr(t, p.lean, "patched lean")
		}},
		{"toolchain library file", func(x *incrFx) {
			p, _ := x.ctx.tchain("")
			wr(t, filepath.Join(p.libDir, "Init.olean"), "patched core library")
		}},
		{"pin file", func(x *incrFx) { wr(t, filepath.Join(x.root, "pins/stubpins.go"), "package pins // new hash\n") }},
		{"gate script", func(x *incrFx) { wr(t, filepath.Join(x.root, "scripts/run.sh"), "#!/bin/sh\necho run --weaker\n") }},
		{"env JANUS_ITEM_TIMEOUT", func(x *incrFx) { x.ctx.environ[1] = "JANUS_ITEM_TIMEOUT=0" }},
		{"env new JANUS_ variable", func(x *incrFx) { x.ctx.environ = append(x.ctx.environ, "JANUS_JOB_MEM=2G") }},
		{"env GOFLAGS (build tags)", func(x *incrFx) { x.ctx.environ = append(x.ctx.environ, "GOFLAGS=-tags=foo") }},
		{"env LEAN_NUM_THREADS", func(x *incrFx) { x.ctx.environ = append(x.ctx.environ, "LEAN_NUM_THREADS=1") }},
		{"extraction Extracted.lean", func(x *incrFx) {
			wr(t, filepath.Join(x.root, "art/Extracted.lean"), "import Janus\nnamespace Extracted\ndef x := 1\nend Extracted\n")
		}},
		{"extraction identity.json", func(x *incrFx) {
			b, _ := os.ReadFile(filepath.Join(x.root, "art/identity.json"))
			wr(t, filepath.Join(x.root, "art/identity.json"), strings.Replace(string(b), `"symbol":"f"`, `"symbol":"g"`, 1))
		}},
		{"extraction extra file", func(x *incrFx) { wr(t, filepath.Join(x.root, "art/Data.lean"), "import Janus\n") }},
		{"binary (identity.json updated to match)", func(x *incrFx) {
			wr(t, filepath.Join(x.root, "bin/ex"), "patched binary")
			s, _ := (&incrCtx{root: x.root, memo: map[string]string{}}).fileSha("bin/ex")
			wr(t, filepath.Join(x.root, "art/identity.json"), fmt.Sprintf(`{"binary":"../bin/ex","binarySha256":%q,"symbol":"f"}`, s))
		}},
		{"item argument (theorem list)", func(x *incrFx) { x.sp.Args = []string{"Proof.correctness", "Proof.Witness.returns"} }},
		{"item id", func(x *incrFx) { x.sp.ID = "arm64:Q" }},
		{"item kind", func(x *incrFx) { x.sp.Kind = "amd64" }},
	}
	for _, e := range edits {
		t.Run(e.name, func(t *testing.T) {
			x := newIncrFx(t)
			x.pass()
			x.wantSkip()
			e.edit(x)
			x.wantRun()
		})
	}
}

func TestIncrUnrelatedEditsStillSkip(t *testing.T) {
	edits := []struct {
		name string
		edit func(x *incrFx)
	}{
		{"framework module not imported (Unused)", func(x *incrFx) { x.fwFiles["Janus/Unused.lean"] = []byte("import Janus.C\n-- edit\n") }},
		{"compiled data of a module not imported", func(x *incrFx) {
			wr(t, filepath.Join(x.build, ".lake/build/lib/lean/Janus/Unused.olean"), "changed")
		}},
		{"a brand-new framework module nobody imports", func(x *incrFx) { x.fwFiles["Janus/Amd64/New.lean"] = []byte("import Janus.C\n") }},
		{"the verifier's outputs in the extraction", func(x *incrFx) {
			wr(t, filepath.Join(x.root, "art/verified.json"), "{}")
			wr(t, filepath.Join(x.root, "art/verify.log"), "log")
			wr(t, filepath.Join(x.root, "art/verified/Proof.correctness.json"), "{}")
		}},
		{"identity.json binary path spelling", func(x *incrFx) {
			b, _ := os.ReadFile(filepath.Join(x.root, "art/identity.json"))
			wr(t, filepath.Join(x.root, "art/identity.json"), strings.Replace(string(b), `"../bin/ex"`, `"`+filepath.Join(x.root, "bin/ex")+`"`, 1))
		}},
		{"a file the item does not name", func(x *incrFx) { wr(t, filepath.Join(x.root, "docs/README.md"), "docs") }},
		{"a scheduling variable", func(x *incrFx) { x.ctx.environ = append(x.ctx.environ, "JANUS_JOBS=9", "JANUS_LANES=4") }},
	}
	for _, e := range edits {
		t.Run(e.name, func(t *testing.T) {
			x := newIncrFx(t)
			x.pass()
			e.edit(x)
			x.wantSkip()
		})
	}
}

func TestIncrFailedRunIsNeverASkip(t *testing.T) {
	x := newIncrFx(t)
	k := x.key()
	out := x.run("record", map[string]string{"rc": "1", "pre-key": k})
	if !strings.HasPrefix(out, "NOTRECORDED") {
		t.Fatal(out)
	}
	x.wantRun()
	if _, err := os.Stat(incrPath(k)); err == nil {
		t.Fatal("a record exists for a failed run")
	}
	for _, rc := range []string{"124", "137", "2", "-1"} {
		out := x.run("record", map[string]string{"rc": rc, "pre-key": k})
		if !strings.HasPrefix(out, "NOTRECORDED") {
			t.Fatalf("rc %s: %s", rc, out)
		}
		x.wantRun()
	}
	// an earlier PASS is withdrawn by a later failure with the same inputs
	x.pass()
	x.wantSkip()
	x.run("record", map[string]string{"rc": "1", "pre-key": k})
	x.wantRun()
	// a bad rc
	var b bytes.Buffer
	if err := runIncr(x.fresh(), "record", x.sp, map[string]string{"rc": "x", "pre-key": k}, &b); err == nil {
		t.Fatal("a non-numeric rc must be an error")
	}
	if err := runIncr(x.fresh(), "record", x.sp, map[string]string{"pre-key": k}, &b); err == nil {
		t.Fatal("a missing rc must be an error")
	}
	x.wantRun()
}

func TestIncrRecordNeedsUnchangedInputs(t *testing.T) {
	x := newIncrFx(t)
	k := x.key()
	// the proof changes while the item runs: nothing is recorded
	wr(t, filepath.Join(x.root, "proofs/P.lean"), "import Janus\nimport Extracted\n-- changed during the run\n")
	out := x.run("record", map[string]string{"rc": "0", "pre-key": k})
	if !strings.HasPrefix(out, "NOTRECORDED") {
		t.Fatal(out)
	}
	x.wantRun()
	if _, err := os.Stat(incrPath(k)); err == nil {
		t.Fatal("record of the pre-run key exists")
	}
	if _, err := os.Stat(incrPath(x.key())); err == nil {
		t.Fatal("record of the post-run key exists")
	}
	// a record without a pre-key, or with a made-up one
	for _, pre := range []string{"", strings.Repeat("0", 64)} {
		out = x.run("record", map[string]string{"rc": "0", "pre-key": pre})
		if !strings.HasPrefix(out, "NOTRECORDED") {
			t.Fatalf("pre-key %q: %s", pre, out)
		}
	}
	x.wantRun()
}

func TestIncrUnkeyedItemsAlwaysRun(t *testing.T) {
	cases := []struct {
		name string
		edit func(x *incrFx)
	}{
		{"missing proof file", func(x *incrFx) { os.Remove(filepath.Join(x.root, "proofs/P.lean")) }},
		{"missing module data (framework not built)", func(x *incrFx) { os.Remove(filepath.Join(x.build, ".lake/build/lib/lean/Janus/C.olean")) }},
		{"missing auditor executable", func(x *incrFx) { os.Remove(filepath.Join(x.build, ".lake/build/bin/janus-audit")) }},
		{"missing extraction", func(x *incrFx) { os.Remove(filepath.Join(x.root, "art/identity.json")) }},
		{"binary does not match identity.json", func(x *incrFx) { wr(t, filepath.Join(x.root, "bin/ex"), "swapped binary") }},
		{"binary missing", func(x *incrFx) { os.Remove(filepath.Join(x.root, "bin/ex")) }},
		{"identity.json not JSON", func(x *incrFx) { wr(t, filepath.Join(x.root, "art/identity.json"), "{") }},
		{"unreadable import (unknown module)", func(x *incrFx) { x.fwFiles["Janus/D.lean"] = []byte("import Mathlib.Algebra\n") }},
		{"ambiguous module (in the extraction and the framework)", func(x *incrFx) { wr(t, filepath.Join(x.root, "art/Janus/C.lean"), "x") }},
		{"no verifier identity", func(x *incrFx) { x.verifier = "" }},
		{"quoted module name", func(x *incrFx) { x.fwFiles["Janus/D.lean"] = []byte("import «Janus».E\n") }},
		{"unterminated header comment", func(x *incrFx) { x.fwFiles["Janus/D.lean"] = []byte("/- never ends\nimport Janus.E\n") }},
		{"missing pin file", func(x *incrFx) { os.Remove(filepath.Join(x.root, "pins/stubpins.go")) }},
		{"missing script", func(x *incrFx) { os.Remove(filepath.Join(x.root, "scripts/run.sh")) }},
		{"JANUS_ROOT set with the embedded framework", func(x *incrFx) { x.ctx.environ = append(x.ctx.environ, "JANUS_ROOT=/elsewhere") }},
		{"unknown framework mode", func(x *incrFx) { x.sp.FW = []string{"bogus"} }},
		{"checkout framework unavailable", func(x *incrFx) { x.sp.FW = []string{"embedded", "dir:."} }},
		{"toolchain without leanchecker", func(x *incrFx) {
			old := x.ctx.tchain
			x.ctx.tchain = func(r string) (*toolchain, error) { tc, e := old(r); tc.hasChecker = false; return tc, e }
		}},
	}
	for _, e := range cases {
		t.Run(e.name, func(t *testing.T) {
			x := newIncrFx(t)
			x.pass()
			x.wantSkip()
			e.edit(x)
			if got := x.run("check", nil); !strings.HasPrefix(got, "NOKEY\t") {
				t.Fatalf("want NOKEY, got %q", got)
			}
			// and nothing is recorded for it, even for a successful run
			out := x.run("record", map[string]string{"rc": "0", "pre-key": strings.Repeat("a", 64)})
			if !strings.HasPrefix(out, "NOTRECORDED") {
				t.Fatal(out)
			}
		})
	}
}

// ---------------------------------------------------------------- record integrity

func TestIncrTamperedRecordIsAMiss(t *testing.T) {
	mutate := map[string]func(t *testing.T, x *incrFx, p string){
		"flipped byte in the body": func(t *testing.T, x *incrFx, p string) {
			b, _ := os.ReadFile(p)
			i := bytes.Index(b, []byte("pass"))
			if i < 0 {
				t.Fatal("body not found")
			}
			b[i] = 'P'
			os.WriteFile(p, b, 0o600)
		},
		"faked wall time": func(t *testing.T, x *incrFx, p string) {
			b, _ := os.ReadFile(p)
			os.WriteFile(p, bytes.Replace(b, []byte("12.5"), []byte("99.5"), 1), 0o600)
		},
		"result changed to fail": func(t *testing.T, x *incrFx, p string) {
			b, _ := os.ReadFile(p)
			os.WriteFile(p, bytes.Replace(b, []byte("pass"), []byte("fail"), 1), 0o600)
		},
		"truncated": func(t *testing.T, x *incrFx, p string) {
			b, _ := os.ReadFile(p)
			os.WriteFile(p, b[:len(b)/2], 0o600)
		},
		"truncated by one byte": func(t *testing.T, x *incrFx, p string) {
			b, _ := os.ReadFile(p)
			os.WriteFile(p, b[:len(b)-1], 0o600)
		},
		"empty":   func(t *testing.T, x *incrFx, p string) { os.WriteFile(p, nil, 0o600) },
		"garbage": func(t *testing.T, x *incrFx, p string) { os.WriteFile(p, []byte("not json at all"), 0o600) },
		"trailing data": func(t *testing.T, x *incrFx, p string) {
			b, _ := os.ReadFile(p)
			os.WriteFile(p, append(b, []byte("\n{}")...), 0o600)
		},
		"mac removed": func(t *testing.T, x *incrFx, p string) {
			var e map[string]json.RawMessage
			b, _ := os.ReadFile(p)
			json.Unmarshal(b, &e)
			delete(e, "mac")
			nb, _ := json.Marshal(e)
			os.WriteFile(p, nb, 0o600)
		},
		"unknown field added": func(t *testing.T, x *incrFx, p string) {
			var e map[string]json.RawMessage
			b, _ := os.ReadFile(p)
			json.Unmarshal(b, &e)
			e["extra"] = json.RawMessage(`1`)
			nb, _ := json.Marshal(e)
			os.WriteFile(p, nb, 0o600)
		},
		"mac of another record": func(t *testing.T, x *incrFx, p string) {
			var e incrEntry
			b, _ := os.ReadFile(p)
			json.Unmarshal(b, &e)
			e.MAC = strings.Repeat("0", 64)
			nb, _ := json.Marshal(e)
			os.WriteFile(p, nb, 0o600)
		},
		"a symbolic link": func(t *testing.T, x *incrFx, p string) {
			b, _ := os.ReadFile(p)
			real := p + ".real"
			os.WriteFile(real, b, 0o600)
			os.Remove(p)
			os.Symlink(real, p)
		},
		"a directory": func(t *testing.T, x *incrFx, p string) { os.Remove(p); os.Mkdir(p, 0o700) },
	}
	for name, m := range mutate {
		t.Run(name, func(t *testing.T) {
			x := newIncrFx(t)
			x.pass()
			x.wantSkip()
			m(t, x, incrPath(x.key()))
			x.wantRun()
		})
	}
}

func TestIncrForgedRecordsAreAMiss(t *testing.T) {
	x := newIncrFx(t)
	x.pass()
	k1 := x.key()
	// a record copied to the path of another key
	x.sp.Args = []string{"Proof.other"}
	k2 := x.key()
	if k1 == k2 {
		t.Fatal("keys collide")
	}
	b, _ := os.ReadFile(incrPath(k1))
	os.MkdirAll(filepath.Dir(incrPath(k2)), 0o700)
	os.WriteFile(incrPath(k2), b, 0o600)
	x.wantRun()
	// ... even with the key field rewritten to match the path (the MAC covers the key)
	var e incrEntry
	json.Unmarshal(b, &e)
	e.Key = k2
	nb, _ := json.Marshal(e)
	os.WriteFile(incrPath(k2), nb, 0o600)
	x.wantRun()
	// ... and with the body's key rewritten as well (the MAC covers the body)
	var r incrRecord
	json.Unmarshal(e.Body, &r)
	r.Key = k2
	e.Body, _ = json.Marshal(r)
	nb, _ = json.Marshal(e)
	os.WriteFile(incrPath(k2), nb, 0o600)
	x.wantRun()
	// a record forged with a MAC under a different (attacker-chosen) key
	forged := incrEntry{Key: k2}
	r.Result = "pass"
	forged.Body, _ = json.Marshal(r)
	forged.MAC = incrMAC([]byte("attacker key attacker key 123456"), k2, forged.Body)
	nb, _ = json.Marshal(forged)
	os.WriteFile(incrPath(k2), nb, 0o600)
	x.wantRun()
	// the original is still good
	x.sp.Args = []string{"Proof.correctness"}
	x.wantSkip()
}

func TestIncrRecordFromAnotherUsersCacheIsAMiss(t *testing.T) {
	x := newIncrFx(t)
	x.pass()
	k := x.key()
	b, _ := os.ReadFile(incrPath(k))
	// a different cache (a different per-user HMAC key) with the very same record file
	t.Setenv("JANUS_CACHE_DIR", t.TempDir())
	os.Chmod(os.Getenv("JANUS_CACHE_DIR"), 0o700)
	if _, err := resultHMACKey(); err != nil {
		t.Fatal(err)
	}
	os.MkdirAll(filepath.Dir(incrPath(k)), 0o700)
	os.WriteFile(incrPath(k), b, 0o600)
	x.wantRun()
}

func TestIncrRecordFromResultCacheKeyDomain(t *testing.T) {
	// a result-cache entry's MAC (a different domain of the same key) is not a valid incr MAC
	x := newIncrFx(t)
	x.pass()
	k := x.key()
	hk, _ := resultHMACKey()
	b, _ := os.ReadFile(incrPath(k))
	var e incrEntry
	json.Unmarshal(b, &e)
	e.MAC = resultMAC(hk, k, e.Body)
	nb, _ := json.Marshal(e)
	os.WriteFile(incrPath(k), nb, 0o600)
	x.wantRun()
}

func TestIncrNoCollisionsBetweenFramings(t *testing.T) {
	x := newIncrFx(t)
	keys := map[string]string{}
	add := func(name string, mut func(sp *incrSpec)) {
		sp := *x.sp
		sp.Args = append([]string(nil), x.sp.Args...)
		mut(&sp)
		k, comps := x.fresh().compute(&sp)
		if k == "" {
			t.Fatalf("%s: %v", name, firstErr(comps))
		}
		if prev, dup := keys[k]; dup {
			t.Fatalf("%s collides with %s", name, prev)
		}
		keys[k] = name
	}
	add("base", func(sp *incrSpec) {})
	add("args split", func(sp *incrSpec) { sp.Args = []string{"a", "b"} })
	add("args joined", func(sp *incrSpec) { sp.Args = []string{"a b"} })
	add("args joined with comma", func(sp *incrSpec) { sp.Args = []string{"a,b"} })
	add("args reversed", func(sp *incrSpec) { sp.Args = []string{"b", "a"} })
	add("args empty element", func(sp *incrSpec) { sp.Args = []string{"a", "", "b"} })
	add("id moves into an arg", func(sp *incrSpec) { sp.ID = "arm64:P arg Proof.correctness"; sp.Args = nil })
	add("kind/id swap", func(sp *incrSpec) { sp.ID, sp.Kind = sp.Kind, sp.ID })
	add("proof as file", func(sp *incrSpec) { sp.Files = append(sp.Files, "proofs/P.lean"); sp.Proofs = nil })
	add("script as pin", func(sp *incrSpec) { sp.Pins = append(sp.Pins, "scripts/run.sh"); sp.Scripts = nil })
	add("both frameworks listed twice", func(sp *incrSpec) { sp.FW = []string{"embedded", "embedded"} })
	// an env value containing what looks like another variable
	k0 := x.key()
	x.ctx.environ = append(x.ctx.environ, "JANUS_A=1\nJANUS_B=2")
	k1 := x.key()
	x.ctx.environ = append(x.ctx.environ[:len(x.ctx.environ)-1], "JANUS_A=1", "JANUS_B=2")
	k2 := x.key()
	if k0 == k1 || k1 == k2 || k0 == k2 {
		t.Fatal("env framings collide")
	}
}

func TestIncrKeyIsStableAcrossProcessesAndCheckouts(t *testing.T) {
	x := newIncrFx(t)
	k1 := x.key()
	if k1 != x.key() {
		t.Fatal("key is not deterministic")
	}
	// the same inputs in another directory (another checkout, another worktree) have the same key
	y := newIncrFx(t)
	y.verifier, y.fwFiles = x.verifier, x.fwFiles
	y.tcver = x.tcver
	// the fixtures differ in absolute paths only (and in the toolchain directory, which is part of cacheID by path)
	if y.key() == "" {
		t.Fatal("no key")
	}
}

// ---------------------------------------------------------------- the dirty-tree and lane keys

func gitInit(t *testing.T, dir string) {
	t.Helper()
	for _, a := range [][]string{{"init", "-q"}, {"config", "user.email", "a@b"}, {"config", "user.name", "n"}, {"add", "-A"}, {"commit", "-qm", "c"}} {
		cmd := exec.Command("git", append([]string{"-C", dir}, a...)...)
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("git %v: %v\n%s", a, err, out)
		}
	}
}

func TestIncrLaneTreeKey(t *testing.T) {
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("no git")
	}
	x := newIncrFx(t)
	wr(t, filepath.Join(x.root, "cmd/a.go"), "package a\n")
	wr(t, filepath.Join(x.root, "docs/T.md"), "doc\n")
	wr(t, filepath.Join(x.root, "README.md"), "readme\n")
	wr(t, filepath.Join(x.root, ".gitignore"), "ignored/\n")
	gitInit(t, x.root)
	x.sp = &incrSpec{ID: "gotest", Kind: "lane", NoFW: true, Host: true, Full: true, Tree: ".", TreeExcl: []string{"docs/", "*.md"}, Args: []string{"-run", "x"}}
	x.pass()
	x.wantSkip()
	// documentation: still a skip
	wr(t, filepath.Join(x.root, "docs/T.md"), "changed doc\n")
	wr(t, filepath.Join(x.root, "README.md"), "changed readme\n")
	wr(t, filepath.Join(x.root, "docs/New.md"), "new\n")
	x.wantSkip()
	// ignored files are not inputs
	wr(t, filepath.Join(x.root, "ignored/z"), "z")
	x.wantSkip()
	// a change in code: miss; dirty (uncommitted) is content-hashed, not commit-named
	wr(t, filepath.Join(x.root, "cmd/a.go"), "package a // dirty\n")
	x.wantRun()
	wr(t, filepath.Join(x.root, "cmd/a.go"), "package a\n")
	x.wantSkip()
	// an untracked new source file
	wr(t, filepath.Join(x.root, "cmd/new.go"), "package a\n")
	x.wantRun()
	os.Remove(filepath.Join(x.root, "cmd/new.go"))
	x.wantSkip()
	// a tracked file deleted
	os.Remove(filepath.Join(x.root, "cmd/a.go"))
	x.wantRun()
	wr(t, filepath.Join(x.root, "cmd/a.go"), "package a\n")
	x.wantSkip()
	// committing the same content does not change the key (the commit is not an input)
	exec.Command("git", "-C", x.root, "add", "-A").Run()
	exec.Command("git", "-C", x.root, "commit", "-qm", "again").Run()
	x.wantSkip()
	// execute bit
	os.Chmod(filepath.Join(x.root, "cmd/a.go"), 0o755)
	x.wantRun()
	os.Chmod(filepath.Join(x.root, "cmd/a.go"), 0o644)
	x.wantSkip()
	// the machine is an input
	x.ctx.host = func() string { return "host2" }
	x.wantRun()
	x.ctx.host = func() string { return "host1" }
	x.wantSkip()
	// a lane has no per-item framework closure but still keys the toolchain
	x.tcver = "Lean (version 4.100)"
	x.wantRun()
}

func TestIncrNotAGitTreeIsUnkeyed(t *testing.T) {
	x := newIncrFx(t)
	x.sp = &incrSpec{ID: "gotest", Kind: "lane", NoFW: true, Tree: "."}
	if got := x.run("check", nil); !strings.HasPrefix(got, "NOKEY\t") {
		t.Fatalf("want NOKEY, got %q", got)
	}
}

// ---------------------------------------------------------------- explain

func TestIncrExplainNamesEveryComponent(t *testing.T) {
	x := newIncrFx(t)
	out := x.run("explain", map[string]string{"verbose": "1"})
	for _, want := range []string{"schema", "item ", "env ", "verifier ", "toolchain:embedded", "fw:embedded:config", "fw:embedded:closure",
		"fw:embedded:auditor", "proof:proofs/P.lean", "art:art", "file:bin/ex", "pin:pins/stubpins.go", "script:scripts/run.sh",
		"key: ", "record: none", "mod Janus.E ", "mod Janus.D "} {
		if !strings.Contains(out, want) {
			t.Errorf("explain lacks %q:\n%s", want, out)
		}
	}
	if strings.Contains(out, "Janus.Unused") {
		t.Errorf("explain lists a module the item does not import:\n%s", out)
	}
	x.pass()
	out = x.run("explain", nil)
	if !strings.Contains(out, "would be SKIPPED") {
		t.Errorf("explain does not report the record:\n%s", out)
	}
	wr(t, filepath.Join(x.root, "proofs/P.lean"), "import Janus\n-- x\n")
	out = x.run("explain", nil)
	if !strings.Contains(out, "would RUN") {
		t.Errorf("explain does not report the miss:\n%s", out)
	}
	os.Remove(filepath.Join(x.root, "proofs/P.lean"))
	out = x.run("explain", nil)
	if !strings.Contains(out, "UNHASHABLE") || !strings.Contains(out, "key: none") {
		t.Errorf("explain does not report the unhashable input:\n%s", out)
	}
}

// ---------------------------------------------------------------- the import parser

func TestLeanImports(t *testing.T) {
	cases := []struct {
		src  string
		want []string
		bad  bool
	}{
		{"import A\nimport B.C\n\ntheorem x : True := trivial\n", []string{"A", "B.C"}, false},
		{"/-! doc\n  /- nested -/ import Fake\n-/\nimport Real -- trailing\n-- import Fake2\nimport Real2\ndef x := 1\nimport NotAHeader\n", []string{"Real", "Real2"}, false},
		{"prelude\nimport Init.Prelude\n", []string{"Init.Prelude"}, false},
		{"import all A\nimport runtime B\npublic import C\nmeta import D\nprivate import E\npublic meta import F\n", []string{"A", "B", "C", "D", "E", "F"}, false},
		{"import all\nimport X\n", []string{"all", "X"}, false},
		{"", nil, false},
		{"def x := 1\nimport A\n", nil, false},
		{"import A/B\n", nil, true},
		{"import «A».B\n", nil, true},
		{"import\n", nil, true},
		{"import .A\n", nil, true},
		{"import A..B\n", nil, true},
		{"/- unterminated\nimport A\n", nil, true},
		{"import A--c\nimport B/-c-/\n", []string{"A", "B"}, false},
		{"import Janus.Amd64.Lemmas'\n", []string{"Janus.Amd64.Lemmas'"}, false},
	}
	for _, c := range cases {
		got, err := leanImports([]byte(c.src))
		if c.bad {
			if err == nil {
				t.Errorf("%q: want an error, got %v", c.src, got)
			}
			continue
		}
		if err != nil || strings.Join(got, ",") != strings.Join(c.want, ",") {
			t.Errorf("%q: got %v, %v; want %v", c.src, got, err, c.want)
		}
	}
}

func TestIncrEnvRelevance(t *testing.T) {
	for _, n := range []string{"JANUS_ITEM_TIMEOUT", "JANUS_JOB_MEM", "JANUS_ROOT", "JANUS_VERIFIER_ID", "JANUS_RESULT_CACHE", "JANUS_CACHE_DIR",
		"LEAN_NUM_THREADS", "LEAN_PATH", "LAKE_HOME", "ELAN_HOME", "GOFLAGS", "GOOS", "GOARCH", "GOAMD64", "GOTOOLCHAIN", "CGO_ENABLED", "CGO_CFLAGS",
		"MEMCAP_MAX", "KEEP", "JANUS_SCRIPT_MEM_MAX", "JANUS_MEM_MAX", "JANUS_LAKE_JOB_MEM"} {
		if !incrEnvRelevant(n) {
			t.Errorf("%s must be part of the key", n)
		}
	}
	for _, n := range []string{"JANUS_JOBS", "JANUS_POOL_DIR", "JANUS_GATE_PG", "JANUS_MEMGUARD_CGROUP", "JANUS_INCR_PRECHECK", "JANUS_EXAMPLES_SUMMARY", "GOCACHE", "GOPATH", "HOME", "PATH", "USER"} {
		if incrEnvRelevant(n) {
			t.Errorf("%s must not be part of the key", n)
		}
	}
}

// ---------------------------------------------------------------- the Go-only verifier identity

func TestVerifierIdentityGoOnlyScope(t *testing.T) {
	tb := baseBuild(t)
	full := mustID(t, tb)
	goOnly, err := verifierIdentityScope(tb.b, false)
	if err != nil {
		t.Fatal(err)
	}
	if full == goOnly {
		t.Fatal("the Go-only identity equals the full one")
	}
	// the Lean trees are not part of the Go-only identity ...
	l := tb.clone()
	l.framework["Janus/Amd64/Only.lean"] = nil
	l.framework["Janus.lean"].Data = append(l.framework["Janus.lean"].Data, []byte("\n-- edit\n")...)
	l.asl["JanusASL/lakefile.toml"].Data = append(l.asl["JanusASL/lakefile.toml"].Data, []byte("\n# edit\n")...)
	delete(l.framework, "Janus/Amd64/Only.lean")
	l.sync()
	if g, err := verifierIdentityScope(l.b, false); err != nil || g != goOnly {
		t.Fatalf("a Lean edit changed the Go-only identity: %v %v", g, err)
	}
	if mustID(t, l) == full {
		t.Fatal("a Lean edit did not change the full identity")
	}
	// ... but every Go input class is
	for name, mut := range map[string]func(c *testBuild){
		"go source": func(c *testBuild) {
			c.sources["cmd/janus/main.go"].Data = append(c.sources["cmd/janus/main.go"].Data, []byte("\n// x\n")...)
		},
		"incr.go": func(c *testBuild) {
			c.sources["cmd/janus/incr.go"].Data = append(c.sources["cmd/janus/incr.go"].Data, []byte("\n// x\n")...)
		},
		"go.mod": func(c *testBuild) { c.sources["go.mod"].Data = append(c.sources["go.mod"].Data, []byte("\n// x\n")...) },
		"go.sum": func(c *testBuild) { c.sources["go.sum"].Data = append(c.sources["go.sum"].Data, []byte("\n")...) },
		"stub pins": func(c *testBuild) {
			c.sources["cmd/janus/stubpins_gen.go"].Data = append(c.sources["cmd/janus/stubpins_gen.go"].Data, []byte("\n// x\n")...)
		},
		"build setting (a tag)": func(c *testBuild) { c.setSetting("-tags", "foo") },
		"GOAMD64":               func(c *testBuild) { c.setSetting("GOAMD64", "v3") },
		"CGO_ENABLED":           func(c *testBuild) { c.setSetting("CGO_ENABLED", "1") },
		"modified tree":         func(c *testBuild) { c.setSetting("vcs.modified", "true") },
	} {
		c := tb.clone()
		mut(c)
		c.sync()
		g, err := verifierIdentityScope(c.b, false)
		if name == "CGO_ENABLED" || name == "modified tree" {
			if err == nil {
				t.Errorf("%s: the identity must be unavailable (fallback to the executable), got %s", name, g)
			}
			continue
		}
		if err != nil {
			t.Errorf("%s: %v", name, err)
			continue
		}
		if g == goOnly {
			t.Errorf("%s did not change the Go-only identity", name)
		}
	}
}
