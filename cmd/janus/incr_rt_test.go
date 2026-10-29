package main

// Red-team tests of the incremental gate's skip records and of the result-cache verifier identity
// (package RT). Every test performs an attack and asserts a MISS (the item runs) or a REJECT; the
// numbering follows the RT brief:
//
//	 1 stale entries              TestRT01Stale*
//	 2 deep / auditor-only edits  TestRT02*
//	 3 toolchain, checker, auditor TestRT03*
//	 4 script, lib and env swaps  TestRT04* (and scripts/lib/test-rt-incr.sh)
//	 5 key-design collisions      TestRT05*
//	 6 cache-file tampering       TestRT06*
//	 7 dependency / build inputs  TestRT07* (verifierid_rt_test.go)
//	 8 dirty tree                 TestRT08* (verifierid_rt_test.go)
//	 9 a proof poisoning caches   TestRT09* (incr_rt_sandbox_test.go)
//	10 races                      TestRT10*
//	11 --fresh verdict store      (verdictstore_rt_test.go, branch agent/speed-j1)
//	12 failed / timed-out runs    TestRT12* and scripts/lib/test-rt-incr.sh

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"
)

// restoreTimes puts back the modification time of p (what `touch -r`, `cp -p` and `tar` do).
func restoreTimes(t *testing.T, p string, fi os.FileInfo) {
	t.Helper()
	if err := os.Chtimes(p, fi.ModTime(), fi.ModTime()); err != nil {
		t.Fatal(err)
	}
}

// editKeepingSizeAndTime rewrites p with b (same length as the old content required) and restores
// the modification time: only the content (and the change time) differs.
func editKeepingSizeAndTime(t *testing.T, p string, b []byte) {
	t.Helper()
	fi, err := os.Stat(p)
	if err != nil {
		t.Fatal(err)
	}
	if int64(len(b)) != fi.Size() {
		t.Fatalf("%s: edit changes the size (%d -> %d)", p, fi.Size(), len(b))
	}
	if err := os.WriteFile(p, b, fi.Mode().Perm()); err != nil {
		t.Fatal(err)
	}
	restoreTimes(t, p, fi)
}

// ---------------------------------------------------------------- 1 stale entries

func TestRT01StaleEditsAfterPass(t *testing.T) {
	cases := []struct {
		name string
		edit func(t *testing.T, x *incrFx)
		want string // "RUN" or "NOKEY"
	}{
		{"proof, same size, mtime restored", func(t *testing.T, x *incrFx) {
			p := filepath.Join(x.root, "proofs/P.lean")
			b, _ := os.ReadFile(p)
			editKeepingSizeAndTime(t, p, bytes.Replace(b, []byte("trivial"), []byte("trivi4l"), 1))
		}, "RUN"},
		{"Extracted.lean, same size, mtime restored", func(t *testing.T, x *incrFx) {
			p := filepath.Join(x.root, "art/Extracted.lean")
			b, _ := os.ReadFile(p)
			editKeepingSizeAndTime(t, p, bytes.Replace(b, []byte("namespace"), []byte("nxmespace"), 1))
		}, "RUN"},
		{"binary swapped, identity.json untouched", func(t *testing.T, x *incrFx) {
			p := filepath.Join(x.root, "bin/ex")
			b, _ := os.ReadFile(p)
			editKeepingSizeAndTime(t, p, bytes.Replace(b, []byte("example"), []byte("exxmple"), 1))
		}, "NOKEY"},
		{"binary swapped and identity.json rewritten to match", func(t *testing.T, x *incrFx) {
			wr(t, filepath.Join(x.root, "bin/ex"), "evil binary, different bytes")
			s, _ := (&incrCtx{root: x.root, memo: map[string]string{}}).fileSha("bin/ex")
			wr(t, filepath.Join(x.root, "art/identity.json"), fmt.Sprintf(`{"binary":"../bin/ex","binarySha256":%q,"symbol":"f"}`, s))
		}, "RUN"},
		{"binary swapped by a symlink to a different file", func(t *testing.T, x *incrFx) {
			other := filepath.Join(x.root, "bin/other")
			wr(t, other, "evil binary, different bytes")
			if err := os.Remove(filepath.Join(x.root, "bin/ex")); err != nil {
				t.Fatal(err)
			}
			if err := os.Symlink(other, filepath.Join(x.root, "bin/ex")); err != nil {
				t.Fatal(err)
			}
		}, "NOKEY"},
		{"identity.json symbol retargeted", func(t *testing.T, x *incrFx) {
			p := filepath.Join(x.root, "art/identity.json")
			b, _ := os.ReadFile(p)
			editKeepingSizeAndTime(t, p, bytes.Replace(b, []byte(`"f"`), []byte(`"g"`), 1))
		}, "RUN"},
		{"a pin edited", func(t *testing.T, x *incrFx) {
			p := filepath.Join(x.root, "pins/stubpins.go")
			b, _ := os.ReadFile(p)
			editKeepingSizeAndTime(t, p, bytes.Replace(b, []byte("pins"), []byte("pinz"), 1))
		}, "RUN"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			x := newIncrFx(t)
			x.pass()
			x.wantSkip()
			c.edit(t, x)
			got := strings.SplitN(x.run("check", nil), "\t", 2)[0]
			if got != c.want {
				t.Fatalf("want %s, got %s", c.want, got)
			}
		})
	}
	// and the edit undone is the original inputs again: a legitimate hit (the key is content-addressed)
	x := newIncrFx(t)
	x.pass()
	p := filepath.Join(x.root, "proofs/P.lean")
	orig, _ := os.ReadFile(p)
	wr(t, p, "import Janus\nimport Extracted\n\ntheorem x : False := sorry\n")
	x.wantRun()
	wr(t, p, string(orig))
	x.wantSkip()
}

// ---------------------------------------------------------------- 2 deep and auditor-only modules

// addFxModule adds Janus.<name> to the fixture's framework (source and compiled data).
func addFxModule(t *testing.T, x *incrFx, name, src string) {
	t.Helper()
	rel := "Janus/" + strings.ReplaceAll(name, ".", "/")
	x.fwFiles[rel+".lean"] = []byte(src)
	wr(t, filepath.Join(x.build, ".lake/build/lib/lean", rel+".olean"), "olean of "+rel)
}

func TestRT02AuditorOnlyModule(t *testing.T) {
	// a module imported ONLY by the auditor (Audit.lean, not reachable from Janus.lean or from the proof)
	setup := func(t *testing.T) *incrFx {
		x := newIncrFx(t)
		addFxModule(t, x, "Tools.AuditHelper", "import Janus.Tools.AuditHelper2\n")
		addFxModule(t, x, "Tools.AuditHelper2", "prelude\n")
		x.fwFiles["Janus/Tools/Audit.lean"] = []byte("import Lean\nimport Janus.Tools.AuditHelper\n")
		x.pass()
		x.wantSkip()
		return x
	}
	t.Run("its source", func(t *testing.T) {
		x := setup(t)
		x.fwFiles["Janus/Tools/AuditHelper.lean"] = []byte("import Janus.Tools.AuditHelper2\n-- weaker\n")
		x.wantRun()
	})
	t.Run("its import two levels down", func(t *testing.T) {
		x := setup(t)
		x.fwFiles["Janus/Tools/AuditHelper2.lean"] = []byte("prelude\n-- weaker\n")
		x.wantRun()
	})
	t.Run("its compiled data", func(t *testing.T) {
		x := setup(t)
		wr(t, filepath.Join(x.build, ".lake/build/lib/lean/Janus/Tools/AuditHelper2.olean"), "weaker audit olean")
		x.wantRun()
	})
	t.Run("its compiled data, same size, mtime restored", func(t *testing.T) {
		x := setup(t)
		p := filepath.Join(x.build, ".lake/build/lib/lean/Janus/Tools/AuditHelper2.olean")
		b, _ := os.ReadFile(p)
		editKeepingSizeAndTime(t, p, bytes.Replace(b, []byte("olean"), []byte("oleaN"), 1))
		x.wantRun()
	})
	t.Run("a module the auditor does not import stays irrelevant", func(t *testing.T) {
		x := setup(t)
		x.fwFiles["Janus/Unused.lean"] = []byte("import Janus.C\n-- edit\n")
		x.wantSkip()
	})
}

func TestRT02DeepFrameworkModules(t *testing.T) {
	// the deepest module of the fixture's chain Janus -> B -> D -> E, in every spelling of the import
	for _, c := range []struct {
		name, header string
	}{
		{"plain import", "import Janus.Unused\n"},
		{"public import", "public import Janus.Unused\n"},
		{"import all", "import all Janus.Unused\n"},
		{"meta import", "meta import Janus.Unused\n"},
		{"private import", "private import Janus.Unused\n"},
		{"module header (Lean module system)", "module\n\nimport Janus.Unused\n"},
		{"module header, comment, public import", "module\n/- c -/\npublic import Janus.Unused -- x\n"},
		{"prelude then import", "prelude\nimport Janus.Unused\n"},
		{"two imports on one line", "import Janus.C import Janus.Unused\n"},
		{"comment between modifier and module", "import /- c -/ Janus.Unused\n"},
		{"leading doc-less comments", "-- a\n/- b -/\n-- c\nimport Janus.Unused\n"},
	} {
		t.Run(c.name, func(t *testing.T) {
			x := newIncrFx(t)
			// a framework module reachable from the proof only (Janus.Unused is not imported by Janus.lean)
			wr(t, filepath.Join(x.root, "proofs/P.lean"), c.header+"theorem x : True := trivial\n")
			x.pass()
			x.wantSkip()
			x.fwFiles["Janus/Unused.lean"] = []byte("import Janus.C\n-- edit\n")
			x.wantRun()
		})
	}
	t.Run("an import after a block comment containing import-looking text", func(t *testing.T) {
		x := newIncrFx(t)
		wr(t, filepath.Join(x.root, "proofs/P.lean"), "/- import Janus.C -/\nimport Janus.Unused\ntheorem x : True := trivial\n")
		x.pass()
		x.fwFiles["Janus/Unused.lean"] = []byte("import Janus.C\n-- edit\n")
		x.wantRun()
	})
}

func TestRT02LeanImportsFailClosed(t *testing.T) {
	// a header that is not understood must be an error (the item is then unkeyed), never "no imports"
	for _, src := range []string{
		"import «Janus».Unused\n",
		"import Janus.Unused.\n",
		"import ..\n",
		"/- never closed\nimport Janus.Unused\n",
	} {
		if mods, err := leanImports([]byte(src)); err == nil {
			t.Errorf("%q parsed as %v", src, mods)
		}
	}
	for src, want := range map[string][]string{
		"module\nimport A\nimport B\n":                 {"A", "B"},
		"module\nprelude\nimport A\n":                  {"A"},
		"module\n\npublic import A.B\nmeta import C\n": {"A.B", "C"},
	} {
		got, err := leanImports([]byte(src))
		if err != nil || strings.Join(got, ",") != strings.Join(want, ",") {
			t.Errorf("%q: got %v, %v want %v", src, got, err, want)
		}
	}
}

// ---------------------------------------------------------------- 3 toolchain, checker, auditor

func TestRT03ToolchainSwaps(t *testing.T) {
	tc := func(x *incrFx) *toolchain { p, _ := x.ctx.tchain(""); return p }
	cases := []struct {
		name string
		edit func(t *testing.T, x *incrFx)
	}{
		{"lean replaced by a different binary, same size and mtime", func(t *testing.T, x *incrFx) {
			p := tc(x).lean
			editKeepingSizeAndTime(t, p, []byte("leaX"))
		}},
		{"leanchecker replaced, same size and mtime", func(t *testing.T, x *incrFx) {
			p := tc(x).leanchecker
			b, _ := os.ReadFile(p)
			b[0] ^= 1
			editKeepingSizeAndTime(t, p, b)
		}},
		{"leanchecker replaced by lean (checker accepts everything)", func(t *testing.T, x *incrFx) {
			a, b := tc(x).lean, tc(x).leanchecker
			data, _ := os.ReadFile(a)
			wr(t, b, string(data))
		}},
		{"lake (any other file of bin/) replaced, same size and mtime", func(t *testing.T, x *incrFx) {
			p := filepath.Join(tc(x).sysroot, "bin", "lake")
			editKeepingSizeAndTime(t, p, []byte("lake2"))
		}},
		{"core library olean, same size and mtime (the change time cannot be restored)", func(t *testing.T, x *incrFx) {
			p := filepath.Join(tc(x).libDir, "Init.olean")
			editKeepingSizeAndTime(t, p, []byte("inix"))
		}},
		{"core library file replaced by a symlink to a copy", func(t *testing.T, x *incrFx) {
			p := filepath.Join(tc(x).libDir, "Init.olean")
			b, _ := os.ReadFile(p)
			cp := p + ".real"
			wr(t, cp, string(b))
			os.Remove(p)
			if err := os.Symlink(cp, p); err != nil {
				t.Fatal(err)
			}
		}},
		{"elan override to another version", func(t *testing.T, x *incrFx) { x.tcver = "Lean (version 4.0.0)" }},
		{"lean-toolchain of the framework", func(t *testing.T, x *incrFx) {
			x.fwFiles["lean-toolchain"] = []byte("leanprover/lean4:v4.0.0\n")
		}},
		{"auditor executable, same size and mtime", func(t *testing.T, x *incrFx) {
			p := filepath.Join(x.build, ".lake/build/bin/janus-audit")
			b, _ := os.ReadFile(p)
			b[0] ^= 1
			editKeepingSizeAndTime(t, p, b)
		}},
		{"auditor executable replaced by a symlink to another file", func(t *testing.T, x *incrFx) {
			p := filepath.Join(x.build, ".lake/build/bin/janus-audit")
			other := filepath.Join(x.root, "permissive-audit")
			wr(t, other, "permissive")
			os.Remove(p)
			if err := os.Symlink(other, p); err != nil {
				t.Fatal(err)
			}
		}},
		{"auditor module data (Audit.olean), same size and mtime", func(t *testing.T, x *incrFx) {
			p := filepath.Join(x.build, ".lake/build/lib/lean/Janus/Tools/Audit.olean")
			b, _ := os.ReadFile(p)
			b[0] ^= 1
			editKeepingSizeAndTime(t, p, b)
		}},
		{"auditor leaves the clean environment: Audit.lean stops importing Janus (still hashed)", func(t *testing.T, x *incrFx) {
			x.fwFiles["Janus/Tools/Audit.lean"] = []byte("import Lean\n-- no Janus\n")
		}},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			x := newIncrFx(t)
			// make bin/lake exist before the first PASS for the lake case
			if strings.HasPrefix(c.name, "lake") {
				wr(t, filepath.Join(tc(x).sysroot, "bin", "lake"), "lake1")
			}
			x.pass()
			x.wantSkip()
			c.edit(t, x)
			x.wantRun()
		})
	}
}

// ---------------------------------------------------------------- 4 env, scripts

func TestRT04EnvironmentChangesAreMisses(t *testing.T) {
	for _, e := range []string{
		"JANUS_ITEM_TIMEOUT=0", "JANUS_ITEM_TIMEOUT=1", "JANUS_UNSAFE_NO_SANDBOX=1", "JANUS_RESULT_CACHE=off",
		"JANUS_VERIFIER_ID=exe", "JANUS_REPLAY_THREADS=1", "JANUS_JOB_MEM=1G", "JANUS_LEAN_SYSROOT=/x",
		"LEAN_PATH=/tmp/shadow", "LEAN_SRC_PATH=/tmp/shadow", "LEAN_NUM_THREADS=1", "LAKE_HOME=/x", "LAKE_NO_CACHE=1",
		"ELAN_TOOLCHAIN=stable", "ELAN_HOME=/x", "GOFLAGS=-tags=x", "GOEXPERIMENT=swissmap", "GODEBUG=x=1",
		"GOARCH=amd64", "GOAMD64=v3", "GOOS=darwin", "GOROOT=/x", "GOTOOLCHAIN=local", "GOWORK=/x/go.work",
		"CGO_ENABLED=1", "CGO_CFLAGS=-O3", "MEMCAP_LIMIT=1G", "KEEP=1", "TMPDIR=/x", "ASL_FOO=1", "SAIL_FOO=1",
		"JANUS_ISA=amd64", "JANUS_ROOT_X=1",
	} {
		t.Run(e, func(t *testing.T) {
			x := newIncrFx(t)
			x.pass()
			x.wantSkip()
			x.ctx.environ = append(x.ctx.environ, e)
			x.wantRun()
		})
	}
	t.Run("a variable set then unset or emptied", func(t *testing.T) {
		x := newIncrFx(t)
		x.ctx.environ = append(x.ctx.environ, "JANUS_FOO=1")
		x.pass()
		x.wantSkip()
		x.ctx.environ = x.ctx.environ[:len(x.ctx.environ)-1] // unset
		x.wantRun()
		x.ctx.environ = append(x.ctx.environ, "JANUS_FOO=") // empty is not unset
		x.wantRun()
	})
	t.Run("a duplicated variable: the last one wins in the process, the key must see a change", func(t *testing.T) {
		x := newIncrFx(t)
		x.ctx.environ = append(x.ctx.environ, "JANUS_FOO=1")
		x.pass()
		x.ctx.environ = append(x.ctx.environ, "JANUS_FOO=2")
		x.wantRun()
	})
}

// the variables that do not enter the key must not be able to change an outcome. Each is on the list
// for a stated reason; this test pins the list so that a new entry is a conscious decision.
func TestRT04EnvSkipListIsPinned(t *testing.T) {
	var names []string
	for k := range incrEnvSkip {
		names = append(names, k)
	}
	// every entry only names a location, a degree of parallelism, a gate bookkeeping flag or a cache dir
	for _, k := range names {
		switch k {
		case "JANUS_JOBS", "JANUS_LANES", "JANUS_LANE_JOBS", "JANUS_PRECHECK_JOBS", "JANUS_GOTEST_PARALLEL", "JANUS_POOL_DIR",
			"JANUS_EXAMPLES_SUMMARY", "JANUS_EXAMPLES_PREBUILT", "JANUS_PRINT_SNAPSHOT", "JANUS_GATE_PG", "JANUS_GATE_PREBUILT",
			"JANUS_GATE_FORCE", "JANUS_GATE_INCREMENTAL", "JANUS_SPEED_BASELINE", "JANUS_INCR", "JANUS_INCR_RECORD",
			"JANUS_INCR_EXPLAIN", "JANUS_INCR_NOTE", "JANUS_INCR_PRECHECK", "JANUS_GATE_T0", "JANUS_MEMGUARD_CGROUP",
			"JANUS_AUDIT_BIN", "JANUS_AUDIT_PREBUILT", "GOCACHE", "GOMODCACHE", "GOPATH", "GOTMPDIR", "GOENV":
		default:
			t.Errorf("unreviewed entry %s in incrEnvSkip", k)
		}
	}
	// the three that change what gets executed or how results are interpreted are handled elsewhere:
	// JANUS_INCR_EXPLAIN (scripts/lib/test-rt-incr.sh: cleared by gate.sh), GOENV and GOMODCACHE (lane arguments).
}

func TestRT04ScriptSwapsAreMisses(t *testing.T) {
	x := newIncrFx(t)
	x.pass()
	x.wantSkip()
	p := filepath.Join(x.root, "scripts/run.sh")
	b, _ := os.ReadFile(p)
	editKeepingSizeAndTime(t, p, bytes.Replace(b, []byte("echo"), []byte("exit"), 1))
	x.wantRun()
	// the script replaced by a symlink to a copy with the original content: same content, a hit
	// (the key names content, not inodes)
	editKeepingSizeAndTime(t, p, b)
	x.wantSkip()
	// a script that is a directory or a special file cannot be hashed: unkeyed
	os.Remove(p)
	os.Mkdir(p, 0o755)
	if got := x.run("check", nil); !strings.HasPrefix(got, "NOKEY") {
		t.Fatalf("want NOKEY, got %q", got)
	}
}

// ---------------------------------------------------------------- 5 key design

func TestRT05SameContentOtherPathIsAnotherKey(t *testing.T) {
	x := newIncrFx(t)
	x.pass()
	k0 := x.key()
	// a renamed proof with the same bytes
	b, _ := os.ReadFile(filepath.Join(x.root, "proofs/P.lean"))
	wr(t, filepath.Join(x.root, "proofs/Q.lean"), string(b))
	x.sp.Proofs = []string{"proofs/Q.lean"}
	if x.key() == k0 {
		t.Fatal("a renamed proof file has the same key")
	}
	x.wantRun()
	// a renamed binary with the same bytes (identity.json updated to name it)
	x.sp.Proofs = []string{"proofs/P.lean"}
	x.wantSkip()
	// the same item under another id never uses this record
	x.sp.ID = "arm64:P2"
	x.wantRun()
	x.sp.ID = "arm64:P"
	x.sp.Kind = "other"
	x.wantRun()
}

func TestRT05SymlinkedInputsAreHashedByContent(t *testing.T) {
	// a package whose build-relevant files are symbolic links: editing the file a link names must change the key
	for _, c := range []struct{ name, link, target string }{
		{"lakefile.toml", "lakefile.toml", "name = \"p\"\n"},
		{"a data file read at elaboration", "data.txt", "x"},
		{"a non-imported lean file", "Orphan.lean", "def x := 1\n"},
	} {
		t.Run(c.name, func(t *testing.T) {
			x := newIncrFx(t)
			shared := filepath.Join(x.root, "shared", c.link)
			wr(t, shared, c.target)
			wr(t, filepath.Join(x.root, "pkg/Main.lean"), "import Janus\n")
			if err := os.Symlink(shared, filepath.Join(x.root, "pkg", c.link)); err != nil {
				t.Fatal(err)
			}
			x.sp.Pkgs = []string{"pkg"}
			x.pass()
			x.wantSkip()
			wr(t, shared, c.target+"-- weaker\n")
			x.wantRun()
		})
	}
	t.Run("a link to a directory of the package", func(t *testing.T) {
		x := newIncrFx(t)
		wr(t, filepath.Join(x.root, "shared/dir/a.lean"), "def a := 1\n")
		wr(t, filepath.Join(x.root, "pkg/Main.lean"), "import Janus\n")
		if err := os.Symlink(filepath.Join(x.root, "shared/dir"), filepath.Join(x.root, "pkg/Sub")); err != nil {
			t.Fatal(err)
		}
		x.sp.Pkgs = []string{"pkg"}
		x.pass()
		wr(t, filepath.Join(x.root, "shared/dir/a.lean"), "def a := 2\n")
		x.wantRun()
	})
	t.Run("a dangling link is unkeyed or keyed by its target text, and changes when it is repaired", func(t *testing.T) {
		x := newIncrFx(t)
		wr(t, filepath.Join(x.root, "pkg/Main.lean"), "import Janus\n")
		if err := os.Symlink(filepath.Join(x.root, "shared/gone"), filepath.Join(x.root, "pkg/lakefile.toml")); err != nil {
			t.Fatal(err)
		}
		x.sp.Pkgs = []string{"pkg"}
		if got := x.run("check", nil); !strings.HasPrefix(got, "NOKEY") {
			t.Fatalf("a dangling link must leave the item unkeyed, got %q", got)
		}
	})
}

func TestRT05LinkAndNameFramingDoNotCollide(t *testing.T) {
	// "a -> b" linking to "c" and "a" linking to "b -> c" must not hash alike
	mk := func(t *testing.T, name, target string) string {
		x := newIncrFx(t)
		wr(t, filepath.Join(x.root, "pkg/Main.lean"), "import Janus\n")
		wr(t, filepath.Join(x.root, "pkg", target), "same content")
		if err := os.Symlink(target, filepath.Join(x.root, "pkg", name)); err != nil {
			t.Fatal(err)
		}
		x.sp.Pkgs = []string{"pkg"}
		return x.key()
	}
	k1 := mk(t, "a -> b", "c")
	k2 := mk(t, "a", "b -> c")
	if k1 == k2 {
		t.Fatal("two different link layouts have the same key")
	}
	// file names that contain what looks like the next field
	mkf := func(t *testing.T, files map[string]string) string {
		x := newIncrFx(t)
		for n, c := range files {
			wr(t, filepath.Join(x.root, "pkg", n), c)
		}
		wr(t, filepath.Join(x.root, "pkg/Main.lean"), "import Janus\n")
		x.sp.Pkgs = []string{"pkg"}
		return x.key()
	}
	h := sha256Hex([]byte("x"))
	if mkf(t, map[string]string{"f": "x"}) == mkf(t, map[string]string{"f " + h + "\nfile g": "x", "g": "x"}) {
		t.Fatal("a file name that spells another entry collides")
	}
}

func TestRT05FinalKeyFramesComponentNames(t *testing.T) {
	// component names come from file names: one that contains a newline and a hash must not be able to
	// stand for two components
	x := newIncrFx(t)
	keys := map[string]string{}
	add := func(name string, mut func(sp *incrSpec)) {
		sp := *x.sp
		mut(&sp)
		k, comps := x.fresh().compute(&sp)
		if k == "" {
			t.Fatalf("%s: %v", name, firstErr(comps))
		}
		if prev, ok := keys[k]; ok {
			t.Fatalf("%s collides with %s", name, prev)
		}
		keys[k] = name
	}
	wr(t, filepath.Join(x.root, "f"), "1")
	wr(t, filepath.Join(x.root, "g"), "2")
	h := x.fresh()
	sf, _ := h.fileSha("f")
	add("base", func(sp *incrSpec) {})
	add("f,g as files", func(sp *incrSpec) { sp.Files = []string{"f", "g"} })
	add("f as file, g as pin", func(sp *incrSpec) { sp.Files = []string{"f"}; sp.Pins = []string{"g"} })
	wr(t, filepath.Join(x.root, "f\nscript:g"), "1")
	add("a file named like the next component", func(sp *incrSpec) { sp.Files = []string{"f\nscript:g"} })
	_ = sf
}

func TestRT05RecordsOfOneItemNeverServeAnother(t *testing.T) {
	x := newIncrFx(t)
	x.pass()
	k1 := x.key()
	// a second item with different inputs: copy item 1's record file to its path
	x.sp.ID = "arm64:Q"
	k2 := x.key()
	b, _ := os.ReadFile(incrPath(k1))
	os.MkdirAll(filepath.Dir(incrPath(k2)), 0o700)
	os.WriteFile(incrPath(k2), b, 0o600)
	x.wantRun()
	// swap two valid records between their paths
	x.pass() // k2 recorded
	b2, _ := os.ReadFile(incrPath(k2))
	os.WriteFile(incrPath(k1), b2, 0o600)
	os.WriteFile(incrPath(k2), b, 0o600)
	x.wantRun()
	x.sp.ID = "arm64:P"
	x.wantRun()
}

// ---------------------------------------------------------------- 6 cache-file tampering

func TestRT06TruncationAtEveryLengthIsAMiss(t *testing.T) {
	x := newIncrFx(t)
	x.pass()
	p := incrPath(x.key())
	good, _ := os.ReadFile(p)
	for n := 0; n < len(good); n++ {
		if err := os.WriteFile(p, good[:n], 0o600); err != nil {
			t.Fatal(err)
		}
		if got := x.run("check", nil); strings.HasPrefix(got, "SKIP") {
			t.Fatalf("a record truncated to %d of %d bytes is a SKIP", n, len(good))
		}
	}
	os.WriteFile(p, good, 0o600)
	x.wantSkip()
}

func TestRT06EveryFlippedByteIsAMiss(t *testing.T) {
	x := newIncrFx(t)
	x.pass()
	p := incrPath(x.key())
	good, _ := os.ReadFile(p)
	skips := 0
	for i := range good {
		b := append([]byte(nil), good...)
		b[i] ^= 0x20 // case flip / punctuation shift
		if bytes.Equal(b, good) {
			continue
		}
		os.WriteFile(p, b, 0o600)
		if got := x.run("check", nil); strings.HasPrefix(got, "SKIP") {
			// a flip that leaves the parsed record and its MAC unchanged (JSON whitespace) is not a change of the
			// record; anything else is a forgery
			var e1, e2 incrEntry
			json.Unmarshal(good, &e1)
			if err := json.Unmarshal(b, &e2); err != nil || e1.Key != e2.Key || e1.MAC != e2.MAC || !bytes.Equal(e1.Body, e2.Body) {
				t.Fatalf("flipping byte %d (%q -> %q) still SKIPs", i, good[i], b[i])
			}
			skips++
		}
	}
	t.Logf("%d of %d single-byte flips were no-ops for the record (case-insensitive JSON keys)", skips, len(good))
}

func TestRT06MacKeyHandling(t *testing.T) {
	t.Run("the HMAC key file is group-readable: every record is refused", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		x.wantSkip()
		kp := filepath.Join(resultCacheDir(), ".key")
		if err := os.Chmod(kp, 0o640); err != nil {
			t.Fatal(err)
		}
		x.wantRun()
		os.Chmod(kp, 0o600)
		x.wantSkip()
	})
	t.Run("the HMAC key is replaced by an attacker's key: old records fail", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		kp := filepath.Join(resultCacheDir(), ".key")
		os.WriteFile(kp, bytes.Repeat([]byte{7}, 32), 0o600)
		x.wantRun()
	})
	t.Run("the HMAC key is deleted: old records fail, a new key is made", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		os.Remove(filepath.Join(resultCacheDir(), ".key"))
		x.wantRun()
		x.pass()
		x.wantSkip()
	})
	t.Run("the HMAC key is a symlink", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		kp := filepath.Join(resultCacheDir(), ".key")
		b, _ := os.ReadFile(kp)
		os.Remove(kp)
		os.WriteFile(kp+".real", b, 0o600)
		os.Symlink(kp+".real", kp)
		x.wantRun()
	})
	t.Run("the HMAC key has the wrong length", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		kp := filepath.Join(resultCacheDir(), ".key")
		b, _ := os.ReadFile(kp)
		os.WriteFile(kp, b[:31], 0o600)
		x.wantRun()
	})
	t.Run("the result directory is group-writable", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		os.Chmod(resultCacheDir(), 0o770)
		x.wantRun()
		os.Chmod(resultCacheDir(), 0o700)
		x.wantSkip()
	})
	t.Run("a record file owned by another user", func(t *testing.T) {
		if os.Geteuid() != 0 {
			t.Skip("needs root to chown")
		}
		x := newIncrFx(t)
		x.pass()
		p := incrPath(x.key())
		if err := os.Chown(p, 65534, 65534); err != nil {
			t.Skip(err)
		}
		x.wantRun()
	})
	t.Run("a record forged with the MAC computed over the wrong domain or the wrong key field", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		k := x.key()
		hk, _ := resultHMACKey()
		var e incrEntry
		b, _ := os.ReadFile(incrPath(k))
		json.Unmarshal(b, &e)
		for _, mac := range []string{
			incrMAC(hk, strings.Repeat("0", 64), e.Body), // MAC for another key
			incrMAC(hk, k, append(e.Body, ' ')),          // MAC over a different body
			resultMAC(hk, k, e.Body),                     // the result-cache domain
			incrMAC(nil, k, e.Body),                      // the empty key
			strings.ToUpper(incrMAC(hk, k, e.Body)),      // right MAC, different spelling
			incrMAC(hk, k, e.Body)[:63],                  // prefix of the right MAC
		} {
			e2 := e
			e2.MAC = mac
			nb, _ := json.Marshal(e2)
			os.WriteFile(incrPath(k), nb, 0o600)
			x.wantRun()
		}
	})
	t.Run("a pass record whose body claims another id or schema is still bound to its key", func(t *testing.T) {
		x := newIncrFx(t)
		x.pass()
		k := x.key()
		hk, _ := resultHMACKey()
		// a record authenticated by the real key but whose body says result=fail, schema 2, or another key
		for _, mut := range []func(r *incrRecord){
			func(r *incrRecord) { r.Result = "fail" },
			func(r *incrRecord) { r.Result = "" },
			func(r *incrRecord) { r.Schema = 2 },
			func(r *incrRecord) { r.Key = strings.Repeat("1", 64) },
		} {
			r := incrRecord{Schema: incrSchema, Key: k, ID: "x", Result: "pass"}
			mut(&r)
			body, _ := json.Marshal(r)
			e := incrEntry{Key: k, Body: body, MAC: incrMAC(hk, k, body)}
			nb, _ := json.Marshal(e)
			os.WriteFile(incrPath(k), nb, 0o600)
			x.wantRun()
		}
	})
}

// ---------------------------------------------------------------- 10 races

func TestRT10ConcurrentWritersAndReadersNeverSeeAPartialRecord(t *testing.T) {
	x := newIncrFx(t)
	k := x.key()
	r := &incrRecord{Schema: incrSchema, Key: k, ID: "i", Kind: "k", Result: "pass", Wall: 1}
	var wg sync.WaitGroup
	stop := make(chan struct{})
	var bad sync.Map
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				if err := incrStore(k, r); err != nil {
					bad.Store("store: "+err.Error(), true)
				}
			}
		}()
	}
	var reads, hits int
	var mu sync.Mutex
	for i := 0; i < 4; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				select {
				case <-stop:
					return
				default:
				}
				got, why := incrLookup(k)
				mu.Lock()
				reads++
				if got != nil {
					hits++
				} else if why != "no record" && !strings.HasPrefix(why, "unreadable record") {
					bad.Store(why, true) // an existing record must be complete or absent, never torn
				}
				mu.Unlock()
			}
		}()
	}
	time.Sleep(1500 * time.Millisecond)
	close(stop)
	wg.Wait()
	bad.Range(func(k, _ any) bool { t.Errorf("torn or failed: %v", k); return true })
	if hits == 0 {
		t.Fatalf("no lookup ever saw the record (%d reads)", reads)
	}
	// stray temp files (a crashed writer) are never read as records
	matches, _ := filepath.Glob(filepath.Join(filepath.Dir(incrPath(k)), ".*tmp-*"))
	for _, m := range matches {
		os.Remove(m)
	}
	if err := os.WriteFile(filepath.Join(filepath.Dir(incrPath(k)), "."+k+".json.tmp-1"), []byte("{"), 0o600); err != nil {
		t.Fatal(err)
	}
	if got, why := incrLookup(k); got == nil {
		t.Fatalf("a stray temp file broke the record: %s", why)
	}
}

func TestRT10FailureWithdrawsAndConcurrentPassesAgree(t *testing.T) {
	// two gates record the same PASS at once: one record, valid
	x := newIncrFx(t)
	k := x.key()
	var wg sync.WaitGroup
	for i := 0; i < 8; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			c := x.fresh()
			var b bytes.Buffer
			_ = runIncr(c, "record", x.sp, map[string]string{"rc": "0", "pre-key": k}, &b)
		}()
	}
	wg.Wait()
	x.wantSkip()
	// a failure by either gate withdraws it
	x.run("record", map[string]string{"rc": "1", "pre-key": k})
	x.wantRun()
	// a gate whose inputs changed under it (edit-and-revert race) records nothing for the edited key
	pk := x.key()
	wr(t, filepath.Join(x.root, "proofs/P.lean"), "import Janus\nimport Extracted\n-- edited while running\n")
	if out := x.run("record", map[string]string{"rc": "0", "pre-key": pk}); !strings.HasPrefix(out, "NOTRECORDED") {
		t.Fatal(out)
	}
	if _, err := os.Stat(incrPath(x.key())); err == nil {
		t.Fatal("a record exists for the edited inputs")
	}
}

// ---------------------------------------------------------------- 12 failed and timed-out runs

func TestRT12EveryNonzeroExitIsNeverRecorded(t *testing.T) {
	x := newIncrFx(t)
	k := x.key()
	// signals as the shell reports them, timeout(1)'s 124, out-of-memory 137, the pool's own codes
	for _, rc := range []string{"1", "2", "3", "75", "90", "124", "125", "126", "127", "130", "137", "139", "143", "255", "256", "-1", "99999999999"} {
		out := x.run("record", map[string]string{"rc": rc, "pre-key": k})
		if strings.HasPrefix(out, "RECORDED") {
			t.Fatalf("rc %s was recorded", rc)
		}
		x.wantRun()
	}
	// rc spellings that are not the number 0 must not be taken for it
	for _, rc := range []string{"00", "0 ", " 0", "+0", "-0", "0x0", "0.0", "", "false", "ok"} {
		var b bytes.Buffer
		err := runIncr(x.fresh(), "record", x.sp, map[string]string{"rc": rc, "pre-key": k}, &b)
		if err == nil && strings.HasPrefix(b.String(), "RECORDED") && rc != "00" && rc != "+0" && rc != "-0" {
			t.Fatalf("rc %q was recorded", rc)
		}
		_ = os.Remove(incrPath(k))
	}
}

func TestRT12PartialLaneArgumentsAreInTheKey(t *testing.T) {
	// a lane run with a narrowed test selection (--gotest-run) or a subset of rounds records under its own key,
	// which a full lane never matches
	x := newIncrFx(t)
	base := *x.sp
	full := func(args ...string) string {
		sp := base
		sp.Args = args
		k, comps := x.fresh().compute(&sp)
		if k == "" {
			t.Fatal(firstErr(comps))
		}
		return k
	}
	kFull := full("lane:gotest", "run:", "shards:2")
	for _, a := range [][]string{
		{"lane:gotest", "run:TestFoo", "shards:2"},
		{"lane:gotest", "run:", "shards:3"},
		{"lane:rounds", "rounds:", "shards:2"},
		{"lane:gotest", "shards:2"},
	} {
		if full(a...) == kFull {
			t.Fatalf("%v has the key of the full lane", a)
		}
	}
	sp := base
	sp.Args = []string{"lane:gotest", "run:TestFoo", "shards:2"}
	x.sp = &sp
	x.pass()
	x.wantSkip()
	x.sp.Args = []string{"lane:gotest", "run:", "shards:2"}
	x.wantRun()
}

// the shell side of the red team: scripts/lib/test-rt-incr.sh (explain/pre-check variables, the tree pin,
// failed items, script coverage, the go configuration of lanes)
func TestRTIncrScripts(t *testing.T) {
	root, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("bash", filepath.Join(root, "scripts", "lib", "test-rt-incr.sh"))
	cmd.Dir = root
	out, err := cmd.CombinedOutput()
	if err != nil || bytes.Contains(out, []byte("\nFAIL ")) || bytes.HasPrefix(out, []byte("FAIL ")) {
		t.Fatalf("scripts/lib/test-rt-incr.sh: %v\n%s", err, out)
	}
}

// the build-cache side: the Sail driver key (toolchain binaries by content, parent cargo config, env) and the
// integrity layer of the ASL/Sail caches
func TestRTBuildCacheScripts(t *testing.T) {
	root, _ := filepath.Abs("../..")
	for _, s := range []string{"test-rt-bcache.sh", "test-bcache.sh"} {
		cmd := exec.Command("bash", filepath.Join(root, "scripts", "lib", s))
		cmd.Dir = root
		out, err := cmd.CombinedOutput()
		if err != nil || bytes.Contains(out, []byte("\nFAIL ")) || bytes.HasPrefix(out, []byte("FAIL ")) {
			t.Fatalf("%s: %v\n%s", s, err, out)
		}
	}
}
