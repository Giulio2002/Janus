package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

// Expensive: needs forged fixtures (RT_BASE = a copy of the framework library, RT_FX = the forged
// oleans, RT_TMP = scratch on disk); skipped unless they are set.
// RT matrix: attacks on the parallel framework replay with the real leanchecker.
func TestRTMatrix(t *testing.T) {
	base := os.Getenv("RT_BASE")
	fx := os.Getenv("RT_FX")
	if base == "" || fx == "" {
		t.Skip("RT_BASE/RT_FX")
	}
	_, tc, _, runIn := realParFixture(t)
	type v struct {
		name     string
		add      map[string]string // lib-relative dest -> fixture src (or "@root" = base Janus.olean)
		wantFail bool
	}
	vs := []v{
		{"honest", nil, false},
		{"extra Janus.Zz forged", map[string]string{"Janus/Zz.olean": "out/zz/Janus/Zz.olean"}, true},
		{"extra Janus.Zz.Y forged, no Janus.Zz", map[string]string{"Janus/Zz/Y.olean": "out/zzy/Janus/Zz/Y.olean"}, true},
		{"JanusX86Zz forged (not a Janus.* module)", map[string]string{"JanusX86Zz.olean": "out/x86/JanusX86Zz.olean"}, false},
		{"JanusReplayRoot.Foo forged", map[string]string{"JanusReplayRoot/Foo.olean": "out/rr/JanusReplayRoot/Foo.olean"}, true},
		{"Janus.Pr with initialize printing replaying lines", map[string]string{"Janus/Pr.olean": "out/pr/Janus/Pr.olean"}, false},
		{"Janus.Okay honest extra", map[string]string{"Janus/Okay.olean": "out/ok/Janus/Okay.olean"}, false},
		{"Janus/Foo.bar.olean forged (odd component)", map[string]string{"Janus/Foo.bar.olean": "out/zz/Janus/Zz.olean"}, true},
		{"Janus/Foo bar.olean forged (space)", map[string]string{"Janus/Foo bar.olean": "out/zz/Janus/Zz.olean"}, true},
		{"Janus/.hidden.olean forged", map[string]string{"Janus/.hid.olean": "out/zz/Janus/Zz.olean"}, true},
	}
	for _, c := range vs {
		t.Run(c.name, func(t *testing.T) {
			lib := filepath.Join(os.Getenv("RT_TMP"), "lib-"+filepath.Base(t.TempDir()))
			if out, err := exec.Command("cp", "-al", base, lib).CombinedOutput(); err != nil {
				t.Fatalf("%v %s", err, out)
			}
			defer os.RemoveAll(lib)
			for dst, src := range c.add {
				p := filepath.Join(lib, dst)
				os.MkdirAll(filepath.Dir(p), 0o755)
				b, err := os.ReadFile(filepath.Join(fx, src))
				if err != nil {
					t.Fatal(err)
				}
				os.WriteFile(p, b, 0o644)
			}
			out, err, calls := realPar(t, tc, lib, runIn, 4)
			t.Logf("calls=%d err=%v out=%.300q", len(calls), err, out)
			if (err != nil) != c.wantFail {
				t.Errorf("UNEXPECTED: wantFail=%v err=%v", c.wantFail, err)
			}
		})
	}
}

func TestRTShadowedAlias(t *testing.T) {
	lib := os.Getenv("RT_LIB")
	if lib == "" {
		t.Skip("RT_LIB")
	}
	_, tc, _, runIn := realParFixture(t)
	out, err, calls := realPar(t, tc, lib, runIn, 4)
	t.Logf("calls=%d err=%v out=%q", len(calls), err, out)
	if err == nil {
		t.Errorf("BLOCKER: forged root passed parallel replay")
	}
}
