package main

// RT 11: the gate-private framework verdict store shared by --fresh rows.

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func rtStore(t *testing.T) (verdictStore, string) {
	t.Helper()
	d := newVerdictDir(t)
	privateCache(t)
	vs, ok, err := externalVerdictStore(map[string]string{"fresh": "true"})
	if err != nil || !ok {
		t.Fatalf("store: %v %v", ok, err)
	}
	return vs, d
}

// A tampered framework olean has another SHA-256, hence another pin set and another key: the stored PASS
// of the genuine build is not reused, in every way the bytes can change.
func TestRT11TamperedFrameworkOleanNeverReusesAPass(t *testing.T) {
	vs, _ := rtStore(t)
	good := pins{"Janus.olean": "aa", "Janus/A.olean": "bb", "Janus/A.ir": "cc"}
	fw := &pinnedLib{want: good}
	k := frameworkVerdictKey("tc", fw)
	vs.record(k, fw)
	if !vs.has(k) {
		t.Fatal("setup")
	}
	for name, p := range map[string]pins{
		"one module's olean changed":           {"Janus.olean": "aa", "Janus/A.olean": "b0", "Janus/A.ir": "cc"},
		"the .ir changed":                      {"Janus.olean": "aa", "Janus/A.olean": "bb", "Janus/A.ir": "c0"},
		"a module's server part appears":       {"Janus.olean": "aa", "Janus/A.olean": "bb", "Janus/A.ir": "cc", "Janus/A.olean.server": "dd"},
		"a module dropped":                     {"Janus.olean": "aa", "Janus/A.olean": "bb"},
		"two modules' hashes swapped":          {"Janus.olean": "bb", "Janus/A.olean": "aa", "Janus/A.ir": "cc"},
		"a name that spells another pin line":  {"Janus.olean": "aa", "Janus/A.olean": "bb", "Janus/A.ir": "cc", "x": "y\nJanus/B.olean zz"},
		"hash moved from one name to the next": {"Janus.olean": "aa", "Janus/A.olean bb": "", "Janus/A.ir": "cc"},
	} {
		if k2 := frameworkVerdictKey("tc", &pinnedLib{want: p}); k2 == k || vs.has(k2) {
			t.Errorf("%s: the stored PASS answers for different bytes", name)
		}
	}
}

// Only a PASS is ever stored, and a stored PASS cannot be turned into a FAIL-masking hit by planting
// a marker: a FAIL leaves no marker, and a planted marker without the store's MAC is not a verdict.
func TestRT11FailedReplayLeavesNothingAndPlantedMarkersAreMisses(t *testing.T) {
	vs, _ := rtStore(t)
	fw := &pinnedLib{want: pins{"Janus.olean": "aa"}}
	k := frameworkVerdictKey("tc", fw)
	for _, werr := range []error{os.ErrInvalid, os.ErrDeadlineExceeded, os.ErrProcessDone} {
		f := startFrameworkReplayIn(vs, "leanchecker", func(argv ...string) (string, error) { return "kernel rejected", werr }, k, fw, false, nil, true, true)
		f.wait()
		f.release()
		if vs.has(k) {
			t.Fatalf("a failed replay (%v) left a verdict", werr)
		}
	}
	if _, err := os.Stat(vs.path(k)); err == nil {
		t.Fatal("a failed replay left a file")
	}
	// the failure is reported to the caller, and the plan then replays the modules itself
	f := startFrameworkReplayIn(vs, "leanchecker", func(argv ...string) (string, error) { return "kernel rejected", os.ErrInvalid }, k, fw, false, nil, true, true)
	f.wait()
	p := &replayPlan{modules: []string{"Janus", "Janus.A"}}
	f.apply(p, &pinnedLib{want: pins{"Janus.olean": "aa", "Janus/A.olean": "bb"}})
	if len(p.cached) != 0 || len(p.done) != 0 {
		t.Fatalf("a failed framework replay marked modules as replayed: cached %v done %v", p.cached, p.done)
	}
	// read-only mode (no sandbox) never records
	f = startFrameworkReplayIn(vs, "leanchecker", func(argv ...string) (string, error) { return "", nil }, k, fw, false, nil, true, false)
	f.wait()
	f.release()
	if vs.has(k) {
		t.Fatal("a run with write=false recorded a verdict")
	}
}

// A marker of another kind or key under the store's own MAC key is not a framework verdict (domain separation),
// including the result-cache MAC of the same key string.
func TestRT11MarkerDomainsAreSeparated(t *testing.T) {
	vs, _ := rtStore(t)
	fw := &pinnedLib{want: pins{"Janus.olean": "aa"}}
	k := frameworkVerdictKey("tc", fw)
	other := frameworkVerdictKey("tc2", fw)
	hk, _ := vs.keyFn()
	p := vs.path(k)
	os.MkdirAll(filepath.Dir(p), 0o755)
	for name, line := range map[string]string{
		"a module marker's MAC":   markerHeader + markerMAC(hk, "module", k),
		"another key's MAC":       markerHeader + markerMAC(hk, "framework", other),
		"the result cache's key":  markerHeader + func() string { h, _ := resultHMACKey(); return markerMAC(h, "framework", k) }(),
		"upper-cased right MAC":   markerHeader + strings.ToUpper(markerMAC(hk, "framework", k)),
		"right MAC, wrong header": "janus-replay-marker-v1 " + markerMAC(hk, "framework", k),
	} {
		os.WriteFile(p, []byte(line+"\n"), 0o600)
		if vs.has(k) {
			t.Errorf("%s accepted as a framework verdict", name)
		}
	}
	// control: the right one is accepted
	os.WriteFile(p, []byte(markerHeader+markerMAC(hk, "framework", k)+"\n"), 0o600)
	if !vs.has(k) {
		t.Fatal("control failed")
	}
	// a marker that is a link, a group-writable-dir marker, or owned by someone else is not trusted
	b, _ := os.ReadFile(p)
	os.Remove(p)
	os.WriteFile(p+".real", b, 0o600)
	os.Symlink(p+".real", p)
	if vs.has(k) {
		t.Error("a symlinked marker was accepted")
	}
}

// The store's key is private: a readable or replaced key is refused, so no verdict is trusted.
func TestRT11StoreKeyIsProtected(t *testing.T) {
	vs, d := rtStore(t)
	fw := &pinnedLib{want: pins{"Janus.olean": "aa"}}
	k := frameworkVerdictKey("tc", fw)
	vs.record(k, fw)
	if !vs.has(k) {
		t.Fatal("setup")
	}
	kp := filepath.Join(d, "key", ".key")
	b, _ := os.ReadFile(kp)
	os.Chmod(kp, 0o644)
	if vs.has(k) {
		t.Error("a world-readable store key is still trusted")
	}
	os.Chmod(kp, 0o600)
	os.WriteFile(kp, bytes.Repeat([]byte{9}, 32), 0o600)
	if vs.has(k) {
		t.Error("a verdict authenticated under a replaced key was accepted")
	}
	os.WriteFile(kp, b, 0o600)
	if !vs.has(k) {
		t.Error("restoring the key did not restore the verdict")
	}
}

// A sandboxed proof sees neither the store's verdicts nor its key, and cannot write a verdict into it.
func TestRT11SandboxedProofCannotReachTheVerdictStore(t *testing.T) {
	for _, mode := range []string{"bwrap", "unshare"} {
		t.Run(mode, func(t *testing.T) {
			vs, d := rtStore(t)
			fw := &pinnedLib{want: pins{"Janus.olean": "aa"}}
			k := frameworkVerdictKey("tc", fw)
			vs.record(k, fw)
			var sb *sandbox
			if mode == "bwrap" {
				p, err := exec.LookPath("bwrap")
				if err != nil {
					t.Skip("no bwrap")
				}
				sb = &sandbox{mode: "bwrap", bwrap: p}
			} else {
				if _, err := exec.LookPath("unshare"); err != nil {
					t.Skip("no unshare")
				}
				sb = &sandbox{mode: "unshare"}
			}
			if err := sb.selfTest(); err != nil {
				t.Skipf("%s unavailable: %v", mode, err)
			}
			base, _ := janusRunBase()
			ws, _ := os.MkdirTemp(base, "rt11-")
			defer os.RemoveAll(ws)
			forgedKey := frameworkVerdictKey("tc", &pinnedLib{want: pins{"Janus.olean": "evil"}})
			hk, _ := vs.keyFn()
			vsd := shQuote(d)
			script := strings.Join([]string{
				"[ -e " + shQuote(vs.path(k)) + " ] && echo SAW_VERDICT",
				"[ \"$(cat " + shQuote(filepath.Join(d, "key", ".key")) + " 2>/dev/null | wc -c)\" -ge 32 ] && echo READ_KEY",
				"mkdir -p " + shQuote(filepath.Dir(vs.path(forgedKey))) + " 2>/dev/null; echo forged > " + shQuote(vs.path(forgedKey)) + " 2>/dev/null",
				"umount " + vsd + " 2>/dev/null; [ -e " + shQuote(vs.path(k)) + " ] && echo SAW_VERDICT_AFTER_UMOUNT",
				"true",
			}, "\n")
			out, _ := sb.command(ws, nil, []string{"/bin/sh", "-c", script}, os.Environ()).CombinedOutput()
			for _, bad := range []string{"SAW_VERDICT", "READ_KEY"} {
				if bytes.Contains(out, []byte(bad)) {
					t.Errorf("%s: %s\n%s", mode, bad, out)
				}
			}
			if bytes.Contains(out, hk) {
				t.Errorf("%s: key bytes leaked", mode)
			}
			if _, err := os.Stat(vs.path(forgedKey)); err == nil {
				t.Errorf("%s: a verdict was written into the store from the sandbox", mode)
			}
			if !vs.has(k) {
				t.Errorf("%s: the genuine verdict vanished", mode)
			}
		})
	}
}

// pinsDigest frames names and hashes: {"a b": "c"} and {"a": "b c"} must not share a digest.
func TestRT11PinsDigestFraming(t *testing.T) {
	if pinsDigest(pins{"a b": "c"}) == pinsDigest(pins{"a": "b c"}) {
		t.Fatal("pins digest collides across the name/hash boundary")
	}
	if pinsDigest(pins{"a": "x\nb y"}) == pinsDigest(pins{"a": "x", "b": "y"}) {
		t.Fatal("pins digest collides across lines")
	}
}
