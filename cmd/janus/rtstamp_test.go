package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func rtSha(b []byte) string { h := sha256.Sum256(b); return hex.EncodeToString(h[:]) }

// rtKeyDir: a private HMAC key directory for the signed restamp records of this test.
func rtKeyDir(t *testing.T) string {
	t.Helper()
	d := filepath.Join(t.TempDir(), "key")
	if err := os.Mkdir(d, 0o700); err != nil {
		t.Fatal(err)
	}
	t.Setenv("JANUS_CACHE_KEY_DIR", d)
	return d
}

const rtSignPy = `
import importlib.util, json, sys
spec = importlib.util.spec_from_file_location("bcache", sys.argv[1]); bc = importlib.util.module_from_spec(spec); spec.loader.exec_module(bc)
tree, out = sys.argv[2], sys.argv[3]
files = json.load(sys.stdin)
json.dump({"files": files, "mac": bc.record_mac(tree, files)}, open(out, "w"))
`

// rtRecord writes a record for dir; signed=false writes the bare (forged) map.
func rtRecord(t *testing.T, dir string, rec map[string]string, signed bool) string {
	t.Helper()
	rf := filepath.Join(t.TempDir(), "rec.json")
	b, _ := json.Marshal(rec)
	if !signed {
		writeBytes(t, rf, b)
		return rf
	}
	c := exec.Command("python3", "-I", "-c", rtSignPy, filepath.Join(repoRoot, "scripts", "lib", "bcache.py"), dir, rf)
	c.Stdin = bytes.NewReader(b)
	if out, err := c.CombinedOutput(); err != nil {
		t.Fatalf("sign: %v %s", err, out)
	}
	return rf
}

func rtRun(t *testing.T, dir, rf string) error {
	t.Helper()
	out, err := exec.Command("python3", "-I", filepath.Join(repoRoot, "scripts", "lib", "restamp.py"), dir, rf).CombinedOutput()
	t.Logf("%s", out)
	return err
}

func rtRestamp(t *testing.T, dir string, rec map[string]string) {
	t.Helper()
	if err := rtRun(t, dir, rtRecord(t, dir, rec, true)); err != nil {
		t.Fatalf("restamp: %v", err)
	}
}

// TestRTStampForgedRecord: restamp.py is not a blessing oracle: an unsigned, wrong-MAC or edited record pins nothing,
// and the real readyInfo then rejects the tampered tree.
func TestRTStampForgedRecord(t *testing.T) {
	rtKeyDir(t)
	fw, dir := j1StampedFramework(t)
	_, oldSp := fw.buildPaths(dir)
	fw.Dir = dir
	fw.Source = "directory"
	_, newSp := fw.buildPaths(dir)
	os.MkdirAll(filepath.Dir(newSp), 0o755)
	if err := os.Rename(oldSp, newSp); err != nil {
		t.Fatal(err)
	}
	A := filepath.Join(dir, ".lake", "build", "lib", "lean", "Janus", "A.olean")
	writeBytes(t, A, []byte("evil-a"))
	rec := map[string]string{A: rtSha([]byte("evil-a"))}
	// 1: no MAC at all
	if err := rtRun(t, dir, rtRecord(t, dir, rec, false)); err == nil {
		t.Error("BLOCKER unsigned record accepted")
	}
	if _, ok := fw.readyInfo(dir, nil); ok {
		t.Error("BLOCKER forged record made the tree ready")
	}
	// 2: wrong MAC
	rf := rtRecord(t, dir, rec, true)
	b, _ := os.ReadFile(rf)
	var doc map[string]any
	json.Unmarshal(b, &doc)
	doc["mac"] = strings.Repeat("0", 64)
	b, _ = json.Marshal(doc)
	writeBytes(t, rf, b)
	if err := rtRun(t, dir, rf); err == nil {
		t.Error("BLOCKER wrong-MAC record accepted")
	}
	// 3: edited after signing (sign a different hash, then swap in the evil one)
	rf = rtRecord(t, dir, map[string]string{A: rtSha([]byte("other"))}, true)
	b, _ = os.ReadFile(rf)
	json.Unmarshal(b, &doc)
	doc["files"] = rec
	b, _ = json.Marshal(doc)
	writeBytes(t, rf, b)
	if err := rtRun(t, dir, rf); err == nil {
		t.Error("BLOCKER edited record accepted")
	}
	if _, ok := fw.readyInfo(dir, nil); ok {
		t.Error("BLOCKER tampered tree ready after refused records")
	}
	// 4: the genuine signed record is honoured
	rtRestamp(t, dir, rec)
	if _, ok := fw.readyInfo(dir, nil); !ok {
		t.Error("genuine signed record not honoured")
	}
}

// TestRTStampSymlinkParent: a symlinked directory component (Janus -> elsewhere) is never followed.
func TestRTStampSymlinkParent(t *testing.T) {
	rtKeyDir(t)
	fw, dir := j1StampedFramework(t)
	_, oldSp := fw.buildPaths(dir)
	fw.Dir = dir
	fw.Source = "directory"
	_, newSp := fw.buildPaths(dir)
	os.MkdirAll(filepath.Dir(newSp), 0o755)
	if err := os.Rename(oldSp, newSp); err != nil {
		t.Fatal(err)
	}
	lib := filepath.Join(dir, ".lake", "build", "lib", "lean")
	other := filepath.Join(t.TempDir(), "Janus")
	if err := os.Rename(filepath.Join(lib, "Janus"), other); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(other, filepath.Join(lib, "Janus")); err != nil {
		t.Fatal(err)
	}
	writeBytes(t, filepath.Join(other, "A.olean"), []byte("evil-a"))
	rtRestamp(t, dir, map[string]string{
		filepath.Join(lib, "Janus", "A.olean"): rtSha([]byte("evil-a")),
		filepath.Join(other, "A.olean"):        rtSha([]byte("evil-a")),
	})
	if _, ok := fw.readyInfo(dir, nil); ok {
		t.Error("BLOCKER symlinked parent component followed")
	}
}

func TestRTStamp(t *testing.T) {
	rtKeyDir(t)
	fw, dir := j1StampedFramework(t)
	_, oldSp := fw.buildPaths(dir)
	fw.Dir = dir
	fw.Source = "directory"
	_, newSp := fw.buildPaths(dir)
	os.MkdirAll(filepath.Dir(newSp), 0o755)
	if err := os.Rename(oldSp, newSp); err != nil {
		t.Fatal(err)
	}
	lib := filepath.Join(dir, ".lake", "build", "lib", "lean")
	A := filepath.Join(lib, "Janus", "A.olean")
	J := filepath.Join(lib, "Janus.olean")
	// 1: recorded + modified -> ready
	writeBytes(t, A, []byte("a-restored"))
	rtRestamp(t, dir, map[string]string{A: rtSha([]byte("a-restored"))})
	if _, ok := fw.readyInfo(dir, nil); !ok {
		t.Error("recorded file not ready")
	}
	// 2: unrecorded modification -> not ready
	writeBytes(t, J, []byte("evil"))
	rtRestamp(t, dir, map[string]string{A: rtSha([]byte("a-restored"))})
	if _, ok := fw.readyInfo(dir, nil); ok {
		t.Error("BLOCKER unrecorded modification ready")
	}
	// 3: record with wrong hash
	rtRestamp(t, dir, map[string]string{J: rtSha([]byte("other"))})
	if _, ok := fw.readyInfo(dir, nil); ok {
		t.Error("BLOCKER wrong-hash record ready")
	}
	// 4: a '..' path in a (signed) record never matches
	rtRestamp(t, dir, map[string]string{lib + "/Janus/../Janus.olean": rtSha([]byte("evil"))})
	_, ok := fw.readyInfo(dir, nil)
	if ok {
		t.Error("BLOCKER dotdot record path made the tree ready")
	}
	// 5: extra file (.olean.private) added, recorded: stamp has no pin for it
	writeBytes(t, J, []byte("janus-data"))
	writeBytes(t, filepath.Join(lib, "Janus", "Z.olean"), []byte("z"))
	rtRestamp(t, dir, map[string]string{filepath.Join(lib, "Janus", "Z.olean"): rtSha([]byte("z"))})
	// Z not in sources -> pinLib ignores (keep) ; just log
	_, ok = fw.readyInfo(dir, nil)
	t.Logf("extra non-framework module Z: ready=%v", ok)
	// 6: auditor exe replaced and recorded -> not ready
	writeBytes(t, auditExePath(dir), []byte("evil-exe"))
	rtRestamp(t, dir, map[string]string{auditExePath(dir): rtSha([]byte("evil-exe"))})
	if _, ok := fw.readyInfo(dir, nil); ok {
		t.Error("BLOCKER auditor swap ready")
	}
	// 7: stamp targets/sha not changed
	_, sp := fw.buildPaths(dir)
	var st frameworkStamp
	b, _ := os.ReadFile(sp)
	json.Unmarshal(b, &st)
	if st.Sha256 != fw.Sha256 || st.AuditExe == rtSha([]byte("evil-exe")) {
		t.Error("header touched")
	}
}
