package main

// RT: two `verify --asl` workspaces seeded from DIFFERENT gate trees at the same time (each tree's JanusASL/.lake is
// a symlink to one source checkout's build) end up with distinct, real, private .lake directories; neither writes the
// other's or the checkout's JanusASL/.lake, and no package-overrides.json appears in the checkout.

import (
	"bytes"
	"crypto/sha256"
	"fmt"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"sync"
	"testing"
)

func treeDigest(t *testing.T, dir string) string {
	t.Helper()
	var ls []string
	filepath.WalkDir(dir, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return nil
		}
		rel, _ := filepath.Rel(dir, p)
		if d.Type()&fs.ModeSymlink != 0 {
			tg, _ := os.Readlink(p)
			ls = append(ls, "L "+rel+" "+tg)
		} else if d.Type().IsRegular() {
			b, _ := os.ReadFile(p)
			ls = append(ls, fmt.Sprintf("F %s %x", rel, sha256.Sum256(b)))
		}
		return nil
	})
	sort.Strings(ls)
	return fmt.Sprint(ls)
}

func TestRTConcurrentASLWorkspacesDoNotShareALake(t *testing.T) {
	root, _ := filepath.Abs("../..")
	scratch := t.TempDir()
	src := filepath.Join(scratch, "checkout", "JanusASL", ".lake")
	wr(t, filepath.Join(src, "build/lib/lean/A.olean"), "a")
	wr(t, filepath.Join(src, "packages/Sail/x"), "s")
	before := treeDigest(t, filepath.Join(scratch, "checkout"))
	const n = 6
	var wg sync.WaitGroup
	ws := make([]string, n)
	errs := make([]error, n)
	for i := 0; i < n; i++ {
		tree := filepath.Join(scratch, fmt.Sprintf("tree%d", i), "JanusASL")
		os.MkdirAll(tree, 0o755)
		wr(t, filepath.Join(tree, "ArmASL", "Part01.lean"), "-- model\n") // the model sources the seed is pruned against
		if err := os.Symlink(src, filepath.Join(tree, ".lake")); err != nil { // the gate tree's shared symlink
			t.Fatal(err)
		}
		ws[i] = filepath.Join(scratch, fmt.Sprintf("ws%d", i))
		os.MkdirAll(ws[i], 0o755)
		// a workspace left over from the old bug: its .lake is a link into the checkout
		if i%2 == 0 {
			os.Symlink(src, filepath.Join(ws[i], ".lake"))
		}
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			// asl.sh do_verify's seeding, as shipped (sed out of the script), then what janus does in the workspace
			script := `set -e
d=` + shQuote(ws[i]) + `
pkg=` + shQuote(tree) + `
root=` + shQuote(root) + `
# the real seed_copy and seeding block of asl.sh; tl_run (the tree lock, tested by scripts/lib/test-treelock.sh) just runs
tl_run() { shift; "$@"; }
` + extractSeedFunc(t, root) + `
` + extractSeedBlock(t, root) + `
echo '{"janus":"tree` + fmt.Sprint(i) + `"}' > "$d/.lake/package-overrides.json"
echo mine > "$d/.lake/build/lib/lean/W` + fmt.Sprint(i) + `.olean"
`
			out, err := exec.Command("bash", "-c", script).CombinedOutput()
			if err != nil {
				errs[i] = fmt.Errorf("%v: %s", err, out)
			}
		}(i)
	}
	wg.Wait()
	for i := 0; i < n; i++ {
		if errs[i] != nil {
			t.Fatalf("workspace %d: %v", i, errs[i])
		}
		fi, err := os.Lstat(filepath.Join(ws[i], ".lake"))
		if err != nil || fi.Mode()&os.ModeSymlink != 0 || !fi.IsDir() {
			t.Fatalf("workspace %d: .lake is not a real directory (%v, %v)", i, fi, err)
		}
		b, _ := os.ReadFile(filepath.Join(ws[i], ".lake/package-overrides.json"))
		if !bytes.Contains(b, []byte(fmt.Sprintf("tree%d", i))) {
			t.Errorf("workspace %d: override is %q", i, b)
		}
		for j := 0; j < n; j++ {
			if j != i {
				if _, err := os.Stat(filepath.Join(ws[i], fmt.Sprintf(".lake/build/lib/lean/W%d.olean", j))); err == nil {
					t.Errorf("workspace %d holds workspace %d's olean", i, j)
				}
			}
		}
	}
	if after := treeDigest(t, filepath.Join(scratch, "checkout")); after != before {
		t.Fatalf("the source checkout's JanusASL/.lake changed:\nbefore %s\nafter  %s", before, after)
	}
	if _, err := os.Stat(filepath.Join(src, "package-overrides.json")); err == nil {
		t.Fatal("a package-overrides.json appeared in the source checkout")
	}
}

// extractSeedFunc returns the seed_copy function of scripts/asl.sh.
func extractSeedFunc(t *testing.T, root string) string {
	t.Helper()
	b, err := os.ReadFile(filepath.Join(root, "scripts", "asl.sh"))
	if err != nil {
		t.Fatal(err)
	}
	i := bytes.Index(b, []byte("seed_copy() {"))
	j := bytes.Index(b[i:], []byte("\n}\n"))
	if i < 0 || j < 0 {
		t.Fatal("cannot find seed_copy in scripts/asl.sh")
	}
	return string(b[i : i+j+3])
}

// extractSeedBlock returns the seeding lines of do_verify in scripts/asl.sh.
func extractSeedBlock(t *testing.T, root string) string {
	t.Helper()
	b, err := os.ReadFile(filepath.Join(root, "scripts", "asl.sh"))
	if err != nil {
		t.Fatal(err)
	}
	s := string(b)
	i := bytes.Index(b, []byte(`if [ -L "$d/.lake" ]`))
	j := bytes.Index(b[i:], []byte("  local fail=0 n"))
	if i < 0 || j < 0 {
		t.Fatal("cannot find the seeding block in scripts/asl.sh")
	}
	blk := s[i : i+j]
	return bytes.NewBufferString(replaceReturn(blk)).String()
}

func replaceReturn(s string) string {
	return string(bytes.ReplaceAll([]byte(s), []byte("return 1"), []byte("exit 1")))
}
