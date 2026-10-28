package main

// RT 9: a malicious proof runs inside the Lean sandbox. It must be unable to read the HMAC key, read or write
// the incr records, the result cache or the rest of the cache, in both sandbox modes.

import (
	"bytes"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestRT09SandboxedProofCannotReachTheCaches(t *testing.T) {
	for _, mode := range []string{"bwrap", "unshare"} {
		t.Run(mode, func(t *testing.T) {
			x := newIncrFx(t)
			x.pass()
			x.wantSkip()
			var sb *sandbox
			switch mode {
			case "bwrap":
				p, err := exec.LookPath("bwrap")
				if err != nil {
					t.Skip("no bwrap")
				}
				sb = &sandbox{mode: "bwrap", bwrap: p}
			default:
				if _, err := exec.LookPath("unshare"); err != nil {
					t.Skip("no unshare")
				}
				sb = &sandbox{mode: "unshare"}
			}
			if err := sb.selfTest(); err != nil {
				t.Skipf("%s unavailable here: %v", mode, err)
			}
			base, _ := janusRunBase()
			ws, err := os.MkdirTemp(base, "rt9-")
			if err != nil {
				t.Fatal(err)
			}
			defer os.RemoveAll(ws)
			key := x.key()
			rec := incrPath(key)
			keyFile := filepath.Join(resultCacheDir(), ".key")
			hk, _ := os.ReadFile(keyFile)
			recBefore, _ := os.ReadFile(rec)
			root := cacheRoot()
			// what a hostile proof (or a lakefile) would try, each step reported
			forged := filepath.Join(filepath.Dir(rec), strings.Repeat("e", 64)+".json")
			rd := shQuote(resultCacheDir())
			script := strings.Join([]string{
				"[ \"$(cat " + shQuote(keyFile) + " 2>/dev/null | wc -c)\" -ge 32 ] && echo READ_KEY",
				"[ -s " + shQuote(rec) + " ] && echo READ_RECORD",
				// writes land on the empty tmpfs that hides the directory; they must not reach the host (checked below)
				"echo pwn > " + shQuote(rec) + " 2>/dev/null",
				"echo pwn > " + shQuote(forged) + " 2>/dev/null",
				"rm -f " + shQuote(rec) + " 2>/dev/null",
				"mv " + rd + " " + rd + ".x 2>/dev/null",
				"echo pwn > " + shQuote(filepath.Join(root, "v1", "pwn")) + " 2>/dev/null",
				// peel off the mask, or remount the cache writable, and look again
				"umount " + rd + " 2>/dev/null; [ \"$(cat " + shQuote(keyFile) + " 2>/dev/null | wc -c)\" -ge 32 ] && echo READ_KEY_AFTER_UMOUNT",
				"mount -o remount,rw,bind " + shQuote(root) + " " + shQuote(root) + " 2>/dev/null; echo pwn > " + shQuote(filepath.Join(root, "v1", "pwn2")) + " 2>/dev/null",
				"true",
			}, "\n")
			out, _ := sb.command(ws, nil, []string{"/bin/sh", "-c", script}, os.Environ()).CombinedOutput()
			for _, bad := range []string{"READ_KEY", "READ_RECORD", "READ_KEY_AFTER_UMOUNT"} {
				if bytes.Contains(out, []byte(bad)) {
					t.Errorf("%s: sandboxed code achieved %s\n%s", mode, bad, out)
				}
			}
			if _, err := os.Lstat(resultCacheDir() + ".x"); err == nil {
				t.Errorf("%s: the result directory was moved on the host", mode)
			}
			if _, err := os.Lstat(filepath.Join(root, "v1", "pwn2")); err == nil {
				t.Errorf("%s: the cache was remounted writable", mode)
			}
			if bytes.Contains(out, hk) && len(hk) > 0 {
				t.Errorf("%s: the HMAC key bytes reached the sandboxed process's output", mode)
			}
			// on the host nothing changed: record, key, no new file, and the item is still a plain SKIP
			if got, _ := os.ReadFile(rec); !bytes.Equal(got, recBefore) {
				t.Errorf("%s: the record changed", mode)
			}
			if got, _ := os.ReadFile(keyFile); !bytes.Equal(got, hk) {
				t.Errorf("%s: the key changed", mode)
			}
			if _, err := os.Lstat(forged); err == nil {
				t.Errorf("%s: a forged record file exists on the host", mode)
			}
			if _, err := os.Lstat(filepath.Join(root, "v1", "pwn")); err == nil {
				t.Errorf("%s: a file was created in the cache", mode)
			}
			x.wantSkip()
		})
	}
}

// The incr cache lives under the result directory that sandboxes hide; this pins that placement, since a
// move of it to another directory would silently make it visible to sandboxed code.
func TestRT09IncrDirIsUnderTheHiddenResultDir(t *testing.T) {
	newIncrFx(t)
	if rel, err := filepath.Rel(resultCacheDir(), incrDir()); err != nil || strings.HasPrefix(rel, "..") {
		t.Fatalf("incrDir %s is outside resultCacheDir %s", incrDir(), resultCacheDir())
	}
}

// The build-cache (ASL/Sail) HMAC key lives in the cache root, which sandboxes expose read-only: it must be
// covered, in both modes.
func TestRT09BuildCacheKeyIsHiddenFromTheSandbox(t *testing.T) {
	for _, mode := range []string{"bwrap", "unshare"} {
		t.Run(mode, func(t *testing.T) {
			newIncrFx(t)
			kf := filepath.Join(cacheRoot(), "asl-cache.key")
			if err := os.WriteFile(kf, bytes.Repeat([]byte{0x5a}, 32), 0o600); err != nil {
				t.Fatal(err)
			}
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
			ws, _ := os.MkdirTemp(base, "rt9k-")
			defer os.RemoveAll(ws)
			out, _ := sb.command(ws, nil, []string{"/bin/sh", "-c", "cat " + shQuote(kf) + " 2>/dev/null | od -An -c | head -2; echo END"}, os.Environ()).CombinedOutput()
			if strings.Contains(string(out), "Z") {
				t.Errorf("%s: the build-cache HMAC key is readable from the sandbox: %q", mode, out)
			}
		})
	}
}
