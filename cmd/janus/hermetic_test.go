package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"syscall"
	"testing"
)

// UP4: the sandbox is HERMETIC. It starts from an empty root with an allowlist of read-only binds, so
// proof code cannot read the result-cache HMAC key (or anything of $HOME, ~/.cache, /srv, /etc, the
// environment) -- whether or not JANUS_CACHE_DIR points elsewhere -- and cannot behave differently
// because of a host file. Both the bwrap mode and the unshare fallback.

func hermeticModes(t *testing.T) []*sandbox {
	t.Helper()
	var out []*sandbox
	for _, m := range []string{"bwrap", "unshare"} {
		t.Setenv("JANUS_SANDBOX", m)
		sb, err := detectSandbox(false)
		if err != nil || sb.mode != m {
			t.Logf("skip %s: %v", m, err)
			continue
		}
		out = append(out, sb)
	}
	if len(out) == 0 {
		t.Skip("no sandbox available")
	}
	t.Setenv("JANUS_SANDBOX", "")
	return out
}

// plantHost makes a fake HOME with ~/.cache/janus/v1/result/.key, an asl key, a secret in /srv-like dir
// and returns paths; JANUS_CACHE_DIR points at a SEPARATE cache so the default-location case is covered.
type plantedHost struct{ home, key, aslKey, secretDir, secret, keyDirKey, cache string }

func plantHost(t *testing.T) plantedHost {
	t.Helper()
	base := t.TempDir()
	h := plantedHost{home: filepath.Join(base, "home")}
	h.cache = filepath.Join(base, "cache")
	def := filepath.Join(h.home, ".cache", "janus")
	h.key = filepath.Join(def, "v1", "result", ".key")
	h.aslKey = filepath.Join(def, "asl-cache.key")
	h.secretDir = filepath.Join(base, "srv")
	h.secret = filepath.Join(h.secretDir, "secret.txt")
	h.keyDirKey = filepath.Join(base, "keys", "asl-cache.key")
	for _, f := range []string{h.key, h.aslKey, h.secret, h.keyDirKey, filepath.Join(h.cache, "v1", "result", ".key")} {
		if err := os.MkdirAll(filepath.Dir(f), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(f, []byte("SECRETKEYBYTES"), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	t.Setenv("HOME", h.home)
	t.Setenv("XDG_CACHE_HOME", "")
	t.Setenv("JANUS_CACHE_DIR", h.cache)
	t.Setenv("JANUS_CACHE_KEY_DIR", filepath.Dir(h.keyDirKey))
	t.Setenv("JANUS_UP4_TOKEN", "tok-should-not-cross")
	return h
}

func runIn(t *testing.T, sb *sandbox, work string, ro []string, script string) string {
	t.Helper()
	cmd := sb.commandRO(work, nil, ro, []string{"/bin/sh", "-c", script}, append(os.Environ(), "LEAN_NUM_THREADS=3"))
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("%s sandbox: %v\n%s", sb.mode, err, out)
	}
	return string(out)
}

func TestHermeticSandboxHidesTheHost(t *testing.T) {
	for _, sb := range hermeticModes(t) {
		t.Run(sb.mode, func(t *testing.T) {
			h := plantHost(t)
			work := t.TempDir()
			ro := t.TempDir()
			if err := os.WriteFile(filepath.Join(ro, "ok.txt"), []byte("legit"), 0o644); err != nil {
				t.Fatal(err)
			}
			script := ""
			for _, p := range []string{h.key, h.aslKey, h.secret, h.keyDirKey, filepath.Join(h.cache, "v1", "result", ".key"),
				"/etc/shadow", "/root", h.home, "/srv", "/etc/hostname"} {
				script += "if cat " + shQuote(p) + " >/dev/null 2>&1 || [ -e " + shQuote(p) + " ]; then echo VISIBLE " + shQuote(p) + "; fi; "
			}
			script += "echo HOME=$HOME; echo TOK=${JANUS_UP4_TOKEN-unset}; echo KD=${JANUS_CACHE_KEY_DIR-unset}; echo LT=$LEAN_NUM_THREADS; " +
				"echo $(cat " + shQuote(filepath.Join(ro, "ok.txt")) + "); (echo x > " + shQuote(filepath.Join(ro, "w")) + ") 2>/dev/null && echo ROWRITE; " +
				"echo x > " + shQuote(filepath.Join(work, "w")) + " && echo WORKOK; echo x > /tmp/priv && echo TMPOK; /usr/bin/true && echo SYSOK"
			out := runIn(t, sb, work, []string{ro}, script)
			if strings.Contains(out, "VISIBLE") {
				t.Fatalf("host path visible in the sandbox:\n%s", out)
			}
			for _, want := range []string{"HOME=/tmp", "TOK=unset", "KD=unset", "LT=3", "legit", "WORKOK", "TMPOK", "SYSOK"} {
				if !strings.Contains(out, want) {
					t.Errorf("missing %q in:\n%s", want, out)
				}
			}
			if strings.Contains(out, "ROWRITE") {
				t.Errorf("read-only dir writable:\n%s", out)
			}
			if _, err := os.Stat("/tmp/priv"); err == nil {
				os.Remove("/tmp/priv")
				t.Errorf("/tmp not private")
			}
		})
	}
}

// A proof that depends on a host file sees the same thing whether the file exists or not.
func TestHermeticSandboxIgnoresHostFiles(t *testing.T) {
	for _, sb := range hermeticModes(t) {
		t.Run(sb.mode, func(t *testing.T) {
			host := filepath.Join(t.TempDir(), "present-on-host")
			work := t.TempDir()
			script := "[ -e " + shQuote(host) + " ] && echo SEEN || echo ABSENT; ls / | tr '\\n' ' '; ls /etc | tr '\\n' ' '"
			before := runIn(t, sb, work, nil, script)
			if err := os.WriteFile(host, []byte("x"), 0o644); err != nil {
				t.Fatal(err)
			}
			after := runIn(t, sb, work, nil, script)
			if before != after || !strings.HasPrefix(after, "ABSENT") {
				t.Fatalf("sandbox output depends on host files:\nbefore: %s\nafter:  %s", before, after)
			}
			if _, err := exec.LookPath("true"); err != nil {
				t.Skip()
			}
		})
	}
}

// A descriptor the caller leaves open without CLOEXEC (heavy-run leaked a write fd to a lock file) must not reach
// the sandboxed process: it cannot write through /proc/self/fd/N to a host file.
func TestHermeticSandboxDoesNotInheritCallerFDs(t *testing.T) {
	for _, sb := range hermeticModes(t) {
		t.Run(sb.mode, func(t *testing.T) {
			host := filepath.Join(t.TempDir(), "leaked.lock")
			fd, err := syscall.Open(host, syscall.O_WRONLY|syscall.O_CREAT, 0o600) // no O_CLOEXEC
			if err != nil {
				t.Fatal(err)
			}
			defer syscall.Close(fd)
			work := t.TempDir()
			script := "ls /proc/self/fd | tr '\\n' ' '; echo; for f in /proc/self/fd/*; do case $(readlink $f) in *leaked.lock*) echo LEAKED $f; echo pwned > $f;; esac; done; " +
				"(echo pwned > /proc/self/fd/" + strconv.Itoa(fd) + ") 2>/dev/null && echo WROTE-FD; echo done"
			out := runIn(t, sb, work, nil, script)
			if strings.Contains(out, "LEAKED") || strings.Contains(out, "WROTE-FD") {
				t.Fatalf("caller fd %d reached the sandbox:\n%s", fd, out)
			}
			if b, _ := os.ReadFile(host); len(b) != 0 {
				t.Fatalf("host file written through a leaked fd: %q", b)
			}
		})
	}
}
