package main

// A gate-private store for framework replay verdicts (J1c).
//
// `--fresh` verifications bypass every cache, including the framework replay verdict, so a gate
// that runs dozens of them re-ran `leanchecker Janus` (390 s under load) for each. With
// JANUS_VERDICT_CACHE=<dir>, the framework verdict of a verification (read and recorded, also with
// --fresh) lives in that directory instead of the cache root. The verdict is exactly the one of the
// replay cache: an HMAC-authenticated marker named by the toolchain identity and the SHA-256 of
// every framework module-data file (the pins), so a framework build with any changed, added or
// removed module, or another toolchain, is another key and is replayed. The directory must be
// private to the user (mode 0700, not a link); its key (mode 0600) is created on first use. It is
// hidden from sandboxed processes like the result cache. `--fresh-framework` ignores the store: that
// verification replays the framework itself. Everything else `--fresh` bypasses stays bypassed.

import (
	"os"
	"path/filepath"
	"syscall"
)

// externalVerdictStore returns the store named by JANUS_VERDICT_CACHE (ok false when unset or
// disabled by --fresh-framework). An unsafe directory is an error, never a silent fallback.
func externalVerdictStore(opts map[string]string) (verdictStore, bool, error) {
	dir := os.Getenv("JANUS_VERDICT_CACHE")
	if dir == "" || opts["fresh-framework"] != "" {
		return verdictStore{}, false, nil
	}
	if !filepath.IsAbs(dir) {
		return verdictStore{}, false, keyDiag("JANUS_VERDICT_CACHE is not an absolute path")
	}
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return verdictStore{}, false, err
	}
	fi, err := os.Lstat(dir)
	if err != nil || !fi.IsDir() || fi.Mode().Perm()&0o077 != 0 {
		return verdictStore{}, false, keyDiag("the verdict store " + dir + " is not a private directory (mode 0700, not a link)")
	}
	if st, ok := fi.Sys().(*syscall.Stat_t); !ok || int(st.Uid) != os.Getuid() {
		return verdictStore{}, false, keyDiag("the verdict store " + dir + " is not owned by this user")
	}
	return verdictStore{replayDir: filepath.Join(dir, "replay"), keyFn: func() ([]byte, error) { return hmacKeyInDir(filepath.Join(dir, "key")) }}, true, nil
}

// verdictStoreDir is the directory sandboxed processes must not see ("" when none).
func verdictStoreDir() string {
	d := os.Getenv("JANUS_VERDICT_CACHE")
	if d == "" || !filepath.IsAbs(d) {
		return ""
	}
	return d
}
