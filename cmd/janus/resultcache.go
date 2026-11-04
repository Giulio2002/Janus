package main

// The trusted verification-result cache (docs/SOUNDNESS.md, "Verification-result cache").
//
// A successful `janus verify` of a single proof file is recorded under a key that covers every
// input the outcome depends on: the verifier (the janus executable's logic and embedded framework,
// named by a content identity of its source and build, or by the executable's bytes: verifierid.go),
// the framework build (its sources' hash, the SHA-256 of every compiled framework
// module and of the compiled auditor), the Lean toolchain, the sandbox mode, the selected theorem
// and options, the artifact (Extracted.lean, identity.json, the binary's verified SHA-256) and the
// proof's bytes. A later verification with exactly the same inputs prints the recorded report
// (plus a "Cached:" line) instead of compiling, auditing and replaying again.
//
// Why a hit is as trustworthy as a fresh run:
//   - the key is computed by the trusted process from bytes it reads itself, after the same
//     extraction integrity check (the binary's hash against identity.json) a fresh run starts
//     with, and after the framework build is confirmed ready (stamped sources, pins, auditor);
//   - entries are written only by a trusted janus process after a successful, sandboxed, non
//     --fresh verification, and every entry is authenticated with an HMAC-SHA256 under a random
//     per-cache key: a modified or forged entry is ignored (the verification runs);
//   - the result directory, key included, is invisible to every sandboxed process: the sandbox
//     mounts an empty tmpfs over it (bubblewrap and the unshare fallback), so neither a proof nor
//     a lakefile can read the key or write an entry;
//   - with --unsafe-no-sandbox or --fresh the cache is neither read nor written.
// The consumer-package path (--proof-root) uses the same cache with its own key
// (consumerResultInputs below); see the red-team checklist in docs/SOUNDNESS.md.

import (
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sync"
	"time"
)

// resultCacheDir holds the result entries and their HMAC key; sandboxes hide it (sandbox.go).
func resultCacheDir() string { return filepath.Join(cacheRoot(), "v1", "result") }

var (
	selfShaOnce sync.Once
	selfSha     string
)

// executableSha is the SHA-256 of the running janus executable ("" if it cannot be read, which
// disables the cache).
func executableSha() string {
	selfShaOnce.Do(func() {
		p, err := os.Executable()
		if err != nil {
			return
		}
		f, err := os.Open(p)
		if err != nil {
			return
		}
		defer f.Close()
		h := sha256.New()
		if _, err := io.Copy(h, f); err == nil {
			selfSha = hex.EncodeToString(h.Sum(nil))
		}
	})
	return selfSha
}

// resultInputs are the inputs of one single-file verification.
type resultInputs struct {
	fw                  *framework
	root                string
	fwPins              *pinnedLib
	auditExeSha         string
	tc                  *toolchain
	sb                  *sandbox
	thm, outdir, proof  string
	opts                map[string]string
	extracted, identity []byte
	binPath, binarySha  string
	proofSrc            []byte
}

// key is the SHA-256 of every input, or "" when the cache cannot be used.
//
// The verifier is named by its identity (verifierid.go): a content hash of the source it was built
// from and of the toolchain and settings, or, when that cannot be established exactly, the
// SHA-256 of the executable. Absolute paths (artifact directory, proof, binary, framework root)
// are not keyed, since they differ between checkouts of identical items: the key binds the
// extraction, identity and proof bytes, the binary's SHA-256, and the proof's and binary's path
// relative to the artifact directory, which is exactly what the recorded report contains
// (binaryRef), plus the framework's source hash, pins and auditor.
func (in *resultInputs) key() string {
	vid := verifierComponent()
	if vid == "" {
		return ""
	}
	h := sha256.New()
	fmt.Fprintf(h, "janus-result-v%d\nverifier %s\n", resultCacheSchema, vid)
	fmt.Fprintf(h, "framework %s %s\npins %s\nauditor %s\n", in.fw.Source, in.fw.Sha256, pinsDigest(in.fwPins.want), in.auditExeSha)
	fmt.Fprintf(h, "toolchain %q %s %s\nsandbox %s %s\n", in.tc.cacheID(), in.tc.lean, in.tc.leanchecker, in.sb.mode, in.sb.bwrap)
	fmt.Fprintf(h, "theorem %s\nreplay-fresh %q\n", in.thm, in.opts["replay-fresh"])
	fmt.Fprintf(h, "proof %q\nbinary %q %s\n", binaryRef(in.outdir, in.proof), binaryRef(in.outdir, in.binPath), in.binarySha)
	fmt.Fprintf(h, "extracted %s\nidentity %s\nproof-src %s\n", sha256Hex(in.extracted), sha256Hex(in.identity), sha256Hex(in.proofSrc))
	return hex.EncodeToString(h.Sum(nil))
}

// resultCacheOK: like the replay cache, only with a sandbox and without --fresh.
func resultCacheOK(sb *sandbox, opts map[string]string) bool {
	// --asl results are not cached: the ASL stage runs (and is itself cached by its replay
	// cache) every time.
	return sb.mode != "none" && opts["fresh"] == "" && opts["asl"] == "" && opts["no-result-cache"] == "" && os.Getenv("JANUS_RESULT_CACHE") != "off"
}

// resultKey returns the per-cache HMAC key, creating it (32 random bytes, mode 0600) on first use.
func resultHMACKey() ([]byte, error) {
	// round 8 C1: the key authenticates every entry (results and trusted compiles); it must be
	// ours alone. The root is checked before anything is created under it.
	if err := checkCacheRoot(); err != nil {
		return nil, err
	}
	return hmacKeyInDir(resultCacheDir())
}

// hmacKeyInDir is the key of the private directory dir (created 0700 with a 32-byte key of mode
// 0600 on first use). A directory or key that others can read or write is refused.
func hmacKeyInDir(dir string) ([]byte, error) {
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return nil, err
	}
	if fi, err := os.Lstat(dir); err != nil || !fi.IsDir() || fi.Mode().Perm()&0o077 != 0 {
		mode := "missing"
		if err == nil {
			mode = fmt.Sprintf("mode %o", fi.Mode().Perm())
		}
		return nil, keyDiag(fmt.Sprintf("the result cache directory %s is not private to this user (%s; it must be a directory of mode 0700)", displayPath(dir), mode))
	}
	p := filepath.Join(dir, ".key")
	if fi, err := os.Lstat(p); err == nil {
		b, err := readPrivateFile(p, true)
		if err != nil || len(b) != 32 {
			why := "it is not a private regular file of this user"
			if fi.Mode()&os.ModeSymlink != 0 {
				why = "it is a symbolic link"
			} else if fi.Mode().IsRegular() && fi.Mode().Perm()&0o077 != 0 {
				why = fmt.Sprintf("its mode is %04o, readable or writable by group or others (it must be 0600)", fi.Mode().Perm())
			} else if err == nil {
				why = fmt.Sprintf("it has %d bytes, not 32", len(b))
			}
			return nil, keyDiag(fmt.Sprintf("the result cache key %s is unsafe: %s", displayPath(p), why))
		}
		return b, nil
	}
	k := make([]byte, 32)
	if _, err := rand.Read(k); err != nil {
		return nil, err
	}
	f, err := os.CreateTemp(dir, ".key.tmp-")
	if err != nil {
		return nil, err
	}
	_ = f.Chmod(0o600)
	if _, err := f.Write(k); err != nil {
		f.Close()
		os.Remove(f.Name())
		return nil, err
	}
	f.Close()
	// Another process may have created it meanwhile: keep the first one.
	if err := os.Link(f.Name(), p); err != nil {
		os.Remove(f.Name())
		if b, err := readPrivateFile(p, true); err == nil && len(b) == 32 {
			return b, nil
		}
		return nil, fmt.Errorf("cannot create the result cache key")
	}
	os.Remove(f.Name())
	return k, nil
}

// keyDiag reports an unsafe result-cache key (round 8 C1). Anyone who could read the key can
// forge cached results, so janus stops instead of silently ignoring the cache.
func keyDiag(msg string) error {
	return &diag{Invalid: true, Stage: "cache safety",
		Msg:  "The Janus cache is not safe to use: " + msg + ", so another user could have read it and forged cached results (round 8 C1).",
		Next: "Remove the result cache directory (janus creates a new private key) or set JANUS_CACHE_DIR to a directory only you can write."}
}

type resultEntry struct {
	Key    string          `json:"key"`
	Report json.RawMessage `json:"report"`
	MAC    string          `json:"mac"` // HMAC-SHA256(key || report) under the cache key
}

func resultMAC(hk []byte, key string, report []byte) string {
	m := hmac.New(sha256.New, hk)
	fmt.Fprintf(m, "janus-result-entry-v1\n%s\n", key)
	m.Write(report)
	return hex.EncodeToString(m.Sum(nil))
}

func resultPath(key string) string { return filepath.Join(resultCacheDir(), key[:2], key+".json") }

// lookupResult returns the recorded report for key, if there is an authentic entry.
func lookupResult(key string) *verifiedReport {
	if key == "" {
		return nil
	}
	b, err := readPrivateFile(resultPath(key), false)
	if err != nil {
		return nil
	}
	hk, err := resultHMACKey()
	if err != nil {
		return nil
	}
	var e resultEntry
	if json.Unmarshal(b, &e) != nil || e.Key != key {
		return nil
	}
	if !hmac.Equal([]byte(e.MAC), []byte(resultMAC(hk, key, e.Report))) {
		return nil
	}
	var r verifiedReport
	if json.Unmarshal(e.Report, &r) != nil {
		return nil
	}
	touchHit(resultPath(key))
	return &r
}

// storeResult records a successful verification under key (atomically; errors are ignored: the
// cache is an optimisation).
func storeResult(key string, r *verifiedReport) {
	if key == "" {
		return
	}
	hk, err := resultHMACKey()
	if err != nil {
		return
	}
	rep, err := json.Marshal(r)
	if err != nil {
		return
	}
	b, _ := json.Marshal(resultEntry{Key: key, Report: rep, MAC: resultMAC(hk, key, rep)})
	p := resultPath(key)
	if os.MkdirAll(filepath.Dir(p), 0o700) != nil {
		return
	}
	_ = writeFileAtomic(p, b)
}

// cachedReport turns a recorded report into this run's: the time and the framework's revision
// (a checkout's commit) are this run's, and it is marked as a cache hit.
func cachedReport(r *verifiedReport, fw *framework, root string) *verifiedReport {
	c := *r
	c.CachedFrom = r.Timestamp
	c.Cached = true
	c.Timestamp = time.Now().UTC().Format(time.RFC3339)
	fi := fw.info()
	c.Framework = fi
	c.JanusRoot = root
	c.JanusCommit = fi.Revision
	if fi.Modified {
		c.JanusCommit += "+dirty"
	}
	return &c
}

// consumerResultInputs are the inputs of one consumer-package (--proof-root) verification of one
// theorem. The key covers everything the verdict and the recorded report depend on: the verifier,
// the framework build (sources, every compiled module, the auditor), the Lean toolchain and Lake
// executable, the sandbox, the theorem and the options that change the verdict, the whole
// consumer package snapshot (every Lean/TOML/JSON/toolchain file, hence the lakefile and the
// manifest), every other Lake dependency as copied (tree hash and pin), the proof's place in the
// package, and the artifact (Extracted.lean, identity.json, the binary's verified SHA-256 and its
// place relative to the artifact directory).
type consumerResultInputs struct {
	fw          *framework
	fwPins      *pinnedLib
	auditExeSha string
	tc          *toolchain
	lakeSha     string
	sb          *sandbox
	thm         string
	opts        map[string]string
	pkg         *consumerPkg
	req         *consumerRequest
}

// key is the SHA-256 of every input, or "" when the cache cannot be used.
func (in *consumerResultInputs) key() string {
	vid := verifierComponent()
	if vid == "" || in.lakeSha == "" || in.auditExeSha == "" || in.fwPins == nil || len(in.fwPins.want) == 0 {
		return ""
	}
	r := in.req
	if !lakefileCacheable(in.pkg.Files, in.pkg.Lakefile) {
		return ""
	}
	for _, d := range in.pkg.Deps {
		if !lakefileCacheable(d.Files, d.Config) {
			return ""
		}
	}
	h := sha256.New()
	fmt.Fprintf(h, "janus-consumer-result-v2 schema %d\nverifier %s\n", resultCacheSchema, vid)
	fmt.Fprintf(h, "framework %s %s\npins %s\nauditor %s\n", in.fw.Source, in.fw.Sha256, pinsDigest(in.fwPins.want), in.auditExeSha)
	fmt.Fprintf(h, "toolchain %q %s %s\nlake %s\nsandbox %s %s\n", in.tc.cacheID(), in.tc.lean, in.tc.leanchecker, in.lakeSha, in.sb.mode, in.sb.bwrap)
	fmt.Fprintf(h, "theorem %s\nreplay-fresh %q\nallow-path-deps %q\n", in.thm, in.opts["replay-fresh"], in.opts["allow-path-deps"])
	fmt.Fprintf(h, "package %s\nproof-rel %q\n", in.pkg.Sha256, r.rel)
	dep, _ := json.Marshal(in.pkg.Dep)
	deps, _ := json.Marshal(in.pkg.depInfos())
	fmt.Fprintf(h, "janus-dep %s\ndeps %s\n", dep, deps)
	fmt.Fprintf(h, "binary %q %s\n", binaryRef(r.Outdir, r.cr.BinPath), r.cr.Identity.BinarySha256)
	idBytes, _ := os.ReadFile(filepath.Join(r.Outdir, "identity.json"))
	fmt.Fprintf(h, "extracted %s\nidentity %s\nproof-src %s\n", sha256Hex(r.cr.Lean), sha256Hex(idBytes), sha256Hex(r.proofSrc))
	return hex.EncodeToString(h.Sum(nil))
}
