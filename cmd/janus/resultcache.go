package main

// The trusted verification-result cache (docs/SOUNDNESS.md, "Verification-result cache").
//
// A successful `janus verify` of a single proof file is recorded under a key that covers every
// input the outcome depends on: the janus executable itself (all of its logic, and the embedded
// framework), the framework build (its sources' hash, the SHA-256 of every compiled framework
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
// The consumer-package path (--proof-root) does not use the cache.

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
func (in *resultInputs) key() string {
	exe := executableSha()
	if exe == "" {
		return ""
	}
	outAbs, _ := filepath.Abs(in.outdir)
	proofAbs, _ := filepath.Abs(in.proof)
	binAbs, _ := filepath.Abs(in.binPath)
	h := sha256.New()
	fmt.Fprintf(h, "janus-result-v1\nexe %s\n", exe)
	fmt.Fprintf(h, "framework %s %s %s\npins %s\nauditor %s\n", in.fw.Source, in.fw.Sha256, in.root, pinsDigest(in.fwPins.want), in.auditExeSha)
	fmt.Fprintf(h, "toolchain %q %s %s\nsandbox %s %s\n", in.tc.version, in.tc.lean, in.tc.leanchecker, in.sb.mode, in.sb.bwrap)
	fmt.Fprintf(h, "theorem %s\nreplay-fresh %q\nbinary-opt %q\n", in.thm, in.opts["replay-fresh"], in.opts["binary"])
	fmt.Fprintf(h, "outdir %s\nproof %s\nbinary %s %s\n", outAbs, proofAbs, binAbs, in.binarySha)
	fmt.Fprintf(h, "extracted %s\nidentity %s\nproof-src %s\n", sha256Hex(in.extracted), sha256Hex(in.identity), sha256Hex(in.proofSrc))
	return hex.EncodeToString(h.Sum(nil))
}

// resultCacheOK: like the replay cache, only with a sandbox and without --fresh.
func resultCacheOK(sb *sandbox, opts map[string]string) bool {
	return sb.mode != "none" && opts["fresh"] == "" && os.Getenv("JANUS_RESULT_CACHE") != "off"
}

// resultKey returns the per-cache HMAC key, creating it (32 random bytes, mode 0600) on first use.
func resultHMACKey() ([]byte, error) {
	dir := resultCacheDir()
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return nil, err
	}
	p := filepath.Join(dir, ".key")
	if b, err := os.ReadFile(p); err == nil && len(b) == 32 {
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
		if b, err := os.ReadFile(p); err == nil && len(b) == 32 {
			return b, nil
		}
		return nil, fmt.Errorf("cannot create the result cache key")
	}
	os.Remove(f.Name())
	return k, nil
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
	b, err := os.ReadFile(resultPath(key))
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
