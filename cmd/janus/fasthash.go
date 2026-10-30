package main

// Streaming SHA-256 of files with pooled buffers (J1). The integrity pins re-hash the whole
// framework build (~450 MB of module data) and the compiled auditor (~230 MB) several times per
// verification; reading each file whole (os.ReadFile) allocates and garbage-collects a buffer
// per file. The digest is the same SHA-256 of the same bytes, so pins, stamps and cache keys are
// unchanged.

import (
	"crypto/sha256"
	"encoding/hex"
	"io"
	"os"
	"sync"
)

var hashBufPool = sync.Pool{New: func() any { b := make([]byte, 1<<20); return &b }}

// fileSha256Hex is the SHA-256 (hex) of the file at path.
func fileSha256Hex(path string) (string, error) {
	f, err := os.Open(path)
	if err != nil {
		return "", err
	}
	defer f.Close()
	return readerSha256Hex(f)
}

func readerSha256Hex(r io.Reader) (string, error) {
	bp := hashBufPool.Get().(*[]byte)
	defer hashBufPool.Put(bp)
	h := sha256.New()
	if _, err := io.CopyBuffer(struct{ io.Writer }{h}, struct{ io.Reader }{r}, *bp); err != nil {
		return "", err
	}
	return hex.EncodeToString(h.Sum(nil)), nil
}
