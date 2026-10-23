//go:build unix

package main

import (
	"os"
	"syscall"
)

// fileLock is an advisory lock on a file next to a cache directory.
type fileLock struct{ f *os.File }

func lockFile(path string, block bool) (*fileLock, error) {
	f, err := os.OpenFile(path, os.O_CREATE|os.O_RDWR, 0o644)
	if err != nil {
		return nil, err
	}
	how := syscall.LOCK_EX
	if !block {
		how |= syscall.LOCK_NB
	}
	if err := syscall.Flock(int(f.Fd()), how); err != nil {
		f.Close()
		return nil, err
	}
	return &fileLock{f}, nil
}

func (l *fileLock) unlock() {
	if l != nil && l.f != nil {
		_ = syscall.Flock(int(l.f.Fd()), syscall.LOCK_UN)
		l.f.Close()
		l.f = nil
	}
}
