//go:build unix

package main

import (
	"os"
	"syscall"
)

// fileLock is an advisory lock on a file next to a cache directory.
type fileLock struct{ f *os.File }

// lockFile takes an exclusive lock on path (created if missing).
func lockFile(path string, block bool) (*fileLock, error) { return lockFileMode(path, false, block) }

// lockFileMode takes a shared (readers) or exclusive (writers) flock on path. A lock file can
// be removed by its holder (the cache collector, cachegc.go, deletes an entry together with its
// lock file), so after the lock is granted the path must still name the locked inode; otherwise
// the lock is on an unlinked file nobody else will ever see, and it is taken again on the new
// file.
func lockFileMode(path string, shared, block bool) (*fileLock, error) {
	for {
		f, err := os.OpenFile(path, os.O_CREATE|os.O_RDWR, 0o644)
		if err != nil {
			return nil, err
		}
		how := syscall.LOCK_EX
		if shared {
			how = syscall.LOCK_SH
		}
		if !block {
			how |= syscall.LOCK_NB
		}
		if err := syscall.Flock(int(f.Fd()), how); err != nil {
			f.Close()
			return nil, err
		}
		if sameFile(f, path) {
			return &fileLock{f}, nil
		}
		f.Close()
	}
}

func sameFile(f *os.File, path string) bool {
	a, err1 := f.Stat()
	b, err2 := os.Stat(path)
	return err1 == nil && err2 == nil && os.SameFile(a, b)
}

// share converts a held exclusive lock into a shared one. flock's conversion is not atomic (the
// old lock is dropped first), so a writer may run in between; callers re-validate afterwards.
func (l *fileLock) share() error { return syscall.Flock(int(l.f.Fd()), syscall.LOCK_SH) }

func (l *fileLock) unlock() {
	if l != nil && l.f != nil {
		_ = syscall.Flock(int(l.f.Fd()), syscall.LOCK_UN)
		l.f.Close()
		l.f = nil
	}
}
