//go:build !unix

package main

import "os"

// fileLock falls back to an exclusive lock file on platforms without flock. A lock left
// behind by a killed process must be removed by hand.
type fileLock struct{ path string }

func lockFile(path string, block bool) (*fileLock, error) {
	for {
		f, err := os.OpenFile(path+".excl", os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0o644)
		if err == nil {
			f.Close()
			return &fileLock{path + ".excl"}, nil
		}
		if !block || !os.IsExist(err) {
			return nil, err
		}
		sleepBriefly()
	}
}

func (l *fileLock) unlock() {
	if l != nil && l.path != "" {
		os.Remove(l.path)
		l.path = ""
	}
}
