//go:build linux || darwin || freebsd

package main

import "syscall"

// fsInfo describes the filesystem holding the cache: its size and free space in bytes (size 0
// if unknown), and whether it is backed by RAM (tmpfs, ramfs).
type fsInfo struct {
	size, avail int64
	ram         bool
}

// statFS is the fsInfo of the filesystem holding p.
func statFS(p string) fsInfo {
	var st syscall.Statfs_t
	if err := syscall.Statfs(p, &st); err != nil {
		return fsInfo{avail: -1}
	}
	bs := int64(st.Bsize)
	return fsInfo{size: int64(st.Blocks) * bs, avail: int64(st.Bavail) * bs, ram: isRAMFS(int64(st.Type))}
}

// isRAMFS reports a tmpfs or ramfs magic number (Linux statfs f_type).
func isRAMFS(t int64) bool { return t == 0x01021994 || t == 0x858458f6 }
