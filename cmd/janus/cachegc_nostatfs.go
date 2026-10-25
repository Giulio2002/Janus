//go:build !linux && !darwin && !freebsd

package main

type fsInfo struct {
	size, avail int64
	ram         bool
}

func statFS(p string) fsInfo { return fsInfo{avail: -1} }
