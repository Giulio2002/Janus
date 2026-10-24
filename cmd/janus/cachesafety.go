package main

// Round 8 (C1, C2): the cache directory must be private to the user running janus.
//
// The result cache, the trusted-compile and replay caches and the framework build are trusted
// state (docs/SOUNDNESS.md). Their protection against sandboxed code is that sandboxes see them
// read-only or not at all, and their authentication key (v1/result/.key) is hidden. Neither
// helps against another *user* who can write the directory: a cache root under a shared
// HOME or XDG_CACHE_HOME, or a JANUS_CACHE_DIR in a world-writable place that someone else
// created first, lets that user choose the HMAC key and forge any "Cached: Verified" report.
// So before the cache is used, janus requires that
//
//   - the cache root (after resolving symlinks) and every one of its directories janus uses
//     (v1, v1/result, ...) is a real directory owned by the current user and not writable by
//     group or others, and no directory below the root is a symbolic link;
//   - every ancestor of the root is owned by the user or by root, and is not writable by group
//     or others unless it has the sticky bit (as /tmp has: others cannot rename our entries);
//   - the HMAC key is a regular file owned by the user, of mode 0600 or stricter, not a link.
//
// Cache files are opened with O_NOFOLLOW, so a symbolic link planted inside the cache is never
// followed.

import (
	"fmt"
	"io"
	"os"
	"path/filepath"
	"syscall"
)

// cacheSubdirs are the directories under the cache root janus creates and trusts.
var cacheSubdirs = []string{"v1", "v1/result", "v1/trusted", "v1/replay", "v1/framework", "v1/consumer", "v1/tmp", "v1/run"}

func ownerOf(fi os.FileInfo) (uint32, bool) {
	st, ok := fi.Sys().(*syscall.Stat_t)
	if !ok {
		return 0, false
	}
	return st.Uid, true
}

// checkCacheRoot verifies that the cache root is private (see the file comment), creating it
// (mode 0700) if it does not exist. The error is a diagnostic.
func checkCacheRoot() error {
	root := cacheRoot()
	bad := func(msg string) error {
		return &diag{Invalid: true, Stage: "cache safety",
			Msg:  fmt.Sprintf("The Janus cache %s is not private to this user: %s, so another user could plant trusted results or builds in it (round 8 C1).", displayPath(root), msg),
			Next: "Set JANUS_CACHE_DIR to a directory only you can write (for example mkdir -m 700 ~/.cache/janus-private), or fix the ownership and permissions."}
	}
	if _, err := os.Lstat(root); os.IsNotExist(err) {
		if err := os.MkdirAll(root, 0o700); err != nil {
			return &diag{Invalid: true, Stage: "cache safety", Msg: "Cannot create the Janus cache: " + err.Error(),
				Next: "Set JANUS_CACHE_DIR to a writable directory."}
		}
	}
	real, err := filepath.EvalSymlinks(root)
	if err != nil {
		return bad(err.Error())
	}
	uid := uint32(os.Geteuid())
	owned := func(p string, allowRoot bool) error {
		fi, err := os.Lstat(p)
		if err != nil {
			return bad(err.Error())
		}
		if fi.Mode()&os.ModeSymlink != 0 {
			return bad(displayPath(p) + " is a symbolic link")
		}
		if !fi.IsDir() {
			return bad(displayPath(p) + " is not a directory")
		}
		o, ok := ownerOf(fi)
		if !ok || (o != uid && !(allowRoot && o == 0)) {
			return bad(fmt.Sprintf("%s is owned by uid %d", displayPath(p), o))
		}
		return nil
	}
	if err := owned(real, false); err != nil {
		return err
	}
	if fi, _ := os.Lstat(real); fi.Mode().Perm()&0o022 != 0 {
		return bad(fmt.Sprintf("%s is writable by group or others (mode %o)", displayPath(real), fi.Mode().Perm()))
	}
	for a := filepath.Dir(real); ; a = filepath.Dir(a) {
		if err := owned(a, true); err != nil {
			return err
		}
		fi, _ := os.Lstat(a)
		if fi.Mode().Perm()&0o022 != 0 && fi.Mode()&os.ModeSticky == 0 {
			return bad(fmt.Sprintf("its parent %s is writable by group or others without the sticky bit (mode %o)", displayPath(a), fi.Mode().Perm()))
		}
		if a == filepath.Dir(a) {
			break
		}
	}
	for _, sub := range cacheSubdirs {
		p := filepath.Join(real, sub)
		fi, err := os.Lstat(p)
		if os.IsNotExist(err) {
			continue
		}
		if err := owned(p, false); err != nil {
			return err
		}
		if fi.Mode().Perm()&0o022 != 0 {
			return bad(fmt.Sprintf("%s is writable by group or others (mode %o)", displayPath(p), fi.Mode().Perm()))
		}
	}
	return nil
}

// readPrivateFile reads a regular file without following a final symbolic link, and returns an
// error unless it is owned by the current user and (with private) has no group or other
// permissions.
func readPrivateFile(p string, private bool) ([]byte, error) {
	f, err := os.OpenFile(p, os.O_RDONLY|syscall.O_NOFOLLOW, 0)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	fi, err := f.Stat()
	if err != nil {
		return nil, err
	}
	o, ok := ownerOf(fi)
	if !fi.Mode().IsRegular() || !ok || o != uint32(os.Geteuid()) || (private && fi.Mode().Perm()&0o077 != 0) {
		return nil, fmt.Errorf("%s is not a private regular file of this user", p)
	}
	return io.ReadAll(f)
}
