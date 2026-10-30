#!/usr/bin/env python3
"""lockexec.py MODE LOCKFILE [+MODE:LOCKFILE ...] CMD ARGS...: take a flock on LOCKFILE (MODE x = exclusive, s =
shared), then on each extra +MODE:LOCKFILE in the order given (the lock order), and exec CMD holding them all. The lock file is created with O_NOFOLLOW and mode 0600 and must be a regular file owned by us
(a symlink, a directory, someone else's file or a hard-linked one is refused, exit 1), then locked by fd."""
import fcntl, os, stat, sys

mode, path, rest = sys.argv[1], sys.argv[2], sys.argv[3:]
locks = [(mode, path)]
while rest and rest[0].startswith("+") and ":" in rest[0]:
    m, _, pth = rest.pop(0)[1:].partition(":")
    locks.append((m, pth))
cmd = rest

def take(mode, path):
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
    except OSError as e:
        sys.exit("lanelake: cannot open the lock file %s: %s (a symlink is refused)" % (path, e.strerror))
    st = os.fstat(fd)
    if not stat.S_ISREG(st.st_mode) or st.st_uid != os.geteuid() or st.st_nlink != 1:
        sys.exit("lanelake: refusing %s: not a regular file of ours with one link" % path)
    fcntl.flock(fd, fcntl.LOCK_SH if mode == "s" else fcntl.LOCK_EX)
    os.set_inheritable(fd, True)

for m, pth in locks:
    take(m, pth)
os.execvp(cmd[0], cmd)
