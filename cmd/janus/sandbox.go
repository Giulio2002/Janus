package main

// Sandboxing for every Lean process that elaborates or loads untrusted code (the proof, the
// consumer package's modules and its Lake configuration). See docs/AUDIT.md F1 and the threat
// model in docs/CONSUMERS.md.
//
// A proof file, a lakefile.lean and any elaborator they import are arbitrary code that runs
// with the verifier's privileges while Lean elaborates them (#eval, run_cmd, initialize,
// macros, …). The sandbox confines that code:
//
//   - no network;
//   - the whole filesystem is read-only — including the Janus framework sources, the
//     ~/.cache/janus build and the janus binary — except a fresh private work directory;
//   - a private /tmp and a new session, PID, IPC, UTS and user namespace.
//
// bubblewrap (bwrap) is preferred. Without it, an unshare-based fallback provides the same
// confinement through a mount namespace: no network, every mount read-only, private tmpfs
// /tmp and /dev/shm (see unshareScript); if a mount cannot be made read-only the fallback is
// refused. With neither, verification
// refuses unless --unsafe-no-sandbox is passed, and the mode is recorded in verified.json.

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

type sandbox struct {
	mode  string // "bwrap", "unshare", or "none"
	bwrap string // path to bwrap, for "bwrap"
	// ctx, when set, ends the sandboxed commands built from this value (their outermost process
	// is killed, and the sandbox with it) once it is cancelled; see auditserve.go.
	ctx context.Context
}

// withContext is a copy of s whose commands are killed when ctx ends.
func (s *sandbox) withContext(ctx context.Context) *sandbox {
	c := *s
	c.ctx = ctx
	return &c
}

func (s *sandbox) newCmd(name string, arg ...string) *exec.Cmd {
	if s.ctx != nil {
		return exec.CommandContext(s.ctx, name, arg...)
	}
	return exec.Command(name, arg...)
}

type sandboxInfo struct {
	Mode string `json:"mode"` // "bwrap", "unshare", or "none"
	Tool string `json:"tool,omitempty"`
}

func (s *sandbox) info() sandboxInfo {
	si := sandboxInfo{Mode: s.mode}
	if s.mode == "bwrap" {
		si.Tool = s.bwrap
	}
	return si
}

// sandboxDiag explains how to get a sandbox, or how to opt out.
func sandboxDiag(detail string) error {
	return &diag{Invalid: true, Stage: "sandbox",
		Msg: "No sandbox is available to confine the untrusted proof/consumer code: " + detail,
		Next: "Install bubblewrap (apt-get install -y bubblewrap), or ensure unprivileged user namespaces are enabled " +
			"(sysctl kernel.unprivileged_userns_clone=1), or rerun with --unsafe-no-sandbox if you fully trust the proof, lakefile and every module it imports."}
}

// detectSandbox picks the strongest available sandbox. With unsafeNoSandbox the caller has
// accepted running untrusted Lean unconfined.
func detectSandbox(unsafeNoSandbox bool) (*sandbox, error) {
	if unsafeNoSandbox {
		return &sandbox{mode: "none"}, nil
	}
	// JANUS_SANDBOX=unshare forces the fallback (for testing it on hosts with bubblewrap);
	// JANUS_SANDBOX=bwrap forbids it.
	force := os.Getenv("JANUS_SANDBOX")
	if force != "" && force != "bwrap" && force != "unshare" {
		return nil, sandboxDiag(fmt.Sprintf("JANUS_SANDBOX=%q is neither bwrap nor unshare", force))
	}
	if p, err := exec.LookPath("bwrap"); err == nil && force != "unshare" {
		s := &sandbox{mode: "bwrap", bwrap: p}
		if err := s.selfTest(); err == nil {
			return s, nil
		}
	}
	var unshareErr error
	if _, err := exec.LookPath("unshare"); err == nil && force != "bwrap" {
		s := &sandbox{mode: "unshare"}
		if unshareErr = s.selfTest(); unshareErr == nil {
			return s, nil
		}
	}
	if unshareErr != nil && force == "unshare" {
		return nil, sandboxDiag("the unshare fallback cannot confine the build (" + unshareErr.Error() +
			")" + unshareTmpHint() + "; it requires every mount to be remountable read-only. Install bubblewrap")
	}
	// A last attempt to make bwrap available, documented as a requirement.
	if tryInstallBwrap() {
		if p, err := exec.LookPath("bwrap"); err == nil {
			s := &sandbox{mode: "bwrap", bwrap: p}
			if err := s.selfTest(); err == nil {
				return s, nil
			}
		}
	}
	if unshareErr != nil {
		return nil, sandboxDiag("bwrap is not installed and the unshare fallback cannot confine the build (" +
			unshareErr.Error() + ")" + unshareTmpHint() + "; install bubblewrap")
	}
	return nil, sandboxDiag("bwrap is not installed and no usable unprivileged user namespace is available")
}

// unshareTmpHint explains the one cause of an unshare refusal that is the user's to fix: the unshare fallback mounts a private
// tmpfs over /tmp, /dev/shm and /run, so a cache or verdict store living there cannot be bound back and the sandbox REFUSES
// (fail-closed: nothing runs unconfined). It returns "" when no such directory is configured.
func unshareTmpHint() string {
	var bad []string
	for _, p := range append([]string{cacheRoot()}, privateStoreDirs()...) {
		if p == "" {
			continue
		}
		p = filepath.Clean(p)
		for _, pre := range []string{"/tmp", "/dev/shm", "/run"} {
			if p == pre || strings.HasPrefix(p, pre+"/") {
				bad = append(bad, p)
			}
		}
	}
	if len(bad) == 0 {
		return ""
	}
	return "; the cache or verdict store " + strings.Join(bad, ", ") + " is under /tmp, /dev/shm or /run, which the unshare fallback hides behind a private tmpfs, so it refuses (fail-closed): move JANUS_CACHE_DIR / JANUS_VERDICT_CACHE / JANUS_FRAMEWORK_STORE elsewhere"
}

// tryInstallBwrap installs bubblewrap with apt when running as root non-interactively. It is a
// convenience; failure is not fatal (detectSandbox then falls back or refuses).
func tryInstallBwrap() bool {
	if os.Geteuid() != 0 {
		return false
	}
	apt, err := exec.LookPath("apt-get")
	if err != nil {
		return false
	}
	env := append(os.Environ(), "DEBIAN_FRONTEND=noninteractive")
	cmd := exec.Command(apt, "install", "-y", "--no-install-recommends", "bubblewrap")
	cmd.Env = env
	if err := cmd.Run(); err != nil {
		upd := exec.Command(apt, "update")
		upd.Env = env
		_ = upd.Run()
		cmd = exec.Command(apt, "install", "-y", "--no-install-recommends", "bubblewrap")
		cmd.Env = env
		if err := cmd.Run(); err != nil {
			return false
		}
	}
	return true
}

// selfTest confirms the sandbox can run a trivial command with the filesystem read-only. The
// probe directory sits under the run base (not /tmp, which the sandbox replaces with a private
// tmpfs), and the "denied" path is in that base — on the real, read-only filesystem.
func (s *sandbox) selfTest() error {
	base, err := janusRunBase()
	if err != nil {
		return err
	}
	tmp, err := os.MkdirTemp(base, "sbx-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(tmp)
	probe := filepath.Join(tmp, "probe")
	if err := os.MkdirAll(probe, 0o700); err != nil {
		return err
	}
	// Subshells so a redirection failure (expected for the read-only path) cannot make the
	// outer shell exit, which dash does for its special built-ins.
	// /tmp and /dev/shm must be private: a file written there must not appear on the host.
	name := "janus-sbx-" + newNonce()
	var private []string
	for _, d := range []string{"/tmp", "/dev/shm"} {
		if st, err := os.Stat(d); err == nil && st.IsDir() {
			private = append(private, filepath.Join(d, name))
		}
	}
	script := "(echo x > " + shQuote(filepath.Join(probe, "ok")) + ") 2>/dev/null; " +
		"if (echo x > /usr/janus-sbx-denied) 2>/dev/null; then echo LEAK; fi; "
	for _, p := range private {
		script += "(echo x > " + shQuote(p) + ") 2>/dev/null; "
	}
	// Hermetic root (UP4): the result cache, the key files and the home cache must not exist inside.
	for _, h := range hermeticProbePaths(tmp) {
		script += "if [ -e " + shQuote(h) + " ]; then echo HOSTVISIBLE " + shQuote(h) + "; fi; "
	}
	script += "echo DONE"
	cmd := s.command(probe, nil, []string{"/bin/sh", "-c", script}, os.Environ())
	out, err := cmd.CombinedOutput()
	for _, p := range private {
		if _, serr := os.Lstat(p); serr == nil {
			_ = os.Remove(p)
			return fmt.Errorf("the sandbox does not have a private %s", filepath.Dir(p))
		}
	}
	if err != nil {
		return fmt.Errorf("%v: %s", err, strings.TrimSpace(string(out)))
	}
	if !strings.Contains(string(out), "DONE") {
		return fmt.Errorf("the sandbox did not run the probe: %s", strings.TrimSpace(string(out)))
	}
	if i := strings.Index(string(out), "HOSTVISIBLE"); i >= 0 {
		return fmt.Errorf("the sandbox is not hermetic: %s", strings.TrimSpace(strings.SplitN(string(out)[i:], "\n", 2)[0]))
	}
	if strings.Contains(string(out), "LEAK") {
		return fmt.Errorf("the sandbox did not make the filesystem read-only")
	}
	if _, err := os.Stat(filepath.Join(probe, "ok")); err != nil {
		return fmt.Errorf("the sandbox could not write the work directory")
	}
	return nil
}

// janusRunBase is the directory under which trusted/work/sandbox dirs are created. It must not
// be /tmp, because the sandbox mounts a private tmpfs over /tmp (which would hide these dirs);
// it lives under the cache, which the sandbox exposes read-only and selectively re-binds.
func janusRunBase() (string, error) {
	base := filepath.Join(cacheRoot(), "v1", "run")
	if err := os.MkdirAll(base, 0o755); err != nil {
		return "", err
	}
	return base, nil
}

// command builds the sandboxed exec.Cmd: argv runs with the given env and cwd workDir, with
// workDir (and any extra dirs) writable and everything else read-only, no network.
func (s *sandbox) command(workDir string, extraWritable []string, argv []string, env []string) *exec.Cmd {
	return s.commandRO(workDir, extraWritable, nil, argv, env)
}

// commandRO is command with additional host directories exposed read-only (bubblewrap's
// private /tmp would otherwise hide those under /tmp).
func (s *sandbox) commandRO(workDir string, extraWritable, readOnly []string, argv []string, env []string) *exec.Cmd {
	return s.commandOverlay(workDir, extraWritable, readOnly, nil, argv, env)
}

// commandOverlay is commandRO with protected directories re-mounted read-only on top of the
// writable ones (mounted last, so they win): the trusted framework build inside a consumer
// workspace stays read-only to the untrusted Lake build that runs in that workspace. A
// mount point cannot be renamed or removed from inside the sandbox, so the protected tree
// cannot be swapped out either. In mode "none" nothing is enforced; the olean pins still are.
func (s *sandbox) commandOverlay(workDir string, extraWritable, readOnly, protected []string, argv []string, env []string) *exec.Cmd {
	writable := append([]string{workDir}, extraWritable...)
	switch s.mode {
	case "bwrap":
		// HERMETIC (UP4): the sandbox starts from an EMPTY root and gets an allowlist of read-only
		// binds (see hermeticSystemBwrap): the system runtime, the toolchain / LEAN_PATH /
		// protected trees the caller names, the work directories, a private /tmp, /dev and /proc.
		// $HOME, ~/.cache, every cache or key directory, /srv, /root and the rest of /etc do not exist
		// inside, so proof code can neither read the HMAC keys nor behave differently because of a
		// host file. The environment is allowlisted too (hermeticEnv): no tokens, no HOME.
		a := []string{"--unshare-all", "--die-with-parent", "--new-session", "--cap-drop", "ALL", "--clearenv"}
		a = append(a, hermeticSystemBwrap()...)
		a = append(a, "--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp")
		for _, e := range hermeticEnv(env) {
			k, v, _ := strings.Cut(e, "=")
			a = append(a, "--setenv", k, v)
		}
		ro := append([]string{}, readOnly...)
		if len(argv) > 0 && filepath.IsAbs(argv[0]) {
			ro = append(ro, filepath.Dir(argv[0]))
		}
	ro:
		for _, r := range ro {
			for _, w := range writable {
				if r == w || strings.HasPrefix(r, w+string(filepath.Separator)) {
					continue ro // stays writable, as before
				}
			}
			if _, err := os.Stat(r); err == nil {
				a = append(a, "--ro-bind", r, r)
			}
		}
		for _, w := range writable {
			a = append(a, "--bind", w, w)
		}
		for _, p := range protected {
			a = append(a, "--ro-bind", p, p)
		}
		// The root tmpfs itself (only mount points and symlinks live in it) becomes read-only.
		a = append(a, "--remount-ro", "/", "--chdir", workDir, "--")
		a = append(a, argv...)
		cmd := s.newCmd(s.bwrap, a...)
		cmd.Env = os.Environ() // bwrap's own environment; the job's is set with --setenv
		return cmd
	case "unshare":
		ro := append([]string{}, readOnly...)
		if len(argv) > 0 && filepath.IsAbs(argv[0]) {
			ro = append(ro, filepath.Dir(argv[0]))
		}
		args := []string{"-Umrnipf", "--map-root-user", "--mount-proc", "--",
			"/bin/sh", "-c", unshareScript(workDir, writable, ro, protected), "janus-sandbox"}
		// The outer process keeps the caller's environment (the memory guard's systemd-run needs the user bus
		// variables); the proof gets only the allowlisted one, through env -i inside the new root.
		args = append(args, "/usr/bin/env", "-i")
		args = append(args, hermeticEnv(env)...)
		args = append(args, argv...)
		cmd := s.newCmd("unshare", args...)
		cmd.Env = env
		return cmd
	default: // "none"
		cmd := s.newCmd(argv[0], argv[1:]...)
		cmd.Dir = workDir
		cmd.Env = env
		return cmd
	}
}

// unshareRefusedStatus is the exit status of the unshare sandbox script when it cannot build the
// hermetic root or make a mount read-only; the self-test then refuses the fallback.
const unshareRefusedStatus = 97

// unshareNewRoot picks the directory on which the unshare fallback mounts the tmpfs that becomes the
// new root: an existing host directory that contains none of the paths to be bound. "" if none fits.
func unshareNewRoot(paths []string) string {
	for _, c := range []string{"/mnt", "/media", "/opt", "/boot", "/home", "/srv", "/var/tmp"} {
		if st, err := os.Stat(c); err != nil || !st.IsDir() {
			continue
		}
		ok := true
		for _, p := range paths {
			p = filepath.Clean(p)
			if p == c || strings.HasPrefix(p, c+"/") || strings.HasPrefix(c, p+"/") {
				ok = false
			}
		}
		if ok {
			return c
		}
	}
	return ""
}

// unshareScript is the setup script of the unshare fallback, run as root of a new user, mount,
// network, PID, IPC and UTS namespace. It builds the SAME hermetic root as the bwrap mode (UP4):
//
//  1. a fresh tmpfs becomes the new root; the system runtime (hermeticSystemPaths, hermeticEtc), the
//     extra read-only dirs, the writable dirs and the protected trees are bound into it (each bind
//     remounted read-only unless writable, keeping the mount's locked flags), plus /dev nodes, a
//     proc mount, a private /tmp and /dev/shm. Nothing else of the host is bound;
//  2. pivot_root makes it the root and the old root is detached, so no host path (home, caches,
//     key directories, /srv, /run sockets) is reachable any more;
//  3. the proof runs with an empty capability set and no way to get one back (RT 9: no umount of
//     a mask, no remount). Without setpriv or pivot_root the fallback is refused.
//
// Any failure aborts with status 97 (fail-closed). $@ carries argv, so its elements need no quoting.
func unshareScript(workDir string, writable, readOnly, protected []string) string {
	var sb strings.Builder
	w := func(line string) { sb.WriteString(line + "\n") }
	all := append(append(append([]string{workDir}, writable...), readOnly...), protected...)
	nr := unshareNewRoot(all)
	w("set -e")
	w(fmt.Sprintf(`fail() { echo "janus-sandbox: $1" >&2; exit %d; }`, unshareRefusedStatus))
	w(`command -v setpriv >/dev/null 2>&1 || fail "setpriv is needed to drop the namespace capabilities"`)
	w(`command -v pivot_root >/dev/null 2>&1 || fail "pivot_root is needed to build the hermetic root"`)
	if nr == "" {
		w(`fail "no directory is available for the new root"`)
		return sb.String()
	}
	// The job's PATH is restored just before exec; the setup uses the system one.
	w(`JANUS_JOB_PATH=$PATH; PATH=/usr/sbin:/usr/bin:/sbin:/bin`)
	// remnt ro|rw TARGET MOUNTINFO-TARGET: change only the read-only flag of the mount at TARGET,
	// passing its other per-mount flags back (the last mountinfo entry for it is the visible one).
	w("remnt() {")
	w(`  o=""`)
	w(`  while read -r _ _ _ _ mp opts _; do [ "$mp" = "$3" ] && o=$opts; done < /proc/self/mountinfo`)
	w(`  o=$(printf '%s' "$o" | sed 's/^r[wo],\{0,1\}//; s/,r[wo]\(,\|$\)/\1/')`)
	w(`  mount -o "remount,bind,$1${o:+,$o}" "$2" "$2"`)
	w("}")
	w("mount --make-rprivate /")
	q := shQuote(nr)
	w("mount -t tmpfs -o mode=0755,nosuid,nodev tmpfs " + q)
	// bind P mode: a bind of the host path P at the same path in the new root.
	bind := func(p string, rw bool) {
		p = filepath.Clean(p)
		st, err := os.Stat(p)
		if err != nil {
			return
		}
		mode := "ro"
		if rw {
			mode = "rw"
		}
		dst := nr + p
		if st.IsDir() {
			w("mkdir -p " + shQuote(dst))
		} else {
			w("mkdir -p " + shQuote(filepath.Dir(dst)) + " && : > " + shQuote(dst))
		}
		w("mount --bind " + shQuote(p) + " " + shQuote(dst))
		w("remnt " + mode + " " + shQuote(dst) + " " + shQuote(mountinfoEscape(dst)))
	}
	for _, p := range hermeticSystemPaths {
		fi, err := os.Lstat(p)
		if err != nil {
			continue
		}
		if fi.Mode()&os.ModeSymlink != 0 {
			if t, err := os.Readlink(p); err == nil {
				w("ln -s " + shQuote(t) + " " + shQuote(nr+p))
			}
			continue
		}
		bind(p, false)
	}
	for _, m := range hermeticMasked {
		if st, err := os.Stat(m); err == nil && st.IsDir() {
			w("mount -t tmpfs -o mode=0755,nosuid,nodev tmpfs " + shQuote(nr+m))
		}
	}
	for _, e := range hermeticEtc {
		bind(e, false)
	}
	w("mkdir -p " + shQuote(nr+"/proc") + " " + shQuote(nr+"/dev") + " " + shQuote(nr+"/tmp") + " " + shQuote(nr+"/.old"))
	w("mount -t proc proc " + shQuote(nr+"/proc"))
	for _, d := range []string{"null", "zero", "full", "random", "urandom", "tty"} {
		if _, err := os.Stat("/dev/" + d); err == nil {
			w(": > " + shQuote(nr+"/dev/"+d) + " && mount --bind /dev/" + d + " " + shQuote(nr+"/dev/"+d))
		}
	}
	w("ln -s /proc/self/fd " + shQuote(nr+"/dev/fd") + "; ln -s /proc/self/fd/0 " + shQuote(nr+"/dev/stdin") +
		"; ln -s /proc/self/fd/1 " + shQuote(nr+"/dev/stdout") + "; ln -s /proc/self/fd/2 " + shQuote(nr+"/dev/stderr"))
	w("mkdir -p " + shQuote(nr+"/dev/shm") + " && mount -t tmpfs -o mode=1777,nosuid,nodev tmpfs " + shQuote(nr+"/dev/shm"))
	w("mount -t tmpfs -o mode=1777,nosuid,nodev tmpfs " + shQuote(nr+"/tmp"))
	ro := append(append([]string{}, readOnly...), []string{}...)
ro:
	for _, r := range ro {
		for _, wr := range writable {
			if r == wr || strings.HasPrefix(r, wr+string(filepath.Separator)) {
				continue ro // stays writable, as with bwrap
			}
		}
		bind(r, false)
	}
	for _, wr := range writable {
		bind(wr, true)
	}
	for _, p := range protected {
		bind(p, false)
	}
	w("remnt ro " + q + " " + shQuote(mountinfoEscape(nr)))
	w("cd " + q)
	w("pivot_root . .old")
	w("cd /")
	w("umount -l /.old")
	w("cd " + shQuote(workDir))
	w(`PATH=$JANUS_JOB_PATH; unset JANUS_JOB_PATH`)
	w(`exec setpriv --bounding-set=-all --inh-caps=-all --ambient-caps=-all --no-new-privs "$@"`)
	return sb.String()
}

// mountinfoEscape encodes a path the way /proc/self/mountinfo prints it (octal escapes for
// space, tab, newline and backslash).
func mountinfoEscape(p string) string {
	return strings.NewReplacer(`\`, `\134`, " ", `\040`, "\t", `\011`, "\n", `\012`).Replace(p)
}

// hiddenKeyFiles are the HMAC key files of the build caches (scripts/lib/bcache.py: asl-cache.key in
// $JANUS_CACHE_KEY_DIR or the cache root). They are outside v1/result but inside the cache root that the
// sandbox exposes read-only, so a proof could read the key; they are covered by /dev/null.
func hiddenKeyFiles() []string {
	var out []string
	for _, d := range []string{os.Getenv("JANUS_CACHE_KEY_DIR"), cacheRoot()} {
		if d == "" {
			continue
		}
		p := filepath.Join(d, "asl-cache.key")
		if st, err := os.Lstat(p); err == nil && st.Mode().IsRegular() {
			out = append(out, filepath.Clean(p))
		}
	}
	return out
}

func shQuote(s string) string { return "'" + strings.ReplaceAll(s, "'", `'\''`) + "'" }

// hermeticSystemPaths are the host paths every sandboxed process may read (read-only): the system
// runtime (libc, the dynamic loader, /bin/sh, git, coreutils). /usr/local and /usr/src are not part
// of it; /etc contributes only hermeticEtc. A path that does not exist on the host is skipped.
var hermeticSystemPaths = []string{"/usr", "/bin", "/sbin", "/lib", "/lib32", "/lib64", "/libx32"}

// hermeticMasked are directories of hermeticSystemPaths that are covered by an empty tmpfs.
var hermeticMasked = []string{"/usr/local", "/usr/src"}

// hermeticEtc are the only /etc entries the sandbox sees: the dynamic loader's configuration and
// the passwd/group/nsswitch/localtime files libc consults.
var hermeticEtc = []string{"/etc/ld.so.cache", "/etc/ld.so.conf", "/etc/ld.so.conf.d", "/etc/alternatives",
	"/etc/passwd", "/etc/group", "/etc/nsswitch.conf", "/etc/localtime"}

// hermeticSystemBwrap is the bwrap argument list that builds the system part of the empty root.
func hermeticSystemBwrap() []string {
	var a []string
	for _, p := range hermeticSystemPaths {
		fi, err := os.Lstat(p)
		if err != nil {
			continue
		}
		if fi.Mode()&os.ModeSymlink != 0 {
			if t, err := os.Readlink(p); err == nil {
				a = append(a, "--symlink", t, p)
			}
			continue
		}
		a = append(a, "--ro-bind", p, p)
	}
	for _, m := range hermeticMasked {
		if st, err := os.Stat(m); err == nil && st.IsDir() {
			a = append(a, "--tmpfs", m)
		}
	}
	for _, e := range hermeticEtc {
		if _, err := os.Stat(e); err == nil {
			a = append(a, "--ro-bind", e, e)
		}
	}
	return a
}

// hermeticEnv is the allowlisted environment of a sandboxed process: PATH, the Lean/Lake/janus
// toolchain variables, the locale, and a HOME that is the private /tmp. Nothing else (tokens, the
// cache and key directories, user variables) crosses into the sandbox.
func hermeticEnv(env []string) []string {
	var out []string
	for _, e := range env {
		k, _, ok := strings.Cut(e, "=")
		if !ok {
			continue
		}
		switch {
		case k == "PATH":
			out = append(out, "PATH="+hermeticPath(strings.TrimPrefix(e, "PATH=")))
		case k == "JANUS_REAL_LAKE", strings.HasPrefix(k, "JANUS_LAKEGUARD_"), k == "LANG", k == "TZ", k == "TERM", k == "JANUS_LEAN_SYSROOT",
			strings.HasPrefix(k, "LEAN_"), strings.HasPrefix(k, "LAKE_"), strings.HasPrefix(k, "LC_"),
			strings.HasPrefix(k, "GIT_"):
			out = append(out, e)
		}
	}
	return append(out, "HOME=/tmp")
}

// hermeticProbePaths are host paths that must NOT exist inside the sandbox (the self-test fails if one
// does): the result cache and the key files, the user's cache and home, secrets in /etc. A path that is
// an ancestor of (or inside) the probe directory is skipped, as it legitimately appears there.
func hermeticProbePaths(probeDir string) []string {
	cands := []string{filepath.Join(cacheRoot(), "v1", "result"), filepath.Join(cacheRoot(), "asl-cache.key"),
		filepath.Join(cacheRoot(), "asl-cache-key"), "/etc/shadow", "/etc/ssh"}
	if h, err := os.UserHomeDir(); err == nil && h != "" {
		cands = append(cands, filepath.Join(h, ".cache"), filepath.Join(h, ".ssh"), filepath.Join(h, ".bashrc"))
	}
	var out []string
	for _, c := range cands {
		if _, err := os.Lstat(c); err != nil {
			continue
		}
		if c == probeDir || strings.HasPrefix(probeDir, c+"/") || strings.HasPrefix(c, probeDir+"/") {
			continue
		}
		out = append(out, c)
	}
	return out
}

// hermeticPath keeps of a PATH only the system directories, the toolchain's bin (".../toolchains/.../bin") and
// the lakeguard wrapper directory; no host-specific entry (~/.cargo/bin, ~/.local/bin, ...) crosses over.
func hermeticPath(p string) string {
	var keep []string
	seen := map[string]bool{}
	for _, d := range filepath.SplitList(p) {
		sys := d == "/usr/bin" || d == "/bin" || d == "/usr/sbin" || d == "/sbin"
		if (sys || strings.Contains(d, "/toolchains/") || strings.Contains(d, "lakeguard")) && !seen[d] {
			seen[d] = true
			keep = append(keep, d)
		}
	}
	for _, d := range []string{"/usr/bin", "/bin"} {
		if !seen[d] {
			keep = append(keep, d)
		}
	}
	return strings.Join(keep, string(os.PathListSeparator))
}
