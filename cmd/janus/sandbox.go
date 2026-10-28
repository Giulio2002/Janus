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
			"); it requires every mount to be remountable read-only. Install bubblewrap")
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
			unshareErr.Error() + "); install bubblewrap")
	}
	return nil, sandboxDiag("bwrap is not installed and no usable unprivileged user namespace is available")
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
		"if (echo x > " + shQuote(filepath.Join(tmp, "denied")) + ") 2>/dev/null; then echo LEAK; fi; "
	for _, p := range private {
		script += "(echo x > " + shQuote(p) + ") 2>/dev/null; "
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
		a := []string{
			"--unshare-all", "--die-with-parent", "--new-session",
			"--ro-bind", "/", "/",
			"--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp",
		}
		// Round 3, S2: `--ro-bind / /` also binds the host's live runtime sockets under /run
		// (/run/docker.sock, the D-Bus system bus, containerd). A *read-only* bind does not stop
		// a process connecting to a unix socket, and unix sockets are not confined by the network
		// namespace, so untrusted proof code could reach a privileged daemon and escape. Overmount
		// /run (and thus /var/run, a symlink to it) with an empty tmpfs; the cache re-bind below
		// restores any janus dir that happens to live under /run.
		if _, err := os.Stat("/run"); err == nil {
			a = append(a, "--tmpfs", "/run")
		}
		// The private /tmp would hide any janus directory placed under /tmp (the cache can be
		// there, e.g. in tests), so re-expose the cache read-only; the writable binds below
		// then override the work dir. Source paths are resolved on the host.
		if base := cacheRoot(); base != "" {
			if _, err := os.Stat(base); err == nil {
				a = append(a, "--ro-bind", base, base)
			}
		}
	ro:
		for _, r := range readOnly {
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
		// The verification-result cache (entries and their HMAC key) is not even visible to
		// sandboxed code: an empty tmpfs covers it, mounted last (resultcache.go).
		if rc := resultCacheDir(); rc != "" {
			if st, err := os.Stat(rc); err == nil && st.IsDir() {
				a = append(a, "--tmpfs", rc)
			}
		}
		a = append(a, "--chdir", workDir, "--")
		a = append(a, argv...)
		cmd := s.newCmd(s.bwrap, a...)
		cmd.Env = env
		return cmd
	case "unshare":
		args := []string{"-Umrnipf", "--map-root-user", "--mount-proc", "--",
			"/bin/sh", "-c", unshareScript(workDir, writable, readOnly, protected), "janus-sandbox"}
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

// unshareRefusedStatus is the exit status of the unshare sandbox script when it cannot make a
// mount read-only; the self-test then refuses the fallback.
const unshareRefusedStatus = 97

// unshareScript is the setup script of the unshare fallback, run as root of a new user, mount,
// network, PID, IPC and UTS namespace (round 2, U1). It matches bubblewrap's confinement:
//
//  1. every mount visible in the namespace is remounted read-only (not only /: /boot,
//     /run/user/…, /dev and any other rw mount too), keeping each mount's locked
//     nosuid/nodev/noexec/atime flags, which a user namespace may not change. A mount that
//     cannot be made read-only aborts the script with status 97 and the fallback is refused;
//     mounts below /proc belong to the host procfs hidden by --mount-proc, and mount points
//     shadowed by a later mount are not reachable, so both are skipped;
//  2. /tmp and /dev/shm get private tmpfs mounts, so nothing written there reaches the host;
//  3. the cache (read-only), the extra read-only dirs, the writable dirs and the protected
//     trees are bound back in that order. Those under the host /tmp are bound from the hidden
//     original through the shell's working directory (`cd /tmp` before the tmpfs mount;
//     relative sources with --no-canonicalize resolve against it).
//
// $@ carries argv, so its elements need no quoting.
func unshareScript(workDir string, writable, readOnly, protected []string) string {
	var sb strings.Builder
	w := func(line string) { sb.WriteString(line + "\n") }
	w("set -e")
	// remnt ro|rw TARGET MOUNTINFO-TARGET: change only the read-only flag of the mount at
	// TARGET, passing its other per-mount flags back (the last mountinfo entry for it is the
	// visible one).
	w("remnt() {")
	w(`  o=""`)
	w(`  while read -r _ _ _ _ mp opts _; do [ "$mp" = "$3" ] && o=$opts; done < /proc/self/mountinfo`)
	w(`  o=$(printf '%s' "$o" | sed 's/^r[wo],\{0,1\}//; s/,r[wo]\(,\|$\)/\1/')`)
	w(`  mount -o "remount,bind,$1${o:+,$o}" "$2" "$2"`)
	w("}")
	w("mount --make-rprivate /")
	w("while read -r _ _ _ _ mp _; do")
	w(`  t=$(printf '%b' "$mp")`)
	w(`  case "$t" in /proc/*) continue ;; esac`)
	w(`  remnt ro "$t" "$mp" 2>/dev/null || {`)
	w(`    mountpoint -q "$t" 2>/dev/null || continue`)
	w(fmt.Sprintf(`    echo "janus-sandbox: cannot make the mount $t read-only" >&2; exit %d; }`, unshareRefusedStatus))
	w("done < /proc/self/mountinfo")
	w("if [ -d /tmp ]; then cd /tmp; mount -t tmpfs -o mode=1777,nosuid,nodev tmpfs /tmp; fi")
	w("if [ -d /dev/shm ]; then mount -t tmpfs -o mode=1777,nosuid,nodev tmpfs /dev/shm; fi")
	// Round 3, S2: overmount /run with an empty tmpfs so the host's live runtime sockets
	// (/run/docker.sock, the D-Bus system bus, containerd) are not reachable from untrusted
	// proof code (a read-only remount does not stop a connect() to a unix socket). Skip it only
	// when a path janus must bind back lives under /run, which the tmpfs would hide; those paths
	// are normally under the home cache, not /run.
	underRun := func(p string) bool {
		p = filepath.Clean(p)
		return p == "/run" || strings.HasPrefix(p, "/run/")
	}
	runSafe := !underRun(cacheRoot())
	for _, p := range append(append(append([]string{}, writable...), readOnly...), protected...) {
		if underRun(p) {
			runSafe = false
		}
	}
	if runSafe {
		w("if [ -d /run ]; then mount -t tmpfs -o mode=0755,nosuid,nodev tmpfs /run; fi")
	}
	// bind P (ro or rw); strict: failure aborts (set -e) instead of continuing.
	bind := func(p string, rw, strict bool) {
		p = filepath.Clean(p)
		st, err := os.Stat(p)
		if err != nil {
			return
		}
		mode := "ro"
		if rw {
			mode = "rw"
		}
		q := shQuote(p)
		tail := " 2>/dev/null || true"
		if strict {
			tail = ""
		}
		src := q
		if rel, ok := strings.CutPrefix(p, "/tmp/"); ok && rel != "" {
			// recreate the mount point in the private tmpfs and bind the original from
			// the hidden host /tmp (the working directory)
			if st.IsDir() {
				w("mkdir -p " + q + tail)
			} else {
				w("mkdir -p " + shQuote(filepath.Dir(p)) + " && : > " + q + tail)
			}
			src = shQuote("./" + rel)
		}
		w("mount --no-canonicalize --bind " + src + " " + q + tail)
		w("remnt " + mode + " " + q + " " + shQuote(mountinfoEscape(p)) + tail)
	}
	if base := cacheRoot(); base != "" {
		bind(base, false, false)
	}
ro:
	for _, r := range readOnly {
		for _, wr := range writable {
			if r == wr || strings.HasPrefix(r, wr+string(filepath.Separator)) {
				continue ro // stays writable, as with bwrap
			}
		}
		bind(r, false, false)
	}
	for _, wr := range writable {
		bind(wr, true, false)
	}
	for _, p := range protected {
		// Protected trees must end up read-only: no "|| true" (set -e aborts otherwise).
		bind(p, false, true)
	}
	// Hide the verification-result cache under an empty tmpfs, as bubblewrap does (strict: the
	// script stops if it cannot).
	if st, err := os.Stat(resultCacheDir()); err == nil && st.IsDir() {
		w("mount -t tmpfs -o mode=0700,nosuid,nodev tmpfs " + shQuote(filepath.Clean(resultCacheDir())))
	}
	w("cd " + shQuote(workDir))
	w(`exec "$@"`)
	return sb.String()
}

// mountinfoEscape encodes a path the way /proc/self/mountinfo prints it (octal escapes for
// space, tab, newline and backslash).
func mountinfoEscape(p string) string {
	return strings.NewReplacer(`\`, `\134`, " ", `\040`, "\t", `\011`, "\n", `\012`).Replace(p)
}

func shQuote(s string) string { return "'" + strings.ReplaceAll(s, "'", `'\''`) + "'" }
