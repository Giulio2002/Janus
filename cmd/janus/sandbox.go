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
// network and read-only-root confinement through a mount namespace. With neither, verification
// refuses unless --unsafe-no-sandbox is passed, and the mode is recorded in verified.json.

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

type sandbox struct {
	mode  string // "bwrap", "unshare", or "none"
	bwrap string // path to bwrap, for "bwrap"
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
	if p, err := exec.LookPath("bwrap"); err == nil {
		s := &sandbox{mode: "bwrap", bwrap: p}
		if err := s.selfTest(); err == nil {
			return s, nil
		}
	}
	if _, err := exec.LookPath("unshare"); err == nil {
		s := &sandbox{mode: "unshare"}
		if err := s.selfTest(); err == nil {
			return s, nil
		}
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
	script := "(echo x > " + shQuote(filepath.Join(probe, "ok")) + ") 2>/dev/null; " +
		"if (echo x > " + shQuote(filepath.Join(tmp, "denied")) + ") 2>/dev/null; then echo LEAK; fi; echo DONE"
	cmd := s.command(probe, nil, []string{"/bin/sh", "-c", script}, os.Environ())
	out, err := cmd.CombinedOutput()
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
		a = append(a, "--chdir", workDir, "--")
		a = append(a, argv...)
		cmd := exec.Command(s.bwrap, a...)
		cmd.Env = env
		return cmd
	case "unshare":
		// New user+mount+net+pid+ipc+uts namespaces; remount / read-only, then re-expose the
		// writable dirs rw, and exec argv. $@ carries argv so no quoting of its elements.
		var sb strings.Builder
		sb.WriteString("set -e\n")
		sb.WriteString("mount --make-rprivate / 2>/dev/null || true\n")
		sb.WriteString("mount -o remount,ro,bind / / 2>/dev/null || mount -o remount,ro / /\n")
		for _, w := range writable {
			q := shQuote(w)
			sb.WriteString("mount --bind " + q + " " + q + " 2>/dev/null || true\n")
			sb.WriteString("mount -o remount,rw,bind " + q + " " + q + " 2>/dev/null || true\n")
		}
		for _, p := range protected {
			// Protected trees must end up read-only: no "|| true" (set -e aborts otherwise).
			q := shQuote(p)
			sb.WriteString("mount --bind " + q + " " + q + "\n")
			sb.WriteString("mount -o remount,ro,bind " + q + " " + q + "\n")
		}
		sb.WriteString("cd " + shQuote(workDir) + "\n")
		sb.WriteString(`exec "$@"` + "\n")
		args := []string{"-Umrnipf", "--map-root-user", "--mount-proc", "--",
			"/bin/sh", "-c", sb.String(), "janus-sandbox"}
		args = append(args, argv...)
		cmd := exec.Command("unshare", args...)
		cmd.Env = env
		return cmd
	default: // "none"
		cmd := exec.Command(argv[0], argv[1:]...)
		cmd.Dir = workDir
		cmd.Env = env
		return cmd
	}
}

func shQuote(s string) string { return "'" + strings.ReplaceAll(s, "'", `'\''`) + "'" }
