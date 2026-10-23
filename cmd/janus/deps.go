package main

// Extra dependencies of consumer packages: Lake packages other than janus (a spec library,
// Mathlib and its own dependencies, …). See docs/CONSUMERS.md § Extra dependencies.
//
// Every one must be a git dependency pinned in lake-manifest.json to a full 40-hex revision and
// checked out at exactly that revision with no local modifications: HEAD equals the pin, `git
// status --porcelain` (ignoring the package's own .lake build directory) is empty, and every
// tracked file of the pinned tree hashes to its git blob id. Exactly those files are copied into
// the verification workspace, where Lake builds them under the sandbox like the consumer's own
// modules; their build outputs are untrusted (the kernel replay covers every dependency module
// the theorem imports). Path dependencies other than janus are rejected unless
// --allow-path-deps is given; then their source snapshot is copied and recorded as is.
//
// git runs with hooks, fsmonitor and the user's global/system configuration disabled, and under
// the sandbox when one is available, so a checkout cannot make the verifier run its code.

import (
	"bytes"
	"crypto/sha1"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io/fs"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
)

// extraDep is one non-janus dependency of a consumer package and the files that are copied
// into the workspace for it.
type extraDep struct {
	Info   dependencyInfo
	Files  map[string][]byte // slash path relative to the package directory -> bytes
	Config string            // lakefile.toml or lakefile.lean
	pkgDir string            // the package directory in the consumer's checkout
}

// loadOpts are the consumer-package options that affect which packages are accepted.
type loadOpts struct {
	AllowPathDeps bool
	SB            *sandbox // sandbox for git; nil runs git directly (hardened)
}

var depNameRE = regexp.MustCompile(`^[A-Za-z0-9_][A-Za-z0-9_.\-«»]*$`)

// Module roots that only the framework and the toolchain may provide.
var reservedModuleRoots = map[string]bool{"Init": true, "Std": true, "Lean": true, "Lake": true, "Janus": true, "Extracted": true, "JanusTrusted": true}

// loadExtraDep validates one manifest entry other than janus and snapshots its files.
func loadExtraDep(root, pkgsDir string, e lakeEntry, lo loadOpts) (*extraDep, error) {
	if !depNameRE.MatchString(e.Name) || e.Name == "janus" {
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("Unsupported dependency name %q in lake-manifest.json.", e.Name), "Rename the package.")
	}
	info := dependencyInfo{Name: e.Name, Type: e.Type, Inherited: e.Inherited}
	if e.SubDir != nil {
		info.SubDir = *e.SubDir
	}
	if e.InputRev != nil {
		info.InputRev = *e.InputRev
	}
	via := ""
	if e.Inherited {
		via = " (required by another dependency)"
	}
	switch e.Type {
	case "git":
		return loadGitDep(root, pkgsDir, e, info, via, lo)
	case "path":
		if !lo.AllowPathDeps {
			return nil, pkgDiag("consumer manifest",
				fmt.Sprintf("The package depends on %s%s through the local path %s; only janus may be a path dependency.", e.Name, via, e.Dir),
				fmt.Sprintf("Require %s from git, pinned to a full 40-hex revision (rev = \"<commit>\"), and run lake update %s; or pass --allow-path-deps to accept the local copy as it is (it is recorded as a path dependency).", e.Name, e.Name))
		}
		dir := filepath.FromSlash(e.Dir)
		if !filepath.IsAbs(dir) {
			dir = filepath.Join(root, dir)
		}
		dir = filepath.Clean(dir)
		if real, err := filepath.EvalSymlinks(dir); err == nil {
			dir = real
		}
		files, err := snapshotDir(dir, nil)
		if err != nil {
			if d, ok := err.(*diag); ok {
				d.Msg = fmt.Sprintf("Path dependency %s: %s", e.Name, d.Msg)
				return nil, d
			}
			return nil, pkgDiag("consumer manifest", fmt.Sprintf("Cannot read the path dependency %s at %s: %v", e.Name, displayPath(dir), err),
				"Run lake update in "+displayPath(root)+".")
		}
		info.Dir = dir
		d := &extraDep{Info: info, Files: files, pkgDir: dir}
		return d, d.finish(root)
	default:
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("Unsupported dependency type %q for %s.", e.Type, e.Name), "Require it from git, pinned to a full revision.")
	}
}

func loadGitDep(root, pkgsDir string, e lakeEntry, info dependencyInfo, via string, lo loadOpts) (*extraDep, error) {
	info.URL, info.Rev = e.URL, e.Rev
	pinNext := fmt.Sprintf("Require %s with rev = \"<40-hex commit>\" (for example the commit lake-manifest.json resolved, %s) and run lake update %s.", e.Name, e.Rev, e.Name)
	if !fullRevRE.MatchString(e.Rev) {
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("%s%s is not pinned to a full revision in lake-manifest.json (rev %q).", e.Name, via, e.Rev), pinNext)
	}
	// A direct dependency must be asked for by full revision in the lakefile, so lake update
	// cannot move it; a dependency's own requirements are pinned by the manifest's rev.
	if !e.Inherited && info.InputRev != e.Rev {
		asked := info.InputRev
		if asked == "" {
			asked = "(no revision)"
		}
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("%s is not pinned to a full revision: the lakefile asks for %s.", e.Name, asked), pinNext)
	}
	if info.SubDir != "" {
		sd := path.Clean(filepath.ToSlash(info.SubDir))
		if path.IsAbs(sd) || sd == ".." || strings.HasPrefix(sd, "../") {
			return nil, pkgDiag("consumer manifest", fmt.Sprintf("%s has an invalid subDir %q.", e.Name, info.SubDir), "Fix the requirement.")
		}
		if sd == "." {
			sd = ""
		}
		info.SubDir = sd
	}
	checkout := filepath.Join(root, filepath.FromSlash(pkgsDir), e.Name)
	info.Dir = checkout
	update := "Run lake update " + e.Name + " in " + displayPath(root) + "."
	if _, err := os.Stat(checkout); err != nil {
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("The dependency %s is not checked out at %s.", e.Name, displayPath(checkout)), update)
	}
	if _, err := os.Lstat(filepath.Join(checkout, ".git")); err != nil {
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("The dependency %s at %s is not a git checkout, so its revision cannot be confirmed.", e.Name, displayPath(checkout)), update)
	}
	if err := checkGitState(checkout, e.Name, e.Rev, lo.SB); err != nil {
		return nil, err
	}
	files, err := gitTrackedFiles(checkout, e.Name, e.Rev, info.SubDir, lo.SB)
	if err != nil {
		return nil, err
	}
	pkgDir := checkout
	if info.SubDir != "" {
		pkgDir = filepath.Join(checkout, filepath.FromSlash(info.SubDir))
	}
	d := &extraDep{Info: info, Files: files, pkgDir: pkgDir}
	return d, d.finish(root)
}

// finish records the snapshot hash and the Lake configuration file.
func (d *extraDep) finish(root string) error {
	d.Info.Sha256 = treeSha(d.Files)
	d.Info.Files = len(d.Files)
	_, toml := d.Files["lakefile.toml"]
	_, lean := d.Files["lakefile.lean"]
	switch {
	case toml && lean:
		return pkgDiag("consumer manifest", fmt.Sprintf("The dependency %s has both lakefile.toml and lakefile.lean.", d.Info.Name), "Use a revision with one Lake configuration file.")
	case toml:
		d.Config = "lakefile.toml"
	case lean:
		d.Config = "lakefile.lean"
	default:
		return pkgDiag("consumer manifest", fmt.Sprintf("The dependency %s (%s) has no lakefile.toml or lakefile.lean.", d.Info.Name, displayPath(d.pkgDir)),
			"Run lake update in "+displayPath(root)+".")
	}
	return nil
}

// gitRun runs git on dir with hooks, fsmonitor and global/system configuration disabled, under
// the sandbox when there is one (read-only filesystem, no network).
func gitRun(sb *sandbox, dir string, args ...string) (string, error) {
	gitBin, err := exec.LookPath("git")
	if err != nil {
		return "", fmt.Errorf("git is not installed")
	}
	argv := append([]string{gitBin, "-c", "core.fsmonitor=false", "-c", "core.hooksPath=/dev/null", "-c", "safe.directory=*",
		"-c", "core.untrackedCache=false", "-c", "core.autocrlf=false", "-C", dir}, args...)
	var env []string
	for _, e := range os.Environ() {
		if !strings.HasPrefix(e, "GIT_") {
			env = append(env, e)
		}
	}
	env = append(env, "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL=/dev/null", "GIT_OPTIONAL_LOCKS=0", "GIT_TERMINAL_PROMPT=0")
	var cmd *exec.Cmd
	if sb == nil || sb.mode == "none" {
		cmd = exec.Command(argv[0], argv[1:]...)
		cmd.Env = env
	} else {
		base, err := janusRunBase()
		if err != nil {
			return "", err
		}
		tmp, err := os.MkdirTemp(base, "git-")
		if err != nil {
			return "", err
		}
		defer os.RemoveAll(tmp)
		cmd = sb.commandRO(tmp, nil, []string{dir}, argv, env)
	}
	var out, errb bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &errb
	if err := cmd.Run(); err != nil {
		return out.String(), fmt.Errorf("git %s: %v: %s", strings.Join(args, " "), err, strings.TrimSpace(errb.String()))
	}
	return out.String(), nil
}

// checkGitState confirms the checkout is at rev with no local modifications: HEAD is rev and
// git status is empty apart from the package's own .lake directory.
func checkGitState(checkout, name, rev string, sb *sandbox) error {
	update := "Run lake update " + name + " (or git -C " + displayPath(checkout) + " checkout " + rev + ")."
	head, err := gitRun(sb, checkout, "rev-parse", "HEAD")
	if err != nil {
		return pkgDiag("consumer manifest", fmt.Sprintf("Cannot read the revision of the dependency %s at %s: %v", name, displayPath(checkout), err), update)
	}
	if h := strings.TrimSpace(head); h != rev {
		return pkgDiag("consumer manifest", fmt.Sprintf("The dependency %s at %s is at %s, lake-manifest.json pins %s.", name, displayPath(checkout), h, rev), update)
	}
	st, err := gitRun(sb, checkout, "status", "--porcelain=v1", "-z", "--untracked-files=normal", "--ignore-submodules=none")
	if err != nil {
		return pkgDiag("consumer manifest", fmt.Sprintf("Cannot read the status of the dependency %s at %s: %v", name, displayPath(checkout), err), update)
	}
	var dirty []string
	for _, ent := range strings.Split(st, "\x00") {
		if len(ent) < 4 {
			continue
		}
		p := ent[3:]
		if p == ".lake" || p == ".lake/" || strings.HasPrefix(p, ".lake/") {
			continue
		}
		dirty = append(dirty, strings.TrimSpace(ent[:2])+" "+p)
	}
	if len(dirty) > 0 {
		shown := dirty
		if len(shown) > 8 {
			shown = append(append([]string{}, shown[:8]...), fmt.Sprintf("… and %d more", len(dirty)-8))
		}
		return pkgDiag("consumer manifest", fmt.Sprintf("The dependency %s at %s has local modifications:\n  %s", name, displayPath(checkout), strings.Join(shown, "\n  ")),
			"Discard them (git -C "+displayPath(checkout)+" checkout -- . && git -C "+displayPath(checkout)+" clean -fd), or commit them to a repository and pin that commit.")
	}
	return nil
}

// gitTrackedFiles reads every regular file of rev's tree under subDir from the working tree and
// checks it hashes to its git blob id, so the copy is exactly the pinned revision.
func gitTrackedFiles(checkout, name, rev, subDir string, sb *sandbox) (map[string][]byte, error) {
	ls, err := gitRun(sb, checkout, "ls-tree", "-r", "-z", "--full-tree", rev)
	if err != nil {
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("Cannot list the files of %s at %s: %v", name, rev, err), "Run lake update "+name+".")
	}
	files := map[string][]byte{}
	var changed []string
	prefix := ""
	if subDir != "" {
		prefix = subDir + "/"
	}
	for _, ent := range strings.Split(ls, "\x00") {
		if ent == "" {
			continue
		}
		tab := strings.IndexByte(ent, '\t')
		if tab < 0 {
			continue
		}
		meta, p := strings.Fields(ent[:tab]), ent[tab+1:]
		if len(meta) != 3 || !strings.HasPrefix(p, prefix) {
			continue
		}
		mode, typ, id := meta[0], meta[1], meta[2]
		rel := strings.TrimPrefix(p, prefix)
		if typ != "blob" {
			continue // a submodule: not part of the package's sources
		}
		if mode == "120000" {
			if isSourceFile(path.Base(rel)) {
				return nil, pkgDiag("consumer manifest", fmt.Sprintf("The dependency %s tracks %s as a symbolic link; dependency sources must be regular files.", name, p), "Use a revision without symlinked sources.")
			}
			continue
		}
		b, err := os.ReadFile(filepath.Join(checkout, filepath.FromSlash(p)))
		if err != nil || gitBlobID(b, len(id)) != id {
			changed = append(changed, p)
			continue
		}
		files[rel] = b
	}
	if len(changed) > 0 {
		sort.Strings(changed)
		shown := changed
		if len(shown) > 8 {
			shown = append(append([]string{}, shown[:8]...), fmt.Sprintf("… and %d more", len(changed)-8))
		}
		return nil, pkgDiag("consumer manifest", fmt.Sprintf("The checkout of %s at %s differs from its pinned revision %s:\n  %s", name, displayPath(checkout), rev, strings.Join(shown, "\n  ")),
			"Restore it (git -C "+displayPath(checkout)+" checkout "+rev+" -- .) or run lake update "+name+".")
	}
	return files, nil
}

// gitBlobID is the git object id of a blob with content b (SHA-1, or SHA-256 for 64-hex ids).
func gitBlobID(b []byte, idLen int) string {
	hdr := "blob " + strconv.Itoa(len(b)) + "\x00"
	if idLen == 64 {
		h := sha256.New()
		h.Write([]byte(hdr))
		h.Write(b)
		return hex.EncodeToString(h.Sum(nil))
	}
	h := sha1.New()
	h.Write([]byte(hdr))
	h.Write(b)
	return hex.EncodeToString(h.Sum(nil))
}

// recheck confirms after verification that the dependency is still the one that was copied.
func (d *extraDep) recheck(sb *sandbox) error {
	if d.Info.Type == "git" {
		if err := checkGitState(d.Info.Dir, d.Info.Name, d.Info.Rev, sb); err != nil {
			return err
		}
		return nil
	}
	files, err := snapshotDir(d.pkgDir, nil)
	if err != nil || treeSha(files) != d.Info.Sha256 {
		return pkgDiag("stale input", fmt.Sprintf("The path dependency %s changed during verification.", d.Info.Name), "Rerun janus verify.")
	}
	return nil
}

// oleanModules lists the modules compiled into a Lake lib directory (relative .olean paths).
func oleanModules(libDir string) []string {
	var mods []string
	_ = filepath.WalkDir(libDir, func(p string, de fs.DirEntry, err error) error {
		if err != nil || de.IsDir() || !strings.HasSuffix(p, ".olean") {
			return nil
		}
		rel, err := filepath.Rel(libDir, p)
		if err != nil {
			return nil
		}
		mods = append(mods, strings.ReplaceAll(strings.TrimSuffix(filepath.ToSlash(rel), ".olean"), "/", "."))
		return nil
	})
	sort.Strings(mods)
	return mods
}

func moduleRoot(m string) string {
	if i := strings.IndexByte(m, '.'); i >= 0 {
		return m[:i]
	}
	return m
}

// checkModuleLayout is the module-identity check for a consumer workspace after the build:
// the framework library holds only framework modules (plus Extracted and JanusTrusted); the
// consumer and its dependencies define no module with a reserved root (Init, Std, Lean, Lake,
// Janus, Extracted, JanusTrusted) and no module name twice; and no module root is shared between
// the consumer and a dependency, so the auditor's per-root classification is exact. It returns
// the module roots of the dependencies.
func checkModuleLayout(janusLib string, janusFiles map[string][]byte, consumerLib string, depLibs map[string]string, toolchainLib string) ([]string, error) {
	bad := func(msg string) error {
		return &diag{Invalid: true, Stage: "module identity", Msg: msg,
			Next: "Rename the module; dependency and consumer modules may not use the framework's or the toolchain's module names."}
	}
	for _, m := range oleanModules(janusLib) {
		if m == "Extracted" || m == "JanusTrusted" {
			continue
		}
		if _, ok := janusFiles[strings.ReplaceAll(m, ".", "/")+".lean"]; !ok {
			return nil, bad(fmt.Sprintf("the framework build directory contains %s.olean, which is not a framework module.", m))
		}
	}
	owner := map[string]string{} // module -> who provides it
	for _, m := range oleanModules(toolchainLib) {
		owner[m] = "the Lean toolchain"
	}
	for _, m := range oleanModules(janusLib) {
		owner[m] = "the Janus framework"
	}
	type lib struct{ who, dir string }
	libs := []lib{{"the consumer package", consumerLib}}
	var names []string
	for n := range depLibs {
		names = append(names, n)
	}
	sort.Strings(names)
	for _, n := range names {
		libs = append(libs, lib{"the dependency " + n, depLibs[n]})
	}
	rootsOf := map[string]map[string]bool{}
	for _, l := range libs {
		rootsOf[l.who] = map[string]bool{}
		for _, m := range oleanModules(l.dir) {
			if reservedModuleRoots[moduleRoot(m)] {
				return nil, bad(fmt.Sprintf("%s defines the module %s, whose root %s is reserved for the framework and the toolchain.", l.who, m, moduleRoot(m)))
			}
			if o, ok := owner[m]; ok {
				return nil, bad(fmt.Sprintf("the module %s is provided by both %s and %s.", m, o, l.who))
			}
			owner[m] = l.who
			rootsOf[l.who][moduleRoot(m)] = true
		}
	}
	depRoots := map[string]bool{}
	for _, l := range libs[1:] {
		for r := range rootsOf[l.who] {
			if rootsOf["the consumer package"][r] {
				return nil, bad(fmt.Sprintf("the module root %s is used by both the consumer package and %s.", r, l.who))
			}
			depRoots[r] = true
		}
	}
	var out []string
	for r := range depRoots {
		out = append(out, r)
	}
	sort.Strings(out)
	return out, nil
}
