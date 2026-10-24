package main

// Hard memory guard for every Lean-family process janus starts (lean, leanchecker, lake,
// janus-audit, janus-decode). See docs/TESTING.md ("Memory guard").
//
// A Lean job that runs away (a kernel replay holding dozens of environments, a proof that
// elaborates a huge term, a lake build compiling many modules at once) must be killed on its
// own, never take the host down through the global OOM killer. Each job therefore runs inside
// a cgroup v2 memory limit (memory.max = the limit, memory.swap.max = 0), so the kernel's
// cgroup-local OOM killer ends it when it exceeds the limit. janus then reports
// `Invalid: … Stage: resource limit` with the limit and the measured memory.peak, instead of
// whatever proof/audit error the killed process would otherwise have caused.
//
// Mechanisms, strongest first (JANUS_MEMGUARD=<mechanism> forces one, for tests):
//
//	cgroup          a child cgroup of $JANUS_MEMGUARD_CGROUP, a delegated cgroup set up by
//	                scripts/lib/memguard.sh (nested guards: a job-level limit around per-process
//	                limits); or of janus's own cgroup when it is delegated and the memory
//	                controller can be enabled for a child
//	systemd-user    `systemd-run --user --scope -p MemoryMax=… -p MemorySwapMax=0`, with janus
//	                re-executed inside the scope as a tiny supervisor that reads memory.peak and
//	                memory.events of the scope after the job exits
//	systemd-system  the same with the system manager (root only)
//	prlimit         RLIMIT_AS = limit + 16 GiB, per process: Lean reserves ~10 GiB of address
//	                space up front (thread stacks, heap arenas), so a virtual limit is blunt; the
//	                peak is the job's max RSS from wait4
//	none            nothing works: the job runs unguarded, with a warning
//
// The limit is JANUS_MEM_MAX ("16G", "1500M", "off"), default min(24 GiB, 40% of MemTotal).
// The guard wraps the whole sandboxed process tree: the cgroup is entered before bwrap/unshare
// starts, and every descendant inherits it.

import (
	"bufio"
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

const (
	memguardExecArg  = "__janus-memguard-exec"
	memguardProbeArg = "__janus-memguard-probe"
	gib              = int64(1) << 30
	prlimitSlack     = 16 * gib
	cgroupRoot       = "/sys/fs/cgroup"
)

// memGuardInfo is what verified.json records about the guard of a verification.
type memGuardInfo struct {
	Mechanism  string `json:"mechanism"`
	Limit      string `json:"limit,omitempty"`
	LimitBytes int64  `json:"limitBytes,omitempty"`
	Source     string `json:"source,omitempty"` // "JANUS_MEM_MAX" or "default"
	// PeakBytes is the largest memory.peak (prlimit: max RSS) of the guarded jobs of this
	// verification (0 if none ran or none was measurable).
	PeakBytes int64  `json:"peakBytes,omitempty"`
	Peak      string `json:"peak,omitempty"`
	Jobs      int    `json:"jobs,omitempty"`
	Note      string `json:"note,omitempty"`
}

type memGuard struct {
	mech    string // cgroup, systemd-user, systemd-system, prlimit, off, none
	limit   int64
	source  string
	parent  string // cgroup mode: the parent cgroup directory
	sdrun   string // systemd modes: path to systemd-run
	prlim   string // prlimit mode: path to prlimit
	self    string // systemd modes: the janus executable re-run as supervisor
	sdEnv   []string
	note    string
	errText string // a configuration error (bad JANUS_MEM_MAX)
}

// memEvent is one guarded job.
type memEvent struct {
	Label  string
	Limit  int64 // effective limit (smallest memory.max on the path)
	Peak   int64
	Killed bool
}

var (
	guardOnce   sync.Once
	theGuard    *memGuard
	memMu       sync.Mutex
	memEvents   []memEvent
	guardLogged sync.Once
)

// currentGuard detects the guard once per process.
func currentGuard() *memGuard {
	guardOnce.Do(func() { theGuard = detectMemGuard() })
	return theGuard
}

// resetMemGuardForTest makes the next currentGuard re-detect (tests change JANUS_MEM_MAX).
func resetMemGuardForTest() {
	guardOnce = sync.Once{}
	guardLogged = sync.Once{}
}

// logMemGuard prints, once per process, which mechanism is active.
func logMemGuard(w io.Writer) {
	if w == nil {
		return
	}
	g := currentGuard()
	guardLogged.Do(func() {
		if os.Getenv("JANUS_MEMGUARD_QUIET") != "" && g.mech != "none" {
			return
		}
		fmt.Fprintf(w, "janus: memory guard: %s\n", g.describe())
	})
}

func (g *memGuard) describe() string {
	switch g.mech {
	case "off":
		return "off (JANUS_MEM_MAX=off): Lean jobs run without a memory limit"
	case "none":
		return "NONE available (" + g.note + "); Lean jobs run without a memory limit. Set up a user systemd manager or a delegated cgroup, or install prlimit"
	}
	s := fmt.Sprintf("%s, limit %s per job (%s), no swap", g.mech, fmtBytes(g.limit), g.source)
	if g.mech == "prlimit" {
		s = fmt.Sprintf("prlimit (weaker: per-process virtual-memory limit %s = %s + %s reservation slack; no cgroup available: %s)",
			fmtBytes(g.limit+prlimitSlack), fmtBytes(g.limit), fmtBytes(prlimitSlack), g.note)
	}
	if g.mech == "cgroup" {
		s += ", under " + g.parent
	}
	return s
}

func (g *memGuard) info() *memGuardInfo {
	mi := &memGuardInfo{Mechanism: g.mech}
	if g.mech != "off" && g.mech != "none" {
		mi.Limit, mi.LimitBytes, mi.Source = fmtBytes(g.limit), g.limit, g.source
	}
	if g.mech == "none" {
		mi.Note = g.note
	}
	return mi
}

// parseMemSize parses "24G", "1500M", "1.5GiB", "1073741824" (binary units).
func parseMemSize(s string) (int64, error) {
	t := strings.TrimSpace(strings.ToUpper(s))
	t = strings.TrimSuffix(strings.TrimSuffix(t, "B"), "I")
	mult := int64(1)
	if t != "" {
		switch t[len(t)-1] {
		case 'K':
			mult = 1 << 10
		case 'M':
			mult = 1 << 20
		case 'G':
			mult = 1 << 30
		case 'T':
			mult = 1 << 40
		}
		if mult != 1 {
			t = t[:len(t)-1]
		}
	}
	f, err := strconv.ParseFloat(t, 64)
	if err != nil || f <= 0 {
		return 0, fmt.Errorf("JANUS_MEM_MAX=%q is not a size like 16G, 1500M or off", s)
	}
	n := int64(f * float64(mult))
	if n < 64<<20 {
		return 0, fmt.Errorf("JANUS_MEM_MAX=%q is below 64M, too small to run Lean", s)
	}
	return n, nil
}

func fmtBytes(n int64) string {
	switch {
	case n >= gib:
		return strconv.FormatFloat(float64(n)/float64(gib), 'f', 1, 64) + " GiB"
	case n >= 1<<20:
		return strconv.FormatFloat(float64(n)/float64(1<<20), 'f', 0, 64) + " MiB"
	default:
		return strconv.FormatInt(n, 10) + " B"
	}
}

// memTotal is MemTotal from /proc/meminfo in bytes (0 if unknown).
func memInfo(key string) int64 {
	f, err := os.Open("/proc/meminfo")
	if err != nil {
		return 0
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		fs := strings.Fields(sc.Text())
		if len(fs) >= 2 && fs[0] == key+":" {
			v, _ := strconv.ParseInt(fs[1], 10, 64)
			return v << 10
		}
	}
	return 0
}

// defaultMemLimit is min(24 GiB, 40% of MemTotal).
func defaultMemLimit() int64 {
	lim := 24 * gib
	if t := memInfo("MemTotal"); t > 0 && t*2/5 < lim {
		lim = t * 2 / 5
	}
	return lim
}

func detectMemGuard() *memGuard {
	g := &memGuard{source: "default", limit: defaultMemLimit()}
	if v := strings.TrimSpace(os.Getenv("JANUS_MEM_MAX")); v != "" {
		if strings.EqualFold(v, "off") {
			g.mech = "off"
			return g
		}
		n, err := parseMemSize(v)
		if err != nil {
			g.mech, g.errText = "off", err.Error()
			return g
		}
		g.limit, g.source = n, "JANUS_MEM_MAX="+v
	}
	if runtime.GOOS != "linux" {
		g.mech, g.note = "none", "not Linux"
		return g
	}
	force := os.Getenv("JANUS_MEMGUARD")
	var notes []string
	try := func(m string, f func() error) bool {
		if force != "" && force != m {
			return false
		}
		if err := f(); err != nil {
			notes = append(notes, m+": "+err.Error())
			return false
		}
		g.mech = m
		return true
	}
	if try("cgroup", g.probeCgroup) || try("systemd-user", func() error { return g.probeSystemd(true) }) ||
		try("systemd-system", func() error { return g.probeSystemd(false) }) || try("prlimit", g.probePrlimit) {
		g.note = strings.Join(notes, "; ")
		return g
	}
	g.mech = "none"
	g.note = strings.Join(notes, "; ")
	if force != "" && g.note == "" {
		g.note = "JANUS_MEMGUARD=" + force + " is not a mechanism"
	}
	return g
}

// ownCgroup is the cgroup v2 directory of this process.
func ownCgroup() (string, error) {
	b, err := os.ReadFile("/proc/self/cgroup")
	if err != nil {
		return "", err
	}
	for _, l := range strings.Split(string(b), "\n") {
		if p, ok := strings.CutPrefix(l, "0::"); ok {
			return filepath.Join(cgroupRoot, p), nil
		}
	}
	return "", errors.New("not on the cgroup v2 unified hierarchy")
}

// probeCgroup: a child of $JANUS_MEMGUARD_CGROUP (or of our own cgroup) gets a memory.max.
func (g *memGuard) probeCgroup() error {
	parents := []string{}
	if p := os.Getenv("JANUS_MEMGUARD_CGROUP"); p != "" {
		parents = append(parents, p)
	}
	if own, err := ownCgroup(); err == nil {
		parents = append(parents, own)
	}
	var errs []string
	for _, p := range parents {
		d, err := newJobCgroup(p, g.limit)
		if err != nil {
			errs = append(errs, err.Error())
			continue
		}
		_ = removeCgroup(d)
		g.parent = p
		return nil
	}
	if len(errs) == 0 {
		return errors.New("no cgroup v2 hierarchy")
	}
	return errors.New(strings.Join(errs, "; "))
}

// newJobCgroup creates a child of parent with memory.max = limit and no swap.
func newJobCgroup(parent string, limit int64) (string, error) {
	if _, err := os.Stat(filepath.Join(parent, "cgroup.subtree_control")); err != nil {
		return "", fmt.Errorf("%s is not a cgroup v2 directory", parent)
	}
	d := filepath.Join(parent, "janus-"+strconv.Itoa(os.Getpid())+"-"+newNonce()[:8])
	if err := os.Mkdir(d, 0o755); err != nil {
		return "", fmt.Errorf("cannot create a child cgroup of %s: %v", parent, err)
	}
	fail := func(err error) (string, error) { _ = os.Remove(d); return "", err }
	if _, err := os.Stat(filepath.Join(d, "memory.max")); err != nil {
		return fail(fmt.Errorf("the memory controller is not enabled for children of %s", parent))
	}
	if err := os.WriteFile(filepath.Join(d, "memory.max"), []byte(strconv.FormatInt(limit, 10)), 0o644); err != nil {
		return fail(fmt.Errorf("cannot set memory.max under %s: %v", parent, err))
	}
	if _, err := os.Stat(filepath.Join(d, "memory.swap.max")); err == nil {
		if err := os.WriteFile(filepath.Join(d, "memory.swap.max"), []byte("0"), 0o644); err != nil {
			return fail(fmt.Errorf("cannot set memory.swap.max under %s: %v", parent, err))
		}
	}
	// Kill the whole job tree (bwrap, lake and the lean processes) on an OOM, not one process.
	_ = os.WriteFile(filepath.Join(d, "memory.oom.group"), []byte("1"), 0o644)
	// The child must be enterable (cgroup.procs writable).
	if f, err := os.OpenFile(filepath.Join(d, "cgroup.procs"), os.O_WRONLY, 0); err != nil {
		return fail(fmt.Errorf("cannot enter a child cgroup of %s: %v", parent, err))
	} else {
		f.Close()
	}
	return d, nil
}

// removeCgroup kills anything left in d (only processes of this job) and removes it.
func removeCgroup(d string) error {
	_ = os.WriteFile(filepath.Join(d, "cgroup.kill"), []byte("1"), 0o644)
	var err error
	for i := 0; i < 50; i++ {
		if err = os.Remove(d); err == nil || os.IsNotExist(err) {
			return nil
		}
		time.Sleep(20 * time.Millisecond)
	}
	return err
}

// cgroupStats reads memory.peak and the OOM kill count of d, and the effective limit (the
// smallest memory.max from d up to the root).
func cgroupStats(d string) (peak, limit int64, killed bool) {
	if b, err := os.ReadFile(filepath.Join(d, "memory.peak")); err == nil {
		peak, _ = strconv.ParseInt(strings.TrimSpace(string(b)), 10, 64)
	}
	if b, err := os.ReadFile(filepath.Join(d, "memory.events")); err == nil {
		for _, l := range strings.Split(string(b), "\n") {
			if f := strings.Fields(l); len(f) == 2 && (f[0] == "oom_kill" || f[0] == "oom_group_kill") && f[1] != "0" {
				killed = true
			}
		}
	}
	for p := d; strings.HasPrefix(p, cgroupRoot+"/"); p = filepath.Dir(p) {
		if b, err := os.ReadFile(filepath.Join(p, "memory.max")); err == nil {
			if v, err := strconv.ParseInt(strings.TrimSpace(string(b)), 10, 64); err == nil && (limit == 0 || v < limit) {
				limit = v
			}
		}
	}
	return
}

func (g *memGuard) systemdArgs(user bool, unit string) []string {
	a := []string{g.sdrun}
	if user {
		a = append(a, "--user")
	}
	return append(a, "--scope", "--quiet", "--collect", "--unit="+unit,
		"-p", "MemoryMax="+strconv.FormatInt(g.limit, 10), "-p", "MemorySwapMax=0", "-p", "OOMPolicy=continue", "--")
}

// probeSystemd runs the supervisor's probe in a transient scope and checks that the scope's
// memory.max is the limit.
func (g *memGuard) probeSystemd(user bool) error {
	if !user && os.Geteuid() != 0 {
		return errors.New("needs root")
	}
	p, err := exec.LookPath("systemd-run")
	if err != nil {
		return errors.New("systemd-run not found")
	}
	self, err := os.Executable()
	if err != nil {
		return err
	}
	g.sdrun, g.self = p, self
	env := os.Environ()
	if user && os.Getenv("XDG_RUNTIME_DIR") == "" {
		rd := "/run/user/" + strconv.Itoa(os.Getuid())
		if _, err := os.Stat(filepath.Join(rd, "bus")); err == nil {
			env = append(env, "XDG_RUNTIME_DIR="+rd)
		}
	}
	g.sdEnv = env
	argv := append(g.systemdArgs(user, "janus-probe-"+newNonce()[:12]), self, memguardProbeArg)
	cmd := exec.Command(argv[0], argv[1:]...)
	cmd.Env = env
	var out bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &out
	done := make(chan error, 1)
	if err := cmd.Start(); err != nil {
		return err
	}
	go func() { done <- cmd.Wait() }()
	select {
	case err = <-done:
	case <-time.After(20 * time.Second):
		_ = cmd.Process.Kill()
		<-done
		return errors.New("systemd-run timed out")
	}
	s := strings.TrimSpace(out.String())
	if err != nil {
		if i := strings.IndexByte(s, '\n'); i > 0 {
			s = s[:i]
		}
		return fmt.Errorf("%v: %s", err, s)
	}
	if s != strconv.FormatInt(g.limit, 10) {
		return fmt.Errorf("the scope's memory.max is %q, not the limit", s)
	}
	return nil
}

func (g *memGuard) probePrlimit() error {
	p, err := exec.LookPath("prlimit")
	if err != nil {
		return errors.New("prlimit not found")
	}
	if err := exec.Command(p, "--as="+strconv.FormatInt(g.limit+prlimitSlack, 10), "--", "/bin/true").Run(); err != nil {
		return err
	}
	g.prlim = p
	return nil
}

// jobLabel names a job for diagnostics: the program and its first arguments.
func jobLabel(cmd *exec.Cmd) string {
	argv := cmd.Args
	// Look through the sandbox wrappers to the real program.
	for i, a := range argv {
		if a == "--" && i+1 < len(argv) && (filepath.Base(argv[0]) == "bwrap") {
			argv = argv[i+1:]
			break
		}
		if a == "janus-sandbox" && filepath.Base(argv[0]) == "unshare" {
			argv = argv[i+1:]
			break
		}
	}
	if len(argv) == 0 {
		return "?"
	}
	parts := []string{filepath.Base(argv[0])}
	for _, a := range argv[1:] {
		if len(parts) >= 3 {
			break
		}
		if strings.HasPrefix(a, "-") {
			continue
		}
		parts = append(parts, filepath.Base(a))
	}
	return strings.Join(parts, " ")
}

// memKillError is returned by guardRun when the job was killed for memory.
type memKillError struct {
	ev  memEvent
	err error
}

func (e *memKillError) Error() string {
	return fmt.Sprintf("%s was killed by the memory limit (peak %s, limit %s)", e.ev.Label, fmtBytes(e.ev.Peak), fmtBytes(e.ev.Limit))
}
func (e *memKillError) Unwrap() error { return e.err }

func recordMem(ev memEvent) {
	memMu.Lock()
	memEvents = append(memEvents, ev)
	memMu.Unlock()
}

// memMark is a position in the job log; memSince summarizes the jobs after it.
func memMark() int {
	memMu.Lock()
	defer memMu.Unlock()
	return len(memEvents)
}

func memSince(mark int) (jobs int, peak int64, kill *memEvent) {
	memMu.Lock()
	defer memMu.Unlock()
	for i := mark; i < len(memEvents); i++ {
		e := memEvents[i]
		jobs++
		if e.Peak > peak {
			peak = e.Peak
		}
		if e.Killed && kill == nil {
			k := e
			kill = &k
		}
	}
	return
}

// memLimitDiag is the resource-limit diagnostic for a killed job.
func memLimitDiag(g *memGuard, ev memEvent, cause error) *diag {
	lim := ev.Limit
	if lim == 0 {
		lim = g.limit
	}
	d := &diag{Invalid: true, Stage: "resource limit",
		Msg: fmt.Sprintf("%s exceeded the memory limit and was killed (limit %s, measured peak %s, mechanism %s). This is not a verdict on the proof.",
			ev.Label, fmtBytes(lim), fmtBytes(ev.Peak), g.mech),
		Next: "Raise the per-job limit with JANUS_MEM_MAX (e.g. JANUS_MEM_MAX=32G; default min(24G, 40% of RAM)) if the host has the memory, " +
			"or make the proof (or what it imports) need less memory."}
	if cd, ok := cause.(*diag); ok && cd != nil && cd.Stage != "resource limit" {
		d.Details = "The killed job interrupted the stage: " + cd.Stage
	}
	return d
}

// memOutcome is applied to the result of one verification that started at mark: a job killed
// for memory turns the result into the resource-limit diagnostic (whatever error it caused,
// and even if a later step happened to pass), and a report records the guard and the peak.
func memOutcome(mark int, r *verifiedReport, err error) (*verifiedReport, error) {
	g := currentGuard()
	jobs, peak, kill := memSince(mark)
	if kill != nil {
		return nil, memLimitDiag(g, *kill, err)
	}
	if r != nil {
		mi := g.info()
		mi.Jobs = jobs
		if peak > 0 {
			mi.PeakBytes, mi.Peak = peak, fmtBytes(peak)
		}
		r.MemoryGuard = mi
	}
	return r, err
}

// memGuardConfigErr reports a bad JANUS_MEM_MAX before anything runs.
func memGuardConfigErr() error {
	if g := currentGuard(); g.errText != "" {
		return &diag{Invalid: true, Stage: "resource limit", Msg: g.errText, Next: "Set JANUS_MEM_MAX to a size (16G, 1500M) or off."}
	}
	return nil
}

// tailWriter forwards to w and keeps the last bytes written (to recognise Lean's own
// out-of-memory message under prlimit).
type tailWriter struct {
	w    io.Writer
	mu   sync.Mutex
	tail []byte
}

func (t *tailWriter) Write(p []byte) (int, error) {
	t.mu.Lock()
	t.tail = append(t.tail, p...)
	if len(t.tail) > 8192 {
		t.tail = t.tail[len(t.tail)-8192:]
	}
	t.mu.Unlock()
	if t.w == nil {
		return len(p), nil
	}
	return t.w.Write(p)
}

// guardRun runs cmd (not yet started) under the memory guard, like cmd.Run.
func guardRun(cmd *exec.Cmd) error {
	g := currentGuard()
	label := jobLabel(cmd)
	switch g.mech {
	case "cgroup":
		d, err := newJobCgroup(g.parent, g.limit)
		if err != nil {
			return fmt.Errorf("memory guard: %v", err)
		}
		defer removeCgroup(d)
		fd, err := syscall.Open(d, syscall.O_DIRECTORY|syscall.O_RDONLY|syscall.O_CLOEXEC, 0)
		if err != nil {
			return fmt.Errorf("memory guard: %v", err)
		}
		defer syscall.Close(fd)
		if cmd.SysProcAttr == nil {
			cmd.SysProcAttr = &syscall.SysProcAttr{}
		}
		cmd.SysProcAttr.UseCgroupFD, cmd.SysProcAttr.CgroupFD = true, fd
		runErr := cmd.Run()
		peak, lim, killed := cgroupStats(d)
		ev := memEvent{Label: label, Limit: lim, Peak: peak, Killed: killed}
		recordMem(ev)
		if killed {
			return &memKillError{ev: ev, err: runErr}
		}
		return runErr
	case "systemd-user", "systemd-system":
		stats, err := os.CreateTemp("", "janus-memguard-*.json")
		if err != nil {
			return fmt.Errorf("memory guard: %v", err)
		}
		stats.Close()
		defer os.Remove(stats.Name())
		path := cmd.Path
		argv := append(g.systemdArgs(g.mech == "systemd-user", "janus-job-"+newNonce()[:12]), g.self, memguardExecArg, stats.Name(), "--", path)
		cmd.Args = append(argv, cmd.Args[1:]...)
		cmd.Path = g.sdrun
		if cmd.Env == nil {
			cmd.Env = os.Environ()
		}
		if g.mech == "systemd-user" && os.Getenv("XDG_RUNTIME_DIR") == "" {
			for _, e := range g.sdEnv {
				if strings.HasPrefix(e, "XDG_RUNTIME_DIR=") {
					cmd.Env = append(cmd.Env, e)
				}
			}
		}
		if cmd.SysProcAttr == nil {
			cmd.SysProcAttr = &syscall.SysProcAttr{}
		}
		cmd.SysProcAttr.Pdeathsig = syscall.SIGKILL
		runErr := cmd.Run()
		var st supervisorStats
		b, _ := os.ReadFile(stats.Name())
		if json.Unmarshal(b, &st) != nil {
			// The supervisor did not report (systemd-run failed, or it was killed itself).
			recordMem(memEvent{Label: label, Limit: g.limit})
			if runErr != nil {
				return fmt.Errorf("memory guard (systemd-run): %v", runErr)
			}
			return nil
		}
		ev := memEvent{Label: label, Limit: st.Limit, Peak: st.Peak, Killed: st.Killed}
		recordMem(ev)
		if st.Killed {
			return &memKillError{ev: ev, err: runErr}
		}
		return runErr
	case "prlimit":
		cmd.Args = append([]string{g.prlim, "--as=" + strconv.FormatInt(g.limit+prlimitSlack, 10), "--", cmd.Path}, cmd.Args[1:]...)
		cmd.Path = g.prlim
		tw := &tailWriter{w: cmd.Stdout}
		sameOut := cmd.Stdout == cmd.Stderr
		cmd.Stdout = tw
		if sameOut {
			cmd.Stderr = tw
		} else {
			cmd.Stderr = &tailWriter{w: cmd.Stderr, tail: nil}
		}
		runErr := cmd.Run()
		var peak int64
		if cmd.ProcessState != nil {
			if ru, ok := cmd.ProcessState.SysUsage().(*syscall.Rusage); ok {
				peak = ru.Maxrss << 10
			}
		}
		out := string(tw.tail)
		if t2, ok := cmd.Stderr.(*tailWriter); ok && t2 != tw {
			out += string(t2.tail)
		}
		killed := runErr != nil && (strings.Contains(out, "out of memory") || strings.Contains(out, "bad_alloc") ||
			strings.Contains(out, "failed to create thread") || strings.Contains(out, "Cannot allocate memory"))
		ev := memEvent{Label: label, Limit: g.limit, Peak: peak, Killed: killed}
		recordMem(ev)
		if killed {
			return &memKillError{ev: ev, err: runErr}
		}
		return runErr
	default:
		return cmd.Run()
	}
}

// supervisorStats is what the in-scope supervisor writes for its parent.
type supervisorStats struct {
	Peak   int64 `json:"peak"`
	Limit  int64 `json:"limit"`
	Killed bool  `json:"killed"`
}

func init() {
	if len(os.Args) >= 2 {
		switch os.Args[1] {
		case memguardProbeArg:
			cg, err := ownCgroup()
			if err == nil {
				var b []byte
				if b, err = os.ReadFile(filepath.Join(cg, "memory.max")); err == nil {
					fmt.Println(strings.TrimSpace(string(b)))
					os.Exit(0)
				}
			}
			fmt.Println(err)
			os.Exit(1)
		case memguardExecArg:
			os.Exit(superviseJob(os.Args[2:]))
		}
	}
}

// superviseJob runs inside the transient scope: it starts the job (same cgroup), forwards
// termination signals, and after the job exits writes the scope's memory.peak, effective limit
// and OOM-kill state to the stats file. It stays out of the OOM killer's way (it is tiny, and
// the scope has OOMPolicy=continue). args: STATSFILE -- PROGRAM ARGS…
func superviseJob(args []string) int {
	if len(args) < 3 || args[1] != "--" {
		fmt.Fprintln(os.Stderr, "janus memguard: bad supervisor arguments")
		return 125
	}
	statsFile, argv := args[0], args[2:]
	_ = os.WriteFile("/proc/self/oom_score_adj", []byte("-500"), 0o644) // best effort (root only)
	runtime.LockOSThread()                                              // Pdeathsig follows this thread
	cmd := exec.Command(argv[0], argv[1:]...)
	cmd.Stdin, cmd.Stdout, cmd.Stderr = os.Stdin, os.Stdout, os.Stderr
	cmd.SysProcAttr = &syscall.SysProcAttr{Pdeathsig: syscall.SIGKILL}
	sigs := make(chan os.Signal, 4)
	signal.Notify(sigs, syscall.SIGTERM, syscall.SIGINT, syscall.SIGHUP)
	if err := cmd.Start(); err != nil {
		fmt.Fprintf(os.Stderr, "janus memguard: %v\n", err)
		return 127
	}
	go func() {
		for s := range sigs {
			_ = cmd.Process.Signal(s)
		}
	}()
	err := cmd.Wait()
	code := 0
	if err != nil {
		code = 1
		var ee *exec.ExitError
		if errors.As(err, &ee) {
			if ws, ok := ee.Sys().(syscall.WaitStatus); ok && ws.Signaled() {
				code = 128 + int(ws.Signal())
			} else {
				code = ee.ExitCode()
			}
		}
	}
	var st supervisorStats
	if cg, err := ownCgroup(); err == nil {
		st.Peak, st.Limit, st.Killed = cgroupStats(cg)
	}
	b, _ := json.Marshal(st)
	_ = os.WriteFile(statsFile, b, 0o600)
	return code
}

// lakeJobMem is the memory one concurrent lake build job (one lean process compiling a
// framework module) is budgeted at ($JANUS_LAKE_JOB_MEM, default 3G; see docs/TESTING.md for the
// measured per-module peaks).
func lakeJobMem() int64 {
	if v := os.Getenv("JANUS_LAKE_JOB_MEM"); v != "" {
		if n, err := parseMemSize(v); err == nil {
			return n
		}
	}
	return 3 * gib
}

// lakeJobs is the number of modules a guarded lake build compiles at once: the per-job memory
// limit divided by the per-module budget, between 1 and the number of CPUs. Lake sizes its
// job pool from LEAN_NUM_THREADS.
func lakeJobs() int {
	n := runtime.NumCPU()
	g := currentGuard()
	if g.mech == "off" || g.mech == "none" {
		return n
	}
	j := int(g.limit / lakeJobMem())
	if j < 1 {
		j = 1
	}
	if j < n {
		n = j
	}
	return n
}

// lakeBuildEnv sets LEAN_NUM_THREADS for a `lake build` from the memory budget, unless the
// caller set it.
func lakeBuildEnv(env []string) []string {
	for _, e := range env {
		if strings.HasPrefix(e, "LEAN_NUM_THREADS=") {
			return env
		}
	}
	return append(env, "LEAN_NUM_THREADS="+strconv.Itoa(lakeJobs()))
}

// cmdMemguard: `janus memguard` prints the active guard; `janus memguard -- CMD ARGS…` runs a
// command under it (stdio inherited) and prints its peak, exiting with its status.
func cmdMemguard(args []string, stdout, stderr io.Writer) error {
	if err := memGuardConfigErr(); err != nil {
		return err
	}
	g := currentGuard()
	if len(args) == 0 {
		fmt.Fprintf(stdout, "memory guard: %s\n", g.describe())
		if g.note != "" && g.mech != "none" {
			fmt.Fprintf(stdout, "  skipped: %s\n", g.note)
		}
		return nil
	}
	if args[0] == "--" {
		args = args[1:]
	}
	if len(args) == 0 {
		return usageErr("memguard -- takes a command")
	}
	p, err := exec.LookPath(args[0])
	if err != nil {
		return &diag{Msg: err.Error(), Stage: "command line"}
	}
	cmd := exec.Command(p, args[1:]...)
	cmd.Args[0] = args[0]
	cmd.Stdin, cmd.Stdout, cmd.Stderr = os.Stdin, stdout, stderr
	mark := memMark()
	runErr := guardRun(cmd)
	_, peak, kill := memSince(mark)
	if kill != nil {
		return memLimitDiag(g, *kill, nil)
	}
	fmt.Fprintf(stderr, "janus memguard: %s: peak %s (%s)\n", jobLabel(cmd), fmtBytes(peak), g.describe())
	if runErr != nil {
		return &diag{Msg: fmt.Sprintf("%s: %v", args[0], runErr), Stage: "command"}
	}
	return nil
}
