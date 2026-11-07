package main

import (
	"errors"
	"strings"
	"testing"
)

// U-SILENT-DEP regression tests: a dependency module that fails only inside the sandbox is named; a module killed for memory is
// named with the peak; a build killed with several jobs is retried one module at a time.

// A dependency whose own compile failed (as under the read-only sandbox, where host IO failed and the proof took other branches)
// is named with its diagnostic; the message is not "no module error recorded".
func TestOwnBuildErrorsNamesModule(t *testing.T) {
	ob := &ownBuild{errs: map[string]error{
		"Fv256.Amd64.SfdTeSum0": &diag{Msg: "SfdTeSum0.lean:10:2: error: unsolved goals"},
		"Fv256.Amd64.SfdTePre":  errors.New("write /host/flag: read-only file system"),
	}}
	got := ownBuildErrors(ob)
	for _, w := range []string{"Fv256.Amd64.SfdTeSum0: SfdTeSum0.lean:10:2: error: unsolved goals", "Fv256.Amd64.SfdTePre: write /host/flag: read-only file system"} {
		if !strings.Contains(got, w) {
			t.Errorf("ownBuildErrors does not name %q:\n%s", w, got)
		}
	}
	if !strings.Contains(ownBuildErrors(&ownBuild{errs: map[string]error{}}), "no module error recorded") {
		t.Errorf("an empty error set must say so")
	}
}

const killedLog = `✔ [1/6] Built Fv256.Amd64.SfdTeBody
✔ [2/6] Built Fv256.Amd64.SfdTePre
[3/6] Building Fv256.Amd64.SfdTeSum0
[4/6] Building Fv256.Amd64.SfdTeSum1
✖ [5/6] Building Fv256.Amd64.SfdTopI
error: Fv256.Amd64.SfdTeSum1: Lean exited with code 137
`

func TestUnfinishedModulesNamed(t *testing.T) {
	got := unfinishedModules(killedLog)
	want := []string{"Fv256.Amd64.SfdTeSum0", "Fv256.Amd64.SfdTeSum1", "Fv256.Amd64.SfdTopI"}
	if strings.Join(got, ",") != strings.Join(want, ",") {
		t.Errorf("unfinishedModules = %v, want %v", got, want)
	}
	if n := unfinishedNote(killedLog); !strings.Contains(n, "SfdTeSum1") {
		t.Errorf("unfinishedNote does not name the module: %q", n)
	}
	if unfinishedNote("nothing started\n") != "" {
		t.Errorf("no Building line, no note")
	}
}

// An OOM-killed module is named with its peak: the diagnostic of a build killed for memory carries the modules it was compiling and
// the measured peak.
func TestKilledBuildDiagNamesModuleAndPeak(t *testing.T) {
	g := &memGuard{mech: "cgroup", limit: 24 << 30}
	d := memLimitDiag(g, memEvent{Label: "lake build", Limit: 24 << 30, Peak: 23 << 30, Killed: true}, nil)
	d.Msg += unfinishedNote(killedLog)
	for _, w := range []string{"SfdTeSum1", "SfdTopI", "measured peak 23", "killed"} {
		if !strings.Contains(d.Msg, w) {
			t.Errorf("diagnostic does not say %q: %s", w, d.Msg)
		}
	}
}

// A build killed for memory with several concurrent modules is retried once, serially, and its second run decides.
func TestGuardedBuildRetriesSerially(t *testing.T) {
	// first run killed, serial run fine
	calls := []bool{}
	mark := memMark()
	run := func(serial bool) (string, error) {
		calls = append(calls, serial)
		if !serial {
			recordMemEvent(memEvent{Label: "lake build", Limit: 24 << 30, Peak: 24 << 30, Killed: true})
			return killedLog, errors.New("exit 137")
		}
		recordMemEvent(memEvent{Label: "lake build", Limit: 24 << 30, Peak: 17 << 30})
		return "✔ [1/1] Built All\n", nil
	}
	var notes []string
	out, err, kill := guardedBuild(run, 8, &mark, func(s string) { notes = append(notes, s) })
	if err != nil || kill != nil {
		t.Fatalf("the serial retry succeeded, got err=%v kill=%v", err, kill)
	}
	if len(calls) != 2 || calls[0] || !calls[1] {
		t.Errorf("calls = %v, want [false true]", calls)
	}
	if len(notes) != 1 || !strings.Contains(notes[0], "SfdTeSum1") || !strings.Contains(notes[0], "retrying with one module at a time") {
		t.Errorf("the retry must be announced and name the module: %v", notes)
	}
	if !strings.Contains(out, "Built All") {
		t.Errorf("the output of the serial run is kept: %q", out)
	}
	// killed again when serial: the kill (with its peak) is reported
	mark = memMark()
	run2 := func(serial bool) (string, error) {
		recordMemEvent(memEvent{Label: "lake build", Limit: 24 << 30, Peak: 25 << 30, Killed: true})
		return killedLog, errors.New("exit 137")
	}
	_, _, kill = guardedBuild(run2, 8, &mark, func(string) {})
	if kill == nil || kill.Peak != 25<<30 {
		t.Errorf("a build killed even when serial reports the kill with its peak, got %v", kill)
	}
	// a single-job build is never retried
	mark = memMark()
	n := 0
	run3 := func(bool) (string, error) {
		n++
		recordMemEvent(memEvent{Label: "lake build", Killed: true})
		return "", errors.New("x")
	}
	guardedBuild(run3, 1, &mark, func(string) {})
	if n != 1 {
		t.Errorf("jobs=1: %d runs, want 1", n)
	}
}
