package main

import (
	"reflect"
	"testing"
)

// A contract-able function reached only through another contract-able function (here
// runtime.mapaccess2_fast32 inside the body of runtime.ifaceeq) is not a direct hint.
func TestContractHintsDirectOnly(t *testing.T) {
	names := []string{"example.com/p.F", "runtime.ifaceeq", "runtime.mapaccess2_fast32", "runtime.newobject", "runtime.memmove"}
	parents := map[string]map[string]bool{
		"runtime.ifaceeq":           {"example.com/p.F": true},
		"runtime.mapaccess2_fast32": {"runtime.ifaceeq": true},
		"runtime.newobject":         {"example.com/p.F": true},
		"runtime.memmove":           {"runtime.newobject": true, "example.com/p.F": true},
	}
	hints, indirect := contractHints(names, "example.com/p.F", parents)
	wantH := []string{"--contract 'runtime.ifaceeq'", "--contract 'runtime.memmove'", "--contract 'runtime.newobject'"}
	if !reflect.DeepEqual(hints, wantH) {
		t.Errorf("hints %v, want %v", hints, wantH)
	}
	if !reflect.DeepEqual(indirect, []string{"runtime.mapaccess2_fast32"}) {
		t.Errorf("indirect %v", indirect)
	}
	// behind a non-contract intermediate: still indirect
	names = append(names, "runtime.rtype.string")
	parents["runtime.rtype.string"] = map[string]bool{"runtime.ifaceeq": true}
	parents["runtime.mapaccess2_fast32"] = map[string]bool{"runtime.rtype.string": true}
	hints, indirect = contractHints(names, "example.com/p.F", parents)
	if !reflect.DeepEqual(hints, wantH) || !reflect.DeepEqual(indirect, []string{"runtime.mapaccess2_fast32"}) {
		t.Errorf("transitive: %v %v", hints, indirect)
	}
	// no known caller: listed (conservative)
	h2, i2 := contractHints([]string{"runtime.newobject"}, "x", map[string]map[string]bool{})
	if len(h2) != 1 || len(i2) != 0 {
		t.Errorf("no-parent case: %v %v", h2, i2)
	}
}
