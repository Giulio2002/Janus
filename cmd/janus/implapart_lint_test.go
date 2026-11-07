package main

import (
	"strings"
	"testing"
)

// U-IMPLAPART-LINT: a proof that assumes ImplApart about an extraction for which it is unsatisfiable for every impl is rejected at
// verify, naming the function and suggesting --contract.
func TestImplApartable(t *testing.T) {
	sp := func(n string, lo, size uint64) implSpan { return implSpan{n, lo, lo + size} }
	ok := []implSpan{sp("main.F", 0x1000, 16), sp("main.G", 0x1010, 16)}
	if err := implApartable("main.F", ok, []implStubAt{{"runtime.newobject", 0x2000}}); err != nil {
		t.Errorf("a disjoint extraction was rejected: %v", err)
	}
	// a stub address inside an extracted runtime function (runtime.osyield pulled in by an omitted contract flag)
	bad := []implSpan{sp("main.F", 0x1000, 16), sp("runtime.osyield", 0x3000, 32)}
	err := implApartable("main.F", bad, []implStubAt{{"runtime.usleep", 0x3008}})
	if err == nil || !strings.Contains(err.Error(), "runtime.osyield") || !strings.Contains(err.(*diag).Next, "--contract 'runtime.osyield'") {
		t.Errorf("a stub inside runtime.osyield must be rejected naming it with the --contract hint, got %v", err)
	}
	// overlapping functions
	if err := implApartable("main.F", []implSpan{sp("main.F", 0x1000, 32), sp("runtime.x", 0x1010, 32)}, nil); err == nil || !strings.Contains(err.Error(), "overlap") {
		t.Errorf("overlapping functions must be rejected, got %v", err)
	}
	// adjacent is fine
	if err := implApartable("main.F", []implSpan{sp("main.F", 0x1000, 16), sp("main.G", 0x1010, 5)}, nil); err != nil {
		t.Errorf("adjacent functions were rejected: %v", err)
	}
	// the selected function itself: no --contract hint
	err = implApartable("main.F", []implSpan{sp("main.F", 0x1000, 32)}, []implStubAt{{"runtime.y", 0x1004}})
	if err == nil || strings.Contains(err.(*diag).Next, "--contract") {
		t.Errorf("an overlap in the selected function suggests no --contract: %v", err)
	}
}

// The identity form: amd64 functions carry their byte length, arm64 their word count.
func TestImplApartableIdentity(t *testing.T) {
	id := &Identity{Symbol: "main.F",
		Functions: []identityFunc{{Name: "main.F", Address: "0x1000", Bytes: 16}, {Name: "runtime.systemstack.abi0", Address: "0x47ee00", Bytes: 0x95}},
		Stubs:     []identityStub{{Name: "trap:INT3", Address: "0x47ee93", Kind: "trap"}}}
	err := implApartableIdentity(id)
	if err == nil || !strings.Contains(err.Error(), "runtime.systemstack.abi0") {
		t.Errorf("amd64 identity: got %v", err)
	}
	id2 := &Identity{Symbol: "main.F", Functions: []identityFunc{{Name: "main.F", Address: "0x1000", Words: 4}, {Name: "main.G", Address: "0x1008", Words: 4}}}
	if err := implApartableIdentity(id2); err == nil {
		t.Errorf("arm64 identity: overlapping words not detected")
	}
	id3 := &Identity{Symbol: "main.F", Functions: []identityFunc{{Name: "main.F", Address: "0x1000", Words: 4}, {Name: "main.G", Address: "0x1010", Words: 4}}}
	if err := implApartableIdentity(id3); err != nil {
		t.Errorf("arm64 identity: disjoint rejected: %v", err)
	}
}
