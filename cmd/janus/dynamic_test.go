package main

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

const (
	itabMul = "go:itab.*example.com/basic.MulHasher,example.com/basic.Hasher"
	itabRot = "go:itab.*example.com/basic.RotHasher,example.com/basic.Hasher"
)

func TestParseTargets(t *testing.T) {
	cases := map[string][]string{
		"":                                     nil,
		"a.F":                                  {"a.F"},
		"a.F,b":                                {"a.F", "b"},
		itabMul + "," + itabRot + ",p.F.func1": {itabMul, itabRot, "p.F.func1"},
		"go:itab.*p.T[int,string],p.I, p.G":    {"go:itab.*p.T[int,string],p.I", "p.G"},
	}
	for in, want := range cases {
		if got := parseTargets(in); fmt.Sprint(got) != fmt.Sprint(want) {
			t.Errorf("parseTargets(%q) = %q, want %q", in, got, want)
		}
	}
}

func dynNames(x *Extraction) []string {
	var out []string
	for _, d := range x.Dynamic {
		out = append(out, d.Name+" "+d.Via)
	}
	return out
}

// Itab targets copy every method of the itab, and the itab itself as its own data object.
func TestDynamicTargetsItab(t *testing.T) {
	for _, bin := range []string{exampleBin, exampleAmd64(t)} {
		b, err := loadBinary(bin)
		if err != nil {
			t.Fatal(err)
		}
		x, err := extractWith(b, "example.com/basic.HashWith", defaultMaxFunctions, nil, itabMul, itabRot)
		if err != nil {
			t.Fatal(err)
		}
		segs := strings.Join(segNames(x), " ")
		for _, want := range []string{"example.com/basic.(*MulHasher).Hash", "example.com/basic.(*RotHasher).Hash"} {
			if !strings.Contains(segs, want) {
				t.Errorf("%s: %s not extracted: %s", b.GOARCH, want, segs)
			}
		}
		if got := fmt.Sprint(dynNames(x)); got != "[example.com/basic.(*MulHasher).Hash itab example.com/basic.(*RotHasher).Hash itab]" {
			t.Errorf("%s: dynamic targets %s", b.GOARCH, got)
		}
		if len(x.Data) != 2 || x.Data[0].Name != itabMul || x.Data[1].Name != itabRot || len(x.Data[0].Bytes) != 32 {
			t.Fatalf("%s: itab data %+v", b.GOARCH, x.Data)
		}
		// fun[0] of each itab is the method's entry
		for i, d := range x.Data {
			fn := uint64(0)
			for k := 7; k >= 0; k-- {
				fn = fn<<8 | uint64(d.Bytes[itabFunOffset+k])
			}
			if fn != x.Dynamic[i].Addr {
				t.Errorf("%s: %s fun[0] = 0x%x, want 0x%x", b.GOARCH, d.Name, fn, x.Dynamic[i].Addr)
			}
		}
		// without targets: only HashWith
		y, err := extractWith(b, "example.com/basic.HashWith", defaultMaxFunctions, nil)
		if err != nil {
			t.Fatal(err)
		}
		if len(y.Dynamic) != 0 || len(y.Data) != 0 {
			t.Errorf("%s: unexpected dynamic targets without --targets: %v", b.GOARCH, dynNames(y))
		}
	}
}

// Code addresses computed by the extracted code (closures, method values) are inferred.
func TestDynamicTargetsInferred(t *testing.T) {
	for _, bin := range []string{exampleBin, exampleAmd64(t)} {
		b, err := loadBinary(bin)
		if err != nil {
			t.Fatal(err)
		}
		for sym, want := range map[string]string{
			"example.com/basic.HashTwice": "example.com/basic.(*MulHasher).Hash-fm code-address",
			"example.com/basic.AffineSum": "example.com/basic.AffineSum.func1 code-address",
			"example.com/basic.DeferAdd":  "example.com/basic.DeferAdd.func1 code-address",
		} {
			x, err := extractWith(b, sym, defaultMaxFunctions, nil)
			if err != nil {
				t.Fatalf("%s %s: %v", b.GOARCH, sym, err)
			}
			if got := strings.Join(dynNames(x), ","); got != want {
				t.Errorf("%s %s: dynamic targets %q, want %q", b.GOARCH, sym, got, want)
			}
		}
		// HashTwice: the method value wrapper calls the method directly, which is copied too.
		x, _ := extractWith(b, "example.com/basic.HashTwice", defaultMaxFunctions, nil)
		if !strings.Contains(strings.Join(segNames(x), " "), "example.com/basic.(*MulHasher).Hash ") &&
			!strings.HasSuffix(strings.Join(segNames(x), " "), "example.com/basic.(*MulHasher).Hash") {
			t.Errorf("%s: HashTwice segments %v", b.GOARCH, segNames(x))
		}
	}
}

// runtime.deferreturn is not followed (open-coded defers call it only after a recovered panic).
func TestDeferreturnOmitted(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.DeferAdd")
	id := readIdentity(t, dir)
	if len(id.OmittedCalls) != 1 || id.OmittedCalls[0].Name != "runtime.deferreturn" {
		t.Errorf("omitted calls: %+v", id.OmittedCalls)
	}
	for _, f := range id.Functions {
		if strings.HasPrefix(f.Name, "runtime.") {
			t.Errorf("runtime function extracted: %s", f.Name)
		}
	}
	if len(id.DynamicTargets) != 1 || id.DynamicTargets[0].Via != "code-address" {
		t.Errorf("dynamic targets: %+v", id.DynamicTargets)
	}
}

// --targets is recorded, re-applied by check, and a changed list is detected.
func TestTargetsRecordedAndChecked(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.HashWith", "--targets", itabMul+","+itabRot)
	id := readIdentity(t, dir)
	if fmt.Sprint(id.Targets) != fmt.Sprint([]string{itabMul, itabRot}) || len(id.DynamicTargets) != 2 {
		t.Fatalf("identity targets %v, dynamic %+v", id.Targets, id.DynamicTargets)
	}
	if code, _, stderr := runJanus(t, "check", dir); code != 0 {
		t.Fatalf("check failed: %s", stderr)
	}
	// dropping a target from identity.json makes the regenerated extraction differ
	p := filepath.Join(dir, "identity.json")
	raw, _ := os.ReadFile(p)
	tampered := strings.Replace(string(raw), "\""+itabRot+"\"\n", "", 1)
	tampered = strings.Replace(tampered, "\""+itabMul+"\",\n", "\""+itabMul+"\"\n", 1)
	if tampered == string(raw) {
		t.Fatal("tamper did not apply")
	}
	if err := os.WriteFile(p, []byte(tampered), 0o644); err != nil {
		t.Fatal(err)
	}
	code, _, stderr := runJanus(t, "check", dir)
	if code == 0 || !strings.Contains(stderr, "Stale or mismatched artifact") {
		t.Errorf("check accepted a changed target list (code %d): %s", code, stderr)
	}
	// unknown and non-itab targets are rejected
	for _, bad := range []string{"no.such.Symbol", "runtime.buildVersion"} {
		code, _, stderr := runJanus(t, "extract", exampleBin, "example.com/basic.HashWith", filepath.Join(t.TempDir(), "x"), "--targets", bad)
		if code == 0 || !strings.Contains(stderr, "--targets") {
			t.Errorf("--targets %s accepted (code %d): %s", bad, code, stderr)
		}
	}
}
