package main

import (
	"sort"
	"strings"
	"testing"
)

// A contract file that names its entry point without the "runtime." prefix still counts.
func TestSpecNamesBare(t *testing.T) {
	entries := map[string]*entry{"makeslice": {}, "growslice": {}, "memmove": {}, "newobject": {}}
	src := "/-- `makeslice(et, len, cap)` and `growslice` -/\n-- TEXT runtime·memmove\n" +
		"the word `other` are not entries; runtime.newobject is\n"
	got := specNames(src, entries)
	sort.Strings(got)
	if g := strings.Join(got, ","); g != "growslice,makeslice,memmove,newobject" {
		t.Fatalf("got %s", g)
	}
	if got := specNames("`other` `x(`", entries); len(got) != 0 {
		t.Fatalf("unexpected %v", got)
	}
}
