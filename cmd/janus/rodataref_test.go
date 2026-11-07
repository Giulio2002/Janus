package main

import (
	"bytes"
	"encoding/binary"
	"testing"
)

// U-RODATA-REF: the bytes a copied string header points to are extracted too (both ISAs share collectData).
func TestRodataRefStringBytes(t *testing.T) {
	const base = 0x400000
	ro := make([]byte, 0x200)
	// the header of "<nil>" at +0x100: pointer to the bytes at +0x180, length 5
	binary.LittleEndian.PutUint64(ro[0x100:], base+0x180)
	binary.LittleEndian.PutUint64(ro[0x108:], 5)
	copy(ro[0x180:], "<nil>")
	// a second-level header at +0x1c0 reached only through the first string's neighbourhood is not needed;
	// a header whose pointer is outside every section is not followed
	binary.LittleEndian.PutUint64(ro[0x120:], 0x10)
	binary.LittleEndian.PutUint64(ro[0x128:], 4)
	b := &Binary{sections: []section{{Name: ".rodata", Addr: base, Size: 0x200, data: ro}}}
	segs, _ := collectData(b, []DataRef{{From: 1, Target: base + 0x100, Kind: "rip-lea"}})
	var got []byte
	for _, s := range segs {
		if s.Base <= base+0x180 && base+0x185 <= s.Base+uint64(len(s.Bytes)) {
			got = s.Bytes[base+0x180-s.Base : base+0x185-s.Base]
		}
	}
	if !bytes.Equal(got, []byte("<nil>")) {
		t.Fatalf("string bytes behind the header not extracted: %v", segs)
	}
	for _, s := range segs {
		if s.Base < base || s.Base >= base+0x200 {
			t.Errorf("segment outside the section: %#x", s.Base)
		}
	}
}

// red team: a pointer into a writable section, into code, a zero or huge length, or past the section end is not followed.
func TestRodataRefNotFollowed(t *testing.T) {
	const base = 0x400000
	mk := func(ptr, n uint64, secs ...section) []DataSeg {
		ro := make([]byte, 0x100)
		binary.LittleEndian.PutUint64(ro[0:], ptr)
		binary.LittleEndian.PutUint64(ro[8:], n)
		all := append([]section{{Name: ".rodata", Addr: base, Size: 0x100, data: ro}}, secs...)
		b := &Binary{sections: all}
		segs, _ := collectData(b, []DataRef{{From: 1, Target: base, Kind: "rip-lea"}})
		return segs
	}
	w := section{Name: ".data", Addr: 0x500000, Size: 0x100, Writable: true, data: make([]byte, 0x100)}
	x := section{Name: ".text", Addr: 0x600000, Size: 0x100, Exec: true, data: make([]byte, 0x100)}
	// a (pointer, small number) pair whose target is not text (a type descriptor field, a pointer table) is not a string header
	bin := func() []DataSeg {
		ro := make([]byte, 0x100)
		binary.LittleEndian.PutUint64(ro[0:], base+0x80)
		binary.LittleEndian.PutUint64(ro[8:], 3)
		copy(ro[0x80:], []byte{0x00, 0x0e, 0xff})
		b := &Binary{sections: []section{{Name: ".rodata", Addr: base, Size: 0x100, data: ro}}}
		segs, _ := collectData(b, []DataRef{{From: 1, Target: base, Kind: "rip-lea"}})
		return segs
	}()
	for name, segs := range map[string][]DataSeg{
		"not text": bin,
		"writable": mk(0x500000, 5, w), "code": mk(0x600000, 5, x), "zero len": mk(base+0x80, 0),
		"huge len": mk(base+0x80, 1<<20), "past end": mk(base+0xfe, 8),
	} {
		if len(segs) != 1 {
			t.Errorf("%s: pointer followed (%d segments)", name, len(segs))
		}
	}
}
