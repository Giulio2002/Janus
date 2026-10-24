// Command cabiprobe is the differential test of Janus's C ABI classification
// (Janus/CABI/AAPCS64.lean, Janus/CABI/SysV.lean) against gcc and clang.
//
// For a corpus of C prototypes (the ABI functions of the C corpus and of the cgo examples, the
// classic edge cases of both ABIs, and seeded random prototypes) it
//
//  1. asks Janus (`lake env lean --run JanusTests/CABIProbe.lean`) where every argument and
//     the result go, the layout of every type, AL, and the va_list states of a variadic call;
//  2. generates, for every prototype, a caller and a callee in C and compiles them with the
//     compiler under test (gcc and clang, -O0 and -O2, arm64 and amd64), together with a fixed
//     driver and two assembly helpers;
//  3. caller test: the compiled caller calls an assembly stub that records every argument
//     register, the stacked-argument area and the memory any of them points to on the stack;
//     each argument's bytes must be where Janus says (registers' low bytes, stack offsets, a
//     pointer to a copy), and AL must bound the vector registers used;
//  4. callee test: an assembly loader places the arguments where Janus says (and a result
//     buffer in X8 / RDI) and calls the compiled callee, which records what it received (and,
//     for a variadic callee, its va_list after va_start and after every va_arg, and its
//     register save areas); every argument must arrive intact, the result must come back where
//     Janus says, the va_list fields must evolve as Janus's vaStart/vaArg say, and Janus's
//     vaArg evaluated on the callee's own save areas must return the values its va_arg read;
//  5. layout: sizeof, _Alignof and the offset of every scalar must match Janus's layout.
//
// Usage: cabiprobe [-root DIR] [-out DIR] [-random N] [-seed S] [-configs LIST]
// Writes <out>/summary.txt and <out>/mismatches.txt; exit status 1 on any mismatch.
package main

import (
	"bufio"
	"bytes"
	_ "embed"
	"flag"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
)

//go:embed stub_arm64.S
var stubArm64 string

//go:embed stub_amd64.S
var stubAmd64 string

// Block layout shared with the assembly helpers.
const (
	blkQ       = 80
	blkStackSz = 208
	blkEntrySP = 216
	blkX87N    = 224
	blkOutR    = 232
	blkOutQ    = 256
	blkOutST   = 320
	blkStack   = 352
	blkSize    = 1376
	maxStack   = 1024
	dumpQ      = 80
	dumpSP     = 208
	dumpStack  = 224
	dumpSize   = 224 + 1024
	nCapt      = 10 + 128
	outSize    = 8192
	valogSave  = 2048
	valogSize  = 2048 + 192
	copySize   = 4096
)

// ---------------------------------------------------------------------------------------
// Janus's predictions

type Leaf struct {
	Off, Len int
	Kind     string
}

type TypeInfo struct {
	Size, Align int
	Leaves      []Leaf
}

type Loc struct {
	Kind byte // 'x' 'v' 's' 't'
	R    int
	Off  int // vector byte offset
}

type Piece struct {
	Loc      Loc
	Src, Len int
}

type Passing struct {
	Indirect bool
	Loc      Loc
	Pieces   []Piece
}

type Pred struct {
	Types   map[string]TypeInfo
	Args    []Passing
	Ret     *Passing
	Stack   int
	VecRegs int
	Va      [][3]int64
}

func parseLoc(s string) Loc {
	switch {
	case strings.HasPrefix(s, "st"):
		n, _ := strconv.Atoi(s[2:])
		return Loc{Kind: 't', R: n}
	case s[0] == 'x':
		n, _ := strconv.Atoi(s[1:])
		return Loc{Kind: 'x', R: n}
	case s[0] == 's':
		n, _ := strconv.Atoi(s[1:])
		return Loc{Kind: 's', R: n}
	case s[0] == 'v':
		p := strings.SplitN(s[1:], ".", 2)
		r, _ := strconv.Atoi(p[0])
		o, _ := strconv.Atoi(p[1])
		return Loc{Kind: 'v', R: r, Off: o}
	}
	panic("loc " + s)
}

func parsePassing(ws []string) Passing {
	if ws[0] == "indirect" {
		return Passing{Indirect: true, Loc: parseLoc(ws[1])}
	}
	var p Passing
	for _, w := range ws[1:] {
		// loc:src+len
		i := strings.LastIndex(w, ":")
		loc := parseLoc(w[:i])
		sl := strings.SplitN(w[i+1:], "+", 2)
		src, _ := strconv.Atoi(sl[0])
		ln, _ := strconv.Atoi(sl[1])
		p.Pieces = append(p.Pieces, Piece{Loc: loc, Src: src, Len: ln})
	}
	return p
}

// runLean feeds lines to the Lean probe and returns its output lines.
func runLean(root string, lines []string) ([]string, error) {
	cmd := exec.Command("lake", "env", "lean", "--run", "JanusTests/CABIProbe.lean")
	cmd.Dir = root
	cmd.Env = append(os.Environ(), "LEAN_NUM_THREADS=4")
	cmd.Stdin = strings.NewReader(strings.Join(lines, "\n") + "\n")
	var out, errb bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &errb
	if err := cmd.Run(); err != nil {
		return nil, fmt.Errorf("lean probe: %v: %s", err, errb.String())
	}
	return strings.Split(strings.TrimSpace(out.String()), "\n"), nil
}

// parsePreds parses the prediction blocks: id -> abi -> Pred.
func parsePreds(lines []string) (map[string]map[string]*Pred, error) {
	res := map[string]map[string]*Pred{}
	var cur *Pred
	for _, l := range lines {
		ws := strings.Fields(l)
		if len(ws) == 0 {
			continue
		}
		switch ws[0] {
		case "error":
			return nil, fmt.Errorf("lean: %s", l)
		case "sig":
			cur = &Pred{Types: map[string]TypeInfo{}}
			if res[ws[1]] == nil {
				res[ws[1]] = map[string]*Pred{}
			}
			res[ws[1]][ws[2]] = cur
		case "type":
			ti := TypeInfo{}
			ti.Size, _ = strconv.Atoi(ws[3])
			ti.Align, _ = strconv.Atoi(ws[5])
			if len(ws) > 7 && ws[7] != "" {
				for _, lf := range strings.Split(ws[7], ",") {
					p := strings.Split(lf, ":")
					o, _ := strconv.Atoi(p[0])
					n, _ := strconv.Atoi(p[1])
					ti.Leaves = append(ti.Leaves, Leaf{o, n, p[2]})
				}
			}
			cur.Types[ws[1]] = ti
		case "arg":
			cur.Args = append(cur.Args, parsePassing(ws[2:]))
		case "ret":
			if ws[1] != "void" {
				p := parsePassing(ws[1:])
				cur.Ret = &p
			}
		case "stack":
			cur.Stack, _ = strconv.Atoi(ws[1])
		case "vecregs":
			cur.VecRegs, _ = strconv.Atoi(ws[1])
		case "va":
			var v [3]int64
			for i := 0; i < 3; i++ {
				v[i], _ = strconv.ParseInt(ws[2+i], 10, 64)
			}
			cur.Va = append(cur.Va, v)
		case "end":
		}
	}
	return res, nil
}

// ---------------------------------------------------------------------------------------
// Configurations

type Config struct {
	ISA, CC, Opt string
}

func (c Config) String() string { return c.ISA + "/" + c.CC + "/" + c.Opt }

func (c Config) cut() []string {
	switch {
	case c.ISA == "arm64" && c.CC == "gcc":
		return []string{"aarch64-linux-gnu-gcc"}
	case c.ISA == "arm64":
		return []string{"clang", "--target=aarch64-linux-gnu"}
	case c.CC == "gcc":
		return []string{"gcc"}
	}
	return []string{"clang"}
}

func (c Config) driverCC() string {
	if c.ISA == "arm64" {
		return "aarch64-linux-gnu-gcc"
	}
	return "gcc"
}

func (c Config) abi() string {
	if c.ISA == "arm64" {
		return "aapcs64"
	}
	return "sysv"
}

// ---------------------------------------------------------------------------------------
// Values

// value returns the bytes of argument k ("r" for the result) of a test: random, with every
// floating-point scalar made finite (and x87 values normal) so that copies through FP
// registers are exact.
func value(id, k string, ti TypeInfo, isa string) []byte {
	h := int64(0)
	for _, c := range id + "/" + k {
		h = h*131 + int64(c)
	}
	r := rand.New(rand.NewSource(h))
	b := make([]byte, ti.Size)
	r.Read(b)
	for _, lf := range ti.Leaves {
		switch lf.Kind {
		case "s":
			switch lf.Len {
			case 2:
				b[lf.Off+1] &= 0x3f
			case 4:
				b[lf.Off+3] &= 0x3f
			case 8:
				b[lf.Off+7] &= 0x3f
			}
		case "x":
			if isa == "arm64" {
				b[lf.Off+15] &= 0x3f
			} else {
				b[lf.Off+7] |= 0x80
				b[lf.Off+8] |= 0x01
				b[lf.Off+9] &= 0x3f
			}
		}
	}
	return b
}

// mask returns the significant bytes of a type: its scalars (an x87 long double is 10 bytes;
// an AAPCS64 one, binary128, all 16).
func mask(ti TypeInfo, isa string) []bool {
	m := make([]bool, ti.Size)
	for _, lf := range ti.Leaves {
		n := lf.Len
		if lf.Kind == "x" && isa == "arm64" {
			n = 16
		}
		for i := 0; i < n && lf.Off+i < ti.Size; i++ {
			m[lf.Off+i] = true
		}
	}
	return m
}

// ---------------------------------------------------------------------------------------
// Code generation

type testGen struct {
	sig   *Sig
	pred  *Pred
	isa   string
	tname string
	vals  map[string][]byte
	// layout of the callee's records
	outOff []int
	outLen int
}

func cIdent(id string) string { return strings.ReplaceAll(id, "-", "_") }

func bytesLit(b []byte) string {
	if len(b) == 0 {
		return "{0}"
	}
	var sb strings.Builder
	sb.WriteString("{")
	for i, x := range b {
		if i > 0 {
			sb.WriteString(",")
		}
		fmt.Fprintf(&sb, "%d", x)
	}
	sb.WriteString("}")
	return sb.String()
}

// leafExprs returns C expressions for the offsets of the scalars of t (in the order of
// Janus's CType.leaves), relative to `base` (an offsetof designator, or "" at top level).
func leafExprs(c *cdecls, tname, path string, t *Ty) []string {
	off := func(p string) string {
		if p == "" {
			return "0"
		}
		return fmt.Sprintf("__builtin_offsetof(%s, %s)", tname, p)
	}
	switch t.K {
	case "cf", "cd", "cld":
		base := map[string]string{"cf": "float", "cd": "double", "cld": "long double"}[t.K]
		return []string{off(path), fmt.Sprintf("%s + sizeof(%s)", off(path), base)}
	case "s", "un":
		var res []string
		for i, e := range t.Elems {
			p := fmt.Sprintf("f%d", i)
			if path != "" {
				p = path + "." + p
			}
			if e.K == "a" {
				for j := 0; j < e.N; j++ {
					res = append(res, leafExprs(c, tname, fmt.Sprintf("%s[%d]", p, j), e.Elems[0])...)
				}
			} else {
				res = append(res, leafExprs(c, tname, p, e)...)
			}
		}
		return res
	}
	return []string{off(path)}
}

func genTests(isa string, sigs []*Sig, preds map[string]map[string]*Pred) (types, tests, driver string, gens []*testGen) {
	abi := "aapcs64"
	if isa == "amd64" {
		abi = "sysv"
	}
	var th, tc, dr strings.Builder
	th.WriteString("#include <stddef.h>\ntypedef int probe_v8_t __attribute__((vector_size(8)));\n" +
		"typedef int probe_v16_t __attribute__((vector_size(16)));\n")
	tc.WriteString("#include <string.h>\n#include <stdarg.h>\n#include \"types.h\"\n" +
		"extern unsigned char probe_out[], probe_valog[];\n")
	for _, s := range sigs {
		id := cIdent(s.ID)
		pred := preds[s.ID][abi]
		g := &testGen{sig: s, pred: pred, isa: isa, vals: map[string][]byte{}}
		gens = append(gens, g)
		cd := &cdecls{prefix: "probe_" + id}
		argT := make([]string, len(s.Args))
		for i, a := range s.Args {
			argT[i] = cd.cname(a)
		}
		retT := "void"
		if s.Ret != nil {
			retT = cd.cname(s.Ret)
		}
		for _, d := range cd.defs {
			th.WriteString(d + "\n")
		}
		for i := range s.Args {
			fmt.Fprintf(&th, "typedef %s T_%s_%d;\n", argT[i], id, i)
		}
		fmt.Fprintf(&th, "typedef %s R_%s;\n", retT, id)
		// values
		for i := range s.Args {
			k := strconv.Itoa(i)
			g.vals[k] = value(s.ID, k, pred.Types[k], isa)
		}
		if s.Ret != nil {
			g.vals["r"] = value(s.ID, "r", pred.Types["r"], isa)
		}
		// prototype parameter lists
		var params, decl []string
		for i := range s.Args {
			if s.Named >= 0 && i >= s.Named {
				break
			}
			params = append(params, fmt.Sprintf("T_%s_%d a%d", id, i, i))
			decl = append(decl, fmt.Sprintf("T_%s_%d", id, i))
		}
		if s.Named >= 0 {
			params = append(params, "...")
			decl = append(decl, "...")
		}
		if len(params) == 0 {
			params = []string{"void"}
			decl = []string{"void"}
		}
		// caller
		fmt.Fprintf(&tc, "extern R_%s probe_dumpstub_%s(%s);\n", id, id, strings.Join(decl, ", "))
		for i := range s.Args {
			fmt.Fprintf(&tc, "static const unsigned char val_%s_%d[] = %s;\n", id, i, bytesLit(g.vals[strconv.Itoa(i)]))
		}
		fmt.Fprintf(&tc, "void caller_%s(void) {\n", id)
		var actuals []string
		for i := range s.Args {
			fmt.Fprintf(&tc, "\tT_%s_%d a%d; memcpy(&a%d, val_%s_%d, sizeof a%d);\n", id, i, i, i, id, i, i)
			actuals = append(actuals, fmt.Sprintf("a%d", i))
		}
		fmt.Fprintf(&tc, "\tprobe_dumpstub_%s(%s);\n}\n", id, strings.Join(actuals, ", "))
		// callee
		if s.Ret != nil {
			fmt.Fprintf(&tc, "static const unsigned char retv_%s[] = %s;\n", id, bytesLit(g.vals["r"]))
		}
		fmt.Fprintf(&tc, "R_%s callee_%s(%s) {\n", id, id, strings.Join(params, ", "))
		off := 0
		for i := range s.Args {
			off = (off + 15) / 16 * 16
			g.outOff = append(g.outOff, off)
			sz := pred.Types[strconv.Itoa(i)].Size
			if s.Named >= 0 && i >= s.Named {
				fmt.Fprintf(&tc, "\t{ T_%s_%d v = va_arg(ap, T_%s_%d); memcpy(probe_out + %d, &v, sizeof v); memcpy(probe_valog + %d, &ap, sizeof ap); }\n",
					id, i, id, i, off, 32*(i-s.Named+1))
			} else {
				fmt.Fprintf(&tc, "\tmemcpy(probe_out + %d, &a%d, sizeof a%d);\n", off, i, i)
			}
			if s.Named >= 0 && i == s.Named-1 {
				fmt.Fprintf(&tc, "\tva_list ap; va_start(ap, a%d); memcpy(probe_valog, &ap, sizeof ap);\n", i)
				if isa == "amd64" {
					fmt.Fprintf(&tc, "\tmemcpy(probe_valog + %d, ((void **)ap)[2], 176);\n", valogSave)
				} else {
					fmt.Fprintf(&tc, "\tmemcpy(probe_valog + %d, (char *)((void **)&ap)[1] - 64, 64);\n", valogSave)
					fmt.Fprintf(&tc, "\tmemcpy(probe_valog + %d, (char *)((void **)&ap)[2] - 128, 128);\n", valogSave+64)
				}
			}
			off += sz
		}
		if s.Named >= 0 {
			if len(s.Args) == s.Named {
				// no variadic argument: va_start/va_end only
			}
			tc.WriteString("\tva_end(ap);\n")
		}
		g.outLen = off
		if s.Ret != nil {
			fmt.Fprintf(&tc, "\tR_%s r; memcpy(&r, retv_%s, sizeof r); return r;\n", id, id)
		}
		tc.WriteString("}\n")
		// layout records
		var lay []string
		addLay := func(tn string, t *Ty) {
			lay = append(lay, fmt.Sprintf("sizeof(%s)", tn), fmt.Sprintf("_Alignof(%s)", tn))
			les := leafExprs(cd, tn, "", t)
			lay = append(lay, strconv.Itoa(len(les)))
			lay = append(lay, les...)
		}
		for i, a := range s.Args {
			addLay(fmt.Sprintf("T_%s_%d", id, i), a)
		}
		if s.Ret != nil {
			addLay("R_"+id, s.Ret)
		}
		if len(lay) == 0 {
			lay = []string{"0"}
		}
		fmt.Fprintf(&tc, "const unsigned long lay_%s[] = {%s};\nconst int nlay_%s = %d;\n", id, strings.Join(lay, ", "), id, len(lay))
	}
	types = th.String()
	tests = tc.String()
	dr.WriteString(genDriver(isa, gens))
	driver = dr.String()
	return
}

// gprSlot: the block/dump slot of a general register by hardware number.
func gprSlot(isa string, r int) int {
	if isa == "arm64" {
		return 8 * r
	}
	m := map[int]int{7: 0, 6: 1, 2: 2, 1: 3, 8: 4, 9: 5, 0: 6}
	if s, ok := m[r]; ok {
		return 8 * s
	}
	return -1
}

// resSlot: the block slot of a result location.
func resSlot(isa string, l Loc) int {
	switch l.Kind {
	case 'x':
		if isa == "arm64" {
			return blkOutR + 8*l.R
		}
		if l.R == 0 {
			return blkOutR
		}
		if l.R == 2 {
			return blkOutR + 8
		}
	case 'v':
		return blkOutQ + 16*l.R + l.Off
	case 't':
		return blkOutST + 16*l.R
	}
	return -1
}

// blockImage lays out the callee test's block from Janus's prediction: the image, the
// pointer patches (offset in the block, offset in the copy buffer or -1 for the result
// buffer), the copy buffer, and the x87 result count.
func (g *testGen) blockImage() (img []byte, patches [][2]int, copies []byte, err error) {
	img = make([]byte, blkSize)
	for i := 0; i < blkStackSz; i++ {
		img[i] = 0xa5
	}
	stackSz := (g.pred.Stack + 15) / 16 * 16
	if stackSz > maxStack {
		return nil, nil, nil, fmt.Errorf("stack area %d too large", stackSz)
	}
	for i := 0; i < stackSz; i++ {
		img[blkStack+i] = 0x5a
	}
	putLE(img[blkStackSz:], uint64(stackSz))
	put := func(l Loc, b []byte) error {
		switch l.Kind {
		case 'x':
			s := gprSlot(g.isa, l.R)
			if s < 0 || len(b) > 8 {
				return fmt.Errorf("bad gpr %d", l.R)
			}
			copy(img[s:], b)
		case 'v':
			if l.R > 7 || l.Off+len(b) > 16 {
				return fmt.Errorf("bad vec %d", l.R)
			}
			copy(img[blkQ+16*l.R+l.Off:], b)
		case 's':
			if l.R+len(b) > stackSz {
				return fmt.Errorf("stack piece beyond the area")
			}
			copy(img[blkStack+l.R:], b)
		default:
			return fmt.Errorf("argument location %c", l.Kind)
		}
		return nil
	}
	slotOff := func(l Loc) (int, error) {
		switch l.Kind {
		case 'x':
			s := gprSlot(g.isa, l.R)
			if s < 0 {
				return 0, fmt.Errorf("bad gpr")
			}
			return s, nil
		case 's':
			return blkStack + l.R, nil
		}
		return 0, fmt.Errorf("pointer location %c", l.Kind)
	}
	for i, p := range g.pred.Args {
		v := g.vals[strconv.Itoa(i)]
		if p.Indirect {
			off := (len(copies) + 15) / 16 * 16
			for len(copies) < off {
				copies = append(copies, 0)
			}
			copies = append(copies, v...)
			so, e := slotOff(p.Loc)
			if e != nil {
				return nil, nil, nil, e
			}
			patches = append(patches, [2]int{so, off})
			continue
		}
		for _, pc := range p.Pieces {
			if pc.Src+pc.Len > len(v) {
				return nil, nil, nil, fmt.Errorf("piece beyond the value")
			}
			if e := put(pc.Loc, v[pc.Src:pc.Src+pc.Len]); e != nil {
				return nil, nil, nil, e
			}
		}
	}
	if g.pred.Ret != nil && g.pred.Ret.Indirect {
		so, e := slotOff(g.pred.Ret.Loc)
		if e != nil {
			return nil, nil, nil, e
		}
		patches = append(patches, [2]int{so, -1})
	}
	x87 := 0
	if g.pred.Ret != nil && !g.pred.Ret.Indirect {
		for _, pc := range g.pred.Ret.Pieces {
			if pc.Loc.Kind == 't' {
				x87++
			}
		}
	}
	putLE(img[blkX87N:], uint64(x87))
	if g.isa == "amd64" && g.sig.Named >= 0 {
		// AL: Janus's bound on the vector registers; the rest of RAX is garbage
		img[gprSlot("amd64", 0)] = byte(g.pred.VecRegs)
	}
	if len(copies) > copySize {
		return nil, nil, nil, fmt.Errorf("copies too large")
	}
	return
}

func putLE(b []byte, v uint64) {
	for i := 0; i < 8; i++ {
		b[i] = byte(v >> (8 * i))
	}
}

func getLE(b []byte) uint64 {
	var v uint64
	for i := 0; i < 8 && i < len(b); i++ {
		v |= uint64(b[i]) << (8 * i)
	}
	return v
}

func genDriver(isa string, gens []*testGen) string {
	var d strings.Builder
	d.WriteString(`#include <stdio.h>
#include <string.h>
#include "types.h"
unsigned char probe_dumparea[` + strconv.Itoa(dumpSize) + `] __attribute__((aligned(16)));
unsigned long probe_capt_val[` + strconv.Itoa(nCapt) + `];
int probe_capt_ok[` + strconv.Itoa(nCapt) + `];
unsigned char probe_capt_mem[` + strconv.Itoa(nCapt) + `][256];
unsigned char probe_out[` + strconv.Itoa(outSize) + `] __attribute__((aligned(16)));
unsigned char probe_valog[` + strconv.Itoa(valogSize) + `] __attribute__((aligned(16)));
unsigned char probe_copies[` + strconv.Itoa(copySize) + `] __attribute__((aligned(16)));
unsigned char probe_sret[512] __attribute__((aligned(16)));
unsigned char probe_blk[` + strconv.Itoa(blkSize) + `] __attribute__((aligned(16)));
extern void probe_load(void *blk, void *fn);
unsigned long probe_stack_top;
void probe_capture(void) {
	unsigned long sp;
	memcpy(&sp, probe_dumparea + ` + strconv.Itoa(dumpSP) + `, 8);
	for (int i = 0; i < ` + strconv.Itoa(nCapt) + `; i++) {
		unsigned long v;
		if (i < 10) memcpy(&v, probe_dumparea + 8 * i, 8);
		else memcpy(&v, probe_dumparea + ` + strconv.Itoa(dumpStack) + ` + 8 * (i - 10), 8);
		probe_capt_val[i] = v;
		probe_capt_ok[i] = v >= sp && v < probe_stack_top;
		if (probe_capt_ok[i]) memcpy(probe_capt_mem[i], (void *)v, 256);
	}
}
static void hex(const char *tag, const void *p, int n) {
	const unsigned char *b = p;
	printf(" %s ", tag);
	for (int i = 0; i < n; i++) printf("%02x", b[i]);
	if (n == 0) printf("-");
}
`)
	for _, g := range gens {
		id := cIdent(g.sig.ID)
		fmt.Fprintf(&d, "extern void caller_%s(void);\nextern char callee_%s[];\nextern const unsigned long lay_%s[];\nextern const int nlay_%s;\n", id, id, id, id)
		img, patches, copies, err := g.blockImage()
		if err != nil {
			fmt.Fprintf(&d, "static void test_%s(void) { printf(\"X %s %s\\n\"); }\n", id, g.sig.ID, strings.ReplaceAll(err.Error(), " ", "_"))
			continue
		}
		fmt.Fprintf(&d, "static const unsigned char blk_%s[] = %s;\n", id, bytesLit(img))
		fmt.Fprintf(&d, "static const unsigned char cp_%s[] = %s;\n", id, bytesLit(copies))
		fmt.Fprintf(&d, "static void test_%s(void) {\n", id)
		fmt.Fprintf(&d, "\tmemset(probe_dumparea, 0, sizeof probe_dumparea); memset(probe_capt_ok, 0, sizeof probe_capt_ok);\n")
		fmt.Fprintf(&d, "\tcaller_%s();\n", id)
		if isa == "amd64" {
			d.WriteString("\t__asm__ volatile(\"fninit\");\n")
		}
		fmt.Fprintf(&d, "\tprintf(\"C %s\"); hex(\"d\", probe_dumparea, %d);\n", g.sig.ID, dumpSize)
		fmt.Fprintf(&d, "\tfor (int i = 0; i < %d; i++) if (probe_capt_ok[i]) { printf(\" c%%d:%%lx\", i, probe_capt_val[i]); hex(\"m\", probe_capt_mem[i], 256); }\n\tprintf(\"\\n\");\n", nCapt)
		fmt.Fprintf(&d, "\tprintf(\"L %s\"); for (int i = 0; i < nlay_%s; i++) printf(\" %%lu\", lay_%s[i]); printf(\"\\n\");\n", g.sig.ID, id, id)
		fmt.Fprintf(&d, "\tmemcpy(probe_blk, blk_%s, sizeof probe_blk); memcpy(probe_copies, cp_%s, sizeof cp_%s);\n", id, id, id)
		d.WriteString("\tmemset(probe_sret, 0xee, sizeof probe_sret); memset(probe_out, 0, sizeof probe_out); memset(probe_valog, 0, sizeof probe_valog);\n")
		for _, p := range patches {
			if p[1] < 0 {
				fmt.Fprintf(&d, "\t{ unsigned long a = (unsigned long)probe_sret; memcpy(probe_blk + %d, &a, 8); }\n", p[0])
			} else {
				fmt.Fprintf(&d, "\t{ unsigned long a = (unsigned long)(probe_copies + %d); memcpy(probe_blk + %d, &a, 8); }\n", p[1], p[0])
			}
		}
		fmt.Fprintf(&d, "\tprobe_load(probe_blk, (void *)callee_%s);\n", id)
		retSize := 0
		if g.sig.Ret != nil {
			retSize = g.pred.Types["r"].Size
		}
		fmt.Fprintf(&d, "\tprintf(\"E %s\"); hex(\"out\", probe_out, %d); hex(\"r\", probe_blk + %d, %d); hex(\"sret\", probe_sret, %d);\n",
			g.sig.ID, g.outLen, blkOutR, blkStack-blkOutR, retSize)
		fmt.Fprintf(&d, "\tprintf(\" sretaddr %%lx copies %%lx\", (unsigned long)probe_sret, (unsigned long)probe_copies); hex(\"entrysp\", probe_blk + %d, 8);\n", blkEntrySP)
		fmt.Fprintf(&d, "\thex(\"stack\", probe_blk + %d, %d); hex(\"cp\", probe_copies, %d);", blkStack, (g.pred.Stack+15)/16*16, len(copies))
		if g.sig.Named >= 0 {
			fmt.Fprintf(&d, " hex(\"valog\", probe_valog, %d);", valogSize)
		}
		d.WriteString(" printf(\"\\n\");\n}\n")
	}
	d.WriteString("int main(void) {\n\tprobe_stack_top = (unsigned long)__builtin_frame_address(0);\n\tsetvbuf(stdout, NULL, _IOFBF, 1 << 20);\n")
	for _, g := range gens {
		fmt.Fprintf(&d, "\ttest_%s();\n", cIdent(g.sig.ID))
	}
	d.WriteString("\treturn 0;\n}\n")
	return d.String()
}

func genStubAliases(isa string, sigs []*Sig) string {
	var b strings.Builder
	if isa == "arm64" {
		b.WriteString(stubArm64)
	} else {
		b.WriteString(stubAmd64)
	}
	b.WriteString("\t.text\n")
	for _, s := range sigs {
		id := cIdent(s.ID)
		fmt.Fprintf(&b, "\t.globl probe_dumpstub_%s\n\t.set probe_dumpstub_%s, probe_dump\n", id, id)
	}
	return b.String()
}

// ---------------------------------------------------------------------------------------
// Running and checking

type result struct {
	cfg        Config
	tests      int
	failed     map[string][]string // test id -> problems
	known      map[string][]string // test id -> failures that are a documented compiler bug
	checks     int
	buildError string
}

func run(cmd []string, dir string) (string, error) {
	c := exec.Command(cmd[0], cmd[1:]...)
	c.Dir = dir
	var out bytes.Buffer
	c.Stdout = &out
	c.Stderr = &out
	err := c.Run()
	return out.String(), err
}

func decodeHex(s string) []byte {
	if s == "-" {
		return nil
	}
	b := make([]byte, len(s)/2)
	for i := range b {
		v, _ := strconv.ParseUint(s[2*i:2*i+2], 16, 8)
		b[i] = byte(v)
	}
	return b
}

// fields of a driver output line: tag -> hex string
func lineFields(ws []string) map[string]string {
	m := map[string]string{}
	for i := 2; i+1 < len(ws); i += 2 {
		m[ws[i]] = ws[i+1]
	}
	return m
}

func runConfig(root, work string, cfg Config, sigs []*Sig, preds map[string]map[string]*Pred, types, tests, driver, stub string, gens []*testGen) *result {
	res := &result{cfg: cfg, failed: map[string][]string{}, known: map[string][]string{}}
	dir := filepath.Join(work, strings.ReplaceAll(cfg.String(), "/", "-"))
	os.MkdirAll(dir, 0o755)
	os.WriteFile(filepath.Join(dir, "types.h"), []byte(types), 0o644)
	os.WriteFile(filepath.Join(dir, "tests.c"), []byte(tests), 0o644)
	os.WriteFile(filepath.Join(dir, "driver.c"), []byte(driver), 0o644)
	os.WriteFile(filepath.Join(dir, "stub.S"), []byte(stub), 0o644)
	cut := append(cfg.cut(), "-"+cfg.Opt, "-fPIC", "-w", "-c", "tests.c", "-o", "tests.o")
	if out, err := run(cut, dir); err != nil {
		res.buildError = "compile tests.c: " + out
		return res
	}
	dcc := cfg.driverCC()
	for _, c := range [][]string{
		{dcc, "-O0", "-w", "-c", "driver.c", "-o", "driver.o"},
		{dcc, "-c", "stub.S", "-o", "stub.o"},
		{dcc, "driver.o", "stub.o", "tests.o", "-o", "probe"},
	} {
		if out, err := run(c, dir); err != nil {
			res.buildError = strings.Join(c, " ") + ": " + out
			return res
		}
	}
	var runCmd []string
	if cfg.ISA == "arm64" {
		runCmd = []string{"qemu-aarch64", "-L", "/usr/aarch64-linux-gnu", "./probe"}
	} else {
		runCmd = []string{"./probe"}
	}
	out, err := run(runCmd, dir)
	if err != nil {
		res.buildError = "run: " + err.Error() + ": " + lastLines(out, 5)
		return res
	}
	os.WriteFile(filepath.Join(dir, "probe.out"), []byte(out), 0o644)
	byID := map[string]*testGen{}
	for _, g := range gens {
		byID[g.sig.ID] = g
	}
	seen := map[string]bool{}
	var vaQueries []string
	vaWant := map[string][]byte{} // "id k" -> callee's va_arg bytes
	sc := bufio.NewScanner(strings.NewReader(out))
	sc.Buffer(make([]byte, 1<<20), 1<<26)
	for sc.Scan() {
		ws := strings.Fields(sc.Text())
		if len(ws) < 2 {
			continue
		}
		g := byID[ws[1]]
		if g == nil {
			continue
		}
		seen[ws[1]] = true
		fail := func(f string, a ...any) {
			res.failed[ws[1]] = append(res.failed[ws[1]], fmt.Sprintf(f, a...))
		}
		switch ws[0] {
		case "X":
			fail("cannot lay out the callee test: %s", ws[2])
		case "C":
			res.checks += checkCaller(g, ws, fail)
		case "L":
			res.checks += checkLayout(g, ws[2:], fail)
		case "E":
			n, qs := checkCallee(g, ws, fail, vaWant)
			res.checks += n
			vaQueries = append(vaQueries, qs...)
		}
	}
	// Janus's va_arg on the callees' own memory
	if len(vaQueries) > 0 {
		lines, err := runLean(root, vaQueries)
		if err != nil {
			res.buildError = "vaeval: " + err.Error()
			return res
		}
		for _, l := range lines {
			ws := strings.Fields(l)
			if len(ws) == 4 && ws[0] == "vaval" {
				g := byID[ws[1]]
				k, _ := strconv.Atoi(ws[2])
				want := vaWant[ws[1]+" "+ws[2]]
				got := decodeHex(ws[3])
				i := g.sig.Named + k - 1
				m := mask(g.pred.Types[strconv.Itoa(i)], g.isa)
				res.checks++
				if !maskedEq(want, got, m) {
					res.failed[ws[1]] = append(res.failed[ws[1]], fmt.Sprintf("va_arg #%d (%s): Janus's vaArg on the callee's save areas gives %x, the callee's va_arg %x", k, g.sig.Args[i], got, want))
				}
			} else if strings.HasPrefix(l, "error") {
				res.buildError = "vaeval: " + l
			}
		}
	}
	for id, ps := range res.failed {
		if knownBug(cfg, byID[id].sig) {
			res.known[id] = ps
			delete(res.failed, id)
		}
	}
	for _, s := range sigs {
		if !seen[s.ID] {
			res.failed[s.ID] = append(res.failed[s.ID], "no output (the probe crashed?)")
		}
	}
	res.tests = len(sigs)
	return res
}

// homogeneousOf reports whether every scalar of t is of kind k.
func homogeneousOf(t *Ty, k string) bool {
	switch t.K {
	case "s", "un", "a":
		for _, e := range t.Elems {
			if !homogeneousOf(e, k) {
				return false
			}
		}
		return true
	case "v":
		return k == fmt.Sprintf("v%d", t.N)
	}
	return t.K == k
}

// knownBug: the compiler bugs the probe found, which are excluded from the verdict and
// listed in known-bugs.txt. gcc 15.2 at -O2 on arm64 miscompiles va_arg of a homogeneous
// aggregate of _Float16 or of short vectors (HFA/HVA of h, v8, v16): the value is read from an
// unrelated stack slot (gcc -O0 and clang -O0/-O2 read it from the SIMD&FP save area, as
// AAPCS64 and Janus say). Only a variadic test of such an aggregate is affected.
func knownBug(cfg Config, s *Sig) bool {
	if cfg.ISA != "arm64" || cfg.CC != "gcc" || cfg.Opt != "O2" || s.Named < 0 {
		return false
	}
	for _, a := range s.Args[s.Named:] {
		if a.K == "s" || a.K == "un" {
			for _, k := range []string{"h", "v8", "v16"} {
				if homogeneousOf(a, k) {
					return true
				}
			}
		}
	}
	return false
}

func lastLines(s string, n int) string {
	ls := strings.Split(strings.TrimSpace(s), "\n")
	if len(ls) > n {
		ls = ls[len(ls)-n:]
	}
	return strings.Join(ls, " | ")
}

func maskedEq(a, b []byte, m []bool) bool {
	for i := range m {
		if !m[i] {
			continue
		}
		if i >= len(a) || i >= len(b) || a[i] != b[i] {
			return false
		}
	}
	return true
}

func locName(isa string, l Loc) string {
	switch l.Kind {
	case 'x':
		if isa == "amd64" {
			return map[int]string{0: "RAX", 1: "RCX", 2: "RDX", 3: "RBX", 6: "RSI", 7: "RDI", 8: "R8", 9: "R9"}[l.R]
		}
		return fmt.Sprintf("X%d", l.R)
	case 'v':
		if isa == "amd64" {
			return fmt.Sprintf("XMM%d[%d..]", l.R, l.Off)
		}
		return fmt.Sprintf("V%d", l.R)
	case 's':
		return fmt.Sprintf("stack+%d", l.R)
	case 't':
		return fmt.Sprintf("ST%d", l.R)
	}
	return "?"
}

// checkCaller: the arguments the compiled caller passed are where Janus says.
func checkCaller(g *testGen, ws []string, fail func(string, ...any)) int {
	d := decodeHex(lineFields(ws)["d"])
	capt := map[uint64][]byte{}
	for i := 2; i < len(ws); i++ {
		if strings.HasPrefix(ws[i], "c") && strings.Contains(ws[i], ":") && i+2 < len(ws) && ws[i+1] == "m" {
			p := strings.SplitN(ws[i], ":", 2)
			v, _ := strconv.ParseUint(p[1], 16, 64)
			capt[v] = decodeHex(ws[i+2])
		}
	}
	if len(d) != dumpSize {
		fail("caller dump missing")
		return 0
	}
	read := func(l Loc, n int) ([]byte, bool) {
		switch l.Kind {
		case 'x':
			s := gprSlot(g.isa, l.R)
			if s < 0 || n > 8 {
				return nil, false
			}
			return d[s : s+n], true
		case 'v':
			o := dumpQ + 16*l.R + l.Off
			return d[o : o+n], true
		case 's':
			if l.R+n > 1024 {
				return nil, false
			}
			return d[dumpStack+l.R : dumpStack+l.R+n], true
		}
		return nil, false
	}
	checks := 0
	for i, p := range g.pred.Args {
		k := strconv.Itoa(i)
		v := g.vals[k]
		m := mask(g.pred.Types[k], g.isa)
		checks++
		if p.Indirect {
			pb, ok := read(p.Loc, 8)
			if !ok {
				fail("arg %d: cannot read %s", i, locName(g.isa, p.Loc))
				continue
			}
			mem, ok := capt[getLE(pb)]
			if !ok || !maskedEq(v, mem, m) {
				fail("arg %d (%s): Janus says a pointer to a copy in %s; the caller passed %x there", i, g.sig.Args[i], locName(g.isa, p.Loc), pb)
			}
			continue
		}
		got := make([]byte, len(v))
		for _, pc := range p.Pieces {
			b, ok := read(pc.Loc, pc.Len)
			if !ok {
				fail("arg %d: cannot read %s", i, locName(g.isa, pc.Loc))
				continue
			}
			copy(got[pc.Src:], b)
		}
		if !maskedEq(v, got, m) {
			var where []string
			for _, pc := range p.Pieces {
				where = append(where, fmt.Sprintf("%s:%d+%d", locName(g.isa, pc.Loc), pc.Src, pc.Len))
			}
			fail("arg %d (%s): Janus says %s; the caller passed %x there, the value is %x", i, g.sig.Args[i], strings.Join(where, " "), got, v)
		}
	}
	if g.pred.Ret != nil && g.pred.Ret.Indirect {
		checks++
		pb, _ := read(g.pred.Ret.Loc, 8)
		if _, ok := capt[getLE(pb)]; !ok {
			fail("result: Janus says a result buffer in %s; the caller passed %x (not its stack)", locName(g.isa, g.pred.Ret.Loc), pb)
		}
	}
	if g.isa == "amd64" && g.sig.Named >= 0 {
		checks++
		al := int(d[gprSlot("amd64", 0)])
		if al < g.pred.VecRegs || al > 8 {
			fail("AL = %d, Janus: at least %d (and at most 8)", al, g.pred.VecRegs)
		}
	}
	return checks
}

// checkLayout: sizeof, _Alignof and the scalar offsets.
func checkLayout(g *testGen, ws []string, fail func(string, ...any)) int {
	nums := make([]int, len(ws))
	for i, w := range ws {
		nums[i], _ = strconv.Atoi(w)
	}
	checks := 0
	pos := 0
	keys := []string{}
	for i := range g.sig.Args {
		keys = append(keys, strconv.Itoa(i))
	}
	if g.sig.Ret != nil {
		keys = append(keys, "r")
	}
	for _, k := range keys {
		ti := g.pred.Types[k]
		if pos+3 > len(nums) {
			fail("layout record short")
			return checks
		}
		checks++
		if nums[pos] != ti.Size || nums[pos+1] != ti.Align {
			fail("type %s: sizeof %d _Alignof %d, Janus %d %d", k, nums[pos], nums[pos+1], ti.Size, ti.Align)
		}
		n := nums[pos+2]
		if n != len(ti.Leaves) {
			fail("type %s: %d scalars, Janus %d", k, n, len(ti.Leaves))
		} else {
			for j := 0; j < n; j++ {
				if nums[pos+3+j] != ti.Leaves[j].Off {
					fail("type %s: scalar %d at offset %d, Janus %d", k, j, nums[pos+3+j], ti.Leaves[j].Off)
				}
			}
		}
		pos += 3 + n
	}
	return checks
}

// checkCallee: the compiled callee received the arguments Janus placed and returned the result
// where Janus says; for a variadic callee, its va_list states. Returns the vaeval queries.
func checkCallee(g *testGen, ws []string, fail func(string, ...any), vaWant map[string][]byte) (int, []string) {
	f := lineFields(ws)
	out := decodeHex(f["out"])
	r := decodeHex(f["r"])
	sret := decodeHex(f["sret"])
	entry := getLE(decodeHex(f["entrysp"]))
	sretAddr, _ := strconv.ParseUint(f["sretaddr"], 16, 64)
	copiesAddr, _ := strconv.ParseUint(f["copies"], 16, 64)
	checks := 0
	for i := range g.sig.Args {
		k := strconv.Itoa(i)
		v := g.vals[k]
		m := mask(g.pred.Types[k], g.isa)
		got := out[g.outOff[i] : g.outOff[i]+len(v)]
		if g.sig.Named >= 0 && i >= g.sig.Named {
			vaWant[fmt.Sprintf("%s %d", g.sig.ID, i-g.sig.Named+1)] = got
		}
		checks++
		if !maskedEq(v, got, m) {
			fail("arg %d (%s): placed by Janus's classification, the callee received %x, want %x", i, g.sig.Args[i], got, v)
		}
	}
	if g.pred.Ret != nil {
		v := g.vals["r"]
		m := mask(g.pred.Types["r"], g.isa)
		checks++
		if g.pred.Ret.Indirect {
			if !maskedEq(v, sret, m) {
				fail("result (%s): Janus says through the buffer in %s; the buffer holds %x, want %x", g.sig.Ret, locName(g.isa, g.pred.Ret.Loc), sret, v)
			}
			if g.isa == "amd64" {
				checks++
				if getLE(r[0:8]) != sretAddr {
					fail("result: RAX = %x, Janus: the buffer address %x", getLE(r[0:8]), sretAddr)
				}
			}
		} else {
			got := make([]byte, len(v))
			ok := true
			for _, pc := range g.pred.Ret.Pieces {
				s := resSlot(g.isa, pc.Loc)
				if s < 0 {
					ok = false
					break
				}
				copy(got[pc.Src:], r[s-blkOutR:s-blkOutR+pc.Len])
			}
			if !ok || !maskedEq(v, got, m) {
				fail("result (%s): Janus says %v; got %x, want %x", g.sig.Ret, g.pred.Ret.Pieces, got, v)
			}
		}
	}
	var queries []string
	if g.sig.Named >= 0 {
		valog := decodeHex(f["valog"])
		nva := len(g.sig.Args) - g.sig.Named
		for k := 0; k <= nva && k < len(g.pred.Va); k++ {
			st := valog[32*k : 32*k+32]
			want := g.pred.Va[k]
			var got [3]int64
			if g.isa == "arm64" {
				got = [3]int64{int64(getLE(st[0:8]) - entry), int64(int32(uint32(getLE(st[24:28])))), int64(int32(uint32(getLE(st[28:32]))))}
			} else {
				got = [3]int64{int64(uint32(getLE(st[0:4]))), int64(uint32(getLE(st[4:8]))), int64(getLE(st[8:16]) - entry)}
			}
			checks++
			if got != want {
				what := "va_start"
				if k > 0 {
					what = fmt.Sprintf("va_arg #%d (%s)", k, g.sig.Args[g.sig.Named+k-1])
				}
				fail("va_list after %s: %v, Janus %v", what, got, want)
			}
		}
		if nva > 0 {
			st := valog[0:32]
			var types []string
			for _, a := range g.sig.Args[g.sig.Named:] {
				types = append(types, a.String())
			}
			stack := f["stack"]
			var q string
			if g.isa == "arm64" {
				grTop, vrTop := getLE(st[8:16]), getLE(st[16:24])
				q = fmt.Sprintf("vaeval a64 %s %d %d %d %d %d %s mem %d:%x %d:%x %d:%s %d:%s", g.sig.ID,
					getLE(st[0:8]), grTop, vrTop, int32(uint32(getLE(st[24:28]))), int32(uint32(getLE(st[28:32]))),
					strings.Join(types, " "), grTop-64, valog[valogSave:valogSave+64], vrTop-128,
					valog[valogSave+64:valogSave+192], entry, stack, copiesAddr, f["cp"])
			} else {
				q = fmt.Sprintf("vaeval sysv %s %d %d %d %d %s mem %d:%x %d:%s %d:%s", g.sig.ID,
					uint32(getLE(st[0:4])), uint32(getLE(st[4:8])), getLE(st[8:16]), getLE(st[16:24]),
					strings.Join(types, " "), getLE(st[16:24]), valog[valogSave:valogSave+176], entry, stack,
					copiesAddr, f["cp"])
			}
			queries = append(queries, q)
		}
	}
	return checks, queries
}

func main() {
	root := flag.String("root", ".", "Janus repository root")
	outDir := flag.String("out", "artifacts/cabi-probe", "output directory")
	nRandom := flag.Int("random", 400, "number of random prototypes")
	seed := flag.Int64("seed", 1, "random seed")
	configs := flag.String("configs", "arm64/gcc/O0,arm64/gcc/O2,arm64/clang/O0,arm64/clang/O2,amd64/gcc/O0,amd64/gcc/O2,amd64/clang/O0,amd64/clang/O2", "configurations")
	keep := flag.Bool("keep", false, "keep the build directory")
	flag.Parse()

	sigs := curated()
	for i, s := range sigs {
		s.ID = fmt.Sprintf("c%02d", i)
	}
	r := rand.New(rand.NewSource(*seed))
	for i := 0; i < *nRandom; i++ {
		sigs = append(sigs, randSig(r, fmt.Sprintf("r%03d", i)))
	}
	var lines []string
	for _, s := range sigs {
		lines = append(lines, s.Line())
	}
	predLines, err := runLean(*root, lines)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	preds, err := parsePreds(predLines)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	// prototypes whose stacked arguments do not fit the probe's 1 KiB area, or with a type
	// larger than the 256 bytes the caller test captures behind a pointer, are dropped
	var kept []*Sig
	for _, s := range sigs {
		ok := preds[s.ID]["aapcs64"].Stack <= maxStack && preds[s.ID]["sysv"].Stack <= maxStack
		for _, ti := range preds[s.ID]["aapcs64"].Types {
			if ti.Size > 256 {
				ok = false
			}
		}
		if ok {
			kept = append(kept, s)
		}
	}
	sigs = kept
	os.MkdirAll(*outDir, 0o755)
	work, err := os.MkdirTemp("", "cabiprobe-")
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	if !*keep {
		defer os.RemoveAll(work)
	} else {
		fmt.Println("build directory:", work)
	}
	var sigList strings.Builder
	for _, s := range sigs {
		name := s.Name
		if name == "" {
			name = "random"
		}
		fmt.Fprintf(&sigList, "%s %-12s %s\n", s.ID, name, s.Line())
	}
	os.WriteFile(filepath.Join(*outDir, "prototypes.txt"), []byte(sigList.String()), 0o644)
	os.WriteFile(filepath.Join(*outDir, "janus-predictions.txt"), []byte(strings.Join(predLines, "\n")+"\n"), 0o644)

	gen := map[string]struct {
		types, tests, driver, stub string
		gens                       []*testGen
	}{}
	for _, isa := range []string{"arm64", "amd64"} {
		t, c, d, g := genTests(isa, sigs, preds)
		gen[isa] = struct {
			types, tests, driver, stub string
			gens                       []*testGen
		}{t, c, d, genStubAliases(isa, sigs), g}
	}
	var cfgs []Config
	for _, c := range strings.Split(*configs, ",") {
		p := strings.Split(c, "/")
		cfgs = append(cfgs, Config{p[0], p[1], p[2]})
	}
	results := make([]*result, len(cfgs))
	var wg sync.WaitGroup
	sem := make(chan struct{}, 4)
	for i, c := range cfgs {
		wg.Add(1)
		go func(i int, c Config) {
			defer wg.Done()
			sem <- struct{}{}
			defer func() { <-sem }()
			gg := gen[c.ISA]
			results[i] = runConfig(*root, work, c, sigs, preds, gg.types, gg.tests, gg.driver, gg.stub, gg.gens)
		}(i, c)
	}
	wg.Wait()

	var sum, mis strings.Builder
	fmt.Fprintf(&sum, "C ABI differential probe: %d prototypes (%d curated, %d random, seed %d)\n", len(sigs), len(curated()), len(sigs)-len(curated()), *seed)
	fmt.Fprintf(&sum, "%-20s %8s %8s %8s %8s\n", "configuration", "tests", "checks", "failed", "gcc-bug")
	var kb strings.Builder
	bad := false
	for _, res := range results {
		if res.buildError != "" {
			fmt.Fprintf(&sum, "%-20s BUILD/RUN ERROR: %s\n", res.cfg, res.buildError)
			bad = true
			continue
		}
		fmt.Fprintf(&sum, "%-20s %8d %8d %8d %8d\n", res.cfg, res.tests, res.checks, len(res.failed), len(res.known))
		kids := make([]string, 0, len(res.known))
		for id := range res.known {
			kids = append(kids, id)
		}
		sort.Strings(kids)
		for _, id := range kids {
			for _, s := range sigs {
				if s.ID == id {
					fmt.Fprintf(&kb, "%s %s [%s]\n", res.cfg, id, s.Line())
				}
			}
			for _, p := range res.known[id] {
				fmt.Fprintf(&kb, "    %s\n", p)
			}
		}
		ids := make([]string, 0, len(res.failed))
		for id := range res.failed {
			ids = append(ids, id)
		}
		sort.Strings(ids)
		for _, id := range ids {
			bad = true
			var line string
			for _, s := range sigs {
				if s.ID == id {
					line = s.Line()
				}
			}
			fmt.Fprintf(&mis, "%s %s [%s]\n", res.cfg, id, line)
			for _, p := range res.failed[id] {
				fmt.Fprintf(&mis, "    %s\n", p)
			}
		}
	}
	sum.WriteString("gcc-bug: tests excluded as the gcc -O2 arm64 va_arg bug for HFA/HVA of _Float16 or short\n" +
		"vectors (knownBug in scripts/cabiprobe/main.go; the failures are listed in known-bugs.txt)\n")
	if !bad {
		sum.WriteString("result: 0 mismatches\n")
	} else {
		sum.WriteString("result: MISMATCHES (see mismatches.txt)\n")
	}
	os.WriteFile(filepath.Join(*outDir, "summary.txt"), []byte(sum.String()), 0o644)
	os.WriteFile(filepath.Join(*outDir, "mismatches.txt"), []byte(mis.String()), 0o644)
	os.WriteFile(filepath.Join(*outDir, "known-bugs.txt"), []byte(kb.String()), 0o644)
	fmt.Print(sum.String())
	if bad {
		os.Exit(1)
	}
}
