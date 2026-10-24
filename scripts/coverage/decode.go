package main

// Running the trusted Lean decoders, and naming the class / ISA-extension family of a
// rejected encoding (the naming is informational; the verdict is the Lean decoder's).

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"regexp"
	"strings"
	"sync"

	"github.com/Giulio2002/Janus/oracle-amd64/gen"
	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
	"golang.org/x/arch/arm64/arm64asm"
	"golang.org/x/arch/x86/x86asm"
)

type Decoder struct {
	Arch   string
	Decode string // janus-decode (arm64)
	Model  string // janus-oracle-amd64
	Jobs   int
	ok     map[string]bool
	cached int
	mu     sync.Mutex
}

func (d *Decoder) Accepted(k string) bool { return d.ok[k] }

// LoadCache reads verdicts of an earlier run with the same decoder executable ("hex 0|1" lines).
func (d *Decoder) LoadCache(path string) {
	if d.ok == nil {
		d.ok = map[string]bool{}
	}
	f, err := os.Open(path)
	if err != nil {
		return
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		h, v, ok := strings.Cut(sc.Text(), " ")
		if b, err := hex.DecodeString(h); ok && err == nil {
			d.ok[string(b)] = v == "1"
		}
	}
	d.cached = len(d.ok)
}

// SaveCache writes every verdict.
func (d *Decoder) SaveCache(path string) {
	if path == "" || len(d.ok) == d.cached {
		return
	}
	f, err := os.Create(path + ".tmp")
	if err != nil {
		return
	}
	w := bufio.NewWriter(f)
	for k, v := range d.ok {
		fmt.Fprintf(w, "%x %s\n", k, map[bool]string{true: "1", false: "0"}[v])
	}
	w.Flush()
	f.Close()
	os.Rename(path+".tmp", path)
}

// Resolve runs every key not yet known through the Lean decoder.
func (d *Decoder) Resolve(keys map[string]struct{}) {
	if d.ok == nil {
		d.ok = map[string]bool{}
	}
	var todo []string
	for k := range keys {
		if _, seen := d.ok[k]; !seen {
			todo = append(todo, k)
		}
	}
	if len(todo) == 0 {
		return
	}
	jobs := max(1, min(d.Jobs, (len(todo)+999)/1000))
	chunk := (len(todo) + jobs - 1) / jobs
	var wg sync.WaitGroup
	for lo := 0; lo < len(todo); lo += chunk {
		hi := min(lo+chunk, len(todo))
		wg.Add(1)
		go func(part []string) {
			defer wg.Done()
			var res []bool
			if d.Arch == "arm64" {
				res = d.runArm64(part)
			} else {
				res = d.runAmd64(part)
			}
			d.mu.Lock()
			for i, k := range part {
				d.ok[k] = res[i]
			}
			d.mu.Unlock()
		}(todo[lo:hi])
	}
	wg.Wait()
}

func (d *Decoder) runArm64(part []string) []bool {
	var in bytes.Buffer
	for _, k := range part {
		fmt.Fprintf(&in, "0x%08x\n", binary.LittleEndian.Uint32([]byte(k)))
	}
	cmd := exec.Command(d.Decode)
	cmd.Stdin = &in
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	out, err := cmd.Output()
	if err != nil {
		die("janus-decode: %v: %s", err, stderr.String())
	}
	lines := strings.Split(strings.TrimSpace(string(out)), "\n")
	if len(lines) != len(part) {
		die("janus-decode: %d results for %d words", len(lines), len(part))
	}
	res := make([]bool, len(part))
	for i, l := range lines {
		f := strings.Fields(l)
		want := fmt.Sprintf("0x%x", binary.LittleEndian.Uint32([]byte(part[i])))
		if len(f) < 2 || f[0] != want {
			die("janus-decode: line %d %q does not answer %s", i, l, want)
		}
		res[i] = f[1] == "ok"
	}
	return res
}

func (d *Decoder) runAmd64(part []string) []bool {
	cmd := exec.Command(d.Model)
	stdin, _ := cmd.StdinPipe()
	stdout, _ := cmd.StdoutPipe()
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Start(); err != nil {
		die("janus-oracle-amd64: %v", err)
	}
	go func() {
		w := bufio.NewWriter(stdin)
		enc := json.NewEncoder(w)
		for i, k := range part {
			var s gen.State
			s.Regs[4] = L.DataBase + 2048
			c := gen.Case(i, "cov", []byte(k), s)
			enc.Encode(&c)
		}
		w.Flush()
		stdin.Close()
	}()
	res := make([]bool, len(part))
	n := 0
	sc := bufio.NewScanner(stdout)
	sc.Buffer(make([]byte, 1<<20), 1<<24)
	for sc.Scan() {
		var m L.Model
		if err := json.Unmarshal(sc.Bytes(), &m); err != nil {
			die("janus-oracle-amd64: %v", err)
		}
		if m.ID < 0 || m.ID >= len(part) {
			die("janus-oracle-amd64: bad id %d", m.ID)
		}
		res[m.ID] = m.Fault != "undecodable" && m.Len == len(part[m.ID])
		n++
	}
	io.Copy(io.Discard, stdout)
	if err := cmd.Wait(); err != nil || n != len(part) {
		die("janus-oracle-amd64: %v (%d/%d results): %s", err, n, len(part), stderr.String())
	}
	return res
}

func die(f string, a ...any) {
	fmt.Fprintf(os.Stderr, "coverage: "+f+"\n", a...)
	os.Exit(1)
}

// ---- naming rejected encodings ----

var vecRe = regexp.MustCompile(`\bV\d+\.(\d+)?[BHSDQ]\b|\bV\d+\.[BHSD]\[`)
var fpRegRe = regexp.MustCompile(`\b[QDSHB]\d+\b`)

// classArm64 returns (mnemonic class, ISA family) of an arm64 word.
func classArm64(k string) (string, string) {
	w := binary.LittleEndian.Uint32([]byte(k))
	inst, err := arm64asm.Decode([]byte(k))
	if err != nil {
		op0 := (w >> 25) & 0xF
		switch {
		case op0 == 0x2:
			return "(sve)", "SVE"
		case op0 == 0x0 && w>>31 == 1:
			return "(sme)", "SME"
		case w == 0:
			return "udf #0", "padding/udf"
		case w&0xFF000000 == 0xCE000000:
			return "(SHA512/SHA3/SM3/SM4, unknown to arm64asm)", "crypto extension (AES/SHA/PMULL/SHA3)"
		case w&0xFFC00000 == 0xD5000000:
			return "(system register / PSTATE, unknown to arm64asm)", "system / barrier / hint"
		}
		return "(unknown to arm64asm)", "unallocated/other"
	}
	op := inst.Op.String()
	s := inst.String()
	vec := vecRe.MatchString(s)
	fam := "integer/base"
	switch {
	case strings.HasPrefix(op, "AES") || strings.HasPrefix(op, "SHA") || op == "PMULL" || op == "PMULL2" ||
		op == "EOR3" || op == "RAX1" || op == "XAR" || op == "BCAX" || strings.HasPrefix(op, "SM3") || strings.HasPrefix(op, "SM4"):
		fam = "crypto extension (AES/SHA/PMULL/SHA3)"
	case strings.HasPrefix(op, "CRC32"):
		fam = "CRC32"
	case strings.HasPrefix(op, "LDADD") || strings.HasPrefix(op, "LDCLR") || strings.HasPrefix(op, "LDEOR") ||
		strings.HasPrefix(op, "LDSET") || strings.HasPrefix(op, "LDSMAX") || strings.HasPrefix(op, "LDSMIN") ||
		strings.HasPrefix(op, "LDUMAX") || strings.HasPrefix(op, "LDUMIN") || strings.HasPrefix(op, "SWP") || strings.HasPrefix(op, "CAS"):
		fam = "LSE atomics"
	case strings.HasPrefix(op, "LDXR") || strings.HasPrefix(op, "LDAXR") || strings.HasPrefix(op, "STXR") ||
		strings.HasPrefix(op, "STLXR") || strings.HasPrefix(op, "LDAR") || strings.HasPrefix(op, "STLR") || strings.HasPrefix(op, "LDXP") ||
		strings.HasPrefix(op, "STXP") || strings.HasPrefix(op, "LDAXP") || strings.HasPrefix(op, "STLXP"):
		fam = "exclusive / acquire-release"
	case op == "MRS" || op == "MSR" || op == "SYS" || op == "SYSL" || op == "DC" || op == "IC" || op == "DMB" || op == "DSB" ||
		op == "ISB" || op == "HINT" || op == "NOP" || op == "YIELD" || op == "BRK" || op == "HLT" || op == "SVC" || op == "CLREX" ||
		op == "PRFM" || op == "PRFUM" || op == "WFE" || op == "WFI" || op == "SEV" || op == "SEVL":
		fam = "system / barrier / hint"
	case vec:
		fam = "ASIMD (NEON vector)"
	case strings.HasPrefix(op, "F") || strings.HasPrefix(op, "SCVTF") || strings.HasPrefix(op, "UCVTF"):
		fam = "FP scalar"
	case fpRegRe.MatchString(s) && (strings.HasPrefix(op, "LD") || strings.HasPrefix(op, "ST")):
		fam = "SIMD&FP load/store"
	case fpRegRe.MatchString(s):
		fam = "ASIMD scalar / FP move"
	}
	cls := op
	if vec {
		cls += " (vector)"
	}
	return cls, fam
}

var (
	ssse3  = set("PSHUFB PALIGNR PHADDW PHADDD PHADDSW PHSUBW PHSUBD PHSUBSW PMADDUBSW PMULHRSW PSIGNB PSIGNW PSIGND PABSB PABSW PABSD")
	sse41  = set("PBLENDW PBLENDVB BLENDPS BLENDPD BLENDVPS BLENDVPD PTEST PMOVZXBW PMOVZXBD PMOVZXBQ PMOVZXWD PMOVZXWQ PMOVZXDQ PMOVSXBW PMOVSXBD PMOVSXBQ PMOVSXWD PMOVSXWQ PMOVSXDQ PINSRB PINSRD PINSRQ PEXTRB PEXTRD PEXTRQ PMULLD PMULDQ PMINSB PMINSD PMAXSB PMAXSD PMINUW PMINUD PMAXUW PMAXUD ROUNDPS ROUNDPD DPPS DPPD PACKUSDW PCMPEQQ MPSADBW PHMINPOSUW EXTRACTPS INSERTPS MOVNTDQA")
	sse42  = set("PCMPESTRI PCMPESTRM PCMPISTRI PCMPISTRM PCMPGTQ CRC32")
	aesni  = set("AESENC AESENCLAST AESDEC AESDECLAST AESIMC AESKEYGENASSIST")
	shani  = set("SHA1RNDS4 SHA1NEXTE SHA1MSG1 SHA1MSG2 SHA256RNDS2 SHA256MSG1 SHA256MSG2")
	bmi    = set("ANDN BEXTR BLSI BLSMSK BLSR BZHI MULX PDEP PEXT RORX SARX SHLX SHRX TZCNT LZCNT")
	sysOps = set("SYSCALL CPUID XGETBV RDTSC RDTSCP RDRAND RDSEED INT UD1 UD2 HLT PAUSE LFENCE MFENCE SFENCE XSAVE XRSTOR FXSAVE FXRSTOR LDMXCSR STMXCSR")
)

func set(s string) map[string]bool {
	m := map[string]bool{}
	for _, f := range strings.Fields(s) {
		m[f] = true
	}
	return m
}

// classAmd64 returns (mnemonic class, ISA family) of an amd64 encoding.
func classAmd64(k string) (string, string) {
	b := []byte(k)
	q := legacyPrefixEnd(b)
	for q < len(b) && b[q] >= 0x40 && b[q] <= 0x4F {
		q++
	}
	enc := ""
	if q < len(b) {
		switch {
		case b[q] == 0x62:
			enc = "evex"
		case b[q] == 0xC5 && q+1 < len(b):
			enc = map[bool]string{true: "vex256", false: "vex128"}[b[q+1]&4 != 0]
		case b[q] == 0xC4 && q+2 < len(b):
			enc = map[bool]string{true: "vex256", false: "vex128"}[b[q+2]&4 != 0]
		}
	}
	if len(b) == 4 && b[0] == 0xF3 && b[1] == 0x0F && b[2] == 0x1E && (b[3] == 0xFA || b[3] == 0xFB) {
		return "endbr64", "CET (ENDBR64)"
	}
	if q := legacyPrefixEnd(b); legacyLen(b) == len(b) {
		r := q
		if r < len(b) && b[r] >= 0x40 && b[r] <= 0x4F {
			r++
		}
		if b[r+1] == 0x38 && b[r+2] == 0xF6 && q > 0 && (b[0] == 0x66 || b[0] == 0xF3) {
			return map[bool]string{true: "adcx", false: "adox"}[b[0] == 0x66], "ADX"
		}
	}
	inst, ok := gen.Decode(b)
	if !ok || inst.Len != len(b) {
		switch enc {
		case "evex":
			return "(evex)", "AVX-512 (EVEX, opmask)"
		case "vex128", "vex256":
			return "(" + enc + " unknown to x86asm)", "AVX/AVX2 other (VEX)"
		}
		return "(bad)", "unallocated/other"
	}
	op := inst.Op.String()
	cls := strings.ToLower(op)
	seg := ""
	for _, p := range b[:legacyPrefixEnd(b)] {
		switch p {
		case 0x64:
			seg = "fs:"
		case 0x65:
			seg = "gs:"
		}
	}
	cls = seg + cls
	if enc != "" {
		cls += "/" + enc
	}
	hasReg := func(lo, hi x86asm.Reg) bool {
		for _, a := range inst.Args {
			switch v := a.(type) {
			case x86asm.Reg:
				if v >= lo && v <= hi {
					return true
				}
			}
		}
		return false
	}
	bare := strings.TrimPrefix(op, "V")
	fam := "integer/base"
	switch {
	case enc == "evex" || (enc != "" && strings.HasPrefix(op, "K")):
		fam = "AVX-512 (EVEX, opmask)"
	case bmi[op]:
		fam = "BMI1/BMI2/LZCNT"
	case enc != "" && (strings.HasPrefix(op, "VFMADD") || strings.HasPrefix(op, "VFMSUB") || strings.HasPrefix(op, "VFNMADD") || strings.HasPrefix(op, "VFNMSUB")):
		fam = "FMA"
	case enc != "" && (aesni[bare] || bare == "PCLMULQDQ"):
		fam = "VAES/VPCLMULQDQ (VEX)"
	case enc == "vex256":
		fam = "AVX2 (256-bit VEX)"
	case enc == "vex128":
		fam = "AVX (128-bit VEX)"
	case aesni[op]:
		fam = "AES-NI"
	case op == "PCLMULQDQ":
		fam = "PCLMULQDQ"
	case shani[op]:
		fam = "SHA-NI"
	case sse42[op]:
		fam = "SSE4.2"
	case sse41[op]:
		fam = "SSE4.1"
	case ssse3[op]:
		fam = "SSSE3"
	case op == "ADCX" || op == "ADOX":
		fam = "ADX"
	case op == "POPCNT" || op == "MOVBE":
		fam = "POPCNT/MOVBE"
	case sysOps[op]:
		fam = "system (SYSCALL/CPUID/XGETBV/fences/MXCSR)"
	case strings.HasPrefix(op, "F") && !hasReg(x86asm.X0, x86asm.X15):
		fam = "x87"
	case hasReg(x86asm.M0, x86asm.M7):
		fam = "MMX"
	case hasReg(x86asm.X0, x86asm.X15) || strings.HasSuffix(op, "SD") || strings.HasSuffix(op, "SS") || strings.HasSuffix(op, "PS") || strings.HasSuffix(op, "PD"):
		fam = "SSE/SSE2"
	case seg != "":
		fam = "segment (FS/GS)"
	case strings.HasPrefix(op, "MOVS") || strings.HasPrefix(op, "STOS") || strings.HasPrefix(op, "CMPS") || strings.HasPrefix(op, "SCAS") || strings.HasPrefix(op, "LODS"):
		fam = "string instructions"
	}
	return cls, fam
}

func asmText(arch, k string) string {
	if arch == "arm64" {
		inst, err := arm64asm.Decode([]byte(k))
		if err != nil {
			return "?"
		}
		return inst.String()
	}
	return gen.Asm([]byte(k))
}

func hexKey(arch, k string) string {
	if arch == "arm64" {
		return fmt.Sprintf("%08x", binary.LittleEndian.Uint32([]byte(k)))
	}
	return hex.EncodeToString([]byte(k))
}
