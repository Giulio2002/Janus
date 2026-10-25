package main

import (
	"fmt"
	"math/rand"
	"strconv"
	"strings"
)

// Ty is a C type in the probe's compact grammar (JanusTests/CABIProbe.lean): i1..i16, u1..u16,
// p, h, f, d, ld, cf, cd, cld, v8, v16, s(t,...), u(t,...), a<n>(t).
type Ty struct {
	K     string // "i" "u" "p" "h" "f" "d" "ld" "cf" "cd" "cld" "v" "s" "un" "a"
	N     int    // int bytes, vector bytes, array length
	Elems []*Ty  // struct/union members, array element
}

func (t *Ty) String() string {
	switch t.K {
	case "i", "u", "v":
		return t.K + strconv.Itoa(t.N)
	case "s", "un":
		var parts []string
		for _, e := range t.Elems {
			parts = append(parts, e.String())
		}
		k := "s"
		if t.K == "un" {
			k = "u"
		}
		return k + "(" + strings.Join(parts, ",") + ")"
	case "a":
		return "a" + strconv.Itoa(t.N) + "(" + t.Elems[0].String() + ")"
	}
	return t.K
}

// parseTy parses the compact grammar.
func parseTy(s string) (*Ty, string, error) {
	switch {
	case strings.HasPrefix(s, "u("):
		es, r, err := parseList(s[2:])
		return &Ty{K: "un", Elems: es}, r, err
	case strings.HasPrefix(s, "s("):
		es, r, err := parseList(s[2:])
		return &Ty{K: "s", Elems: es}, r, err
	case strings.HasPrefix(s, "a"):
		i := 1
		for i < len(s) && s[i] >= '0' && s[i] <= '9' {
			i++
		}
		n, _ := strconv.Atoi(s[1:i])
		if i >= len(s) || s[i] != '(' {
			return nil, s, fmt.Errorf("bad array %q", s)
		}
		e, r, err := parseTy(s[i+1:])
		if err != nil || !strings.HasPrefix(r, ")") {
			return nil, s, fmt.Errorf("bad array %q", s)
		}
		return &Ty{K: "a", N: n, Elems: []*Ty{e}}, r[1:], nil
	case strings.HasPrefix(s, "i") || strings.HasPrefix(s, "u") || strings.HasPrefix(s, "v"):
		i := 1
		for i < len(s) && s[i] >= '0' && s[i] <= '9' {
			i++
		}
		n, err := strconv.Atoi(s[1:i])
		return &Ty{K: s[:1], N: n}, s[i:], err
	}
	for _, k := range []string{"cld", "cf", "cd", "ld", "p", "h", "f", "d"} {
		if strings.HasPrefix(s, k) {
			return &Ty{K: k}, s[len(k):], nil
		}
	}
	return nil, s, fmt.Errorf("bad type %q", s)
}

func parseList(s string) ([]*Ty, string, error) {
	var es []*Ty
	for {
		e, r, err := parseTy(s)
		if err != nil {
			return nil, s, err
		}
		es = append(es, e)
		if strings.HasPrefix(r, ",") {
			s = r[1:]
			continue
		}
		if strings.HasPrefix(r, ")") {
			return es, r[1:], nil
		}
		return nil, r, fmt.Errorf("bad list %q", s)
	}
}

func mustTy(s string) *Ty {
	t, r, err := parseTy(s)
	if err != nil || r != "" {
		panic(fmt.Sprintf("type %q: %v (rest %q)", s, err, r))
	}
	return t
}

// cdecls accumulates the struct/union definitions of a test.
type cdecls struct {
	prefix string
	n      int
	defs   []string
}

// cname returns the C spelling of t, defining aggregates as needed.
func (c *cdecls) cname(t *Ty) string {
	switch t.K {
	case "i", "u":
		sign := "signed "
		if t.K == "u" {
			sign = "unsigned "
		}
		switch t.N {
		case 1:
			return sign + "char"
		case 2:
			return sign + "short"
		case 4:
			return sign + "int"
		case 8:
			return sign + "long"
		case 16:
			return sign + "__int128"
		}
	case "p":
		return "void *"
	case "h":
		return "_Float16"
	case "f":
		return "float"
	case "d":
		return "double"
	case "ld":
		return "long double"
	case "cf":
		return "_Complex float"
	case "cd":
		return "_Complex double"
	case "cld":
		return "_Complex long double"
	case "v":
		return fmt.Sprintf("probe_v%d_t", t.N)
	case "s", "un":
		kw := "struct"
		if t.K == "un" {
			kw = "union"
		}
		var fields []string
		for i, e := range t.Elems {
			if e.K == "a" {
				fields = append(fields, fmt.Sprintf("%s f%d[%d];", c.cname(e.Elems[0]), i, e.N))
			} else {
				fields = append(fields, fmt.Sprintf("%s f%d;", c.cname(e), i))
			}
		}
		name := fmt.Sprintf("%s %s_%d", kw, c.prefix, c.n)
		c.n++
		c.defs = append(c.defs, fmt.Sprintf("%s { %s };", name, strings.Join(fields, " ")))
		return name
	case "a":
		// only as a member (handled above); a parameter array would decay
		panic("array outside a struct")
	}
	panic("cname " + t.String())
}

// Random signature generation.

var scalars = []string{"i1", "i2", "i4", "i8", "i16", "u1", "u2", "u4", "u8", "u16", "p", "h", "f", "d", "ld",
	"cf", "cd", "cld", "v8", "v16"}

// promoted reports whether a top-level type survives the default argument promotions (so
// that it can be a variadic argument).
func promoted(t *Ty) bool {
	switch t.K {
	case "h", "f":
		return false
	case "i", "u":
		return t.N >= 4
	}
	return true
}

func randScalar(r *rand.Rand) *Ty { return mustTy(scalars[r.Intn(len(scalars))]) }

func randMember(r *rand.Rand, depth int) *Ty {
	switch x := r.Intn(10); {
	case x < 6 || depth >= 2:
		return randScalar(r)
	case x < 8:
		return randAggregate(r, depth+1)
	default:
		return &Ty{K: "a", N: 1 + r.Intn(4), Elems: []*Ty{randScalarOrSmall(r)}}
	}
}

func randScalarOrSmall(r *rand.Rand) *Ty {
	ks := []string{"i1", "i2", "i4", "i8", "u1", "f", "d", "h", "v8", "v16", "ld"}
	return mustTy(ks[r.Intn(len(ks))])
}

// randAggregate: homogeneous floating-point/vector structs (HFA/HVA candidates, sometimes with
// a fifth member or nested), mixed structs, unions.
func randAggregate(r *rand.Rand, depth int) *Ty {
	switch x := r.Intn(10); {
	case x < 4:
		bases := []string{"f", "d", "ld", "h", "v8", "v16", "cf", "cd"}
		b := bases[r.Intn(len(bases))]
		k := 1 + r.Intn(5)
		var es []*Ty
		for i := 0; i < k; i++ {
			if r.Intn(4) == 0 && depth < 2 {
				es = append(es, &Ty{K: "a", N: 1 + r.Intn(2), Elems: []*Ty{mustTy(b)}})
			} else {
				es = append(es, mustTy(b))
			}
		}
		return &Ty{K: "s", Elems: es}
	case x < 8:
		k := 1 + r.Intn(5)
		var es []*Ty
		for i := 0; i < k; i++ {
			es = append(es, randMember(r, depth))
		}
		return &Ty{K: "s", Elems: es}
	default:
		k := 2 + r.Intn(2)
		var es []*Ty
		for i := 0; i < k; i++ {
			es = append(es, randMember(r, depth+1))
		}
		return &Ty{K: "un", Elems: es}
	}
}

func randArg(r *rand.Rand) *Ty {
	if r.Intn(10) < 6 {
		return randScalar(r)
	}
	return randAggregate(r, 0)
}

// Sig is a prototype of the corpus.
type Sig struct {
	ID    string
	Name  string // the corpus function it mirrors, if any
	Ret   *Ty    // nil = void
	Args  []*Ty
	Named int // -1: not variadic
}

func (s *Sig) Line() string {
	ret := "v"
	if s.Ret != nil {
		ret = s.Ret.String()
	}
	named := "-"
	if s.Named >= 0 {
		named = strconv.Itoa(s.Named)
	}
	var as []string
	for _, a := range s.Args {
		as = append(as, a.String())
	}
	return strings.TrimSpace(fmt.Sprintf("%s %s %s %s", s.ID, ret, named, strings.Join(as, " ")))
}

func randSig(r *rand.Rand, id string) *Sig {
	s := &Sig{ID: id, Named: -1}
	switch x := r.Intn(10); {
	case x < 2:
	case x < 6:
		s.Ret = randScalar(r)
	default:
		s.Ret = randAggregate(r, 0)
	}
	n := r.Intn(13)
	variadic := r.Intn(6) == 0
	if variadic {
		s.Named = 1 + r.Intn(3)
		if n < s.Named {
			n = s.Named
		}
	}
	for i := 0; i < n; i++ {
		var a *Ty
		for {
			a = randArg(r)
			if !variadic || i < s.Named || promoted(a) {
				break
			}
		}
		s.Args = append(s.Args, a)
	}
	return s
}

// curated: the ABI functions of the C corpus (scripts/coverage/ccorpus/abi.c) and of the cgo
// examples (examples/cgo/cabi/kabi.c), with the prototypes those files declare, and the
// classic edge cases of both ABIs.
func curated() []*Sig {
	mk := func(name, ret string, named int, args ...string) *Sig {
		s := &Sig{Name: name, Named: named}
		if ret != "v" {
			s.Ret = mustTy(ret)
		}
		for _, a := range args {
			s.Args = append(s.Args, mustTy(a))
		}
		return s
	}
	small := "s(i8,i8)"
	big := "s(a6(i8))"
	mixed := "s(d,i4)"
	hfa := "s(f,f,f,f)"
	pt := "s(d,d)"
	kmix := "s(d,i8)"
	kbig := "s(i8,i8,i8,i8)"
	return []*Sig{
		mk("a_varargs", "i8", 1, "i4", "i8", "i8", "i8", "i8", "i8", "i8", "i8", "i8", "i8"),
		mk("a_varargs_f", "d", 1, "i4", "d", "d", "d", "d", "d", "d", "d", "d", "d", "d"),
		mk("a_small", small, -1, "i8"),
		mk("a_small_arg", "i8", -1, small),
		mk("a_big", big, -1, "i8"),
		mk("a_big_arg", "i8", -1, big),
		mk("a_mixed", "d", -1, mixed),
		mk("a_hfa", "f", -1, hfa),
		mk("a_stackargs", "i8", -1, "i8", "i8", "i8", "i8", "i8", "i8", "i8", "i8", "i8", "i8"),
		mk("a_fargs", "d", -1, "d", "f", "d", "i8"),
		mk("a_callback", "i8", -1, "p", "p", "i8"),
		mk("a_ldouble", "ld", -1, "ld", "ld"),
		mk("a_complex", "cd", -1, "cd", "cd"),
		mk("a_u128", "u16", -1, "u16", "u16"),
		mk("k_stack10", "i8", -1, "i8", "i8", "i8", "i8", "i8", "i8", "i8", "i8", "i4", "i8"),
		mk("k_fp", "d", -1, "d", "f", "d"),
		mk("k_pmix", kmix, -1, pt, pt, "i8"),
		mk("k_big", kbig, -1, "i8", "i8"),
		mk("k_vsum", "i8", 1, "i4", "i8", "i8", "i8", "i8", "i8", "i8", "i8", "i8"),
		mk("k_vsum8", "i8", -1, "i8", "i8", "i8", "i8", "i8", "i8", "i8", "i8"),
		// edge cases
		mk("int128_odd", "v", -1, "i8", "i16", "i8", "i16", "i16", "i16"),
		mk("hfa_spill", "v", -1, "s(d,d,d)", "s(d,d,d)", "s(d,d,d)", "d"),
		mk("hfa5", "s(f,f,f,f,f)", -1, "s(d,d,d,d,d)", "s(f,f,f,f)"),
		mk("hva", "s(v16,v16)", -1, "s(v16,v16,v16,v16)", "v8", "s(v8,v8)"),
		mk("sse_struct3", "s(f,f,f)", -1, "s(f,f,f)", "s(f,i4,f)"),
		mk("mixed_order", "s(i8,d)", -1, "s(i8,d)", "s(f,i4)", "s(i1,f,d)"),
		mk("allornothing", "v", -1, "i8", "i8", "i8", "i8", "i8", "s(i8,i8)", "i8"),
		mk("sse_exhaust", "v", -1, "d", "d", "d", "d", "d", "d", "d", "s(d,d)", "d"),
		mk("ld_stack", "cld", -1, "i4", "ld", "i4", "cld", "i8"),
		mk("unions", "u(d,i8)", -1, "u(f,i4)", "u(ld,i8)", "u(s(f,f),d)"),
		mk("arrays", "s(a2(d))", -1, "s(a3(f))", "s(a2(i4),f)", "s(a4(i1),a2(h))"),
		mk("small_ints", "i1", -1, "i1", "u2", "i4", "u1", "h", "i2"),
		mk("big_byref", "s(a5(i8))", -1, "s(a3(i8))", "s(a2(i8),i1)", "i8", "i8", "i8", "i8", "i8", "i8", "s(a3(i8))"),
		mk("va_mixed", "d", 2, "i4", "d", "s(d,i8)", "s(f,f)", "ld", "i8", "s(a3(i8))", "cd", "d"),
		mk("va_hfa", "v", 1, "i4", "s(d,d,d)", "s(f,f)", "s(d,d,d,d)", "s(d,d,d)", "i8", "d"),
		mk("va_int128", "v", 1, "i4", "i8", "i16", "i8", "i16", "i16", "i16", "i8"),
		mk("va_many_d", "d", 1, "i4", "d", "d", "d", "d", "d", "d", "d", "d", "d", "d", "d"),
		mk("v16_args", "v16", -1, "v16", "s(v16)", "v16", "i8"),
		mk("float16", "h", -1, "h", "s(h,h)", "s(h,h,h,h,h)", "s(h,f)"),
	}
}
