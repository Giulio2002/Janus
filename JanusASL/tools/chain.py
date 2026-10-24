#!/usr/bin/env python3
"""Generate decode-chain lemmas for JanusASL.Proofs (docs/ASL.md).

The generated `__DecodeA64_<class>` functions are if-chains, one `if` per sail-arm decode clause:

    (if ((←((pure ((extractLsb __opcode hi lo == c) && ...)) <&&> (do (pure ((← readReg SEE) <b N))))) : Bool)
    then (do writeReg SEE N; let F := (BitVec.slice __opcode lo len); ...; (decode_X F ...))
    else (do ...next clause...)

For an encoding class given by its fixed bits, this script finds the clause every word of the
class reaches (all conjuncts of every earlier clause decided by fixed bits) and prints a Lean
lemma `run_<class>_<name>`: on such a word, with SEE = -1, the class function runs the clause's
decode function on the word's fields, with SEE set. The proof is `rw` + `simp` with one
`have` per earlier clause (a conjunct that the fixed bits falsify), discharged by `omega`.

    chain.py PARTS_DIR CLASS_FN LEMMA_NAME 'lo:len:val,...' [DECODE_FN]

Fixed bits are given as fields `lo:len:val` (bits lo+len-1..lo equal val). A clause body guarded
by should-be-one checks (`if access(op, i) != 1 || ... then ConstrainedUnpredictable`, as SMULH's
Ra) is accepted when the class fixes those bits to 1; the lemma then also uses `access_ofNat32`.
"""
import glob, re, sys


def load_fn(parts, name):
    for f in sorted(glob.glob(parts + "/Part*.lean")):
        txt = open(f).read()
        i = txt.find("\ndef %s " % name)
        if i < 0:
            continue
        j = txt.find("\ndef ", i + 1)
        k = txt.find("\n/--", i + 1)
        j = min(x for x in (j, k, len(txt)) if x > 0)
        return txt[i + 1:j]
    raise SystemExit("no " + name)


COND = re.compile(r"\(if \(\(←\(\(pure (.*?) <&&> \(do\s*\(pure \(\(← readReg SEE\) <b (\d+)\)\)", re.S)
CONJ = re.compile(r"\(Sail\.BitVec\.extractLsb __opcode (\d+) (\d+)\) == \(((?:0b[01]+)|(?:0x[0-9A-Fa-f]+)|\d+)#(\d+) : \(BitVec \d+\)\)")
# a whole-opcode comparison `(__opcode == (C#32 : (BitVec 32)))` (hi = 31, lo = 0, marked by width -32)
CONJW = re.compile(r"\(__opcode == \(((?:0b[01]+)|(?:0x[0-9A-Fa-f]+)|\d+)#32 : \(BitVec 32\)\)\)")


def clauses(fn):
    out = []
    pos = 0
    while True:
        m = COND.search(fn, pos)
        if not m:
            break
        conj = [(int(a), int(b), int(c, 0), int(d)) for a, b, c, d in CONJ.findall(m.group(1))]
        conj += [(31, 0, int(c, 0), -32) for c in CONJW.findall(m.group(1))]
        if not conj:
            raise SystemExit("unparsed condition: " + m.group(1)[:200])
        # body: from 'then' to the matching 'else' at the same nesting; we only need the callee
        then = fn.index("then", m.end())
        nxt = COND.search(fn, m.end())
        rest = fn[then:nxt.start() if nxt else len(fn)]
        dm = re.search(r"\((decode_[A-Za-z0-9_]+) ", rest)
        th = rest.find("sailThrow")
        el = rest.find("\n", rest.find("else"))
        callee = dm.group(1) if dm and (th < 0 or dm.start() < th) else "throw"
        if callee == "throw" and dm and dm.start() < el + 4000:
            # the throw may be a should-be-one guard in front of the decode call (checked below)
            g = rest[:dm.start()]
            if "(if" in g and re.search(r"Error_ConstrainedUnpredictable", g) and \
                    re.search(r"BitVec\.access __opcode \d+\) : BitVec 1\) != 1#1", g):
                callee = dm.group(1)
        body = None
        if callee != "throw":
            seg = rest[:dm.end() + 400]
            lets = dict((n, (int(a), int(b))) for n, a, b in
                        re.findall(r"let (\w+) := \(BitVec\.slice __opcode (\d+) (\d+)\)", seg[:dm.start()]))
            cm = re.match(r"\((decode_[A-Za-z0-9_]+) ((?:[A-Za-z0-9_]+ ?)+)\)", rest[dm.start():])
            pre = rest[:dm.start()]
            sbo = []
            if "(if" in pre:
                # a should-be-one guard `(if (access __opcode i != 1#1) || ... then throw ...)`
                g = pre[pre.index("(if"):]
                sbo = [int(i) for i in re.findall(r"BitVec\.access __opcode (\d+)\) : BitVec 1\) != 1#1", g)]
                stripped = re.sub(r"BitVec\.access __opcode \d+\) : BitVec 1\) != 1#1", "", g)
                if not sbo or "__opcode" in stripped or g.count("(if") != 1:
                    sbo = None
            if cm and all(a in lets for a in cm.group(2).split()) and sbo is not None:
                body = "(%s %s)" % (cm.group(1), " ".join("(fld w %d %d)" % lets[a] for a in cm.group(2).split()))
        else:
            sbo = []
        out.append((conj, int(m.group(2)), callee, body, sbo))
        pos = m.end()
    return out


def fixed(fields):
    """bit -> value for the class's fixed bits."""
    fx = {}
    for lo, ln, val in fields:
        for b in range(ln):
            fx[lo + b] = (val >> b) & 1
    return fx


def decide(conj, fx):
    """True / False if every word of the class makes the conjunct true / false, else None."""
    hi, lo, c, _ = conj
    vals = []
    for b in range(lo, hi + 1):
        want = (c >> (b - lo)) & 1
        if b in fx:
            if fx[b] != want:
                return False
        else:
            vals.append(b)
    return True if not vals else None


def main():
    parts, fn_name, lemma, flds = sys.argv[1:5]
    want = sys.argv[5] if len(sys.argv) > 5 else None
    fields = [tuple(int(x, 0) for x in f.split(":")) for f in flds.split(",") if f]
    fx = fixed(fields)
    cl = clauses(load_fn(parts, fn_name))
    haves, used = [], []
    target = None
    for idx, (conj, see, callee, _b, _sbo) in enumerate(cl):
        ds = [decide(c, fx) for c in conj]
        if all(d is True for d in ds):
            target = (idx, conj, see, callee)
            for k, c in enumerate(conj):
                haves.append(("t%d_%d" % (idx, k), c, True))
            break
        if False in ds:
            k = ds.index(False)
            haves.append(("f%d" % idx, conj[k], False))
        else:
            raise SystemExit("clause %d (SEE %d, %s) is not decided by the fixed bits: %s"
                             % (idx, see, callee, [(c, d) for c, d in zip(conj, ds)]))
    if target is None:
        raise SystemExit("no clause matches")
    idx, conj, see, callee = target
    body = cl[idx][3]
    sbo = cl[idx][4] or []
    for i in sbo:
        if fx.get(i) != 1:
            raise SystemExit("should-be-one bit %d is not fixed to 1 by the class" % i)
    if body is None:
        raise SystemExit("clause body of %s is not a plain decode call; write the lemma by hand" % callee)
    if want and callee != want:
        raise SystemExit("class reaches %s, not %s" % (callee, want))
    hyps = " ".join("(h%d : (w / 2 ^ %d) %% %d = %d)" % (i, lo, 2 ** ln, val)
                    for i, (lo, ln, val) in enumerate(fields))
    print("set_option maxHeartbeats 8000000 in")
    print("/-- `%s` on its encoding class reaches clause SEE %d (`%s`). -/" % (fn_name, see, callee))
    print("theorem %s {w : Nat} (hw : w < 2 ^ 32) %s {s : SState} (hs : s.regs.get? .SEE = some (-1))"
          % (lemma, hyps))
    print("    (pc : Int) :")
    print("    (%s pc (BitVec.ofNat 32 w)).run s =" % fn_name)
    print("      %s.run (s.set .SEE %d) := by" % (body, see))
    names = []
    for nm, (hi, lo, c, width), val in haves:
        if width == -32:
            print("  have %s : (BitVec.ofNat 32 w == (%d#32 : BitVec 32)) = %s := by"
                  % (nm, c, "true" if val else "false"))
            print("    exact %s (by simp; omega)" % ("ofNat_beq_true" if val else "ofNat_beq_false"))
        else:
            print("  have %s : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) %d %d == (%d#%d : BitVec %d)) = %s := by"
                  % (nm, hi, lo, c, width, width, "true" if val else "false"))
            print("    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact %s (by simp; omega)"
                  % ("ofNat_beq_true" if val else "ofNat_beq_false"))
        names.append(nm)
    for i in sbo:
        print("  have s%d : Sail.BitVec.access (BitVec.ofNat 32 w) %d = 1#1 := access_ofNat32 _ _ (by decide) (by omega)"
              % (i, i))
        names.append("s%d" % i)
    print("  rw [%s]" % fn_name)
    print("  simp only [run_bind, %s, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,"
          % ", ".join(names))
    print("    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,%s"
          % (" bne_self_eq_false, Bool.or_false," if sbo else ""))
    print("    show ((-1 : Int) < %d) = True from by decide]" % see)
    print("  all_goals rfl")
    print("-- clause index %d of %d" % (idx, len(cl)), file=sys.stderr)


if __name__ == "__main__":
    main()
