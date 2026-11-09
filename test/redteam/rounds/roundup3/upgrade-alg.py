#!/usr/bin/env python3
"""UP3c: put the RUN conjunct (the main contract's own post at the witness state s) into the Alg*equal / Alg*hash0 witnesses.
Usage: upgrade-alg.py FILE... (arm64 examples/proofs/X.lean or amd64 examples/proofs-amd64/X/Proof.lean)"""
import re, sys
for f in sys.argv[1:]:
    s = open(f).read(); amd = 'proofs-amd64' in f
    r2 = 3 if amd else 1
    retf = '(retAddrOf s)' if amd else '(s.regs 30)'
    m = re.search(r'theorem correctness (\([^)]*\) )*: (\w+) Extracted.program Extracted.entry (.*?) :=', s)
    fam, args = m.group(2), m.group(3).split()
    B = lambda n: f's.mem.readLE (s.regs 0).toNat {n} == s.mem.readLE (s.regs {r2}).toNat {n}'
    if fam == 'MemequalN':
        n = {'0':0,'1':1,'2':2,'4':4,'8':8,'16':16}[args[1]]
        post = f'EqRet 64 2 s s\' fun r => BoolRes r ({B(n)})'; pf = 'correctness 64 s rfl pre'
    elif fam == 'Memequal':
        post = f'EqRet 64 0 s s\' fun r => BoolRes r (s.mem.readLE (s.regs 0).toNat (s.regs 2).toNat == s.mem.readLE (s.regs {r2}).toNat (s.regs 2).toNat)'
    elif fam in ('Cequal', 'Fequal'):
        F, n = args[1], int(args[2])
        fe = lambda off: (f'feq {F} (s.mem.readLE (s.regs 0).toNat {n}) (s.mem.readLE (s.regs {r2}).toNat {n})' if off == 0 else
                         f'feq {F} (s.mem.readLE ((s.regs 0).toNat + {n}) {n}) (s.mem.readLE ((s.regs {r2}).toNat + {n}) {n})')
        body = fe(0) if fam == 'Fequal' else f'({fe(0)}) && ({fe(1)})'
        post = f'EqRet 64 2 s s\' fun r => BoolRes r ({body})'
    elif fam == 'Memhash0':
        post = f'HRet H0 64 2 s s\' fun r => r 0 = s.regs {r2}'
    else: print('SKIP fam', fam, f); continue
    conj = f'(ReachesRet Extracted.program {retf} s\n    (fun s\' => {post}))'
    i = s.index('theorem nonvacuous'); j = s.index('end Witness')
    nv = s[i:j]
    # statement part up to ':=\n  ⟨'
    k = nv.index(' :=\n  ⟨')
    stmt, rest = nv[:k], nv[k:]
    stmt = re.sub(r' ∧\n    \((ReachesRet|Returns).*$', '', stmt, flags=re.S)
    cm = re.search(r':=\n  ⟨(.*?)(, returns)?⟩', rest, re.S)
    comps = cm.group(1)
    hdr = f'correctness {"H0 " if fam=="Memhash0" else ""}64 s0 rfl pre'
    # when returns present in the term it is the last component; replace by the generic proof
    new = stmt + ' ∧\n    ' + conj + f' :=\n  ⟨{comps}, {hdr}⟩'
    # the returns lemma must precede? not needed: proof term is direct
    tail = rest[cm.end():]
    s = s[:i] + new + tail + s[j:]
    open(f, 'w').write(s); print('UPGRADED', f)
