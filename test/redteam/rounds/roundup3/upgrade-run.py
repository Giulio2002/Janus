#!/usr/bin/env python3
"""UP3b: add the U-WITNESS-RUN conjunct to simple Witness.nonvacuous statements `∃ s, A ∧ B …` whose `returns` lemma states the main
theorem's conclusion at the concrete state `s0`: nonvacuous := ∃ s, A ∧ … ∧ (returns' statement with s0 ↦ s), proof `⟨…, returns⟩`; `returns` is
moved before `nonvacuous`. Skips (and reports) files of any other shape.   Usage: upgrade-run.py FILE..."""
import re, sys
def block(src, name):
    m = re.search(r'(?m)^(?:/--.*?-/\n)?theorem ' + name + r'\b', src, re.S)
    if not m: return None
    # a block ends at the next blank line followed by a top-level item (theorem/def/end/namespace/open/lemma/abbrev) or EOF
    st = src.rfind('\n\n', 0, m.start()) + 2 if src[:m.start()].rfind('\n\n') >= 0 else 0
    m2 = re.search(r'\n\n(?=(?:/--|theorem|def|end |namespace|open|lemma|abbrev|@\[|/-!))', src[m.end():])
    en = m.end() + (m2.start() if m2 else len(src) - m.end())
    ts = src.index('theorem ' + name, st)
    if src[:ts].endswith('-/\n'):
        ts = src.rfind('/--', 0, ts)
    return ts, en
for f in sys.argv[1:]:
    src = open(f).read()
    if 'namespace Witness' not in src: print('SKIP(no witness)', f); continue
    nb, rb = block(src, 'nonvacuous'), block(src, 'returns')
    if not nb or not rb: print('SKIP(no nonvacuous/returns)', f); continue
    nv = src[nb[0]:nb[1]]; rt = src[rb[0]:rb[1]]
    docpre = nv[:nv.index('theorem nonvacuous')]; nv = nv[len(docpre):]
    nm = re.match(r'theorem nonvacuous : (∃ .*?) :=\n?\s*(⟨.*⟩)\s*$', nv, re.S)
    rm = re.search(r'theorem returns : (.*?) :=', rt, re.S)
    if not nm or not rm: print('SKIP(shape)', f); continue
    stmt, proof = nm.group(1), nm.group(2)
    rstmt = rm.group(1)
    if 'ReachesRet' not in rstmt and 'Returns' not in rstmt: print('SKIP(returns shape)', f); continue
    if not re.search(r'\bs0\b', rstmt): print('SKIP(no s0)', f); continue
    rs = re.sub(r'\bs0\b', 's', rstmt)
    new_nv = docpre + 'theorem nonvacuous : ' + stmt + ' ∧\n    (' + rs + ') :=\n  ' + proof[:-1] + ', returns⟩'
    # reorder: returns before nonvacuous
    if rb[0] < nb[0]: print('SKIP(returns already first)', f); continue
    out = src[:nb[0]] + rt.rstrip('\n') + '\n\n' + new_nv + src[rb[1]:] if nb[1] <= rb[0] and src[nb[1]:rb[0]].strip() == '' else None
    if out is None:
        out = src[:rb[0]] + src[rb[1]:]  # remove returns
        nb2 = block(out, 'nonvacuous'); nv2 = out[nb2[0]:nb2[1]]
        out = out[:nb2[0]] + rt.rstrip('\n') + '\n\n' + new_nv + out[nb2[1]:]
    open(f, 'w').write(out); print('UPGRADED', f)
