#!/usr/bin/env python3
"""jx1gen.py: mechanical part of the U-WITNESS-CALLSITE/RUN upgrade of an example witness.
usage: from jx1gen import patch;  patch(path, site_ws, conjs, terms, subs)
 site_ws : text inserted before the nonvacuous docstring (Site defs, wsCall, wsCall_pre lemmas)
 conjs   : list of conjunct texts appended to the nonvacuous statement (before the Returns conjunct)
 terms   : list of proof terms for them (same order)
 subs    : list of (old,new) identifier substitutions applied to the `returns` statement to make the Returns conjunct
           (s0->s, implAt->impl, model constants -> the bound variable names)
The `returns` theorem is moved before nonvacuous, and passed as the last component."""
import re
def ident_sub(txt, old, new):
    if re.fullmatch(r'[\w\.\']+', old):
        return re.sub(r'(?<![\w\.\'])'+re.escape(old)+r'(?![\w\'])', new, txt)
    return txt.replace(old, new)
def patch(path, site_ws, conjs, terms, subs, returns_term='returns', rstmt_override=None):
    t = open(path).read()
    if 'JX1' in t and 'callsite' in t: print('already patched?', path)
    w = t.index('namespace Witness')
    n = t.index('theorem nonvacuous', w)
    # docstring before nonvacuous (a `/-- ... -/` immediately preceding)
    d = t.rfind('/--', w, n)
    if d != -1 and '-/' in t[d:n] and t[t.index('-/', d)+2:n].strip() == '':
        ins = d
    else:
        ins = n
    # returns block
    r = t.index('theorem returns', w)
    rd = t.rfind('/--', w, r)
    if rd == -1 or t[t.index('-/', rd)+2:r].strip() != '': rd = r
    e = t.index('end Witness', r)
    rblock = t[rd:e]
    rstmt_start = t.index(':', r) + 1          # after 'theorem returns'
    rstmt_start = r + len('theorem returns :')
    # statement ends at first ':=' after r that is followed by newline or ' by'
    m = re.search(r':=(\s*\n|\s+by)', t[rstmt_start:])
    rstmt = t[rstmt_start: rstmt_start + m.start()].strip()
    for o, nw in subs: rstmt = ident_sub(rstmt, o, nw)
    if rstmt_override: rstmt = "fun s' => " + rstmt_override
    rstmt = rstmt.replace("s'.mem", "s'.mem")
    # statement of nonvacuous: ends at first ' :=' newline after n
    m2 = re.search(r' :=\n', t[n:])
    sp = n + m2.start()
    # term: from after ' :=\n' to first blank line
    ts = n + m2.end()
    te = t.index('\n\n', ts)
    term = t[ts:te].rstrip()
    assert term.endswith('⟩'), term[-20:]
    term = term[:-1] + ', ' + ', '.join(terms + [returns_term]) + '⟩'
    stmt = t[n:sp] + ' ∧\n    ' + ' ∧\n    '.join(conjs + ['Returns ((Extracted.program.link impl).withExit ret) s fun s\' => ' + rstmt.split("fun s' =>",1)[1].strip()])
    new_nonvac = stmt + ' :=\n' + t[ts:ts] + term + t[te:r if False else te]
    # assemble: [..ins) site_ws + returns_block(moved) + [ins..n) + new nonvacuous + rest with returns block removed
    pre = t[:ins]
    mid = t[ins:n]
    rest_after_nonvac = t[te:rd] + t[e:]
    out = pre + site_ws.rstrip('\n') + '\n\n' + rblock.rstrip('\n') + '\n\n' + mid + new_nonvac + rest_after_nonvac
    open(path, 'w').write(out)
