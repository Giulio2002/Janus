#!/usr/bin/env python3
"""Mechanical migration of an example/test proof file to the v0.4.0 `Ensures` shape.

Usage: scripts/dev/migrate-v040.py FILE.lean [...]     (rewrites in place; prints what needs a manual look)

Rewrites (see CHANGELOG.md, "v0.4.0", Migration guide):
 1. Main theorems stated with Ensures / EnsuresResults / EnsuresWithin / EnsuresGo / EnsuresGoX /
    RunsAtLeastOnCall: the old proof body is kept, preceded by `janus_ensures_old` (arm64) or
    `janus64_ensures_old` (amd64); that tactic proves `pre s -> pre (s.setRet ret)` and leaves the old-shaped goal,
    so the following `intro ret hret s hs hpre ...` is unchanged.
 2. Witnesses that apply such a theorem: `CallSetup (P.withExit ret) E args s` -> `CallSetup0 E args s`;
    `Returns|ReturnsWithin n|RunsAtLeast n (P.withExit ret) s` -> the same at `(s.setRet ret)`, with every free `s` of that
    conjunct (the `ABIReturn s s'` and any `s` in the post) replaced by `(s.setRet ret)`; the application
    `thm args ret hret s0 hs hpre` -> `thm args s0 hs hpre ret hret`; the `setup` lemma loses the return-address field
    (amd64) / gains the `len` field (arm64).
Raw old-shaped statements (`faults`, `panics`, ...: `∀ ret, RetAddr .. -> ∀ s, CallSetup ..`) are NOT Ensures forms and are
left alone, with the witness states they use.
"""
import re, sys

HEADS = ['Ensures', 'EnsuresResults', 'EnsuresWithin', 'EnsuresGo', 'EnsuresGoX', 'RunsAtLeastOnCall']
HEADRE = re.compile(r'(?<![\w.])(?:' + '|'.join(HEADS) + r')(?![\w])')

def split_blocks(t):
    starts = [m.start() for m in re.finditer(r'^(?:theorem|lemma|def|abbrev|namespace|end|set_option [^\n]* in\n(?=(?:set_option|/--|theorem|lemma)))', t, re.M)]
    return starts

def migrate(t, amd0):
    warn = []
    # split into top-level items: each starts at a line beginning with theorem/lemma/def/namespace/end/set_option/`/--`
    items = re.split(r'(?m)^(?=(?:theorem |lemma |example |def |abbrev |namespace |end |set_option |/--))', t)
    # the ISA of each item: the last `open ...` line seen decides (a file may hold both an arm64 and an amd64 section)
    isa = []
    cur = amd0
    for it in items:
        for ol in re.findall(r'(?m)^open [^\n]*', it):
            if 'Janus.Amd64' in ol: cur = True
            elif 'Janus.Arm64' in ol or 'Janus.GoABI' in ol: cur = False
        isa.append(cur)
    # pass 1: Ensures-head theorems
    ens = set()
    for i, it in enumerate(items):
        amd = isa[i]
        tac = 'janus64_ensures_old' if amd else 'janus_ensures_old'
        m = re.match(r'(?:theorem|lemma) ([\w.]+)', it) or re.match(r'(example)\b', it)
        if m and ':= by' in it:
            head = it.split(':= by', 1)[0]
            if HEADRE.search(head) and 'Witness' not in head:
                if m.group(1) != 'example': ens.add(m.group(1))
                if re.search(r':= by\n[ \t]*janus6?4?_ensures_old', it):
                    it2, n = it, 1
                else:
                    def ins(mm):   # `intro h₁ h₂ ret hret …`: the leading names (the statement's hypotheses) are introduced first
                        pre = mm.group(3).strip()
                        return mm.group(1) + (mm.group(2) + 'intro ' + pre + '\n' if pre else '') + mm.group(2) + tac + '\n' + mm.group(2) + 'intro ret hret'
                    it2, n = re.subn(r'(:= by\n)([ \t]*)intro ((?:[\w\'_]+ )*?)ret hret', ins, it, count=1)
                if n == 0: warn.append('theorem %s: no `intro ret hret` right after `:= by`' % (m.group(1)))
                items[i] = it2
    # pass 2: setups used with an Ensures-head theorem
    appre = re.compile(r'(?<![\w.])((?:Proof\.)?(?:' + '|'.join(re.escape(n) for n in sorted(ens)) + r')) ((?:\([^()]*\) |[\w.]+ )*?)ret hret (\w+) (\w+) ([^\s⟩,)]+)') if ens else None
    used_setups = set()
    if appre:
        for it in items:
            for m in appre.finditer(it): used_setups.add(m.group(4))
    for i, it in enumerate(items):
        amd = isa[i]
        m = re.match(r'(?:theorem|lemma) ([\w.]+)', it)
        if not m: continue
        name = m.group(1)
        if name in used_setups and re.search(r'CallSetup \(', it):
            it = re.sub(r'CallSetup \((?:[^()]|\([^()]*\))*?\.withExit ret\) ([\w.]+) (\[[^\]]*\]) (\w+)', r'CallSetup0 \1 \2 \3', it)
            if amd: it = it.replace('⟨rfl, by decide, rfl, by decide,', '⟨rfl, rfl, by decide,')
            else: it = re.sub(r'⟨rfl, rfl, by', '⟨rfl, by decide, by', it)
            if 'CallSetup0' not in it: warn.append('setup %s not rewritten' % name)
            items[i] = it
            continue
        # witnesses applying an Ensures-head theorem
        if '∃' in it.split(':=', 1)[0] and appre and appre.search(it):
            it = re.sub(r'CallSetup \((?:[^()]|\([^()]*\))*?\.withExit ret\) ([\w.]+) (\[[^\]]*\]) (\w+)', r'CallSetup0 \1 \2 \3', it)
            lines = it.split('\n')
            k = 0
            while k < len(lines):
                if re.search(r'(Returns|ReturnsWithin \d+|RunsAtLeast \d+) \((?:[^()]|\([^()]*\))*?\.withExit ret\) s(?![\w\'])', lines[k]):
                    j = k
                    while True:
                        lines[j] = re.sub(r'(?<![\w.\'])s(?![\w\'])', '(s.setRet ret)', lines[j])
                        if ':=' in lines[j] or j + 1 >= len(lines) or not lines[j + 1].strip(): break
                        j += 1
                    k = j
                k += 1
            it = '\n'.join(lines)
            it = appre.sub(lambda mm: f'{mm.group(1)} {mm.group(2)}{mm.group(3)} {mm.group(4)} {mm.group(5)} ret hret', it)
            items[i] = it
    return ''.join(items), warn

for f in sys.argv[1:]:
    t = open(f).read()
    amd = 'Janus.Amd64' in t
    t2, warn = migrate(t, amd)
    open(f, 'w').write(t2)
    print(f, ('WARN: ' + '; '.join(warn)) if warn else 'ok')
