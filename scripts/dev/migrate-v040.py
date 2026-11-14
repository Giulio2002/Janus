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

HEADS = ['Ensures', 'EnsuresResults', 'EnsuresWithin', 'EnsuresGo', 'EnsuresGoX', 'RunsAtLeastOnCall',
         # phase 1b: the other main-theorem forms (ABI0, C ABI, cgo contracts, syscalls, stack growth)
         'Ensures0', 'EnsuresResults0', 'CEnsures', 'CEnsuresResults', 'CEnsuresA', 'CEnsuresR', 'EnsuresC',
         'CEnsuresC', 'EnsuresK', 'EnsuresGrow', 'EnsuresGrow64']
HEADRE = re.compile(r'(?<![\w.])(?:' + '|'.join(HEADS) + r')(?![\w])')

def split_blocks(t):
    starts = [m.start() for m in re.finditer(r'^(?:theorem|lemma|def|abbrev|namespace|end|set_option [^\n]* in\n(?=(?:set_option|/--|theorem|lemma)))', t, re.M)]
    return starts

SETUP_RE = re.compile(r'\b(CallSetup0|CallSetup|CCallA|CCall)\b ((?:\((?:[^()]|\([^()]*\))*?\.withExit \w+\)))\s*')
SETUP_NEW = {'CallSetup': 'CallSetup0', 'CallSetup0': 'CallSetupF', 'CCall': 'CCallF', 'CCallA': 'CCallAF'}

def fix_setups(text):
    """`CallSetup (P.withExit ret) E …` -> `CallSetup0 E …` (and CCall -> CCallF, CCallA -> CCallAF, ABI0 CallSetup0 -> CallSetupF)."""
    return SETUP_RE.sub(lambda m: SETUP_NEW[m.group(1)] + ' ', text)

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
    ens = {}
    for i, it in enumerate(items):
        amd = isa[i]
        tac = 'janus64_ensures_old' if amd else 'janus_ensures_old'
        m = re.match(r'(?:theorem|lemma) ([\w.]+)', it) or re.match(r'(example)\b', it)
        if m and ':=' in it and ':= by' not in it and HEADRE.search(it.split(':=', 1)[0]) and 'Witness' not in it.split(':=', 1)[0]:
            # a term-mode proof of a main theorem (`:= (go_spec x y).refine refines`): registered, nothing to insert
            if m.group(1) != 'example':
                ens[m.group(1)] = bool(re.search(r'(?<![\w.])EnsuresK(?![\w])', it.split(':=', 1)[0]))
        if m and ':= by' in it:
            head = it.split(':= by', 1)[0]
            if HEADRE.search(head) and 'Witness' not in head:
                if re.search(r'(?<![\w.])EnsuresGrow(64)?(?![\w])', head):
                    warn.append('theorem %s: EnsuresGrow needs the manual `caller` split (see CHANGELOG, v0.4.0: GCaller, correctness_old + of_old_with); not rewritten' % m.group(1))
                    continue
                if m.group(1) != 'example': ens[m.group(1)] = bool(re.search(r'(?<![\w.])EnsuresK(?![\w])', head))
                if re.search(r':= by\n[ \t]*janus6?4?_ensures_old', it):
                    it2, n = it, 1
                else:
                    def ins(mm):   # `intro h₁ h₂ ret hret …`: the leading names (the statement's hypotheses) are introduced first
                        pre = mm.group(3).strip()
                        return mm.group(1) + (mm.group(2) + 'intro ' + pre + '\n' if pre else '') + mm.group(2) + tac + '\n' + mm.group(2) + 'intro ret hret'
                    it2, n = re.subn(r'(:= by\n)([ \t]*)intro ((?:[\w\'_]+ )*?)ret hret', ins, it, count=1)
                if n == 0: warn.append('theorem %s: no `intro ret hret` right after `:= by`' % (m.group(1)))
                items[i] = it2
    # pass 2: applications `thm args RET hret s0 setup pre` (EnsuresK: `RET hret s0 k0 setup pre`) of Ensures-head theorems
    def app_re(names):
        if not names: return None
        return re.compile(r'(?<![\w.])((?:Proof\.)?(?:' + '|'.join(re.escape(n) for n in sorted(names)) + r')) ((?:\([^()]*\) |[^\s()⟨⟩]+ )*?)(\w+) hret (\w+) ')
    plain = {n for n, k in ens.items() if not k}
    kern = {n for n, k in ens.items() if k}
    def find_apps(it):
        out = []
        for names, isk in ((plain, False), (kern, True)):
            r = app_re(names)
            if not r: continue
            tail = r'(\w+) (\w+) (⟨[^⟩]*⟩|\([^)]*\)|[^\s⟩,)]+)' if isk else r'(\w+) (⟨[^⟩]*⟩|\([^)]*\)|[^\s⟩,)]+)'
            r2 = re.compile(r.pattern + tail)
            for m in r2.finditer(it): out.append((m, isk))
        return out
    used_setups = set()
    for it in items:
        for m, isk in find_apps(it): used_setups.add(m.group(6 if isk else 5))
    for i, it in enumerate(items):
        amd = isa[i]
        m = re.match(r'(?:theorem|lemma) ([\w.]+)', it)
        if not m: continue
        name = m.group(1)
        if name in used_setups and SETUP_RE.search(it):
            it = fix_setups(it)
            if amd:
                it = re.sub(r'⟨rfl, (?:by decide|rfl), ', '⟨rfl, ', it, count=1)   # amd64: drop the `[RSP] = ret` field
            elif 'CallSetupF' in it:      # ABI0 (arm64): pc, lr, argWords, frame, spAligned -> pc, argWords, frame, spAligned
                it = re.sub(r'⟨rfl, rfl, by', '⟨rfl, by', it)
            else:
                it = re.sub(r'⟨rfl, rfl, by', '⟨rfl, by decide, by', it)
            if SETUP_RE.search(it): warn.append('setup %s not rewritten' % name)
            items[i] = it
            continue
        # any other item that applies an Ensures-head theorem: a witness (`∃ …`) or a `returns` statement
        apps = find_apps(it)
        exw = '∃' in it.split(':=', 1)[0] and SETUP_RE.search(it) is not None   # a witness statement that states a call
        if (apps or exw) and name not in ens:
            it = fix_setups(it)
            states = {'s'} | {mm.group(4) for mm, isk in apps}
            hm = re.search(r'RetAddr \S+ (\w+)', it.split(':=', 1)[0])
            retv = hm.group(1) if '∃' in it.split(':=', 1)[0] and hm else (apps[0][0].group(3) if apps else 'ret')
            lines = it.split('\n')
            k = 0
            while k < len(lines):
                if re.search(r'(Returns\w*|GrownReturns\w*|RunsAtLeast \d+|ReturnsWithin \d+) \((?:[^()]|\([^()]*\))*?\.withExit \w+\)', lines[k]) and 'setRet' not in lines[k]:
                    j = k
                    while True:
                        for st in states:
                            lines[j] = re.sub(r'(?<![\w.\'])' + re.escape(st) + r'(?![\w\'])', '(' + st + '.setRet ' + retv + ')', lines[j])
                        if ':=' in lines[j] or j + 1 >= len(lines) or not lines[j + 1].strip(): break
                        j += 1
                    k = j
                k += 1
            it = '\n'.join(lines)
            def sub_plain(mm):
                return f'{mm.group(1)} {mm.group(2)}{mm.group(4)} {mm.group(5)} {mm.group(6)} {mm.group(3)} hret'
            def sub_k(mm):
                return f'{mm.group(1)} {mm.group(2)}{mm.group(4)} {mm.group(5)} {mm.group(6)} {mm.group(7)} {mm.group(3)} hret'
            for names, isk in ((plain, False), (kern, True)):
                r = app_re(names)
                if not r: continue
                tail = r'(\w+) (\w+) (⟨[^⟩]*⟩|\([^)]*\)|[^\s⟩,)]+)' if isk else r'(\w+) (⟨[^⟩]*⟩|\([^)]*\)|[^\s⟩,)]+)'
                r2 = re.compile(r.pattern + tail)
                it = r2.sub(sub_k if isk else sub_plain, it)
            items[i] = it
    return ''.join(items), warn

for f in sys.argv[1:]:
    t = open(f).read()
    amd = 'Janus.Amd64' in t
    t2, warn = migrate(t, amd)
    open(f, 'w').write(t2)
    print(f, ('WARN: ' + '; '.join(warn)) if warn else 'ok')
