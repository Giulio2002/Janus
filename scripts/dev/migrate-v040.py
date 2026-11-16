#!/usr/bin/env python3
"""Mechanical migration of a proof tree to the v0.4.0 main-theorem shape (`Ensures` & co. evaluate the precondition
BEFORE the return address is installed).

Usage: scripts/dev/migrate-v040.py FILE.lean [FILE.lean ...]     (rewrites in place; prints what needs a manual look)
       scripts/dev/migrate-v040.py --check-idempotent FILE.lean ...  (migrates a temporary copy twice; exit 1 unless the second run changes nothing)

Give it the WHOLE tree in one call (`find lean -name '*.lean' | xargs scripts/dev/migrate-v040.py`): a first pass over
all files collects the names of the theorems whose conclusion is an `Ensures` form (so applications of them in other
files are recognised); the second pass rewrites each file.

Rewrites (see CHANGELOG.md, "v0.4.0", Migration guide):
 1. ROW theorems (conclusion `Ensures …` / `Ensures0 …` / `EnsuresWithin …` / … with a concrete precondition): `janus_ensures_old`
    (arm64) / `janus64_ensures_old` (amd64) is inserted as the first tactic; it proves `pre s -> pre (s.setRet ret)` and
    leaves the old-shaped goal, so the old proof (`intro ret hret s hs hpre …`, `rw`s and comments before it included) is
    unchanged. A term-mode `:= fun ret hret s hs … => …` becomes `:= by janus_ensures_old; exact (fun …)`.
 2. GENERIC HELPERS (conclusion `Ensures P entry args pre post` with `pre` a bound variable, e.g. `Ensures.full64`,
    `ensures_of_summary`): a last binder `(hinv : Ensures.SetRetInv P entry args pre := by janus_pre_setRet)` is added and the
    proof starts with `refine Ensures.of_old hinv ?_`. Call sites are unchanged (the default tactic proves `hinv` for their
    concrete `pre`).
 3. Old-shaped applications `thm args ret hret s hs hp` of such theorems (inside an old-shaped proof) become
    `(thm args).toOld ret hret s hs hp`.
 4. Witnesses (`namespace Witness`): `CallSetup (P.withExit ret) E args s` -> `CallSetup0 E args s` (the `setup` lemma loses
    the return-address field on amd64 / replaces `lr` by `len` on arm64); `Returns|ReturnsWithin n|RunsAtLeast n
    (P.withExit ret) s …` -> the same at `(s.setRet ret)`, with every free `s` of that conjunct replaced by `(s.setRet ret)`;
    the application `thm args ret hret s0 setup pre` -> `thm args s0 setup pre ret hret`.
Raw old-shaped statements (`faults`, `panics`, ...: `∀ ret, RetAddr .. -> ∀ s, CallSetup ..`) are NOT Ensures forms and are
left alone, with the witness states they use. `Ensures.mono`, `Ensures0.of_summary0`, `Ensures.toSummaryIn`, `janus_intro`,
`janus64_intro` keep their v0.3 signatures and need no rewrite.
"""
import re, sys, os

FORCE = set(filter(None, os.environ.get('JANUS_MIG_FORCE', '').split(',')))   # witness items to rewrite although no application of a main theorem is seen in them

HEADS = ['Ensures', 'EnsuresResults', 'EnsuresWithin', 'EnsuresGo', 'EnsuresGoX', 'RunsAtLeastOnCall',
         'Ensures0', 'EnsuresResults0', 'CEnsures', 'CEnsuresResults', 'CEnsuresA', 'CEnsuresR', 'EnsuresC',
         'CEnsuresC', 'EnsuresK', 'EnsuresGrow', 'EnsuresGrow64']
HEADRE = re.compile(r'(?<![\w.])(?:' + '|'.join(HEADS) + r')(?![\w.])')
CONCL = re.compile(r'^\s*((?:\w+\.)*)(' + '|'.join(HEADS) + r')(?![\w.])')

OPEN, CLOSE = '([{⟨', ')]}⟩'

def depth_scan(s, start=0):
    """Yield (index, char, depth-before) skipping `--` comments."""
    d = 0
    i = start
    n = len(s)
    while i < n:
        c = s[i]
        if c == '-' and s[i:i + 2] == '--':
            j = s.find('\n', i)
            i = n if j < 0 else j
            continue
        if c in OPEN: d += 1
        elif c in CLOSE: d -= 1
        yield i, c, d
        i += 1

def split_sig(it):
    """(sig, body_start): the signature of a `theorem`/`lemma` item up to its top-level `:=`, and the index just after it."""
    d = 0
    i = 0
    n = len(it)
    while i < n:
        c = it[i]
        if c == '-' and it[i:i + 2] == '--':
            j = it.find('\n', i); i = n if j < 0 else j; continue
        if c in OPEN: d += 1
        elif c in CLOSE: d -= 1
        elif c == ':' and d == 0 and it[i:i + 2] == ':=':
            return it[:i], i + 2
        i += 1
    return None, None

def top_colon(sig):
    """Index of the top-level `:` that starts the conclusion."""
    d = 0
    i = 0
    n = len(sig)
    # skip the name
    while i < n:
        c = sig[i]
        if c == '-' and sig[i:i + 2] == '--':
            j = sig.find('\n', i); i = n if j < 0 else j; continue
        if c in OPEN: d += 1
        elif c in CLOSE: d -= 1
        elif c == ':' and d == 0 and sig[i:i + 2] != ':=': return i
        i += 1
    return -1

def tokens(s, i=0):
    """Whitespace-separated balanced tokens starting at index i, until a `,`/`:=`/closer/`|` at depth 0.
    Returns [(tok, start, end)] and the index where scanning stopped."""
    out = []
    n = len(s)
    while i < n:
        while i < n and s[i] in ' \t\n': i += 1
        if i >= n: break
        if s[i] in CLOSE or s[i] == ',' or s[i:i + 2] == ':=' or s[i] == '|': break
        st = i
        d = 0
        while i < n:
            c = s[i]
            if c == '-' and s[i:i + 2] == '--' and d == 0: break
            if c in OPEN: d += 1
            elif c in CLOSE:
                if d == 0: break
                d -= 1
            elif d == 0 and (c in ' \t\n,' or s[i:i + 2] == ':='): break
            i += 1
        if i == st: break
        out.append((s[st:i], st, i))
    return out, i

def split_top(s, sep=','):
    """Split `s` at top-level `sep` (depth 0)."""
    parts = []
    d = 0
    last = 0
    for i, c, dep in depth_scan(s):
        if c in OPEN: pass
        if c == sep and dep == 0:
            parts.append(s[last:i]); last = i + 1
    parts.append(s[last:])
    return parts

def conclusion(it):
    """(head_prefix, head, conclusion_text, sig, body_start) for a theorem whose conclusion is an Ensures form, else None."""
    sig, bs = split_sig(it)
    if sig is None: return None
    ci = top_colon(sig)
    if ci < 0: return None
    concl = sig[ci + 1:]
    if not CONCL.match(concl):
        # `H₁ → H₂ → Ensures …` (hypotheses after the colon): the conclusion is what follows the last top-level arrow
        d = 0; last = -1
        for q, c in enumerate(concl):
            if c in OPEN: d += 1
            elif c in CLOSE: d -= 1
            elif d == 0 and c == '→': last = q
        if last >= 0: concl = concl[last + 1:]
    m = CONCL.match(concl)
    if not m: return None
    return m.group(1), m.group(2), concl, sig, bs, ci

def is_generic(head, concl, sig):
    """`Ensures P entry args pre post` with `pre` a bound identifier of the signature: a generic helper."""
    if head != 'Ensures': return None
    m = CONCL.match(concl)
    toks, _ = tokens(concl, m.end())
    if len(toks) != 5: return None
    P, ent, args, pre, post = [t[0] for t in toks]
    if not re.fullmatch(r"[A-Za-z_][\w']*", pre): return None
    if not re.search(r'[({{\[]\s*(?:[\w\']+\s+)*' + re.escape(pre) + r'(?:\s+[\w\']+)*\s*:', sig): return None
    return P, ent, args, pre

SETUP_RE = re.compile(r'\b(CallSetup0|CallSetup|CCallA|CCall)\b\s+(\()')
SETUP_NEW = {'CallSetup': 'CallSetup0', 'CallSetup0': 'CallSetupF', 'CCall': 'CCallF', 'CCallA': 'CCallAF'}

def fix_setups(text):
    """`CallSetup (P.withExit ret) E …` -> `CallSetup0 E …` (and CCall -> CCallF, CCallA -> CCallAF, ABI0 CallSetup0 -> CallSetupF).
    The program argument is a balanced parenthesised term ending in `.withExit R)`."""
    out = []
    i = 0
    while True:
        m = SETUP_RE.search(text, i)
        if not m:
            out.append(text[i:]); break
        out.append(text[i:m.start()])
        # balanced paren starting at m.start(2)
        d = 0
        j = m.start(2)
        while j < len(text):
            if text[j] == '(': d += 1
            elif text[j] == ')':
                d -= 1
                if d == 0: break
            j += 1
        inner = text[m.start(2):j + 1]
        if '.withExit' in inner:
            out.append(SETUP_NEW[m.group(1)] + ' ')
            i = j + 1
            while i < len(text) and text[i] == ' ': i += 1
        else:
            out.append(text[m.start():m.end()]); i = m.end()
    return ''.join(out)

def first_tactic_pos(it, bs):
    """Position (index in `it`) and indentation of the first tactic of a `:= by` body, or None."""
    m = re.match(r'\s*by\b[ \t]*', it[bs:])
    if not m: return None
    j = bs + m.end()
    # the first tactic is on the same line (`:= by tac`) or on the next non-empty line
    rest = it[j:]
    if rest.startswith('\n') or rest.strip() == '' or rest.lstrip(' \t').startswith('\n'):
        mm = re.match(r'[ \t]*\n((?:[ \t]*\n)*)([ \t]*)', rest)
        if not mm: return None
        return j + mm.end(1) + len(rest[:mm.end(1)]) - len(rest[:mm.end(1)]) if False else (j + mm.end(), len(mm.group(2)), True)
    return (j, None, False)


def lambda_binders(s, i):
    """Binder tokens of the `fun b1 b2 … =>` starting at index i (`fun` at i); returns ([(tok,start,end)], index of `=>`)."""
    toks, stop = tokens(s, i + 3)
    out = []
    for tk in toks:
        if tk[0] == '=>' : break
        out.append(tk)
    # the `=>` is a token on its own at top level
    j = s.find('=>', out[-1][2] if out else i + 3)
    return out, j

def fix_mono(it, warn, ok_heads=None):
    """`Ensures.mono h hpre hpost` / `(h …).mono hpre hpost` with the v0.3 `hpost` (`fun s s' hp hq`): the first binder `_`
    (or unused) -> `mono_ret` with one more `_` (the new `hpost` also binds `ret`)."""
    out = []
    pos = 0
    pat = re.compile(r'(?<![\w.\'])((?:[\w]+\.)*Ensures0?)\.mono(?![\w\'])|\)\.mono(?![\w\'])')
    while True:
        m = pat.search(it, pos)
        if not m: break
        toks, stop = tokens(it, m.end())
        dot = m.group(1) is None
        if dot and ok_heads is not None:
            # `(h args).mono …`: only when the receiver is an Ensures-form theorem or hypothesis (`Summary.mono` has the same shape)
            d = 0; q = m.start()
            while q >= 0:
                if it[q] == ')': d += 1
                elif it[q] == '(':
                    d -= 1
                    if d == 0: break
                q -= 1
            hd = re.match(r"\(\s*([\w.']+)", it[q:]) if q >= 0 else None
            if not hd or hd.group(1).split('.')[-1] not in ok_heads and hd.group(1) not in ok_heads:
                out.append(it[pos:m.end()]); pos = m.end(); continue
        # locate the hpost lambda: the last argument, `(fun …)` or an unparenthesised `fun …`
        k = None
        for q, tk in enumerate(toks):
            if tk[0] == 'fun' and q >= (1 if dot else 2):
                k = q; break
            if tk[0].startswith('(fun ') and q >= (1 if dot else 2):
                k = q; break
        if k is None or (k != (1 if dot else 2)):
            out.append(it[pos:m.end()]); pos = m.end(); continue
        if dot:
            # `.mono (fun s hp => …) fun s s' hp hq => …`: the first argument must be a lambda
            if not toks[0][0].startswith('(fun '):
                out.append(it[pos:m.end()]); pos = m.end(); continue
        tk = toks[k]
        if tk[0].startswith('(fun '):
            fpos = tk[1] + 1                  # `fun` after the `(`
        else:
            fpos = tk[1]
        bt, arrow = lambda_binders(it, fpos)
        if len(bt) < 3:
            out.append(it[pos:m.end()]); pos = m.end(); continue
        first = bt[0][0]
        body = it[arrow + 2:tk[2]]
        if first != '_' and re.search(r'(?<![\w.\'])' + re.escape(first) + r'(?![\w\'])', body):
            warn.append('Ensures.mono with a named state binder `%s` used in the postcondition proof: adjust by hand (mono_ret binds the state without the return address)' % first)
            out.append(it[pos:m.end()]); pos = m.end(); continue
        newname = ('Ensures0.mono_ret' if (m.group(1) or '').endswith('Ensures0') else (m.group(1) + '.mono_ret' if m.group(1) else ').mono_ret'))
        out.append(it[pos:m.start()])
        out.append(newname)
        # copy up to the end of the first binder, then add `_`
        out.append(it[m.end():bt[0][2]])
        out.append(' _')
        pos = bt[0][2]
    out.append(it[pos:])
    return ''.join(out)

def add_hlen(it, amd, warn, name, reg=None):
    """arm64 generic wrapper over an `Ensures` hypothesis with generic `args`: `Ensures.toSummaryIn h …` needs
    `ArgsFit args` (`args.length ≤ numIntRegs`, an instance for every literal list); the wrapper takes `[ArgsFit args]`."""
    if amd: return it
    sig, bs = split_sig(it)
    if sig is None or name.split('.')[-1] not in (reg.argsfit if reg else set()): return it
    if not re.search(r'\{args\s*:\s*List', sig): return it
    if 'ArgsFit' in sig: return it
    ci = top_colon(sig)
    sig2 = sig[:ci].rstrip() + ' [ArgsFit args] ' + sig[ci:]
    return sig2 + ':=' + it[bs:]

class Reg:
    names = set()       # theorem names (as written) whose conclusion is an Ensures form
    generic = set()
    imports = {}        # file -> [imported module names]
    modfile = {}        # module name -> file
    aliases = []
    argthms = []        # (name, body) of theorems with a generic `{args : List …}` binder
    argsfit = set()     # those that (transitively) call `Ensures.toSummaryIn`: they take `[ArgsFit args]`
    ensdefs = {}        # defs whose body is `∀ …, Ensures …` (a spec: `Hyp2 impl R …`) -> (file, body)
    setupnames = set()  # theorems `name : CallSetup (P.withExit R) …` (last component)
    setupused = set()   # those passed as the setup of a `ret hret s SETUP` application anywhere in the consumer tree
    local_non = set()   # raw old-shaped theorems of the file being migrated
    opens = {}          # file -> namespaces it opens
    isa_amd = {}        # file -> True when it works on the amd64 model
    fns = {}            # file -> its namespace (the first `namespace X` line)
    defs = {}           # last component of a def/abbrev name -> [(file, body text)] for the Prop-valued ones

DEFRE = re.compile(r'(?m)^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:def|abbrev) ([\w.\']+)')

ENSDEF = re.compile(r'^\s*(?:∀[^,]*,\s*)*(?:\w+\.)*(?:' + '|'.join(HEADS) + r')(?![\w.])')

def collect_ensdefs(t, reg):
    parts = re.split(r'(?m)^(?=(?:theorem |lemma |example |def |abbrev |namespace |end |set_option |/--|@\[|private |protected |noncomputable |structure |instance |attribute |open |section ))', t)
    for it in parts:
        m = DEFRE.match(it)
        if not m: continue
        sig, bs = split_sig(it)
        if sig is None: continue
        body = it[bs:].strip()
        if body.startswith('by'): continue
        if ENSDEF.match(re.sub(r'^fun [^=]*=>\s*', '', body)): reg.ensdefs[m.group(1).split('.')[-1]] = (None, it[bs:])

def collect_defs(t, f, reg):
    parts = re.split(r'(?m)^(?=(?:theorem |lemma |example |def |abbrev |namespace |end |set_option |/--|@\[|private |protected |noncomputable |structure |instance |attribute |open |section ))', t)
    ns = []
    for it in parts:
        mn = re.match(r'namespace ([\w.]+)', it)
        if mn: ns.append(mn.group(1)); continue
        me = re.match(r'end ([\w.]+)', it)
        if me:
            if ns and ns[-1] == me.group(1): ns.pop()
            continue
        m = DEFRE.match(it)
        if not m: continue
        name = m.group(1)
        qn = name if name.startswith('_root_.') else '.'.join(ns + [name])
        sig, bs = split_sig(it)
        if sig is None: continue
        ci = top_colon(sig)
        if ci < 0:           # `def Pre := PreS 4440` (no type ascription)
            reg.aliases.append((name.split('.')[-1], f, it[bs:], qn))
            continue
        concl = sig[ci + 1:].strip()
        # a definition that reads the state or its memory (`win s stk above`, `CallEnv R L s …`, `stLen m st`, `NatLive m …`):
        # installing the return address changes its argument, so it is unfolded; the others (`Serves R`, `Held R L p n`) cannot change
        nullary = concl == 'Nat' and not re.search(r'[({\[]', re.sub(r'@\[[^\]]*\]', '', sig[:ci]))      # `def gA : Nat := …`: an address constant
        if not nullary and not re.search(r'[:\s(]\s*(?:Janus\.)?(?:Amd64\.|Arm64\.)?(?:State|Memory)\b', sig[:ci]) \
                and not re.match(r'(?:Janus\.)?(?:Amd64\.|Arm64\.)?State\s*(?:→|->)', concl):      # `abbrev PreRaw (z) : State → Prop := fun s => …` reads the state too
            # an alias of such a definition (`def Pre := PreS 4440`): resolved after every file is collected
            reg.aliases.append((name.split('.')[-1], f, it[bs:], qn))
            continue
        reg.defs.setdefault(name.split('.')[-1], []).append((f, it[bs:], qn))

def modname(path):
    p = path.replace('\\', '/')
    i = p.find('lean/')
    p = p[i + 5:] if i >= 0 and p.rfind('lean/') == i else p
    return p[:-5].replace('/', '.') if p.endswith('.lean') else p

def import_closure(f, reg):
    out = set()
    stack = [f]
    while stack:
        g = stack.pop()
        if g in out: continue
        out.add(g)
        for m in reg.imports.get(g, []):
            h = reg.modfile.get(m)
            if h: stack.append(h)
    return out

# masked runtime views stay folded: `view_setRet` / `rtView_setRet` (amd64 janus64_pre_setRet) rewrite them as they are
NO_UNFOLD = {'rtView', 'view'}

def unfold_list(pre_text, reg, f, bound=()):
    """The consumer's state-reading definitions reachable from `pre_text`, as fully qualified names (the definition visible
    from this file: the same file, else the import closure, else the only one; inside a definition body, the one in the
    nearest enclosing namespace)."""
    closure = import_closure(f, reg)
    seen = []
    todo = [(w, '') for w in dict.fromkeys(re.findall(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", pre_text))]
    seen_set = set()
    def common(a, b):
        n = 0
        for x, y in zip(a.split('.'), b.split('.')):
            if x != y: break
            n += 1
        return n
    while todo:
        w, owner = todo.pop(0)
        if w in bound: continue
        base = w.split('.')[-1]
        if base not in reg.defs or base in NO_UNFOLD: continue
        cands = reg.defs[base]
        if '.' in w and len(w.split('.')[0]) <= 1 and not any(c[2].endswith('.' + w) or c[2] == w for c in cands):
            continue      # `R.ok`: a field of a bound variable (`Q.NatMul.MPre` is a namespace)
        if '.' in w:
            q = [c for c in cands if c[2].endswith('.' + w) or c[2] == w]
            if q: cands = q
        same = [c for c in cands if c[0] == f]
        vis = [c for c in cands if c[0] in closure]
        opened0 = reg.opens.get(f, [])
        if len(vis) > 1:       # several definitions of that name in the import closure: the ones whose namespace the file opens
            ov = [c for c in vis if '.'.join(c[2].split('.')[:-1]) in opened0]
            if ov: vis = ov
        # precedence (Lean's name resolution, then fixed tie-breaks; never the discovery order of files or dict/set iteration):
        #   1. the definition whose namespace shares the most with the enclosing definition (inside a definition body),
        #   2. a definition in the namespace the file is in (or an enclosing one) beats one that is merely visible, the innermost first,
        #   3. a definition in an opened namespace, 4. the nearest file path, 5. qualified name, then file path.
        nsf = reg.fns.get(f, '')
        def encl(c):
            n_ = c[2].rsplit('.', 1)[0] if '.' in c[2] else ''
            return len(n_.split('.')) if n_ and (nsf == n_ or nsf.startswith(n_ + '.')) else 0
        file_amd = reg.isa_amd.get(f, 'Amd64' in f)
        isa_bad = lambda c: (('Amd64' in c[2] or 'Amd64' in c[0]) != file_amd)     # `Janus.Program.DataLoaded` (arm64) vs `Janus.Amd64.Program.DataLoaded`
        key = (lambda c: (-common(c[2], owner), -encl(c), isa_bad(c), -len(os.path.commonprefix([c[0], f])), c[2], c[0]))
        if len(vis) > 1: vis.sort(key=key)
        if len(same) > 1: same.sort(key=key)
        pick = same[0] if same else (vis[0] if vis else (cands[0] if len(cands) == 1 else None))
        if pick is None and not same and not vis:
            # a framework predicate (`Janus/…`): the file sees it through its `open`s (namespace of the definition opened)
            opened = reg.opens.get(f, [])
            lib = [c for c in cands if c[0].startswith('Janus/') and '.'.join(c[2].split('.')[:-1]) in opened]
            if len(lib) > 1: lib = [c for c in lib if not isa_bad(c)]       # `Contracts.Iface` and `Contracts.IfaceAmd64` both opened: the file's ISA decides
            if len(lib) == 1: pick = lib[0]
        if pick is None or pick[2] in seen_set: continue
        seen_set.add(pick[2])
        seen.append(pick[2])
        for w2 in re.findall(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", pick[1]):
            todo.append((w2, pick[2]))
    return seen

TACTIC_WORDS = {'exact', 'refine', 'apply', 'simp', 'intro', 'rw', 'have', 'show', 'calc', 'decide', 'omega', 'rfl', 'trivial', 'assumption', 'constructor', 'cases', 'rcases', 'obtain', 'by', 'fun'}

def collect(t, reg):
    items = re.split(r'(?m)^(?=(?:theorem |lemma |example |def |abbrev |namespace |end |set_option |/--|@\[|private |protected ))', t)
    for it in items:
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )*(?:theorem|lemma) ([\w.\']+)', it)
        if not m: continue
        sgs, _bss = split_sig(it)
        cis = top_colon(sgs) if sgs is not None else -1
        if cis >= 0 and re.match(r'\s*(?:CallSetup|CCallA?)\s*\(', sgs[cis + 1:]) and '.withExit' in sgs[cis + 1:]: reg.setupnames.add(m.group(1).split('.')[-1])
        sg0, bs0 = split_sig(it)
        if sg0 is not None and re.search(r'\{args\s*:\s*List', sg0):
            reg.argthms.append((m.group(1).split('.')[-1], it[bs0:]))
        c = conclusion(it)
        if not c: continue
        if m.group(1) in TACTIC_WORDS: continue      # a theorem named `exact` must not turn the tactic `exact thm ..` into an application
        reg.names.add(m.group(1))
        if is_generic(c[1], c[2], c[3]): reg.generic.add(m.group(1))

def split_conj_ensures(concl):
    """The conjuncts of `E₁ ∧ E₂ ∧ …` when each starts with an Ensures-form head (top-level `∧` only), else [concl]."""
    d = 0; cuts = [0]
    for q, c in enumerate(concl):
        if c in OPEN: d += 1
        elif c in CLOSE: d -= 1
        elif d == 0 and c == '∧' and CONCL.match(concl[q + 1:]): cuts.append(q + 1)
    if len(cuts) == 1: return [concl]
    parts = [concl[cuts[k]:(cuts[k + 1] - 1 if k + 1 < len(cuts) else len(concl))] for k in range(len(cuts))]
    if any(not CONCL.match(x) or CONCL.match(x).group(2) in ('EnsuresK', 'EnsuresGrow', 'EnsuresGrow64') for x in parts): return [concl]
    return parts

def tac_with_defs(tac, head, concl, reg, fname, sig=''):
    """`janus_ensures_old [Pre, CallEnv, …]`: the consumer's Prop-valued definitions reachable from the precondition."""
    m = CONCL.match(concl)
    toks, _ = tokens(concl, m.end())
    if not toks: return tac
    PRE_IDX = {'Ensures': 3, 'EnsuresGo': 3, 'EnsuresGoX': 3, 'CEnsures': 3, 'EnsuresWithin': 4, 'Ensures0': 4, 'EnsuresResults': 4,
               'EnsuresResults0': 4, 'CEnsuresResults': 4, 'CEnsuresA': 4, 'CEnsuresR': 4, 'EnsuresC': 4, 'CEnsuresC': 4}
    if head == 'EnsuresK': pre_text = concl[m.end():]
    elif head in PRE_IDX and len(toks) > PRE_IDX[head]: pre_text = toks[PRE_IDX[head]][0]
    else: pre_text = toks[-2][0] if len(toks) >= 2 else concl
    bound = set(w for grp in re.findall(r"[({\[]\s*((?:[\w'.]+\s+)+?)[\w'.]*\s*:", sig) for w in grp.split())
    names = unfold_list(pre_text, reg, fname, bound)
    return tac + (' [' + ', '.join(names) + ']' if names else '')

NEW_SHAPED = {'Ensures0.of_summary0', 'Ensures0.of_summary0_at', 'Ensures0.of_summary', 'Ensures.mono', 'Ensures.mono_ret',
              'Ensures0.mono', 'Ensures0.mono_ret', 'Ensures.of_old', 'Ensures0.of_old', 'CEnsures.of_summary', 'CEnsuresA.of_summary',
              'EnsuresC.of_ensures', 'EnsuresGrow.of_old', 'EnsuresGrow.of_old_with'}

def proof_kind(body, reg):
    """'old' if the tactic proof starts (after rw/unfold/… and comments) with `intro … ret hret`, 'new' if it starts from a
    new-shaped lemma (`refine/exact/apply <Ensures-form theorem or helper>`), else 'none'."""
    lines = body.split('\n')[1:] if body.lstrip().startswith('by') and '\n' in body else [re.sub(r'^\s*by\s*', '', body)]
    first = body.lstrip()[2:].lstrip(' \t')
    if first and not first.startswith('\n'): lines = [first] + body.split('\n')[1:]
    n = 0
    for ln in lines:
        s = ln.strip()
        if not s or s.startswith('--'): continue
        n += 1
        if n > 30: break
        if re.match(r'(?:intro|rintro|intros)\b[^\n]*?\bret\s+hret\b', s): return 'old'
        m = re.match(r'(?:refine|exact|apply|refine\'|exact_mod_cast)\s+\(?([\w.\']+)', s)
        if m:
            nm = m.group(1)
            if nm in NEW_SHAPED or nm in reg.names or any(nm.endswith('.' + x) for x in reg.names) or nm.split('.')[-1] in {x.split('.')[-1] for x in reg.names}:
                return 'new'
        if re.match(r'(?:fun\s+ret\s+hret)', s): return 'old'
    return 'old' if re.search(r'\bret\s+hret\b', body) else 'none'

def indent_of(it, pos):
    ls = it.rfind('\n', 0, pos) + 1
    return len(it[ls:pos]) - len(it[ls:pos].lstrip(' '))

def migrate(t, amd0, reg, fname=''):
    # a theorem of THIS file whose conclusion is not an Ensures form (`correctness : Panics .. ↔ .. ∧ ..`, a raw old-shaped
    # statement) shadows a same-named Ensures theorem of another file of the tree: its applications keep the old shape
    saved_names = reg.names
    local_non = set()
    for it0 in re.split(r'(?m)^(?=(?:theorem |lemma |@\[|private |protected ))', t):
        m0 = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )*(?:theorem|lemma) ([\w.\']+)', it0)
        if not m0 or conclusion(it0): continue
        sg0, _b0 = split_sig(it0)
        ci0 = top_colon(sg0) if sg0 is not None else -1
        mh = re.match(r'\s*(?:\w+\.)*(\w+)', sg0[ci0 + 1:]) if ci0 >= 0 else None
        if mh and mh.group(1) in reg.ensdefs: continue
        if ci0 >= 0 and (HEADRE.search(sg0[ci0 + 1:]) or any(w in reg.ensdefs for w in re.findall(r"[A-Za-z_][\w']*", sg0[ci0 + 1:]))): continue
        local_non.add(m0.group(1))
    reg.names = saved_names - local_non
    reg.local_non = local_non
    try:
        return _migrate(t, amd0, reg, fname)
    finally:
        reg.names = saved_names

def _migrate(t, amd0, reg, fname=''):
    warn = []
    RAW = re.search(r'∀ ret, RetAddr|\bret hret\b[^\n]*→ ∀ s', t) is not None   # a raw old-shaped statement (faults, panics, ...) in the file
    # split into top-level items
    items = re.split(r'(?m)^(?=(?:theorem |lemma |example |def |abbrev |namespace |end |set_option |/--|@\[|private |protected ))', t)
    isa = []
    cur = amd0
    for it in items:
        for ol in re.findall(r'(?m)^open [^\n]*', it):
            if 'Janus.Amd64' in ol: cur = True
            elif ('Janus.Arm64' in ol or 'Janus.GoABI' in ol) and not re.search(r'\bJanus\.(?:Arm64|GoABI)[\w.]*\s*\(', ol): cur = False      # `open Janus.Arm64 (elem)` opens single names only
        if re.search(r'Janus\.Amd64\.GoABI\.(?:Ensures|CallSetup)', it.split(':=', 1)[0]): cur = True
        isa.append(cur)
    inw, w = [], False
    for it in items:
        if re.match(r'namespace (?:[\w.]+\.)?Witness\w*\b', it): w = True
        if re.match(r'end (?:[\w.]+\.)?Witness\w*\b', it): w = False
        inw.append(w)
    ens = {}      # row theorem name -> is EnsuresK
    # ---- pass 1: row theorems and generic helpers
    for i, it in enumerate(items):
        amd = isa[i]
        tac = 'janus64_ensures_old' if amd else 'janus_ensures_old'
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )*(?:theorem|lemma) ([\w.\']+)', it) or re.match(r'(example)\b', it)
        if not m: continue
        name = m.group(1)
        c = conclusion(it)
        if not c:
            # a spec definition as the conclusion (`Hyp2 impl R names 4256 64`, unfolding to `∀ …, Ensures …`): the old-shaped
            # intro of `ret hret` is preceded by `janus_ensures_old`
            sg, bs0 = split_sig(it)
            if sg is not None and reg.ensdefs and ':= by' in it[bs0 - 2:bs0 + 8] + it[bs0:bs0 + 8]:
                ci0 = top_colon(sg)
                hm = re.match(r'\s*((?:\w+\.)*\w+)', sg[ci0 + 1:]) if ci0 >= 0 else None
                if hm and hm.group(1).split('.')[-1] in reg.ensdefs and m and m.group(1) != 'example': ens.setdefault(m.group(1), False)       # a row theorem too
                if hm and hm.group(1).split('.')[-1] in reg.ensdefs and 'janus_ensures_old' not in it and 'janus64_ensures_old' not in it:
                    mi = re.search(r'(?m)^([ \t]*)intro ((?:[\w\'_]+ )*?)ret hret\b', it[bs0:])
                    if mi:
                        pos = bs0 + mi.start()
                        body_e = reg.ensdefs[hm.group(1).split('.')[-1]][1]
                        hmm = HEADRE.search(body_e)
                        if hmm:
                            cc2 = CONCL.match(body_e[hmm.start():])
                            if cc2: tac2 = tac_with_defs(tac, cc2.group(2), body_e[hmm.start():], reg, fname, sg)
                            else: tac2 = tac
                        else: tac2 = tac
                        lead = mi.group(2).strip()
                        if lead:       # `intro H b … ret hret …`: the statement's binders first
                            endl = pos + len(mi.group(1)) + len('intro ') + len(mi.group(2))
                            it2 = it[:pos] + mi.group(1) + 'intro ' + lead + '\n' + mi.group(1) + tac2 + '\n' + mi.group(1) + 'intro ' + it[endl:]
                        else:
                            it2 = it[:pos] + mi.group(1) + tac2 + '\n' + it[pos:]
                        items[i] = it2
            continue
        pre_, head, concl, sig, bs, ci = c
        tac = tac_with_defs(tac, head, concl, reg, fname, sig)
        cparts = split_conj_ensures(concl)
        if len(cparts) > 1:
            # `E₁ ∧ E₂ ∧ …` (several rows proved together): one `suffices` that keeps the old-shaped conjunction as the goal
            ptac0 = 'janus64_pre_setRet' if amd else 'janus_pre_setRet'
            brs = []
            for k, part in enumerate(cparts):
                mk = CONCL.match(part)
                dlk = tac_with_defs(ptac0, mk.group(2), part, reg, fname, sig)
                proj = 'h' if len(cparts) == 1 else ('h' + '.2' * k + ('.1' if k < len(cparts) - 1 else ''))
                brs.append('%s%s.of_old (by %s) %s' % (mk.group(1), mk.group(2), dlk, proj))
            tac = 'suffices h : ' + ' ∧ '.join(['_'] * len(cparts)) + ' from ⟨' + ', '.join(brs) + '⟩'
        if 'Witness' in sig.split(':', 1)[0] and False: continue
        if head in ('EnsuresGrow', 'EnsuresGrow64'):
            warn.append('theorem %s: EnsuresGrow needs the manual `caller` split (see CHANGELOG, v0.4.0: GCaller, correctness_old + of_old_with); not rewritten' % name)
            continue
        if name != 'example': ens[name] = (head == 'EnsuresK')
        gen = is_generic(head, concl, sig)
        body = it[bs:]
        bstripped = body.lstrip()
        nm = (re.match(r'\s*', body).end())
        if gen:
            if '.SetRetInv' in it[:bs] or re.search(r'(?<![\w.\'])(?:\w+\.)*Ensures0?\.of_old\b', it[bs:]): continue      # already migrated (idempotent)
            P, ent, args, pre = gen
            hn = 'hinv'
            if re.search(r'\bhinv\b', it): hn = 'hinv\''
            ptac = 'janus64_pre_setRet' if amd else 'janus_pre_setRet'
            prefix = pre_ + 'Ensures'
            binder = ' (%s : %s.SetRetInv %s %s %s %s := by %s)' % (hn, prefix, P, ent, args, pre, ptac)
            sig2 = sig[:ci].rstrip() + binder + ' ' + sig[ci:]
            ref = 'refine %s.of_old %s ?_' % (prefix, hn)
            if bstripped.startswith('by'):
                pos = first_tactic_pos(it, bs)
                if pos is None:
                    warn.append('theorem %s: cannot find the first tactic' % name); continue
                p, ind, nl = pos
                if nl:
                    items[i] = sig2 + ':=' + it[bs:p] + ' ' * 0 + ref + '\n' + ' ' * ind + it[p:]
                else:
                    indent = indent_of(it, bs) + 2
                    items[i] = sig2 + ':= by\n' + ' ' * indent + ref + '\n' + ' ' * indent + it[p:].lstrip()
            else:
                tb = body.rstrip()
                trail = body[len(tb):]
                items[i] = sig2 + ':= by\n  ' + ref + '\n  exact (' + tb.lstrip() + ')' + trail
            continue
        # a row theorem
        if bstripped.startswith('by'):
            if re.match(r'\s*by\s*\n\s*(?:--[^\n]*\n\s*)*(?:(?:apply|refine) (?:[\w.]+\.)?toGoX?\b[^\n]*\n\s*(?:--[^\n]*\n\s*)*)?(?:janus6?4?_ensures_old|suffices h : _ (?:∧ _ )*from ⟨(?:[\w.]+\.)?\w+\.of_old \(by janus6?4?_pre_setRet)', body): continue     # already migrated (idempotent)
            mhd = re.search(r"(?m)^[ \t]*intro (?:[\w'_]+ )*?ret hret", body)
            if mhd and re.search(r'janus6?4?_ensures_old', body[:mhd.start()]): continue     # `intro H1 H2` / `apply Ensures.toGo` + the bridge before the old-shaped intro: already migrated (idempotent)
            kind = proof_kind(body, reg)
            if kind == 'new': continue          # starts from a new-shaped lemma (`refine Ensures0.of_summary0 …`, a helper): unchanged
            if kind == 'none':
                warn.append('theorem %s: the proof is neither old-shaped (`intro ret hret …`) nor a new-shaped lemma application; adjust by hand' % name)
                continue
            pos = first_tactic_pos(it, bs)
            if pos is None:
                warn.append('theorem %s: cannot find the first tactic' % name); continue
            p, ind, nl = pos
            # `apply Ensures.toGo` (an EnsuresGo derived from an Ensures) comes first: the bridge goes after it, on the Ensures it leaves
            mt = re.match(r'(?:apply|refine) (?:[\w.]+\.)?toGoX?\b[^\n]*\n([ \t]*)', it[p:])
            if mt:
                p += mt.end(); ind = len(mt.group(1)); nl = True
            # statement-level hypotheses: `intro h₁ h₂ ret hret …` introduces them first
            rest = it[p:]
            mi = re.match(r'intro ((?:[\w\'_]+ )*?)ret hret', rest)
            if mi and mi.group(1).strip():
                items[i] = it[:p] + 'intro ' + mi.group(1).strip() + '\n' + ' ' * (ind or 2) + tac + '\n' + ' ' * (ind or 2) + 'intro ret hret' + rest[mi.end():]
            elif nl:
                items[i] = it[:p] + tac + '\n' + ' ' * ind + rest
            else:
                indent = indent_of(it, bs) + 2
                items[i] = it[:bs] + ' by\n' + ' ' * indent + tac + '\n' + ' ' * indent + rest.lstrip() if False else \
                    it[:p] + '\n' + ' ' * indent + tac + '\n' + ' ' * indent + rest.lstrip()
        elif re.match(r'\s*fun ret hret\b', body):
            tb = body.rstrip()
            trail = body[len(tb):]
            items[i] = sig + ':= by\n  ' + tac + '\n  exact (' + tb.lstrip() + ')' + trail
        # else: a term that applies another (migrated) theorem or helper: unchanged
    for i, it in enumerate(items):
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )*(?:theorem|lemma) ([\w.\']+)', it)
        if not m: continue
        ok_heads = {n.split('.')[-1] for n in reg.names} | {n.split('.')[-1] for n in ens}
        sg_, _bs_ = split_sig(it)
        if sg_ is not None:
            for mm in re.finditer(r"\((\w+) : ((?:[^()]|\([^()]*\))*)\)", sg_):
                ty = mm.group(2)
                if ENSDEF.match(ty) or (re.match(r'\s*(?:\w+\.)*(\w+)', ty) and re.match(r'\s*(?:\w+\.)*(\w+)', ty).group(1) in reg.ensdefs):
                    ok_heads.add(mm.group(1))
        it = fix_mono(it, warn, ok_heads)
        cc = conclusion(it)
        if cc and reg.generic and not is_generic(cc[1], cc[2], cc[3]):
            # a row that calls a generic helper (`Ensures.full64 hap … ens`): its `hinv` default has no definition list, so the
            # row's own list is passed
            ptac = 'janus64_pre_setRet' if isa[i] else 'janus_pre_setRet'
            dl = tac_with_defs(ptac, cc[1], cc[2], reg, fname, cc[3])
            if dl != ptac:
                gre = re.compile(r'(?<![\w.\'])((?:[\w]+\.)*(?:' + '|'.join(re.escape(n) for n in sorted(reg.generic, key=len, reverse=True)) + r'))(?![\w\'])(?!\s*\(hinv\s*:=)')
                se = split_sig(it)[1] or 0
                it = it[:se] + gre.sub(lambda mm: mm.group(1) + ' (hinv := by ' + dl + ')', it[se:])
        if cc and re.search(r'(?<![\w.\'])(?:\w+\.)*Ensures0?\.mono(?![\w\'])', it[split_sig(it)[1] or 0:]):
            ptac = 'janus64_pre_setRet' if isa[i] else 'janus_pre_setRet'
            dl = tac_with_defs(ptac, cc[1], cc[2], reg, fname, cc[3])
            if dl != ptac:
                it = re.sub(r'(?<![\w.\'])((?:\w+\.)*Ensures0?\.mono)(?![\w\'_])(?!\s*\(hinv\s*:=)', lambda mm: mm.group(1) + ' (hinv := by ' + dl + ')', it[split_sig(it)[1] or 0:]) if False else \
                    it[:split_sig(it)[1]] + re.sub(r'(?<![\w.\'])((?:\w+\.)*Ensures0?\.mono)(?![\w\'_])(?!\s*\(hinv\s*:=)', lambda mm: mm.group(1) + ' (hinv := by ' + dl + ')', it[split_sig(it)[1]:])
        it = add_hlen(it, isa[i], warn, m.group(1), reg)
        items[i] = it
    # ---- pass 2: old-shaped applications of Ensures-form theorems (and hypotheses) -> `(thm args).toOld ret hret …`
    appnames = set(reg.names) | set(ens)
    def hyp_names(it):
        """Hypotheses of the signature whose type is an Ensures form (`(h : ∀ H, Ensures …)`)."""
        sg = split_sig(it)[0]
        if sg is None: return set()
        ci = top_colon(sg)
        out = set()
        for mm in re.finditer(r"\((\w+) : ", sg[:ci] if ci >= 0 else sg):
            toks_, _ = tokens(sg, mm.end())
            ty = sg[mm.end():]
            # the type extends to the matching close paren
            d = 1; k = 0
            while k < len(ty) and d > 0:
                if ty[k] in OPEN: d += 1
                elif ty[k] in CLOSE: d -= 1
                k += 1
            if ENSDEF.match(ty[:k - 1]): out.add(mm.group(1))
        return out
    for i, it in enumerate(items):
        names_i = appnames | hyp_names(it)
        if not names_i: continue
        nre = '|'.join(re.escape(n) for n in sorted(names_i, key=len, reverse=True))
        are = re.compile(r'(?<![\w.\'])((?:[\w]+\.)*(?:' + nre + r'))(?![\w\'])')
        out = []
        pos = 0
        changed = False
        sigend = split_sig(it)[1] if split_sig(it)[0] is not None else 0
        while True:
            m = are.search(it, max(pos, sigend))
            if not m: break
            if re.match(r'\s*=>', it[m.end():]) or re.search(r'\|\s*$', it[max(0, m.start() - 12):m.start()]):
                out.append(it[pos:m.end()]); pos = m.end(); continue      # a match arm (`| zero => …`) that shares its name with a theorem, not an application
            toks, stop = tokens(it, m.end())
            idx = None
            for k in range(len(toks) - 1):
                if toks[k][0] in ('·', '<;>', 'at', 'with', 'from', 'by', 'then', 'else', '|'): break      # the application ended
                if toks[k][0] == 'ret' and toks[k + 1][0] == 'hret' and k + 2 < len(toks):     # old shape: ret hret s hs hp; a trailing ret hret is the migrated shape (idempotent)
                    idx = k; break
            if idx is None:
                # `(thm args).1 ret hret …` (a conjunction of rows, one projected): `(thm args).1.toOld ret hret …`
                mp = re.compile(r'\)((?:\.(?:\d+|left|right))+)(?=\s+ret\s+hret\b)').match(it, stop) if stop < len(it) and it[stop] == ')' else None
                if mp and all(t[0] not in ('·', '<;>', 'at', 'with', 'from', 'by', 'then', 'else', '|') for t in toks):
                    out.append(it[pos:mp.end()]); out.append('.toOld'); pos = mp.end(); changed = True; continue
                out.append(it[pos:m.end()]); pos = m.end(); continue
            argtoks = toks[:idx]
            argend = argtoks[-1][2] if argtoks else m.end()
            out.append(it[pos:m.start()])
            out.append('(' + it[m.start():argend] + ').toOld')
            pos = argend
            changed = True
        if changed:
            out.append(it[pos:])
            items[i] = ''.join(out)
    # arm64 theorems with a generic `args` that now apply `.toOld` need `[ArgsFit args]` as well
    for i, it in enumerate(items):
        if isa[i]: continue
        sg, bs = split_sig(it)
        if sg is None or 'ArgsFit' in sg or not re.search(r'\{args\s*:\s*List', sg) or '.toOld' not in it[bs:]: continue
        mm = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )*(?:theorem|lemma) ', it)
        if not mm: continue
        ci = top_colon(sg)
        items[i] = sg[:ci].rstrip() + ' [ArgsFit args] ' + sg[ci:] + ':=' + it[bs:]
    # ---- pass 3: witnesses
    def app_re(names):
        if not names: return None
        return re.compile(r'(?<![\w.\'])((?:[\w]+\.)*(?:' + '|'.join(re.escape(n) for n in sorted(names, key=len, reverse=True)) + r'))(?![\w\'])')
    plain = {n for n, k in ens.items() if not k} | {n for n in reg.names}
    kern = {n for n, k in ens.items() if k}

    def find_apps(it):
        """Applications `thm args RET hret S SETUP PRE` (EnsuresK: `RET hret S K SETUP PRE`): (m, args_tokens, ret, s, k?, setup, pre, end)."""
        out = []
        for names, isk in ((plain, False), (kern, True)):
            r = app_re(names)
            if not r: continue
            for m in r.finditer(it):
                if re.match(r'\s*=>', it[m.end():]) or re.search(r'\|\s*$', it[max(0, m.start() - 12):m.start()]): continue      # a match arm sharing a theorem's name
                toks, stop = tokens(it, m.end())
                for k in range(len(toks) - 3):
                    if (re.fullmatch(r"hret[\w']*", toks[k + 1][0].split('.')[-1]) or (toks[k][0] == 'ret' and re.fullmatch(r"\?\w+", toks[k + 1][0]))) and re.fullmatch(r"[\w'.]+", toks[k][0]):
                        need = 5 if isk else 4          # ret hret s [k] setup  (+ pre follows)
                        if k + need <= len(toks):
                            out.append((m, toks, k, isk))
                        break
        return out
    used_setups = set(reg.setupused)
    raw_setups, both_used = set(), set()      # setup lemmas applied by raw old-shaped theorems; and by rows too: the old lemma stays, `NAME_at0` is the new-shaped twin
    # a setup lemma applied only by the raw old-shaped theorems of this file (`local_non`) keeps its v0.3 form
    if reg.local_non:
        raw_used, row_used = set(), set()
        for itx in items:
            for nmx in reg.local_non:
                for mx in re.finditer(r'(?<![\w\'])(?:[\w]+\.)*' + re.escape(nmx) + r'(?![\w\'])', itx):
                    tk, _ = tokens(itx, mx.end())
                    for kx in range(len(tk) - 3):
                        if re.fullmatch(r"hret[\w']*", tk[kx + 1][0].split('.')[-1]) and kx + 3 < len(tk):
                            raw_used.add(tk[kx + 3][0].split('.')[-1]); break
        raw_setups = set(raw_used) & reg.setupnames      # genuine `theorem NAME : CallSetup (P.withExit R) …` lemmas only
        used_setups -= raw_used
    extra = {}
    for i, it in enumerate(items):
        mm0 = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )*(?:theorem|lemma) ([\w.\']+)', it)
        if mm0 and (mm0.group(1) not in ens or inw[i]) and re.search(r'\.toOld\s+ret\s+hret', it):
            it2, st2 = untoold(it, reg.setupnames)
            if st2:
                items[i] = it2; extra[i] = st2
                for sx in st2:
                    if sx.startswith('__setup__'): used_setups.add(sx[9:])
    for it in items:
        for m, toks, k, isk in find_apps(it):
            sidx = k + (4 if isk else 3)
            if sidx < len(toks):
                used_setups.add(toks[sidx][0])
                if toks[sidx][0].split('.')[-1] in raw_setups: both_used.add(toks[sidx][0].split('.')[-1])
    both_used |= {n.split('.')[-1] for n in used_setups if n.split('.')[-1] in raw_setups}
    restated = set()
    for i, it in enumerate(items):
        amd = isa[i]
        m = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )*(?:theorem|lemma) ([\w.\']+)', it)
        if not m: continue
        name = m.group(1)
        if SETUP_RE.search(it) and any(re.search(r'theorem\s+' + re.escape(name) + r'_at0\b', x) for x in items): continue     # its twin exists already (idempotent)
        if name.split('.')[-1] in both_used and name in used_setups and SETUP_RE.search(it):
            # the old setup lemma stays (raw theorems apply it); the new-shaped twin `NAME_at0` is what the rows and witnesses use
            twin = re.sub(r'(theorem\s+)' + re.escape(name) + r'\b', lambda mm: mm.group(1) + name + '_at0', it, count=1)
            twin = fix_setup_body(fix_setups(twin), amd, warn, name + '_at0')
            items[i] = it + '\n' + twin
            continue
        if name in used_setups and SETUP_RE.search(it):
            it = fix_setups(it)
            it = fix_setup_body(it, amd, warn, name)
            if re.search(r'\b(?:CallSetup0?|CCallA?)\b\s*\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\.withExit', it): warn.append('setup %s not rewritten' % name)
            items[i] = it
            continue
        if inw[i] and name not in ens and not find_apps(it) and not conclusion(it):
            it2 = fix_reexported_run(it, restated)
            if it2 != it: items[i] = it2; restated.add(name.split('.')[-1]); continue
        apps = find_apps(it)
        sig0 = it.split(':=', 1)[0]
        exw = '∃' in sig0 and SETUP_RE.search(it) is not None
        if exw and inw[i] and not apps and restated and any(re.search(r"(?<![\w.'])" + re.escape(r) + r"(?![\w'])", it[len(sig0):]) for r in restated): name_force = True
        else: name_force = False
        if (apps or extra.get(i) or (exw and inw[i] and (name in FORCE or name_force or (ens and not RAW)))) and (name not in ens or inw[i]) and not conclusion(it) is not None:
            it = rewrite_witness(it, apps, amd, name, warn, plain, kern, extra.get(i, ()))
            for bn in both_used:      # the rewritten witness applies the new-shaped twin of a setup lemma the raw theorems still apply
                bsx = split_sig(it)[1]
                if bsx is not None and not name == bn:
                    it = it[:bsx] + re.sub(r"(?<![\w.'])" + re.escape(bn) + r"(?![\w'])", bn + '_at0', it[bsx:])
            items[i] = it
            if '.setRet' in it.split(':=', 1)[0]: restated.add(name.split('.')[-1])
    return ''.join(items), warn

def fix_reexported_run(it, restated=()):
    """A claim file restates a witness run in its `Witness` namespace and proves it by the proof module's theorem of the same name:
    `theorem returns : Returns (P.withExit Wit.ret) Wit.s0 fun s' => ABIReturn Wit.s0 s' ∧ … := Wit.returns`. The proof module's
    theorem is now stated at `Wit.s0.setRet Wit.ret` (see `rewrite_witness`), so the restatement follows: every `Wit.s0` after the
    `withExit` becomes `(Wit.s0.setRet Wit.ret)`. Only a bare identifier body (a re-export) is rewritten."""
    sg, bs = split_sig(it)
    if sg is None: return it
    mb = re.match(r"\s*\(?([\w']+)(?:\.[\w.']+)?", it[bs:])      # a bare name, or `NAME.mono …` / `NAME.…` of a witness claim restated at the setRet state already
    if not (re.fullmatch(r"\s*[\w.']+\s*", it[bs:]) or (mb and mb.group(1) in restated)): return it
    if SETUP_RE.search(sg): return it      # a statement with a call setup is rewritten as a whole by `rewrite_witness`
    m = re.search(r'(?:Returns\w*|RunsAtLeast \d+|ReturnsWithin \d+) \((?:[^()]|\([^()]*\))*\.withExit ([\w.\']+)\) ([\w.\']+)(?=[\s])', sg)
    if not m or 'setRet' in m.group(2) or m.group(2).startswith('(') : return it
    R, S = m.group(1), m.group(2)
    tail = re.sub(r"(?<![\w.'])" + re.escape(S) + r"(?![\w'])", '(' + S + '.setRet ' + R + ')', sg[m.end(2):])
    return sg[:m.start(2)] + '(' + S + '.setRet ' + R + ')' + tail + it[len(sg):]

def fix_setup_body(it, amd, warn, name):
    """Drop/replace the return-address field of the anonymous constructor that proves a `CallSetup`."""
    sig, bs = split_sig(it)
    if sig is None: return it
    body = it[bs:]
    k = body.find('⟨')
    if k < 0 or not re.fullmatch(r'\s*(?:by\s*(?:refine|exact)?)?\s*', body[:k]):
        if 'CallSetup0' in sig or 'CallSetupF' in sig:
            warn.append('setup %s: not an anonymous constructor; adjust the return-address field by hand' % name)
        return it
    # matching close
    d = 0
    j = k
    while j < len(body):
        if body[j] == '⟨': d += 1
        elif body[j] == '⟩':
            d -= 1
            if d == 0: break
        j += 1
    inner = body[k + 1:j]
    parts = split_top(inner)
    if len(parts) < 3: return it
    abi0 = 'CallSetupF' in sig
    if amd:
        # CallSetup (rip, ret, zero, len, args, df) / ABI0 CallSetup0 (rip, ret, argWords, frame, df): drop `ret`
        parts = [parts[0]] + parts[2:]
    elif abi0:
        parts = [parts[0]] + parts[2:]        # (pc, lr, argWords, frame, spAligned) -> (pc, argWords, frame, spAligned)
    else:
        parts = [parts[0], ' by first | decide | simp | omega'] + parts[2:]   # (pc, lr, args) -> (pc, len, args)
    return it[:bs] + body[:k + 1] + ','.join(parts) + body[j:]

def untoold(it, setups):
    """`(thm args).toOld ret hret S SETUP PRE` (the row-proof rewrite applied to a witness application) -> `(thm args) S SETUP PRE ret hret`
    when SETUP is a known `CallSetup (P.withExit R)` lemma. Returns (text, states)."""
    states = set()
    pos = 0
    while True:
        m = re.compile(r'\)((?:\.(?:\d+|left|right))*)\.toOld\s+ret\s+hret\s+').search(it, pos)
        if not m: break
        toks, stop = tokens(it, m.end())
        si = 1
        sname = re.match(r'\(?([\w.\']+)', toks[1][0]) if len(toks) >= 2 else None
        if (sname is None or sname.group(1).split('.')[-1] not in setups) and len(toks) >= 3:
            si = 2          # EnsuresK: `S K SETUP PRE`
            sname = re.match(r'\(?([\w.\']+)', toks[2][0])
        if sname is None or sname.group(1).split('.')[-1] not in setups:
            pos = m.end(); continue
        last = si + 2 if len(toks) >= si + 2 else si + 1
        states.add(toks[0][0]); states.add('__raw__')
        states.add('__setup__' + sname.group(1).split('.')[-1])
        new = ')' + m.group(1) + ' ' + it[toks[0][1]:toks[last - 1][2]] + ' ret hret'
        it = it[:m.start()] + new + it[toks[last - 1][2]:]
        pos = m.start() + len(new)
    return it, states

def rewrite_witness(it, apps, amd, name, warn, plain, kern, extra=()):
    it = fix_setups(it)
    sig_end = split_sig(it)[1] if split_sig(it)[0] is not None else len(it)
    stmt = it[:sig_end]
    # states set up by the statement, and the return-address variable
    states = {'s'} | set(extra)
    for mm in re.finditer(r"(?:CallSetup0|CallSetupF|CCallF|CCallAF)\b(?:[^∧:=]|\n|=(?!>)|:(?!=))*?\s(\w+'?)(?=\s*(?:∧|$|:=))", stmt, re.M):
        states.add(mm.group(1))
    for m, toks, k, isk in apps:
        sidx = k + 2
        if sidx < len(toks): states.add(toks[sidx][0])
    states.discard('_')
    hm = re.search(r'RetAddr\s+', stmt)
    retv = None
    if hm:
        tk, _ = tokens(stmt, hm.end())
        if len(tk) >= 2 and re.fullmatch(r"[\w']+", tk[1][0]): retv = tk[1][0]
    if retv is None and apps:
        m, toks, k, isk = apps[0]
        retv = toks[k][0]
    if retv is None: retv = 'ret'
    # every run claim `Returns (P.withExit R) S …` (the conjunct only: up to the `∧` / closing paren that ends it, or the end of the
    # statement when its `fun` is not parenthesised): the free states become `(S.setRet R)`
    RUNRE = re.compile(r'(Returns\w*|Panics|GrownReturns\w*|RunsAtLeast \d+|ReturnsWithin \d+) \((?:[^()]|\([^()]*\)|\((?:[^()]|\([^()]*\))*\))*?\.withExit \w+\)')
    def conj_end(t, i):
        d = 0; bare_fun = False; n = len(t)
        while i < n:
            c = t[i]
            if c == '-' and t[i:i + 2] == '--':
                j = t.find('\n', i); i = n if j < 0 else j; continue
            if c in OPEN: d += 1
            elif c in CLOSE:
                d -= 1
                if d < 0: return i
            elif d == 0:
                if t.startswith(':=', i): return i
                if t.startswith('fun ', i) or t.startswith('fun\n', i): bare_fun = True
                if c == '∧' and not bare_fun: return i
            i += 1
        return n
    pos = 0
    while True:
        m = RUNRE.search(it, pos)
        if not m: break
        end = conj_end(it, m.end())
        seg = it[m.start():end]
        if 'setRet' in m.group(0) or '.setRet' in seg.split('\n')[0]:
            pos = end; continue
        head = m.group(0)
        tail = it[m.end():end]
        tk0, _ = tokens(tail, 0)
        extra_st = []
        if (it[max(0, m.start() - 2):m.start()] == 'Go' or m.group(1) == 'ReturnsC') and len(tk0) >= 2: tk0 = tk0[1:]      # `GoReturns P C S …` / `ReturnsC P C post S`: the class / contract comes first
        if tk0 and tk0[0][0].startswith('(') and '.setRet' not in tk0[0][0] and tk0[0][0] not in ('(fun', ) and not tk0[0][0].startswith('(fun'):
            extra_st = [tk0[0][0]]       # a state given by an expression (`(s0 mem0)`), not a variable
        for st in extra_st:
            tail = re.sub(r'(?<![\w.\'])' + re.escape(st) + r'(?![\w\'])', '(' + st + '.setRet ' + retv + ')', tail)
        for st in states:
            tail = re.sub(r'(?<![\w.\'])' + re.escape(st) + r'(?![\w\'])', '(' + st + '.setRet ' + retv + ')', tail)
        it = it[:m.end()] + tail + it[end:]
        pos = m.end() + len(tail)
    # a lambda `(fun (S.setRet R) s' => body)` applied to the state: the binder stays `S`, the body reads the binder
    for st in states:
        key = '(fun (' + st + '.setRet ' + retv + ')'
        pos = 0
        while True:
            q = it.find(key, pos)
            if q < 0: break
            d, j = 0, q
            while j < len(it):
                if it[j] == '(': d += 1
                elif it[j] == ')':
                    d -= 1
                    if d == 0: break
                j += 1
            seg = it[q:j + 1].replace('(' + st + '.setRet ' + retv + ')', st)
            it = it[:q] + seg + it[j + 1:]
            pos = q + len(seg)
    # applications: `thm args RET hret S SETUP PRE` -> `thm args S SETUP PRE RET hret`
    sig_end = split_sig(it)[1] if split_sig(it)[0] is not None else 0
    for names, isk in ((plain, False), (kern, True)):
        r = re.compile(r'(?<![\w.\'])((?:[\w]+\.)*(?:' + '|'.join(re.escape(n) for n in sorted(names, key=len, reverse=True)) + r'))(?![\w\'])') if names else None
        if not r: continue
        pos = sig_end
        while True:
            m = r.search(it, pos)
            if not m: break
            toks, stop = tokens(it, m.end())
            kk = None
            for q in range(len(toks) - 1):
                if (re.fullmatch(r"hret[\w']*", toks[q + 1][0].split('.')[-1]) or (toks[q][0] == 'ret' and re.fullmatch(r"\?\w+", toks[q + 1][0]))) and re.fullmatch(r"[\w'.]+", toks[q][0]):
                    kk = q; break
            need = 5 if isk else 4
            if kk is None or kk + need > len(toks):
                pos = m.end(); continue
            ret_t, hret_t = toks[kk], toks[kk + 1]
            lastidx = kk + (4 if isk else 3)      # the setup token; the precondition proof follows
            if lastidx + 1 < len(toks):
                lastidx += 1                       # include the precondition proof
            rest_start = hret_t[2]
            rest_end = toks[lastidx][2]
            moved = it[ret_t[1]:hret_t[2]]
            new = it[rest_start:rest_end].lstrip() + ' ' + moved
            # keep line structure: put the moved pair on the same line as the end
            it = it[:ret_t[1]] + new + it[rest_end:]
            pos = ret_t[1] + len(new)
    # `hr.mono fun s' hq => ⟨hq.1, (post_iff … s s').1 hq.2⟩`: the lambda's body speaks about the run that now starts at `S.setRet R`, so the
    # lemma instances that took `s s'` take `(s.setRet ret) s'`
    mm = re.search(r'\.mono\s+\(?fun\s', it[sig_end:])
    if mm:
        k0 = sig_end + mm.start()
        head_, tail_ = it[:k0], it[k0:]
        for st in sorted(states):
            if st.startswith('__') or not re.fullmatch(r"[\w']+", st): continue
            tail_ = re.sub(r"(?<![\w.'])" + re.escape(st) + r"(?= s'(?![\w']))", '(' + st + '.setRet ' + retv + ')', tail_)
        it = head_ + tail_
    return it

ALT3 = re.compile(r"(?m)^([ \t]*)\| \(refine ⟨((?:by decide \+kernel|\?_)), ((?:by decide \+kernel|\?_)), ((?:by decide \+kernel|\?_))⟩;(?:[^()]|\((?:[^()]|\([^()]*\))*\))*?\)$")

def fix_stackguard_alts(t):
    """`first | … | (refine ⟨k, ?_, k⟩; rw [..]; decide +kernel) | …` proving a `pre` that contains a StackGuardOK: the guard
    has a 4th field (`apart`), so every 3-hole alternative gets a 4-hole twin (the extra hole a kernel `decide`)."""
    out, pos, n = [], 0, 0
    for m in ALT3.finditer(t):
        alt = m.group(0)
        if '+kernel⟩' in alt.split(';')[0] and alt.split(';')[0].count(',') >= 3: continue
        twin = alt.replace('⟩;', ', by decide +kernel⟩;', 1)
        if twin in t: continue
        out.append(t[pos:m.end()]); out.append('\n' + twin); pos = m.end(); n += 1
    out.append(t[pos:])
    return ''.join(out), n

def fix_stackguard(t):
    """amd64 `StackGuardOK` has a 4th field (`apart`: the guard word is not the return slot): the destructuring
    the nested pattern `⟨hg1, hg2, hg3⟩` (the customary names of its three fields) becomes `⟨hg1, hg2, hg3, hg4⟩`. Constructions
    `⟨…, hg1, hg2, hg3, …⟩` of another state still need their own proof of `hg4` (reported)."""
    parts = re.split(r'(?m)^(?=(?:theorem |lemma |def |abbrev |namespace |end |set_option |/--|@\[|private |protected ))', t)
    # `RtContract64` / `GuardOK64` (the runtime contracts' own three-field guard) is not the StackGuardOK
    return ''.join(p_ if re.search(r'RtContract64|GuardOK64', p_) else _fix_stackguard_item(p_) for p_ in parts)

def _fix_stackguard_item(t):
    t = re.sub(r'⟨hg1, hg2, hg3⟩', '⟨hg1, hg2, hg3, hg4⟩', t)
    # any other three binders followed by the region triple `⟨hb', …⟩` (the `CallEnv` shape: StackGuardOK, then the region)
    def ext(m):
        if m.group(2) == 'hnw' or m.group(3) == 'hacc':      # `⟨hle, hnw, hacc⟩`: a StackWritable (three fields), not a StackGuardOK
            return m.group(0)
        return '⟨%s, %s, %s, %s⟩%s' % (m.group(1), m.group(2), m.group(3), '-' if m.group(3) == '-' else '_', m.group(4))
    return re.sub(r"⟨([\w'-]+), ([\w'-]+), ([\w'-]+)⟩(, ⟨hb)", ext, t)

SG_CLOSER = "first | omega | (simp_all only [stackguard0Offset, regG, regSP, Apart]; omega)"

SG_INLINE = "by first | (simp only [stackguard0Offset, regG, regSP] at *; omega) | omega | decide +kernel | (simp_all only [stackguard0Offset, regG, regSP, Apart]; omega)"

def fix_stackguard_terms(t):
    """Constructions of a StackGuardOK as an anonymous constructor with three components (the 4th field `apart` is new):
    `⟨g1, g2, g3⟩` (hypotheses destructured earlier) gets a 4th component proved from the context; a triple of `by decide` /
    `by decide +kernel` proofs is tried with a 4th `by decide` first and falls back to the 3-field structures it may also build (TlsG)."""
    n = 0
    out = []
    pat_intro = re.compile(r'\b(?:rintro|obtain|rcases|intro|fun|match|cases)\b')
    for ln in t.split('\n'):
        if '⟨g1, g2, g3⟩' in ln and not pat_intro.search(ln):
            ln = ln.replace('⟨g1, g2, g3⟩', '⟨g1, g2, g3, (%s)⟩' % SG_INLINE)
            n += 1
        out.append(ln)
    t = '\n'.join(out)
    comp = r"by decide(?: \+kernel)?|by unfold stackguard0 stackguard0Offset regG regSP; decide"
    rx = re.compile(r'(?<![\w])⟨(' + comp + r'), (' + comp + r'), (' + comp + r')⟩')
    def tri(m):
        a, b, c = m.group(1), m.group(2), m.group(3)
        if t[:m.start()].endswith('exact ⟨%s, %s, %s, by decide⟩ | exact ' % (a, b, c)): return m.group(0)      # the 3-field fallback of an earlier run (idempotent)
        return '(by first | exact ⟨%s, %s, %s, by decide⟩ | exact ⟨%s, %s, %s⟩)' % (a, b, c, a, b, c)
    t2, k = rx.subn(tri, t)
    return t2, n + k

def fix_stackguard_construct(t):
    """`refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, …⟩` (an environment transfer lemma: a `CallEnv` whose first component is a
    `StackGuardOK`): a 4th hole for the guard word's apartness from `[RSP, RSP + 8)`, and a bullet after the third one."""
    lines = t.split('\n')
    out = []
    i = 0
    changed = 0
    pat = re.compile(r'^(\s*)refine ⟨((?:⟨)?)⟨\?_, \?_, \?_⟩, (⟨\?_, \?_, \?_⟩|⟨by omega, by omega, by omega, \?_, hx15, hdf, hra⟩|⟨\?_, \?_, \?_, \?_, hx\w*, hdf, hra⟩)')
    while i < len(lines):
        ln = lines[i]
        m = pat.match(ln)
        if not m:
            out.append(ln); i += 1; continue
        ind = m.group(1)
        out.append(ln.replace('⟨?_, ?_, ?_⟩', '⟨?_, ?_, ?_, ?_⟩', 1))
        i += 1
        nb = 0
        bullet = re.compile('^' + re.escape(ind) + '· ')
        done = False
        while i < len(lines):
            l2 = lines[i]
            if bullet.match(l2):
                if nb == 3 and not done:
                    out.append(ind + '· ' + SG_CLOSER)
                    done = True
                nb += 1
            elif l2.strip() and not l2.startswith(ind + ' ') and not bullet.match(l2) and nb >= 3:
                pass
            out.append(l2); i += 1
            if done and nb > 4: break
            if nb > 3 and done: 
                # keep copying the remaining lines normally
                break
        if not done and nb == 3:
            out.append(ind + '· ' + SG_CLOSER)
        changed += 1
    return '\n'.join(out), changed

def main(files):
    files = sorted(dict.fromkeys(files))      # a defined processing and registry order (the output never depends on the argument order)
    reg = Reg()
    texts = {}
    for f in files:
        t = open(f).read()
        texts[f] = t
        collect(t, reg)
        collect_defs(t, f, reg)
        collect_ensdefs(t, reg)
        reg.imports[f] = re.findall(r'(?m)^import\s+([\w.]+)', t)
        mns = re.search(r'(?m)^namespace\s+([\w.]+)', t)
        reg.fns[f] = mns.group(1) if mns else ''
        reg.isa_amd[f] = 'Janus.Amd64' in t
        reg.opens[f] = [w for ol in re.findall(r'(?m)^open ([^\n]*(?:\n[ \t]+[\w.][^\n]*)*)', t) for w in ol.split() if re.fullmatch(r'[\w.]+', w)]
        reg.modfile[modname(f)] = f
        reg.modfile[f.replace('/', '.')[:-5]] = f
    # the framework's own predicates (`CallerOK`, `IsMap`, …) are unfolded by `janus_pre_setRet` too: collect the definitions of the
    # Janus library next to this script (definitions and import graph only; nothing there is rewritten)
    libroot = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), 'Janus')
    if os.path.isdir(libroot) and not os.environ.get('JANUS_MIG_NOLIB'):
        for dp, _dn, fns in os.walk(libroot):
            for fn in fns:
                if not fn.endswith('.lean'): continue
                lf = os.path.join(dp, fn)
                lt = open(lf).read()
                rel = os.path.relpath(lf, os.path.dirname(libroot))
                collect_defs(lt, rel, reg)
                reg.imports[rel] = re.findall(r'(?m)^import\s+([\w.]+)', lt)
                reg.modfile[rel.replace('/', '.')[:-5]] = rel
    # theorems whose conclusion is a spec definition that unfolds to an Ensures form (`case_dzp : CaseDZP`): row theorems too
    for f in files:
        for it0 in re.split(r'(?m)^(?=(?:theorem |lemma |@\[|private |protected ))', texts[f]):
            m0 = re.match(r'(?:@\[[^\]]*\]\s*)?(?:private |protected )*(?:theorem|lemma) ([\w.\']+)', it0)
            if not m0 or conclusion(it0) or m0.group(1) in TACTIC_WORDS: continue
            sg0, _b0 = split_sig(it0)
            ci0 = top_colon(sg0) if sg0 is not None else -1
            mh = re.match(r'\s*(?:\w+\.)*(\w+)', sg0[ci0 + 1:]) if ci0 >= 0 else None
            if mh and mh.group(1) in reg.ensdefs: reg.names.add(m0.group(1))
    for f in files:
        for mm in re.finditer(r"\bret\s+hret\s+[\w'.]+\s+\(?([\w.']+)", texts[f]):
            if mm.group(1).split('.')[-1] in reg.setupnames: reg.setupused.add(mm.group(1).split('.')[-1])
    changed = True
    while changed:                    # theorems with a generic `args` that call `Ensures.toSummaryIn` or such a theorem
        changed = False
        for nm, body in reg.argthms:
            if nm not in reg.argsfit and ('Ensures.toSummaryIn' in body or any(re.search(r'(?<![\w.\'])' + re.escape(x) + r'(?![\w\'])', body) for x in reg.argsfit)):
                reg.argsfit.add(nm); changed = True
    for nm, f, body, qn in reg.aliases:       # `def Pre := PreS 4440`
        m0 = re.match(r"\s*([A-Za-z_][\w']*)", body)
        if m0 and m0.group(1).split('.')[-1] in reg.defs:
            reg.defs.setdefault(nm, []).append((f, body, qn))
    for f in files:
        t = texts[f]
        amd = 'Janus.Amd64' in t
        t2, warn = migrate(t, amd, reg, f)
        if amd and ('⟨hg1, hg2, hg3⟩' in t2 or re.search(r"⟨[\w'-]+, [\w'-]+, [\w'-]+⟩, ⟨hb", t2)):
            t3 = fix_stackguard(t2)
            if t3 != t2: warn.append('StackGuardOK patterns `hg1, hg2, hg3` extended by `hg4` (a construction of another state needs its own proof of the guard word apart from [RSP, RSP+8))')
            t2 = t3
        if amd and 'refine ⟨' in t2:
            t4, nchg = fix_stackguard_construct(t2)
            if nchg:
                warn.append('%d `refine ⟨⟨?_, ?_, ?_⟩, …⟩` StackGuardOK constructions got a 4th hole and a closing bullet' % nchg)
                t2 = t4
        if amd and '(refine ⟨by decide +kernel' in t2 or amd and '(refine ⟨?_, by decide +kernel' in t2:
            t5, nalt = fix_stackguard_alts(t2)
            if nalt:
                warn.append('%d `refine ⟨k, ?_, k⟩` alternatives got a 4-hole twin (StackGuardOK 4th field)' % nalt)
                t2 = t5
        if amd:
            t8, n8 = fix_stackguard_terms(t2)
            if n8:
                warn.append('%d StackGuardOK constructions (`⟨g1, g2, g3⟩`, `⟨by decide, …⟩` triples) got a 4th component proving the guard word apart from [RSP, RSP+8)' % n8)
                t2 = t8
        if amd and '⟨?_, ?_, ?_⟩ <;>' in t2:
            # `first | decide | (refine ⟨?_, ?_, ?_⟩ <;> TAIL) | …` proving a precondition with a StackGuardOK (4 fields now): a 4-hole twin first
            t6, n6 = re.subn(r'(\| )\(refine ⟨\?_, \?_, \?_⟩ <;> ((?:[^()\n]|\((?:[^()\n]|\([^()\n]*\))*\))*)\)',
                             lambda m: m.group(0) if t2[:m.start()].endswith('(refine ⟨?_, ?_, ?_, ?_⟩ <;> ' + m.group(2) + ') ') else
                             m.group(1) + '(refine ⟨?_, ?_, ?_, ?_⟩ <;> ' + m.group(2) + ') | (refine ⟨?_, ?_, ?_⟩ <;> ' + m.group(2) + ')', t2)
            if n6: n6 = sum(1 for _ in re.finditer(r'\(refine ⟨\?_, \?_, \?_, \?_⟩ <;>', t6)) - sum(1 for _ in re.finditer(r'\(refine ⟨\?_, \?_, \?_, \?_⟩ <;>', t2))
            if n6:
                warn.append('%d `refine ⟨?_, ?_, ?_⟩ <;> …` alternatives got a 4-hole twin (StackGuardOK 4th field)' % n6)
                t2 = t6
        if t2 != t: open(f, 'w').write(t2)
        print(f, ('WARN: ' + '; '.join(warn)) if warn else 'ok')

def check_idempotent(files):
    """`migrate-v040.py --check-idempotent FILE...`: copy the files to a temporary tree, migrate it twice, and fail when the second run
    changes any file (a migrated tree must be a fixed point of the script). The originals are never written."""
    import tempfile, shutil, io, contextlib
    tmp = tempfile.mkdtemp(prefix='mig-idem-')
    try:
        cp = []
        for f in sorted(dict.fromkeys(files)):
            rel = os.path.relpath(os.path.abspath(f), os.path.commonpath([os.path.abspath(x) for x in files]) if len(files) > 1 else os.path.dirname(os.path.abspath(f)))
            i = os.path.abspath(f).rfind('/lean/')
            rel = os.path.abspath(f)[i + 1:] if i >= 0 else rel
            dst = os.path.join(tmp, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(f, dst); cp.append(dst)
        snap = lambda: {c: open(c).read() for c in cp}
        with contextlib.redirect_stdout(io.StringIO()): main(cp)
        s1 = snap()
        with contextlib.redirect_stdout(io.StringIO()): main(cp)
        s2 = snap()
        bad = [c for c in cp if s1[c] != s2[c]]
        print('first run changed %d of %d files; second run changed %d' % (sum(1 for f, c in zip(sorted(dict.fromkeys(files)), cp) if open(f).read() != s1[c]), len(cp), len(bad)))
        for c in bad[:20]: print('NOT IDEMPOTENT:', os.path.relpath(c, tmp))
        return 1 if bad else 0
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--check-idempotent': sys.exit(check_idempotent(sys.argv[2:]))
    main(sys.argv[1:])
