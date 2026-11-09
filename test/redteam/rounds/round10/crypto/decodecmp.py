# Compare the Lean decoder (janus-decode) with the sail-arm v9.4 decode clauses on the
# crypto/CRC32/permute/AES/TBL/EXT/scalar-DUP families. Usage:
#   python3 -I decodecmp.py CLAUSES.json JANUS_DECODE OUTDIR
import json, re, sys, subprocess, itertools
from collections import Counter, defaultdict
clauses = json.load(open(sys.argv[1])); dec = sys.argv[2]; out = sys.argv[3]
FAM = re.compile(r'crypto|crc32|_tbl_|_tbx_|_ext_advsimd|_zip[12]_|_uzp[12]_|_trn[12]_|dup_advsimd_elt_.*sisd|pmull')
def b(w, hi, lo): return (w >> lo) & ((1 << (hi - lo + 1)) - 1)
def asl(w):
    for c in clauses:
        if w & c['mask'] == c['val']:
            return c['fn']
    return None
def asl_undef(fn, w):
    """UNDEFINED per the decode function, all FEAT_* implemented except we tag SM3/SM4."""
    if fn is None: return True
    if 'crc32' in fn:
        sf, sz = b(w,31,31), b(w,11,10)
        return (sf == 1 and sz != 3) or (sf == 0 and sz == 3)
    if 'dup_advsimd_elt' in fn and 'sisd' in fn:
        imm5 = b(w,20,16); return imm5 & 0xF == 0
    if 'permute' in fn:
        return (b(w,23,22) << 1 | b(w,30,30)) == 0b110
    if 'pmull' in fn:
        return b(w,23,22) in (1, 2)
    if '_ext_advsimd' in fn:
        return b(w,30,30) == 0 and b(w,14,14) == 1
    return False
def short(fn):
    return fn.replace('decode_', '').split('_advsimd')[0].split('_aarch64')[0] if fn else None
def lean_name(line):
    m = re.match(r'(0x[0-9a-f]+) (ok|none)\s*(.*)', line)
    w = int(m.group(1), 16)
    if m.group(2) == 'none': return w, None, None
    r = m.group(3)
    toks = r.replace('(', ' ').replace(')', ' ').split()
    head = toks[0].split('.')[-1]
    if head == 'crypto':
        ctor = toks[1].split('.')[-1]; args = toks[2:]
        A = lambda i: int(args[i]) if args[i].isdigit() else args[i]
        if ctor == 'sha3Reg': n = ['sha1c','sha1p','sha1m','sha1su0','sha256h','sha256h2','sha256su1','?'][A(0)]
        elif ctor == 'sha2Reg': n = ['sha1h','sha1su1','sha256su0'][A(0)] if A(0) < 3 else '?'
        elif ctor == 'sha512Reg': n = ['sha512h','sha512h2','sha512su1','rax1'][A(0)]
        elif ctor == 'sha512Su0': n = 'sha512su0'
        elif ctor == 'sha4Reg': n = ['eor3','bcax','?','?'][A(0)]
        elif ctor == 'xar': n = 'xar'
        elif ctor == 'pmull': n = 'pmull'
        elif ctor == 'crc32': n = 'crc32c' if args[2] == 'true' else 'crc32'
        elif ctor == 'permute': n = {1:'uzp1',2:'trn1',3:'zip1',5:'uzp2',6:'trn2',7:'zip2'}.get(A(3), '?')
        elif ctor == 'dupScalar': n = 'dup'
        else: n = '?' + ctor
        return w, n, r
    if head == 'vAes': return w, {4:'aese',5:'aesd',6:'aesmc',7:'aesimc'}.get(int(toks[1]), '?aes'), r
    if head == 'vTbl': return w, 'tbx' if toks[4] == 'true' else 'tbl', r
    if head == 'vExt': return w, 'ext', r
    return w, 'other:' + head, r
FAMNAMES = set('sha1c sha1p sha1m sha1su0 sha256h sha256h2 sha256su1 sha1h sha1su1 sha256su0 sha512h sha512h2 sha512su1 rax1 sha512su0 eor3 bcax xar pmull crc32 crc32c uzp1 trn1 zip1 uzp2 trn2 zip2 dup aese aesd aesmc aesimc tbl tbx ext'.split())
def words():
    # SIMD&FP DP (bits 27:25 = 111) and DP register (bits 27:25 = 101), bits 28,31:29,24:10 free;
    # (Rd, Rn) in {(1,2), (31,0)}.
    for g in (0b111, 0b101):
        for rdn in ((1, 2), (31, 0)):
            for hi in range(16):          # bits 31:28
                for mid in range(1 << 15):  # bits 24:10
                    yield hi << 28 | g << 25 | mid << 10 | rdn[1] << 5 | rdn[0]
ws = list(words())
import numpy as np
W = np.array(ws, dtype=np.uint64); FN = np.full(len(ws), -1, dtype=np.int64)
for i, c in enumerate(clauses):
    m = (FN < 0) & ((W & np.uint64(c['mask'])) == np.uint64(c['val']))
    FN[m] = i
ASL = {w: (clauses[int(i)]['fn'] if i >= 0 else None) for w, i in zip(ws, FN.tolist())}
p = subprocess.run([dec], input='\n'.join(hex(w) for w in ws) + '\n', capture_output=True, text=True)
lines = p.stdout.splitlines(); assert len(lines) == len(ws), (len(lines), len(ws))
stats = Counter(); bad = defaultdict(list); gap = Counter(); gapex = {}
for line in lines:
    w, ln, rep = lean_name(line)
    fn = ASL[w]; an = short(fn); und = asl_undef(fn, w)
    infam_asl = fn is not None and FAM.search(fn) is not None
    infam_lean = ln is not None and not ln.startswith('other:')
    if fn is None and ln is not None: stats['side-info: lean accepts, asl no clause: ' + ln] += 1
    if not (infam_asl or infam_lean): continue
    if an == 'dup' and 'sisd' not in fn: an = 'dup_vec'
    if infam_lean:
        if und or an != ln:
            bad[(ln, an, 'UNDEF' if und and fn else '')].append((w, rep))
        else:
            stats[ln] += 1
    elif ln is not None:
        bad[(ln, an, 'lean-other-ctor' + (':UNDEF' if und else ''))].append((w, rep))
    else:
        if not und and an not in ('sm3partw1','sm3partw2','sm3ss1','sm3tt1a','sm3tt1b','sm3tt2a','sm3tt2b','sm4e','sm4ekey'):
            gap[(ln, an)] += 1; gapex.setdefault((ln, an), w)
        else:
            stats['rejected-ok:' + str(an) + (':UNDEF' if und else '')] += 1
with open(out + '/decodecmp.txt', 'w') as f:
    print('words', len(ws), file=f)
    for k, v in sorted(stats.items()): print('agree', k, v, file=f)
    for k, v in sorted(gap.items(), key=str): print('GAP (asl valid, lean other/none)', k, v, hex(gapex[k]), file=f)
    for k, v in sorted(bad.items(), key=str):
        print('BAD lean', k[0], 'asl', k[1], k[2], len(v), 'e.g.', hex(v[0][0]), v[0][1], file=f)
print(open(out + '/decodecmp.txt').read())
