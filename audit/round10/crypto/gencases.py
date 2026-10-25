# Targeted oracle cases for the crypto/CRC32/permute/AES/TBL/EXT/scalar-DUP families plus every
# single-bit neighbour of each base word.  Usage: python3 -I gencases.py N SEED OUT.jsonl
import json, random, sys
N = int(sys.argv[1]); R = random.Random(int(sys.argv[2])); out = open(sys.argv[3], 'w')
M64 = (1 << 64) - 1; M128 = (1 << 128) - 1
def edge64(): return R.choice([0, 1, 2, 0x7f, 0x80, 0xff, 0x80000000, 0xffffffff, 0x100000000, 1 << 63, M64, M64 - 1, 0x5555555555555555, 0xaaaaaaaaaaaaaaaa])
def x64():
    k = R.random()
    if k < 0.3: return edge64()
    if k < 0.5: return R.getrandbits(32)
    return R.getrandbits(64)
def v128(tbl=False):
    k = R.random()
    if tbl and k < 0.5:   # TBL index vectors: mostly 0..63 with some out of range
        return int.from_bytes(bytes(R.choice([R.randrange(64), R.randrange(16), R.randrange(256), 0xff, 0x40, 0x3f, 0x10, 0x20, 0x30]) for _ in range(16)), 'little')
    if k < 0.15: return R.choice([0, M128, 1, 1 << 127, (1 << 64) - 1, M128 ^ ((1 << 64) - 1), 0x80808080808080808080808080808080, 0x0101010101010101 * ((1 << 64) + 1)])
    return R.getrandbits(128)
def regs(n, wrap=False):
    k = R.random()
    if k < 0.25:  # aliasing
        r = R.randrange(32); return [r] * n
    if wrap and k < 0.6: return [R.choice([28, 29, 30, 31])] + [R.randrange(32) for _ in range(n - 1)]
    return [R.randrange(32) for _ in range(n)]
KINDS = {}
def kind(name):
    def d(f): KINDS[name] = f; return f
    return d
@kind('aes')
def _():
    rd, rn = regs(2); return 0x4E284800 | R.randrange(4, 8) << 12 | rn << 5 | rd
@kind('sha3reg')
def _():
    rd, rn, rm = regs(3); return 0x5E000000 | rm << 16 | R.randrange(7) << 12 | rn << 5 | rd
@kind('sha2reg')
def _():
    rd, rn = regs(2); return 0x5E280800 | R.randrange(3) << 12 | rn << 5 | rd
@kind('sha512reg')
def _():
    rd, rn, rm = regs(3); return 0xCE608000 | rm << 16 | R.randrange(4) << 10 | rn << 5 | rd
@kind('sha512su0')
def _():
    rd, rn = regs(2); return 0xCEC08000 | rn << 5 | rd
@kind('sha4reg')
def _():
    rd, rn, rm, ra = regs(4); return 0xCE000000 | R.randrange(2) << 21 | rm << 16 | ra << 10 | rn << 5 | rd
@kind('xar')
def _():
    rd, rn, rm = regs(3); return 0xCE800000 | rm << 16 | R.randrange(64) << 10 | rn << 5 | rd
@kind('pmull')
def _():
    rd, rn, rm = regs(3); return 0x0E20E000 | R.randrange(2) << 30 | R.choice([0, 3]) << 22 | rm << 16 | rn << 5 | rd
@kind('crc32')
def _():
    rd, rn, rm = regs(3); sz = R.randrange(4); sf = 1 if sz == 3 else 0
    return 0x1AC04000 | sf << 31 | rm << 16 | R.randrange(2) << 12 | sz << 10 | rn << 5 | rd
@kind('permute')
def _():
    rd, rn, rm = regs(3)
    while True:
        q, size = R.randrange(2), R.randrange(4)
        if not (size == 3 and q == 0): break
    return 0x0E000800 | q << 30 | size << 22 | rm << 16 | R.choice([1, 2, 3, 5, 6, 7]) << 12 | rn << 5 | rd
@kind('dupscalar')
def _():
    rd, rn = regs(2)
    while True:
        imm5 = R.randrange(32)
        if imm5 & 15: break
    return 0x5E000400 | imm5 << 16 | rn << 5 | rd
@kind('tbl')
def _():
    rd, rn, rm = regs(3, wrap=True)
    return 0x0E000000 | R.randrange(2) << 30 | rm << 16 | R.randrange(4) << 13 | R.randrange(2) << 12 | rn << 5 | rd
@kind('ext')
def _():
    rd, rn, rm = regs(3); q = R.randrange(2)
    return 0x2E000000 | q << 30 | rm << 16 | R.randrange(16 if q else 8) << 11 | rn << 5 | rd
cid = 0
def emit(cls, w, tbl=False):
    global cid
    c = dict(id=cid, **{'class': cls}, word='0x%08x' % w, pc='0x1000000800',
             x=['0x%x' % x64() for _ in range(31)], sp='0x10000404f0', nzcv=R.randrange(16),
             seed=R.randrange(1 << 20), dczid=7, v=['0x%032x' % v128(tbl) for _ in range(32)])
    out.write(json.dumps(c) + '\n'); cid += 1
for name, f in KINDS.items():
    seen = set()
    for i in range(N):
        w = f(); emit('a64c/' + name, w, tbl=(name == 'tbl'))
        if i < 64:   # neighbours: every single-bit flip of bits 31..10, two states each
            for bpos in range(10, 32):
                nw = w ^ (1 << bpos)
                if nw in seen: continue
                seen.add(nw)
                for _ in range(2): emit('a64c-nb/' + name, nw)
print(cid, file=sys.stderr)
