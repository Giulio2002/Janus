# python3 -I mallocfast_arm64.py BINARY  (BINARY = probe9-arm64, built from audit/round9/probe)
# Stops at runtime.mallocgc calls with typ = nil and 16 <= size <= 1016 (the requests
# examples/proofs/MallocFast.lean covers; growslice of []uint64 makes them) and evaluates every
# conjunct of MCacheOK that is a property of the runtime state (Go 1.26 linux/arm64 layout, the
# offsets the proof uses), plus the Spread facts that involve the runtime globals.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsp import launch, symbols
binary = sys.argv[1]
N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
S = symbols(binary)
mallocgc = S["runtime.mallocgc"]
G = dict(debugMalloc=(S["runtime.debug"] + 0x2c, 1), gcBlackenEnabled=(S["runtime.gcBlackenEnabled"], 4),
         sizeToClass8=(S["internal/runtime/gc.SizeToSizeClass8"], 129),
         classToSize=(S["internal/runtime/gc.SizeClassToSize"], 136),
         writeBarrier=(S["runtime.writeBarrier"], 1), memProfileRate=(S["runtime.MemProfileRate"], 8))
globLo = min(a for a, n in G.values()); globHi = max(a + n for a, n in G.values())
m0 = S["runtime.m0"]
proc, r = launch(binary, ["strcat", "200000"], 41234 + os.getpid() % 1000)
# start sampling once the program's own loop runs (runtime start-up allocates from empty mcaches)
r.bp(S["example.com/basic.AppendOne"]); r.cont(); r.unbp(S["example.com/basic.AppendOne"])
r.bp(mallocgc)
fails = {}; hits = 0; onm0 = 0; allok = 0; okNoGlobSpread = 0
def apart(a, n, b, k): return a + n <= b or b + k <= a
stops = 0
while hits < N:
    try:
        st = r.cont()
    except (TimeoutError, EOFError):
        break
    stops += 1
    if not st.startswith("T"):
        break
    x = r.regs()
    size, typ = x[0], x[1]
    if typ != 0 or not (16 <= size <= 1016):
        continue
    hits += 1
    g = x[28]; sp = x[31]
    rd = r.rd
    m = rd(g + 48); p = rd(m + 208)
    if p == 0:
        fails["p != 0"] = fails.get("p != 0", 0) + 1
        continue
    c = rd(p + 56)
    sc = rd(G["sizeToClass8"][0] + (size + 7) // 8, 1)
    cs = rd(G["classToSize"][0] + 2 * sc, 2)
    span = rd(c + 48 + 8 * (2 * sc + 1))
    cache = rd(span + 56); fidx = rd(span + 48, 2); nel = rd(span + 50, 2)
    base = rd(span + 24); esz = rd(span + 104); nz = rd(span + 100, 1)
    if os.environ.get("PROBE_DEBUG") and hits <= 5:
        print("dbg size=%d sc=%d cs=%d m=%x p=%x c=%x span=%x cache=%x fidx=%d nel=%d esz=%d base=%x nz=%d" %
              (size, sc, cs, m, p, c, span, cache, fidx, nel, esz, base, nz))
    ctz = (cache & -cache).bit_length() - 1 if cache else 64
    res = ctz + fidx; slot = (base + esz * res) % 2**64
    try:
        zero = all(b == 0 for b in r.mem(slot, cs))
    except IOError:
        zero = False
    conds = {
        "p != 0": p != 0, "sc < 68": sc < 68, "allocCache != 0": cache != 0,
        "res < nelems": res < nel, "refill cond": (res + 1) % 64 != 0 or res + 1 == nel,
        "slot != 0": slot != 0, "span.needzero = 0": nz == 0, "slot zero": zero,
        "elemsize = class size": esz == cs,
        "debug.malloc off": rd(*G["debugMalloc"]) % 2 == 0,
        "gcBlackenEnabled = 0": rd(*G["gcBlackenEnabled"]) == 0,
        "writeBarrier off": rd(*G["writeBarrier"]) % 2 == 0,
        "no sample due": (rd(c) + 2**64 - cs) % 2**64 < 2**63,
        "MemProfileRate = c.memProfRate": rd(*G["memProfileRate"]) == rd(c + 8),
    }
    objs = [(sp - 152, 184), (g + 16, 162), (m + 208, 60), (p + 56, 8), (c, 1136), (span + 24, 88),
            (slot, cs)]
    spread_rt = all(apart(*objs[i], *objs[j]) for i in range(len(objs)) for j in range(i))
    glob_range = all(apart(a, n, globLo, globHi - globLo) for a, n in objs)
    glob_each = all(apart(a, n, b, k) for a, n in objs for b, k in G.values())
    conds["Spread (runtime objects)"] = spread_rt
    conds["Spread vs one globals range (shipped MCacheOK)"] = glob_range
    conds["apart from each global (fixed MCacheOK)"] = glob_each
    onm0 += (m == m0)
    for k, v in conds.items():
        if not v:
            fails[k] = fails.get(k, 0) + 1
    if all(conds.values()) or all(v for k, v in conds.items() if k != "apart from each global (fixed MCacheOK)"):
        allok += all(v for k, v in conds.items() if k != "apart from each global (fixed MCacheOK)")
    okNoGlobSpread += all(v for k, v in conds.items() if k != "Spread vs one globals range (shipped MCacheOK)")
print("stops at mallocgc: %d" % stops)
print("PROBE mallocfast-arm64: calls=%d on_m0=%d MCacheOK(shipped)=%d MCacheOK(fixed)=%d" %
      (hits, onm0, allok, okNoGlobSpread))
for k, v in sorted(fails.items(), key=lambda kv: -kv[1]):
    print("  failed %-48s %d/%d" % (k, v, hits))
proc.kill()
