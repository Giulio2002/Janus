# gdb -batch -x setnext_amd64.py --args probe9-amd64 loopgc 200000
# At every call of example.com/basic.SetNext made with the write barrier on, read the runtime
# state BarrierOK (examples/proofs-amd64/SetNext/Proof.lean) talks about and check whether ANY
# interval [lo, hi) can satisfy it: it must contain g.m, m.p, p.wbBuf.{next,end} and the two
# buffer slots, and be disjoint from n.Next and the stack window [RSP-136, RSP+8).
# The tightest candidate is lo = min(...), hi = max(...): if it fails, every interval fails.
import gdb
gdb.execute("set pagination off")
gdb.execute("set confirm off")
OFF_M, OFF_P, OFF_NEXT, OFF_END = 0x30, 0xd0, 0x2550, 0x2558   # read off gcWriteBarrier
inf = None
def rd(a, n=8):
    return int.from_bytes(bytes(gdb.selected_inferior().read_memory(a, n)), "little")
def sym(name):
    return int(gdb.lookup_global_symbol(name).value().address)
wb = sym("runtime.writeBarrier")
m0 = sym("runtime.m0")
gdb.execute("break 'example.com/basic.SetNext'")
gdb.execute("run")
stats = {"on": 0, "sat": 0, "m0": 0}
fails = []
calls = 0
while calls < 400000 and stats["on"] < 300:
    calls += 1
    try:
        fr = gdb.selected_frame()
    except gdb.error:
        break
    if rd(wb, 4) != 0:
        g = int(fr.read_register("r14")); n = int(fr.read_register("rax"))
        sp = int(fr.read_register("rsp"))
        m = rd(g + OFF_M); p = rd(m + OFF_P); nxt = rd(p + OFF_NEXT)
        objs = [(g + OFF_M, 8), (m + OFF_P, 8), (p + OFF_NEXT, 16), (nxt, 16)]
        lo = min(a for a, k in objs); hi = max(a + k for a, k in objs)
        disj = lambda a, k: a + k <= lo or hi <= a
        ok = disj(n, 8) and disj(sp - 136, 144)
        ap = lambda a, k, b, l: a + k <= b or b + l <= a
        fixed = all(ap(a, k, n, 8) and ap(a, k, sp - 136, 144) for a, k in objs) and \
            ap(nxt, 16, p + OFF_NEXT, 16)
        stats["on"] += 1; stats["sat"] += ok; stats["m0"] += (m == m0)
        stats["fixed"] = stats.get("fixed", 0) + fixed
        if not ok and len(fails) < 3:
            fails.append(dict(g=hex(g), m=hex(m), p=hex(p), next=hex(nxt), n=hex(n), sp=hex(sp),
                              lo=hex(lo), hi=hex(hi)))
    try:
        gdb.execute("continue", to_string=True)
    except gdb.error:
        break
print("PROBE setnext-amd64: calls=%d barrier_on=%d barrierok_satisfiable=%d barrierok_round9=%d on_m0=%d" %
      (calls, stats["on"], stats["sat"], stats.get("fixed", 0), stats["m0"]))
for f in fails:
    print("  counterexample", f)
gdb.execute("kill")
