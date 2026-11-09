# gdb -batch -x wb_amd64.py --args probertstr-amd64 wb 200000
# At real calls of runtime.gcWriteBarrier2 (SetNext's barrier, made only with the GC marking),
# evaluate examples/proofs-amd64/WriteBarrier's readiness HRoom for N = 2: g.m, m.p and
# p.wbBuf.{next,end} readable, the buffer has room for 2 pointers at an 8-aligned next, and the
# barrier's frame [RSP-120, RSP+8) apart from those runtime objects (rt is taken to be exactly
# them). The theorem speaks about the calls where HRoom holds; the others are the flushes
# (the buffer is full), which the contract leaves to wbBufFlush.
import gdb
gdb.execute("set pagination off")
gdb.execute("set confirm off")
OFF_M, OFF_P, OFF_NEXT, OFF_END = 0x30, 0xd0, 0x2550, 0x2558
def rd(a, n=8):
    return int.from_bytes(bytes(gdb.selected_inferior().read_memory(a, n)), "little")
gdb.execute("break runtime.gcWriteBarrier2")
gdb.execute("run")
calls = room = apart = 0
while calls < 2000:
    try:
        fr = gdb.selected_frame()
    except gdb.error:
        break
    calls += 1
    g = int(fr.read_register("r14")); sp = int(fr.read_register("rsp"))
    m = rd(g + OFF_M); p = rd(m + OFF_P); nxt = rd(p + OFF_NEXT); end = rd(p + OFF_END)
    ok = nxt + 16 <= end and nxt % 8 == 0 and end <= 1 << 48
    objs = [(g + OFF_M, 8), (m + OFF_P, 8), (p + OFF_NEXT, 16), (nxt, 16)]
    ap = all(a + k <= sp - 120 or sp + 8 <= a for a, k in objs)
    room += ok; apart += (ok and ap)
    try:
        gdb.execute("continue", to_string=True)
    except gdb.error:
        break
print("PROBE wb-amd64: calls=%d room=%d hroom=%d" % (calls, room, apart))
gdb.execute("kill")
