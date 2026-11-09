# gdb -batch -x maps_amd64.py --args probe9-amd64 maps 2000
# At calls of runtime.mapaccess2_fast64 / mapaccess1_fast64 on a small map, check what
# smallModel (Janus/Spec/SwissMap.lean) needs from one interval `heap`: it must hold the 48-byte
# header and the 136-byte group, and (Access1's RTPre) the stack window [RSP - 64, RSP + 32) must
# lie outside it. The tightest candidate is the hull of header and group.
import gdb
gdb.execute("set pagination off"); gdb.execute("set confirm off")
def rd(a, n=8):
    return int.from_bytes(bytes(gdb.selected_inferior().read_memory(a, n)), "little")
for fn in ("runtime.mapaccess2_fast64", "runtime.mapaccess1_fast64"):
    try: gdb.execute("break '%s'" % fn)
    except gdb.error: pass
gdb.execute("run")
n = small = ok = 0
while n < 400:
    try: fr = gdb.selected_frame()
    except gdb.error: break
    mp = int(fr.read_register("rbx")); sp = int(fr.read_register("rsp"))
    if mp and rd(mp + 24) == 0:
        small += 1
        grp = rd(mp + 16)
        lo, hi = min(mp, grp), max(mp + 48, grp + 136)
        ok += (sp + 32 <= lo or hi <= sp - 64)
    n += 1
    try: gdb.execute("continue", to_string=True)
    except gdb.error: break
print("PROBE maps-amd64: calls=%d small=%d heap_interval_ok=%d" % (n, small, ok))
gdb.execute("kill")
