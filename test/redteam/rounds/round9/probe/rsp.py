"""Minimal GDB remote-serial-protocol client for qemu-user's gdb stub (arm64 probes; the host
has no aarch64 gdb). Software breakpoints (Z0), continue, register and memory reads."""
import socket, subprocess, time, os

class RSP:
    def __init__(self, port):
        for _ in range(100):
            try:
                self.s = socket.create_connection(("127.0.0.1", port)); break
            except OSError:
                time.sleep(0.05)
        self.s.settimeout(120)
        self.buf = b""
    def _send(self, data):
        ck = sum(data.encode()) % 256
        self.s.sendall(b"$" + data.encode() + b"#%02x" % ck)
    def _recv(self):
        while True:
            i = self.buf.find(b"$")
            if i >= 0:
                j = self.buf.find(b"#", i)
                if j >= 0 and len(self.buf) >= j + 3:
                    pkt = self.buf[i + 1:j].decode()
                    self.buf = self.buf[j + 3:]
                    self.s.sendall(b"+")
                    return pkt
            chunk = self.s.recv(65536)
            if not chunk:
                raise EOFError
            self.buf += chunk
    def cmd(self, data):
        self._send(data); r = self._recv()
        # an extra stop reply (two threads hitting a breakpoint together) is not the answer
        while data not in ("c", "s", "?") and r[:1] in ("T", "S"):
            r = self._recv()
        if os.environ.get("RSP_TRACE"):
            print(">", data, "<", r[:60])
        return r
    def regs(self):
        h = self.cmd("g")
        r = [int.from_bytes(bytes.fromhex(h[16 * i:16 * i + 16]), "little") for i in range(33)]
        return r  # x0..x30, sp, pc
    def mem(self, a, n):
        out = b""
        while n > 0:
            k = min(n, 2048)
            h = self.cmd("m%x,%x" % (a, k))
            if h.startswith("E"):
                raise IOError("unreadable %x" % a)
            out += bytes.fromhex(h); a += k; n -= k
        return out
    def rd(self, a, n=8):
        return int.from_bytes(self.mem(a, n), "little")
    def bp(self, a):
        assert self.cmd("Z0,%x,4" % a) == "OK"
        self.bps = getattr(self, "bps", set()) | {a}
    def unbp(self, a):
        self.cmd("z0,%x,4" % a)
        self.bps.discard(a)
    def _stop(self, st):
        # make the stopped thread the one register and memory reads refer to
        if "thread:" in st:
            tid = st.split("thread:")[1].split(";")[0]
            self.cmd("Hg" + tid)
        return st
    def cont(self):
        # qemu's stub does not step over a breakpoint at the current pc. Single-stepping one
        # thread of a multi-threaded process desynchronises the stop replies, so instead lift
        # the breakpoint, run to a temporary one at pc + 4, and re-arm.
        pc = self.regs()[32]
        if pc in getattr(self, "bps", set()):
            self.cmd("z0,%x,4" % pc); self.cmd("Z0,%x,4" % (pc + 4))
            while True:
                st = self._stop(self.cmd("c"))
                if not st.startswith("T") or self.regs()[32] == pc + 4:
                    break
            self.cmd("z0,%x,4" % (pc + 4)); self.cmd("Z0,%x,4" % pc)
            if not st.startswith("T"):
                return st
        return self._stop(self.cmd("c"))
    def step(self):
        return self.cmd("s")

def symbols(binary):
    out = subprocess.run(["nm", binary], capture_output=True, text=True).stdout
    d = {}
    for line in out.splitlines():
        p = line.split()
        if len(p) == 3:
            d[p[2]] = int(p[0], 16)
    return d

def launch(binary, args, port):
    p = subprocess.Popen(["qemu-aarch64", "-g", str(port), binary] + args,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return p, RSP(port)
