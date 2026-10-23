# Compare Janus decoder acceptance with GNU objdump on the same words.
import subprocess, sys, struct, os, tempfile
dec = [l.split(' ', 2) for l in open(sys.argv[1])]
words = [int(d[0], 16) for d in dec]
ok = [d[1] == 'ok' for d in dec]
tmp = tempfile.mkdtemp()
binp = os.path.join(tmp, 'w.bin')
with open(binp, 'wb') as f:
    for w in words: f.write(struct.pack('<I', w))
out = subprocess.run(['aarch64-linux-gnu-objdump', '-D', '-b', 'binary', '-m', 'aarch64', binp],
                     capture_output=True, text=True).stdout
dis = {}
for line in out.splitlines():
    parts = line.split('\t')
    if len(parts) >= 3 and parts[0].strip().endswith(':'):
        try: off = int(parts[0].strip()[:-1], 16)
        except ValueError: continue
        dis[off // 4] = '\t'.join(parts[2:]).strip()
bad = 0
for i, w in enumerate(words):
    d = dis.get(i, '?')
    invalid = d.startswith('.inst') or 'undefined' in d or 'unallocated' in d or 'unpredictable' in d.lower() or 'reserved' in d.lower()
    if ok[i] and invalid:
        bad += 1
        if bad <= 40: print('MODEL-OK/OBJDUMP-INVALID', hex(w), d, '|', dec[i][2].strip()[:120])
print('model-ok', sum(ok), 'model-ok-but-objdump-invalid', bad)
