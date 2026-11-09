# Parse sail-arm __DecodeA64_* clauses into (mask, value, guard?, decode_fn) in source order.
import re, sys, json
SRC = "/srv/janus-asl-deps/sail-arm-7d05816/arm-v9.4-a/src/instrs64.sail"
def parse():
    txt = open(SRC).read()
    out = []
    for m in re.finditer(r'^function clause (__DecodeA64_\w+) \(\(pc, (.*?)\)\) if (.*?) = \{\n(.*?)\n\}\n', txt, re.S | re.M):
        grp, pat, guard, body = m.groups()
        pat = pat.strip()
        if pat.startswith('(0b'):
            bitsstr = re.match(r'\(0b([01]{32}) as __opcode', pat).group(1)
            mask = 0xFFFFFFFF; val = int(bitsstr, 2)
        else:
            inner = re.match(r'\(\[(.*)\] as __opcode', pat, re.S).group(1)
            ents = [e.strip() for e in inner.split(',')]
            assert len(ents) == 32, (len(ents), pat[:80])
            mask = val = 0
            for i, e in enumerate(ents):
                b = 31 - i
                if e == 'bitone': mask |= 1 << b; val |= 1 << b
                elif e == 'bitzero': mask |= 1 << b
                else: assert e == '_', e
        extra = re.sub(r'SEE < \d+', '', guard).strip()
        calls = re.findall(r'\b(decode_\w+)\(', body)
        out.append(dict(grp=grp, mask=mask, val=val, guard=extra, fn=calls[-1] if calls else None))
    return out
if __name__ == '__main__':
    cs = parse()
    print(len(cs), file=sys.stderr)
    json.dump(cs, open(sys.argv[1], 'w'))
