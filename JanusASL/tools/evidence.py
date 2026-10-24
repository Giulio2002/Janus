#!/usr/bin/env python3
"""Cross-check janus-asl-check MISMATCHes against the two independent references.

    evidence.py VERDICTS CASES QEMU_HW SAIL_CPP > table.md

For every MISMATCH whose reason is a register difference ("X: janus [...] asl [...]"), print the
differing registers with the value of Janus, the generated Lean ASL model, qemu (hw.jsonl of
scripts/oracle.sh) and the Sail C++ model of the same ASL (sail.jsonl of scripts/oracle-sail.sh).
A row where qemu or C++ Sail disagrees with Janus is flagged JANUS? (a potential Janus bug).
"""
import json, re, sys

verdicts, cases, hwf, sailf = sys.argv[1:5]
mism = {}
for l in open(verdicts):
    j = json.loads(l)
    if j["verdict"] == "MISMATCH":
        mism[j["id"]] = j
def load(path):
    out = {}
    for l in open(path):
        if any(('"id":%d,' % i) in l for i in ()):
            pass
        j = json.loads(l)
        if j.get("id") in mism:
            out[j["id"]] = j
    return out
cs, hw, sail = load(cases), load(hwf), load(sailf)
rows, flagged, other = [], 0, []
for i, j in sorted(mism.items()):
    m = re.match(r"X: janus \[(.*)\] asl \[(.*)\]", j["why"])
    if not m:
        other.append(j)
        continue
    a, b = m.group(1).split(", "), m.group(2).split(", ")
    for r in range(31):
        if a[r] != b[r]:
            q = hw[i]["x"][r] if hw.get(i, {}).get("status") == "ok" else hw.get(i, {}).get("status")
            s = sail[i]["x"][r] if sail.get(i, {}).get("status") == "ok" else sail.get(i, {}).get("status")
            ok = int(q, 16) == int(a[r], 16) and int(s, 16) == int(a[r], 16)
            flagged += not ok
            rows.append((i, j["class"], j["word"], "X%d" % r, a[r], b[r], q, s, "" if ok else "JANUS?"))
print("| id | class | word | reg | Janus | Lean ASL | qemu | Sail C++ | |")
print("|---:|---|---|---|---|---|---|---|---|")
for r in rows:
    print("| " + " | ".join(str(x) for x in r) + " |")
print()
print("register-difference mismatches: %d cases, %d rows; rows where qemu or Sail C++ differ from Janus: %d; other mismatches: %d"
      % (len(mism) - len(other), len(rows), flagged, len(other)))
