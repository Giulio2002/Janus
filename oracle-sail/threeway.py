#!/usr/bin/env python3
"""Three-way agreement report: Janus (Lean model) vs Sail (Arm ASL) vs qemu.

usage: threeway.py DIR

DIR (written by scripts/oracle-sail.sh) holds
  cases.jsonl               the corpus (layout.Case)
  qemu.jsonl                qemu runner results (layout.HW)
  janus.jsonl               janus-oracle results (layout.Model)
  sail.jsonl                janus-oracle-sail results (layout.HW + esr/far/ec)
  janus-vs-sail/verdicts.jsonl   `oracle run` verdicts, hardware := Sail, model := Janus
  qemu-vs-sail/verdicts.jsonl    `oracle run` verdicts, hardware := qemu, model := Sail
  janus-vs-qemu/verdicts.jsonl   `oracle run` verdicts, hardware := qemu, model := Janus
The pairwise verdicts come from the qemu agent's comparator (oracle/cmd/oracle/compare.go),
unchanged; this script only joins them and adds a signal-level check of faults.
Writes DIR/threeway.md and DIR/soundness.jsonl.
"""
import collections
import json
import os
import sys

D = sys.argv[1]


def load(path, key="id"):
    out = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                v = json.loads(line)
                out[v.get(key)] = v
    return out


cases = load(os.path.join(D, "cases.jsonl"))
qemu = load(os.path.join(D, "qemu.jsonl"))
janus = load(os.path.join(D, "janus.jsonl"))
sail = load(os.path.join(D, "sail.jsonl"))
V = {p: load(os.path.join(D, p, "verdicts.jsonl")) for p in ("janus-vs-sail", "qemu-vs-sail", "janus-vs-qemu")}


def bits(w, hi, lo):
    return (w >> lo) & ((1 << (hi - lo + 1)) - 1)


def store_exclusive(w):
    """STXR/STLXR/STXP/STLXP: sail-arm stubs the exclusive monitor (always passes)."""
    if w & 0x3F000000 != 0x08000000:
        return False
    o2, l, o1 = bits(w, 23, 23), bits(w, 22, 22), bits(w, 21, 21)
    if o2 != 0 or l != 0:
        return False
    if o1 == 1 and bits(w, 31, 30) < 2 and bits(w, 14, 10) == 31:
        return False  # CASP
    return True


def sbo_violation(w):
    """Arm ARM "(1)" (should-be-one) fields of the load/store exclusive and ordered encodings
    (C4.1.66/C4.1.68) not all ones: CONSTRAINED UNPREDICTABLE. sail-arm decodes them as
    UNDEFINED (its decode patterns hard-code the ones); qemu ignores the fields."""
    if w & 0x3F000000 != 0x08000000:
        return False
    o2, l, o1 = bits(w, 23, 23), bits(w, 22, 22), bits(w, 21, 21)
    rs, rt2, size = bits(w, 20, 16), bits(w, 14, 10), bits(w, 31, 30)
    if o2 == 0 and o1 == 0:
        return rt2 != 31 or (l == 1 and rs != 31)  # STXR: Rt2; LDXR: Rs, Rt2
    if o2 == 0 and o1 == 1:
        if size < 2:
            return rt2 != 31  # CASP
        return l == 1 and rs != 31  # LDXP: Rs
    if o2 == 1 and o1 == 0:
        return rs != 31 or rt2 != 31  # LDAR/STLR/LDLAR/STLLR
    return rt2 != 31  # CAS


def pauth(w):
    """PAuth: PAC*/AUT*/XPAC* hints, data-processing PAC*/AUT*/XPAC*, PACGA, LDRAA/LDRAB,
    RETAA/RETAB, BRAA..., ERETAA (results depend on the keys or on FEAT_FPAC)."""
    if w & 0xFFFFFC1F == 0xD503201F and ((w >> 5) & 0x7F) in (0x08, 0x0A, 0x0C, 0x0E, 0x07,
                                                              0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F):
        return True
    if w & 0xFFFFC000 == 0xDAC10000:  # PACIA..XPACD (dp1, opcode2 = 1)
        return True
    if w & 0xFFE0FC00 == 0x9AC03000:  # PACGA
        return True
    if w & 0xFF200400 == 0xF8200400:  # LDRAA/LDRAB
        return True
    if w & 0xFE000800 == 0xD6000800:  # BRAA/BLRAA/RETAA/ERETAA ... (Z/M forms)
        return True
    return False


def tag(cid):
    c = cases[cid]
    w = int(c["word"], 16)
    t = []
    if "!unpredictable" in c.get("class", ""):
        t.append("unpredictable")
    s = sail.get(cid) or {}
    if s.get("unpredictable"):
        t.append("sail-unpredictable")
    if (w & 0x3B200C00) == 0x19000400 or (w & 0x3BE00C00) == 0x19C00400:
        t.append("mops-impdef")  # CPY*/SET*: per-stage sizes are IMPLEMENTATION DEFINED
    if pauth(w):
        t.append("pauth-keys")  # result depends on the PAC keys (qemu: random per process)
    q = qemu.get(cid) or {}
    if s.get("status") == "fault" and "translation" in (s.get("note") or "") and q.get("status") == "ok":
        t.append("qemu-process-memory")  # the address is mapped in the qemu runner process
    if s.get("status") in ("ok", "selfloop") and q.get("status") == "fault" and q.get("sig") == 4:
        t.append("qemu-lacks-feature")  # e.g. FEAT_THE (RCW*), FEAT_LRCPC3 (LDIAPP/STILP)
    if sbo_violation(w):
        t.append("sbo-unpredictable")
    if store_exclusive(w):
        t.append("sail-monitor-stub")
    if s.get("status") == "error":
        t.append("sail-error")
    return t


def short(v):
    if v is None:
        return "none"
    return v["verdict"]


ids = sorted(cases)
pair_counts = {p: collections.Counter(short(V[p].get(i)) for i in ids) for p in V}
triple = collections.Counter()
for i in ids:
    triple[(short(V["janus-vs-sail"].get(i)), short(V["qemu-vs-sail"].get(i)), short(V["janus-vs-qemu"].get(i)))] += 1

# Signal-level agreement where qemu and Sail both fault.
sig_pairs = collections.Counter()
sig_examples = collections.defaultdict(list)
addr_mismatch = collections.Counter()
for i in ids:
    q, s = qemu.get(i), sail.get(i)
    if q and s and q.get("status") == "fault" and s.get("status") == "fault":
        k = (q.get("sig", 0), q.get("code", 0), s.get("sig", 0), s.get("code", 0))
        sig_pairs[k] += 1
        if k[0] != k[2] or k[1] != k[3]:
            if len(sig_examples[k]) < 3:
                sig_examples[k].append(i)
        elif q.get("addr") != s.get("addr") and q.get("sig") in (7, 11):
            addr_mismatch[cases[i]["class"]] += 1

# Soundness: Janus succeeded, result differs from Sail.
sound = []
for i in ids:
    v = V["janus-vs-sail"].get(i)
    if v and v["verdict"] == "MISMATCH":
        qv = V["qemu-vs-sail"].get(i)
        jq = V["janus-vs-qemu"].get(i)
        sound.append({
            "id": i, "class": cases[i]["class"], "word": cases[i]["word"], "asm": v.get("asm", ""),
            "kind": v["kind"], "diffs": v.get("diffs", []), "tags": tag(i),
            "qemu_vs_sail": short(qv), "janus_vs_qemu": short(jq),
            "sail": {k: sail[i].get(k) for k in ("status", "sig", "code", "addr", "pc", "note", "esr", "far")},
        })
with open(os.path.join(D, "soundness.jsonl"), "w") as f:
    for r in sound:
        f.write(json.dumps(r) + "\n")

b = []
p = b.append
p("# Janus vs Sail vs qemu: three-way agreement\n")
p(f"{len(ids)} cases. Sail = rems-project sail-arm arm-v9.4-a (Arm ASL), EL0 Linux-like state; "
  "see docs/ORACLE-SAIL.md. Verdicts are the qemu agent's comparator: `agree` (identical "
  "successor state, or both fault), `MISMATCH` (the *model* side succeeded with a state the "
  "*hardware* side does not produce, or succeeded where it faults), `model-gap` (model faulted, "
  "hardware succeeded), `unobserved`, `model-error`.\n")
p("| pair (hardware side vs model side) | agree | MISMATCH | model-gap | unobserved | model-error |")
p("|---|---:|---:|---:|---:|---:|")
names = {"janus-vs-sail": "Sail (hw) vs Janus (model)", "qemu-vs-sail": "qemu (hw) vs Sail (model)",
         "janus-vs-qemu": "qemu (hw) vs Janus (model)"}
for k in ("janus-vs-sail", "qemu-vs-sail", "janus-vs-qemu"):
    c = pair_counts[k]
    p(f"| {names[k]} | {c['agree']} | {c['MISMATCH']} | {c['model-gap']} | {c['unobserved']} | {c['model-error']} |")
p("")
p("## Joint verdicts (Janus-vs-Sail, qemu-vs-Sail, Janus-vs-qemu)\n")
p("| Janus vs Sail | qemu vs Sail | Janus vs qemu | cases |\n|---|---|---|---:|")
for k, n in triple.most_common():
    p(f"| {k[0]} | {k[1]} | {k[2]} | {n} |")
p("")

p("## Soundness: Janus succeeded with a result Sail does not produce\n")
by = collections.defaultdict(list)
for r in sound:
    by[(r["class"].split("!")[0].split("/")[-1], (r["asm"].split() or ["?"])[0], r["kind"],
        "+".join(r["tags"]) or "-", r["qemu_vs_sail"])].append(r)
p(f"**{len(sound)} cases** in {len(set(r['word'] for r in sound))} distinct words.\n")
if by:
    p("| class | mnemonic | kind | tags | qemu vs Sail | cases | words |\n|---|---|---|---|---|---:|---:|")
    for k, rs in sorted(by.items(), key=lambda kv: -len(kv[1])):
        p(f"| {k[0]} | `{k[1]}` | {k[2]} | {k[3]} | {k[4]} | {len(rs)} | {len(set(r['word'] for r in rs))} |")
    p("")
    for k, rs in sorted(by.items(), key=lambda kv: -len(kv[1])):
        r = rs[0]
        c = cases[r["id"]]
        p(f"### `{k[1]}` ({k[0]}, {k[2]}, tags {k[3]}, qemu vs Sail: {k[4]})\n")
        p(f"* case {r['id']}: word `{r['word']}` = `{r['asm']}`")
        for d in r["diffs"]:
            p(f"  * {d.replace('hw ', 'sail ')}")
        s = r["sail"]
        p(f"  * sail: status {s['status']} pc {s.get('pc')} {s.get('note') or ''} {('esr ' + s['esr']) if s.get('esr') else ''}")
        w = int(c["word"], 16)
        regs = sorted({w & 31, (w >> 5) & 31, (w >> 10) & 31, (w >> 16) & 31})
        p("  * input: " + " ".join(f"x{q}={c['x'][q]}" for q in regs if q < 31) +
          f" sp={c['sp']} nzcv={c['nzcv']:04b} seed={c['seed']}")
        p("")

p("## qemu vs Sail disagreements (Sail as the reference)\n")
qs = collections.Counter()
qex = {}
for i in ids:
    v = V["qemu-vs-sail"].get(i)
    if v and v["verdict"] not in ("agree",):
        k = (v["verdict"], v["class"].split("!")[0].split("/")[-1], (v.get("asm", "").split() or ["?"])[0], v["kind"],
             "+".join(tag(i)) or "-")
        qs[k] += 1
        qex.setdefault(k, v)
p("Read `MISMATCH` here as *Sail succeeded where qemu faulted, or with a different state*, "
  "and `model-gap` as *Sail faulted where qemu succeeded*.\n")
p("| verdict | class | mnemonic | kind | tags | cases | example |\n|---|---|---|---|---|---:|---|")
for k, n in qs.most_common(60):
    e = qex[k]
    d = "; ".join(e.get("diffs", [])[:2]).replace("|", "/")
    p(f"| {k[0]} | {k[1]} | `{k[2]}` | {k[3]} | {k[4]} | {n} | {e['id']} `{e['word']}` {d[:160]} |")
if len(qs) > 60:
    p(f"\n... {len(qs) - 60} more groups (see qemu-vs-sail/verdicts.jsonl)")
p("")
p("## Fault signals where qemu and Sail both fault\n")
p("| qemu sig/code | Sail sig/code | cases | examples |\n|---|---|---:|---|")
for k, n in sig_pairs.most_common():
    p(f"| {k[0]}/{k[1]} | {k[2]}/{k[3]} | {n} | {' '.join(map(str, sig_examples.get(k, [])))} |")
p("")
if addr_mismatch:
    p("si_addr differs (same signal) by class: " + ", ".join(f"{k} {v}" for k, v in addr_mismatch.most_common()) + "\n")
open(os.path.join(D, "threeway.md"), "w").write("\n".join(b) + "\n")
print("\n".join(b[:40]))
