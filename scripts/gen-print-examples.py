#!/usr/bin/env python3
"""Generate the example modules examples/proofs-print/PrintProofs/<Isa>/Print{X,Bool,Neg,Str}.lean from the
proofs about the shared code (Main{X,Bool,Neg,Str}.lean there, which are about `PrintCode.program`):
each example module imports `Extracted` (the extraction of one entry point, which `janus verify`
supplies), proves that `Extracted.program` has the same code as `PrintCode.program`
(`Program.Equiv`, by `decide`) and transports the guarantees (`correctness`, `full_output`,
`Witness.nonvacuous`, `Witness.returns`) of the Main module to `Extracted.program`. The expensive
proofs about the print functions are built and checked once, in the Fn* and Main* modules; the
example modules hold only the `decide` and the transport lemmas.

Usage: scripts/gen-print-examples.py [--check] arm64|amd64
  --check   exit 1 if a generated file differs from what the Main modules give."""
import re, sys, os
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
check = "--check" in sys.argv[1:]
isa = [a for a in sys.argv[1:] if not a.startswith("--")][0]
bad = 0
ISA = {"arm64": "Arm64", "amd64": "Amd64"}[isa]
base = os.path.join(root, "examples", "proofs-print", "PrintProofs", ISA)
EX = {"PrintX": ("X", "hp.2.2.2" if False else None), "PrintBool": ("Bool", None), "PrintNeg": ("Neg", None), "PrintStr": ("Str", "rest")}
# which examples have extra precondition conjuncts after PrintReady/DataLoaded/DataOutside
REST = {"PrintX": False, "PrintBool": False, "PrintNeg": False, "PrintStr": True}
ARGS = {"PrintX": "x", "PrintBool": "b", "PrintNeg": "", "PrintStr": "ptr len"}
def stmt(text, name):
    i = text.index("theorem " + name + " ")
    m = re.search(r":=( by)?\n", text[i:])
    return text[i:i + m.start()], text[i + m.end():]
def block(text, name):
    # statement up to ':=' and the proof (to the next blank line followed by non-indented text)
    i = text.index("theorem " + name + " ")
    return i
def consts(isa):
    h = open(base + "/FnHead.lean").read()
    a = h.index("/-! ## The runtime's print globals")
    c = h[a:h.index("end PrintFn")].rstrip() + "\n"
    c = c.replace("P ", "Extracted.program ") if False else c
    return c
for ex, (n, _) in EX.items():
    mpath = f"{base}/Main{n}.lean"
    try:
        m = open(mpath).read()
    except FileNotFoundError:
        continue
    pre_doc = m[m.index("/-!\n# "):m.index("namespace PrintFn.")]
    ent = f"PrintCode.entryPrint{ex[5:]}"
    def fix(t):
        return t.replace(ent, "Extracted.entry")
    s_corr, _ = stmt(m, "correctness")
    s_full, rest_full = stmt(m, "full_output")
    # full_output proof: until blank line before 'namespace Witness'
    full_proof = rest_full[:rest_full.index("\nnamespace Witness")].rstrip() + "\n"
    s_nv, _ = stmt(m, "nonvacuous")
    s_ret, _ = stmt(m, "returns")
    # docstrings preceding nonvacuous/returns
    def doc_before(name):
        i = m.index("theorem " + name + " ")
        j = m.rfind("/--", 0, i)
        k = m.rfind("\n\n", 0, i)
        return m[j:i] if j > k else ""
    d_nv, d_ret = doc_before("nonvacuous"), doc_before("returns")
    d_full = "/-- **Full output**: if fd 2 grew by as many bytes as the pieces hold, it grew by exactly them. -/\n"
    nsm = f"PrintFn.{n}"
    args = ARGS[ex]
    has_rest = REST[ex]
    arm = isa == "arm64"
    EQ = "Janus" if arm else "Janus.Amd64"
    PRN = "" if arm else "Amd64.Print."
    DO = "Janus.Print.DataOutside" if arm else "Janus.Amd64.Print.DataOutside"
    EK = "Janus.Kernel.EnsuresK" if arm else "Janus.Amd64.Kernel.EnsuresK"
    SEG = "Segment" if arm else "Amd64.Segment"
    SETUP = "⟨h5.pc, h5.lr, h5.args⟩" if arm else "⟨h5.rip, h5.ret, h5.zero, h5.len, h5.args, h5.df⟩"
    pre_tail = "hp.2.2.2" if has_rest else None
    xfer_pre = (("⟨hp.1, equiv.dataLoaded hp.2.1, {DO}.of_equiv equiv hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩" if has_rest else "⟨hp.1, equiv.dataLoaded hp.2.1, {DO}.of_equiv equiv hp.2.2⟩")).replace("{DO}", DO)
    eqs = "rw [← pk_eq, ← bi_eq, ← bl_eq, ← ow_eq, ← dl_eq]"
    nl_fwd = "rw [nl_eq]; " if ex == "PrintStr" else ""
    eqs_fwd = "rw [pk_eq, bi_eq, bl_eq, ow_eq, dl_eq" + (", nl_eq" if ex == "PrintStr" else "") + "]"
    out = []
    out.append("import Extracted\nimport PrintProofs.%s.Main%s\nimport PrintProofs.%s.Equiv\n" % (ISA, n, ISA))
    if isa == "arm64":
        out.append("open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Kernel Janus.Print\n")
    else:
        out.append("open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Kernel\n  Janus.Amd64.Kernel Janus.Print Janus.Amd64.Print\n")
    out.append(pre_doc.rstrip() + "\n")
    out.append("namespace Proof\n\nabbrev P := Extracted.program\n")
    out.append(("""/-- The code the proofs of `PrintProofs.%s.Fn*` and `Main%s` are about, `PrintCode.program`, has the
same code as `Extracted.program` (the segments in another order): the guarantees transport. -/
theorem equiv : {EQ}.Program.Equiv P PrintCode.program :=
  ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, rfl⟩
""" % (ISA, n)).replace("{EQ}", EQ))
    out.append(consts(isa))
    out.append("""
theorem pk_eq : PK = PrintFn.PK := by decide +kernel
theorem bi_eq : BI = PrintFn.BI := by decide +kernel
theorem bl_eq : BL = PrintFn.BL := by decide +kernel
theorem dl_eq : DL = PrintFn.DL := by decide +kernel
theorem ow_eq : OW = PrintFn.OW := by decide +kernel
theorem nl_eq : NL = PrintFn.NL := by decide +kernel
""")
    hyp = f"{PRN}Lock2Contract.of_equiv equiv impl rt 1024 hl) ({PRN}Unlock2Contract.of_equiv equiv impl rt 1024 hu) ({PRN}MemmoveContract.of_equiv equiv impl hmm)"
    out.append(f"\nset_option maxRecDepth 100000 in\n{fix(s_corr)}:= by\n  have h := {nsm}.correctness impl rt E ({hyp} {args}\n  refine {EK}.of_equiv equiv impl h (fun s k hp => ?_) (fun _ _ _ _ hq => hq)\n  {eqs}\n  exact {xfer_pre}\n")
    out.append("\n" + d_full + fix(s_full) + ":= by\n" + full_proof)
    out.append(f"""
namespace Witness

/-- The witness of `PrintProofs.{ISA}.FnWitness`, over this program: the code at its contract
addresses, its read-only data in the witness memory, the witness call state. -/
abbrev ret : Nat := PrintFn.Witness.ret

def implAt : List {SEG} :=
  PrintFn.Witness.implAtOf (P.contractAddr "runtime.lock2") (P.contractAddr "runtime.unlock2")
    (P.contractAddr "runtime.memmove")

def wmem : Memory := PrintFn.Witness.wmemOf OW BL P.data

def wstate (r : Nat → W64) : State := PrintFn.Witness.wstateMem wmem Extracted.entry r

theorem implAt_eq : implAt = PrintFn.Witness.implAt := rfl

theorem wmem_eq : wmem = PrintFn.Witness.wmem := by
  unfold wmem PrintFn.Witness.wmem; rw [ow_eq, bl_eq]; rfl

theorem wstate_eq (r : Nat → W64) : wstate r = PrintFn.Witness.wstate PrintCode.entryPrint{ex[5:]} r := by
  unfold wstate PrintFn.Witness.wstate; rw [wmem_eq]; rfl
""")
    nv_stmt = fix(s_nv)
    ret_stmt = fix(s_ret).replace("wstate Extracted.entry ", "wstate ").replace("(P.link implAt)", "(Extracted.program.link implAt)")
    out.append("\n" + d_nv + nv_stmt + f""":= by
  obtain ⟨impl, rt, ret, s, h1, h2, h3, h4, h5, hp⟩ := {nsm}.Witness.nonvacuous
  refine ⟨impl, rt, ret, s, {PRN}Lock2Contract.of_equiv equiv.symm impl rt 1024 h1, {PRN}Unlock2Contract.of_equiv equiv.symm impl rt 1024 h2,
    {PRN}MemmoveContract.of_equiv equiv.symm impl h3, equiv.symm.retAddr impl h4, ?_, ?_⟩
  · {nl_fwd}exact {SETUP}
  · {eqs_fwd}
    exact {xfer_pre.replace('equiv.dataLoaded', 'equiv.symm.dataLoaded').replace('of_equiv equiv ', 'of_equiv equiv.symm ')}
""")
    out.append("\n" + d_ret + ret_stmt + f""":= by
  rw [implAt_eq, wstate_eq]
  {('rw [nl_eq, wmem_eq]' if ex == 'PrintStr' else '')}
  exact (((equiv.sim PrintFn.Witness.implAt).withExit ret).symm).returnsK ({nsm}.Witness.returns E k)

end Witness

end Proof
""")
    txt = "\n".join(out)
    path = f"{base}/{ex}.lean"
    old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
    if old != txt:
        if check:
            print("stale: " + os.path.relpath(path, root) + " (run scripts/gen-print-examples.py " + isa + ")"); bad = 1
        else:
            open(path, "w", encoding="utf-8").write(txt); print("wrote", os.path.relpath(path, root))
sys.exit(bad)
