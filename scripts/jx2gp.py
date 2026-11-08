"""Gopanic / Goexit call-site state from the example's own frame (arm64 + amd64).
gp_defs(isa, kind, fiName, F, bo, so, resOff, lr, words, items, bitsval, tag='') -> (defs, conjunct, proof)
 words: list of (offset below wsp, value-expr); items: list of (offset below wsp, bits)."""
def gp_defs(isa, kind, fiName, F, bo, so, resOff, lr, words, items, bitsval, tag='', W=None):
    arm = isa=='arm64'
    W = W or ('0x48000' if arm else '0x4ff00')
    S='State' if arm else 'Janus.Amd64.State'
    FI='FuncInfo' if arm else 'Spec.FuncInfo'
    M='Memory' if arm else 'Janus.Arm64.Memory'
    sp = F if arm else F+8
    pre = 'GopanicPre' if kind=='gopanic' else 'GoexitPre'
    addr = 'runtime.gopanic' if kind=='gopanic' else 'runtime.Goexit'
    ws=''.join(f", ({W} - {o}, {v})" for o,v in words)
    ws=f"(({W} - {sp}), {lr})"+ws if not arm else ws[2:]
    if not arm: ws=ws  # amd: includes LR word at rsp
    bitsAt=f"{W} - {bo+1+0}" 
    # bits address = varp - bo ; varp = wsp - 8 (arm: S.sp+F-8 = wsp-8 ; amd fsp-8 = wsp-8)
    bAddr=f"{W} - {8+bo}"; sAddr=f"{W} - {8+so}"
    its=', '.join(f"{{ fn := {W} - {o}, bits := some {b}, chain := [] }}" for o,b in items)
    fr=f"⟨{W} - {F}, {W}, Extracted.entry + {resOff}, some ({bAddr}, {sAddr})⟩"
    if arm:
        regs=f"if i = 28 then BitVec.ofNat 64 0x50000 else if i = 30 then BitVec.ofNat 64 ({lr}) else if i = 29 then BitVec.ofNat 64 ({W} - {F} - 8) else if i = 0 then 1#64 else 0"
        st=f"{{ regs := fun i => {regs},\n    sp := BitVec.ofNat 64 ({W} - {F}), pc := BitVec.ofNat 64 (Extracted.program.contractAddr \"{addr}\"),\n    flags := ⟨false, false, false, false⟩, mem := wmG{tag} }}"
        find=f"{FI}.find T0 (wsG{tag}.regs 30).toNat = some wfi"
        findc=f"{FI}.find Extracted.funcs (s_c.regs 30).toNat = some fi"
        pcc="s_c.pc"; fsp=f"wsG{tag}.sp.toNat"; fspn=f"{W} - {F}"
        ppre="⟨env_G{t}, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩".replace('{t}',tag)
        npre = 'by decide, ' if kind=='gopanic' else ''
    else:
        regs=f"if i = 4 then BitVec.ofNat 64 ({W} - {F+8}) else if i = 14 then BitVec.ofNat 64 0x50000 else if i = 0 then 1#64 else 0"
        st=f"{{ regs := fun i => {regs},\n    rip := BitVec.ofNat 64 (Extracted.program.contractAddr \"{addr}\"), flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := wmG{tag} }}"
        find=f"Spec.FuncInfo.find T0 (wsG{tag}.mem.readLE (wsG{tag}.regs 4).toNat 8) = some wfi"
        findc=f"Spec.FuncInfo.find Extracted.funcs (s_c.mem.readLE (s_c.regs 4).toNat 8) = some fi"
        pcc="s_c.rip"; fsp=f"fspOf wsG{tag}"; fspn=f"{W} - {F}"
        ppre=f"⟨env_G{tag}, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, rfl, rfl, by decide, ?_⟩"
        npre = 'by decide, ' if kind=='gopanic' else ''
    # the pre-conjunct: Gopanic: PanicPre, regs0≠0, room, open, FrameOK ; Goexit: PanicPre, room, open, FrameOK
    framef = 'frameOf' 
    pframeof = 'frameOf' if arm else 'Panic.frameOf'
    unf_fok = 'Panic.FrameOK' if arm else 'FrameOK Panic.FrameOK'
    d=f"""def wfi{tag} : {FI} := {FI}.named Extracted.funcs "{fiName}"

/-- The call state at `{addr}`'s entry: `{fiName.split('.')[-1]}`'s own frame, pending open-coded defers in place, `LR` inside the function. -/
def wmG{tag} : {M} := witMem (tabWords T0 ++ [{ws}])

def wsG{tag} : {S} :=
  {st}

theorem env_G{tag} : Env0 T0 wmG{tag} := by
  unfold Env0
  have hnd : ndef wmG{tag} = 0 := by decide
  refine ⟨by decide, by decide, by decide, fun i hi => ?_, ?_⟩
  · omega
  · unfold TableOK
    exact ⟨by decide, by decide, by decide⟩

theorem wsG_find{tag} : {find} := by decide

theorem defers_G{tag} : defers0 wmG{tag} = [] := by
  have hnd : ndef wmG{tag} = 0 := by decide
  rw [defers0_eq, hnd]; rfl

theorem wsG_pre{tag} : {pre} PW wfi{tag} wsG{tag} := by
  refine ⟨{ppre}, {npre}?_, ?_, ?_⟩
  · simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · show 0 < room0 wmG{tag}
    rw [room0_eq]; decide
  · intro _; refine ⟨by decide, ?_⟩
    simp only [P0_priv, outside_cons, outside_nil, and_true]; decide
  · have hs : {fsp} = {fspn} := by decide
    have hr : PW.defers wmG{tag} (gOf wsG{tag}) = [] := defers_G{tag}
    have f_frame : wfi{tag}.frame = {F} := by rfl
    have f_od : wfi{tag}.openDefer = some ({bo}, {so}) := by rfl
    have f_res : wfi{tag}.resume = Extracted.entry + {resOff} := by rfl
    have hbA : wfi{tag}.bitsAt ({fspn}) = {bAddr} := by
      unfold {FI}.bitsAt {FI}.varp; rw [f_frame, f_od]; try rfl
    have hsA : wfi{tag}.slotsAt ({fspn}) = {sAddr} := by
      unfold {FI}.slotsAt {FI}.varp; rw [f_frame, f_od]; try rfl
    have hbd : wfi{tag}.bound ({fspn}) = {W} := by
      unfold {FI}.bound; rw [f_frame]; try rfl
    have hbit : wmG{tag}.readLE ({bAddr}) 1 = {bitsval} := by decide
    have hF : {pframeof} wfi{tag} ({fspn}) wmG{tag} = {fr} := by
      unfold {pframeof}; rw [hbA, hsA, hbd, f_res, f_od]
      simp only [hbit]; try rfl
    show FrameOK PW wmG{tag} (frameOf wfi{tag} ({fsp}) wmG{tag}) (frameItems wmG{tag} (frameOf wfi{tag} ({fsp}) wmG{tag}) (PW.defers wmG{tag} (gOf wsG{tag})))
    rw [hs, hr]
    {'' if arm else 'unfold frameOf'}
    rw [hF]
    have hI : frameItems wmG{tag} {fr} [] = [{its}] := by
      unfold frameItems openItems recItems
      simp only [hbit]
      decide
    unfold {unf_fok}
    rw [hI]
    simp only [hbit, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, P0_priv, outside_cons,
      outside_nil, and_true]
    decide
"""
    # for goexit the premise order differs in the proof: handled below
    conj=f"(∃ (s_c : {S}) (fi : {FI}), {pcc} = BitVec.ofNat 64 (Extracted.program.contractAddr \"{addr}\") ∧\n      {findc} ∧ {pre} P fi s_c)"
    return d, conj, f"⟨wsG{tag}, wfi{tag}, rfl, wsG_find{tag}, wsG_pre{tag}⟩"
