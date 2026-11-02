import FV.E2E.SemanticPipelineCheckWith
import FV.E2E.PreparedPipeline
import FV.E2E.LinkReturnPinContract

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver Clif Opt
set_option autoImplicit false
set_option Elab.async false

structure SemanticPreparedFactsFor (extra : Clif.Function → VCode → Bool) (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) (g : Clif.Function) (a : Art) : Prop where
  pipe : prepare (stage g a.vc) = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
    emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
    a.base = BitVec.ofNat 64 (I.baseOf g.name)
  lowerOk : (SemanticNI.check g a.vc || extra g a.vc) = true
  prepOk : prepCheck (stage g a.vc) a.vcp = true
  check : checkAlloc a.vcp a.rf = .ok ()
  covered : FormsCovered ⟨a.fa.k, a.af.slotBase⟩
    a.vcp
  rets : allInsts a.vc (retsB g) = true
  outFits : ∀ e ∈ g.externs, ((progOf R).func? e.2.name).isSome = true →
    outFitsB e.2.sig (RAFrame.compute a.vcp a.rf).intBase = true
  nodup : (regLocs g.sig).Nodup
  argReg : ∀ r ∈ regLocs g.sig, r.isArgReg = true
  width : ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  callee : calleeB (progOf R) (fun n => I.syms.lookup n) g = true → (g.slots = [] →
    (RAFrame.compute a.vcp a.rf).size =
      a.af.frameSize - clobberBytes a.af.saves) ∧ slotFitsB g a = true
  sites : allInsts a.vcp (siteB (siteOk (progOf R) g
    (indToB (fun n => I.syms.lookup n) g) a.vcp)) = true
  declSig : ∀ e ∈ g.externs.map (·.2), ∀ h, (progOf R).func? e.name = some h → e.sig = h.sig
  entry : entryB g a.vcp = true
  fits : a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64
  ra : raCallB (tabOf R) g a = true
  depth : frameDrop a.af ≤ I.D
  free : Clif.LinkFree g
  subsetE : Compile.functionE g = true
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  indOk : indSigsOk g = true
  ind : indB (progOf R) (fun n => I.syms.lookup n) g = true

theorem semanticPreparedFactsFor (extra : Clif.Function → VCode → Bool) (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (hR : PreparedResults stage I R) (h : okRSemanticFor extra stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) : SemanticPreparedFactsFor extra stage I R g (artOf R g) := by
  have hn := okRSemanticFor_names extra stage h
  obtain ⟨e, he, rfl, hart⟩ := artOf_spec hn hg
  have hall : ∀ c ∈ chksSemanticFor extra stage I (progOf R) (tabOf R) e.1 e.2, c.2 = true := by
    simp only [okRSemanticFor, chksSemanticFor, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 e he
  rw [hart]
  simp only [chksSemanticFor, staticChksSemanticFor_expanded, linkChks, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hall
  obtain ⟨h1, h2, h3, h4, h5, h7, h9, h10, h11, h15, h16, h18, h19, h20, h22, h23, h8,
    h12, h13, h14, h17, h24⟩ := hall
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h8 h9 h10 h11 h12 h14 h16 h18 h22
  refine ⟨hR e he _ (getOk_eq h1), h2, h3, toBool_unit h4,
    (formsCoveredB_iff _ _).1 h5, h7, fun x hx hs => ?_, h9, h10, h11, fun hc => ?_, h13,
    fun x hx h' hf => ?_, h15, h16, h17, h18, linkFreeB_sound h19, h20,
    ⟨h22.1, h22.2⟩, h23, h24⟩
  · rcases h8 x hx with h | h
    · simp [hs] at h
    · exact h
  · rcases h12 with h | ⟨h', hfit⟩
    · simp [hc] at h
    · refine ⟨fun hs => ?_, hfit⟩
      rcases h' with h | h
      · simp [hs] at h
      · exact h
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 hx
    have := h14 _ hm
    simp only [hf, decide_eq_true_eq] at this
    exact this

theorem semanticPreparedIndFactsFor (extra : Clif.Function → VCode → Bool) (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (hR : PreparedResults stage I R) (h : okRSemanticFor extra stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) (hnf : ¬ Clif.IndFree g) :
    ∀ h ∈ (progOf R).funcs, mayB (fun n => I.syms.lookup n) g h.name = true →
      ((∃ sig ∈ indSigs g, LinkSys.IndSigMatch sig h) ∨
        (DeclN g h.name ∧ ∃ sig ∈ indSigs g, LinkSys.IndTyMatch sig h)) →
      (∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
      ∀ sig ∈ indSigs g, LinkSys.IndTyMatch sig h → h.sig.returns.length = sig.returns.length →
        (sigRets h.sig).length = (sigRets sig).length := by
  have h := (semanticPreparedFactsFor extra stage hR h hg).ind
  simp only [indB, Bool.or_eq_true, List.all_eq_true] at h
  rcases h with h | h2
  · exact absurd (indFreeB_sound h) hnf
  intro h' hh hd hm
  have hany : indSigB g h' = true := by
    simp only [indSigB, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
    rcases hm with ⟨sig, hs, hm⟩ | ⟨hdn, sig, hs, hm⟩
    · exact .inl ⟨sig, hs, hm⟩
    · exact .inr ⟨declB_of hdn, sig, hs, hm⟩
  have h2' := h2 h' hh
  simp only [Bool.and_eq_true] at h2'
  rw [hd, hany] at h2'
  rcases h2' with (e | e) | ⟨hb8, hr⟩
  · cases e
  · cases e
  refine ⟨?_, indRetsB_sound hr⟩
  revert hb8
  cases hb : sigParamBytes h'.sig <;> simp


structure SemanticPreparedMetadata (L : LinkSys) : Prop where
  /-- distinct names, no `return_call` -/
  names : (L.P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ L.P.funcs, Clif.LinkFree g
  subset : ∀ g ∈ L.P.funcs, InSubset L.P.bare g
  covered : ∀ g ∈ L.P.funcs, FormsCovered ⟨(L.A g).fa.k, (L.A g).af.slotBase⟩ (L.A g).vcp
  /-- scope: the outgoing-argument area of a function holds the stack-passed arguments of the
  functions of `P` it declares (checked per declaration; vacuous for register-only signatures) -/
  outFits : ∀ g ∈ L.P.funcs, ∀ e ∈ g.externs.map (·.2), (L.P.func? e.name).isSome →
    ∀ (i off : Nat) (p : Clif.AbiParam), (locsOf e.sig)[i]? = some (ArgLoc.stack off) →
      e.sig.params[i]? = some p →
      off + p.ty.bytes ≤ (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase
  /-- the base externs create no allocation (needed only when a function of `P` has an
  outgoing-argument area: the callees' runs keep it free of live CLIF bytes) -/
  baseNoAlloc : (∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    NoAllocEnv L.base
  argRegs : ∀ g ∈ L.P.funcs, (regLocs g.sig).Nodup ∧ (∀ r ∈ regLocs g.sig, r.isArgReg = true) ∧
    ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  /-- an `sret` function's returns carry its ABI results (the struct pointer: `lowerFunction`
  appends it to every `return`), checked on the compiled code -/
  sretRets : ∀ g ∈ L.P.funcs, g.sig.params.any (·.purpose == .sret) = true → ∀ us,
    (L.A g).vc.RetsSite us → (sigRets g.sig).length ≤ us.length
  /-- layout: a function called from `P` without stack slots has no slot region, and the slots
  of one with stack slots fit in its slot region (checked per function; the slot layout of
  `lowerFunction`) -/
  calleeFrame : ∀ g ∈ L.P.funcs, ∀ h, L.Callee g h → h.slots = [] →
    (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves
  slotFits : ∀ g ∈ L.P.funcs, ∀ h, L.Callee g h → ∀ p ∈ h.slots, ∃ off,
    (slotLayout h.slots).1.lookup p.1 = some off ∧
      (L.A h).af.slotBase + off + p.2.size ≤ (L.A h).af.frameSize - clobberBytes (L.A h).af.saves
  /-- scope: a call of a function `h` of `P` passes integer arguments in `h`'s parameter
  registers and takes its results from x0.. (those of its defs that are results: the defs past
  them are a `try_call`'s exception payload registers; checked per call site) -/
  callRegs : ∀ g ∈ L.P.funcs, ∀ info h, L.ProgSite g info h →
    ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h.sig ∧
      (Ld.map (·.1)).take (sigRets h.sig).length =
        (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x
  /-- scope: a `blr` call site (an indirect call, or a call through the GOT) passes integer
  arguments in the parameter registers of every function of `P` it may enter (`BlrTo`: one its
  function may reach, `MayCall`; at a call through the GOT only the GOT symbol's function, none
  for a base extern) that has as many register parameters, and takes the results its defs hold
  from x0.. (a site with fewer defs than that function's results constrains nothing more; checked
  per site; vacuous without `blr` sites) -/
  blrRegs : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → (∀ n, info.dest ≠ .sym n) →
    ∃ t Lu Ld, info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      ∀ h ∈ L.P.funcs, L.BlrTo g t h → (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x
  /-- layout: the return address of a `blr` is not in the code of a function of `P` it may call
  (`MayCall`), or is after a call instruction of that function's code, not at its entry
  (`RaOk`: functions sharing one copy of code) -/
  raBlr : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → (∀ n, info.dest ≠ .sym n) →
    ∀ h ∈ L.P.funcs, L.MayCall g h.name → ∀ pc, CallPc (L.A g).fa (L.A g).base pc →
      RaOk (L.A h) pc
  /-- scope of the indirect calls (`call_indirect`, `try_call_indirect`; vacuous without them):
  the base externs keep the symbols and distinct names of `P` and of the base environment have
  distinct addresses (`Clif.IndScope`) -/
  indScope : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g → Clif.IndScope L.P L.base L.syms
  /-- the functions `g` may reach whose signature one of its indirect calls matches
  (`LinkSys.IndSigMatch`: parameter types and purposes, return types; the whole-program run enters no
  other, `Clif.stepCallIndirect`), or, for a function `g` declares (which the per-function run
  may enter through any pointer to it), whose parameter types one of them has (`LinkSys.IndTyMatch`),
  take their arguments in registers (an `sret` pointer in x8), and an indirect call of `g` with
  their parameter types and as many declared returns has as many ABI returns (`sigRets`: both
  or neither pass an `sret` pointer) -/
  indSig : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g →
    ∀ h ∈ L.P.funcs, L.MayCall g h.name → ((∃ sig ∈ indSigs g, LinkSys.IndSigMatch sig h) ∨
      (DeclN g h.name ∧ ∃ sig ∈ indSigs g, LinkSys.IndTyMatch sig h)) →
      (∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
      ∀ sig ∈ indSigs g, LinkSys.IndTyMatch sig h → h.sig.returns.length = sig.returns.length →
        (sigRets h.sig).length = (sigRets sig).length
  /-- when no program callee has stack slots (`NeedSlots` fails: the slot-placement oracle is
  not in play), a function of `P` has an outgoing-argument area and one has indirect calls, the
  functions with an address have no stack slots (an indirect call enters no slotted function);
  with `NeedSlots` the runs' allocations are the base's to keep (`baseKeepsAllocs`) -/
  addrSlots : ¬ L.NeedSlots → (∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    (∃ g ∈ L.P.funcs, ¬ Clif.IndFree g) → ∀ h ∈ L.P.funcs, L.syms h.name ≠ none → h.slots = []
  /-- the link-time address of a function of `P` is no other symbol's -/
  symInj : ∀ h ∈ L.P.funcs, ∀ n, L.Xb.sym h.name 0 = L.Xb.sym n 0 → n = h.name
  /-- the declarations of the program's functions are their definitions' signatures -/
  declSig : ∀ g ∈ L.P.funcs, ∀ e ∈ g.externs.map (·.2), ∀ h, L.P.func? e.name = some h → e.sig = h.sig
  /-- the entry `Args` reads parameter registers -/
  entryRegs : ∀ g ∈ L.P.funcs, ∀ r, (L.A g).vcp.EntryArg r → r ∈ regLocs g.sig
  /-- layout: every function's words fit at its base -/
  fits : ∀ g ∈ L.P.funcs, (L.A g).base.toNat + 4 * (L.A g).fb.words.size ≤ 2 ^ 64
  /-- layout: the code image (`Img`, holding `imgMem`) contains every function's words -/
  imgAddr : ∀ g ∈ L.P.funcs, ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default
    ((L.A g).fb.program (L.A g).base)) a → L.Img a
  imgCode : ∀ g ∈ L.P.funcs, ∀ t : Arm.ArmState, (∀ a, L.Img a → t.mem a = L.imgMem a) →
    ∀ k w, (L.A g).fb.words[k]? = some w →
      Arm.read_mem_bytes 4 ((L.A g).base + BitVec.ofNat 64 (4 * k)) t = w
  /-- the code is outside every activation's world -/
  imgF : ∀ a, L.Img a → L.F a
  /-- layout: the return address of a call is not in the code of a function of `P` that `g`
  calls, or is after a call instruction of that function's code, not at its entry (`RaOk`;
  stated for the callees of `g`'s call sites, not for every function of `P`: the return address
  is in `g`'s own code, so a native recursive callee or a callee sharing `g`'s code
  takes the second case) -/
  raCall : ∀ g ∈ L.P.funcs, ∀ info h, L.ProgSite g info h → ∀ pc, CallPc (L.A g).fa (L.A g).base pc →
    RaOk (L.A h) pc
  raStar : ∀ h ∈ L.P.funcs, ∀ k < (L.A h).fb.words.size,
    L.raStar ≠ (L.A h).base + BitVec.ofNat 64 (4 * k)
  /-- the stack of one call level -/
  depth : ∀ g ∈ L.P.funcs, frameDrop (L.A g).af ≤ L.D
  /-- the base environment: symbols, the contracts of the calls outside `P` (at the program's
  call sites), the CLIF contract of the base externs, TLS -/
  symOk : ∀ n b, L.syms n = some b → L.Xb.sym n 0 = BitVec.ofNat 64 b
  baseOs : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → L.BaseDest (destOf info) →
    ∀ F K G s0 Pc ctx, CallSoundCtlG F K G s0 Pc (callExec L.Hb) (csem F ctx L.Xb) (.call info) .next
  basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (L.Hb.call d s) = Arm.r .PC s + 4
  baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs, w') →
    Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program
  baseX : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XCallsOk L.base
    ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  /-- the indirect calls of `g` that reach an extern outside `P`, whatever the call-site
  signature (`sigOf` erased: the linked environment knows only the signatures of `P`'s
  functions, `Clif.linkEnvN`; vacuous without indirect calls) -/
  baseXI : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XCallsIndOk { L.base with sigOf := fun _ => none }
    (indSigs g) (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  baseTls : ∀ g ∈ L.P.funcs, hasTls g = true → ∀ F K, TlsOk F K L.Xb L.Hb
  /-- the results of a `try_call` of an extern outside `P` (normal return; vacuous without such
  `try_call`s) -/
  baseTry : ∀ g ∈ L.P.funcs, ∀ F, CalleeTryOk F L.Xb L.Hb
    fun info ti => (L.A g).vcp.TrySite info ti ∧ L.BaseDest (destOf info)
  /-- **non-interference of the base externs** (needed only when a program callee has an
  outgoing-argument area or a slot region): a returning call of an extern outside `P`, pinned to
  its CLIF call, from two worlds that agree outside `Z ⊇ F`, related to the same CLIF memory, with
  the same stack pointer and the same argument bytes, gives the same results and worlds that agree
  outside `Z` -/
  baseNI : L.NeedNI → ∀ g ∈ L.P.funcs, ∀ F c, XNI F L.syms (g.externs.map (·.2)) (indSigs g) c
    (fun n sig vals cm => L.P.func? n = none ∧
      CallLg L.base (g.externs.map (·.2)) (indSigs g) n sig vals cm) L.Xb
  /-- the TLSDESC flags do not depend on the world outside `F` (needed only when a program
  callee has an outgoing-argument area) -/
  baseTlsNI : L.NeedNI → ∀ F, XTls F L.Xb
  /-- the base externs keep the slot-placement oracle and create no allocation (needed only when
  a program callee has stack slots) -/
  baseKeepsPlace : L.NeedSlots → Clif.EnvKeepsPlace L.base
  baseKeepsAllocs : L.NeedSlots → Clif.EnvKeepsAllocs L.base

theorem semanticPreparedMetadata_sound (extra : Clif.Function → VCode → Bool) (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (hR : PreparedResults stage I R) (hI : okRSemanticFor extra stage I R = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (ofRes I R B F)) (hF : ∀ a, (ofRes I R B F).Img a → F a) :
    SemanticPreparedMetadata (ofRes I R B F) := by
  have hn := okRSemanticFor_names extra stage hI
  have hgl := okRSemanticFor_global extra stage hI
  simp only [globalChks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hgl
  obtain ⟨-, himg, hstar, hinj, hsymok, haddr⟩ := hgl
  have fa := fun {g} (hg : g ∈ (progOf R).funcs) => semanticPreparedFactsFor extra stage hR hI hg
  have site : ∀ g ∈ (progOf R).funcs, ∀ info h,
      (ofRes I R B F).ProgSite g info h →
      h ∈ (progOf R).funcs ∧
        calleeB (progOf R) (fun n => I.syms.lookup n) h = true ∧
        ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x := by
    intro g hg info h ⟨hs, n, hd, hf⟩
    have hf' : (progOf R).func? n = some h := hf
    obtain ⟨⟨e, he, hen⟩, Lu, Ld, heq, h1, h2⟩ :=
      siteOk_sound (site_sound (fa hg).sites hs) hd hf'
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hf'
    refine ⟨hh, ?_, n, Lu, Ld, heq, h1, h2⟩
    simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact .inl ⟨g, hg, e, he, by rw [hen, hname]⟩
  have hcal : ∀ g ∈ (progOf R).funcs, ∀ h, (ofRes I R B F).Callee g h →
      (h.slots = [] → (RAFrame.compute (artOf R h).vcp (artOf R h).rf).size =
        (artOf R h).af.frameSize - clobberBytes (artOf R h).af.saves) ∧ slotFitsB h (artOf R h) = true := by
    intro g hg h hh
    have hc : calleeB (progOf R) (fun n => I.syms.lookup n) h = true ∧
        h ∈ (progOf R).funcs := by
      rcases hh with ⟨info, hs⟩ | ⟨e, he, hf⟩ | ⟨hh', hmay⟩
      · obtain ⟨hh', hc, -⟩ := site g hg info h hs
        exact ⟨hc, hh'⟩
      · obtain ⟨hh', hname⟩ := Clif.Program.func?_some (p := progOf R) hf
        refine ⟨?_, hh'⟩
        obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
        simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
        exact .inl ⟨g, hg, (fn, e'), hm, hname.symm⟩
      · refine ⟨?_, hh'⟩
        simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true,
          Bool.not_eq_true']
        rcases hmay with hm | ⟨hnf, hs, -⟩
        · obtain ⟨⟨fn, e'⟩, he, hen⟩ := List.mem_map.1 hm
          exact .inl ⟨g, hg, (fn, e'), he, hen⟩
        · refine .inr ⟨?_, g, hg, indFreeB_false hnf⟩
          show (I.syms.lookup h.name).isSome = true
          cases h' : I.syms.lookup h.name
          · exact absurd h' hs
          · rfl
    exact (fa hc.2).callee hc.1
  refine
    { names := hn
      free := fun g hg => (fa hg).free
      subset := fun g hg => ⟨(fa hg).subsetE, ?_, ?_, (fa hg).abi, ?_⟩
      covered := fun g hg => (fa hg).covered
      outFits := fun g hg e he hs i off p hl hp => ?_
      baseNoAlloc := hB.baseNoAlloc
      argRegs := fun g hg => ⟨(fa hg).nodup, (fa hg).argReg, (fa hg).width⟩
      sretRets := fun g hg hs us hr => retsB_sound (fa hg).rets hs hr
      calleeFrame := fun g hg h hh hs => (hcal g hg h hh).1 hs
      slotFits := fun g hg h hh => slotFitsB_sound (hcal g hg h hh).2
      callRegs := fun g hg info h hs => (site g hg info h hs).2.2
      blrRegs := fun g hg info hs hreg => by
        obtain ⟨t, Lu, Ld, heq, hall⟩ := blrOk_sound (siteOk_reg (site_sound (fa hg).sites hs) hreg)
        exact ⟨t, Lu, Ld, heq, fun h hh hb hl =>
          hall h hh (indToB_of hb.1) (fun n hn => (hb.2 n (gotOf_sound hn)).symm) hl⟩
      raBlr := fun g hg info hs hreg h hh hmay pc hpc => by
        by_cases hhg : h.name = g.name
        · rw [Clif.name_inj hn hh hg hhg]
          exact raOk_self (fa hg).pipe.2.2.2.1 (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
        · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
      indScope := fun g hg hnf => ⟨hB.keepSyms ⟨g, hg, hnf⟩, ?_, hB.aliasSyms ⟨g, hg, hnf⟩⟩
      indSig := fun g hg hnf h hh hmay hm => semanticPreparedIndFactsFor extra stage hR hI hg hnf h hh (mayB_of hmay) hm
      addrSlots := fun hN ⟨g, hg, hout⟩ ⟨g', hg', hind⟩ h hh hs => ?_
      symInj := fun h hh n hn => ?_
      declSig := fun g hg e he h hf => (fa hg).declSig e he h hf
      entryRegs := fun g hg r hr => entryB_sound (fa hg).entry hr
      fits := fun g hg => (fa hg).fits
      imgAddr := fun g hg a ha => ⟨_, tab_mem hn hg, ha⟩
      imgCode := fun g hg t ht k w hw => imgCode_of himg (tab_mem hn hg) t ht k w hw
      imgF := hF
      raCall := fun g hg info h hs pc hpc => ?_
      raStar := fun h hh k hk => ?_
      depth := fun g hg => (fa hg).depth
      symOk := fun n b hn' => ?_
      baseOs := hB.baseOs
      basePc := hB.basePc
      baseExt := hB.baseExt
      baseX := hB.baseX
      baseXI := hB.baseXI
      baseTls := hB.baseTls
      baseTry := hB.baseTry
      baseNI := hB.baseNI
      baseTlsNI := hB.baseTlsNI
      baseKeepsPlace := hB.baseKeepsPlace
      baseKeepsAllocs := hB.baseKeepsAllocs }
  · intro b _ st _ fn args _ e he
    exact Clif.Program.bare_func? _ _
  · intro b _ fn args et _ e he
    exact Clif.Program.bare_func? _ _
  · intro sig hs
    have := List.all_eq_true.mp (fa hg).indOk sig hs
    simpa [Bool.and_eq_true, decide_eq_true_eq] using this
  · obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
    exact outFitsB_sound ((fa hg).outFits _ hm hs) hl hp
  · -- the functions of `P` have distinct addresses: their link-map addresses (`symOk`), which
    -- no other link-map entry has (`symInj`)
    intro a ha b hb x hxa hxb
    obtain ⟨g', -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨h', hh', rfl⟩ := List.mem_map.1 hb
    simp only [symOkB, List.all_eq_true, beq_iff_eq] at hsymok
    have ea : I.addrOf g'.name = x := hsymok _ (lookup_pair hxa)
    have eb : I.addrOf h'.name = x := hsymok _ (lookup_pair hxb)
    simp only [symInjB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
      ne_eq, Bool.or_eq_true, beq_iff_eq] at hinj
    obtain ⟨⟨hlt, h0⟩, hall⟩ := hinj h' hh'
    rcases addrOf_cases I g'.name with hz | hm
    · exact absurd (eb.trans (ea.symm.trans hz)) h0
    · rcases hall _ hm with e | e
      · exact e
      · exact absurd (by rw [ea, ← eb, Nat.mod_eq_of_lt hlt]) e
  · simp only [addrSlotsB, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      List.any_eq_false, List.all_eq_true, Bool.not_eq_true, bne_iff_ne, ne_eq,
      Decidable.not_not, Bool.or_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at haddr
    rcases haddr with ((h1 | h1) | h1) | h1
    · exact absurd (h1 _ (tab_mem hn hg)) hout
    · exact absurd (indFreeB_sound (by simpa using h1 g' hg')) hind
    · exact (h1 h hh).resolve_left hs
    · obtain ⟨g0, hg0, e, he, h0, hf, hs0⟩ := declSlotsB_sound h1
      exact absurd ⟨g0, hg0, h0, .inr (.inl ⟨e, he, hf⟩), hs0⟩ hN
  · simp only [symInjB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
      ne_eq, Bool.or_eq_true, beq_iff_eq] at hinj
    obtain ⟨⟨hlt, h0⟩, hall⟩ := hinj h hh
    have hn' : I.symAddr h.name 0 = I.symAddr n 0 := hn
    rw [symAddr_zero, symAddr_zero] at hn'
    have e1 : (I.addrOf h.name) = (I.addrOf n) % 2 ^ 64 := by
      have := congrArg BitVec.toNat hn'
      simpa [Nat.mod_eq_of_lt hlt] using this
    by_cases hne : n = h.name
    · exact hne
    exfalso
    rcases addrOf_cases I n with hz | hm
    · rw [hz] at e1; exact h0 (by simpa using e1)
    · rcases hall _ hm with h' | h'
      · exact hne h'
      · exact h' e1.symm
  · obtain ⟨hh, -⟩ := site g hg info h hs
    by_cases hhg : h.name = g.name
    · rw [Clif.name_inj hn hh hg hhg]
      exact raOk_self (fa hg).pipe.2.2.2.1 (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
    · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
  · simp only [raStarB, List.all_eq_true] at hstar
    exact outside_sound (hstar _ (tab_mem hn hh)) k hk
  · simp only [symOkB, List.all_eq_true, beq_iff_eq] at hsymok
    have := hsymok _ (lookup_pair hn')
    show I.symAddr n 0 = _
    rw [symAddr_zero, this]

theorem SemanticPreparedMetadata.toSemanticNI {L : LinkSys} (facts : SemanticPreparedMetadata L)
    (compiled : ∀ g ∈ L.P.funcs,CompiledSemanticNI g (L.A g).k (L.A g).vc (L.A g).vcp (L.A g).rf
      (L.A g).af (L.A g).fa (L.A g).fb) : L.OkSemanticNI where
  names := facts.names
  free := facts.free
  subset := facts.subset
  covered := facts.covered
  outFits := facts.outFits
  baseNoAlloc := facts.baseNoAlloc
  argRegs := facts.argRegs
  sretRets := facts.sretRets
  calleeFrame := facts.calleeFrame
  slotFits := facts.slotFits
  callRegs := facts.callRegs
  blrRegs := facts.blrRegs
  raBlr := facts.raBlr
  indScope := facts.indScope
  indSig := facts.indSig
  addrSlots := facts.addrSlots
  symInj := facts.symInj
  declSig := facts.declSig
  entryRegs := facts.entryRegs
  fits := facts.fits
  imgAddr := facts.imgAddr
  imgCode := facts.imgCode
  imgF := facts.imgF
  raCall := facts.raCall
  raStar := facts.raStar
  depth := facts.depth
  symOk := facts.symOk
  baseOs := facts.baseOs
  basePc := facts.basePc
  baseExt := facts.baseExt
  baseX := facts.baseX
  baseXI := facts.baseXI
  baseTls := facts.baseTls
  baseTry := facts.baseTry
  baseNI := facts.baseNI
  baseTlsNI := facts.baseTlsNI
  baseKeepsPlace := facts.baseKeepsPlace
  baseKeepsAllocs := facts.baseKeepsAllocs
  compiled := compiled

theorem SemanticPreparedMetadata.toReturnPins {L : LinkSys} {modes : Clif.Function → ReturnPinMode} (facts : SemanticPreparedMetadata L)
    (compiled : ∀ g ∈ L.P.funcs,CompiledProgramReturnPins L g modes) : L.OkReturnPins modes where
  names := facts.names
  free := facts.free
  subset := facts.subset
  covered := facts.covered
  outFits := facts.outFits
  baseNoAlloc := facts.baseNoAlloc
  argRegs := facts.argRegs
  sretRets := facts.sretRets
  calleeFrame := facts.calleeFrame
  slotFits := facts.slotFits
  callRegs := facts.callRegs
  blrRegs := facts.blrRegs
  raBlr := facts.raBlr
  indScope := facts.indScope
  indSig := facts.indSig
  addrSlots := facts.addrSlots
  symInj := facts.symInj
  declSig := facts.declSig
  entryRegs := facts.entryRegs
  fits := facts.fits
  imgAddr := facts.imgAddr
  imgCode := facts.imgCode
  imgF := facts.imgF
  raCall := facts.raCall
  raStar := facts.raStar
  depth := facts.depth
  symOk := facts.symOk
  baseOs := facts.baseOs
  basePc := facts.basePc
  baseExt := facts.baseExt
  baseX := facts.baseX
  baseXI := facts.baseXI
  baseTls := facts.baseTls
  baseTry := facts.baseTry
  baseNI := facts.baseNI
  baseTlsNI := facts.baseTlsNI
  baseKeepsPlace := facts.baseKeepsPlace
  baseKeepsAllocs := facts.baseKeepsAllocs
  compiled := compiled

end E2E.LinkCheck
