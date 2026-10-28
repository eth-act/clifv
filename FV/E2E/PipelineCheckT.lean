import FV.E2E.PipelineCheck
import FV.E2E.LinkCheckT
import FV.E2E.LinkArmT
import FV.E2E.LinkSiteTC

/-! # Typed copies of `FV.E2E.PipelineCheck` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.PipelineCheck` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`).

S11f (#35): the lowering check of `staticChksWithT` (and `FactsWithT.lowerOk`) admits, outside
the typed movement scope, the scope with the proven float operations (`Compile.functionETCF`
with `lowerCheckTCF`; it was `Compile.functionETC` with `lowerCheckTC`, which it contains:
`Compile.functionETCF_of_functionETC`, `lowerCheckTCF_of_lowerCheckTC`). The compiled code is
unchanged; `okRWith_soundT`'s statement is unchanged. -/

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

def staticChksWithT (stage : Clif.Function → VCode → VCode) (I : LinkInput) (g : Clif.Function) (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  [("compiled: pipeline", r.toBool),
  ("compiled: lowerCheckT/TCF",
    (Compile.functionET g && lowerCheckT g a.vc) || (Compile.functionETCF g && lowerCheckTCF g a.vc)),
  ("compiled: prepCheck", prepCheck (stage g a.vc) a.vcp),
   ("compiled: checkAlloc", (checkAlloc a.vcp a.rf).toBool),
   ("covered", formsCoveredB ⟨a.fa.k, a.af.slotBase⟩ a.vcp),
   ("sretRets", allInsts a.vc (retsB g)),
   ("argRegs: distinct", decide (regLocs g.sig).Nodup),
   ("argRegs: argument registers", (regLocs g.sig).all (·.isArgReg)),
   ("argRegs: width ≤ 64", g.sig.params.all (fun p => decide (p.ty.width ≤ 64))),
   ("entryRegs", entryB g a.vcp),
   ("fits", decide (a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64)),
   ("depth", decide (frameDrop a.af ≤ I.D)),
   ("free (no return_call)", linkFreeB g),
   ("subset: storeTyped", Compile.storeTypedB g),
   ("subset: ABI signatures", sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)),
   ("subset: indirect-call signatures", indSigsOk g),
   ("sret: subset E, lowerCheck", !(g.sig.params.any (·.purpose == .sret)) ||
     (Compile.functionE g && lowerCheck g a.vc))]

def chksWithT (stage : Clif.Function → VCode → VCode) (I : LinkInput) (P : Clif.Program)
    (T : List (Clif.Function × Art)) (g : Clif.Function) (r : Except String Art) :
    List (String × Bool) := staticChksWithT stage I g r ++ linkChksT I P T g r ++ [("calleeInt", calleeIntChk I P g)]

def okRWithT (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  (globalChks I (progOf R) (tabOf R)).all (·.2) &&
    R.all fun e => (chksWithT stage I (progOf R) (tabOf R) e.1 e.2).all (·.2)

structure FactsWithT (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) (g : Clif.Function) (a : Art) : Prop where
  pipe : lowerFunction g = .ok a.vc ∧ prepare (stage g a.vc) = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
    emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
    a.base = BitVec.ofNat 64 (I.baseOf g.name)
  lowerOk : (Compile.functionET g = true ∧ lowerCheckT g a.vc = true) ∨
    (Compile.functionETCF g = true ∧ lowerCheckTCF g a.vc = true)
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
  sites : allInsts a.vcp (siteB (siteOkTC (progOf R) g
    (indToB (fun n => I.syms.lookup n) g) a.vcp)) = true
  declSig : ∀ e ∈ g.externs.map (·.2), ∀ h, (progOf R).func? e.name = some h → e.sig = h.sig
  entry : entryB g a.vcp = true
  fits : a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64
  ra : raCallB (tabOf R) g a = true
  depth : frameDrop a.af ≤ I.D
  free : Clif.LinkFree g
  storeT : Compile.storeTypedB g = true
  sretE : g.sig.params.any (·.purpose == .sret) = true →
    Compile.functionE g = true ∧ lowerCheck g a.vc = true
  calleeInt : calleeB (progOf R) (fun n => I.syms.lookup n) g = true →
    ∀ p ∈ g.sig.returns, p.ty.isInt = true
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  indOk : indSigsOk g = true
  ind : indB (progOf R) (fun n => I.syms.lookup n) g = true

theorem okRWith_globalT (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (h : okRWithT stage I R = true) :
    ∀ c ∈ globalChks I (progOf R) (tabOf R), c.2 = true := by
  simp only [okRWithT, chksWithT, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem okRWith_namesT (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (h : okRWithT stage I R = true) :
    ((progOf R).funcs.map (·.name)).Nodup := by
  have := okRWith_globalT stage h _ (by simp [globalChks]; exact Or.inl rfl)
  simpa using this

theorem factsRWithT (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (hR : ResOkWith stage I R)
    (h : okRWithT stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) : FactsWithT stage I R g (artOf R g) := by
  have hn := okRWith_namesT stage h
  obtain ⟨e, he, rfl, hart⟩ := artOf_spec hn hg
  have hall : ∀ c ∈ chksWithT stage I (progOf R) (tabOf R) e.1 e.2, c.2 = true := by
    simp only [okRWithT, chksWithT, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 e he
  rw [hart]
  simp only [chksWithT, staticChksWithT, linkChksT, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.append_assoc] at hall
  obtain ⟨h1, h2, h3, h4, h5, h7, h9, h10, h11, h15, h16, h18, h19, h20, h22, h23, hsr, h8,
    h12, h13, h14, h17, h24, hci⟩ := hall
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h8 h9 h10 h11 h12 h14 h16 h18 h20 h22 hsr
  simp only [calleeIntChk, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at hci
  refine ⟨hR e he _ (getOk_eq h1),
    (by rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
        rcases h2 with h | h
        · exact .inl ⟨h.1, h.2⟩
        · exact .inr ⟨h.1, h.2⟩),
    h3, toBool_unit h4,
    (formsCoveredB_iff _ _).1 h5, h7, fun x hx hs => ?_, h9, h10, h11, fun hc => ?_, h13,
    fun x hx h' hf => ?_, h15, h16, h17, h18, linkFreeB_sound h19, h20, fun hs => ?_,
    fun hc p hp => ?_, ⟨h22.1, h22.2⟩, h23, h24⟩
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
  · rcases hsr with h | h
    · rw [hs] at h; cases h
    · exact h
  · rcases hci with h | h
    · rw [hc] at h; cases h
    · exact h p hp

theorem indFactsRWithT (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res} (hR : ResOkWith stage I R) (h : okRWithT stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) (hnf : ¬ Clif.IndFree g) :
    ∀ h ∈ (progOf R).funcs, mayB (fun n => I.syms.lookup n) g h.name = true →
      ((∃ sig ∈ indSigs g, LinkSys.IndSigMatch sig h) ∨
        (DeclN g h.name ∧ ∃ sig ∈ indSigs g, LinkSys.IndTyMatch sig h)) →
      (∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
      ∀ sig ∈ indSigs g, LinkSys.IndTyMatch sig h → h.sig.returns.length = sig.returns.length →
        (sigRets h.sig).length = (sigRets sig).length := by
  have h := (factsRWithT stage hR h hg).ind
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

theorem okRWith_soundT (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (hstage : stage = (fun _ => id) ∨ stage = cleanupStage) (hR : ResOkWith stage I R)
    (hI : okRWithT stage I R = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (ofRes I R B F)) (hF : ∀ a, (ofRes I R B F).Img a → F a) :
    (ofRes I R B F).OkT := by
  have hn := okRWith_namesT stage hI
  have hgl := okRWith_globalT stage hI
  simp only [globalChks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hgl
  obtain ⟨-, himg, hstar, hinj, hsymok, haddr⟩ := hgl
  have fa := fun {g} (hg : g ∈ (progOf R).funcs) => factsRWithT stage hR hI hg
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
      siteOkTC_sound (site_sound (fa hg).sites hs) hd hf'
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hf'
    refine ⟨hh, ?_, n, Lu, Ld, heq, h1, h2⟩
    simp only [calleeB, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact .inl ⟨g, hg, e, he, by rw [hen, hname]⟩
  have hcalB : ∀ g ∈ (progOf R).funcs, ∀ h, (ofRes I R B F).Callee g h →
      calleeB (progOf R) (fun n => I.syms.lookup n) h = true ∧ h ∈ (progOf R).funcs := by
    intro g hg h hh
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
  have hcal : ∀ g ∈ (progOf R).funcs, ∀ h, (ofRes I R B F).Callee g h →
      (h.slots = [] → (RAFrame.compute (artOf R h).vcp (artOf R h).rf).size =
        (artOf R h).af.frameSize - clobberBytes (artOf R h).af.saves) ∧ slotFitsB h (artOf R h) = true := fun g hg h hh =>
    (fa (hcalB g hg h hh).2).callee (hcalB g hg h hh).1
  have hinT : ∀ g ∈ (progOf R).funcs, Compile.functionET g = true →
      InSubsetT (ofRes I R B F).P.bare g := by
    intro g hg hET
    refine ⟨hET, fun b _ st _ fn args _ e he => Clif.Program.bare_func? _ _,
      fun b _ fn args et _ e he => Clif.Program.bare_func? _ _, (fa hg).abi, fun sig hs => ?_,
      (fa hg).storeT⟩
    have := List.all_eq_true.mp (fa hg).indOk sig hs
    simpa [Bool.and_eq_true, decide_eq_true_eq] using this
  have hinTC : ∀ g ∈ (progOf R).funcs, Compile.functionETCF g = true →
      InSubsetTCF (ofRes I R B F).P.bare g := by
    intro g hg hETCF
    refine ⟨hETCF, fun b _ st _ fn args _ e he => Clif.Program.bare_func? _ _,
      fun b _ fn args et _ e he => Clif.Program.bare_func? _ _, (fa hg).abi, fun sig hs => ?_,
      (fa hg).storeT⟩
    have := List.all_eq_true.mp (fa hg).indOk sig hs
    simpa [Bool.and_eq_true, decide_eq_true_eq] using this
  have hcomp : ∀ g ∈ (progOf R).funcs,
      CompiledAnyT (ofRes I R B F).P.bare g (artOf R g).k (artOf R g).vc (artOf R g).vcp
        (artOf R g).rf (artOf R g).af (artOf R g).fa (artOf R g).fb ∧
      (artOf R g).base = BitVec.ofNat 64 (I.baseOf g.name) := by
    intro g hg
    obtain ⟨hl, hpr, ha, he, hla, hb⟩ := (fa hg).pipe
    rcases (fa hg).lowerOk with ⟨hET, hlowT⟩ | ⟨hETC, hlowTC⟩
    · rcases hstage with rfl | rfl
      · exact ⟨.inl ⟨hinT g hg hET,
          .legacy ⟨hl, hlowT, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩⟩, hb⟩
      · exact ⟨.inl ⟨hinT g hg hET,
          .cleanup ⟨hl, hlowT, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩⟩, hb⟩
    · rcases hstage with rfl | rfl
      · exact ⟨.inr (.legacy ⟨hl, hlowTC, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩), hb⟩
      · exact ⟨.inr (.cleanup ⟨hl, hlowTC, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩), hb⟩
  refine
    { names := hn
      free := fun g hg => (fa hg).free
      subset := fun g hg =>
        (fa hg).lowerOk.elim (fun h => (hinT g hg h.1).toTC.toTCF) (fun h => hinTC g hg h.1)
      compiled := fun g hg => .inl (hcomp g hg).1
      sretE := fun g hg hs => by
        obtain ⟨hE, hlc⟩ := (fa hg).sretE hs
        obtain ⟨hl, hpr, ha, he, hla, -⟩ := (fa hg).pipe
        have hS : InSubset (ofRes I R B F).P.bare g := by
          rcases (fa hg).lowerOk with ⟨hET, -⟩ | ⟨hETC, -⟩
          · exact ⟨hE, (hinT g hg hET).externCalls, (hinT g hg hET).tryExterns,
              (hinT g hg hET).abiSigs, (hinT g hg hET).indSigs⟩
          · exact ⟨hE, (hinTC g hg hETC).externCalls, (hinTC g hg hETC).tryExterns,
              (hinTC g hg hETC).abiSigs, (hinTC g hg hETC).indSigs⟩
        refine .inl ⟨hS, ?_⟩
        rcases hstage with rfl | rfl
        · exact .legacy ⟨hl, hlc, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩
        · exact .cleanup ⟨hl, hlc, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩
      covered := fun g hg => (fa hg).covered
      outFits := fun g hg e he hs i off p hl hp => ?_
      baseNoAlloc := hB.baseNoAlloc
      argRegs := fun g hg => ⟨(fa hg).nodup, (fa hg).argReg, (fa hg).width⟩
      sretRets := fun g hg hs us hr => retsB_sound (fa hg).rets hs hr
      calleeFrame := fun g hg h hh hs => (hcal g hg h hh).1 hs
      slotFits := fun g hg h hh => slotFitsB_sound (hcal g hg h hh).2
      callRegs := fun g hg info h hs =>
        callRegsC_of_int ((fa (hcalB g hg h (.inl ⟨info, hs⟩)).2).calleeInt
          (hcalB g hg h (.inl ⟨info, hs⟩)).1) (site g hg info h hs).2.2
      blrRegs := fun g hg info hs hreg => by
        refine LinkSys.blrRegsC_of_int _ (fun t h hh hb =>
          (fa (hcalB g hg h (.inr (.inr ⟨hh, hb.1.1⟩))).2).calleeInt
            (hcalB g hg h (.inr (.inr ⟨hh, hb.1.1⟩))).1) ?_
        obtain hbl := siteOkTC_reg (site_sound (fa hg).sites hs) hreg
        rcases blrOkTC_sound hbl with ⟨t, Lu, Ld, heq, hall⟩ | ⟨t, Lc, Dc, hshape, hno⟩
        · exact .inl ⟨t, Lu, Ld, heq, fun h hh hb hl =>
            hall h hh (indToB_of hb.1) (fun n hn => (hb.2 n (gotOf_sound hn)).symm) hl⟩
        · exact .inr ⟨t, Lc, Dc, hshape, fun h hh hb => absurd hh (fun hc => hno h hh (indToB_of hb.1)
            (fun n hn => (hb.2 n (gotOf_sound hn)).symm))⟩
      raBlr := fun g hg info hs hreg h hh hmay pc hpc => by
        by_cases hhg : h.name = g.name
        · rw [Clif.name_inj hn hh hg hhg]
          exact raOk_self (hcomp g hg).1.layout (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
        · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
      indScope := fun g hg hnf => ⟨hB.keepSyms ⟨g, hg, hnf⟩, ?_, hB.aliasSyms ⟨g, hg, hnf⟩⟩
      indSig := fun g hg hnf h hh hmay hm =>
        (indFactsRWithT stage hR hI hg hnf h hh (mayB_of hmay) hm).1
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
      exact raOk_self (hcomp g hg).1.layout (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
    · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
  · simp only [raStarB, List.all_eq_true] at hstar
    exact outside_sound (hstar _ (tab_mem hn hh)) k hk
  · simp only [symOkB, List.all_eq_true, beq_iff_eq] at hsymok
    have := hsymok _ (lookup_pair hn')
    show I.symAddr n 0 = _
    rw [symAddr_zero, this]
end E2E.LinkCheck
