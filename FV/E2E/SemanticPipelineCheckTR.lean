import FV.E2E.SemanticPipelineCheckT
import FV.E2E.LinkArmTR

/-! # The typed checks with the register-guarded calls (#753, stage R4)

`okRWithTSR stage I R` is `okRWithTS` (`SemanticPipelineCheckT`) with the call-site check of a
`blr` site narrowed to its shape (`siteOkCR`, `LinkSiteTCR`: the registers of the entered function
are the world theorems' register guard's), the return classes checked (`retClsB`), and a
Stock-category artifact admitted only without call sites (`lowerOkTSRB`, `noCallSitesB`; every
function with a call site has the retained production artifact). `okRWithTSR_soundTR`: the typed
link contract with the register-guarded calls `LinkSys.OkTR`. `okRWithTSRFast` evaluates it with
the lookups of `LinkCtx`, the per-function checks in parallel and the scans indexed
(`@[csimp]`, `okRWithTSR_eq_fast`).
-/

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

set_option autoImplicit false

/-- **The lowering check of `okRWithTSR`**: `lowerOkTSB` whose Stock case admits a Stock-category
artifact (`SemanticNI.check`'s classifiers) only when the prepared code has no call site
(`noCallSitesB`), and otherwise the retained production artifact (`lowerCheck`): every function
with a call site takes the latter (#753 issuecomment-7229737530). -/
def lowerOkTSRB (g : Clif.Function) (vc vcp : VCode) : Bool :=
  (Compile.functionE g && !(g.sig.params.any (·.purpose == .sret)) &&
      ((noCallSitesB vcp && SemanticNI.check g vc) || lowerCheck g vc)) ||
    (lowersToB g vc &&
      ((Compile.functionET g && lowerCheckT g vc) || (Compile.functionETCF g && lowerCheckTCF g vc)))

theorem lowerOkTSRB_sound {g : Clif.Function} {vc vcp : VCode} (h : lowerOkTSRB g vc vcp = true) :
    (Compile.functionE g = true ∧ g.sig.params.any (·.purpose == .sret) = false ∧
      ((noCallSitesB vcp = true ∧ SemanticNI.check g vc = true) ∨ lowerCheck g vc = true)) ∨
    (lowerFunction g = .ok vc ∧ ((Compile.functionET g = true ∧ lowerCheckT g vc = true) ∨
      (Compile.functionETCF g = true ∧ lowerCheckTCF g vc = true))) := by
  simp only [lowerOkTSRB, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨hE, hs⟩, hc⟩ | ⟨hl, h⟩
  · exact .inl ⟨hE, hs, hc⟩
  · exact .inr ⟨lowersToB_sound hl, h⟩

/-- **A Stock artifact for the register-guarded world theorems from the checks**: the retained
production artifact where `lowerCheck` holds, else a Stock-category artifact
(`CompiledSemanticNI.of_checks`) of code without call sites. -/
theorem CompiledSemanticNIR.of_checksR {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} {cleanup : Bool}
    (lower : (noCallSitesB vcp = true ∧ SemanticNI.check f vc = true) ∨ lowerCheck f vc = true)
    (prepared : Backend.prepare (Stock.Arithmetic.stageF cleanup f vc) = .ok vcp)
    (prepOk : prepCheck (Stock.Arithmetic.stageF cleanup f vc) vcp = true)
    (check : Backend.checkAlloc vcp rf = .ok ()) (alloc : lowerRFunc vcp rf = .ok af)
    (emit : emitFunc k af = .ok fa) (layout : fa.layout = .ok fb) :
    CompiledSemanticNIR f k vc vcp rf af fa fb := by
  rcases lower with ⟨hnc, hsem⟩ | legacy
  · exact .inr ⟨CompiledSemanticNI.of_checks hsem prepared prepOk check alloc emit layout,
      noCallSitesB_sound hnc⟩
  · refine .inl ?_
    cases cleanup with
    | false =>
      exact .stock ⟨⟨legacy,prepared,prepOk,allocChecked_of_checkAlloc check,alloc,emit,layout⟩,check⟩
    | true =>
      exact .stockCleanup ⟨⟨legacy,prepared,prepOk,allocChecked_of_checkAlloc check,alloc,emit,layout⟩,check⟩

def staticChksWithTSR (stage : Clif.Function → VCode → VCode) (I : LinkInput) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  [("compiled: pipeline", r.toBool),
   ("compiled: Stock (SemanticNI without call sites, or lowerCheck) or lowerFunction lowerCheckT/TCF",
     lowerOkTSRB g a.vc a.vcp),
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
   ("sret: subset E, lowerCheck, or returns in retX", !(g.sig.params.any (·.purpose == .sret)) ||
     (Compile.functionE g && lowerCheck g a.vc) || allInsts a.vc (retsXB g.sig.returns.length))]

/-- The per-function checks of `okRWithTSR`: `staticChksWithTSR` and the link checks with the
`blr` sites checked for their shape and the return classes (`linkChksTSR`). -/
def chksWithTSR (stage : Clif.Function → VCode → VCode) (I : LinkInput) (P : Clif.Program)
    (T : List (Clif.Function × Art)) (g : Clif.Function) (r : Except String Art) :
    List (String × Bool) :=
  staticChksWithTSR stage I g r ++ linkChksTSR I P T g r

/-- **The typed checks on any pipeline's results with the register-guarded calls** (#753, stage
R4): `okRWithTS` with a `blr` site checked for its shape (`siteOkCR`), the return classes
(`retClsB`), and a Stock-category artifact admitted only without call sites (`lowerOkTSRB`). -/
def okRWithTSR (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  (globalChks I (progOf R) (tabOf R)).all (·.2) &&
    R.all fun e => (chksWithTSR stage I (progOf R) (tabOf R) e.1 e.2).all (·.2)

/-- `okRWithTSR` with the lookups computed once (`LinkCtx.of`), the per-function checks in
parallel tasks (`Link.parMap`) and the program's scans indexed (`linkChksWithTSXR_of`). The
compiler evaluates this in place of `okRWithTSR` (`okRWithTSR_eq_fast`, `@[csimp]`). -/
def okRWithTSRFast (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  let P := progOf R
  let T := tabOf R
  let C := LinkCtx.of I P T
  let X := LinkIdx.of P C.ents
  let SI := sigIdx P C.S
  (globalChksWith C I P T).all (·.2) &&
    (Link.parMap (fun e => (staticChksWithTSR stage I e.1 e.2 ++ linkChksWithTSXR C X SI e.1 e.2).all
      (·.2)) R).all id

@[csimp] theorem okRWithTSR_eq_fast : @okRWithTSR = @okRWithTSRFast := by
  funext stage I R
  simp only [okRWithTSRFast, okRWithTSR, chksWithTSR, assocMap_fun, globalChksWith_of,
    linkChksWithTSXR_of, Link.parMap_eq, List.all_map, Function.comp_def, id]


/-- The facts of one function that `okRWithTSR` establishes (`FactsWithTS` with `lowerOkTSRB`,
`siteOkCR` and `retClsB`). -/
structure FactsWithTSR (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res)
    (g : Clif.Function) (a : Art) : Prop where
  pipe : prepare (stage g a.vc) = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
    emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
    a.base = BitVec.ofNat 64 (I.baseOf g.name)
  lowerOk : (Compile.functionE g = true ∧ g.sig.params.any (·.purpose == .sret) = false ∧
      ((noCallSitesB a.vcp = true ∧ SemanticNI.check g a.vc = true) ∨ lowerCheck g a.vc = true)) ∨
    (lowerFunction g = .ok a.vc ∧ ((Compile.functionET g = true ∧ lowerCheckT g a.vc = true) ∨
      (Compile.functionETCF g = true ∧ lowerCheckTCF g a.vc = true)))
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
  sites : allInsts a.vcp (siteB (siteOkCR (progOf R) g)) = true
  declSig : ∀ e ∈ g.externs.map (·.2), ∀ h, (progOf R).func? e.name = some h → e.sig = h.sig
  entry : entryB g a.vcp = true
  fits : a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64
  ra : raCallB (tabOf R) g a = true
  depth : frameDrop a.af ≤ I.D
  free : Clif.LinkFree g
  storeT : Compile.storeTypedB g = true
  sretE : g.sig.params.any (·.purpose == .sret) = true →
    (Compile.functionE g = true ∧ lowerCheck g a.vc = true) ∨
      allInsts a.vc (retsXB g.sig.returns.length) = true
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  indOk : indSigsOk g = true
  ind : indBC (progOf R) (fun n => I.syms.lookup n) g = true
  retCls : retClsB g = true

theorem okRWithTSR_global (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (h : okRWithTSR stage I R = true) :
    ∀ c ∈ globalChks I (progOf R) (tabOf R), c.2 = true := by
  simp only [okRWithTSR, chksWithTSR, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem okRWithTSR_names (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (h : okRWithTSR stage I R = true) : ((progOf R).funcs.map (·.name)).Nodup := by
  have := okRWithTSR_global stage h _ (by simp [globalChks]; exact Or.inl rfl)
  simpa using this

theorem factsRWithTSR (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (hR : PreparedResults stage I R) (h : okRWithTSR stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) : FactsWithTSR stage I R g (artOf R g) := by
  have hn := okRWithTSR_names stage h
  obtain ⟨e, he, rfl, hart⟩ := artOf_spec hn hg
  have hall : ∀ c ∈ chksWithTSR stage I (progOf R) (tabOf R) e.1 e.2, c.2 = true := by
    simp only [okRWithTSR, chksWithTSR, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 e he
  rw [hart]
  simp only [chksWithTSR, staticChksWithTSR, linkChksTSR, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.append_assoc] at hall
  obtain ⟨h1, h2, h3, h4, h5, h7, h9, h10, h11, h15, h16, h18, h19, h20, h22, h23, hsr, h8,
    h12, h13, h14, h17, h24, h25⟩ := hall
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h8 h9 h10 h11 h12 h14 h16 h18 h20 h22 hsr
  refine ⟨hR e he _ (getOk_eq h1), lowerOkTSRB_sound h2,
    h3, toBool_unit h4,
    (formsCoveredB_iff _ _).1 h5, h7, fun x hx hs => ?_, h9, h10, h11, fun hc => ?_, h13,
    fun x hx h' hf => ?_, h15, h16, h17, h18, linkFreeB_sound h19, h20, fun hs => ?_,
    ⟨h22.1, h22.2⟩, h23, h24, h25⟩
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
  · rcases hsr with (h | h) | h
    · rw [hs] at h; cases h
    · exact .inl h
    · exact .inr h

theorem indFactsRWithTSR (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (hR : PreparedResults stage I R) (h : okRWithTSR stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) (hnf : ¬ Clif.IndFree g) :
    ∀ h ∈ (progOf R).funcs, mayB (fun n => I.syms.lookup n) g h.name = true →
      ((∃ sig ∈ indSigs g, LinkSys.IndSigMatch sig h) ∨
        (DeclN g h.name ∧ ∃ sig ∈ indSigs g, LinkSys.IndTyMatch sig h)) →
      ∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8 := by
  have h := (factsRWithTSR stage hR h hg).ind
  simp only [indBC, Bool.or_eq_true, List.all_eq_true] at h
  rcases h with h | h2
  · exact absurd (indFreeB_sound h) hnf
  intro h' hh hd hm
  have hany : indSigB g h' = true := by
    simp only [indSigB, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
    rcases hm with ⟨sig, hs, hm⟩ | ⟨hdn, sig, hs, hm⟩
    · exact .inl ⟨sig, hs, hm⟩
    · exact .inr ⟨declB_of hdn, sig, hs, hm⟩
  have h2' := h2 h' hh
  rw [hd, hany] at h2'
  rcases h2' with (e | e) | hb8
  · cases e
  · cases e
  revert hb8
  cases hb : sigParamBytes h'.sig <;> simp

/-- **The typed checks with the register-guarded calls establish `LinkSys.OkTR`** (#753, stage R4;
`okRWithTS_soundT` for `okRWithTSR`). `okRWithTS_soundT`'s doc: (#722)
`okRWith_soundT` for results whose later stages are the compiler's (`PreparedResults`; no
lowering equation), each function's artifact being either typed one or the Stock artifact of an
integer function (`CompiledAnyTS`). (The cleanup alternative of `hstage` was
`fun _ => DeadCleanup.prune`; the compiler's cleanup stage is now `cleanupStage`, #552.) -/
theorem okRWithTSR_soundTR (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (hstage : stage = (fun _ => id) ∨ stage = cleanupStage)
    (hR : PreparedResults stage I R)
    (hI : okRWithTSR stage I R = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (ofRes I R B F)) (hF : ∀ a, (ofRes I R B F).Img a → F a) :
    (ofRes I R B F).OkTR := by
  have hn := okRWithTSR_names stage hI
  have hgl := okRWithTSR_global stage hI
  simp only [globalChks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hgl
  obtain ⟨-, himg, hstar, hinj, hsymok, haddr⟩ := hgl
  have fa := fun {g} (hg : g ∈ (progOf R).funcs) => factsRWithTSR stage hR hI hg
  have site : ∀ g ∈ (progOf R).funcs, ∀ info h,
      (ofRes I R B F).ProgSite g info h →
      h ∈ (progOf R).funcs ∧
        calleeB (progOf R) (fun n => I.syms.lookup n) h = true ∧
        ∃ n Lc Dc, info = ⟨.sym n, argPairsC Lc, callDefsC Dc⟩ ∧
        Lc.map (·.2.2) = regLocs h.sig ∧
        (Dc.map (·.1)).take (sigRets h.sig).length = (sigRetRegs h.sig).take Dc.length := by
    intro g hg info h ⟨hs, n, hd, hf⟩
    have hf' : (progOf R).func? n = some h := hf
    obtain ⟨⟨e, he, hen⟩, Lc, Dc, heq, h1, h2⟩ :=
      siteOkCR_sym_sound (site_sound (fa hg).sites hs) hd hf'
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hf'
    refine ⟨hh, ?_, n, Lc, Dc, heq, h1, h2⟩
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
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  have hinTC : ∀ g ∈ (progOf R).funcs, Compile.functionETCF g = true →
      InSubsetTCF (ofRes I R B F).P.bare g := by
    intro g hg hETCF
    refine ⟨hETCF, fun b _ st _ fn args _ e he => Clif.Program.bare_func? _ _,
      fun b _ fn args et _ e he => Clif.Program.bare_func? _ _, (fa hg).abi, fun sig hs => ?_,
      (fa hg).storeT⟩
    have := List.all_eq_true.mp (fa hg).indOk sig hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  have hinE : ∀ g ∈ (progOf R).funcs, Compile.functionE g = true →
      InSubset (ofRes I R B F).P.bare g := by
    intro g hg hE
    have hT := hinT g hg (Compile.functionET_of_functionE hE)
    exact ⟨hE, hT.externCalls, hT.tryExterns, hT.abiSigs, hT.indSigs⟩
  have hcomp : ∀ g ∈ (progOf R).funcs,
      CompiledAnyTSR (ofRes I R B F).P.bare g (artOf R g).k (artOf R g).vc (artOf R g).vcp
        (artOf R g).rf (artOf R g).af (artOf R g).fa (artOf R g).fb ∧
      (artOf R g).base = BitVec.ofNat 64 (I.baseOf g.name) := by
    intro g hg
    obtain ⟨hpr, ha, he, hla, hb⟩ := (fa hg).pipe
    rcases (fa hg).lowerOk with ⟨hE, hns, hsem⟩ | ⟨hl, ⟨hET, hlowT⟩ | ⟨hETC, hlowTC⟩⟩
    · refine ⟨.inr ⟨hinE g hg hE, hns, ?_⟩, hb⟩
      rcases hstage with rfl | rfl
      · exact CompiledSemanticNIR.of_checksR (cleanup := false) hsem hpr (fa hg).prepOk
          (fa hg).check ha he hla
      · exact CompiledSemanticNIR.of_checksR (cleanup := true) hsem hpr (fa hg).prepOk
          (fa hg).check ha he hla
    · rcases hstage with rfl | rfl
      · exact ⟨.inl (.inl ⟨hinT g hg hET,
          .legacy ⟨hl, hlowT, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩⟩), hb⟩
      · exact ⟨.inl (.inl ⟨hinT g hg hET,
          .cleanup ⟨hl, hlowT, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩⟩), hb⟩
    · rcases hstage with rfl | rfl
      · exact ⟨.inl (.inr (.legacy ⟨hl, hlowTC, hpr, (fa hg).prepOk, (fa hg).check, ha, he,
          hla⟩)), hb⟩
      · -- As in `PipelineCheckT`: the skip runs only on subset-E functions accepted by
        -- `lowerCheck` (typed branch); elsewhere the stage is `prune vc`.
        cases hk : (Compile.functionE g && lowerCheck g (artOf R g).vc)
        · have hst : cleanupStage g (artOf R g).vc = DeadCleanup.prune (artOf R g).vc := by
            simp only [cleanupStage, skipStage, hk, Bool.false_eq_true, ↓reduceIte]
          have hpo := (fa hg).prepOk
          rw [hst] at hpr hpo
          exact ⟨.inl (.inr (.cleanup ⟨hl, hlowTC, hpr, hpo, (fa hg).check, ha, he, hla⟩)), hb⟩
        · rw [Bool.and_eq_true] at hk
          obtain ⟨hE, hlc⟩ := hk
          exact ⟨.inl (.inl ⟨hinT g hg (Compile.functionET_of_functionE hE),
            .cleanup ⟨hl, lowerCheckT_of_lowerCheck hlc, hpr, (fa hg).prepOk, (fa hg).check, ha,
              he, hla⟩⟩), hb⟩
  refine
    { names := hn
      free := fun g hg => (fa hg).free
      subset := fun g hg => by
        rcases (fa hg).lowerOk with ⟨hE, -, -⟩ | ⟨-, h | h⟩
        · exact (hinT g hg (Compile.functionET_of_functionE hE)).toTC.toTCF
        · exact (hinT g hg h.1).toTC.toTCF
        · exact hinTC g hg h.1
      compiled := fun g hg => (hcomp g hg).1
      sretE := fun g hg hs => by
        rcases (fa hg).sretE hs with ⟨hE, hlc⟩ | hx
        · obtain ⟨hpr, ha, he, hla, -⟩ := (fa hg).pipe
          have hl : lowerFunction g = .ok (artOf R g).vc := by
            rcases (fa hg).lowerOk with ⟨-, hns, -⟩ | ⟨hl, -⟩
            · rw [hs] at hns; cases hns
            · exact hl
          refine .inl ⟨hinE g hg hE, ?_⟩
          rcases hstage with rfl | rfl
          · exact .legacy ⟨hl, hlc, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩
          · exact .cleanup ⟨hl, hlc, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩
        · exact .inr (retsXB_sound hx)
      covered := fun g hg => (fa hg).covered
      outFits := fun g hg e he hs i off p hl hp => ?_
      baseNoAlloc := hB.baseNoAlloc
      argRegs := fun g hg => ⟨(fa hg).nodup, (fa hg).argReg, (fa hg).width⟩
      sretRets := fun g hg hs us hr => retsB_sound (fa hg).rets hs hr
      calleeFrame := fun g hg h hh hs => (hcal g hg h hh).1 hs
      slotFits := fun g hg h hh => slotFitsB_sound (hcal g hg h hh).2
      callRegs := fun g hg info h hs => (site g hg info h hs).2.2
      blrShape := fun g hg info hs hreg => siteOkCR_reg (site_sound (fa hg).sites hs) hreg
      retCls := fun g hg => retClsB_sound (fa hg).retCls
      raBlr := fun g hg info hs hreg h hh hmay pc hpc => by
        by_cases hhg : h.name = g.name
        · rw [Clif.name_inj hn hh hg hhg]
          exact raOk_self (hcomp g hg).1.toTS.layout (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
        · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
      indScope := fun g hg hnf => ⟨hB.keepSyms ⟨g, hg, hnf⟩, ?_, hB.aliasSyms ⟨g, hg, hnf⟩⟩
      indSig := fun g hg hnf h hh hmay hm => indFactsRWithTSR stage hR hI hg hnf h hh (mayB_of hmay) hm
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
  · intro a ha b hb x hxa hxb
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
      exact raOk_self (hcomp g hg).1.toTS.layout (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
    · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
  · simp only [raStarB, List.all_eq_true] at hstar
    exact outside_sound (hstar _ (tab_mem hn hh)) k hk
  · simp only [symOkB, List.all_eq_true, beq_iff_eq] at hsymok
    have := hsymok _ (lookup_pair hn')
    show I.symAddr n 0 = _
    rw [symAddr_zero, this]

end E2E.LinkCheck
