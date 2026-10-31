import FV.Link.Image
import FV.E2E.LinkArmT
import FV.E2E.PreparedPipeline

/-! # The typed checks on any pipeline's results (#722)

`okRWithTS stage I R` is `okRWithT` (the typed checks of `FV/E2E/PipelineCheckT.lean`) with the
lowering check widened per function to either

* the typed validators on `lowerFunction`'s output (`lowerFunction g = .ok vc`, decided, then
  `lowerCheckT`/`lowerCheckTCF` as in `okRWithT`), or
* the Stock route's validator `SemanticNI.check` on an integer function (subset E) without `sret`
  parameter (Cranelift's code where the Stock lowerings are proven).

Since the typed case decides the lowering equation, the results may come from any pipeline whose
later stages are the compiler's (`PreparedResults`, e.g. the Stock routes' results
`resultsProductionWith`, which fall back to `lowerFunction` on the functions the Stock lowerings
reject). `okRWithTS_soundT`: the typed link contract `LinkSys.OkT` (whose artifact field is
`CompiledAnyTS`). `okRWithTSFast` evaluates it with the lookups of `LinkCtx` and the per-function
checks in parallel (`@[csimp]`, `okRWithTS_eq_fast`).
-/

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

/-- `lowerFunction g = .ok vc`, decided. -/
def lowersToB (g : Clif.Function) (vc : VCode) : Bool :=
  match lowerFunction g with
  | .ok v => decide (v = vc)
  | .error _ => false

theorem lowersToB_sound {g : Clif.Function} {vc : VCode} (h : lowersToB g vc = true) :
    lowerFunction g = .ok vc := by
  unfold lowersToB at h
  split at h
  · rename_i v hv
    rw [hv, of_decide_eq_true h]
  · cases h

/-- The lowering check of `okRWithTS`: the Stock validator on an integer function without `sret`
parameter, or the typed validators on `lowerFunction`'s output. -/
def lowerOkTSB (g : Clif.Function) (vc : VCode) : Bool :=
  (Compile.functionE g && !(g.sig.params.any (·.purpose == .sret)) && SemanticNI.check g vc) ||
    (lowersToB g vc &&
      ((Compile.functionET g && lowerCheckT g vc) || (Compile.functionETCF g && lowerCheckTCF g vc)))

/-- Every return of the code is in x0, x1, … (`RetsX`, decided per instruction). -/
def retsXB : MInst → Bool
  | .rets us => decide (us.map (·.2) = (List.range us.length).map Reg.x)
  | _ => true

theorem retsXB_sound {vc : VCode} (h : allInsts vc retsXB = true) : RetsX vc := by
  intro us hr
  obtain ⟨b, vb, k, hb, hk⟩ := hr
  have := allInsts_sound h hb hk
  simpa [retsXB] using this

def staticChksWithTS (stage : Clif.Function → VCode → VCode) (I : LinkInput) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  [("compiled: pipeline", r.toBool),
   ("compiled: Stock SemanticNI or lowerFunction lowerCheckT/TCF", lowerOkTSB g a.vc),
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
   ("sret: subset E, lowerCheck, or returns in x0..", !(g.sig.params.any (·.purpose == .sret)) ||
     (Compile.functionE g && lowerCheck g a.vc) || allInsts a.vc retsXB)]

/-- The per-function checks of `okRWithTS`: `staticChksWithTS` and the class-aware link checks
`linkChksTS` (#742: program calls with arguments and results of either class; it had
`linkChksT` and "calleeInt", integer returns of the functions of `P` called from `P`). -/
def chksWithTS (stage : Clif.Function → VCode → VCode) (I : LinkInput) (P : Clif.Program)
    (T : List (Clif.Function × Art)) (g : Clif.Function) (r : Except String Art) :
    List (String × Bool) :=
  staticChksWithTS stage I g r ++ linkChksTS I P T g r

/-- **The typed checks on any pipeline's results** (#722). -/
def okRWithTS (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  (globalChks I (progOf R) (tabOf R)).all (·.2) &&
    R.all fun e => (chksWithTS stage I (progOf R) (tabOf R) e.1 e.2).all (·.2)

/-- `okRWithTS` with the lookups of `linkChksTS`/`globalChks` computed once (`LinkCtx.of`) and
the per-function checks in parallel tasks (`Link.parMap`). The compiler evaluates this in place
of `okRWithTS` (`okRWithTS_eq_fast`, `@[csimp]`). -/
def okRWithTSFast (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  let P := progOf R
  let T := tabOf R
  let C := LinkCtx.of I P T
  (globalChksWith C I P T).all (·.2) &&
    (Link.parMap (fun e => (staticChksWithTS stage I e.1 e.2 ++ linkChksWithTS C P e.1 e.2).all
      (·.2)) R).all id

@[csimp] theorem okRWithTS_eq_fast : @okRWithTS = @okRWithTSFast := by
  funext stage I R
  simp only [okRWithTSFast, okRWithTS, chksWithTS, assocMap_fun, globalChksWith_of,
    linkChksWithTS_of, Link.parMap_eq, List.all_map, Function.comp_def, id]

/-- The facts of one function that `okRWithTS` establishes (`FactsWithT` without the lowering
equation, which only the typed case has). -/
structure FactsWithTS (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res)
    (g : Clif.Function) (a : Art) : Prop where
  pipe : prepare (stage g a.vc) = .ok a.vcp ∧ lowerRFunc a.vcp a.rf = .ok a.af ∧
    emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
    a.base = BitVec.ofNat 64 (I.baseOf g.name)
  lowerOk : (Compile.functionE g = true ∧ g.sig.params.any (·.purpose == .sret) = false ∧
      SemanticNI.check g a.vc = true) ∨
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
  sites : allInsts a.vcp (siteB (siteOkC (progOf R) g
    (indToB (fun n => I.syms.lookup n) g) a.vcp)) = true
  declSig : ∀ e ∈ g.externs.map (·.2), ∀ h, (progOf R).func? e.name = some h → e.sig = h.sig
  entry : entryB g a.vcp = true
  fits : a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64
  ra : raCallB (tabOf R) g a = true
  depth : frameDrop a.af ≤ I.D
  free : Clif.LinkFree g
  storeT : Compile.storeTypedB g = true
  sretE : g.sig.params.any (·.purpose == .sret) = true →
    (Compile.functionE g = true ∧ lowerCheck g a.vc = true) ∨ allInsts a.vc retsXB = true
  abi : sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true
  indOk : indSigsOk g = true
  ind : indBC (progOf R) (fun n => I.syms.lookup n) g = true

theorem okRWithTS_global (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (h : okRWithTS stage I R = true) :
    ∀ c ∈ globalChks I (progOf R) (tabOf R), c.2 = true := by
  simp only [okRWithTS, chksWithTS, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1

theorem okRWithTS_names (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (h : okRWithTS stage I R = true) : ((progOf R).funcs.map (·.name)).Nodup := by
  have := okRWithTS_global stage h _ (by simp [globalChks]; exact Or.inl rfl)
  simpa using this

theorem lowerOkTSB_sound {g : Clif.Function} {vc : VCode} (h : lowerOkTSB g vc = true) :
    (Compile.functionE g = true ∧ g.sig.params.any (·.purpose == .sret) = false ∧
      SemanticNI.check g vc = true) ∨
    (lowerFunction g = .ok vc ∧ ((Compile.functionET g = true ∧ lowerCheckT g vc = true) ∨
      (Compile.functionETCF g = true ∧ lowerCheckTCF g vc = true))) := by
  simp only [lowerOkTSB, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨hE, hs⟩, hc⟩ | ⟨hl, h⟩
  · exact .inl ⟨hE, hs, hc⟩
  · exact .inr ⟨lowersToB_sound hl, h⟩

theorem factsRWithTS (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (hR : PreparedResults stage I R) (h : okRWithTS stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) : FactsWithTS stage I R g (artOf R g) := by
  have hn := okRWithTS_names stage h
  obtain ⟨e, he, rfl, hart⟩ := artOf_spec hn hg
  have hall : ∀ c ∈ chksWithTS stage I (progOf R) (tabOf R) e.1 e.2, c.2 = true := by
    simp only [okRWithTS, chksWithTS, Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 e he
  rw [hart]
  simp only [chksWithTS, staticChksWithTS, linkChksTS, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.append_assoc] at hall
  obtain ⟨h1, h2, h3, h4, h5, h7, h9, h10, h11, h15, h16, h18, h19, h20, h22, h23, hsr, h8,
    h12, h13, h14, h17, h24⟩ := hall
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h8 h9 h10 h11 h12 h14 h16 h18 h20 h22 hsr
  refine ⟨hR e he _ (getOk_eq h1), lowerOkTSB_sound h2,
    h3, toBool_unit h4,
    (formsCoveredB_iff _ _).1 h5, h7, fun x hx hs => ?_, h9, h10, h11, fun hc => ?_, h13,
    fun x hx h' hf => ?_, h15, h16, h17, h18, linkFreeB_sound h19, h20, fun hs => ?_,
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
  · rcases hsr with (h | h) | h
    · rw [hs] at h; cases h
    · exact .inl h
    · exact .inr h

theorem indFactsRWithTS (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (hR : PreparedResults stage I R) (h : okRWithTS stage I R = true) {g : Clif.Function}
    (hg : g ∈ (progOf R).funcs) (hnf : ¬ Clif.IndFree g) :
    ∀ h ∈ (progOf R).funcs, mayB (fun n => I.syms.lookup n) g h.name = true →
      ((∃ sig ∈ indSigs g, LinkSys.IndSigMatch sig h) ∨
        (DeclN g h.name ∧ ∃ sig ∈ indSigs g, LinkSys.IndTyMatch sig h)) →
      ∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8 := by
  have h := (factsRWithTS stage hR h hg).ind
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

/-- **The typed checks on any pipeline's results establish the typed link contract** (#722):
`okRWith_soundT` for results whose later stages are the compiler's (`PreparedResults`; no
lowering equation), each function's artifact being either typed one or the Stock artifact of an
integer function (`CompiledAnyTS`). -/
theorem okRWithTS_soundT (stage : Clif.Function → VCode → VCode) {I : LinkInput} {R : Res}
    (hstage : stage = (fun _ => id) ∨ stage = (fun _ => DeadCleanup.prune))
    (hR : PreparedResults stage I R)
    (hI : okRWithTS stage I R = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (ofRes I R B F)) (hF : ∀ a, (ofRes I R B F).Img a → F a) :
    (ofRes I R B F).OkT := by
  have hn := okRWithTS_names stage hI
  have hgl := okRWithTS_global stage hI
  simp only [globalChks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hgl
  obtain ⟨-, himg, hstar, hinj, hsymok, haddr⟩ := hgl
  have fa := fun {g} (hg : g ∈ (progOf R).funcs) => factsRWithTS stage hR hI hg
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
      siteOkC_sound (site_sound (fa hg).sites hs) hd hf'
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
      CompiledAnyTS (ofRes I R B F).P.bare g (artOf R g).k (artOf R g).vc (artOf R g).vcp
        (artOf R g).rf (artOf R g).af (artOf R g).fa (artOf R g).fb ∧
      (artOf R g).base = BitVec.ofNat 64 (I.baseOf g.name) := by
    intro g hg
    obtain ⟨hpr, ha, he, hla, hb⟩ := (fa hg).pipe
    rcases (fa hg).lowerOk with ⟨hE, hns, hsem⟩ | ⟨hl, ⟨hET, hlowT⟩ | ⟨hETC, hlowTC⟩⟩
    · refine ⟨.inr ⟨hinE g hg hE, hns, ?_⟩, hb⟩
      rcases hstage with rfl | rfl
      · exact CompiledSemanticNI.of_checks (cleanup := false) hsem hpr (fa hg).prepOk
          (fa hg).check ha he hla
      · exact CompiledSemanticNI.of_checks (cleanup := true) hsem hpr (fa hg).prepOk
          (fa hg).check ha he hla
    · rcases hstage with rfl | rfl
      · exact ⟨.inl (.inl ⟨hinT g hg hET,
          .legacy ⟨hl, hlowT, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩⟩), hb⟩
      · exact ⟨.inl (.inl ⟨hinT g hg hET,
          .cleanup ⟨hl, hlowT, hpr, (fa hg).prepOk, (fa hg).check, ha, he, hla⟩⟩), hb⟩
    · rcases hstage with rfl | rfl
      · exact ⟨.inl (.inr (.legacy ⟨hl, hlowTC, hpr, (fa hg).prepOk, (fa hg).check, ha, he,
          hla⟩)), hb⟩
      · exact ⟨.inl (.inr (.cleanup ⟨hl, hlowTC, hpr, (fa hg).prepOk, (fa hg).check, ha, he,
          hla⟩)), hb⟩
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
      blrRegs := fun g hg info hs hreg => by
        obtain ⟨t, Lc, Dc, heq, hall⟩ := blrOkC_sound (siteOkC_reg (site_sound (fa hg).sites hs) hreg)
        exact ⟨t, Lc, Dc, heq, fun h hh hb hl =>
          hall h hh (indToB_of hb.1) (fun n hn => (hb.2 n (gotOf_sound hn)).symm) hl⟩
      raBlr := fun g hg info hs hreg h hh hmay pc hpc => by
        by_cases hhg : h.name = g.name
        · rw [Clif.name_inj hn hh hg hhg]
          exact raOk_self (hcomp g hg).1.layout (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
        · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
      indScope := fun g hg hnf => ⟨hB.keepSyms ⟨g, hg, hnf⟩, ?_, hB.aliasSyms ⟨g, hg, hnf⟩⟩
      indSig := fun g hg hnf h hh hmay hm => indFactsRWithTS stage hR hI hg hnf h hh (mayB_of hmay) hm
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
      exact raOk_self (hcomp g hg).1.layout (List.all_eq_true.1 hstar _ (tab_mem hn hg)) hpc
    · exact raCallB_sound (fa hg).ra hpc _ (tab_mem hn hh) hhg
  · simp only [raStarB, List.all_eq_true] at hstar
    exact outside_sound (hstar _ (tab_mem hn hh)) k hk
  · simp only [symOkB, List.all_eq_true, beq_iff_eq] at hsymok
    have := hsymok _ (lookup_pair hn')
    show I.symAddr n 0 = _
    rw [symAddr_zero, this]

end E2E.LinkCheck
