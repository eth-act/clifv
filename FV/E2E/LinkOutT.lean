import FV.E2E.LinkCheckT
import FV.E2E.LinkScopeT
import FV.E2E.LinkScope

/-! # The typed checker on the compiler's own output (S11e5 Stage C, slice 8)

`okT_of_inScopeT : InScopePT I → OutOkT I → (pipeline success) → linkerOkB I →
okRT (I.withDepth I.resultsT) I.resultsT`: the typed checker `okRT` (`FV/E2E/LinkCheckT.lean`)
accepts the compiler's results from

* the typed input conditions `InScopePT` (`FV/E2E/LinkScopeDefsT.lean`): the typed subset and
  signatures, the validators `lowerCheckT`/`prepCheck` (`CompiledT.of_lowerT`), and the integer
  validator `lowerCheck` of an `sret` function (`lowerCheck_complete`);
* the linker's facts `linkerOkB` and the pipeline's success (both checked by `leanLink`);
* **`OutOkT`**: the checks of `okRT` on the compiler's own output whose completeness is proven
  only for subset E today, decided at run time: `checkAlloc`'s verdict on the lowered allocation
  (the typed chain proves `AllocChecked`, `allocChecked_of_fnScopeT`; the link-level world
  theorems need `checkAlloc`), the form coverage with the artifact's frame, `sretRets`,
  `entryRegs`, `outFits` and the call sites (the integer proofs `LinkOwn*.lean` read
  `LowerScope`), and the two callee checks of `LinkSys.OkT` (an `sret` function is in subset E,
  a callee returns integers). `outOkT_of_inScopeP` (`FV/E2E/LinkScopeIntT.lean`) proves it from
  the integer input conditions.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- **The output checks of the typed link** for the function `g` (pipeline result `r`) of the
program `P`. -/
def outChksT (I : LinkInput) (P : Clif.Program) (g : Clif.Function) (r : Except String Art) :
    List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let may := indToB (fun n => I.syms.lookup n) g
  [("compiled: checkAlloc", (checkAlloc a.vcp a.rf).toBool),
   ("covered", formsCoveredB ⟨a.fa.k, a.af.slotBase⟩ a.vcp),
   ("sretRets", allInsts a.vc (retsB g)),
   ("entryRegs", entryB g a.vcp),
   ("outFits", g.externs.all (fun e => !(P.func? e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteOk P g may a.vcp))),
   ("sret: subset E", !(g.sig.params.any (·.purpose == .sret)) || Compile.functionE g),
   ("calleeInt", calleeIntChk I P g)]

/-- `outChksT` of every function of the results `R`. -/
def outOkTR (I : LinkInput) (R : Res) : Bool :=
  R.all fun e => (outChksT I (progOf R) e.1 e.2).all (·.2)

/-- **`OutOkT`**: the output checks of the compiler's results (`resultsT`). -/
def OutOkT (I : LinkInput) : Bool := outOkTR I I.resultsT

/-- The program's checks hold for the compiler's results of a typed in-scope input. -/
theorem global_resultsTT {I : LinkInput} (hin : InScopePT I = true) (hlk : linkerOkB I = true) :
    (globalChks (I.withDepth I.resultsT) (progOf I.resultsT) (tabOf I.resultsT)).all (·.2) =
      true := by
  obtain ⟨hps, -⟩ := inScopePT_parts hin
  obtain ⟨hnd, -, has⟩ := progScope_parts hps
  obtain ⟨himg, hstar, hinj, hsym, -⟩ := linker_parts hlk
  rw [List.all_eq_true]
  intro c hc
  simp only [globalChks, List.mem_cons, List.not_mem_nil, or_false, progOf_resultsT] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact decide_eq_true hnd
  · exact himg
  · exact hstar
  · rw [progOf_resultsT] at hinj; exact hinj
  · exact hsym
  · exact addrSlotsB_of_in has

/-- `LowerScope` of a subset-E function of the typed scope. -/
theorem lowerScope_of_T {f : Clif.Function} (hs : LowerScopeT f) (hE : Compile.functionE f = true) :
    LowerScope f :=
  ⟨hE, hs.nonempty, hs.noEntryPred, hs.ctxFacts, hs.tryRet, hs.stackLayout, hs.indStackLayout⟩

/-- **The typed per-function checks hold** for the compiler's results of a typed in-scope input
that passes the output checks. -/
theorem chksT_resultsT {I : LinkInput} (hin : InScopePT I = true) (hout : OutOkT I = true)
    (hpipe : I.resultsT.all (·.2.toBool) = true) (hlk : linkerOkB I = true)
    {e : Clif.Function × Except String Art} (he : e ∈ I.resultsT) :
    (chksT (I.withDepth I.resultsT) (progOf I.resultsT) (tabOf I.resultsT) e.1 e.2).all
      (·.2) = true := by
  obtain ⟨hps, hfs⟩ := inScopePT_parts hin
  obtain ⟨-, hpg, -⟩ := progScope_parts hps
  obtain ⟨-, -, -, -, hlf⟩ := linker_parts hlk
  obtain ⟨hfit, hra⟩ := hlf e he
  have hdep := le_depthOf he
  have hok := List.all_eq_true.1 hpipe e he
  have ho := List.all_eq_true.1 hout e he
  obtain ⟨fi, hfi, h1, h2⟩ := mem_resultsT he
  obtain ⟨g, r⟩ := e
  dsimp only at h1 h2 hfit hra hdep hok ho ⊢
  subst h1 h2
  have hgP : fi.func ∈ I.prog.funcs := List.mem_map_of_mem hfi
  have hsc : fnScopeTB fi.func = true := hfs _ hgP
  obtain ⟨hE, hst, -, habi, hind, hnd', harg, hw, hfree, hd, hs, -⟩ := fnScopeT_parts hsc
  obtain ⟨a, hpr⟩ : ∃ a, pipeT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name))
      (raJ fi.ra fi.j) = .ok a := by
    cases hpr : pipeT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j) with
    | error m => rw [hpr] at hok; cases hok
    | ok a => exact ⟨a, rfl⟩
  rw [hpr] at hfit hra hdep ho
  obtain ⟨hl, hp, -, hlr, hem, hla, -, -⟩ := pipeT_spec hpr
  have hga : getOk (Except.ok (ε := String) a) = a := rfl
  simp only [outChksT, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, hga,
    progOf_resultsT] at ho
  obtain ⟨hca, hcov, hrets, hent, hout, hsite, hsr, hci⟩ := ho
  have hca' : checkAlloc a.vcp a.rf = .ok () := toBool_unit hca
  have hc := CompiledT.of_lowerT (dominated_of hd) (lowerScopeT_of hs) hl hp hca' hlr hem hla
  have hfr := frame_of_lower hl hp hlr
  obtain ⟨hdecl, hindB, -, -⟩ := hpg _ hgP
  rw [List.all_eq_true]
  intro c hc'
  simp only [chksT, staticChksT, linkChks, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, List.append_assoc, progOf_resultsT, hpr, hga] at hc'
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact hc.lowerOk
  · exact hc.prepOk
  · exact hca
  · exact hcov
  · exact hrets
  · exact decide_eq_true hnd'
  · exact List.all_eq_true.2 harg
  · simpa using hw
  · exact hent
  · exact decide_eq_true hfit
  · exact decide_eq_true hdep
  · exact hfree
  · simp [hE, hst]
  · simpa [Bool.and_eq_true, List.all_eq_true] using habi
  · exact hind
  · simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hsr ⊢
    rcases hsr with h | h
    · exact .inl h
    · exact .inr ⟨h, lowerCheck_complete (dominated_of hd) (lowerScope_of_T (lowerScopeT_of hs) h) hl⟩
  · exact hout
  · simp only [Bool.or_eq_true]
    exact .inr hfr
  · exact hsite
  · exact hdecl
  · exact hra
  · exact hindB
  · exact hci

/-- **`okRT`'s checks hold on the compiler's results of every typed in-scope input** that passes
the output checks, whose pipeline succeeds and whose link the linker's facts describe. -/
theorem okT_of_inScopeT {I : LinkInput} (hin : InScopePT I = true) (hout : OutOkT I = true)
    (hpipe : I.resultsT.all (·.2.toBool) = true) (hlk : linkerOkB I = true) :
    okRT (I.withDepth I.resultsT) I.resultsT = true := by
  simp only [okRT, Bool.and_eq_true]
  exact ⟨global_resultsTT hin hlk,
    List.all_eq_true.2 fun e he => chksT_resultsT hin hout hpipe hlk he⟩

/-- **`LinkSys.OkT` of the compiler's linked system** of a typed in-scope input. -/
theorem okT_soundT {I : LinkInput} (hin : InScopePT I = true) (hout : OutOkT I = true)
    (hpipe : I.resultsT.all (·.2.toBool) = true) (hlk : linkerOkB I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (LinkSys.ofInputT I B F))
    (hF : ∀ a, (LinkSys.ofInputT I B F).Img a → F a) : (LinkSys.ofInputT I B F).OkT :=
  okR_soundT (resultsT_ok I I.resultsT) (okT_of_inScopeT hin hout hpipe hlk) hB hF

end E2E.LinkCheck
