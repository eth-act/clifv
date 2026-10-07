import FV.E2E.LinkScopeDefs
import FV.E2E.EmitTotalIn
import FV.E2E.LinkOwnGotLocal
import FV.E2E.LinkOwnSegRange
import FV.E2E.LinkOwnFrames
import FV.E2E.LinkOwnRetsIsel
import FV.E2E.SpillCheckAlloc

/-! # Linking without the checker's verdict: input conditions + own outputs + linker (L2a)

`crate_correct` (`FV/E2E/LinkCheck.lean`) takes `okB I = true`, decided per crate by
`native_decide`. Here `okB`'s checks are split (docs/TO-PROVE.md §3 "L2", L2a, the table there)
into

* **input conditions** (`InScopeP`, `FV/E2E/LinkScopeDefs.lean`): decidable on the CLIF program
  alone — the subset, signatures, no `return_call`, distinct names, declared signatures, the
  scope of indirect calls, the call sites' registers (`callScopeB`), the callees' stack
  arguments (`outScopeB`), the conditions of the backend's totality theorems (`dominatedB`,
  `lowerScopeB`, `arityOkB`), `lowerFunction`/`prepare` acceptance, V6c's `extendsWidenB` and
  V6b's size bound `spillSizeOkB` (`lowersB`; `emitCondsB` follows: `emitCondsB_of_input`);
* **properties of the compiler's own outputs**, proven here for the compiler's pipeline `pipeT`
  (`lowerAllocReady`): pipeline success (V5/V6b), the validators (`lowerCheck_complete`,
  `prepCheck_complete`, `formsCovered_complete`), `checkAlloc` of the allocation lowered
  (regalloc2's only if accepted, the spill allocation's by `spillCheckAlloc`), the depth (by
  construction, `withDepth`), the call sites (`sites_of_lower` from the call inversion
  `CallShapeHyp`: `callShapeHyp_of` of the per-run facts `callStmtRunHyp`, `tryRunHyp`
  (`callRunHyp_of`), `segRangeHyp`, `gotLocalHyp` (`gotRunHyp_of`)), the returns
  (`retsB_of_lower` with the ISLE inversion `iselNoRets`) and the entry (`entryB_of_lower`), the
  frames (`outFits_of_lower`, `frame_of_lower`);
* **the linker's facts** (`linkerOkB`): the checks about the addresses rust-lld chose — what the
  Lean static linker (L2b) must provide.

`okT_of_inScope : SpillDefinedHyp → InScopeP I → linkerOkB I →
okR (I.withDepth I.resultsT) I.resultsT`, then `okT_sound` (`LinkSys.Ok` of the compiler's linked
system `LinkSys.ofInputT`) and `crate_correct_inScope` (`backend_correct_program` for every
function, no `okB` premise).

The one fact still taken as an explicit, program-independent hypothesis: `SpillDefinedHyp`
(`FV/E2E/SpillCheckAlloc.lean`), definite assignment of the prepared VCode (availability sets
holding nothing on entry), from which `checkAlloc` accepts the spill allocation (the link-level
`Compiled` keeps `checkAlloc`'s verdict, whose fixpoint starts from no vreg in its home).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The pipeline -/

theorem mem_resultsT {I : LinkInput} {e : Clif.Function × Except String Art}
    (he : e ∈ I.resultsT) : ∃ fi ∈ I.funcs, e.1 = fi.func ∧
      e.2 = pipeT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j) := by
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 he
  exact ⟨fi, hfi, rfl, rfl⟩

theorem progOf_resultsT (I : LinkInput) : progOf I.resultsT = I.prog := by
  simp [progOf, LinkInput.resultsT, LinkInput.prog, Function.comp_def]

/-- The compiler's results are the pipeline's outputs. -/
theorem resultsT_ok (I : LinkInput) (R : Res) : ResOk (I.withDepth R) I.resultsT := by
  intro e he a ha
  obtain ⟨fi, -, h1, h2⟩ := mem_resultsT he
  rw [h2] at ha
  obtain ⟨hl, hp, -, hlr, hem, hla, -, hb⟩ := pipeT_spec ha
  rw [h1]
  exact ⟨hl, hp, hlr, hem, hla, hb⟩

/-! ## The input conditions -/

theorem fnScope_parts {g : Clif.Function} (h : fnScopeB g = true) :
    Compile.functionE g = true ∧ (∀ e ∈ g.externs, e.2.name ≠ g.name) ∧
    (sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true) ∧ indSigsOk g = true ∧
    (regLocs g.sig).Nodup ∧ (∀ r ∈ regLocs g.sig, r.isArgReg = true) ∧
    (∀ p ∈ g.sig.params, p.ty.width ≤ 64) ∧ linkFreeB g = true ∧ dominatedB g = true ∧
    lowerScopeB g = true ∧ Spill.arityOkB g = true ∧ lowersB g = true ∧
    Spill.entryParamsB g = true := by
  simp only [fnScopeB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h3', h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, ⟨h3, h3'⟩, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The subset of the per-function programs (`LinkSys.Ok.subset`) from `fnScopeB`. -/
theorem inSubset_of_fnScope {g : Clif.Function} (h : fnScopeB g = true) (p : Clif.Program) :
    InSubset (p.only g) g := by
  obtain ⟨hE, hne, habi, hind, -⟩ := fnScope_parts h
  refine ⟨?_, hE, ?_, ?_, habi, ?_⟩
  · simp [Clif.Program.only, Clif.Program.func?]
  · intro b _ st _ fn args _ e he
    have hne' := hne _ (lookup_pair he)
    simp [Clif.Program.only, Clif.Program.func?, Ne.symm hne']
  · intro b _ fn args et _ e he
    have hne' := hne _ (lookup_pair he)
    simp [Clif.Program.only, Clif.Program.func?, Ne.symm hne']
  · intro sig hs
    have := List.all_eq_true.mp hind sig hs
    simpa [Bool.and_eq_true, decide_eq_true_eq] using this

theorem lowersB_spec {f : Clif.Function} (h : lowersB f = true) :
    extendsWidenB f = true ∧ ∃ vc vcp, lowerFunction f = .ok vc ∧ prepare vc = .ok vcp ∧
      spillSizeOkB vcp = true := by
  unfold lowersB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hw, h⟩ := h
  refine ⟨hw, ?_⟩
  split at h
  · rename_i vc hl
    split at h
    · rename_i vcp hp
      exact ⟨vc, vcp, hl, hp, h⟩
    · cases h
  · cases h

theorem progScope_parts {P : Clif.Program} {S : String → Option Nat} (h : progScopeB P S = true) :
    (P.funcs.map (·.name)).Nodup ∧
      (∀ g ∈ P.funcs, declSigB P g = true ∧ indB P S g = true ∧ callScopeB P S g = true ∧
        outScopeB P g = true) ∧
      addrSlotsInB P S = true := by
  simp only [progScopeB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc] at h
  exact h

theorem declSig_of {P : Clif.Program} {g : Clif.Function} (h : declSigB P g = true) :
    ∀ e ∈ g.externs.map (·.2), ∀ h', P.func? e.name = some h' → e.sig = h'.sig := by
  intro e he h' hf
  obtain ⟨⟨fn, e'⟩, hm, rfl⟩ := List.mem_map.1 he
  have := List.all_eq_true.1 h _ hm
  dsimp only at hf this
  rw [hf] at this
  simpa using this

theorem linker_parts {I : LinkInput} {R : Res} (h : linkerOkR I R = true) :
    imgB (tabOf R) = true ∧ raStarB (tabOf R) (BitVec.ofNat 64 I.raStar) = true ∧
      symInjB I (progOf R) = true ∧ symOkB I = true ∧
      ∀ e ∈ R, (getOk e.2).base.toNat + 4 * (getOk e.2).fb.words.size ≤ 2 ^ 64 ∧
        raCallB (tabOf R) e.1 (getOk e.2) = true := by
  simp only [linkerOkR, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- A compiled function with an outgoing area in its frame (`intBase`) has one in
`lowerFunction`'s VCode (`prepare` keeps it; an error's default image has none). -/
theorem outArea_of_intBase {I : LinkInput} {x : Clif.Function × Art}
    (hx : x ∈ tabOf I.resultsT) (h : (RAFrame.compute x.2.vcp x.2.rf).intBase ≠ 0) :
    x.1 ∈ I.prog.funcs ∧ outAreaB x.1 = true := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨fi, hfi, h1, h2⟩ := mem_resultsT he
  dsimp only at h ⊢
  rw [h1]
  refine ⟨List.mem_map_of_mem hfi, ?_⟩
  rw [h2] at h
  cases hp : pipeT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j) with
  | error m =>
    rw [hp] at h
    exact (h (show alignTo (default : Art).vcp.outgoing 16 = 0 from rfl)).elim
  | ok a =>
    rw [hp] at h
    obtain ⟨hl, hpr, -⟩ := pipeT_spec hp
    unfold outAreaB
    rw [hl]
    simp only [bne_iff_ne, ne_eq]
    intro h0
    apply h
    show alignTo a.vcp.outgoing 16 = 0
    rw [outgoing_of_prepare hpr, h0]
    rfl

theorem addrSlotsB_of_in {I : LinkInput} {S : String → Option Nat}
    (h : addrSlotsInB I.prog S = true) : addrSlotsB I.prog (tabOf I.resultsT) S = true := by
  simp only [addrSlotsInB, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at h
  simp only [addrSlotsB, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
  rcases h with (h | h) | h
  · refine .inl (.inl ?_)
    rw [List.any_eq_false] at h ⊢
    intro x hx hne
    obtain ⟨hm, ho⟩ := outArea_of_intBase hx (by simpa using hne)
    exact h x.1 hm ho
  · exact .inl (.inr h)
  · exact .inr h

/-! ## Pipeline success and the validators -/

theorem isOk_unit {ε : Type} {x : Except ε Unit} (h : x.isOk = true) : x = .ok () := by
  cases x <;> simp_all [Except.isOk, Except.toBool]

/-- `checkAlloc` accepts the allocation `allocResult` chooses: regalloc2's only if accepted. -/
theorem checkAlloc_allocResult {vcp : VCode} (hsp : checkAlloc vcp (spillAlloc vcp) = .ok ())
    (ra : Except String RFunc) : checkAlloc vcp (allocResult vcp ra) = .ok () := by
  unfold allocResult
  cases ra with
  | error e => exact hsp
  | ok rf =>
    simp only
    split
    · rename_i hc
      split
      · exact isOk_unit hc
      · exact hsp
    · exact hsp

/-- **The compiler's pipeline succeeds on an in-scope function**, and its artifact passes the
validators. -/
theorem pipeT_ok {g : Clif.Function} (hsc : fnScopeB g = true) (hD : SpillDefinedHyp)
    (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    ∃ a, pipeT g k base o = .ok a ∧ lowerCheck g a.vc = true ∧ prepCheck a.vc a.vcp = true ∧
      checkAlloc a.vcp a.rf = .ok () ∧ FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp := by
  obtain ⟨-, -, -, -, -, -, -, -, hd, hs, har, hlw, hen⟩ := fnScope_parts hsc
  obtain ⟨hw, vc, vcp, hl, hp, hsz⟩ := lowersB_spec hlw
  have hem := emitCondsB_of_input hs hw hl hp hsz
  have hsub := inSubset_of_fnScope hsc { funcs := [] }
  have hD' := dominated_of hd
  have hS := lowerScope_of hs
  obtain ⟨af, ha, fa, fb, he, hla, -⟩ :=
    backend_correct_final_total_emit (k := k) hsub hd hs har hl hp hem (raAnswer vcp o)
  refine ⟨⟨k, vc, vcp, allocResult vcp (readyAnswer vcp (raAnswer vcp o)), af, fa, fb, base⟩,
    ?_, lowerCheck_complete hD' hS hl,
    Prep.prepCheck_complete hp (prepDomain_of_lower hS hl hS.nonempty),
    checkAlloc_allocResult (spillCheckAlloc hD hsub (Spill.arityOk_of har) hD' hS hen hl hp) _,
    formsCovered_complete hS hl hp _⟩
  simp [pipeT, hl, hp, ha, he, hla, bind, Except.bind, pure, Except.pure]

/-! ## The checks hold -/

theorem le_foldl_max : ∀ (l : List Nat) (m x : Nat), x ∈ l ∨ x ≤ m → x ≤ l.foldl max m
  | [], m, x, h => by
    rcases h with h | h
    · cases h
    · exact h
  | y :: l, m, x, h => by
    rw [List.foldl_cons]
    apply le_foldl_max l (max m y) x
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr (Nat.le_max_right _ _)
      · exact .inl h
    · exact .inr (Nat.le_trans h (Nat.le_max_left _ _))

theorem le_depthOf {R : Res} {e : Clif.Function × Except String Art} (he : e ∈ R) :
    frameDrop (getOk e.2).af ≤ depthOf R :=
  le_foldl_max _ 0 _ (.inl (List.mem_map_of_mem he))

/-- **The per-function checks hold** for the compiler's results of an in-scope input. -/
theorem chks_resultsT (hD : SpillDefinedHyp) {I : LinkInput} (hin : InScopeP I = true)
    (hlk : linkerOkB I = true) {e : Clif.Function × Except String Art} (he : e ∈ I.resultsT) :
    (chks (I.withDepth I.resultsT) (progOf I.resultsT) (tabOf I.resultsT) e.1 e.2).all
      (·.2) = true := by
  simp only [InScopeP, Bool.and_eq_true] at hin
  obtain ⟨hps, hfs⟩ := hin
  obtain ⟨hnd, hpg, -⟩ := progScope_parts hps
  obtain ⟨-, -, -, -, hlf⟩ := linker_parts hlk
  obtain ⟨hfit, hra⟩ := hlf e he
  have hdep := le_depthOf he
  obtain ⟨fi, hfi, h1, h2⟩ := mem_resultsT he
  obtain ⟨g, r⟩ := e
  dsimp only at h1 h2 hfit hra hdep ⊢
  subst h1 h2
  have hgP : fi.func ∈ I.prog.funcs := List.mem_map_of_mem hfi
  have hsc : fnScopeB fi.func = true := List.all_eq_true.1 hfs _ hgP
  obtain ⟨hE, hne, habi, hind, hnd', harg, hw, hfree, hd, hs, -, -⟩ := fnScope_parts hsc
  obtain ⟨a, ha, hlc, hpc, hca, hcov⟩ := pipeT_ok hsc hD fi.k
    (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j)
  obtain ⟨hl, hp, -, hlr, -, -, -, -⟩ := pipeT_spec ha
  have hga : getOk (pipeT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name))
      (raJ fi.ra fi.j)) = a := by rw [ha]; rfl
  rw [hga] at hfit hra hdep
  obtain ⟨hdecl, hindB, hcall, hos⟩ := hpg _ hgP
  obtain ⟨hsite, htry⟩ := sites_of_lower
    (callShapeHyp_of (callRunHyp_of callStmtRunHyp tryRunHyp)
      (gotRunHyp_of segRangeHyp gotLocalHyp))
    (inSubset_of_fnScope hsc I.prog) hd hs hnd
    (declSig_of hdecl) hcall hl hp
  have hout := outFits_of_lower hd hs hos hl hp a.rf
  have hfr := frame_of_lower hl hp hlr
  have hrets := retsB_of_lower iselNoRets hs hl
  have hent := entryB_of_lower hs hl hp
  rw [List.all_eq_true]
  intro c hc
  simp only [chks, staticChks, linkChks, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, ha, progOf_resultsT] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact hlc
  · exact hpc
  · simp [getOk, hca, Except.toBool]
  · exact (formsCoveredB_iff _ _).2 hcov
  · exact hrets
  · exact decide_eq_true hnd'
  · exact List.all_eq_true.2 harg
  · simpa using hw
  · exact hent
  · exact decide_eq_true hfit
  · exact decide_eq_true hdep
  · exact hfree
  · exact hE
  · simpa using hne
  · simpa [Bool.and_eq_true, List.all_eq_true] using habi
  · exact hind
  · exact htry
  · exact hout
  · simp only [Bool.or_eq_true]
    exact .inr hfr
  · exact hsite
  · exact hdecl
  · exact hra
  · exact hindB

/-- **The program's checks hold** for the compiler's results of an in-scope input. -/
theorem global_resultsT {I : LinkInput} (hin : InScopeP I = true) (hlk : linkerOkB I = true) :
    (globalChks (I.withDepth I.resultsT) (progOf I.resultsT) (tabOf I.resultsT)).all (·.2) =
      true := by
  simp only [InScopeP, Bool.and_eq_true] at hin
  obtain ⟨hnd, -, has⟩ := progScope_parts hin.1
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

/-- **`okB`'s checks hold on the compiler's results of every in-scope input** whose link the
linker's facts describe: `InScopeP` (the input) and `linkerOkB` (the linker), no check of the
compiler's own output. -/
theorem okT_of_inScope (hD : SpillDefinedHyp) {I : LinkInput} (hin : InScopeP I = true)
    (hlk : linkerOkB I = true) : okR (I.withDepth I.resultsT) I.resultsT = true := by
  simp only [okR, Bool.and_eq_true]
  exact ⟨global_resultsT hin hlk, List.all_eq_true.2 fun e he => chks_resultsT hD hin hlk he⟩

/-! ## The linked system of the compiler's results -/

/-- **`LinkSys.ofInputT`**: the linked system of a crate's input compiled by the compiler's
pipeline (`resultsT`), with the stack of one call level by construction (`withDepth`). -/
def _root_.E2E.LinkSys.ofInputT (I : LinkInput) (B : BaseEnv) (F : BitVec 64 → Prop) : LinkSys :=
  ofRes (I.withDepth I.resultsT) I.resultsT B F

/-- **`LinkSys.Ok` of the compiler's linked system** of an in-scope input whose link satisfies
the linker's facts. -/
theorem okT_sound (hD : SpillDefinedHyp) {I : LinkInput} (hin : InScopeP I = true)
    (hlk : linkerOkB I = true) {B : BaseEnv} {F : BitVec 64 → Prop}
    (hB : BaseOk (LinkSys.ofInputT I B F)) (hF : ∀ a, (LinkSys.ofInputT I B F).Img a → F a) :
    (LinkSys.ofInputT I B F).Ok :=
  okR_sound (resultsT_ok I I.resultsT) (okT_of_inScope hD hin hlk) hB hF

/-- The crate's theorem (`CrateStmt`) for the compiler's linked system `LinkSys.ofInputT`. -/
def CrateStmtT (I : LinkInput) (n : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (LinkSys.ofInputT I B F) →
    (∀ a, (LinkSys.ofInputT I B F).Img a → F a) → ProgStmt (LinkSys.ofInputT I B F) n

/-- **`backend_correct_program` for every function of an in-scope input** (L2a): no `okB`
premise; the input conditions `InScopeP`, the linker's facts `linkerOkB` (what L2b must provide)
and the program-independent open facts `OwnHyps`. -/
theorem crate_correct_inScope (hD : SpillDefinedHyp) {I : LinkInput} (hin : InScopeP I = true)
    (hlk : linkerOkB I = true) (n : String) : CrateStmtT I n :=
  fun _ _ hB hF _ hf M _ _ _ _ _ hent hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr =>
    backend_correct_program _ (okT_sound hD hin hlk hB hF) (Clif.Program.func?_some hf).1 M hent
      hres hFeq hgfree himg hbe hargs hcs hsav hrel hpl htr

/-- **Non-vacuity of `BaseOk`** for the compiler's linked system: the closed base environment
satisfies the base premises of every input without `tls_value`. -/
theorem baseOk_closedT {I : LinkInput} {F : BitVec 64 → Prop}
    (htls : ∀ g ∈ I.prog.funcs, hasTls g = false) :
    BaseOk (LinkSys.ofInputT I closedBase F) :=
  baseOk_closedR (fun g hg => htls g (progOf_resultsT I ▸ hg))

end E2E.LinkCheck
