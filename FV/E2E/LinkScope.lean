import FV.E2E.LinkScopeDefs
import FV.E2E.EmitTotal

/-! # Linking without the checker's verdict: input conditions + own outputs + linker (L2a)

`crate_correct` (`FV/E2E/LinkCheck.lean`) takes `okB I = true`, decided per crate by
`native_decide`. Here `okB`'s checks are split (docs/TO-PROVE.md §3 "L2", L2a, the table there)
into

* **input conditions** (`InScopeP`, `FV/E2E/LinkScopeDefs.lean`): decidable on the CLIF program
  alone — the subset, signatures, no `return_call`, distinct names, declared signatures, the
  scope of indirect calls, the conditions of the backend's totality theorems (`dominatedB`,
  `lowerScopeB`, `arityOkB`), `lowerFunction`/`prepare` acceptance and the spill-code size bound
  (`lowersB`);
* **properties of the compiler's own outputs**, proven here for the compiler's pipeline `pipeT`
  (`lowerAllocReady`): pipeline success (V5/V6b), the validators (`lowerCheck_complete`,
  `prepCheck_complete`, `formsCovered_complete`), `checkAlloc` of regalloc2's answer (kept only if
  accepted), the depth (by construction, `withDepth`), and the facts of the families below;
* **the linker's facts** (`linkerOkB`): the checks about the addresses rust-lld chose — what the
  Lean static linker (L2b) must provide.

`okT_of_inScope : InScopeP I → linkerOkB I → … → okR (I.withDepth I.resultsT) I.resultsT`, then
`okT_sound` (`LinkSys.Ok` of the compiler's linked system `LinkSys.ofInputT`) and
`crate_correct_inScope` (`backend_correct_program` for every function, no `okB` premise).

The facts still taken as explicit, program-independent hypotheses (`OwnHyps`; none mentions
the crate):
* `SpillCheckAllocHyp`: `checkAlloc` accepts the spill allocation (V4 proved `AllocChecked`;
  the link-level theorem's `Compiled` asks the checker's verdict);
* `EmitCondsHyp`: `immsOkB`, `noAlwaysB`, `branchTargetsOkB` of the prepared VCode (V6c);
* `RetsFact`, `EntryFact`, `SitesFact`, `OutFitsFact`, `FrameFact`: the families of own-output
  facts about call sites, returns, the entry and frames.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The pipeline -/

theorem pipeT_spec {f : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (h : pipeT f k base o = .ok a) :
    lowerFunction f = .ok a.vc ∧ prepare a.vc = .ok a.vcp ∧
      a.rf = allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp o)) ∧
      lowerRFunc a.vcp a.rf = .ok a.af ∧ emitFunc a.k a.af = .ok a.fa ∧ a.fa.layout = .ok a.fb ∧
      a.k = k ∧ a.base = base := by
  unfold pipeT at h
  rcases h1 : lowerFunction f with _ | vc <;> simp only [h1, bind, Except.bind] at h
  · cases h
  rcases h2 : prepare vc with _ | vcp <;> simp only [h2] at h
  · cases h
  rcases h3 : lowerAllocReady vcp (raAnswer vcp o) with _ | af <;> simp only [h3] at h
  · cases h
  rcases h4 : emitFunc k af with _ | fa <;> simp only [h4] at h
  · cases h
  rcases h5 : fa.layout with _ | fb <;> simp only [h5] at h
  · cases h
  cases h
  exact ⟨rfl, h2, rfl, lowerAlloc_eq ((lowerAllocReady_eq _ _).symm.trans h3), h4, h5, rfl, rfl⟩

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

/-! ## The per-function input conditions -/

theorem fnScope_parts {g : Clif.Function} (h : fnScopeB g = true) :
    Compile.functionE g = true ∧ (∀ e ∈ g.externs, e.2.name ≠ g.name) ∧
    (sigAbiOk g.sig = true ∧ ∀ e ∈ g.externs, sigAbiOk e.2.sig = true) ∧ indSigsOk g = true ∧
    (regLocs g.sig).Nodup ∧ (∀ r ∈ regLocs g.sig, r.isArgReg = true) ∧
    (∀ p ∈ g.sig.params, p.ty.width ≤ 64) ∧ linkFreeB g = true ∧ dominatedB g = true ∧
    lowerScopeB g = true ∧ Spill.arityOkB g = true ∧ lowersB g = true := by
  simp only [fnScopeB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3, h3'⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, ⟨h3, h3'⟩, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

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
    ∃ vc vcp, lowerFunction f = .ok vc ∧ prepare vc = .ok vcp ∧ spillSizeOkB vcp = true := by
  unfold lowersB at h
  split at h
  · rename_i vc hl
    split at h
    · rename_i vcp hp
      exact ⟨vc, vcp, hl, hp, h⟩
    · cases h
  · cases h

/-! ## The open, program-independent hypotheses -/

/-- **`checkAlloc` accepts the spill allocation** of every in-scope function. V4 proved
`AllocChecked vcp (spillAlloc vcp)` (`spillAccepted`: verified in-states); the link-level
theorem's `Compiled` asks for the checker's own verdict (one VCode outcome for all
activations). `lean-e2e-check` counts it (1149 of 1149). -/
def SpillCheckAllocHyp : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc vcp : VCode), InSubset p f → Spill.ArityOk f →
    Dominated f → LowerScope f → lowerFunction f = .ok vc → prepare vc = .ok vcp →
    checkAlloc vcp (spillAlloc vcp) = .ok ()

/-- **V6c**: instruction selection's immediates are encodable, no `al`/`nv` conditional branch,
every branch target is a block label (`emitCondsB` without its size part, which `lowersB`
decides on the input). -/
def EmitCondsHyp : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc vcp : VCode), InSubset p f → dominatedB f = true →
    lowerScopeB f = true → lowerFunction f = .ok vc → prepare vc = .ok vcp →
    immsOkB vcp = true ∧ vcp.noAlwaysB = true ∧ branchTargetsOkB vcp = true

/-- The returns of an `sret` function carry its ABI results (`sretRets`). -/
def RetsFact : Prop :=
  ∀ (g : Clif.Function) (vc : VCode), fnScopeB g = true → lowerFunction g = .ok vc →
    allInsts vc (retsB g) = true

/-- The entry `Args` reads parameter registers (`entryRegs`). -/
def EntryFact : Prop :=
  ∀ (g : Clif.Function) (vc vcp : VCode), fnScopeB g = true → lowerFunction g = .ok vc →
    prepare vc = .ok vcp → entryB g vcp = true

/-- The call sites' registers and results (`callRegs`, `blrRegs`, `tryRets`, `blrTry`). -/
def SitesFact : Prop :=
  ∀ (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) (vc vcp : VCode),
    progScopeB P S = true → P.funcs.all fnScopeB = true → g ∈ P.funcs →
    lowerFunction g = .ok vc → prepare vc = .ok vcp →
    allInsts vcp (siteB (siteOk P g (indToB S g) vcp)) = true ∧
      allInsts vcp (tryB P (indToB S g) vcp) = true

/-- The outgoing argument area holds the stack arguments of the declared program callees
(`outFits`). -/
def OutFitsFact : Prop :=
  ∀ (P : Clif.Program) (S : String → Option Nat) (g : Clif.Function) (vc vcp : VCode) (rf : RFunc),
    progScopeB P S = true → P.funcs.all fnScopeB = true → g ∈ P.funcs →
    lowerFunction g = .ok vc → prepare vc = .ok vcp →
    g.externs.all (fun e => !(P.func? e.2.name).isSome ||
      outFitsB e.2.sig (RAFrame.compute vcp rf).intBase) = true

/-- The frame of a callee: no slot region without slots, the slots fit (`calleeFrame`,
`slotFits`). -/
def FrameFact : Prop :=
  ∀ (g : Clif.Function) (a : Art), fnScopeB g = true → lowerFunction g = .ok a.vc →
    prepare a.vc = .ok a.vcp → lowerRFunc a.vcp a.rf = .ok a.af →
    ((!g.slots.isEmpty || (RAFrame.compute a.vcp a.rf).size == a.af.frameSize) &&
      slotFitsB g a) = true

/-- **The open own-output facts**, all program-independent. -/
structure OwnHyps : Prop where
  spill : SpillCheckAllocHyp
  emit : EmitCondsHyp
  rets : RetsFact
  entry : EntryFact
  sites : SitesFact
  outFits : OutFitsFact
  frame : FrameFact

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
theorem pipeT_ok {g : Clif.Function} (hsc : fnScopeB g = true) (hca : SpillCheckAllocHyp)
    (hem : EmitCondsHyp) (k : Nat) (base : BitVec 64) (o : Lean.Json) :
    ∃ a, pipeT g k base o = .ok a ∧ lowerCheck g a.vc = true ∧ prepCheck a.vc a.vcp = true ∧
      checkAlloc a.vcp a.rf = .ok () ∧ FormsCovered ⟨a.fa.k, a.af.slotBase⟩ a.vcp := by
  obtain ⟨-, -, -, -, -, -, -, -, hd, hs, har, hlw⟩ := fnScope_parts hsc
  obtain ⟨vc, vcp, hl, hp, hsz⟩ := lowersB_spec hlw
  have hsub := inSubset_of_fnScope hsc ⟨[]⟩
  have hD := dominated_of hd
  have hS := lowerScope_of hs
  have hne : g.blocks ≠ [] := by
    simp only [lowerScopeB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hs
    exact hs.1.1.1.1.1.1.2
  obtain ⟨himm, hna, htg⟩ := hem _ _ _ _ hsub hd hs hl hp
  have hemc : emitCondsB vcp = true := by
    simp [emitCondsB, hsz, himm, hna, htg]
  obtain ⟨af, ha, fa, fb, he, hla, -⟩ :=
    backend_correct_final_total_emit (k := k) hsub hd hs har hl hp hemc (raAnswer vcp o)
  refine ⟨⟨k, vc, vcp, allocResult vcp (readyAnswer vcp (raAnswer vcp o)), af, fa, fb, base⟩,
    ?_, lowerCheck_complete hD hS hl, prepCheck_complete hp (prepDomain_of_lower hS hl hne),
    checkAlloc_allocResult (hca _ _ _ _ hsub (Spill.arityOk_of har) hD hS hl hp) _,
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

theorem progScope_parts {P : Clif.Program} {S : String → Option Nat} (h : progScopeB P S = true) :
    (P.funcs.map (·.name)).Nodup ∧ (∀ g ∈ P.funcs, declSigB P g = true ∧ indB P S g = true) ∧
      addrSlotsInB P S = true := by
  simp only [progScopeB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem linker_parts {I : LinkInput} {R : Res} (h : linkerOkR I R = true) :
    imgB (tabOf R) = true ∧ raStarB (tabOf R) (BitVec.ofNat 64 I.raStar) = true ∧
      symInjB I (progOf R) = true ∧ symOkB I = true ∧
      ∀ e ∈ R, (getOk e.2).base.toNat + 4 * (getOk e.2).fb.words.size ≤ 2 ^ 64 ∧
        raCallB (tabOf R) e.1 (getOk e.2) = true := by
  simp only [linkerOkR, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem addrSlotsB_of_in {P : Clif.Program} {T : List (Clif.Function × Art)}
    {S : String → Option Nat} (h : addrSlotsInB P S = true) : addrSlotsB P T S = true := by
  simp only [addrSlotsInB, Bool.or_eq_true] at h
  simp only [addrSlotsB, Bool.or_eq_true]
  rcases h with h | h
  · left
    simp only [Bool.not_eq_true'] at h
    simp [h]
  · exact .inr h

/-- **The per-function checks hold** for the compiler's results of an in-scope input. -/
theorem chks_resultsT {I : LinkInput} (hin : InScopeP I = true) (hlk : linkerOkB I = true)
    (hO : OwnHyps) {e : Clif.Function × Except String Art} (he : e ∈ I.resultsT) :
    (chks (I.withDepth I.resultsT) (progOf I.resultsT) (tabOf I.resultsT) e.1 e.2).all
      (·.2) = true := by
  simp only [InScopeP, Bool.and_eq_true] at hin
  obtain ⟨hps, hfs⟩ := hin
  obtain ⟨-, hpg, -⟩ := progScope_parts hps
  obtain ⟨-, -, -, -, hlf⟩ := linker_parts hlk
  obtain ⟨fi, hfi, h1, h2⟩ := mem_resultsT he
  have hgP : e.1 ∈ I.prog.funcs := by
    rw [h1]; exact List.mem_map_of_mem hfi
  have hsc : fnScopeB e.1 = true := List.all_eq_true.1 hfs _ hgP
  obtain ⟨hE, hne, habi, hind, hnd, harg, hw, hfree, -, -, -, -⟩ := fnScope_parts hsc
  obtain ⟨a, ha, hlc, hpc, hca, hcov⟩ := pipeT_ok (k := fi.k)
    (base := BitVec.ofNat 64 (I.baseOf fi.func.name)) (o := raJ fi.ra fi.j)
    (h1 ▸ hsc) hO.spill hO.emit
  rw [← h1] at ha hlc
  rw [h2, ← h1] at *
  have hR := ha
  rw [← h2] at hR
  obtain ⟨hl, hp, -, hlr, -, -, -, -⟩ := pipeT_spec ha
  have hga : getOk e.2 = a := by rw [hR]; rfl
  obtain ⟨hfit, hra⟩ := hlf e he
  rw [hga] at hfit hra
  have hdep := le_depthOf he
  rw [hga] at hdep
  obtain ⟨hdecl, hindB⟩ := hpg _ hgP
  have hPs : progScopeB (progOf I.resultsT) (fun n => I.syms.lookup n) = true := by
    rw [progOf_resultsT]; exact hps
  have hPf : (progOf I.resultsT).funcs.all fnScopeB = true := by
    rw [progOf_resultsT]; exact hfs
  have hgR : e.1 ∈ (progOf I.resultsT).funcs := by rw [progOf_resultsT]; exact hgP
  obtain ⟨hsite, htry⟩ := hO.sites _ _ _ _ _ hPs hPf hgR hl hp
  have hout := hO.outFits _ _ _ _ _ a.rf hPs hPf hgR hl hp
  have hfr := hO.frame _ a hsc hl hp hlr
  rw [List.all_eq_true]
  intro c hc
  simp only [chks, staticChks, linkChks, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rw [hR, progOf_resultsT] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact hlc
  · exact hpc
  · simp [getOk, hca, Except.toBool]
  · exact (formsCoveredB_iff _ _).2 hcov
  · exact hO.rets _ _ hsc hl
  · exact decide_eq_true hnd
  · exact List.all_eq_true.2 harg
  · simpa using hw
  · exact hO.entry _ _ _ hsc hl hp
  · exact decide_eq_true hfit
  · exact decide_eq_true hdep
  · exact hfree
  · exact hE
  · simpa using hne
  · simpa [Bool.and_eq_true, List.all_eq_true] using habi
  · exact hind
  · rw [progOf_resultsT] at htry; exact htry
  · rw [progOf_resultsT] at hout; exact hout
  · simp only [getOk] at hfr ⊢
    simp only [Bool.or_eq_true]
    exact .inr (by rw [progOf_resultsT] at *; simpa using hfr)
  · rw [progOf_resultsT] at hsite; exact hsite
  · exact hdecl
  · exact hra
  · exact hindB

end E2E.LinkCheck
