import FV.E2E.LinkIdxSig

/-! # The program-level input conditions with the indirect-call candidates indexed (#1108)

`progScopeFastB`/`progScopeInFastB` (`FV/E2E/LinkScopeFast.lean`, the program-level part of
`Link.inScopePar`/`inScopeInPar`, which every route's `attempt` and `compileExe` decide) test, for
every function `g` with an indirect call, every function of the program at each of `g`'s
indirect-call sites (`indSiteWithB`, in `callScopeWithB`) and once more for the indirect-call
scope (`indWithB`), one function after another: on ruint's test executable (232,604 functions,
11,781 of them with an indirect call) that is the scan `lean-link`'s exclusion list did in
1,347 s (#1108, `scopeFailsFast`), once per route.

`progScopeIdxB`/`progScopeInIdxB` decide the same with the index of `FV/E2E/LinkIdxSig.lean`:
the functions `g` declares (`LinkIdx.byName`) and the distinct signatures of the others it may
enter (`sigIdx`, `sigCands`), built once per program (`candFacts`, `allMay_eq`), and the functions
in parallel. `@[csimp] progScopeFastB_eq_idx`, `progScopeInFastB_eq_idx`. No statement changes.
-/

namespace E2E.LinkCheck

open Backend

/-- `indSiteWithB P to s args` over the functions `M1` that `g` declares and the signatures `S2`
of the others `to` admits (`indSiteFastB_eq`). -/
def indSiteFastB (M1 : List Clif.Function) (S2 : List Clif.Signature) (to : Clif.Function → Bool)
    (s : Clif.Signature) (args : List Nat) : Bool :=
  M1.all (fun h => !to h || (decide ((regLocs h.sig).length ≠ (callRegs s args).length) ||
      decide (regLocs h.sig = callRegs s args))) &&
    S2.all fun t => decide ((regLocs t).length ≠ (callRegs s args).length) ||
      decide (regLocs t = callRegs s args)

theorem indSiteFastB_eq {P : Clif.Program} {to : Clif.Function → Bool} {M1 : List Clif.Function}
    {S2 : List Clif.Signature} (D : String → Bool)
    (hM1 : ∀ h ∈ M1, h ∈ P.funcs) (hD : ∀ h ∈ P.funcs, D h.name = true → h ∈ M1)
    (hS1 : ∀ t ∈ S2, ∃ h ∈ P.funcs, to h = true ∧ h.sig = t)
    (hS2 : ∀ h ∈ P.funcs, to h = true → D h.name = false → h.sig ∈ S2)
    (s : Clif.Signature) (args : List Nat) :
    indSiteFastB M1 S2 to s args = indSiteWithB P to s args := by
  rw [indSiteWithB]
  simp only [Bool.or_assoc]
  exact (allMay_eq D hM1 hD hS1 hS2 (fun t => decide ((regLocs t).length ≠ (callRegs s args).length) ||
      decide (regLocs t = callRegs s args))).symm

/-- `callScopeWithB F P to g` with the indirect-call sites through `indSiteFastB`
(`callScopeFastB_eq`). -/
def callScopeFastB (F : String → Option Clif.Function) (M1 : List Clif.Function)
    (S2 : List Clif.Signature) (to : Clif.Function → Bool) (g : Clif.Function) : Bool :=
  g.blocks.all fun B =>
    B.body.all (fun st => match st.inst with
      | .call fn args => match g.extern? fn with
        | some e => dirSiteWithB F e args
        | none => true
      | .callIndirect sg _ args => match g.sigDecls.lookup sg with
        | some s => indSiteFastB M1 S2 to s args
        | none => true
      | _ => true) &&
    match B.term with
    | .tryCall fn args _ => match g.extern? fn with
      | some e => dirSiteWithB F e args
      | none => true
    | .tryCallIndirect _ args et => match g.sigDecls.lookup et.sig with
      | some s => indSiteFastB M1 S2 to s args
      | none => true
    | _ => true

theorem callScopeFastB_eq {P : Clif.Program} {to : Clif.Function → Bool} {M1 : List Clif.Function}
    {S2 : List Clif.Signature} (F : String → Option Clif.Function) (D : String → Bool)
    (hM1 : ∀ h ∈ M1, h ∈ P.funcs) (hD : ∀ h ∈ P.funcs, D h.name = true → h ∈ M1)
    (hS1 : ∀ t ∈ S2, ∃ h ∈ P.funcs, to h = true ∧ h.sig = t)
    (hS2 : ∀ h ∈ P.funcs, to h = true → D h.name = false → h.sig ∈ S2) (g : Clif.Function) :
    callScopeFastB F M1 S2 to g = callScopeWithB F P to g := by
  simp only [callScopeFastB, callScopeWithB, indSiteFastB_eq D hM1 hD hS1 hS2]
  all_goals rfl

/-- The indirect-call scope's test of a callee's signature `t` (`indWithB`'s: at most 8 bytes of
stack-passed parameters, and the returns `indRetsSig`). -/
def paramsRetsOk (sigs : List Clif.Signature) (t : Clif.Signature) : Bool :=
  (match sigParamBytes t with | .ok b => decide (b.length ≤ 8) | .error _ => false) &&
    indRetsSig sigs t

/-- `indWithB P S ind D sigs` over the functions `M1` that `g` declares and the signatures `S3`
of the others it may enter (`indFastX_eq`). -/
def indFastX (ind : Bool) (mi : Clif.Function → Bool) (M1 : List Clif.Function)
    (S3 : List Clif.Signature) (sigs : List Clif.Signature) : Bool :=
  ind || (M1.all (fun h => !mi h || paramsRetsOk sigs h.sig) && S3.all (paramsRetsOk sigs))

theorem indFastX_eq {P : Clif.Program} {S : String → Option Nat} {ind : Bool}
    {D : String → Bool} {sigs : List Clif.Signature} {M1 : List Clif.Function}
    {S3 : List Clif.Signature}
    (hM1 : ∀ h ∈ M1, h ∈ P.funcs) (hD : ∀ h ∈ P.funcs, D h.name = true → h ∈ M1)
    (hS3 : ∀ t ∈ S3, ∃ h ∈ P.funcs,
      (mayWithB S ind D h.name && indSigWithB D sigs h) = true ∧ h.sig = t)
    (hS4 : ∀ h ∈ P.funcs, (mayWithB S ind D h.name && indSigWithB D sigs h) = true →
      D h.name = false → h.sig ∈ S3) :
    indFastX ind (fun h => mayWithB S ind D h.name && indSigWithB D sigs h) M1 S3 sigs =
      indWithB P S ind D sigs := by
  unfold indFastX indWithB
  congr 1
  refine (allMay_eq (P := P) (may := fun h => mayWithB S ind D h.name && indSigWithB D sigs h)
    D hM1 hD hS3 hS4 (paramsRetsOk sigs)).symm.trans ?_
  congr 1
  funext h
  simp only [Bool.not_and, paramsRetsOk, indRetsWithB_sig, Bool.or_assoc]
  all_goals rfl

/-- **`progFnWithB F P S g` through the index** `X = LinkIdx.of P []`, `SI = sigIdx P S`
(`progFnFastB_eq`). -/
def progFnFastB (F : String → Option Clif.Function) (S : String → Option Nat) (X : LinkIdx)
    (SI : Std.HashMap (List Clif.Ty) (List Clif.Signature)) (g : Clif.Function) : Bool :=
  let ind := indFreeB g
  let Ds := declSet g
  let D := fun n => Ds.contains n
  let sigs := indSigs g
  let to := indToWithB S ind D sigs g
  let M1 := g.externs.flatMap fun e => X.byName.getD e.2.name []
  let cs := if ind then [] else sigCands SI sigs
  declSigWithB F g &&
    indFastX ind (fun h => mayWithB S ind D h.name && indSigWithB D sigs h) M1
      (cs.filter (indSigMatchSig sigs)) sigs &&
    callScopeFastB F M1 (cs.filter (indMatchSig sigs)) to g && outScopeWithB F g

theorem progFnFastB_eq (F : String → Option Clif.Function) (P : Clif.Program)
    (S : String → Option Nat) (g : Clif.Function) :
    progFnFastB F S (LinkIdx.of P []) (sigIdx P S) g = progFnWithB F P S g := by
  obtain ⟨hM1, hD, hS1, hS2, hS3, hS4⟩ := candFacts P [] S g _ _ _ _ _ rfl rfl rfl rfl rfl
  unfold progFnFastB progFnWithB indFastB
  dsimp only
  rw [indFastX_eq hM1 hD hS3 hS4, callScopeFastB_eq F _ hM1 hD hS1 hS2]

/-- **`progScopeFastB` through the index, the functions in parallel** (`progScopeFastB_eq_idx`). -/
def progScopeIdxB (P : Clif.Program) (S : String → Option Nat) : Bool :=
  let m := funcMap P
  let X := LinkIdx.of P []
  let SI := sigIdx P S
  namesNodupB (P.funcs.map (·.name)) &&
    (Link.parMap (progFnFastB (fun n => m[n]?) S X SI) P.funcs).all id && addrSlotsInB P S

/-- **`progScopeInFastB` through the index, the functions in parallel**
(`progScopeInFastB_eq_idx`). -/
def progScopeInIdxB (P : Clif.Program) (S : String → Option Nat) : Bool :=
  let m := funcMap P
  let X := LinkIdx.of P []
  let SI := sigIdx P S
  namesNodupB (P.funcs.map (·.name)) &&
    (Link.parMap (progFnFastB (fun n => m[n]?) S X SI) P.funcs).all id && addrSlotsInputB P S

@[csimp] theorem progScopeFastB_eq_idx : @progScopeFastB = @progScopeIdxB := by
  funext P S
  unfold progScopeFastB progScopeIdxB
  dsimp only
  rw [progScopeWithB, namesNodupB_eq, Link.parMap_eq, List.all_map]
  simp only [Function.comp_def, id_eq, progFnFastB_eq]

@[csimp] theorem progScopeInFastB_eq_idx : @progScopeInFastB = @progScopeInIdxB := by
  funext P S
  unfold progScopeInFastB progScopeInIdxB
  dsimp only
  rw [progScopeInWithB, namesNodupB_eq, Link.parMap_eq, List.all_map]
  simp only [Function.comp_def, id_eq, progFnFastB_eq]

end E2E.LinkCheck
