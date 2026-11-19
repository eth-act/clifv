import FV.E2E.LinkScopeIdx

/-! # The integer routes' `blr` and indirect-call checks with the signatures indexed (#1108)

`linkChksWithI` (`FV/E2E/LinkIdx.lean`, the per-function link checks of the Stock and return-pin
routes' `okRSemanticNI`/`okRSemanticFor`) tests each `blr` site of `g` (`blrOk`) and `g`'s
indirect-call scope (`indWithB`) against `LinkIdx.cands g sigs`: every function with the parameter
types of one of `g`'s indirect-call signatures, once per site. On ruint's test executable those
groups hold up to 82,814 functions, and the checks ran one function after another: the return-pin
attempt's per-function checks alone took 24,726 s of CPU (#1108).

`linkChksWithIX` is `linkChksWithI` with `FV/E2E/LinkIdxSig.lean`'s index, as `linkChksWithTSX`
for the typed checks: the functions `g` declares (`M1`), the distinct signatures of the others it
may enter (`sigCands`, `S2`/`S3`), at a call through the GOT symbol `n` the functions named `n`.
`blrFastI_eq`, `siteFastI_eq`, `linkChksWithIX_of` (equal to `linkChksWith` over the program).
No statement changes.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof

/-- `blrOk`'s test of a function of signature `t` at the `blr` site `info`. -/
def blrSigI (info : CallInfo) (t : Clif.Signature) : Bool :=
  decide ((regLocs t).length ≠ (decU info.uses).length) ||
    (decide ((decU info.uses).map (·.2) = regLocs t) &&
      decide (((decD info.defs).map (·.1)).take (sigRets t).length =
        (List.range (min (sigRets t).length (decD info.defs).length)).map Reg.x))

/-- **`blrOk` with the functions it tests precomputed** (`blrFastI_eq`): at a call through the
GOT symbol `n` the functions named `n` (`byName n`), at another `blr` the functions `g` declares
(`M1`) and the signatures `S2` of the others `g` may enter. -/
def blrFastI (byName : String → List Clif.Function) (may : Clif.Function → Bool)
    (M1 : List Clif.Function) (S2 : List Clif.Signature) (got : Nat → Option String)
    (info : CallInfo) : Bool :=
  match info.dest with
  | .reg (.vreg t .int) =>
    decide (info.uses = retPairs (decU info.uses)) &&
    decide (info.defs = callDefs (decD info.defs)) &&
    match got t with
    | some n => (byName n).all fun h => !may h || blrSigI info h.sig
    | none => M1.all (fun h => !may h || blrSigI info h.sig) && S2.all (blrSigI info)
  | _ => false

theorem blrFastI_eq {P : Clif.Program} {byName : String → List Clif.Function}
    {may : Clif.Function → Bool} {M1 : List Clif.Function} {S2 : List Clif.Signature}
    (D : String → Bool)
    (hB : ∀ n h, h ∈ byName n ↔ h ∈ P.funcs ∧ h.name = n)
    (hM1 : ∀ h ∈ M1, h ∈ P.funcs) (hD : ∀ h ∈ P.funcs, D h.name = true → h ∈ M1)
    (hS1 : ∀ t ∈ S2, ∃ h ∈ P.funcs, may h = true ∧ h.sig = t)
    (hS2 : ∀ h ∈ P.funcs, may h = true → D h.name = false → h.sig ∈ S2)
    (got : Nat → Option String) (info : CallInfo) :
    blrFastI byName may M1 S2 got info = blrOk P may got info := by
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r =>
    cases r with
    | vreg t c =>
      cases c with
      | float => rfl
      | int =>
        simp only [blrFastI, blrOk]
        congr 1
        apply Bool.eq_iff_iff.2
        cases hg : got t with
        | some n =>
          simp only [List.all_eq_true]
          constructor
          · intro h x hx
            by_cases hn : x.name = n
            · have := h x ((hB n x).2 ⟨hx, hn⟩)
              cases hm : may x
              · simp
              · simp only [hm, Bool.not_true, Bool.false_or, blrSigI] at this
                simp only [hm, hn, bne_self_eq_false, Bool.not_true, Bool.false_or]
                exact this
            · simp [hn]
          · intro h x hx
            obtain ⟨hx', hn⟩ := (hB n x).1 hx
            have := h x hx'
            simp only [hn, bne_self_eq_false, Bool.or_false] at this
            cases hm : may x
            · simp
            · simp only [hm, Bool.not_true, Bool.false_or] at this
              simp only [Bool.not_true, Bool.false_or, blrSigI]
              exact this
        | none =>
          simp only [List.all_eq_true, Bool.and_eq_true]
          constructor
          · rintro ⟨h1, h2⟩ x hx
            cases hm : may x
            · simp
            · cases hd : D x.name
              · have := h2 _ (hS2 x hx hm hd)
                simp only [blrSigI] at this
                simp only [Bool.not_true, Bool.or_false, Bool.false_or]
                exact this
              · have := h1 x (hD x hx hd)
                simp only [hm, Bool.not_true, Bool.false_or, blrSigI] at this
                simp only [Bool.not_true, Bool.or_false, Bool.false_or]
                exact this
          · intro h
            refine ⟨fun x hx => ?_, fun t ht => ?_⟩
            · have := h x (hM1 x hx)
              cases hm : may x
              · simp
              · simp only [hm, Bool.not_true, Bool.or_false, Bool.false_or] at this
                simp only [Bool.not_true, Bool.false_or, blrSigI]
                exact this
            · obtain ⟨x, hx, hm, rfl⟩ := hS1 t ht
              have := h x hx
              simp only [hm, Bool.not_true, Bool.or_false, Bool.false_or] at this
              simp only [blrSigI]
              exact this
    | _ => rfl

/-- `siteWithOk` with `blrFastI` at the `blr` sites (`siteFastI_eq`). -/
def siteFastI (F : String → Option Clif.Function) (g : Clif.Function)
    (byName : String → List Clif.Function) (may : Clif.Function → Bool)
    (M1 : List Clif.Function) (S2 : List Clif.Signature) (vc : VCode) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match F n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        decide (info.uses = retPairs (decU info.uses)) &&
        decide (info.defs = callDefs (decD info.defs)) &&
        decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length (decD info.defs).length)).map Reg.x)
    | none => true
  | .reg _ => blrFastI byName may M1 S2 (gotOf vc) info

theorem siteFastI_eq (F : String → Option Clif.Function) {P : Clif.Program} (g : Clif.Function)
    {byName : String → List Clif.Function} {may : Clif.Function → Bool}
    {M1 : List Clif.Function} {S2 : List Clif.Signature} (D : String → Bool)
    (hB : ∀ n h, h ∈ byName n ↔ h ∈ P.funcs ∧ h.name = n)
    (hM1 : ∀ h ∈ M1, h ∈ P.funcs) (hD : ∀ h ∈ P.funcs, D h.name = true → h ∈ M1)
    (hS1 : ∀ t ∈ S2, ∃ h ∈ P.funcs, may h = true ∧ h.sig = t)
    (hS2 : ∀ h ∈ P.funcs, may h = true → D h.name = false → h.sig ∈ S2) (vc : VCode) :
    siteFastI F g byName may M1 S2 vc = siteWithOk F P g may vc := by
  funext info
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r => exact blrFastI_eq D hB hM1 hD hS1 hS2 _ _

/-- **`linkChksWith` with the signatures indexed** (`linkChksWithIX_of`): `SI` the program's
distinct signatures with a symbol (`sigIdx P C.S`); `g`'s candidates computed once. -/
def linkChksWithIX (C : LinkCtx) (X : LinkIdx)
    (SI : Std.HashMap (List Clif.Ty) (List Clif.Signature)) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let D := fun n => Ds.contains n
  let sigs := indSigs g
  let ind := indFreeB g
  let may := indToWithB C.S ind D sigs g
  let M1 := g.externs.flatMap fun e => X.byName.getD e.2.name []
  let cs := if ind then [] else sigCands SI sigs
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteFastI C.F g (fun n => X.byName.getD n []) may
     M1 (cs.filter (indMatchSig sigs)) a.vcp))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallIdxB X g a),
   ("indScope/indSig", indFastX ind (fun h => mayWithB C.S ind D h.name && indSigWithB D sigs h)
     M1 (cs.filter (indSigMatchSig sigs)) sigs)]

theorem linkChksWithIX_of (C : LinkCtx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) :
    linkChksWithIX C (LinkIdx.of P C.ents) (sigIdx P C.S) g r = linkChksWith C P g r := by
  obtain ⟨hM1, hD, hS1, hS2, hS3, hS4⟩ := candFacts P C.ents C.S g _ _ _ _ _ rfl rfl rfl rfl rfl
  unfold linkChksWithIX linkChksWith indFastB
  dsimp only
  rw [indFastX_eq hM1 hD hS3 hS4,
    siteFastI_eq C.F g _ (fun n h => byName_mem P C.ents n h) hM1 hD hS1 hS2, raCallIdxB_eq]

end E2E.LinkCheck
