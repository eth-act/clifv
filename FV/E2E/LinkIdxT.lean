import FV.E2E.LinkIdx
import FV.E2E.LinkSiteTC

/-! # The widened and class-aware link checks with the index (#1062)

`linkChksWithT` and `linkChksWithTS` (`FV/E2E/LinkSiteTC.lean`) with `LinkIdx`
(`FV/E2E/LinkIdx.lean`): the `blr` sites (`siteWithOkTC`, `siteWithOkC`) and the indirect-call
scope (`indFastB`, `indFastBC`) scan only the functions `g` may enter (`LinkIdx.progFor`), the
return-address check only the functions whose code may contain the address (`raCallIdxB`).
`linkChksWithTI_of`, `linkChksWithTSI_of`: equal to `linkChksWithT`, `linkChksWithTS` at
`LinkIdx.of P C.ents`. No statement changes.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof

theorem siteWithOkTC_restrict (F : String → Option Clif.Function) {P P' : Clif.Program}
    (g : Clif.Function) {may : Clif.Function → Bool}
    (hc : ∀ h ∈ P.funcs, may h = true → h ∈ P'.funcs) (hs : ∀ h ∈ P'.funcs, h ∈ P.funcs)
    (vc : VCode) : siteWithOkTC F P' g may vc = siteWithOkTC F P g may vc := by
  funext info
  unfold siteWithOkTC
  rw [siteWithOk_restrict F g hc hs vc]
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r =>
    cases r with
    | vreg t c =>
      cases c with
      | float => rfl
      | int =>
        simp only []
        rw [all_sub_eq (l := P.funcs) (c := P'.funcs) ?_ hs]
        intro x hx hp
        apply hc x hx
        cases hm : may x
        · simp [hm] at hp
        · rfl
    | _ => rfl

theorem blrOkC_restrict {P P' : Clif.Program} {may : Clif.Function → Bool}
    (hc : ∀ h ∈ P.funcs, may h = true → h ∈ P'.funcs) (hs : ∀ h ∈ P'.funcs, h ∈ P.funcs)
    (got : Nat → Option String) (info : CallInfo) :
    blrOkC P' may got info = blrOkC P may got info := by
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r =>
    cases r with
    | vreg t c =>
      cases c with
      | float => rfl
      | int =>
        simp only [blrOkC]
        rw [all_sub_eq (l := P.funcs) (c := P'.funcs) ?_ hs]
        intro x hx hp
        apply hc x hx
        cases hm : may x
        · simp [hm] at hp
        · rfl
    | _ => rfl

theorem siteWithOkC_restrict (F : String → Option Clif.Function) {P P' : Clif.Program}
    (g : Clif.Function) {may : Clif.Function → Bool}
    (hc : ∀ h ∈ P.funcs, may h = true → h ∈ P'.funcs) (hs : ∀ h ∈ P'.funcs, h ∈ P.funcs)
    (vc : VCode) : siteWithOkC F P' g may vc = siteWithOkC F P g may vc := by
  funext info
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r => exact blrOkC_restrict hc hs _ _

theorem indWithBC_restrict {P P' : Clif.Program} (S : String → Option Nat) (ind : Bool)
    (D : String → Bool) (sigs : List Clif.Signature)
    (hc : ∀ h ∈ P.funcs, indSigWithB D sigs h = true → h ∈ P'.funcs)
    (hs : ∀ h ∈ P'.funcs, h ∈ P.funcs) :
    indWithBC P' S ind D sigs = indWithBC P S ind D sigs := by
  unfold indWithBC
  rw [all_sub_eq (l := P.funcs) (c := P'.funcs) ?_ hs]
  intro x hx hp
  apply hc x hx
  cases hm : indSigWithB D sigs x
  · simp [hm] at hp
  · rfl

theorem siteWithOkTC_progFor (F : String → Option Clif.Function) (P : Clif.Program)
    (E : List RaEnt) (S : String → Option Nat) (ind : Bool) (g : Clif.Function)
    (sigs : List Clif.Signature) (vc : VCode) :
    siteWithOkTC F ((LinkIdx.of P E).progFor P g sigs) g
        (indToWithB S ind (fun n => (declSet g).contains n) sigs g) vc =
      siteWithOkTC F P g (indToWithB S ind (fun n => (declSet g).contains n) sigs g) vc :=
  siteWithOkTC_restrict F g (fun _ hh hm => indTo_cands E S ind g sigs hh hm)
    (fun _ hh => cands_sub hh) vc

theorem siteWithOkC_progFor (F : String → Option Clif.Function) (P : Clif.Program)
    (E : List RaEnt) (S : String → Option Nat) (ind : Bool) (g : Clif.Function)
    (sigs : List Clif.Signature) (vc : VCode) :
    siteWithOkC F ((LinkIdx.of P E).progFor P g sigs) g
        (indToWithB S ind (fun n => (declSet g).contains n) sigs g) vc =
      siteWithOkC F P g (indToWithB S ind (fun n => (declSet g).contains n) sigs g) vc :=
  siteWithOkC_restrict F g (fun _ hh hm => indTo_cands E S ind g sigs hh hm)
    (fun _ hh => cands_sub hh) vc

theorem indWithBC_progFor (P : Clif.Program) (E : List RaEnt) (S : String → Option Nat)
    (ind : Bool) (g : Clif.Function) (sigs : List Clif.Signature) :
    indWithBC ((LinkIdx.of P E).progFor P g sigs) S ind (fun n => (declSet g).contains n) sigs =
      indWithBC P S ind (fun n => (declSet g).contains n) sigs :=
  indWithBC_restrict S ind _ sigs (fun _ hh hm => indSig_cands E g sigs hh hm)
    (fun _ hh => cands_sub hh)

/-- **`linkChksWithT` with the index `X`** (`linkChksWithTI_of`). -/
def linkChksWithTI (C : LinkCtx) (X : LinkIdx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let sigs := indSigs g
  let may := indToWithB C.S (indFreeB g) (fun n => Ds.contains n) sigs g
  let Pg := X.progFor P g sigs
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteWithOkTC C.F Pg g may a.vcp))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallIdxB X g a),
   ("indScope/indSig", indWithB Pg C.S (indFreeB g) (fun n => Ds.contains n) sigs)]

theorem linkChksWithTI_of (C : LinkCtx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) :
    linkChksWithTI C (LinkIdx.of P C.ents) P g r = linkChksWithT C P g r := by
  simp only [linkChksWithTI, linkChksWithT, siteWithOkTC_progFor, indWithB_progFor,
    raCallIdxB_eq, indFastB]

/-- **`linkChksWithTS` with the index `X`** (`linkChksWithTSI_of`). -/
def linkChksWithTSI (C : LinkCtx) (X : LinkIdx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let sigs := indSigs g
  let may := indToWithB C.S (indFreeB g) (fun n => Ds.contains n) sigs g
  let Pg := X.progFor P g sigs
  [("outFits", g.externs.all (fun e => !(C.F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("calleeFrame/slotFits",
     !(C.callees.contains g.name || ((C.S g.name).isSome && C.anyInd)) ||
       ((!g.slots.isEmpty || fr.size == a.af.frameSize - clobberBytes a.af.saves) && slotFitsB g a)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteWithOkC C.F Pg g may a.vcp))),
   ("declSig", declSigWithB C.F g),
   ("raCall/raBlr", raCallIdxB X g a),
   ("indScope/indSig", indWithBC Pg C.S (indFreeB g) (fun n => Ds.contains n) sigs)]

theorem linkChksWithTSI_of (C : LinkCtx) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) :
    linkChksWithTSI C (LinkIdx.of P C.ents) P g r = linkChksWithTS C P g r := by
  simp only [linkChksWithTSI, linkChksWithTS, siteWithOkC_progFor, indWithBC_progFor,
    raCallIdxB_eq, indFastBC]

end E2E.LinkCheck
