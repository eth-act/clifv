import FV.E2E.ReturnPinCheckFast
import FV.E2E.LinkIdxSig

/-! # The return-pin attempt's call-site check with the candidates indexed (#1108)

`returnPinsWith C g` (`FV/E2E/ReturnPinCheckFast.lean`, the program part of the return-pin
attempt's `okRReturnPinCalls`) tests, at each `blr` site of `g`, every function of the program
(`C.entries`), deciding `indToB C.symbols g h` per entry: `g`'s declarations and indirect-call
signatures are recomputed for each of them. On ruint's test executable (227,551 functions) that
check alone ran for more than an hour, one function after another (#1108).

`returnPinsIdx C Y g` tests the same entries the original test can fail on, with `g`'s facts
computed once (`indToWithB`, `indToWithB_declSet`):

* at a call through the GOT symbol `n`, the entries of the functions named `n` (`Y.byName`);
* at another `blr`, the entries of the functions `g` declares and those of the functions with a
  symbol and the parameter types of one of `g`'s indirect-call signatures (`Y.byTys`): an entry
  outside both has `indToB C.symbols g h = false`.

`returnPinsIdx_eq`: equal to `returnPinsWith C g` at `Y = ReturnPinIdx.of C`. No statement changes.
-/

namespace E2E.LinkCheck
open Backend
set_option autoImplicit false

/-- The entries of `C` by their function's name, and those of a function with a symbol by its
parameter types. -/
structure ReturnPinIdx where
  byName : Std.HashMap String (List ReturnPinEntry)
  byTys : Std.HashMap (List Clif.Ty) (List ReturnPinEntry)

def ReturnPinIdx.of (C : ReturnPinCtx) : ReturnPinIdx where
  byName := groupMulti (fun e => [e.function.name]) C.entries
  byTys := groupMulti (fun e => if (C.symbols e.function.name).isSome then
    [Clif.AbiParam.tys e.function.sig.params] else []) C.entries

/-- An entry's test at the `blr` site `info` (`returnPinSiteWith`'s, without the GOT name). -/
def returnPinEntryOk (to : Clif.Function → Bool) (info : CallInfo) (e : ReturnPinEntry) : Bool :=
  !to e.function || decide (e.arity ≠ info.uses.length) ||
    e.check (info.defs.take e.function.sig.returns.length)

/-- `returnPinSiteWith C g` with the entries it tests precomputed: at a call through the GOT
symbol `n`, `byName n`; at another `blr`, `cands`. -/
def returnPinSiteIdx (C : ReturnPinCtx) (byName : String → List ReturnPinEntry)
    (to : Clif.Function → Bool) (cands : List ReturnPinEntry) (got : Nat → Option String)
    (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match C.direct n with
    | some e => e.check (info.defs.take e.function.sig.returns.length)
    | none => true
  | .reg (.vreg t .int) =>
    match got t with
    | some n => (byName n).all (returnPinEntryOk to info)
    | none => cands.all (returnPinEntryOk to info)
  | _ => true

/-- **`returnPinsWith C g` with `g`'s facts computed once and the entries indexed**
(`returnPinsIdx_eq`). -/
def returnPinsIdx (C : ReturnPinCtx) (Y : ReturnPinIdx) (g : Clif.Function) : Bool :=
  let Ds := declSet g
  let ind := indFreeB g
  let sigs := indSigs g
  let to := indToWithB C.symbols ind (fun n => Ds.contains n) sigs g
  let cands := g.externs.flatMap (fun x => Y.byName.getD x.2.name []) ++
    (if ind then [] else
      (sigs.map fun s => Clif.AbiParam.tys s.params).eraseDups.flatMap fun k => Y.byTys.getD k [])
  let vcp := (C.artifact g).vcp
  allInsts vcp (siteB (returnPinSiteIdx C (fun n => Y.byName.getD n []) to cands (gotOf vcp)))

theorem returnPinIdx_byName (C : ReturnPinCtx) (n : String) (e : ReturnPinEntry) :
    e ∈ (ReturnPinIdx.of C).byName.getD n [] ↔ e ∈ C.entries ∧ e.function.name = n := by
  simp only [ReturnPinIdx.of, mem_groupMulti, List.mem_singleton]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b.symm⟩, fun ⟨a, b⟩ => ⟨a, b.symm⟩⟩

theorem returnPinIdx_byTys (C : ReturnPinCtx) (k : List Clif.Ty) (e : ReturnPinEntry) :
    e ∈ (ReturnPinIdx.of C).byTys.getD k [] ↔ e ∈ C.entries ∧
      (C.symbols e.function.name).isSome = true ∧ k = Clif.AbiParam.tys e.function.sig.params := by
  simp only [ReturnPinIdx.of, mem_groupMulti]
  constructor
  · rintro ⟨he, hk⟩
    by_cases hs : (C.symbols e.function.name).isSome = true
    · simp only [hs, ite_true, List.mem_singleton] at hk
      exact ⟨he, hs, hk⟩
    · simp [hs] at hk
  · rintro ⟨he, hs, hk⟩
    simp [he, hs, hk]

/-- The candidates of `returnPinsIdx` at `Y = ReturnPinIdx.of C`. -/
def returnPinCands (C : ReturnPinCtx) (g : Clif.Function) : List ReturnPinEntry :=
  g.externs.flatMap (fun x => (ReturnPinIdx.of C).byName.getD x.2.name []) ++
    (if indFreeB g then [] else ((indSigs g).map fun s => Clif.AbiParam.tys s.params).eraseDups.flatMap
      fun k => (ReturnPinIdx.of C).byTys.getD k [])

theorem returnPinCands_sub (C : ReturnPinCtx) (g : Clif.Function) :
    ∀ x ∈ returnPinCands C g, x ∈ C.entries := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨e, -, he⟩ := List.mem_flatMap.1 h
    exact ((returnPinIdx_byName C _ x).1 he).1
  · split at h
    · simp at h
    · obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 h
      exact ((returnPinIdx_byTys C k x).1 hk).1

/-- An entry `g` may enter through an address is a candidate. -/
theorem returnPinCands_of (C : ReturnPinCtx) (g : Clif.Function) (x : ReturnPinEntry)
    (hx : x ∈ C.entries)
    (hto : indToWithB C.symbols (indFreeB g) (fun n => (declSet g).contains n) (indSigs g) g
      x.function = true) :
    x ∈ returnPinCands C g := by
  unfold returnPinCands
  by_cases hd : (declSet g).contains x.function.name = true
  · refine List.mem_append.2 (Or.inl ?_)
    have hd' : declB g x.function.name = true := by
      rw [← declSet_contains]; exact hd
    simp only [declB, List.any_eq_true, beq_iff_eq] at hd'
    obtain ⟨e, he, hen⟩ := hd'
    exact List.mem_flatMap.2 ⟨e, he, (returnPinIdx_byName C _ x).2 ⟨hx, hen.symm⟩⟩
  · refine List.mem_append.2 (Or.inr ?_)
    have hd0 : (declSet g).contains x.function.name = false := by simpa using hd
    simp only [indToWithB, mayWithB, hd0, Bool.false_or, Bool.false_and, Bool.and_eq_true,
      Bool.not_eq_true'] at hto
    obtain ⟨⟨hi, hS⟩, hrest⟩ := hto
    rw [hi]
    simp only [Bool.false_eq_true, ite_false]
    rw [indMatchWithB_sig] at hrest
    obtain ⟨s, hs, hsm⟩ := List.any_eq_true.1 hrest
    have hab : s.abiMatch x.function.sig = true := (Bool.and_eq_true _ _ ▸ hsm).1
    refine List.mem_flatMap.2 ⟨Clif.AbiParam.tys s.params, ?_, ?_⟩
    · exact List.mem_eraseDups.2 (List.mem_map.2 ⟨s, hs, rfl⟩)
    · exact (returnPinIdx_byTys C _ x).2 ⟨hx, hS, (tys_of_abiMatch hab).symm⟩

theorem returnPinSiteIdx_eq (C : ReturnPinCtx) (g : Clif.Function) :
    returnPinSiteIdx C (fun n => (ReturnPinIdx.of C).byName.getD n [])
      (indToWithB C.symbols (indFreeB g) (fun n => (declSet g).contains n) (indSigs g) g)
      (returnPinCands C g) (gotOf (C.artifact g).vcp) = returnPinSiteWith C g := by
  funext info
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n => rfl
  | reg r =>
    cases r with
    | vreg t c =>
      cases c with
      | float => rfl
      | int =>
        simp only [returnPinSiteIdx, returnPinSiteWith]
        cases hg : gotOf (C.artifact g).vcp t with
        | some n =>
          simp only
          refine Eq.symm ((all_sub_eq (c := (ReturnPinIdx.of C).byName.getD n [])
            (fun x hx hp => ?_) (fun x hx => ((returnPinIdx_byName C n x).1 hx).1)).trans ?_)
          · refine (returnPinIdx_byName C n x).2 ⟨hx, ?_⟩
            simp only [Bool.or_eq_false_iff] at hp
            simpa using hp.1.1.2
          · apply Bool.eq_iff_iff.2
            simp only [List.all_eq_true]
            refine forall₂_congr fun x hx => ?_
            rw [((returnPinIdx_byName C n x).1 hx).2, ← indToWithB_declSet]
            simp [returnPinEntryOk]
        | none =>
          simp only [Bool.or_false]
          refine Eq.symm ((all_sub_eq (c := returnPinCands C g) (fun x hx hp => ?_)
            (returnPinCands_sub C g)).trans ?_)
          · refine returnPinCands_of C g x hx ?_
            simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hp
            rw [indToWithB_declSet]
            exact hp.1.1
          · rw [← indToWithB_declSet]
            rfl
    | _ => rfl

theorem returnPinsIdx_eq (C : ReturnPinCtx) (g : Clif.Function) :
    returnPinsIdx C (ReturnPinIdx.of C) g = returnPinsWith C g := by
  unfold returnPinsIdx returnPinsWith
  dsimp only
  rw [← returnPinSiteIdx_eq C g]
  rfl

end E2E.LinkCheck
