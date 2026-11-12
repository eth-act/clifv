import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.LowerLoopCtxT
import FV.E2E.RegLevelArgs
import FV.Backend.Proof.EntryClass
import FV.Backend.Proof.AbiClassRegs

/-!
Non-vacuity of the widened control-form check (S11e5 Stage C, slice 5): `ctlCheck` accepts
class-compatible `Args`/`Rets` pairs (`argPairOk`, `retPairOk`: an f32/f64 vreg in v0–v7), so
`lowerRFunc` lowers a function with `f32`/`f64` parameters and returns; the integer check
`ctlCheckInt` rejected it ("control-form check (ctlCheck) failed"). The function is in the typed
lowering's input conditions (`Dominated`, `LowerScopeT`). Old acceptance implies new acceptance
(`ctlCheck_of_int`) on an integer function. Checks by `native_decide` (witness only).
`lake build FVTest.Backend.FloatCtlT`.
-/

open Backend Backend.Proof Backend.Proof.Driver

namespace FloatCtlT

/-- The first function of a CLIF text. -/
def fnOfText (src : String) : Clif.Function :=
  match (Clif.parseFile src).funcs with
  | p :: _ => match p.func with
    | .ok f => f
    | .error _ => default
  | [] => default

/-- `prepareChecked (lowerFunction f)` (`default` if either fails). -/
def vcpOf (f : Clif.Function) : VCode :=
  match lowerFunction f >>= prepareChecked with
  | .ok vc => vc
  | .error _ => default

/-- `(f64, i64, f32) -> f64`: float parameters in v0/v1, the integer one in x0, the result in
v0. -/
def fCtl : Clif.Function := fnOfText
  "function %ctl(f64, i64, f32) -> f64 {
block0(v0: f64, v1: i64, v2: f32):
    store v2, v1
    return v0
}
"

/-- An integer function (`(i64, i64) -> i64`). -/
def fInt : Clif.Function := fnOfText
  "function %int(i64, i64) -> i64 {
block0(v0: i64, v1: i64):
    v2 = iadd v0, v1
    return v2
}
"

-- the prepared code carries float `Args`/`Rets` pairs in v registers
#guard (lowerFunction fCtl >>= prepareChecked).toBool
#guard (vcpOf fCtl).blocks.any fun vb => vb.insts.any fun
  | .args ps => ps.any (fun (r, p) => r.isVregFloat && p == .v 0) &&
      ps.any (fun (r, p) => r.isVregFloat && p == .v 1) && ps.any (fun (r, p) => r.isVregInt && p == .x 0)
  | _ => false
#guard (vcpOf fCtl).blocks.any fun vb => vb.insts.any fun
  | .rets us => us.any fun (r, p) => r.isVregFloat && p == .v 0
  | _ => false
-- the spill allocation lowers now; before the widening it did not
#guard (lowerRFunc (vcpOf fCtl) (spillAlloc (vcpOf fCtl))).toBool

/-- **The widened check accepts** the float function's spill allocation. -/
theorem ctlCheck_fCtl : ctlCheck (vcpOf fCtl) (spillAlloc (vcpOf fCtl)) = true := by native_decide

/-- **The integer check rejected it.** -/
theorem ctlCheckInt_fCtl : ctlCheckInt (vcpOf fCtl) (spillAlloc (vcpOf fCtl)) = false := by
  native_decide

/-- Non-vacuity of `ctlCheck_of_int`: the integer check accepts an integer function's spill
allocation (so does the widened one). -/
theorem ctlCheckInt_fInt : ctlCheckInt (vcpOf fInt) (spillAlloc (vcpOf fInt)) = true := by
  native_decide

example : ctlCheck (vcpOf fInt) (spillAlloc (vcpOf fInt)) = true := ctlCheck_of_int ctlCheckInt_fInt

/-- Non-vacuity of `ctlInstOk_of_int`. -/
example : ctlInstOk 0 0 (.args [(.vreg 3 .int, .x 0)]) = true := ctlInstOk_of_int (by decide)

/-- The pairs the class facts describe: a float `Args` pair in v1, a float `Rets` pair in v0. -/
example : (∃ n, (Reg.vreg 5 .float, Reg.v 1).1 = .vreg n .int ∧ (Reg.vreg 5 .float, Reg.v 1).2.isArgReg = true) ∨
    (∃ n m, (Reg.vreg 5 .float, Reg.v 1).1 = .vreg n .float ∧ (Reg.vreg 5 .float, Reg.v 1).2 = .v m ∧ m < 8) :=
  argPairOk_cls (by decide)
example : (∃ n c, (Reg.vreg 5 .float, Reg.v 1).1 = .vreg n c) ∧ (Reg.vreg 5 .float, Reg.v 1).2.isArgReg = true :=
  argPairOk_facts (by decide)
example : (∃ n, (Reg.vreg 2 .float, Reg.v 0).1 = .vreg n .int) ∨
    (∃ n m, (Reg.vreg 2 .float, Reg.v 0).1 = .vreg n .float ∧ (Reg.vreg 2 .float, Reg.v 0).2 = .v m ∧ m < 8) := by
  rcases argPairOk_cls (p := (Reg.vreg 2 .float, Reg.v 0)) (by decide) with ⟨n, h, -⟩ | h
  · exact .inl ⟨n, h⟩
  · exact .inr h
example : ∃ n c, (Reg.vreg 2 .float, Reg.v 0).1 = .vreg n c :=
  (argPairOk_facts (p := (Reg.vreg 2 .float, Reg.v 0)) (by decide)).1

theorem lowerFunction_ok_fCtl : (lowerFunction fCtl).toBool = true := by native_decide

/-- The prepared VCode of `fCtl` is `prepareChecked`'s output. -/
theorem vcpOf_fCtl : ∃ vc, lowerFunction fCtl = .ok vc ∧ prepareChecked vc = .ok (vcpOf fCtl) := by
  have h : (lowerFunction fCtl >>= prepareChecked).toBool = true := by native_decide
  unfold vcpOf
  cases hl : lowerFunction fCtl with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    refine ⟨vc, rfl, ?_⟩
    simp only [hl, bind, Except.bind] at h ⊢
    cases hp : prepareChecked vc with
    | error e => rw [hp] at h; cases h
    | ok vcp => rfl

/-- Non-vacuity of `ctlCheck_args`/`ctlCheck_rets` with float pairs: `fCtl`'s `Args` has a float
vreg (fixed to v0) and the widened check holds. -/
theorem ctlCheck_args_fCtl : ∃ vb ds, (vcpOf fCtl).blocks[0]? = some vb ∧ vb.insts[0]? = some (.args ds) ∧
    (∃ p ∈ ds, ∃ n, p.1 = .vreg n .float ∧ p.2 = .v 0) ∧
    ∀ p ∈ ds, (∃ n c, p.1 = .vreg n c) ∧ p.2.isArgReg = true := by
  have h : (match (vcpOf fCtl).blocks[0]? with
    | some vb => match vb.insts[0]? with
      | some (MInst.args ds) => ds.any (fun p => p.1.isVregFloat && p.2 == .v 0)
      | _ => false
    | none => false) = true := by native_decide
  split at h
  · rename_i vb hvb
    split at h
    · rename_i ds hi
      refine ⟨vb, ds, hvb, hi, ?_, (ctlCheck_args ctlCheck_fCtl hvb hi).2.2⟩
      obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
      obtain ⟨r, q⟩ := p
      simp only [Bool.and_eq_true, beq_iff_eq] at hq
      obtain ⟨hr, rfl⟩ := hq
      cases r with
      | vreg n c => cases c <;> simp [Reg.isVregFloat] at hr; exact ⟨_, hp, n, rfl, rfl⟩
      | _ => simp [Reg.isVregFloat] at hr
    · cases h
  · cases h

/-- `fCtl` is `Dominated`. -/
theorem dominated_fCtl : Dominated fCtl := dominated_of (by native_decide)

/-- `fCtl`'s entry parameters have the classes of its signature's (`entryClassOkB`). -/
theorem entryClassOk_fCtl : EntryClassOk fCtl := entryClassOk_of (by native_decide)

-- an entry block whose `f64` parameter sits at an `i64` signature position is rejected
#guard !entryClassOkB (fnOfText
  "function %bad(i64) -> i64 {\nblock0(v0: f64):\n    v1 = bitcast.i64 v0\n    return v1\n}\n")

theorem functionET_fCtl : Compile.functionET fCtl = true := by native_decide

/-- `fCtl` is in the typed lowering's input conditions. -/
theorem scopeT_fCtl : LowerScopeT fCtl where
  subsetT := functionET_fCtl
  nonempty := by native_decide
  noEntryPred := by native_decide
  ctxFacts := by
    intro ctx ranges st0 hb
    have h : (match buildCtx fCtl with
        | .ok (c, _, _) => brIdxOk fCtl c && ctxOkT fCtl c
        | .error _ => false) = true := by native_decide
    rw [hb] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1, (ctxOkT_sound h.2).addr64⟩
  tryRet := by
    have h : fCtl.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    intro B hB et ht
    have := List.all_eq_true.mp h B hB
    rcases ht with ⟨fn, args, he⟩ | ⟨c, args, he⟩ <;> rw [he] at this <;> cases this
  stackLayout := by
    have h : fCtl.blocks.all (fun B => B.body.all fun st => !(st.inst matches .call ..) ) = true := by
      native_decide
    have h2 : fCtl.blocks.all (fun B => !B.term.isTry) = true := by native_decide
    refine ⟨fun B hB st hst fn args e hi _ => ?_, fun B hB fn args et e ht _ => ?_⟩
    · have := List.all_eq_true.mp (List.all_eq_true.mp h B hB) st hst
      rw [hi] at this; cases this
    · have := List.all_eq_true.mp h2 B hB
      rw [ht] at this; cases this
  indStackLayout := by
    have h : (Backend.indSigs fCtl).all (fun s => stackLayoutOk s) = true := by native_decide
    exact fun s hs => List.all_eq_true.mp h s hs

/-! ## Slice 5b: float `Args`/`Rets` meet `SpillInstOk` -/

/-- Non-vacuity of `spillInstOk_retsC`: a `Rets` of a float vreg in v0 and an int vreg in x0. -/
example : Spill.SpillInstOk (.rets (argPairsC [(5, .float, .v 0), (6, .int, .x 0)])) :=
  Spill.spillInstOk_retsC (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact .inr ⟨rfl, 0, by decide, rfl⟩
    · exact .inl ⟨rfl, 0, by decide, rfl⟩) (by decide)

/-- Non-vacuity of `sigArgLocs_regsC`: `fCtl`'s signature places `[v0, x0, v1]`. -/
theorem sigArgLocs_regs_fCtl : ∃ locs n, sigArgLocs fCtl.sig = .ok (locs, n) ∧ locs.length = 3 ∧
    (Spill.locRegs locs).Nodup ∧ Spill.Pw2 Spill.PLoc fCtl.sig.params locs := by
  have h : (match sigArgLocs fCtl.sig with
    | .ok r => r.1.length == 3
    | .error _ => false) = true := by native_decide
  split at h
  · rename_i r hr
    obtain ⟨locs, n⟩ := r
    exact ⟨locs, n, hr, by simpa using h, Spill.sigArgLocs_regsC (by native_decide) hr⟩
  · cases h

/-- The entry block of `fCtl`. -/
def B0 : Clif.Block := fCtl.blocks[0]!

/-- **Non-vacuity of `spillInstOk_entryArgsT`**: the typed entry `Args` of `fCtl` (float
parameters in v0/v1) in its `buildCtx` context meets `SpillInstOk`. -/
theorem entryArgsT_fCtl : ∃ ctx r s, buildCtx fCtl = .ok (ctx, r, s) ∧
    Spill.SpillInstOk (.args (entryRegsT fCtl ctx id B0)) := by
  have hok : (buildCtx fCtl).toBool = true := by native_decide
  cases hb : buildCtx fCtl with
  | error e => rw [hb] at hok; cases hok
  | ok res =>
    obtain ⟨ctx, r, s⟩ := res
    refine ⟨ctx, r, s, rfl, Spill.spillInstOk_entryArgsT (by native_decide) (by native_decide)
      (by native_decide) (fun _ _ => rfl) ?_⟩
    have hc : (match buildCtx fCtl with
        | .ok (c, _, _) => (B0.params.zip fCtl.sig.params).all fun q =>
            decide (valClassOf c q.1.1 = tyClass q.2.ty)
        | .error _ => false) = true := by native_decide
    rw [hb] at hc
    intro i x t sp hbp hs
    have hz : (B0.params.zip fCtl.sig.params)[i]? = some ((x, t), sp) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hbp, hs⟩
    simpa using List.all_eq_true.mp hc _ (List.mem_of_getElem? hz)

end FloatCtlT
