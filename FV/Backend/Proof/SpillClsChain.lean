import FV.Backend.Proof.SpillClsRun
import FV.Backend.Proof.LowerComplete
import FV.Backend.Proof.SpillLocal

/-!
# The lowering states along `lowerFunction`'s loop (V4 classes)

`ClsStep` (classes only appended, one per fresh vreg) along the recorded lowering: every ISLE
call (`runTerm_cls`), the `try_call` vregs (`tryRegsOf_cls`: fresh int vregs of their
classes), the statement loop, the terminator, the block loop (`lowB_chain`: every recorded
state lies between the start and the final state). The alias resolution keeps the classes of
registers whose aliases are int vregs of int values (`resolve_cls`).
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp

theorem clsStep_clear (s : LState) : ClsStep s { s with emitted := #[] } := clsStep_of_eq rfl rfl

theorem clsStep_unclear (s : LState) : ClsStep { s with emitted := #[] } s := clsStep_of_eq rfl rfl

/-- Every ISLE run of the driver only appends classes. -/
theorem runTerm_cls {ctx : Ctx} {term : String} {args : List V} {s : LState} {out : Option V}
    {s' : LState} {tr : List RuleId} (h : runTerm ctx term args s = .ok (out, s', tr)) : ClsStep s s' := by
  obtain ⟨t, tr', -, h⟩ := runTerm_apply h
  exact (presAt (R := ClsStep) clsStep_refl (fun _ _ _ => clsStep_trans)
    (fun term vs s v s' h => (externCtor_cls ctx term vs s v s' h).step) 1000000).apply _ _ _ _ _ _ _ _ h

theorem foldl_push_size {β : Type} (l : List β) (F : Array Reg × LState → β → Array Reg × LState)
    (hF : ∀ q b, (F q b).1.size = q.1.size + 1) : ∀ q, (l.foldl F q).1.size = q.1.size + l.length := by
  induction l with
  | nil => intro q; rfl
  | cons b l ih => intro q; rw [List.foldl_cons, ih, hF]; simp; omega

/-- An int vreg of the class the state records. -/
def IntCls (cls : Array RegClass) (r : Reg) : Prop := RegCls cls r ∧ ∃ n, r = .vreg n .int

theorem intCls_step {st st' : LState} (h : ClsStep st st') {r : Reg} (hr : IntCls st.classes r) :
    IntCls st'.classes r := ⟨regCls_step h hr.1, hr.2⟩

/-- **The `try_call` vregs** are fresh int vregs of their classes. -/
theorem tryRegsOf_cls {sig : Clif.Signature} {st st1 : LState} {trs : List Reg × List Reg}
    (h : tryRegsOf sig st = some (trs, st1)) :
    ClsStep st st1 ∧ (Sz st → ∀ r ∈ trs.1 ++ trs.2, IntCls st1.classes r) := by
  unfold tryRegsOf at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  rename_i ps hps
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  let F1 := fun (x : Array Reg × LState) (_ : Reg) =>
    (x.1.push (x.2.fresh RegClass.int).1, (x.2.fresh RegClass.int).2)
  have h1 := foldl_inv (fun x : Array Reg × LState =>
      ClsStep st x.2 ∧ (Sz st → ∀ r ∈ x.1.toList, IntCls x.2.classes r)) F1 ps (#[], st)
    ⟨clsStep_refl st, by simp⟩ (by
      intro _ _ x ⟨hs, hr⟩
      have hs1 := clsStep_fresh x.2 .int
      refine ⟨clsStep_trans hs hs1, fun hsz r hrm => ?_⟩
      simp only [F1, Array.toList_push, List.mem_append, List.mem_singleton] at hrm
      rcases hrm with hrm | rfl
      · exact intCls_step hs1 (hr hsz r hrm)
      · exact ⟨fresh_cls (sz_step hs hsz) .int, _, rfl⟩)
  have hsize : (ps.foldl F1 (#[], st)).1.size = ps.length := by
    rw [foldl_push_size ps F1 (fun _ _ => by simp [F1])]; simp
  generalize ps.foldl F1 (#[], st) = q1 at h1 hsize
  obtain ⟨rets, s1⟩ := q1
  obtain ⟨hs1, hr1⟩ := h1
  generalize hq2 : List.foldl _ (#[], s1) (payloadRegs sig.callConv) = q2
  have h2 : ClsStep s1 q2.2 ∧ (Sz st → ∀ r ∈ q2.1.toList, IntCls q2.2.classes r) := by
    rw [← hq2]
    refine foldl_inv (fun x : Array Reg × LState =>
      ClsStep s1 x.2 ∧ (Sz st → ∀ r ∈ x.1.toList, IntCls x.2.classes r)) _ _ _
      ⟨clsStep_refl s1, by simp⟩ ?_
    intro p _ x ⟨hs, hr⟩
    try dsimp only
    split
    · rename_i i hi
      refine ⟨hs, fun hsz r hrm => ?_⟩
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hrm
      rcases hrm with hrm | rfl
      · exact hr hsz r hrm
      · have hil : i < rets.size := by
          rw [hsize]
          obtain ⟨hlt, -⟩ := List.idxOf?_eq_some_iff.mp hi
          exact hlt
        rw [getElem!_pos rets i hil]
        exact intCls_step hs (hr1 hsz _ (by simp))
    · have hs2 := clsStep_fresh x.2 .int
      refine ⟨clsStep_trans hs hs2, fun hsz r hrm => ?_⟩
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hrm
      rcases hrm with hrm | rfl
      · exact intCls_step hs2 (hr hsz r hrm)
      · exact ⟨fresh_cls (sz_step (clsStep_trans hs1 hs) hsz) .int, _, rfl⟩
  obtain ⟨hs2, hr2⟩ := h2
  refine ⟨clsStep_trans hs1 hs2, fun hsz r hr => ?_⟩
  simp only [List.mem_append] at hr
  rcases hr with hr | hr
  · exact intCls_step hs2 (hr1 hsz r (by simpa using hr))
  · exact hr2 hsz r (by simpa using hr)

/-! ## The loop -/

/-- The driver's calls only append classes. -/
def StepsCls (call : StmtCall) (tcall : TermCallF) (ycall : TryCallF) : Prop :=
  (∀ ii s out s' tr, call ii s = .ok (out, s', tr) → ClsStep s s') ∧
  (∀ ti d t ls s out s' tr, tcall ti d t ls s = .ok (out, s', tr) → ClsStep s s') ∧
  ∀ ti d trs ls s out s' tr, ycall ti d trs ls s = .ok (out, s', tr) → ClsStep s s'

theorem stepsCls_driver (ctx : Ctx) : StepsCls (stmtCall ctx) (termCallF ctx) (tryCallF ctx) :=
  ⟨fun _ _ _ _ _ h => runTerm_cls h, fun _ _ _ _ _ _ _ _ h => runTerm_cls h,
    fun _ _ _ _ _ _ _ _ h => runTerm_cls h⟩

theorem lowStmts_chain {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF}
    (hm : StepsCls call tcall ycall) :
    ∀ {ss : List Clif.Stmt} {ii : Nat} {st : LState} {sls : List SLow} {stE : LState},
      lowStmts call ii ss st = some (sls, stE) →
      ClsStep st stE ∧ ∀ sl ∈ sls, ClsStep st sl.st ∧ ClsStep sl.st' stE
  | [], _, _, _, _, h => by
    simp only [lowStmts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨clsStep_refl _, by simp⟩
  | _ :: ss, ii, st, sls, stE, h => by
    simp only [lowStmts] at h
    split at h
    · rename_i out st' tr' hc
      split at h
      · cases hrec : lowStmts call (ii + 1) ss { st' with emitted := #[] } with
        | none => rw [hrec] at h; cases h
        | some q =>
          rw [hrec] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := lowStmts_chain hm hrec
          have h0 := hm.1 _ _ _ _ _ hc
          have h0' : ClsStep st st' := clsStep_trans (clsStep_clear st) h0
          refine ⟨clsStep_trans h0' (clsStep_trans (clsStep_clear st') h1), fun sl hsl => ?_⟩
          rcases List.mem_cons.mp hsl with rfl | hsl
          · exact ⟨clsStep_clear st, clsStep_trans (clsStep_clear st') h1⟩
          · obtain ⟨a, b⟩ := h2 sl hsl
            exact ⟨clsStep_trans h0' (clsStep_trans (clsStep_clear st') a), b⟩
      · cases h
    · cases h

theorem lowTerm_chain {f : Clif.Function} {tcall : TermCallF} {ycall : TryCallF} {call : StmtCall}
    (hm : StepsCls call tcall ycall) {ti : Nat} {t : Clif.Terminator} {tst : LState} {nl : Nat}
    {data : V} {targets : List Label} {tl : Option TryLow} {tst' : LState} {nl' : Nat}
    (h : lowTerm f tcall ycall ti t tst nl = some (data, targets, tl, tst', nl')) :
    ClsStep tst tst' ∧ ∀ T, tl = some T → ClsStep tst T.st1 := by
  obtain ⟨hn, hy⟩ := lowTerm_spec h
  cases ht : t.isTry with
  | false =>
    obtain ⟨htl, -, out, tr, hc⟩ := hn ht
    exact ⟨hm.2.1 _ _ _ _ _ _ _ _ hc, fun T hT => by rw [htl] at hT; cases hT⟩
  | true =>
    obtain ⟨et, het⟩ : ∃ et, IsTryWith t et := by
      cases t <;> simp [Clif.Terminator.isTry] at ht
      · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
      · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
    obtain ⟨T, hT, -, -, -, hr, -, out, tr, hc⟩ := hy et het
    have h1 := (tryRegsOf_cls hr).1
    have h2 := hm.2.2 _ _ _ _ _ _ _ _ hc
    refine ⟨clsStep_trans h1 (clsStep_trans (clsStep_clear _) h2), fun T' hT' => ?_⟩
    rw [hT] at hT'; cases hT'; exact h1

/-- Every state the recorded lowering of blocks `Bs` passes lies between its start and its end. -/
theorem lowB_chain {f : Clif.Function} {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF}
    (hm : StepsCls call tcall ycall) :
    ∀ (Bs : List Clif.Block) (start : Nat) (st : LState) (nl : Nat) (bl : List BLow) (st' : LState)
      (nl' : Nat), lowB f call tcall ycall start Bs st nl = some (bl, st', nl') →
      ClsStep st st' ∧ ∀ L ∈ bl, ClsStep st L.tst ∧ ClsStep L.tst' st' ∧
        (∀ sl ∈ L.sl, ClsStep st sl.st ∧ ClsStep sl.st' st') ∧
        (∀ T, L.tl = some T → ClsStep st T.st1)
  | [], start, st, nl, bl, st', nl', h => by
    simp only [lowB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨clsStep_refl _, by simp⟩
  | B :: Bs, start, st, nl, bl, st', nl', h => by
    rw [lowB_cons] at h
    split at h
    · cases h
    rename_i sls stE hstm
    split at h
    · rename_i data targets tl tst' nl1 hterm
      cases hr : lowB f call tcall ycall (start + B.body.length + 1) Bs { tst' with emitted := #[] } nl1 with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        obtain ⟨bl1, st1, nl2⟩ := r
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨s1, s2⟩ := lowStmts_chain hm hstm
        obtain ⟨t1, t2⟩ := lowTerm_chain hm hterm
        obtain ⟨r1, r2⟩ := lowB_chain hm Bs _ _ _ bl1 _ _ hr
        have e1 : ClsStep st { stE with emitted := #[] } := clsStep_trans s1 (clsStep_clear stE)
        have e2 : ClsStep tst' st1 := clsStep_trans (clsStep_clear tst') r1
        refine ⟨clsStep_trans e1 (clsStep_trans t1 e2), fun L hL => ?_⟩
        rcases List.mem_cons.mp hL with rfl | hL
        · refine ⟨e1, e2, fun sl hsl => ?_, fun T hT => clsStep_trans e1 (t2 T hT)⟩
          obtain ⟨a, b⟩ := s2 sl hsl
          exact ⟨a, clsStep_trans b (clsStep_trans (clsStep_clear stE) (clsStep_trans t1 e2))⟩
        · have e3 : ClsStep st { tst' with emitted := #[] } :=
            clsStep_trans e1 (clsStep_trans t1 (clsStep_clear tst'))
          obtain ⟨a1, a2, a3, a4⟩ := r2 L hL
          exact ⟨clsStep_trans e3 a1, a2, fun sl hsl => ⟨clsStep_trans e3 (a3 sl hsl).1, (a3 sl hsl).2⟩,
            fun T hT => clsStep_trans e3 (a4 T hT)⟩
    · cases h

/-! ## Alias resolution -/

/-- The alias resolution keeps the classes of registers when every alias goes from an int vreg
to an int vreg. -/
theorem resolve_cls {cls : Array RegClass} {a : Array (Option Nat)}
    (ha : ∀ n o : Nat, (a[n]?).join = some o → cls[n]? = some RegClass.int ∧ cls[o]? = some RegClass.int) :
    ∀ k r, RegCls cls r → RegCls cls (lowerFunction.resolve a k r) := by
  have hc : ∀ k n c, cls[n]? = some c → cls[chaseF (fun n => (a[n]?).join) k n]? = some c := by
    intro k
    induction k with
    | zero => intro n c h; exact h
    | succ k ih =>
      intro n c h
      simp only [chaseF]
      split
      · rename_i o ho
        obtain ⟨h1, h2⟩ := ha n o ho
        rw [h1] at h; cases h
        exact ih o _ h2
      · exact h
  intro k r hr
  cases r with
  | vreg n c =>
    rw [resolve_vreg]
    exact regCls_vreg.mpr (hc k n c (regCls_vreg.mp hr))
  | _ => cases k <;> exact hr

end Backend.Proof.Spill
