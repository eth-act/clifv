import FV.Compile.Proof.Gen

/-!
# Backward transfer (`Bk`) for every emitter function

`compileExpr`, `compileOp`, … keep a block open (`Bk Good Good`); `finish` and
`compileStmt` close it (`Bk Good Lk`).
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile
open Clif (ValueId BlockId Inst Terminator)
open DSL (Ty IntW)

macro "bk_auto" : tactic => `(tactic| repeat (first
  | exact Bk.pure _
  | exact Bk.inst1_gg _
  | exact Bk.iconstN_gg _ _
  | exact Bk.selectVals_gg _ _ _ _
  | exact Bk.callFn_gg _ _ _
  | exact Bk.errIf_gg _ _
  | exact Bk.newBlock_gg
  | exact Bk.fresh_gg
  | exact Bk.newSlot_gg _
  | exact Bk.freshFor_gg _
  | exact Bk.terminate_gl _
  | exact Bk.switchTo_lg _ _
  | assumption
  | apply Bk.bind
  | split
  | intro _))

theorem Bk.toWordV (t : Ty) (vs : List ValueId) : Bk Good Good (Compile.toWordV t vs) := by
  unfold Compile.toWordV; split <;> bk_auto

theorem Bk.ofWordV (t : Ty) (x : ValueId) : Bk Good Good (Compile.ofWordV t x) := by
  unfold Compile.ofWordV; split <;> bk_auto

theorem Bk.boundsCheck (w : IntW) (n : Nat) (i : ValueId) :
    Bk Good Good (Compile.boundsCheck w n i) := by
  unfold Compile.boundsCheck; bk_auto

theorem Bk.selectElem (t : Ty) (w : IntW) (n : Nat) (i : ValueId) (vs : List ValueId) :
    Bk Good Good (Compile.selectElem t w n i vs) := by
  unfold Compile.selectElem
  exact Bk.foldlM _ (fun _ _ => by bk_auto) _ _

theorem Bk.updateElem (t : Ty) (w : IntW) (n : Nat) (i : ValueId) (e vs : List ValueId) :
    Bk Good Good (Compile.updateElem t w n i e vs) := by
  unfold Compile.updateElem
  exact Bk.bind (Bk.mapM _ (fun _ => by bk_auto) _) fun _ => Bk.pure _

theorem Bk.cloneVals (fc : FnCtx) : ∀ (t : Ty) (vs : List ValueId),
    Bk Good Good (Compile.cloneVals fc t vs)
  | .map _ _, _ => by unfold Compile.cloneVals callRt; bk_auto
  | .prod a b, vs => by
    unfold Compile.cloneVals
    exact Bk.bind (Bk.cloneVals fc a _) fun _ => Bk.bind (Bk.cloneVals fc b _) fun _ => Bk.pure _
  | .vec n t, vs => by
    unfold Compile.cloneVals
    split
    · exact Bk.bind (Bk.mapM _ (fun _ => Bk.cloneVals fc t _) _) fun _ => Bk.pure _
    · exact Bk.pure _
  | .int _, _ | .bool, _ | .unit, _ => by unfold Compile.cloneVals; exact Bk.pure _

theorem Bk.compileExpr (fc : FnCtx) {Γ : List Ty} (env : List (List ValueId)) {t : Ty}
    (e : DSL.Expr Γ t) : Bk Good Good (Compile.compileExpr fc env e) := by
  induction e with
  | var v => exact Bk.pure _
  | clone v => exact Bk.cloneVals fc _ _
  | ilit w x => exact Bk.bind (Bk.iconstN_gg _ _) fun _ => Bk.pure _
  | blit b => exact Bk.bind (Bk.iconstN_gg _ _) fun _ => Bk.pure _
  | unit => exact Bk.pure _
  | ibin op a b iha ihb | icmp op a b iha ihb | band a b iha ihb | bor a b iha ihb =>
    exact Bk.bind iha fun _ => Bk.bind ihb fun _ => Bk.bind (Bk.inst1_gg _) fun _ => Bk.pure _
  | inot a ih => exact Bk.bind ih fun _ => Bk.bind (Bk.inst1_gg _) fun _ => Bk.pure _
  | bnot a ih =>
    exact Bk.bind ih fun _ => Bk.bind (Bk.iconstN_gg _ _) fun _ =>
      Bk.bind (Bk.inst1_gg _) fun _ => Bk.pure _
  | cast op w' a ih =>
    refine Bk.bind ih fun _ => ?_
    simp only
    split
    · exact Bk.bind (Bk.inst1_gg _) fun _ => Bk.pure _
    · split
      · split <;> exact Bk.bind (Bk.inst1_gg _) fun _ => Bk.pure _
      · exact Bk.pure _
  | cond c a b ihc iha ihb =>
    exact Bk.bind ihc fun _ => Bk.bind iha fun _ => Bk.bind ihb fun _ =>
      Bk.selectVals_gg _ _ _ _
  | pair a b iha ihb => exact Bk.bind iha fun _ => Bk.bind ihb fun _ => Bk.pure _
  | fst p ih | snd p ih | vrepl n p ih => exact Bk.bind ih fun _ => Bk.pure _
  | mapEmpty => exact Bk.callFn_gg _ _ _
  | mapContains m k ih =>
    exact Bk.bind ih fun _ => Bk.bind (Bk.toWordV _ _) fun _ => Bk.callFn_gg _ _ _

theorem Bk.compileExprs (fc : FnCtx) {Γ : List Ty} (env : List (List ValueId)) {σ : List Ty}
    (es : DSL.Exprs Γ σ) : Bk Good Good (Compile.compileExprs fc env es) := by
  induction es with
  | nil => exact Bk.pure _
  | cons e es ih =>
    simp only [Compile.compileExprs]
    exact Bk.bind (Bk.compileExpr fc env e) fun _ => Bk.bind ih fun _ => Bk.pure _

theorem Bk.compileOp (fc : FnCtx) {Γ : List Ty} (env : List (List ValueId)) {t : Ty}
    (o : DSL.Op Γ t) : Bk Good Good (Compile.compileOp fc env o) := by
  have he := fun {t : Ty} (e : DSL.Expr Γ t) => Bk.compileExpr fc env e
  cases o with
  | iop op a b =>
    refine Bk.bind (he a) fun _ => Bk.bind (he b) fun _ => ?_
    cases op
    · exact Bk.bind (Bk.inst1_gg _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ =>
        Bk.bind (Bk.errIf_gg _ _) fun _ => Bk.pure _
    · exact Bk.bind (Bk.inst1_gg _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ =>
        Bk.bind (Bk.errIf_gg _ _) fun _ => Bk.pure _
    · exact Bk.bind (Bk.inst1_gg _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ =>
        Bk.bind (Bk.iconstN_gg _ _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ =>
        Bk.bind (Bk.errIf_gg _ _) fun _ => Bk.pure _
    · exact Bk.bind (Bk.iconstN_gg _ _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ =>
        Bk.bind (Bk.errIf_gg _ _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ => Bk.pure _
    · exact Bk.bind (Bk.iconstN_gg _ _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ =>
        Bk.bind (Bk.errIf_gg _ _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ => Bk.pure _
  | vget v i =>
    simp only [Compile.compileOp]
    exact Bk.bind (he i) fun _ => Bk.bind (Bk.boundsCheck _ _ _) fun _ => Bk.selectElem _ _ _ _ _
  | mapGet m k =>
    simp only [Compile.compileOp, callRt]
    refine Bk.bind (he k) fun _ => Bk.bind (Bk.toWordV _ _) fun _ => ?_
    refine Bk.bind (Bk.newSlot_gg _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ => ?_
    refine Bk.bind (Bk.callFn_gg _ _ _) fun _ => Bk.bind (Bk.iconstN_gg _ _) fun _ => ?_
    refine Bk.bind Bk.newBlock_gg fun _ => Bk.bind (Bk.terminate_gl _) fun _ => ?_
    refine Bk.bind (Bk.switchTo_lg _ _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ => ?_
    exact Bk.ofWordV _ _

theorem Bk.storeVals (p : ValueId) (tys : List Clif.Ty) (vs : List ValueId) :
    Bk Good Good (Compile.storeVals p tys vs) := by
  unfold Compile.storeVals
  exact Bk.forM _ (fun _ => Bk.emitStmt_gg _ _) _

theorem Bk.loadVals (p : ValueId) (tys : List Clif.Ty) : Bk Good Good (Compile.loadVals p tys) := by
  unfold Compile.loadVals
  exact Bk.mapM _ (fun _ => Bk.inst1_gg _) _

theorem Bk.finish (fc : FnCtx) (kont : Cont) (vs : List ValueId) :
    Bk Good Lk (Compile.finish fc kont vs) := by
  cases kont with
  | jump b => exact Bk.terminate_gl _
  | ret =>
    simp only [Compile.finish]
    refine Bk.bind (Bk.iconstN_gg _ _) fun _ => ?_
    split
    · exact Bk.bind (Bk.storeVals _ _ _) fun _ => Bk.terminate_gl _
    · exact Bk.terminate_gl _

theorem Bk.compileStmt (fc : FnCtx) {Γ : List Ty} {τ : Ty} (s : DSL.Stmt Γ τ) :
    ∀ (env : List (List ValueId)) (kont : Cont), Bk Good Lk (Compile.compileStmt fc env s kont) := by
  induction s with
  | ret e =>
    intro env kont
    exact Bk.bind (Bk.compileExpr fc env e) fun _ => Bk.finish _ _ _
  | throw e =>
    intro env kont
    exact Bk.bind (Bk.iconstN_gg _ _) fun _ => Bk.terminate_gl _
  | op o =>
    intro env kont
    exact Bk.bind (Bk.compileOp fc env o) fun _ => Bk.finish _ _ _
  | call name body args =>
    intro env kont
    simp only [Compile.compileStmt]
    refine Bk.bind (Bk.compileExprs fc env args) fun argv => ?_
    split
    · exact Bk.bind (Bk.newSlot_gg _) fun _ => Bk.bind (Bk.inst1_gg _) fun _ =>
        Bk.bind (Bk.pure _) fun _ => Bk.bind (Bk.callFn_gg _ _ _) fun _ =>
        Bk.bind Bk.newBlock_gg fun _ => Bk.bind (Bk.terminate_gl _) fun _ =>
        Bk.bind (Bk.switchTo_lg _ _) fun _ => by
          split
          · exact Bk.bind (Bk.loadVals _ _) fun _ => Bk.finish _ _ _
          · exact Bk.bind (Bk.pure _) fun _ => Bk.finish _ _ _
    · exact Bk.bind (Bk.pure _) fun _ => Bk.bind (Bk.callFn_gg _ _ _) fun _ =>
        Bk.bind Bk.newBlock_gg fun _ => Bk.bind (Bk.terminate_gl _) fun _ =>
        Bk.bind (Bk.switchTo_lg _ _) fun _ => by
          split
          · exact Bk.bind (Bk.loadVals _ _) fun _ => Bk.finish _ _ _
          · exact Bk.bind (Bk.pure _) fun _ => Bk.finish _ _ _
  | let_ e k ih =>
    intro env kont
    exact Bk.bind (Bk.compileExpr fc env e) fun _ => ih _ _
  | letPair e k ih =>
    intro env kont
    exact Bk.bind (Bk.compileExpr fc env e) fun _ => ih _ _
  | bind s k ihs ihk =>
    intro env kont
    refine Bk.bind Bk.newBlock_gg fun _ => Bk.bind (Bk.freshFor_gg _) fun _ => ?_
    exact Bk.bind (ihs _ _) fun _ => Bk.bind (Bk.switchTo_lg _ _) fun _ => ihk _ _
  | set v e k ih =>
    intro env kont
    exact Bk.bind (Bk.compileExpr fc env e) fun _ => ih _ _
  | vset v i e k ih =>
    intro env kont
    exact Bk.bind (Bk.compileExpr fc env i) fun _ => Bk.bind (Bk.compileExpr fc env e) fun _ =>
      Bk.bind (Bk.boundsCheck _ _ _) fun _ => Bk.bind (Bk.updateElem _ _ _ _ _ _) fun _ => ih _ _
  | mapInsert v key val k ih =>
    intro env kont
    simp only [Compile.compileStmt, callRt]
    exact Bk.bind (Bk.compileExpr fc env key) fun _ => Bk.bind (Bk.toWordV _ _) fun _ =>
      Bk.bind (Bk.compileExpr fc env val) fun _ => Bk.bind (Bk.toWordV _ _) fun _ =>
      Bk.bind (Bk.callFn_gg _ _ _) fun _ => ih _ _
  | ite c t e iht ihe =>
    intro env kont
    refine Bk.bind (Bk.compileExpr fc env c) fun _ => Bk.bind Bk.newBlock_gg fun _ => ?_
    refine Bk.bind Bk.newBlock_gg fun _ => Bk.bind (Bk.terminate_gl _) fun _ => ?_
    refine Bk.bind (Bk.switchTo_lg _ _) fun _ => Bk.bind (iht _ _) fun _ => ?_
    exact Bk.bind (Bk.switchTo_lg _ _) fun _ => ihe _ _
  | forRange n init body ih =>
    intro env kont
    refine Bk.bind (Bk.compileExpr fc env init) fun _ => Bk.bind Bk.newBlock_gg fun _ => ?_
    refine Bk.bind Bk.fresh_gg fun _ => Bk.bind (Bk.freshFor_gg _) fun _ => ?_
    refine Bk.bind (Bk.iconstN_gg _ _) fun _ => Bk.bind (Bk.terminate_gl _) fun _ => ?_
    refine Bk.bind (Bk.switchTo_lg _ _) fun _ => Bk.bind (Bk.iconstN_gg _ _) fun _ => ?_
    refine Bk.bind (Bk.inst1_gg _) fun _ => Bk.bind Bk.newBlock_gg fun _ => ?_
    refine Bk.bind Bk.newBlock_gg fun _ => Bk.bind Bk.newBlock_gg fun _ => ?_
    refine Bk.bind (Bk.terminate_gl _) fun _ => Bk.bind (Bk.switchTo_lg _ _) fun _ => ?_
    refine Bk.bind (ih _ _) fun _ => Bk.bind (Bk.freshFor_ll _) fun _ => ?_
    refine Bk.bind (Bk.switchTo_lg _ _) fun _ => Bk.bind (Bk.iconstN_gg _ _) fun _ => ?_
    refine Bk.bind (Bk.inst1_gg _) fun _ => Bk.bind (Bk.terminate_gl _) fun _ => ?_
    exact Bk.bind (Bk.switchTo_lg _ _) fun _ => Bk.finish _ _ _

end Compile.Proof
