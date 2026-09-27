import FV.Compile.Proof.Gen

/-!
# One-step unfolding of `compileExpr` runs (all by `rfl`)
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile
open Clif (ValueId Inst)
open DSL (Ty IntW)

variable (fc : FnCtx) {Γ : List Ty} (env : List (List ValueId)) (cg : CG)

theorem run_var {t : Ty} (v : DSL.Var Γ t) :
    (compileExpr fc env (.var v)).run cg = (env.getD v.idx [], cg) := rfl

theorem run_clone {t : Ty} (v : DSL.Var Γ t) :
    (compileExpr fc env (.clone v)).run cg = (cloneVals fc t (env.getD v.idx [])).run cg := rfl

theorem run_ilit (w : IntW) (x : BitVec w.bits) :
    (compileExpr fc env (Γ := Γ) (.ilit w x)).run cg =
      ([cg.nextVal], ((iconstN (intTy w) x.toNat).run cg).2) := rfl

theorem run_blit (b : Bool) :
    (compileExpr fc env (Γ := Γ) (.blit b)).run cg =
      ([cg.nextVal], ((iconstN .i8 (if b then 1 else 0)).run cg).2) := rfl

theorem run_unit : (compileExpr fc env (Γ := Γ) .unit).run cg = ([], cg) := rfl

theorem run_ibin {w : IntW} (op : DSL.IBin) (a b : DSL.Expr Γ (.int w)) :
    (compileExpr fc env (.ibin op a b)).run cg =
      ([((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).2.nextVal],
       ((inst1 (.binary (IBin.clif op) (intTy w) (((compileExpr fc env a).run cg).1.headD 0)
          (((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).1.headD 0))).run
          ((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).2).2) := rfl

theorem run_icmp {w : IntW} (op : DSL.ICmp) (a b : DSL.Expr Γ (.int w)) :
    (compileExpr fc env (.icmp op a b)).run cg =
      ([((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).2.nextVal],
       ((inst1 (.icmp (ICmp.clif op) (intTy w) (((compileExpr fc env a).run cg).1.headD 0)
          (((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).1.headD 0))).run
          ((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).2).2) := rfl

theorem run_band (a b : DSL.Expr Γ .bool) :
    (compileExpr fc env (.band a b)).run cg =
      ([((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).2.nextVal],
       ((inst1 (.binary .band .i8 (((compileExpr fc env a).run cg).1.headD 0)
          (((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).1.headD 0))).run
          ((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).2).2) := rfl

theorem run_bor (a b : DSL.Expr Γ .bool) :
    (compileExpr fc env (.bor a b)).run cg =
      ([((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).2.nextVal],
       ((inst1 (.binary .bor .i8 (((compileExpr fc env a).run cg).1.headD 0)
          (((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).1.headD 0))).run
          ((compileExpr fc env b).run ((compileExpr fc env a).run cg).2).2).2) := rfl

theorem run_inot {w : IntW} (a : DSL.Expr Γ (.int w)) :
    (compileExpr fc env (.inot a)).run cg =
      ([((compileExpr fc env a).run cg).2.nextVal],
       ((inst1 (.unary .bnot (intTy w) (((compileExpr fc env a).run cg).1.headD 0))).run
          ((compileExpr fc env a).run cg).2).2) := rfl

theorem run_bnot (a : DSL.Expr Γ .bool) :
    (compileExpr fc env (.bnot a)).run cg =
      ([((compileExpr fc env a).run cg).2.nextVal + 1],
       ((inst1 (.binary .bxor .i8 (((compileExpr fc env a).run cg).1.headD 0)
          ((compileExpr fc env a).run cg).2.nextVal)).run
          ((iconstN .i8 1).run ((compileExpr fc env a).run cg).2).2).2) := rfl

theorem run_cast {w : IntW} (op : DSL.Cast) (w' : IntW) (a : DSL.Expr Γ (.int w)) :
    (compileExpr fc env (.cast op w' a)).run cg =
      if w'.bits < w.bits then
        ([((compileExpr fc env a).run cg).2.nextVal],
         ((inst1 (.ireduce (intTy w') (((compileExpr fc env a).run cg).1.headD 0))).run
            ((compileExpr fc env a).run cg).2).2)
      else if w.bits < w'.bits then
        ([((compileExpr fc env a).run cg).2.nextVal],
         ((inst1 (.extend (if op = .sext then .sextend else .uextend) (intTy w')
            (((compileExpr fc env a).run cg).1.headD 0))).run
            ((compileExpr fc env a).run cg).2).2)
      else ([((compileExpr fc env a).run cg).1.headD 0], ((compileExpr fc env a).run cg).2) := by
  simp only [compileExpr, bind_run]
  split
  · rfl
  · split
    · cases op <;> rfl
    · rfl

theorem run_cond {t : Ty} (c : DSL.Expr Γ .bool) (a b : DSL.Expr Γ t) :
    (compileExpr fc env (.cond c a b)).run cg =
      (selectVals (flat t) (((compileExpr fc env c).run cg).1.headD 0)
        ((compileExpr fc env a).run ((compileExpr fc env c).run cg).2).1
        ((compileExpr fc env b).run
          ((compileExpr fc env a).run ((compileExpr fc env c).run cg).2).2).1).run
        ((compileExpr fc env b).run
          ((compileExpr fc env a).run ((compileExpr fc env c).run cg).2).2).2 := rfl

theorem run_pair {a b : Ty} (x : DSL.Expr Γ a) (y : DSL.Expr Γ b) :
    (compileExpr fc env (.pair x y)).run cg =
      (((compileExpr fc env x).run cg).1 ++
        ((compileExpr fc env y).run ((compileExpr fc env x).run cg).2).1,
       ((compileExpr fc env y).run ((compileExpr fc env x).run cg).2).2) := rfl

theorem run_fst {a b : Ty} (p : DSL.Expr Γ (.prod a b)) :
    (compileExpr fc env (.fst p)).run cg =
      (((compileExpr fc env p).run cg).1.take (flat a).length, ((compileExpr fc env p).run cg).2) :=
  rfl

theorem run_snd {a b : Ty} (p : DSL.Expr Γ (.prod a b)) :
    (compileExpr fc env (.snd p)).run cg =
      (((compileExpr fc env p).run cg).1.drop (flat a).length, ((compileExpr fc env p).run cg).2) :=
  rfl

theorem run_vrepl {t : Ty} (n : Nat) (x : DSL.Expr Γ t) :
    (compileExpr fc env (.vrepl n x)).run cg =
      ((List.replicate n ((compileExpr fc env x).run cg).1).flatten,
       ((compileExpr fc env x).run cg).2) := rfl

theorem run_mapEmpty {k v : Ty} :
    (compileExpr fc env (Γ := Γ) (.mapEmpty (k := k) (v := v))).run cg =
      (callFn rtNew.1 rtNew.2 [fc.ctx.getD 0]).run cg := rfl

theorem run_mapContains {k v : Ty} (m : DSL.Var Γ (.map k v)) (key : DSL.Expr Γ k) :
    (compileExpr fc env (.mapContains m key)).run cg =
      (callFn rtContains.1 rtContains.2 [fc.ctx.getD 0, (env.getD m.idx []).headD 0,
          ((toWordV k ((compileExpr fc env key).run cg).1).run
            ((compileExpr fc env key).run cg).2).1]).run
        ((toWordV k ((compileExpr fc env key).run cg).1).run
          ((compileExpr fc env key).run cg).2).2 := rfl

end Compile.Proof
