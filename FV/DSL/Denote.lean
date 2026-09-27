import FV.DSL.Syntax

/-!
# Denotational semantics

All functions are structurally recursive on the syntax. The meaning of each primitive is the
corresponding `DSL.Ops` function (or core `BitVec`/`Bool` operation), which is what the
generated shallow definitions call, so `denote_eq` holds by `rfl`.
-/

namespace DSL

def IBin.denote {n : Nat} : IBin → BitVec n → BitVec n → BitVec n
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => Ops.shl a b
  | .lshr, a, b => Ops.lshr a b
  | .ashr, a, b => Ops.ashr a b

def ICmp.denote {n : Nat} : ICmp → BitVec n → BitVec n → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .ult, a, b => BitVec.ult a b
  | .ule, a, b => BitVec.ule a b
  | .slt, a, b => BitVec.slt a b
  | .sle, a, b => BitVec.sle a b

def Cast.denote {n : Nat} : Cast → (w : Nat) → BitVec n → BitVec w
  | .zext, w, a => Ops.zext w a
  | .sext, w, a => Ops.sext w a
  | .trunc, w, a => Ops.trunc w a

def IOp.denote {n : Nat} : IOp → BitVec n → BitVec n → M (BitVec n)
  | .addC, a, b => Ops.addC a b
  | .subC, a, b => Ops.subC a b
  | .mulC, a, b => Ops.mulC a b
  | .udiv, a, b => Ops.udiv a b
  | .urem, a, b => Ops.urem a b

def Expr.denote {Γ : List Ty} : {t : Ty} → Expr Γ t → Env Γ → t.denote
  | _, .var v, env => v.get env
  | _, .clone v, env => v.get env
  | _, .ilit _ x, _ => x
  | _, .blit b, _ => b
  | _, .unit, _ => ()
  | _, .ibin op a b, env => op.denote (a.denote env) (b.denote env)
  | _, .inot a, env => ~~~(a.denote env)
  | _, .icmp op a b, env => op.denote (a.denote env) (b.denote env)
  | _, .cast op w a, env => op.denote w.bits (a.denote env)
  | _, .band a b, env => a.denote env && b.denote env
  | _, .bor a b, env => a.denote env || b.denote env
  | _, .bnot a, env => !(a.denote env)
  | _, .cond c a b, env => if c.denote env then a.denote env else b.denote env
  | _, .pair a b, env => (a.denote env, b.denote env)
  | _, .fst p, env => (p.denote env).1
  | _, .snd p, env => (p.denote env).2
  | _, .vrepl n x, env => Vector.replicate n (x.denote env)
  | _, .mapEmpty, _ => Map.empty
  | _, .mapContains m k, env => (m.get env).contains (k.denote env)

def Exprs.denote {Γ : List Ty} : {σ : List Ty} → Exprs Γ σ → Env Γ → Env σ
  | _, .nil, _ => ()
  | _, .cons e es, env => (e.denote env, es.denote env)

def Op.denote {Γ : List Ty} {t : Ty} : Op Γ t → Env Γ → M t.denote
  | .iop op a b, env => op.denote (a.denote env) (b.denote env)
  | .vget v i, env => Ops.vget (v.get env) (i.denote env)
  | .mapGet m k, env => Ops.mapGet (m.get env) (k.denote env)

def Stmt.denote : {Γ : List Ty} → {τ : Ty} → Stmt Γ τ → Env Γ → M τ.denote
  | _, _, .ret e, env => pure (e.denote env)
  | _, _, .throw err, _ => MonadExcept.throw err
  | _, _, .op o, env => o.denote env
  | _, _, .call _ body args, env => body.denote (args.denote env)
  | _, _, .let_ e k, env => k.denote (e.denote env, env)
  | _, _, .letPair e k, env => k.denote ((e.denote env).2, (e.denote env).1, env)
  | _, _, .bind s k, env => s.denote env >>= fun x => k.denote (x, env)
  | _, _, .set v e k, env => k.denote (v.set env (e.denote env))
  | _, _, .vset v i e k, env =>
    Ops.vset (v.get env) (i.denote env) (e.denote env) >>= fun xs => k.denote (v.set env xs)
  | _, _, .mapInsert v key val k, env =>
    k.denote (v.set env ((v.get env).insert (key.denote env) (val.denote env)))
  | _, _, .ite c t e, env => if c.denote env then t.denote env else e.denote env
  | _, _, .forRange n init body, env =>
    Ops.forRange n (init.denote env) (fun i acc => body.denote (acc, i, env))

/-- The meaning of a DSL function. -/
def denote {σ : List Ty} {τ : Ty} (f : FlatFn σ τ) (args : Args σ) : M τ.denote :=
  f.body.denote args

end DSL
