import FV.Backend.Proof.IselCovFns
import FV.Backend.Proof.DriverCheck

/-!
# The size of the ISLE lowering's output (V6c): weights and the cost analysis

The layout needs the emitted function below `2 ^ 27` bytes (`E2E.spillSizeOkB`). To state that
as a condition on the CLIF input, every ISLE run of the driver is bounded: the **weight** of the
instructions it emits (`wtA`, a sum of `szInstW`) is at most a bound of the CLIF instruction.

* `szWords m`: `E2E.instWords` (the lines `MInst.lines` emits); `regCount m`: an upper bound on
  the register operands (`MInst.operands`); `szInstW m = szWords m + 20 · regCount m` (plus the
  callee-saved restores before a `Rets`): the words the spill allocation's code has for `m` (a
  load or store of at most 20 words per operand).
* The cost analysis: `cExpr`/`cArgs`/`cBinds`/`cIfLets`/`cRule` bound the weight an expression,
  if-lets or rule emits, on V3's abstract values (`aExpr`, the value table `tab`), with a cost
  table `ctab` (`CTab`: per entry a term, abstract inputs, a weight) for internal terms and
  `actorW` for extern constructors (`emit`: `emitW` of the instruction's abstract variant; a
  `Call`/`CallInd`/`JTSequence` variant, whose weight depends on its lists, has none; the call
  rules and `br_table` are checked by hand). `chkCost`: every rule of every entry costs at most
  the entry's weight.
* The same analysis bounds the branch targets emitted (`tgA`, with `actorT`: only a
  `JTSequence` `emit`, in the hand-checked `br_table` rule, has more than two).
* The driver's contract `IselSz f`: a statement's run emits at most `stmtSzB` (a call: linear in
  its arguments) and `tgStmtK` targets, a terminator's at most `termSzB` and `termTgB` (a
  `br_table`: plus its table).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-! ## Weights -/

/-- `E2E.instWords`: an upper bound on the words `MInst.lines` emits (including a `trapIf`'s
deferred trap; for a `Rets`, the epilogue `lowerRFunc` puts in its place). -/
def szWords : MInst → Nat
  | .load .. | .store .. | .loadAddr .. => 5
  | .atomicRmwLoop .. | .atomicCasLoop .. | .elfTlsGetAddr .. => 7
  | .jtSequence _ ts _ _ _ => 7 + ts.length
  | .condBr .. | .testBitAndBranch .. | .tryCall .. | .trapIf .. | .loadExtNameGot ..
  | .loadExtNameNear .. => 2
  | .rets _ => 7
  | _ => 1

/-- An upper bound on the register operands of an instruction (`MInst.operands`): its list
lengths for `call`/`tryCall`/`args`/`rets`, 5 otherwise. -/
def regCount : MInst → Nat
  | .call info | .tryCall info _ => 1 + info.uses.length + info.defs.length
  | .args ds => ds.length
  | .rets us => us.length
  | _ => 5

/-- The callee-saved restores before a `Rets` (`spillRestores`: one slot load per callee-saved
register, 10 words each). -/
def restW : Nat := 10 * calleeSaved.length

/-- **The weight of an instruction**: its words, 20 words per register operand, its branch
targets (each may become an edge block of `prepare`), and the restores of a `Rets`. -/
def szInstW (m : MInst) : Nat :=
  szWords m + 20 * regCount m + m.targets.length + (match m with | .rets _ => restW | _ => 0)

/-- The weight of a list of instructions. -/
def wtL (ms : List MInst) : Nat := (ms.map szInstW).sum

/-- The weight of an array of instructions. -/
def wtA (ms : Array MInst) : Nat := wtL ms.toList

/-- The weight of every instruction variant but `Call`, `CallInd` and `JTSequence` (whose
weights depend on their lists): `szWords ≤ 7`, at most 5 register operands, at most 2 targets
(and never both 7 words and a target). -/
def emitK : Nat := 107

/-- The weight of an `emit`ted instruction value `a` describes: `emitK` if every variant it may
have is neither `Call`, `CallInd` nor `JTSequence`. -/
def emitW (a : AW) : Option Nat :=
  let okK (k : Nat) : Bool :=
    k != VIdx.MInst.Call && k != VIdx.MInst.CallInd && k != VIdx.MInst.JTSequence
  match a with
  | .data t k _ => if t == tyMInst && okK k then some emitK else none
  | .alts as =>
    if as.all (fun b => match b with
      | .data t k _ => t == tyMInst && okK k
      | _ => false) then some emitK else none
  | _ => none

/-- The weight of `load_constant_full`'s `movz`/`movn` and at most three `movk`s. -/
def loadConstW : Nat := 4 * emitK

/-- The weight of `gen_return`'s `Rets` (at most 8 return registers). -/
def retsW : Nat := 7 + 20 * 8 + restW

/-- The number of branch targets of a list of instructions. -/
def tgL (ms : List MInst) : Nat := (ms.map fun m => m.targets.length).sum

/-- The branch targets of an array of instructions. -/
def tgA (ms : Array MInst) : Nat := tgL ms.toList

/-- The branch targets of an instruction variant (`none`: `JTSequence`, its table). -/
def varT (k : Nat) : Option Nat :=
  if k == VIdx.MInst.JTSequence then none
  else if k == VIdx.MInst.Jump then some 1
  else if k == VIdx.MInst.CondBr || k == VIdx.MInst.TestBitAndBranch then some 2
  else some 0

/-- The branch targets of an `emit`ted instruction value `a` describes: the maximum over the
variants it may have (none for a `JTSequence`). -/
def emitT (a : AW) : Option Nat :=
  match a with
  | .data t k _ => if t == tyMInst then varT k else none
  | .alts as =>
    (as.mapM fun (b : AW) => match b with
      | .data t k _ => if t == tyMInst then varT k else none
      | _ => none).map fun (ns : List Nat) => ns.foldl max 0
  | _ => none

/-- **Extern constructors**: the branch targets they emit (only `emit`'s instruction has any). -/
def actorT (id : TermId) (as : List AW) : Option Nat :=
  if id == TId.emit then
    match as with
    | [a] => emitT a
    | _ => none
  else some 0

/-- **Extern constructors**: the weight they emit (`none`: not bounded here). -/
def actorW (id : TermId) (as : List AW) : Option Nat :=
  if id == TId.emit then
    match as with
    | [a] => emitW a
    | _ => none
  else if id == TId.load_constant_full then some loadConstW
  else if id == TId.gen_return then some retsW
  else if id == TId.gen_call_args then none
  else some 0

/-! ## The cost analysis -/

/-- Cost table: per entry, an internal term, its abstract inputs and a weight. -/
abbrev CTab := List (TermId × List AW × Nat)

/-- The weight of an entry of `t` whose inputs are above `as`. -/
def ctabGet (ctab : CTab) (t : TermId) (as : List AW) : Option Nat :=
  (ctab.find? fun e => e.1 == t && AW.leAll as e.2.1).map (·.2.2)

section Eval
variable (p : Program) (tab : Tab) (aw : TermId → List AW → Option Nat) (ctab : CTab)
  (aext : TermId → AW → List AW)
  (actor : TermId → List AW → AW) (apre : TermId → List AW → Bool)
  (aOracle : TermId → List AW → Option AW)

/-- The weight an application of term `t` to values `as` describes emits (mirrors `aApply`:
`some` only where `aApply` is). -/
def cApply (ty : TypeId) (t : TermId) (as : List AW) : Option Nat :=
  if as.any AW.isBot then some 0 else
  match termOf p t with
  | .ok term =>
    match term.kind with
    | .enumVariant _ => some 0
    | .struct => some 0
    | .decl _ (some (.external _)) _ =>
      if apre term.id as then aw term.id as else none
    | .decl _ (some .internal) _ =>
      match aOracle t as with
      | some _ => some 0
      | none =>
        match tabGet tab t as with
        | some _ => ctabGet ctab t as
        | none => none
    | _ => some 0
  | .error _ => some 0

mutual
/-- The weight evaluating an expression emits (`none`: not bounded, or `aExpr` fails). -/
def cExpr : Isle.Expr → List AW → Option Nat
  | .var .., _ => some 0
  | .constBool .., _ => some 0
  | .constInt .., _ => some 0
  | .constPrim .., _ => some 0
  | .let _ bs body, env =>
    match aBinds p tab actor apre aOracle bs env, cBinds bs env with
    | some env', some c =>
      match cExpr body env' with
      | some d => some (c + d)
      | none => none
    | _, _ => none
  | .term ty t args, env =>
    match aArgs p tab actor apre aOracle args env, cArgs args env with
    | some as, some c =>
      match cApply p tab aw ctab apre aOracle ty t as with
      | some d => some (c + d)
      | none => none
    | _, _ => none
/-- The weight evaluating arguments emits. -/
def cArgs : List Isle.Expr → List AW → Option Nat
  | [], _ => some 0
  | e :: es, env =>
    match cExpr e env, cArgs es env with
    | some c, some d => some (c + d)
    | _, _ => none
/-- The weight evaluating `let*` bindings emits. -/
def cBinds : List (VarId × TypeId × Isle.Expr) → List AW → Option Nat
  | [], _ => some 0
  | (x, _, e) :: bs, env =>
    match aExpr p tab actor apre aOracle e env, cExpr e env with
    | some a, some c =>
      match cBinds bs (env.set x a) with
      | some d => some (c + d)
      | none => none
    | _, _ => none
end

/-- The weight the if-lets emit, on every path of abstract environments (the maximum). -/
def cIfLets : List IfLet → List AW → Option Nat
  | [], _ => some 0
  | il :: ils, env =>
    match aExpr p tab actor apre aOracle il.rhs env, cExpr p tab aw ctab actor apre aOracle il.rhs env with
    | some a, some c =>
      match (aPat p aext a il.lhs env).mapM fun e => cIfLets ils e with
      | some ds => some (c + ds.foldl max 0)
      | none => none
    | _, _ => none

/-- The weight a run of rule `r` on values `ins` describes emits: its if-lets (on every
environment of its argument patterns) and its right-hand side (on every environment after its
if-lets). -/
def cRule (ins : List AW) (r : Rule) : Option Nat :=
  match (aPatArgs p aext ins r.args (List.replicate r.vars.length .top)).mapM
      (cIfLets p tab aw ctab aext actor apre aOracle r.iflets),
    aRuleEnvs p tab aext actor apre aOracle ins r with
  | some cs, some envs =>
    match envs.mapM (cExpr p tab aw ctab actor apre aOracle r.rhs) with
    | some ds => some (cs.foldl max 0 + ds.foldl max 0)
    | none => none
  | _, _ => none

/-- Rule `r` on values `ins` emits at most weight `c`. -/
def cRuleLe (ins : List AW) (c : Nat) (r : Rule) : Bool :=
  match cRule p tab aw ctab aext actor apre aOracle ins r with
  | some c' => decide (c' ≤ c)
  | none => false

/-- Every rule of every entry of the cost table emits at most the entry's weight. -/
def chkCost : Bool :=
  ctab.all fun e => (p.rulesOf e.1).all (cRuleLe p tab aw ctab aext actor apre aOracle e.2.1 e.2.2)

end Eval

/-! ## The facts the soundness of the cost analysis assumes -/

section Facts

/-- **Extern constructors** emit at most their cost: `aw` bounds the growth of the measure `W`
of the lowering state for arguments the abstract values describe. -/
def ExtW (f : Clif.Function) (ctx : Ctx) (apre : TermId → List AW → Bool)
    (aw : TermId → List AW → Option Nat) (W : LState → Nat) : Prop :=
  ∀ (as : List AW) (vs : List V) (term : Term) (v : V) (st st' : LState) (c : Nat),
    γL f ctx as vs → apre term.id as = true → aw term.id as = some c →
    (sem ctx).ctor term vs st = .ok (v, st') → W st' ≤ W st + c

/-- **The oracle's runs** do not grow the measure `W`. -/
def OracleW (p : Program) (f : Clif.Function) (ctx : Ctx) (aOracle : TermId → List AW → Option AW)
    (W : LState → Nat) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (n : Nat) (ty : TypeId) (t : TermId)
    (as : List AW) (vs : List V) (a : AW) (s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId), aOracle t as = some a → γL f ctx as vs →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) → W s' ≤ W s

/-- **A hand-checked rule** `rl` on arguments `vs` emits at most `c`: every run of it (its match,
then its right-hand side, at the fuel a root's rule selection leaves) grows `W` by at most `c`. -/
def HandW (p : Program) (ctx : Ctx) (vs : List V) (rl : Rule) (W : LState → Nat) (c : Nat) : Prop :=
  ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (m n : Nat) (s : LState) (tr : Array RuleId)
    (env : Isle.Interp.Env V) (s1 : LState × Array RuleId) (r : Option V) (s2 : LState)
    (tr2 : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    (matchRule p (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, s1) →
    (evalExpr p (sem ctx) cfg n rl.rhs env).run s1 = .ok (r, (s2, tr2)) → W s2 ≤ W s + c

end Facts

end Backend.Proof.Cov

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Cov Isle

/-! ## The driver's contract -/

/-- The weight bound of a non-call statement's run (`IselSzTab`'s root check). -/
def szStmtK : Nat := 1200

/-- The weight bound of a call's run with `n` arguments: the stores of the stack-passed ones,
the call with its argument and result registers, a GOT load (the hand-checked call rules). -/
def szCallB (n : Nat) : Nat := 400 + 125 * n

/-- The weight bound of a `return`/`trap`/`jump`/`brif` run. -/
def szTermK : Nat := 600

/-- The weight bound of a `br_table` run, without the table's targets. -/
def szBrK : Nat := 1500

/-- The branch-target bound of a statement's run. -/
def tgStmtK : Nat := 0

/-- The branch-target bound of a non-`br_table` terminator's run. -/
def tgTermK : Nat := 2

/-- The weight bound of a statement's run. -/
def stmtSzB : Clif.Inst → Nat
  | .call _ args | .callIndirect _ _ args => szCallB args.length
  | _ => szStmtK

/-- The weight bound of a terminator's run (a `try_call`'s: its call). -/
def termSzB : Clif.Terminator → Nat
  | .brTable _ _ tbl => szBrK + (1 + tbl.length)
  | .tryCall _ args _ | .tryCallIndirect _ args _ => szCallB args.length
  | _ => szTermK

/-- The branch-target bound of a terminator's run (a `br_table`'s: its default and table). -/
def termTgB : Clif.Terminator → Nat
  | .brTable _ _ tbl => 1 + tbl.length
  | _ => tgTermK

/-- Every statement's `lower` run emits at most `stmtSzB` of its instruction and `tgStmtK`
branch targets. -/
def StmtSz (ctx : Ctx) : Prop :=
  ∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
    runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) →
    wtA s'.emitted ≤ wtA s.emitted + stmtSzB inst ∧ tgA s'.emitted ≤ tgA s.emitted + tgStmtK

/-- Every non-`try_call` terminator's run emits at most `termSzB` and `termTgB`. -/
def TermSz (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t data targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false →
    termData (abiTerm f t) = .ok data →
    termCallF ctx ti data t targets s = .ok (out, s', tr) →
    wtA s'.emitted ≤ wtA s.emitted + termSzB t ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB t

/-- Every `try_call` terminator's run emits at most `termSzB` and `termTgB`. -/
def TrySz (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ ti t data trs targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → tryCallData f t = .ok data →
    tryCallF ctx ti data trs targets s = .ok (out, s', tr) →
    wtA s'.emitted ≤ wtA s.emitted + termSzB t ∧ tgA s'.emitted ≤ tgA s.emitted + termTgB t

/-- **The ISLE runs of the driver on `f` are bounded.** -/
def IselSz (f : Clif.Function) : Prop :=
  ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → StmtSz ctx ∧ TermSz f ctx ∧ TrySz f ctx

end Backend.Proof.Driver
