import FV.Isle.Lookup
import FV.Backend.Proof.IselCovLe
import FV.Backend.Proof.IselFlowGen

/-!
# Form coverage of the ISLE lowering (V3): the abstract interpreter and its soundness

`aRule tab ins out r` evaluates rule `r` on abstract arguments `ins`: its patterns give a list
of abstract environments (`aPat`: a set of types is split into single types, so that a
summary sees the type its rules dispatch on; a pattern that cannot match a value gives none:
an empty value, a type or boolean constant outside the value's, an enum variant the value does
not have, a pattern the exclusion checker `fails` on), its if-lets and right-hand side are
evaluated (`aExpr`), and the result must be below `out`. Internal constructor calls go to an
oracle (`aOracle`) or to an entry of the summary table `tab` whose inputs are above the
arguments (several entries per term). Extern constructors and extractors use `actor`/`aext`
(`IselCovExt`); `apre` is the precondition of an extern constructor (an `emit`ted instruction
is covered).

`soundAt` (by induction on the interpreter's fuel): with `chkTab`, a run of a table term from
arguments its inputs describe returns a value its output describes and keeps the model's state
invariant `Is`; `root` does the same for one term whose rules each pass `aRule` or never match.
The facts about the extern helpers are the fields of `CovModel`.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-! ## Transfer functions -/

/-- The value of a type constant `$n`. -/
def aprim (ty : TypeId) (n : String) : AW :=
  match primTy ty n with
  | some (.ty t) => .ty [t]
  | _ => .c0

/-- A constant pattern `$n` can match a value `a` describes. -/
def primOk (a : AW) (ty : TypeId) (n : String) : Bool :=
  match primTy ty n, a with
  | some (.ty t), .ty ts => ts.any fun u => decide (u = t)
  | _, _ => true

/-- A constant pattern `b` can match a value `a` describes. -/
def boolOk (a : AW) (b : Bool) : Bool :=
  match a with
  | .bool b' => b == b'
  | _ => true

/-- The value of an integer constant: a small non-negative one exactly (`normInt` keeps it). -/
def aint (n : Int) : AW := if 0 ≤ n ∧ n < 128 then .num .int (n.toNat + 1) else .c0

/-- The fields of a value matched against variant `k` with `n` field patterns (`none`: it
cannot be variant `k`). -/
def aun (a : AW) (k : Nat) (n : Nat) : Option (List AW) :=
  match a with
  | .data _ k' fs => if k == k' then some fs else none
  | .alts as =>
    if as.all (fun b => match b with | .data .. => true | _ => false) then
      match as.filter (fun b => match b with | .data _ k' _ => k == k' | _ => false) with
      | [] => none
      | [.data _ _ fs] => some fs
      | bs => some (List.replicate n (.flat (AW.deepL bs).1 (AW.deepL bs).2))
    else some (List.replicate n (.flat (AW.deepL as).1 (AW.deepL as).2))
  | .flat m c => some (List.replicate n (.flat m c))
  | .xv .data => some (List.replicate n .c0)
  | _ => none

/-- The fields of a value matched against a struct pattern with `n` field patterns. -/
def aunS (a : AW) (n : Nat) : Option (List AW) :=
  match a with
  | .data _ _ fs => some fs
  | .alts as => some (List.replicate n (.flat (AW.deepL as).1 (AW.deepL as).2))
  | .flat m c => some (List.replicate n (.flat m c))
  | .xv .data => some (List.replicate n .c0)
  | _ => none

/-- The pattern cannot match a value `a` describes (beyond the shape checks). -/
def aPrune (p : Program) (a : AW) (q : Pattern) : Bool :=
  a.isBot ||
  match a with
  | .xv e => fails p e.toAV q
  | _ => false

/-- Summary table: per entry, an internal term, its abstract inputs and output. -/
abbrev Tab := List (TermId × List AW × AW)

namespace AW

/-- `le` by structural recursion on a fuel `n`, for the checks the kernel evaluates: `le` is
well-founded recursive, which the kernel reduces several times slower. `leF n a b` implies
`le a b` (`leF_le`); fuel 64 covers every comparison of the tables (a shortfall only makes a
check fail). -/
def leF : Nat → AW → AW → Bool
  | 0, _, _ => false
  | _ + 1, .bot, _ => true
  | n + 1, .alts as, b => as.all (leF n · b)
  | _ + 1, .data t k fs, .flat m c => deepLe (.data t k fs) m c
  | n + 1, .data t k fs, .data t' k' gs =>
    t == t' && k == k' && fs.length == gs.length && (fs.zip gs).all fun q => leF n q.1 q.2
  | n + 1, .data t k fs, .alts bs => bs.any (leF n (.data t k fs))
  | _ + 1, .data _ _ _, _ => false
  | _ + 1, a, b => leBase a b

/-- `leAll` through `leF` (`leAllF_leAll`). -/
def leAllF (as bs : List AW) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => leF 64 q.1 q.2

theorem leAlts_of : ∀ {as : List AW} {b : AW}, (∀ a ∈ as, le a b = true) → leAlts as b = true
  | [], _, _ => by simp [leAlts]
  | a :: as, b, h => by
    rw [leAlts]
    simp only [Bool.and_eq_true]
    exact ⟨h a (by simp), leAlts_of fun x hx => h x (by simp [hx])⟩

theorem leSome_of : ∀ {a : AW} {bs : List AW} {b : AW}, b ∈ bs → le a b = true → leSome a bs = true
  | _, [], _, hb, _ => by simp at hb
  | a, b' :: bs, b, hb, h => by
    rw [leSome]
    simp only [Bool.or_eq_true]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl h
    · exact Or.inr (leSome_of hb h)

theorem leL_of : ∀ {as bs : List AW}, as.length = bs.length →
    (∀ q ∈ as.zip bs, le q.1 q.2 = true) → leL as bs = true
  | [], [], _, _ => by simp [leL]
  | [], _ :: _, hl, _ => absurd hl (Nat.succ_ne_zero _).symm
  | _ :: _, [], hl, _ => absurd hl (Nat.succ_ne_zero _)
  | a :: as, b :: bs, hl, h => by
    rw [leL]
    simp only [Bool.and_eq_true]
    exact ⟨h (a, b) (by simp), leL_of (by simpa using hl) fun q hq => h q (by simp [hq])⟩

theorem leF_le : ∀ (n : Nat) (a b : AW), leF n a b = true → le a b = true
  | 0, _, _, h => by simp [leF] at h
  | n + 1, a, b, h => by
    cases a with
    | bot => simp [le]
    | alts as =>
      rw [le]
      simp only [leF, List.all_eq_true] at h
      exact leAlts_of fun x hx => leF_le n x b (h x hx)
    | data t k fs =>
      cases b with
      | flat m c => simpa [leF, le] using h
      | data t' k' gs =>
        simp only [leF, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
        obtain ⟨⟨⟨rfl, rfl⟩, hl⟩, h⟩ := h
        rw [le.eq_4]
        simp only [Bool.and_eq_true]
        exact ⟨⟨beq_iff_eq.mpr rfl, beq_iff_eq.mpr rfl⟩, leL_of hl fun q hq => leF_le n q.1 q.2 (h q hq)⟩
      | alts bs =>
        simp only [leF, List.any_eq_true] at h
        obtain ⟨b, hb, h⟩ := h
        rw [le]
        exact leSome_of hb (leF_le n _ b h)
      | _ => simp [leF] at h
    | _ => simpa [leF, le] using h

theorem leAllF_leAll {as bs : List AW} (h : leAllF as bs = true) : leAll as bs = true := by
  simp only [leAllF, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact leL_of h.1 fun q hq => leF_le 64 q.1 q.2 (h.2 q hq)

end AW

/-- The output of an entry of `t` whose inputs are above `as`: the first with inputs equivalent
to `as`, else the first above them. -/
def tabGet (tab : Tab) (t : TermId) (as : List AW) : Option AW :=
  match tab.find? (fun e => e.1 == t && AW.leAllF as e.2.1 && AW.leAllF e.2.1 as) with
  | some e => some e.2.2
  | none => (tab.find? fun e => e.1 == t && AW.leAllF as e.2.1).map (·.2.2)

section Eval
variable (p : Program) (tab : Tab) (aext : TermId → AW → List AW) (actor : TermId → List AW → AW)
  (apre : TermId → List AW → Bool) (aOracle : TermId → List AW → Option AW)

mutual
/-- The abstract environments after matching `q` against a value `a` describes. -/
def aPat (a : AW) (q : Pattern) (env : List AW) : List (List AW) :=
  if aPrune p a q then [] else
  match q with
  | .bind _ x sub => (AW.split a).flatMap fun b => aPat b sub (env.set x b)
  | .and _ ps => aPatAll a ps env
  | .term _ t args =>
    match termOfT p t with
    | .ok term =>
      match term.kind with
      | .enumVariant k =>
        match aun a k args.length with
        | some fs => aPatArgs fs args env
        | none => []
      | .struct =>
        match aunS a args.length with
        | some fs => aPatArgs fs args env
        | none => []
      | .decl _ _ (some (.external _ _)) => aPatArgs (aext term.id a) args env
      | _ => [env]
    | .error _ => [env]
  | .constPrim ty n => if primOk a ty n then [env] else []
  | .constBool _ b => if boolOk a b then [env] else []
  | _ => [env]
/-- `aPat` of every pattern of a list, against the same value. -/
def aPatAll (a : AW) : List Pattern → List AW → List (List AW)
  | [], env => [env]
  | q :: qs, env => (aPat a q env).flatMap fun e => aPatAll a qs e
/-- Patterns against abstract values pointwise (`top` past the end). -/
def aPatArgs : List AW → List Pattern → List AW → List (List AW)
  | a :: as, q :: qs, env => (aPat a q env).flatMap fun e => aPatArgs as qs e
  | [], q :: qs, env => (aPat .top q env).flatMap fun e => aPatArgs [] qs e
  | _, [], env => [env]
end

/-- Abstract application of term `t` (result type `ty`). -/
def aApply (ty : TypeId) (t : TermId) (as : List AW) : Option AW :=
  if as.any AW.isBot then some .bot else
  match termOf p t with
  | .ok term =>
    match term.kind with
    | .enumVariant k => some (.data ty k as)
    | .struct => some (.data ty 0 as)
    | .decl _ (some (.external _)) _ =>
      if apre term.id as then some (actor term.id as) else none
    | .decl _ (some .internal) _ =>
      match aOracle t as with
      | some a => some a
      | none => tabGet tab t as
    | _ => some .top
  | .error _ => some .top

mutual
/-- Abstract value of an expression (`none`: a check failed). -/
def aExpr : Isle.Expr → List AW → Option AW
  | .var _ x, env => some (env.getD x .top)
  | .constBool _ b, _ => some (.bool b)
  | .constInt _ n, _ => some (aint n)
  | .constPrim ty n, _ => some (aprim ty n)
  | .let _ bs body, env =>
    match aBinds bs env with
    | some env' => aExpr body env'
    | none => none
  | .term ty t args, env =>
    match aArgs args env with
    | some as => aApply p tab actor apre aOracle ty t as
    | none => none
/-- Abstract values of arguments. -/
def aArgs : List Isle.Expr → List AW → Option (List AW)
  | [], _ => some []
  | e :: es, env =>
    match aExpr e env, aArgs es env with
    | some a, some as => some (a :: as)
    | _, _ => none
/-- Abstract `let*` bindings. -/
def aBinds : List (VarId × TypeId × Isle.Expr) → List AW → Option (List AW)
  | [], env => some env
  | (x, _, e) :: bs, env =>
    match aExpr e env with
    | some a => aBinds bs (env.set x a)
    | none => none
end

/-- Abstract if-lets: the environments after them (`none`: a check failed). -/
def aIfLets : List IfLet → List AW → Option (List (List AW))
  | [], env => some [env]
  | il :: ils, env =>
    match aExpr p tab actor apre aOracle il.rhs env with
    | some a =>
      ((aPat p aext a il.lhs env).mapM fun e => aIfLets ils e).map List.flatten
    | none => none

/-- The abstract environments after a rule's match phase. -/
def aRuleEnvs (ins : List AW) (r : Rule) : Option (List (List AW)) :=
  ((aPatArgs p aext ins r.args (List.replicate r.vars.length .top)).mapM
    fun e => aIfLets p tab aext actor apre aOracle r.iflets e).map List.flatten

/-- Rule `r` checks with inputs `ins` and output `out`. -/
def aRule (ins : List AW) (out : AW) (r : Rule) : Bool :=
  match aRuleEnvs p tab aext actor apre aOracle ins r with
  | some envs => envs.all fun env =>
    match aExpr p tab actor apre aOracle r.rhs env with
    | some a => AW.le a out
    | none => false
  | none => false

/-- Every rule of every table entry checks. -/
def chkTab : Bool :=
  tab.all fun e => (p.rulesOf e.1).all (aRule p tab aext actor apre aOracle e.2.1 e.2.2)

end Eval

end Backend.Proof.Cov
