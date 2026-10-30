import FV.Opt.Proof.Dom
import FV.Opt.Simplify

/-!
# A declarative specification of `Opt.checkCore` (M1)

`Opt.checkCore` is written with nested `for` loops in `Except`. For the completeness proofs of the
passes (`FV/Opt/Proof/Complete*.lean`) this file states when it succeeds and what it returns:
`checkCore_ok_iff : checkCore f = .ok i ↔ CoreOk f ∧ i = coreInfo f`.
-/

namespace Opt

open Clif

/-! ## `Except` loops that always yield -/

/-- `C` holds at every step of the fold of `g` over `l` from `s`. -/
def AllAlong {α β : Type} (C : β → α → Prop) (g : β → α → β) : List α → β → Prop
  | [], _ => True
  | a :: as, s => C s a ∧ AllAlong C g as (g s a)

/-- A loop whose body yields `g s a` exactly when `C s a` (and errs otherwise) succeeds exactly
when `C` holds along the fold, with the fold as result. -/
theorem forIn_ok_iff {ε α β : Type} {body : α → β → Except ε (ForInStep β)}
    (C : β → α → Prop) (g : β → α → β)
    (hb : ∀ a s r, body a s = .ok r ↔ C s a ∧ r = .yield (g s a)) :
    ∀ (l : List α) (init r : β),
      forIn l init body = .ok r ↔ AllAlong C g l init ∧ r = l.foldl g init
  | [], init, r => by
    simp only [List.forIn_nil, AllAlong, List.foldl_nil, true_and]
    exact ⟨fun h => (Except.ok.inj h).symm, fun h => h ▸ rfl⟩
  | a :: l, init, r => by
    rw [List.forIn_cons]
    simp only [AllAlong, List.foldl_cons]
    cases hba : body a init with
    | error e =>
      have : ¬ C init a := fun hc => by
        have := (hb a init (.yield (g init a))).2 ⟨hc, rfl⟩
        rw [hba] at this; cases this
      constructor
      · intro h; simp [bind, Except.bind] at h
      · intro h; exact absurd h.1.1 this
    | ok st =>
      obtain ⟨hc, rfl⟩ := (hb a init st).1 hba
      simp only [bind, Except.bind]
      rw [forIn_ok_iff C g hb l (g init a) r]
      exact ⟨fun h => ⟨⟨hc, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

theorem ensure_bind_ok {β : Type} {c : Bool} {m : String} {k : Except String β} {r : β} :
    (ensure c m >>= fun _ => k) = .ok r ↔ c = true ∧ k = .ok r := by
  unfold ensure
  cases c <;> simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {k : α → Except ε β} {r : β} :
    (x >>= k) = .ok r ↔ ∃ y, x = .ok y ∧ k y = .ok r := by
  cases x <;> simp [bind, Except.bind]

/-! ## The definitions loop -/

abbrev TyMap := Std.HashMap ValueId Ty
abbrev BlkMap := Std.HashMap ValueId Nat
abbrev PureMap := Std.HashMap ValueId Inst

/-- One definition `v : t` in block `i`. -/
def defStep (i : Nat) (s : TyMap × BlkMap) (p : ValueId × Ty) : TyMap × BlkMap :=
  (s.1.insert p.1 p.2, s.2.insert p.1 i)

/-- The definition `v : t` is new. -/
def defC (s : TyMap × BlkMap) (p : ValueId × Ty) : Prop := s.1.contains p.1 = false

/-- The definitions of a statement of block `i`. -/
def stmtDefStep (f : Function) (i : Nat) (s : TyMap × BlkMap × PureMap) (st : Stmt) :
    TyMap × BlkMap × PureMap :=
  match st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none) with
  | some ts =>
    let s' := (st.results.zip ts).foldl (defStep i) (s.1, s.2.1)
    (s'.1, s'.2, if isPure st.inst then
      (match st.results with
       | [v] => s.2.2.insert v st.inst
       | _ => s.2.2) else s.2.2)
  | none => s

def stmtDefC (f : Function) (i : Nat) (s : TyMap × BlkMap × PureMap) (st : Stmt) : Prop :=
  ∃ ts, st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none) = some ts ∧
    ts.length = st.results.length ∧ AllAlong defC (defStep i) (st.results.zip ts) (s.1, s.2.1)

def blockDefStep (f : Function) (s : TyMap × BlkMap × PureMap) (x : Block × Nat) :
    TyMap × BlkMap × PureMap :=
  let s1 := x.1.params.foldl (defStep x.2) (s.1, s.2.1)
  x.1.body.foldl (stmtDefStep f x.2) (s1.1, s1.2, s.2.2)

def blockDefC (f : Function) (s : TyMap × BlkMap × PureMap) (x : Block × Nat) : Prop :=
  AllAlong defC (defStep x.2) x.1.params (s.1, s.2.1) ∧
    AllAlong (stmtDefC f x.2) (stmtDefStep f x.2) x.1.body
      ((x.1.params.foldl (defStep x.2) (s.1, s.2.1)).1,
       (x.1.params.foldl (defStep x.2) (s.1, s.2.1)).2, s.2.2)

/-- The maps the definitions loop builds. -/
def defsState (f : Function) : TyMap × BlkMap × PureMap :=
  f.blocks.zipIdx.foldl (blockDefStep f) ({}, {}, {})

/-- The definitions loop succeeds. -/
def DefsOk (f : Function) : Prop :=
  AllAlong (blockDefC f) (blockDefStep f) f.blocks.zipIdx ({}, {}, {})

/-! ## `checkCore` with named loop bodies -/

/-- The body of the definitions loop (copied from `checkCore`). -/
def defsBody (f : Function) (x : Block × Nat) (s : TyMap × BlkMap × PureMap) :
    Except String (ForInStep (TyMap × BlkMap × PureMap)) := do
  let sigOf := fun r => (f.externs.lookup r).map (·.sig)
  let (b, i) := x
  let mut types := s.1
  let mut defBlock := s.2.1
  let mut pureDef := s.2.2
  for (v, t) in b.params do
    ensure (!types.contains v) s!"v{v} defined twice"
    types := types.insert v t
    defBlock := defBlock.insert v i
  for st in b.body do
    let some ts := st.inst.resultTypes sigOf (fun _ => none) | throw s!"ill-formed instruction defining {st.results}"
    ensure (ts.length == st.results.length) s!"result arity of {st.results}"
    for (v, t) in st.results.zip ts do
      ensure (!types.contains v) s!"v{v} defined twice"
      types := types.insert v t
      defBlock := defBlock.insert v i
    if isPure st.inst then
      if let [v] := st.results then pureDef := pureDef.insert v st.inst
  return .yield (types, defBlock, pureDef)

/-- The body of the uses loop (copied from `checkCore`). -/
def usesBody (f : Function) (types : TyMap) (defBlock : BlkMap) (x : Block × Nat) (_u : Unit) :
    Except String (ForInStep Unit) := do
  let cfg := Cfg.build f
  let blocks := f.blocks.toArray
  let ty := fun v => types.get? v
  let (b, i) := x
  let mut seen : Std.HashSet ValueId := b.params.foldl (·.insert ·.1) {}
  let avail := fun (seen : Std.HashSet ValueId) (v : ValueId) =>
    seen.contains v || match defBlock.get? v with
      | some d => d != i && cfg.dominates d i
      | none => false
  for st in b.body do
    for v in operands st.inst do
      ensure (avail seen v) s!"block{b.id}: use of v{v} not dominated by its definition"
    if isPure st.inst then
      ensure (pureTyped ty f st.inst) s!"block{b.id}: ill-typed pure instruction defining {st.results}"
    seen := st.results.foldl (·.insert ·) seen
  for v in termOperands b.term do
    ensure (avail seen v) s!"block{b.id}: terminator uses v{v}, not dominated by its definition"
  let calls : List BlockCall := match b.term with
    | .jump d => [d] | .brif _ t e => [t, e] | .brTable _ d t => d :: t | _ => []
  for bc in calls do
    let some j := cfg.index.get? bc.block | throw s!"unknown block{bc.block}"
    let ps := blocks[j]!.params
    ensure (ps.length == bc.args.length &&
      (ps.zip bc.args).all fun (p, a) => ty a == some p.2) s!"block{b.id}: arguments of block{bc.block}"
  match b.term with
  | .brTable x _ _ => do
    ensure (ty x == some .i32) s!"block{b.id}: br_table index not i32"
    pure (ForInStep.yield PUnit.unit)
  | _ => pure (ForInStep.yield PUnit.unit)

/-- The reachability loop's body. -/
def reachBody (f : Function) (i : Nat) (_u : Unit) : Except String (ForInStep Unit) := do
  ensure ((Cfg.build f).reachable i) s!"unreachable block{(Cfg.build f).ids[i]!}"
  pure (ForInStep.yield PUnit.unit)

/-- `checkCore` with the named bodies. -/
theorem checkCore_eq (f : Function) : checkCore f = (do
    ensure ((Cfg.build f).size > 0) "no blocks"
    ensure ((Cfg.build f).index.size == (Cfg.build f).size) "duplicate block ids"
    forIn [:(Cfg.build f).size] PUnit.unit (reachBody f)
    let s ← forIn f.blocks.toArray.zipIdx ((∅ : TyMap), (∅ : BlkMap), (∅ : PureMap)) (defsBody f)
    ensure ((f.blocks.toArray[0]!.params.map (·.2)) == f.sig.params.map (·.ty))
      "entry parameters ≠ signature"
    forIn f.blocks.toArray.zipIdx PUnit.unit (usesBody f s.1 s.2.1)
    pure { cfg := Cfg.build f, types := s.1, defBlock := s.2.1, pureDef := s.2.2 }) := rfl

def paramBody (i : Nat) (x : ValueId × Ty) (s : TyMap × BlkMap) :
    Except String (ForInStep (TyMap × BlkMap)) :=
  match x with
  | (v, t) => do
    ensure (!s.1.contains v) s!"v{v} defined twice"
    pure (.yield (s.1.insert v t, s.2.insert v i))

def stmtBody (f : Function) (i : Nat) (st : Stmt) (s : TyMap × BlkMap × PureMap) :
    Except String (ForInStep (TyMap × BlkMap × PureMap)) :=
  match st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none) with
  | some ts => do
    ensure (ts.length == st.results.length) s!"result arity of {st.results}"
    let s2 ← forIn (st.results.zip ts) (s.1, s.2.1) (paramBody i)
    if isPure st.inst = true then
      match st.results with
      | [v] => pure (.yield (s2.1, s2.2, s.2.2.insert v st.inst))
      | _ => pure (.yield (s2.1, s2.2, s.2.2))
    else pure (.yield (s2.1, s2.2, s.2.2))
  | _ => do
    throw s!"ill-formed instruction defining {st.results}"
    pure (.yield (s.1, s.2.1, s.2.2))

def defsBody' (f : Function) (x : Block × Nat) (s : TyMap × BlkMap × PureMap) :
    Except String (ForInStep (TyMap × BlkMap × PureMap)) :=
  match x with
  | (b, i) => do
    let s1 ← forIn b.params (s.1, s.2.1) (paramBody i)
    let s2 ← forIn b.body (s1.1, s1.2, s.2.2) (stmtBody f i)
    pure (.yield (s2.1, s2.2.1, s2.2.2))

theorem defsBody_eq (f : Function) : defsBody f = defsBody' f := rfl

/-- Availability as `checkCore` checks it. -/
def availCk (f : Function) (defBlock : BlkMap) (i : Nat) (seen : Std.HashSet ValueId) (v : ValueId) :
    Bool :=
  seen.contains v || match defBlock.get? v with
    | some d => d != i && (Cfg.build f).dominates d i
    | none => false

def opBody (f : Function) (defBlock : BlkMap) (b : Block) (i : Nat) (seen : Std.HashSet ValueId)
    (v : ValueId) (_u : Unit) : Except String (ForInStep Unit) := do
  ensure (availCk f defBlock i seen v) s!"block{b.id}: use of v{v} not dominated by its definition"
  pure (ForInStep.yield PUnit.unit)

def stmtUseBody (f : Function) (types : TyMap) (defBlock : BlkMap) (b : Block) (i : Nat) (st : Stmt)
    (seen : Std.HashSet ValueId) : Except String (ForInStep (Std.HashSet ValueId)) := do
  forIn (operands st.inst) PUnit.unit (opBody f defBlock b i seen)
  if isPure st.inst = true then do
    ensure (pureTyped (fun v => types.get? v) f st.inst)
      s!"block{b.id}: ill-typed pure instruction defining {st.results}"
    pure (ForInStep.yield (st.results.foldl (·.insert ·) seen))
  else pure (ForInStep.yield (st.results.foldl (·.insert ·) seen))

def termOpBody (f : Function) (defBlock : BlkMap) (b : Block) (i : Nat) (seen : Std.HashSet ValueId)
    (v : ValueId) (_u : Unit) : Except String (ForInStep Unit) := do
  ensure (availCk f defBlock i seen v)
    s!"block{b.id}: terminator uses v{v}, not dominated by its definition"
  pure (ForInStep.yield PUnit.unit)

def callBody (f : Function) (types : TyMap) (b : Block) (bc : BlockCall) (_u : Unit) :
    Except String (ForInStep Unit) :=
  match (Cfg.build f).index.get? bc.block with
  | some j => do
    ensure (f.blocks.toArray[j]!.params.length == bc.args.length &&
      (f.blocks.toArray[j]!.params.zip bc.args).all fun x => types.get? x.2 == some x.1.2)
      s!"block{b.id}: arguments of block{bc.block}"
    pure (ForInStep.yield PUnit.unit)
  | _ => do
    throw s!"unknown block{bc.block}"
    pure (ForInStep.yield PUnit.unit)

def usesBody' (f : Function) (types : TyMap) (defBlock : BlkMap) (x : Block × Nat) (_u : Unit) :
    Except String (ForInStep Unit) :=
  match x with
  | (b, i) => do
    let seen ← forIn b.body (b.params.foldl (fun s p => s.insert p.1) ∅)
      (stmtUseBody f types defBlock b i)
    forIn (termOperands b.term) PUnit.unit (termOpBody f defBlock b i seen)
    forIn (termCalls b.term) PUnit.unit (callBody f types b)
    match b.term with
    | .brTable x _ _ => do
      ensure (types.get? x == some .i32) s!"block{b.id}: br_table index not i32"
      pure (ForInStep.yield PUnit.unit)
    | _ => pure (ForInStep.yield PUnit.unit)

theorem usesBody_eq (f : Function) (types : TyMap) (defBlock : BlkMap) :
    usesBody f types defBlock = usesBody' f types defBlock := rfl

/-! ## The bodies -/

theorem ensure_ok {c : Bool} {m : String} {u : Unit} : ensure c m = .ok u ↔ c = true := by
  unfold ensure
  cases c <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem allAlong_unit {α : Type} (P : α → Prop) :
    ∀ (l : List α), AllAlong (fun (_ : Unit) a => P a) (fun _ _ => ()) l () ↔ ∀ a ∈ l, P a
  | [] => by simp [AllAlong]
  | a :: l => by simp [AllAlong, allAlong_unit P l]

/-- A loop over `Unit` whose body checks `P`. -/
theorem forIn_unit_ok_iff {ε α : Type} {body : α → Unit → Except ε (ForInStep Unit)} (P : α → Prop)
    (hb : ∀ a u r, body a u = .ok r ↔ P a ∧ r = .yield ()) (l : List α) (r : Unit) :
    forIn l () body = .ok r ↔ ∀ a ∈ l, P a := by
  rw [forIn_ok_iff (fun _ a => P a) (fun _ _ => ()) (fun a s r => hb a s r) l () r]
  rw [allAlong_unit]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem paramBody_ok (i : Nat) (x : ValueId × Ty) (s : TyMap × BlkMap) (r) :
    paramBody i x s = .ok r ↔ defC s x ∧ r = .yield (defStep i s x) := by
  obtain ⟨v, t⟩ := x
  simp only [paramBody, ensure_bind_ok, defC, defStep, pure, Except.pure, Except.ok.injEq,
    Bool.not_eq_true']
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

theorem stmtBody_ok (f : Function) (i : Nat) (st : Stmt) (s : TyMap × BlkMap × PureMap) (r) :
    stmtBody f i st s = .ok r ↔ stmtDefC f i s st ∧ r = .yield (stmtDefStep f i s st) := by
  unfold stmtBody stmtDefC stmtDefStep
  cases hts : st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none) with
  | none =>
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff,
      not_and]
    rintro ⟨ts, h, -⟩; cases h
  | some ts =>
    simp only [bind_ok_iff, ensure_ok, beq_iff_eq, forIn_ok_iff defC (defStep i) (paramBody_ok i),
      Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨_, hlen, ⟨a, b⟩, ⟨hA, hab⟩, hk⟩
      refine ⟨⟨hlen, hA⟩, ?_⟩
      rw [← hab]
      split at hk
      · split at hk <;> simp_all [pure, Except.pure] <;> exact hk.symm
      · simp_all [pure, Except.pure]
    · rintro ⟨⟨hlen, hA⟩, rfl⟩
      refine ⟨(), hlen, _, ⟨hA, rfl⟩, ?_⟩
      split
      · split <;> simp_all [pure, Except.pure]
      · simp_all [pure, Except.pure]

theorem defsBody_ok (f : Function) (x : Block × Nat) (s : TyMap × BlkMap × PureMap) (r) :
    defsBody f x s = .ok r ↔ blockDefC f s x ∧ r = .yield (blockDefStep f s x) := by
  rw [defsBody_eq]
  obtain ⟨b, i⟩ := x
  simp only [defsBody', bind_ok_iff, forIn_ok_iff defC (defStep i) (paramBody_ok i),
    forIn_ok_iff (stmtDefC f i) (stmtDefStep f i) (stmtBody_ok f i), blockDefC, blockDefStep,
    pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨y1, ⟨h1, rfl⟩, y2, ⟨h2, rfl⟩, rfl⟩
    exact ⟨⟨h1, h2⟩, rfl⟩
  · rintro ⟨⟨h1, h2⟩, rfl⟩
    exact ⟨_, ⟨h1, rfl⟩, _, ⟨h2, rfl⟩, rfl⟩

/-- The definitions loop. -/
theorem defsLoop_ok (f : Function) (r) :
    forIn f.blocks.toArray.zipIdx ((∅ : TyMap), (∅ : BlkMap), (∅ : PureMap)) (defsBody f) = .ok r ↔
      DefsOk f ∧ r = defsState f := by
  rw [← Array.forIn_toList, Array.toList_zipIdx, List.toList_toArray,
    forIn_ok_iff (blockDefC f) (blockDefStep f) (defsBody_ok f)]
  rfl

/-! ## The uses loop -/

def seenStep (seen : Std.HashSet ValueId) (st : Stmt) : Std.HashSet ValueId :=
  st.results.foldl (·.insert ·) seen

def stmtUseC (f : Function) (types : TyMap) (defBlock : BlkMap) (i : Nat) (seen : Std.HashSet ValueId)
    (st : Stmt) : Prop :=
  (∀ v ∈ operands st.inst, availCk f defBlock i seen v = true) ∧
    (isPure st.inst = true → pureTyped (fun v => types.get? v) f st.inst = true)

def callOk (f : Function) (types : TyMap) (bc : BlockCall) : Prop :=
  ∃ j, (Cfg.build f).index.get? bc.block = some j ∧
    (f.blocks.toArray[j]!.params.length == bc.args.length &&
      (f.blocks.toArray[j]!.params.zip bc.args).all fun x => types.get? x.2 == some x.1.2) = true

def brTableOk (types : TyMap) : Terminator → Prop
  | .brTable x _ _ => types.get? x = some .i32
  | _ => True

def paramSeen (b : Block) : Std.HashSet ValueId := b.params.foldl (fun s p => s.insert p.1) ∅

def BlockUsesOk (f : Function) (types : TyMap) (defBlock : BlkMap) (x : Block × Nat) : Prop :=
  AllAlong (stmtUseC f types defBlock x.2) seenStep x.1.body (paramSeen x.1) ∧
    (∀ v ∈ termOperands x.1.term,
      availCk f defBlock x.2 (x.1.body.foldl seenStep (paramSeen x.1)) v = true) ∧
    (∀ bc ∈ termCalls x.1.term, callOk f types bc) ∧ brTableOk types x.1.term

theorem opBody_ok (f : Function) (defBlock : BlkMap) (b : Block) (i : Nat) (seen) (v : ValueId) (u r) :
    opBody f defBlock b i seen v u = .ok r ↔ availCk f defBlock i seen v = true ∧ r = .yield () := by
  simp only [opBody, ensure_bind_ok, pure, Except.pure, Except.ok.injEq]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

theorem termOpBody_ok (f : Function) (defBlock : BlkMap) (b : Block) (i : Nat) (seen) (v : ValueId)
    (u r) :
    termOpBody f defBlock b i seen v u = .ok r ↔ availCk f defBlock i seen v = true ∧ r = .yield () := by
  simp only [termOpBody, ensure_bind_ok, pure, Except.pure, Except.ok.injEq]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

theorem stmtUseBody_ok (f : Function) (types : TyMap) (defBlock : BlkMap) (b : Block) (i : Nat)
    (st : Stmt) (seen) (r) :
    stmtUseBody f types defBlock b i st seen = .ok r ↔
      stmtUseC f types defBlock i seen st ∧ r = .yield (seenStep seen st) := by
  simp only [stmtUseBody, bind_ok_iff,
    forIn_unit_ok_iff _ (opBody_ok f defBlock b i seen), stmtUseC, seenStep]
  constructor
  · rintro ⟨_, hops, hk⟩
    split at hk
    · rename_i hp
      simp only [bind_ok_iff, ensure_ok, pure, Except.pure, Except.ok.injEq] at hk
      obtain ⟨_, ht, rfl⟩ := hk
      exact ⟨⟨hops, fun _ => ht⟩, rfl⟩
    · rename_i hp
      simp only [pure, Except.pure, Except.ok.injEq] at hk
      exact ⟨⟨hops, fun h => absurd h hp⟩, hk.symm⟩
  · rintro ⟨⟨hops, ht⟩, rfl⟩
    refine ⟨(), hops, ?_⟩
    split
    · rename_i hp
      rw [ensure_bind_ok]; exact ⟨ht hp, rfl⟩
    · rfl

theorem callBody_ok (f : Function) (types : TyMap) (b : Block) (bc : BlockCall) (u r) :
    callBody f types b bc u = .ok r ↔ callOk f types bc ∧ r = .yield () := by
  unfold callBody callOk
  cases hj : (Cfg.build f).index.get? bc.block with
  | none =>
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff,
      not_and]
    rintro ⟨j, h, -⟩; cases h
  | some j =>
    simp only [ensure_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq,
      exists_eq_left']
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

theorem brBody_ok (types : TyMap) (m : String) (t : Terminator) (r : ForInStep Unit) :
    (match t with
     | .brTable x _ _ => do
       ensure (types.get? x == some .i32) m
       pure (ForInStep.yield PUnit.unit)
     | _ => pure (ForInStep.yield PUnit.unit) : Except String (ForInStep Unit)) = .ok r ↔
      brTableOk types t ∧ r = .yield () := by
  cases t <;>
    first
    | (simp only [brTableOk, pure, Except.pure, Except.ok.injEq, true_and]
       exact ⟨fun h => h.symm, fun h => h.symm⟩)
    | (simp only [brTableOk, ensure_bind_ok, beq_iff_eq, pure, Except.pure, Except.ok.injEq]
       exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩)

theorem usesBody_ok (f : Function) (types : TyMap) (defBlock : BlkMap) (x : Block × Nat) (u r) :
    usesBody f types defBlock x u = .ok r ↔ BlockUsesOk f types defBlock x ∧ r = .yield () := by
  rw [usesBody_eq]
  obtain ⟨b, i⟩ := x
  simp only [usesBody', bind_ok_iff,
    forIn_ok_iff (stmtUseC f types defBlock i) seenStep (stmtUseBody_ok f types defBlock b i),
    BlockUsesOk, paramSeen, brBody_ok]
  simp only [forIn_unit_ok_iff _ (termOpBody_ok f defBlock b i _),
    forIn_unit_ok_iff _ (callBody_ok f types b)]
  constructor
  · rintro ⟨_, ⟨hA, rfl⟩, _, hops, _, hcalls, hbr, rfl⟩
    exact ⟨⟨hA, hops, hcalls, hbr⟩, rfl⟩
  · rintro ⟨⟨hA, hops, hcalls, hbr⟩, rfl⟩
    exact ⟨_, ⟨hA, rfl⟩, (), hops, (), hcalls, hbr, rfl⟩

theorem usesLoop_ok (f : Function) (types : TyMap) (defBlock : BlkMap) (r : Unit) :
    forIn f.blocks.toArray.zipIdx () (usesBody f types defBlock) = .ok r ↔
      ∀ x ∈ f.blocks.zipIdx, BlockUsesOk f types defBlock x := by
  rw [← Array.forIn_toList, Array.toList_zipIdx, List.toList_toArray,
    forIn_unit_ok_iff _ (usesBody_ok f types defBlock)]

/-! ## `checkCore` -/

theorem reachBody_ok (f : Function) (i : Nat) (u r) :
    reachBody f i u = .ok r ↔ (Cfg.build f).reachable i = true ∧ r = .yield () := by
  simp only [reachBody, ensure_bind_ok, pure, Except.pure, Except.ok.injEq]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

/-- When `checkCore` succeeds (module doc). -/
def CoreOk (f : Function) : Prop :=
  0 < (Cfg.build f).size ∧ (Cfg.build f).index.size = (Cfg.build f).size ∧
    (∀ i < (Cfg.build f).size, (Cfg.build f).reachable i = true) ∧ DefsOk f ∧
    f.blocks.toArray[0]!.params.map (·.2) = f.sig.params.map (·.ty) ∧
    ∀ x ∈ f.blocks.zipIdx, BlockUsesOk f (defsState f).1 (defsState f).2.1 x

/-- What `checkCore` returns. -/
def coreInfo (f : Function) : Info :=
  { cfg := Cfg.build f, types := (defsState f).1, defBlock := (defsState f).2.1,
    pureDef := (defsState f).2.2 }

/-- **`checkCore` succeeds exactly on `CoreOk`, returning `coreInfo`.** -/
theorem checkCore_ok_iff (f : Function) (i : Info) :
    checkCore f = .ok i ↔ CoreOk f ∧ i = coreInfo f := by
  rw [checkCore_eq]
  simp only [bind_ok_iff, ensure_ok, decide_eq_true_eq, beq_iff_eq,
    Std.Legacy.Range.forIn_eq_forIn_range', forIn_unit_ok_iff _ (reachBody_ok f), defsLoop_ok,
    usesLoop_ok, pure, Except.pure, Except.ok.injEq]
  simp only [Std.Legacy.Range.size, List.mem_range'_1]
  constructor
  · rintro ⟨_, h1, _, h2, _, h3, _, ⟨h4, rfl⟩, _, h5, _, h6, rfl⟩
    exact ⟨⟨h1, h2, fun i hi => h3 i (by omega), h4, h5, h6⟩, rfl⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩
    exact ⟨(), h1, (), h2, (), fun i hi => h3 i (by omega), _, ⟨h4, rfl⟩, (), h5, (), h6, rfl⟩

theorem check_ok_iff (f : Function) (i : Info) :
    check f = .ok i ↔ CoreOk f ∧ i = coreInfo f ∧
      wfCert f (Cfg.build f) (defsState f).1 = true := by
  unfold check
  simp only [bind_ok_iff, checkCore_ok_iff, ensure_ok, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨_, ⟨hc, rfl⟩, _, hw, rfl⟩; exact ⟨hc, rfl, hw⟩
  · rintro ⟨hc, rfl, hw⟩; exact ⟨_, ⟨hc, rfl⟩, (), hw, rfl⟩

/-! ## `AllAlong` -/

theorem allAlong_append {α β : Type} (C : β → α → Prop) (g : β → α → β) :
    ∀ (l1 l2 : List α) (s : β),
      AllAlong C g (l1 ++ l2) s ↔ AllAlong C g l1 s ∧ AllAlong C g l2 (l1.foldl g s)
  | [], l2, s => by simp [AllAlong]
  | a :: l1, l2, s => by
    simp only [List.cons_append, AllAlong, List.foldl_cons, allAlong_append C g l1 l2, and_assoc]

theorem allAlong_iff {α β : Type} (C : β → α → Prop) (g : β → α → β) :
    ∀ (l : List α) (s : β),
      AllAlong C g l s ↔ ∀ (j : Nat) (a : α), l[j]? = some a → C ((l.take j).foldl g s) a
  | [], s => by simp [AllAlong]
  | a :: l, s => by
    simp only [AllAlong, allAlong_iff C g l (g s a)]
    constructor
    · rintro ⟨h0, h⟩ j b hb
      cases j with
      | zero => simp at hb; subst hb; simpa using h0
      | succ j => simpa using h j b (by simpa using hb)
    · intro h
      exact ⟨by simpa using h 0 a rfl, fun j b hb => by simpa using h (j + 1) b (by simpa using hb)⟩

/-! ## The definitions as a list -/

/-- A definition event: value, type, block. -/
abbrev DefEv := ValueId × Ty × Nat

def evStep (s : TyMap × BlkMap) (e : DefEv) : TyMap × BlkMap :=
  (s.1.insert e.1 e.2.1, s.2.insert e.1 e.2.2)

def evC (s : TyMap × BlkMap) (e : DefEv) : Prop := s.1.contains e.1 = false

/-- The result types of a statement (as `checkCore` computes them). -/
def stmtTys (f : Function) (st : Stmt) : Option (List Ty) :=
  st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none)

def stmtEvs (f : Function) (i : Nat) (st : Stmt) : List DefEv :=
  match stmtTys f st with
  | some ts => (st.results.zip ts).map fun p => (p.1, p.2, i)
  | none => []

def blockEvs (f : Function) (b : Block) (i : Nat) : List DefEv :=
  b.params.map (fun p => (p.1, p.2, i)) ++ b.body.flatMap (stmtEvs f i)

/-- Every definition of `f`, in `checkCore`'s order. -/
def defList (f : Function) : List DefEv := f.blocks.zipIdx.flatMap fun x => blockEvs f x.1 x.2

/-- Every statement's result types are known, with the right arity. -/
def Arity (f : Function) : Prop :=
  ∀ b ∈ f.blocks, ∀ st ∈ b.body, ∃ ts, stmtTys f st = some ts ∧ ts.length = st.results.length

theorem allAlong_map {α γ β : Type} (C : β → γ → Prop) (g : β → γ → β) (h : α → γ) :
    ∀ (l : List α) (s : β),
      AllAlong C g (l.map h) s ↔ AllAlong (fun s a => C s (h a)) (fun s a => g s (h a)) l s
  | [], s => by simp [AllAlong]
  | a :: l, s => by simp [AllAlong, allAlong_map C g h l]

theorem foldl_defStep (i : Nat) (l : List (ValueId × Ty)) (s : TyMap × BlkMap) :
    l.foldl (defStep i) s = (l.map fun p => (p.1, p.2, i)).foldl evStep s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, List.map_cons]; rw [ih]; rfl

theorem allAlong_defStep (i : Nat) (l : List (ValueId × Ty)) (s : TyMap × BlkMap) :
    AllAlong defC (defStep i) l s ↔ AllAlong evC evStep (l.map fun p => (p.1, p.2, i)) s := by
  rw [allAlong_map]; rfl

theorem stmtDefStep_proj (f : Function) (i : Nat) (s : TyMap × BlkMap × PureMap) (st : Stmt) :
    ((stmtDefStep f i s st).1, (stmtDefStep f i s st).2.1) = (stmtEvs f i st).foldl evStep (s.1, s.2.1) := by
  unfold stmtDefStep stmtEvs stmtTys
  cases h : st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none) with
  | none => rfl
  | some ts => simp only [foldl_defStep]

theorem stmtDefC_iff (f : Function) (i : Nat) (s : TyMap × BlkMap × PureMap) (st : Stmt) :
    stmtDefC f i s st ↔ (∃ ts, stmtTys f st = some ts ∧ ts.length = st.results.length) ∧
      AllAlong evC evStep (stmtEvs f i st) (s.1, s.2.1) := by
  unfold stmtDefC stmtEvs stmtTys
  cases h : st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none) with
  | none => simp
  | some ts => simp [allAlong_defStep, AllAlong]

theorem allAlong_stmts (f : Function) (i : Nat) :
    ∀ (body : List Stmt) (s : TyMap × BlkMap × PureMap),
      (AllAlong (stmtDefC f i) (stmtDefStep f i) body s ↔
        (∀ st ∈ body, ∃ ts, stmtTys f st = some ts ∧ ts.length = st.results.length) ∧
          AllAlong evC evStep (body.flatMap (stmtEvs f i)) (s.1, s.2.1)) ∧
      ((body.foldl (stmtDefStep f i) s).1, (body.foldl (stmtDefStep f i) s).2.1) =
        (body.flatMap (stmtEvs f i)).foldl evStep (s.1, s.2.1)
  | [], s => by simp [AllAlong]
  | st :: body, s => by
    have ih := allAlong_stmts f i body (stmtDefStep f i s st)
    have hp := stmtDefStep_proj f i s st
    simp only [AllAlong, List.flatMap_cons, allAlong_append, List.foldl_append, List.foldl_cons,
      List.mem_cons, forall_eq_or_imp, stmtDefC_iff]
    rw [ih.1, ← hp]
    refine ⟨?_, ih.2⟩
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem allAlong_blocks (f : Function) :
    ∀ (l : List (Block × Nat)) (s : TyMap × BlkMap × PureMap),
      (AllAlong (blockDefC f) (blockDefStep f) l s ↔
        (∀ x ∈ l, ∀ st ∈ x.1.body, ∃ ts, stmtTys f st = some ts ∧ ts.length = st.results.length) ∧
          AllAlong evC evStep (l.flatMap fun x => blockEvs f x.1 x.2) (s.1, s.2.1)) ∧
      ((l.foldl (blockDefStep f) s).1, (l.foldl (blockDefStep f) s).2.1) =
        (l.flatMap fun x => blockEvs f x.1 x.2).foldl evStep (s.1, s.2.1)
  | [], s => by simp [AllAlong]
  | x :: l, s => by
    obtain ⟨b, i⟩ := x
    have ih := allAlong_blocks f l (blockDefStep f s (b, i))
    have hs := allAlong_stmts f i b.body
      ((b.params.foldl (defStep i) (s.1, s.2.1)).1, (b.params.foldl (defStep i) (s.1, s.2.1)).2, s.2.2)
    have hstep : ((blockDefStep f s (b, i)).1, (blockDefStep f s (b, i)).2.1) =
        (blockEvs f b i).foldl evStep (s.1, s.2.1) := by
      simp only [blockDefStep, blockEvs, List.foldl_append]
      rw [hs.2, foldl_defStep]
    simp only [AllAlong, List.flatMap_cons, allAlong_append, List.foldl_append, List.foldl_cons,
      List.mem_cons, forall_eq_or_imp]
    rw [ih.1, ← hstep]
    refine ⟨?_, ih.2⟩
    simp only [blockDefC, blockEvs, allAlong_append, allAlong_defStep, hs.1, ← foldl_defStep]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩; exact ⟨⟨h2, h4⟩, ⟨h1, h3⟩, h5⟩
    · rintro ⟨⟨h2, h4⟩, ⟨h1, h3⟩, h5⟩; exact ⟨⟨h1, h2, h3⟩, h4, h5⟩

theorem defsOk_iff (f : Function) :
    DefsOk f ↔ Arity f ∧ AllAlong evC evStep (defList f) (∅, ∅) := by
  have := (allAlong_blocks f f.blocks.zipIdx (∅, ∅, ∅)).1
  rw [DefsOk, this, defList]
  simp only [Arity]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun b hb st hst => by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
      exact h1 (b, i) (List.mem_zipIdx_iff_getElem?.2 hi) st hst, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x hx st hst => h1 x.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hx)) st hst, h2⟩

theorem defsState_proj (f : Function) :
    ((defsState f).1, (defsState f).2.1) = (defList f).foldl evStep (∅, ∅) :=
  (allAlong_blocks f f.blocks.zipIdx (∅, ∅, ∅)).2

theorem foldl_evStep_contains (l : List DefEv) (s : TyMap × BlkMap) (v : ValueId) :
    (l.foldl evStep s).1.contains v = (s.1.contains v || (l.map (·.1)).contains v) := by
  induction l generalizing s with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, ih]
    simp only [evStep, Std.HashMap.contains_insert, List.map_cons, List.contains_cons]
    by_cases hv : e.1 = v
    · subst hv; simp
    · have h1 : (e.1 == v) = false := by simpa using hv
      have h2 : (v == e.1) = false := by simpa using Ne.symm hv
      simp [h1, h2]

theorem allAlong_evC_iff (l : List DefEv) (s : TyMap × BlkMap) :
    AllAlong evC evStep l s ↔ (∀ e ∈ l, s.1.contains e.1 = false) ∧ (l.map (·.1)).Nodup := by
  induction l generalizing s with
  | nil => simp [AllAlong]
  | cons e l ih =>
    simp only [AllAlong, ih, evC, List.mem_cons, forall_eq_or_imp, List.map_cons, List.nodup_cons,
      evStep, Std.HashMap.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      List.mem_map]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, fun e' he' => (h2 e' he').2⟩, fun ⟨e', he', hv⟩ => (h2 e' he').1 hv.symm, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, fun e' he' => ⟨fun hv => h3 ⟨e', he', hv.symm⟩, h2 e' he'⟩, h4⟩

theorem foldl_evStep_get (l : List DefEv) (hl : (l.map (·.1)).Nodup) (s : TyMap × BlkMap) :
    (∀ e ∈ l, (l.foldl evStep s).1[e.1]? = some e.2.1 ∧ (l.foldl evStep s).2[e.1]? = some e.2.2) ∧
      ∀ v, v ∉ l.map (·.1) → (l.foldl evStep s).1[v]? = s.1[v]? ∧ (l.foldl evStep s).2[v]? = s.2[v]? := by
  induction l generalizing s with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    have ih' := ih hl.2 (evStep s e)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp, List.map_cons, not_or]
    refine ⟨⟨?_, ih'.1⟩, fun v ⟨hv1, hv2⟩ => ?_⟩
    · rw [(ih'.2 e.1 hl.1).1, (ih'.2 e.1 hl.1).2]
      simp [evStep]
    · rw [(ih'.2 v hv2).1, (ih'.2 v hv2).2]
      have h1 : (e.1 == v) = false := by simpa using Ne.symm hv1
      simp [evStep, Std.HashMap.getElem?_insert, h1]

/-- The types and defining blocks `checkCore` records, on a function with distinct definitions. -/
theorem defsState_get (f : Function) (hn : ((defList f).map (·.1)).Nodup) :
    (∀ e ∈ defList f, (defsState f).1[e.1]? = some e.2.1 ∧ (defsState f).2.1[e.1]? = some e.2.2) ∧
      ∀ v, v ∉ (defList f).map (·.1) → (defsState f).1[v]? = none ∧ (defsState f).2.1[v]? = none := by
  have hp := defsState_proj f
  have h := foldl_evStep_get (defList f) hn (∅, ∅)
  rw [← hp] at h
  simpa using h

/-! ## The CFG depends only on block ids and successors -/

/-- The part of a function `Cfg.build` reads. -/
def cfgShape (f : Function) : List (BlockId × List BlockId) :=
  f.blocks.map fun b => (b.id, termSuccs b.term)

theorem build_congr {f g : Function} (h : cfgShape f = cfgShape g) : Cfg.build f = Cfg.build g := by
  have hid : f.blocks.toArray.map (·.id) = g.blocks.toArray.map (·.id) := by
    have := congrArg (List.map Prod.fst) h
    simp only [cfgShape, List.map_map] at this
    simp only [List.map_toArray]
    exact congrArg List.toArray this
  have hsu : ∀ idx : BlockId → Option Nat,
      f.blocks.toArray.map (fun b => ((termSuccs b.term).filterMap idx).eraseDups) =
        g.blocks.toArray.map (fun b => ((termSuccs b.term).filterMap idx).eraseDups) := by
    intro idx
    have := congrArg (List.map (fun p => (p.2.filterMap idx).eraseDups)) h
    simp only [cfgShape, List.map_map] at this
    simp only [List.map_toArray]
    exact congrArg List.toArray this
  unfold Cfg.build
  dsimp only
  rw [hid, hsu]

/-! ## Completeness of `ancB` and of `wfCert` -/

/-- `l` lists the blocks of the `idom` chain from `b` up to `a` (excluded). -/
def ChainTo (idom : Array (Option Nat)) : List Nat → Nat → Nat → Prop
  | [], a, b => a = b
  | x :: l, a, b => x = b ∧ ∃ c, idom[b]?.join = some c ∧ ChainTo idom l a c

theorem Anc.chain {idom : Array (Option Nat)} {a b : Nat} (h : Anc idom a b) :
    ∃ l, ChainTo idom l a b := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | up hc _ ih => obtain ⟨l, hl⟩ := ih; exact ⟨_ :: l, rfl, _, hc, hl⟩

theorem ChainTo.ancB_true {idom : Array (Option Nat)} (l : List Nat) :
    ∀ {a b : Nat}, ChainTo idom l a b → ∀ fuel, l.length ≤ fuel → ancB idom fuel a b = true := by
  induction l with
  | nil =>
    intro a b h fuel _
    simp only [ChainTo] at h; subst h
    cases fuel <;> simp [ancB]
  | cons x l ih =>
    intro a b h fuel hle
    obtain ⟨_, c, hc, hl⟩ := h
    cases fuel with
    | zero => simp at hle
    | succ fuel =>
      have := ih hl fuel (by simp at hle; omega)
      simp [ancB, hc, this]

theorem ChainTo.lt {idom : Array (Option Nat)} (l : List Nat) :
    ∀ {a b : Nat}, ChainTo idom l a b → ∀ x ∈ l, x < idom.size := by
  induction l with
  | nil => intro a b _ x hx; simp at hx
  | cons y l ih =>
    intro a b h x hx
    obtain ⟨hy, c, hc, hl⟩ := h
    subst hy
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rcases Nat.lt_or_ge x idom.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hc; cases hc
    · exact ih hl x hx

theorem ChainTo.rank_le {idom : Array (Option Nat)} {rank : Nat → Nat}
    (hr : ∀ b c, idom[b]?.join = some c → rank c < rank b) (l : List Nat) :
    ∀ {a b : Nat}, ChainTo idom l a b → ∀ x ∈ l, rank x ≤ rank b := by
  induction l with
  | nil => intro a b _ x hx; simp at hx
  | cons y l ih =>
    intro a b h x hx
    obtain ⟨hy, c, hc, hl⟩ := h
    subst hy
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.le_refl _
    · have := ih hl x hx; have := hr _ _ hc; omega

theorem ChainTo.nodup {idom : Array (Option Nat)} {rank : Nat → Nat}
    (hr : ∀ b c, idom[b]?.join = some c → rank c < rank b) (l : List Nat) :
    ∀ {a b : Nat}, ChainTo idom l a b → l.Nodup := by
  induction l with
  | nil => intros; exact List.nodup_nil
  | cons y l ih =>
    intro a b h
    obtain ⟨hy, c, hc, hl⟩ := h
    subst hy
    refine List.nodup_cons.2 ⟨fun hy => ?_, ih hl⟩
    have := ChainTo.rank_le hr l hl y hy; have := hr _ _ hc; omega

/-- **`ancB` is complete** on a tree whose ranks decrease along `idom`. -/
theorem ancB_complete {idom : Array (Option Nat)} {rank : Nat → Nat}
    (hr : ∀ b c, idom[b]?.join = some c → rank c < rank b) {a b : Nat} (h : Anc idom a b) :
    ancB idom idom.size a b = true := by
  obtain ⟨l, hl⟩ := h.chain
  refine ChainTo.ancB_true l hl _ ?_
  have := (ChainTo.nodup hr l hl).length_le_of_subset (l₂ := List.range idom.size)
    (fun x hx => List.mem_range.2 (ChainTo.lt l hl x hx))
  simpa using this

theorem availB_complete {W : WfData} (hr : ∀ b c, W.idom[b]?.join = some c → W.rank c < W.rank b)
    {i k v} (h : Avail W i k v) : availB W.dm (ancB W.idom W.idom.size) i k v = true := by
  obtain ⟨d, t, hd, h⟩ := h
  simp only [availB, hd]
  rcases h with ⟨rfl, h⟩ | ⟨hne, h⟩
  · simp [h]
  · simp [hne, ancB_complete hr h]

/-- **`wfCert` is complete**: the converse of `wfCert_sound`. -/
theorem wfCert_complete {f : Function} {info : Info} (h : Wf f (wfData f info)) :
    wfCert f info.cfg info.types = true := by
  have hr := h.rank
  simp only [wfCert, Bool.and_eq_true, List.all_eq_true]
  have hmem : ∀ {α : Type} {l : List α} {x : α × Nat}, x ∈ l.zipIdx → l[x.2]? = some x.1 :=
    fun h => List.mem_zipIdx_iff_getElem?.1 h
  refine ⟨⟨⟨⟨fun x hx => ?_, fun x hx => ?_⟩, ?_⟩, fun b _ => ?_⟩, fun x hx => ?_⟩
  · simpa [wfData, Std.HashMap.get?_eq_getElem?] using h.ids _ _ (hmem hx)
  · simpa [wfData] using h.sites _ _ hx
  · simpa [wfData] using h.root
  · cases hb : info.cfg.idom[b]?.join with
    | none => simp
    | some c => simpa [wfData] using hr b c (by simpa [wfData] using hb)
  · obtain ⟨b, i⟩ := x
    have hb := hmem hx
    simp only at hb
    refine ⟨⟨⟨fun p hp => ?_, fun y hy => ?_⟩, fun v hv => ?_⟩, fun bid hid => ?_⟩
    · simpa [wfData, Std.HashMap.get?_eq_getElem?] using h.params i b hb p hp
    · obtain ⟨st, j⟩ := y
      have hst := hmem hy
      simp only at hst
      refine ⟨⟨fun v hv => ?_, ?_⟩, ?_⟩
      · simpa [wfData] using availB_complete hr (h.uses i b hb j st hst v hv)
      · obtain ⟨ts, hts, hlen, htys⟩ := h.results i b hb j st hst
        have hts' : st.inst.resultTypes (fun r => (f.externs.lookup r).map (·.sig)) (fun _ => none) =
            some ts := hts
        rw [hts']
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
        refine ⟨hlen, fun ⟨r, t⟩ hz => ?_⟩
        obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hz
        rw [List.getElem?_zip_eq_some] at hn
        have := htys n r hn.1
        rw [hn.2] at this
        simpa [wfData] using this
      · cases hp : isPure st.inst with
        | false => simp
        | true => simpa [wfData, Std.HashMap.get?_eq_getElem?] using h.pure i b hb j st hst hp
    · simpa [wfData] using availB_complete hr (h.termUses i b hb v hv)
    · obtain ⟨j, b', hj, hbj, hid', hanc⟩ := h.edges i b hb bid hid
      simp only [wfData] at hj
      simp only [Std.HashMap.get?_eq_getElem?] at hj
      simp only [Std.HashMap.get?_eq_getElem?, hj, hbj, Option.map_some, hid', beq_self_eq_true,
        Bool.true_and]
      cases hc : info.cfg.idom[j]?.join with
      | none => simp
      | some c => exact ancB_complete hr (hanc c (by simpa [wfData] using hc))

/-! ## Definitions, sites, and `defMap` -/

theorem mem_defList {f : Function} {e : DefEv} :
    e ∈ defList f ↔ ∃ i b, f.blocks[i]? = some b ∧
      ((∃ p ∈ b.params, e = (p.1, p.2, i)) ∨ ∃ st ∈ b.body, e ∈ stmtEvs f i st) := by
  simp only [defList, blockEvs, List.mem_flatMap, List.mem_append, List.mem_map,
    List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨b, i⟩, hb, ⟨p, hp, rfl⟩ | ⟨st, hst, he⟩⟩
    · exact ⟨i, b, hb, .inl ⟨p, hp, rfl⟩⟩
    · exact ⟨i, b, hb, .inr ⟨st, hst, he⟩⟩
  · rintro ⟨i, b, hb, ⟨p, hp, rfl⟩ | ⟨st, hst, he⟩⟩
    · exact ⟨(b, i), hb, .inl ⟨p, hp, rfl⟩⟩
    · exact ⟨(b, i), hb, .inr ⟨st, hst, he⟩⟩

theorem stmtEvs_map_fst {f : Function} {i : Nat} {st : Stmt} {ts : List Ty}
    (hts : stmtTys f st = some ts) (hlen : ts.length = st.results.length) :
    (stmtEvs f i st).map (·.1) = st.results := by
  unfold stmtEvs; rw [hts]; simp only [List.map_map]
  have : ((fun x : DefEv => x.1) ∘ fun p : ValueId × Ty => (p.1, p.2, i)) = Prod.fst := by
    funext p; rfl
  rw [this]; exact List.map_fst_zip (by omega)

theorem flatMap_congr' {α β : Type} {l : List α} {g h : α → List β} (hg : ∀ a ∈ l, g a = h a) :
    l.flatMap g = l.flatMap h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [hg a (List.mem_cons_self ..), ih fun x hx => hg x (List.mem_cons_of_mem _ hx)]

theorem sites_body_fst (i : Nat) (body : List Stmt) : ∀ k,
    ((body.zipIdx k).flatMap fun x => x.1.results.map fun r => (r, i, x.2 + 1)).map (·.1) =
      body.flatMap (·.results) := by
  induction body with
  | nil => intro k; rfl
  | cons st body ih =>
    intro k
    simp only [List.zipIdx_cons, List.flatMap_cons, List.map_append, ih (k + 1), List.map_map]
    congr 1
    conv => rhs; rw [← List.map_id st.results]
    rfl

theorem evs_body_fst {f : Function} (i : Nat) (body : List Stmt)
    (ha : ∀ st ∈ body, ∃ ts, stmtTys f st = some ts ∧ ts.length = st.results.length) :
    (body.flatMap (stmtEvs f i)).map (·.1) = body.flatMap (·.results) := by
  induction body with
  | nil => rfl
  | cons st body ih =>
    simp only [List.flatMap_cons, List.map_append]
    obtain ⟨ts, hts, hlen⟩ := ha st (List.mem_cons_self ..)
    rw [stmtEvs_map_fst hts hlen, ih fun x hx => ha x (List.mem_cons_of_mem _ hx)]

/-- On functions with known result types, the defined values in `defSites` order are those of
`defList`. -/
theorem defSites_map_fst {f : Function} (ha : Arity f) :
    (defSites f).map (·.1) = (defList f).map (·.1) := by
  simp only [defSites, defList, List.map_flatMap]
  apply flatMap_congr'
  rintro ⟨b, i⟩ hx
  have hb : b ∈ f.blocks := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hx)
  simp only [blockEvs, List.map_append, List.map_map]
  rw [sites_body_fst, evs_body_fst i b.body (ha b hb)]
  rfl

theorem foldl_insert_notin {l : List (ValueId × Nat × Nat)} {v : ValueId} (hv : v ∉ l.map (·.1)) :
    ∀ m : Std.HashMap ValueId (Nat × Nat),
      (l.foldl (fun m (x : ValueId × Nat × Nat) => m.insert x.1 x.2) m).get? v = m.get? v := by
  induction l with
  | nil => intro m; rfl
  | cons x l ih =>
    intro m
    simp only [List.map_cons, List.mem_cons, not_or] at hv
    rw [List.foldl_cons, ih hv.2]
    have : (x.1 == v) = false := by simpa using Ne.symm hv.1
    simp [Std.HashMap.getElem?_insert, this]

/-- `defMap` on a function whose values are defined once. -/
theorem defMap_get_iff {f : Function} (hn : ((defSites f).map (·.1)).Nodup) (v : ValueId)
    (s : Nat × Nat) : (defMap f).get? v = some s ↔ (v, s) ∈ defSites f := by
  constructor
  · intro h
    rcases foldl_insert_get _ v s h with h | h
    · simp at h
    · exact h
  · intro h
    unfold defMap
    generalize (∅ : Std.HashMap ValueId (Nat × Nat)) = m
    revert hn h
    generalize defSites f = l
    intro hn h
    induction l generalizing m with
    | nil => simp at h
    | cons x l ih =>
      simp only [List.map_cons, List.nodup_cons] at hn
      simp only [List.mem_cons] at h
      rw [List.foldl_cons]
      rcases h with rfl | h
      · rw [foldl_insert_notin hn.1]; simp
      · exact ih _ hn.2 h

/-- `pureTyped` reads only the operand types and the function's slots and globals. -/
theorem pureTyped_congr {ty ty' : ValueId → Option Ty} {f f' : Function} {i : Inst}
    (ht : ∀ x ∈ operands i, ty x = ty' x) (hs : f.slots = f'.slots) (hg : f.globals = f'.globals) :
    pureTyped ty f i = pureTyped ty' f' i := by
  cases i <;> simp_all [pureTyped, operands]

end Opt
