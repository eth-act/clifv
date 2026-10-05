import FV.Backend.Proof.LowerLoopCode
import FV.Backend.Proof.PrepareComplete

/-!
# `buildCtx`, functionally

`buildCtx`'s loops, as folds (`maxVOf`, `ctxModel`), with the conditions it checks on the way
(`buildCtx_model`); from them the facts the completeness proof uses (`ctxFacts_of`,
`ctxOk_complete` in `LowerLoop.lean`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## `forIn` in `Except`, as a fold -/

/-- A loop whose body always yields is a fold. -/
theorem forIn_okYield {ε α β : Type} (g : α → β → β) : ∀ (l : List α) (init : β),
    forIn l init (fun a b => (Except.ok (.yield (g a b)) : Except ε (ForInStep β))) =
      .ok (l.foldl (fun b a => g a b) init)
  | [], _ => rfl
  | a :: l, init => by
    rw [List.forIn_cons]
    exact forIn_okYield g l (g a init)

/-- A loop whose body, when it succeeds, yields `g b a` and satisfies `C a b`: on success the
result is the fold, and every element satisfied `C` at its state. -/
theorem forIn_foldC {ε α β : Type} (body : α → β → Except ε (ForInStep β)) (g : β → α → β)
    (C : α → β → Prop) (hb : ∀ a b r, body a b = .ok r → r = .yield (g b a) ∧ C a b) :
    ∀ (l : List α) (init r : β), forIn l init body = .ok r →
      r = l.foldl g init ∧ ∀ (i : Nat) (a : α), l[i]? = some a → C a ((l.take i).foldl g init)
  | [], init, r, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun i a h => by simp at h⟩
  | a :: l, init, r, h => by
    rw [List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i st hst
    obtain ⟨rfl, hc⟩ := hb a init st hst
    obtain ⟨h1, h2⟩ := forIn_foldC body g C hb l (g init a) r h
    refine ⟨h1, fun i x hx => ?_⟩
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; exact hc
    | succ i => exact h2 i x (by simpa using hx)

/-! ## The model of `buildCtx` -/

/-- `buildCtx`'s result types of a statement (`[]` where they do not compute). -/
def tysOf (f : Clif.Function) (s : Clif.Stmt) : List Clif.Ty :=
  (s.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).getD []

/-- `buildCtx`'s instruction data of a statement (`default` where it does not compute). -/
def dataOf (f : Clif.Function) (s : Clif.Stmt) : V :=
  match instData f s.inst with
  | .ok d => d
  | .error _ => default

/-- `buildCtx`'s table entry of a statement. -/
def infoOf (f : Clif.Function) (s : Clif.Stmt) : IInfo :=
  ⟨dataOf f s, s.results, (tysOf f s).map CTy.ofClif, some s.inst⟩

/-- The terminator's placeholder entry. -/
def placeholder : IInfo := ⟨.op .unit, [], [], none⟩

/-- `buildCtx`'s update for result `p.1` of type `p.2` of instruction `n`. -/
def resStepM (n : Nat) (a : Array (Option CTy) × Array (Option Nat)) (p : Nat × Clif.Ty) :
    Array (Option CTy) × Array (Option Nat) :=
  (a.1.set! p.1 (some (CTy.ofClif p.2)), a.2.set! p.1 (some n))

/-- `buildCtx`'s update for a statement. -/
def stmtStepM (f : Clif.Function) (a : Array (Option CTy) × Array (Option Nat) × Array IInfo)
    (s : Clif.Stmt) : Array (Option CTy) × Array (Option Nat) × Array IInfo :=
  let q := (s.results.zip (tysOf f s)).foldl (resStepM a.2.2.size) (a.1, a.2.1)
  (q.1, q.2, a.2.2.push (infoOf f s))

/-- `buildCtx`'s update for a block parameter. -/
def parStepM (vt : Array (Option CTy)) (p : Nat × Clif.Ty) : Array (Option CTy) :=
  vt.set! p.1 (some (CTy.ofClif p.2))

/-- The state of `buildCtx`'s main loop. -/
abbrev CState := Array (Option CTy) × Array (Option Nat) × Array IInfo × Array (Nat × Nat)

/-- `buildCtx`'s update for a block. -/
def blockStepM (f : Clif.Function) (a : CState) (b : Clif.Block) : CState :=
  let q := b.body.foldl (stmtStepM f) (b.params.foldl parStepM a.1, a.2.1, a.2.2.1)
  (q.1, q.2.1, q.2.2.push placeholder, a.2.2.2.push (a.2.2.1.size, (q.2.2.push placeholder).size))

/-- `buildCtx`'s main loop. -/
def ctxModel (f : Clif.Function) (M : Nat) : CState :=
  f.blocks.foldl (blockStepM f) (Array.replicate M none, Array.replicate M none, #[], #[])

/-- `buildCtx`'s number of values. -/
def maxVOf (f : Clif.Function) : Nat :=
  f.blocks.foldl (fun m b => b.body.foldl (fun m s => s.results.foldl (fun m r => max m (r + 1)) m)
    (b.params.foldl (fun m p => max m (p.1 + 1)) m)) 0

/-- What `buildCtx` checks of a statement. -/
def StmtC (f : Clif.Function) (s : Clif.Stmt) : Prop :=
  (∃ d, instData f s.inst = .ok d) ∧
  (∃ tys, s.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys ∧
    tys.length = s.results.length) ∧ ∀ t ∈ tysOf f s, t ≠ .i128

/-- What `buildCtx` checks of a block. -/
def BlockC (f : Clif.Function) (b : Clif.Block) : Prop :=
  (∀ q ∈ b.params, q.2 ≠ .i128) ∧ ∀ s ∈ b.body, StmtC f s

/-- **`buildCtx`, functionally.** -/
theorem buildCtx_model {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) :
    ctx = { func := f, insts := (ctxModel f (maxVOf f)).2.2.1, valTy := (ctxModel f (maxVOf f)).1,
            valDef := (ctxModel f (maxVOf f)).2.1,
            valReg := (Array.range (maxVOf f)).map fun v =>
              if ((ctxModel f (maxVOf f)).1[v]?).join.isSome then some (.vreg v .int) else none,
            slotOff := (slotLayout f.slots).1 } ∧
    ranges = (ctxModel f (maxVOf f)).2.2.2 ∧
    st0 = { nextVreg := maxVOf f, classes := Array.replicate (maxVOf f) .int } ∧
    ∀ B ∈ f.blocks, BlockC f B := by
  unfold buildCtx at hb
  simp only [bind, Except.bind, pure, Except.pure] at hb
  split at hb
  · cases hb
  rename_i s1 h1
  split at hb
  · cases hb
  rename_i s2 h2
  simp only [forIn_okYield] at h1
  have e1 : s1 = maxVOf f := (Except.ok.inj h1).symm
  subst e1
  obtain ⟨hs2, hC⟩ := forIn_foldC _ (blockStepM f) (fun B _ => BlockC f B) (by
    intro b s r h
    split at h
    · cases h
    rename_i vt hvt
    obtain ⟨evt, hpar⟩ := forIn_foldC _ parStepM (fun q _ => q.2 ≠ .i128) (by
      intro q a r h
      split at h
      · split at h
        · cases h
        · rename_i hh; cases hh
      · rename_i hq
        simp only [Except.ok.injEq] at h
        exact ⟨h.symm, by simpa using hq⟩) b.params _ vt hvt
    split at h
    · cases h
    rename_i q hq
    have hres : ∀ (n : Nat) (a0 : Array (Option CTy) × Array (Option Nat)) (l : List (Nat × Clif.Ty))
        (body : Nat × Clif.Ty → Array (Option CTy) × Array (Option Nat) →
          Except String (ForInStep (Array (Option CTy) × Array (Option Nat)))) (out : _),
        (∀ p a r, body p a = .ok r → r = .yield (resStepM n a p) ∧ p.2 ≠ .i128) →
        forIn l a0 body = .ok out → out = l.foldl (resStepM n) a0 ∧ ∀ p ∈ l, p.2 ≠ .i128 := by
      intro n a0 l body out hb ho
      obtain ⟨h1, h2⟩ := forIn_foldC body (resStepM n) (fun p _ => p.2 ≠ .i128) hb l a0 out ho
      refine ⟨h1, fun p hp => ?_⟩
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem hp
      exact h2 i p (by rw [List.getElem?_eq_getElem hi, e])
    obtain ⟨eq, hst⟩ := forIn_foldC _ (stmtStepM f) (fun s _ => StmtC f s) (by
      intro st a r h
      split at h
      · cases h
      rename_i d hd
      split at h
      · rename_i tys hty
        split at h
        · split at h
          · cases h
          · rename_i hh; cases hh
        · rename_i hlen
          split at h
          · cases h
          rename_i w hw
          obtain ⟨ew, hw⟩ := hres _ _ _ _ _ (by
            intro p a r h
            split at h
            · split at h
              · cases h
              · rename_i hh; cases hh
            · rename_i hp
              simp only [Except.ok.injEq] at h
              exact ⟨by rw [← h]; rfl, by simpa using hp⟩) hw
          simp only [Except.ok.injEq] at h
          have htys : tysOf f st = tys := by simp [tysOf, hty]
          refine ⟨by rw [← h, ew]; simp [stmtStepM, infoOf, dataOf, hd, htys], ⟨d, hd⟩,
            ⟨tys, hty, by simpa using hlen⟩, ?_⟩
          rw [htys]
          intro t ht
          obtain ⟨i, hi, e⟩ := List.getElem_of_mem ht
          have hlt : i < (st.results.zip tys).length := by
            simp only [List.length_zip]; simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen; omega
          have := hw (st.results.zip tys)[i] (List.getElem_mem hlt)
          simpa [e] using this
      · split at h
        · cases h
        · rename_i hh; cases hh) b.body _ q hq
    simp only [Except.ok.injEq] at h
    refine ⟨by rw [← h, eq, evt]; rfl, fun p hp => ?_, fun st hs => ?_⟩
    · obtain ⟨i, hi, e⟩ := List.getElem_of_mem hp
      exact hpar i p (by rw [List.getElem?_eq_getElem hi, e])
    · obtain ⟨i, hi, e⟩ := List.getElem_of_mem hs
      exact hst i st (by rw [List.getElem?_eq_getElem hi, e])) f.blocks _ s2 h2
  have e2 : s2 = ctxModel f (maxVOf f) := hs2
  subst e2
  split at hb
  · cases hb
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl, rfl⟩ := hb
  refine ⟨rfl, rfl, rfl, fun B hB => ?_⟩
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hB
  exact hC i B (by rw [List.getElem?_eq_getElem hi, e])

/-! ## Writes into an array of options -/

/-- Write `some p.2` at `p.1` (`Array.set!`: nothing out of range). -/
def setW {α : Type} (a : Array (Option α)) (p : Nat × α) : Array (Option α) := a.set! p.1 (some p.2)

/-- The last value written at `x` by `W`. -/
def lastOf {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | p :: W, x => match lastOf W x with
    | some t => some t
    | none => if p.1 = x then some p.2 else none

theorem setW_size {α : Type} : ∀ (W : List (Nat × α)) (a : Array (Option α)),
    (W.foldl setW a).size = a.size
  | [], _ => rfl
  | p :: W, a => by
    rw [List.foldl_cons, setW_size W]
    simp [setW]

theorem setW_get {α : Type} : ∀ (W : List (Nat × α)) (a : Array (Option α)) (x : Nat),
    ((W.foldl setW a)[x]?).join =
      match lastOf W x with
      | some t => if x < a.size then some t else none
      | none => (a[x]?).join
  | [], a, x => rfl
  | p :: W, a, x => by
    rw [List.foldl_cons, setW_get W]
    have hs : (setW a p).size = a.size := by simp [setW]
    simp only [lastOf, hs]
    cases lastOf W x with
    | some t => rfl
    | none =>
      simp only [setW, Array.set!, Array.getElem?_setIfInBounds]
      by_cases h : p.1 = x
      · subst h
        by_cases hl : p.1 < a.size <;> simp [hl]
      · simp [h]

theorem lastOf_mem {α : Type} : ∀ {W : List (Nat × α)} {x : Nat} {t : α}, lastOf W x = some t → (x, t) ∈ W
  | [], _, _, h => by simp [lastOf] at h
  | p :: W, x, t, h => by
    simp only [lastOf] at h
    split at h
    · rename_i t' h'
      cases h; exact List.mem_cons_of_mem _ (lastOf_mem h')
    · split at h
      · rename_i hp; cases h; rw [← hp]; exact List.mem_cons_self
      · cases h

theorem lastOf_isSome {α : Type} : ∀ {W : List (Nat × α)} {x : Nat} {t : α}, (x, t) ∈ W →
    (lastOf W x).isSome
  | [], _, _, h => by simp at h
  | p :: W, x, t, h => by
    simp only [lastOf]
    split
    · rfl
    · rename_i hn
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have := lastOf_isSome (W := W) h
        rw [hn] at this; cases this

theorem lastOf_nodup {α : Type} : ∀ {W : List (Nat × α)} {x : Nat} {t : α}, (W.map Prod.fst).Nodup →
    (x, t) ∈ W → lastOf W x = some t
  | [], _, _, _, h => by simp at h
  | p :: W, x, t, hn, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    simp only [lastOf]
    rcases List.mem_cons.mp h with rfl | h
    · split
      · rename_i t' h'
        exact absurd ⟨_, lastOf_mem h', rfl⟩ hn.1
      · simp
    · rw [lastOf_nodup hn.2 h]

/-! ## The model as lists -/

/-- The type writes of a statement. -/
def tyWrites (f : Clif.Function) (s : Clif.Stmt) : List (Nat × CTy) :=
  (s.results.zip (tysOf f s)).map fun p => (p.1, CTy.ofClif p.2)

/-- The type writes of a block. -/
def blockTyW (f : Clif.Function) (B : Clif.Block) : List (Nat × CTy) :=
  B.params.map (fun q => (q.1, CTy.ofClif q.2)) ++ B.body.flatMap (tyWrites f)

/-- The definition writes of statements `ss` (the first at instruction `n`). -/
def defW (f : Clif.Function) : List Clif.Stmt → Nat → List (Nat × Nat)
  | [], _ => []
  | s :: ss, n => (s.results.zip (tysOf f s)).map (fun p => (p.1, n)) ++ defW f ss (n + 1)

/-- The definition writes of blocks `Bs` (the first instruction at `n`). -/
def defWB (f : Clif.Function) : List Clif.Block → Nat → List (Nat × Nat)
  | [], _ => []
  | B :: Bs, n => defW f B.body n ++ defWB f Bs (n + B.body.length + 1)

/-- The table entries of blocks `Bs`. -/
def instsOf (f : Clif.Function) (Bs : List Clif.Block) : List IInfo :=
  Bs.flatMap fun B => B.body.map (infoOf f) ++ [placeholder]

/-- The instruction ranges of blocks `Bs` (the first at `n`). -/
def rangesOf : List Clif.Block → Nat → List (Nat × Nat)
  | [], _ => []
  | B :: Bs, n => (n, n + B.body.length + 1) :: rangesOf Bs (n + B.body.length + 1)

theorem resFold (n : Nat) : ∀ (l : List (Nat × Clif.Ty)) (a : Array (Option CTy)) (b : Array (Option Nat)),
    l.foldl (resStepM n) (a, b) =
      ((l.map fun p => (p.1, CTy.ofClif p.2)).foldl setW a, (l.map fun p => (p.1, n)).foldl setW b)
  | [], _, _ => rfl
  | p :: l, a, b => by
    rw [List.foldl_cons]
    exact resFold n l _ _

theorem bodyFold (f : Clif.Function) : ∀ (ss : List Clif.Stmt) (vt : Array (Option CTy))
    (vd : Array (Option Nat)) (insts : Array IInfo),
    ss.foldl (stmtStepM f) (vt, vd, insts) =
      ((ss.flatMap (tyWrites f)).foldl setW vt, (defW f ss insts.size).foldl setW vd,
        insts ++ (ss.map (infoOf f)).toArray)
  | [], _, _, _ => by simp [defW]
  | s :: ss, vt, vd, insts => by
    rw [List.foldl_cons]
    simp only [stmtStepM, resFold]
    rw [bodyFold f ss]
    simp only [List.flatMap_cons, List.foldl_append, defW, Array.size_push, tyWrites, List.map_cons]
    refine Prod.ext rfl (Prod.ext rfl (Array.ext' ?_))
    simp

theorem blockFold (f : Clif.Function) : ∀ (Bs : List Clif.Block) (vt : Array (Option CTy))
    (vd : Array (Option Nat)) (insts : Array IInfo) (rg : Array (Nat × Nat)),
    Bs.foldl (blockStepM f) (vt, vd, insts, rg) =
      ((Bs.flatMap (blockTyW f)).foldl setW vt, (defWB f Bs insts.size).foldl setW vd,
        insts ++ (instsOf f Bs).toArray, rg ++ (rangesOf Bs insts.size).toArray)
  | [], _, _, _, _ => by simp [defWB, instsOf, rangesOf]
  | B :: Bs, vt, vd, insts, rg => by
    rw [List.foldl_cons]
    simp only [blockStepM, bodyFold]
    rw [blockFold f Bs]
    simp only [List.flatMap_cons, List.foldl_append, defWB, Array.size_push, Array.size_append,
      List.size_toArray, List.length_map, blockTyW, instsOf, rangesOf]
    rw [List.foldl_map]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext (Array.ext' ?_) (Array.ext' ?_))) <;> simp

/-! ## Layout -/

/-- The index of block `bi`'s first instruction in the table of blocks `Bs`. -/
def bsl (Bs : List Clif.Block) (bi : Nat) : Nat := ((Bs.take bi).map (·.body.length + 1)).sum

theorem bsl_zero (Bs : List Clif.Block) : bsl Bs 0 = 0 := by simp [bsl]

theorem bsl_cons (B : Clif.Block) (Bs : List Clif.Block) (bi : Nat) :
    bsl (B :: Bs) (bi + 1) = B.body.length + 1 + bsl Bs bi := by
  simp [bsl, List.take_succ_cons]

theorem blockStart_eq (f : Clif.Function) (bi : Nat) : blockStart f bi = bsl f.blocks bi := rfl

theorem instsOf_cons (f : Clif.Function) (B : Clif.Block) (Bs : List Clif.Block) :
    instsOf f (B :: Bs) = B.body.map (infoOf f) ++ [placeholder] ++ instsOf f Bs := by
  simp [instsOf]

theorem instsOf_len (f : Clif.Function) : ∀ Bs : List Clif.Block,
    (instsOf f Bs).length = bsl Bs Bs.length
  | [] => by simp [instsOf, bsl]
  | B :: Bs => by
    rw [instsOf_cons, List.length_cons, bsl_cons, ← instsOf_len f Bs]
    simp; omega

theorem instsOf_stmt (f : Clif.Function) : ∀ (Bs : List Clif.Block) (bi : Nat) (B : Clif.Block)
    (j : Nat) (stm : Clif.Stmt), Bs[bi]? = some B → B.body[j]? = some stm →
    (instsOf f Bs)[bsl Bs bi + j]? = some (infoOf f stm)
  | [], _, _, _, _, h, _ => by simp at h
  | B' :: Bs, 0, B, j, stm, h, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have hj : j < B'.body.length := (List.getElem?_eq_some_iff.mp hs).1
    rw [instsOf_cons, bsl_zero, Nat.zero_add, List.append_assoc,
      List.getElem?_append_left (by simpa using hj)]
    simp [hs]
  | B' :: Bs, bi + 1, B, j, stm, h, hs => by
    simp only [List.getElem?_cons_succ] at h
    rw [instsOf_cons, bsl_cons, List.getElem?_append_right (by simp; omega)]
    have := instsOf_stmt f Bs bi B j stm h hs
    rw [← this]; congr 1; simp; omega

theorem instsOf_term (f : Clif.Function) : ∀ (Bs : List Clif.Block) (bi : Nat) (B : Clif.Block),
    Bs[bi]? = some B → (instsOf f Bs)[bsl Bs bi + B.body.length]? = some placeholder
  | [], _, _, h => by simp at h
  | B' :: Bs, 0, B, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [instsOf_cons, bsl_zero, Nat.zero_add, List.getElem?_append_left (by simp)]
    simp
  | B' :: Bs, bi + 1, B, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [instsOf_cons, bsl_cons, List.getElem?_append_right (by simp; omega)]
    have := instsOf_term f Bs bi B h
    rw [← this]; congr 1; simp; omega

theorem instsOf_mem {f : Clif.Function} {Bs : List Clif.Block} {info : IInfo}
    (h : info ∈ instsOf f Bs) : info = placeholder ∨ ∃ B ∈ Bs, ∃ s ∈ B.body, info = infoOf f s := by
  simp only [instsOf, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_singleton] at h
  obtain ⟨B, hB, ⟨s, hs, rfl⟩ | rfl⟩ := h
  · exact .inr ⟨B, hB, s, hs, rfl⟩
  · exact .inl rfl

theorem rangesOf_len : ∀ (Bs : List Clif.Block) (n : Nat), (rangesOf Bs n).length = Bs.length
  | [], _ => rfl
  | B :: Bs, n => by simp [rangesOf, rangesOf_len Bs]

theorem rangesOf_get : ∀ (Bs : List Clif.Block) (n bi : Nat) (B : Clif.Block), Bs[bi]? = some B →
    (rangesOf Bs n)[bi]? = some (n + bsl Bs bi, n + bsl Bs bi + B.body.length + 1)
  | [], _, _, _, h => by simp at h
  | B' :: Bs, n, 0, B, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [rangesOf, bsl_zero]
  | B' :: Bs, n, bi + 1, B, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [rangesOf, List.getElem?_cons_succ, rangesOf_get Bs _ bi B h, bsl_cons]
    congr 2 <;> omega

theorem defW_mem {f : Clif.Function} : ∀ {ss : List Clif.Stmt} {n x d : Nat}, (x, d) ∈ defW f ss n →
    ∃ j stm, ss[j]? = some stm ∧ x ∈ stm.results ∧ d = n + j
  | [], _, _, _, h => by simp [defW] at h
  | s :: ss, n, x, d, h => by
    simp only [defW, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨⟨r, t⟩, hp, rfl, rfl⟩ | h
    · exact ⟨0, s, rfl, (List.of_mem_zip hp).1, rfl⟩
    · obtain ⟨j, stm, h1, h2, rfl⟩ := defW_mem h
      exact ⟨j + 1, stm, by simpa using h1, h2, by omega⟩

theorem defWB_mem {f : Clif.Function} : ∀ {Bs : List Clif.Block} {n x d : Nat}, (x, d) ∈ defWB f Bs n →
    ∃ bi B j stm, Bs[bi]? = some B ∧ B.body[j]? = some stm ∧ x ∈ stm.results ∧ d = n + bsl Bs bi + j
  | [], _, _, _, h => by simp [defWB] at h
  | B :: Bs, n, x, d, h => by
    simp only [defWB, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨j, stm, h1, h2, rfl⟩ := defW_mem h
      exact ⟨0, B, j, stm, rfl, h1, h2, by simp [bsl_zero]⟩
    · obtain ⟨bi, B', j, stm, h0, h1, h2, rfl⟩ := defWB_mem h
      exact ⟨bi + 1, B', j, stm, by simpa using h0, h1, h2, by rw [bsl_cons]; omega⟩

theorem zip_fst {α β : Type} {l1 : List α} {l2 : List β} (h : l2.length = l1.length) :
    (l1.zip l2).map Prod.fst = l1 := List.map_fst_zip (by omega)

theorem stmtC_len {f : Clif.Function} {s : Clif.Stmt} (h : StmtC f s) :
    (tysOf f s).length = s.results.length := by
  obtain ⟨-, ⟨tys, ht, hl⟩, -⟩ := h
  simp [tysOf, ht, hl]

theorem defW_of {f : Clif.Function} : ∀ {ss : List Clif.Stmt} {n j : Nat} {stm : Clif.Stmt} {x : Nat},
    (∀ s ∈ ss, StmtC f s) → ss[j]? = some stm → x ∈ stm.results → (x, n + j) ∈ defW f ss n
  | [], _, _, _, _, _, h, _ => by simp at h
  | s :: ss, n, 0, stm, x, hc, h, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [defW, List.mem_append, List.mem_map]
    left
    have hz : x ∈ (s.results.zip (tysOf f s)).map Prod.fst := by
      rw [zip_fst (stmtC_len (hc s List.mem_cons_self))]; exact hx
    obtain ⟨p, hp, e⟩ := List.mem_map.mp hz
    exact ⟨p, hp, by simp [e]⟩
  | s :: ss, n, j + 1, stm, x, hc, h, hx => by
    simp only [List.getElem?_cons_succ] at h
    simp only [defW, List.mem_append]
    right
    have := defW_of (n := n + 1) (fun s hs => hc s (List.mem_cons_of_mem _ hs)) h hx
    rwa [show n + 1 + j = n + (j + 1) by omega] at this

theorem defWB_of {f : Clif.Function} : ∀ {Bs : List Clif.Block} {n bi : Nat} {B : Clif.Block} {j : Nat}
    {stm : Clif.Stmt} {x : Nat}, (∀ B ∈ Bs, BlockC f B) → Bs[bi]? = some B → B.body[j]? = some stm →
    x ∈ stm.results → (x, n + bsl Bs bi + j) ∈ defWB f Bs n
  | [], _, _, _, _, _, _, _, h, _, _ => by simp at h
  | B' :: Bs, n, 0, B, j, stm, x, hc, h, hs, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [defWB, List.mem_append, bsl_zero, Nat.add_zero]
    exact .inl (defW_of (hc B' List.mem_cons_self).2 hs hx)
  | B' :: Bs, n, bi + 1, B, j, stm, x, hc, h, hs, hx => by
    simp only [List.getElem?_cons_succ] at h
    simp only [defWB, List.mem_append]
    right
    have := defWB_of (n := n + B'.body.length + 1) (fun B hB => hc B (List.mem_cons_of_mem _ hB)) h hs hx
    rw [bsl_cons]
    rwa [show n + B'.body.length + 1 + bsl Bs bi + j = n + (B'.body.length + 1 + bsl Bs bi) + j by omega] at this

theorem defW_fst {f : Clif.Function} : ∀ {ss : List Clif.Stmt} {n : Nat}, (∀ s ∈ ss, StmtC f s) →
    (defW f ss n).map Prod.fst = ss.flatMap (·.results)
  | [], _, _ => rfl
  | s :: ss, n, hc => by
    simp only [defW, List.map_append, List.map_map, List.flatMap_cons]
    rw [defW_fst (fun s hs => hc s (List.mem_cons_of_mem _ hs))]
    congr 1
    rw [show (Prod.fst ∘ fun p : Nat × Clif.Ty => (p.1, n)) = Prod.fst from rfl]
    exact zip_fst (stmtC_len (hc s List.mem_cons_self))

theorem defWB_fst {f : Clif.Function} : ∀ {Bs : List Clif.Block} {n : Nat}, (∀ B ∈ Bs, BlockC f B) →
    (defWB f Bs n).map Prod.fst = Bs.flatMap fun B => B.body.flatMap (·.results)
  | [], _, _ => rfl
  | B :: Bs, n, hc => by
    simp only [defWB, List.map_append, List.flatMap_cons]
    rw [defW_fst (hc B List.mem_cons_self).2, defWB_fst (fun B hB => hc B (List.mem_cons_of_mem _ hB))]

theorem flatMap_congr' {α β : Type} {g h : α → List β} : ∀ {l : List α}, (∀ a ∈ l, g a = h a) →
    l.flatMap g = l.flatMap h
  | [], _ => rfl
  | a :: l, e => by
    simp only [List.flatMap_cons]
    rw [e a List.mem_cons_self, flatMap_congr' fun b hb => e b (List.mem_cons_of_mem _ hb)]

theorem tyW_fst {f : Clif.Function} {Bs : List Clif.Block} (hc : ∀ B ∈ Bs, BlockC f B) :
    (Bs.flatMap (blockTyW f)).map Prod.fst =
      Bs.flatMap fun B => B.params.map (·.1) ++ B.body.flatMap (·.results) := by
  simp only [List.map_flatMap]
  refine flatMap_congr' fun B hB => ?_
  simp only [blockTyW, List.map_append, List.map_map, List.map_flatMap]
  congr 1
  refine flatMap_congr' fun s hs => ?_
  simp only [tyWrites, List.map_map]
  rw [show (Prod.fst ∘ fun p : Nat × Clif.Ty => (p.1, CTy.ofClif p.2)) = Prod.fst from rfl]
  exact zip_fst (stmtC_len ((hc B hB).2 s hs))

theorem tyW_mem {f : Clif.Function} {Bs : List Clif.Block} {x : Nat} {t : CTy}
    (h : (x, t) ∈ Bs.flatMap (blockTyW f)) :
    (∃ B ∈ Bs, ∃ q ∈ B.params, x = q.1 ∧ t = CTy.ofClif q.2) ∨
      ∃ B ∈ Bs, ∃ s ∈ B.body, ∃ (m : Nat) (ty : Clif.Ty), s.results[m]? = some x ∧ (tysOf f s)[m]? = some ty ∧
        t = CTy.ofClif ty := by
  simp only [List.mem_flatMap, blockTyW, List.mem_append, List.mem_map, tyWrites, Prod.mk.injEq] at h
  obtain ⟨B, hB, ⟨q, hq, rfl, rfl⟩ | ⟨s, hs, ⟨r, ty⟩, hp, rfl, rfl⟩⟩ := h
  · exact .inl ⟨B, hB, q, hq, rfl, rfl⟩
  · obtain ⟨m, hm, e⟩ := List.getElem_of_mem hp
    rw [List.getElem_zip] at e
    simp only [Prod.mk.injEq] at e
    simp only [List.length_zip] at hm
    exact .inr ⟨B, hB, s, hs, m, ty, by rw [List.getElem?_eq_getElem (by omega), e.1],
      by rw [List.getElem?_eq_getElem (by omega), e.2], rfl⟩

/-! ## The number of values -/

theorem foldl_infl {α : Type} (g : Nat → α → Nat) (hg : ∀ m a, m ≤ g m a) :
    ∀ (l : List α) (m : Nat), m ≤ l.foldl g m
  | [], _ => Nat.le_refl _
  | a :: l, m => Nat.le_trans (hg m a) (foldl_infl g hg l (g m a))

theorem foldl_infl_mem {α : Type} (g : Nat → α → Nat) (hg : ∀ m a, m ≤ g m a) (P : α → Nat → Prop)
    (hP : ∀ a m, P a (g m a)) (hmono : ∀ a m m', m ≤ m' → P a m → P a m') :
    ∀ (l : List α) (m : Nat), ∀ a ∈ l, P a (l.foldl g m)
  | [], _, _, h => by simp at h
  | b :: l, m, a, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact hmono _ _ _ (foldl_infl g hg l _) (hP a m)
    · exact foldl_infl_mem g hg P hP hmono l _ a h

theorem maxV_bound (f : Clif.Function) : ∀ x ∈ valueDefs f, x < maxVOf f := by
  have hr : ∀ (l : List Nat) (m : Nat), m ≤ l.foldl (fun m r => max m (r + 1)) m :=
    foldl_infl _ fun m r => Nat.le_max_left _ _
  have hs : ∀ (l : List Clif.Stmt) (m : Nat),
      m ≤ l.foldl (fun m s => s.results.foldl (fun m r => max m (r + 1)) m) m :=
    foldl_infl _ fun m s => hr _ _
  have hp : ∀ (l : List (Clif.ValueId × Clif.Ty)) (m : Nat),
      m ≤ l.foldl (fun m p => max m (p.1 + 1)) m := foldl_infl _ fun m p => Nat.le_max_left _ _
  have hrm : ∀ (l : List Nat) (m : Nat), ∀ r ∈ l, r < l.foldl (fun m r => max m (r + 1)) m :=
    foldl_infl_mem _ (fun m r => Nat.le_max_left _ _) (fun r m => r < m)
      (fun r m => by omega) (fun _ _ _ h1 h2 => by omega)
  have hsm : ∀ (l : List Clif.Stmt) (m : Nat), ∀ s ∈ l, ∀ r ∈ s.results,
      r < l.foldl (fun m s => s.results.foldl (fun m r => max m (r + 1)) m) m :=
    foldl_infl_mem (fun m (s : Clif.Stmt) => s.results.foldl (fun m r => max m (r + 1)) m)
      (fun m s => hr _ _) (fun (s : Clif.Stmt) m => ∀ r ∈ s.results, r < m)
      (fun s m r h => hrm _ _ r h) (fun _ _ _ h1 h2 r hr => Nat.lt_of_lt_of_le (h2 r hr) h1)
  have hpm : ∀ (l : List (Clif.ValueId × Clif.Ty)) (m : Nat), ∀ q ∈ l,
      q.1 < l.foldl (fun m p => max m (p.1 + 1)) m :=
    foldl_infl_mem (fun m (p : Clif.ValueId × Clif.Ty) => max m (p.1 + 1))
      (fun m p => Nat.le_max_left _ _) (fun (q : Clif.ValueId × Clif.Ty) m => q.1 < m)
      (fun q m => Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
      (fun _ m m' h1 h2 => Nat.lt_of_lt_of_le h2 h1)
  intro x hx
  simp only [valueDefs, List.mem_flatMap, List.mem_append, List.mem_map] at hx
  obtain ⟨B, hB, hx⟩ := hx
  unfold maxVOf
  refine foldl_infl_mem (fun m (B : Clif.Block) => B.body.foldl
      (fun m s => s.results.foldl (fun m r => max m (r + 1)) m) (B.params.foldl (fun m p => max m (p.1 + 1)) m))
    (fun m B => Nat.le_trans (hp B.params m) (hs B.body _))
    (fun (B : Clif.Block) m => ∀ x, (∃ q ∈ B.params, q.1 = x) ∨ (∃ s ∈ B.body, x ∈ s.results) → x < m)
    (fun B m x hx => ?_) (fun _ _ _ h1 h2 x hx => Nat.lt_of_lt_of_le (h2 x hx) h1) f.blocks 0 B hB x ?_
  · rcases hx with ⟨q, hq, rfl⟩ | ⟨s, hs', hx⟩
    · exact Nat.lt_of_lt_of_le (hpm _ _ q hq) (hs _ _)
    · exact hsm _ _ s hs' x hx
  · rcases hx with ⟨q, hq, rfl⟩ | hx
    · exact .inl ⟨q, hq, rfl⟩
    · exact .inr hx

/-! ## The facts -/

theorem flatMap_sub {α β : Type} (P R : α → List β) :
    ∀ l : List α, (l.flatMap R).Sublist (l.flatMap fun a => P a ++ R a)
  | [] => List.Sublist.slnil
  | a :: l => by
    simp only [List.flatMap_cons]
    exact List.Sublist.append (List.sublist_append_right _ _) (flatMap_sub P R l)

/-- Everything about `buildCtx f = .ok (ctx, ranges, st0)` the proof uses. -/
structure CtxSpec (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState) :
    Prop where
  blockC : ∀ B ∈ f.blocks, BlockC f B
  facts : CtxFacts f ctx st0
  func : ctx.func = f
  slotOff : ctx.slotOff = (slotLayout f.slots).1
  st0 : st0 = { nextVreg := ctx.valDef.size, classes := Array.replicate ctx.valDef.size .int }
  rsize : ranges.size = f.blocks.length
  ranges : ∀ bi B, f.blocks[bi]? = some B →
    ranges[bi]? = some (blockStart f bi, blockStart f bi + B.body.length + 1)
  insts : ∀ info ∈ ctx.insts.toList, info = placeholder ∨ ∃ B ∈ f.blocks, ∃ s ∈ B.body, info = infoOf f s
  regEq : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int
  regTy : ∀ x, (ctx.valueReg? x).isSome = (ctx.valueType? x).isSome
  tyOf : ∀ x t, ctx.valueType? x = some t →
    (∃ B ∈ f.blocks, ∃ q ∈ B.params, x = q.1 ∧ t = CTy.ofClif q.2) ∨
      ∃ B ∈ f.blocks, ∃ s ∈ B.body, ∃ (m : Nat) (ty : Clif.Ty), s.results[m]? = some x ∧
        (tysOf f s)[m]? = some ty ∧ t = CTy.ofClif ty
  defOf : ∀ x d, ctx.defInst? x = some d → ∃ bi B j stm, f.blocks[bi]? = some B ∧
    B.body[j]? = some stm ∧ x ∈ stm.results ∧ d = blockStart f bi + j

theorem getD_replicate_join {α : Type} (M x : Nat) :
    ((Array.replicate M (none : Option α))[x]?).join = none := by
  simp only [Array.getElem?_replicate]; split <;> rfl

theorem ctxSpec_of {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hb : buildCtx f = .ok (ctx, ranges, st0)) : CtxSpec f ctx ranges st0 := by
  obtain ⟨hctx, hrg, hst, hC⟩ := buildCtx_model hb
  have hm := blockFold f f.blocks (Array.replicate (maxVOf f) none) (Array.replicate (maxVOf f) none)
    #[] #[]
  simp only [List.size_toArray, List.length_nil, Array.empty_append] at hm
  unfold ctxModel at hctx hrg
  rw [hm] at hctx hrg
  simp only at hctx hrg
  subst hctx hrg hst
  clear hm hb
  have hWf : (f.blocks.flatMap (blockTyW f)).map Prod.fst = valueDefs f := tyW_fst hC
  have hDf : (defWB f f.blocks 0).map Prod.fst = f.blocks.flatMap fun B => B.body.flatMap (·.results) :=
    defWB_fst hC
  have hMb := maxV_bound f
  have hDm : ∀ {x d}, (x, d) ∈ defWB f f.blocks 0 → ∃ bi B j stm, f.blocks[bi]? = some B ∧
      B.body[j]? = some stm ∧ x ∈ stm.results ∧ d = 0 + bsl f.blocks bi + j := defWB_mem
  have hDo : ∀ {bi B j stm x}, f.blocks[bi]? = some B → B.body[j]? = some stm → x ∈ stm.results →
      (x, 0 + bsl f.blocks bi + j) ∈ defWB f f.blocks 0 := defWB_of hC
  have hWm : ∀ {x t}, (x, t) ∈ f.blocks.flatMap (blockTyW f) → _ := tyW_mem
  have hWp : ∀ B ∈ f.blocks, ∀ q ∈ B.params, (q.1, CTy.ofClif q.2) ∈ f.blocks.flatMap (blockTyW f) := by
    intro B hB q hq
    simp only [List.mem_flatMap, blockTyW, List.mem_append, List.mem_map]
    exact ⟨B, hB, .inl ⟨q, hq, rfl⟩⟩
  have hWs : ∀ B ∈ f.blocks, ∀ s ∈ B.body, ∀ r ty, (r, ty) ∈ s.results.zip (tysOf f s) →
      (r, CTy.ofClif ty) ∈ f.blocks.flatMap (blockTyW f) := by
    intro B hB s hs r ty hz
    simp only [List.mem_flatMap, blockTyW, List.mem_append, tyWrites, List.mem_map]
    exact ⟨B, hB, .inr ⟨s, hs, _, hz, rfl⟩⟩
  generalize maxVOf f = M at *
  generalize f.blocks.flatMap (blockTyW f) = W at *
  generalize defWB f f.blocks 0 = D at *
  have hvt : ∀ x, ((W.foldl setW (Array.replicate M none))[x]?).join =
      match lastOf W x with
      | some t => if x < M then some t else none
      | none => none := by
    intro x; rw [setW_get]; simp only [Array.size_replicate]
    cases lastOf W x <;> simp [getD_replicate_join]
  have hvd : ∀ x, ((D.foldl setW (Array.replicate M none))[x]?).join =
      match lastOf D x with
      | some t => if x < M then some t else none
      | none => none := by
    intro x; rw [setW_get]; simp only [Array.size_replicate]
    cases lastOf D x <;> simp [getD_replicate_join]
  have hreg : ∀ x, ((((Array.range M).map fun v =>
      if ((W.foldl setW (Array.replicate M none))[v]?).join.isSome then some (Reg.vreg v .int)
      else none)[x]?).join) =
      if x < M ∧ (lastOf W x).isSome then some (.vreg x .int) else none := by
    intro x
    rw [Array.getElem?_map, Array.getElem?_range]
    by_cases hx : x < M
    · simp only [hx, ite_true, Option.map_some, Option.join_some, hvt]
      cases lastOf W x <;> simp [hx]
    · simp [hx]
  have hsW : (W.foldl setW (Array.replicate M none)).size = M := by
    rw [setW_size]; simp
  have hsD : (D.foldl setW (Array.replicate M none)).size = M := by
    rw [setW_size]; simp
  have hval : ∀ x ∈ valueDefs f, x < M ∧ (lastOf W x).isSome := by
    intro x hx
    refine ⟨hMb x hx, ?_⟩
    rw [← hWf] at hx
    obtain ⟨⟨x', t⟩, hp, rfl⟩ := List.mem_map.mp hx
    exact lastOf_isSome hp
  refine ⟨hC, ⟨⟨by simp [hsD], by simp [hsD], by simp [hsW, hsD]⟩, fun x hx => ⟨by
      simpa using (hval x hx).1, by
      simp only [Ctx.valueReg?]; rw [hreg]; simp [hval x hx]⟩, rfl, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, rfl, by simp [hsD], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [instsOf_len, blockStart_eq]
  · intro bi B j stm hB hs
    refine ⟨infoOf f stm, ?_, rfl, rfl⟩
    simp only [List.getElem?_toArray]
    exact instsOf_stmt f f.blocks bi B j stm hB hs
  · intro bi B hB
    rw [← Array.getElem?_toList]; simp only [List.toList_toArray]
    exact instsOf_term f f.blocks bi B hB
  · intro hnd x d
    have hDn : (D.map Prod.fst).Nodup := by
      rw [hDf]; rw [valueDefs] at hnd; exact hnd.sublist (flatMap_sub _ _ _)
    simp only [Ctx.defInst?]
    rw [hvd]
    constructor
    · intro h
      split at h
      · rename_i t ht
        split at h
        · cases h
          obtain ⟨bi, B, j, stm, h1, h2, h3, h4⟩ := hDm (lastOf_mem ht)
          exact ⟨bi, B, j, stm, h1, h2, h3, by rw [h4, blockStart_eq]; omega⟩
        · cases h
      · cases h
    · rintro ⟨bi, B, j, stm, h1, h2, h3, rfl⟩
      have hm : (x, 0 + bsl f.blocks bi + j) ∈ D := hDo h1 h2 h3
      rw [lastOf_nodup hDn hm]
      have hx : x ∈ valueDefs f := by
        simp only [valueDefs, List.mem_flatMap, List.mem_append]
        exact ⟨B, List.mem_of_getElem? h1, .inr ⟨stm, List.mem_of_getElem? h2, h3⟩⟩
      simp [(hval x hx).1, blockStart_eq]
  · intro hnd
    have hWn : (W.map Prod.fst).Nodup := by rw [hWf]; exact hnd
    have key : ∀ x t, (x, t) ∈ W → x ∈ valueDefs f → ((W.foldl setW (Array.replicate M none))[x]?).join = some t := by
      intro x t hm hx
      rw [hvt, lastOf_nodup hWn hm]; simp [(hval x hx).1]
    refine ⟨fun ii info hi m r t hr ht => ?_, fun B hB q hq => ?_⟩
    · have hmem : info ∈ (instsOf f f.blocks) := by
        have := Array.mem_of_getElem? hi
        simpa using this
      rcases instsOf_mem hmem with rfl | ⟨B, hB, s, hs, rfl⟩
      · simp [placeholder] at hr
      · simp only [infoOf, List.getElem?_map] at hr ht
        cases hty : (tysOf f s)[m]? with
        | none => rw [hty] at ht; cases ht
        | some ty =>
          rw [hty] at ht
          simp only [Option.map_some, Option.some.injEq] at ht
          subst ht
          have hmz : (r, ty) ∈ s.results.zip (tysOf f s) := by
            have hl1 := (List.getElem?_eq_some_iff.mp hr).1
            have hl2 := (List.getElem?_eq_some_iff.mp hty).1
            have : (s.results.zip (tysOf f s))[m]? = some (r, ty) := by
              rw [List.getElem?_zip_eq_some]; exact ⟨hr, hty⟩
            exact List.mem_of_getElem? this
          have hmW : (r, CTy.ofClif ty) ∈ W := hWs B hB s hs r ty hmz
          have hx : r ∈ valueDefs f := by
            rw [← hWf]; exact List.mem_map.mpr ⟨_, hmW, rfl⟩
          exact key _ _ hmW hx
    · have hmW : (q.1, CTy.ofClif q.2) ∈ W := hWp B hB q hq
      have hx : q.1 ∈ valueDefs f := by
        rw [← hWf]; exact List.mem_map.mpr ⟨_, hmW, rfl⟩
      exact key _ _ hmW hx
  · simp [rangesOf_len]
  · intro bi B hB
    rw [← Array.getElem?_toList]; simp only [List.toList_toArray]
    rw [rangesOf_get f.blocks 0 bi B hB]; simp [blockStart_eq]
  · intro info hi
    exact instsOf_mem (by simpa using hi)
  · intro x r h
    simp only [Ctx.valueReg?] at h; rw [hreg] at h
    split at h
    · cases h; rfl
    · cases h
  · intro x
    simp only [Ctx.valueReg?, Ctx.valueType?]; rw [hreg, hvt]
    by_cases hx : x < M
    · cases lastOf W x <;> simp [hx]
    · cases lastOf W x <;> simp [hx]
  · intro x t h
    simp only [Ctx.valueType?] at h; rw [hvt] at h
    split at h
    · rename_i t' ht
      split at h
      · cases h; exact hWm (lastOf_mem ht)
      · cases h
    · cases h
  · intro x d h
    simp only [Ctx.defInst?] at h; rw [hvd] at h
    split at h
    · rename_i t ht
      split at h
      · cases h
        obtain ⟨bi, B, j, stm, h1, h2, h3, h4⟩ := hDm (lastOf_mem ht)
        exact ⟨bi, B, j, stm, h1, h2, h3, by rw [h4, blockStart_eq]; omega⟩
      · cases h
    · cases h

theorem ofClif_e {ty : Clif.Ty} (h : ty ≠ .i128) :
    [CTy.int 8, .int 16, .int 32, .int 64].any (fun u => decide (CTy.ofClif ty = u)) = true := by
  cases ty <;> simp_all [CTy.ofClif]

/-- `buildCtx`'s context passes `ctxOk` on in-scope input. -/
theorem ctxOk_of {f : Clif.Function} (hs : LowerScope f) {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) : ctxOk f ctx = true := by
  have sp := ctxSpec_of hb
  have haddr := (hs.ctxFacts ctx ranges st0 hb).2
  simp only [ctxOk, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨sp.func, ?_⟩, ?_⟩, ?_⟩, ?_⟩, sp.slotOff⟩, ?_⟩, ?_⟩, ?_⟩
  · refine List.all_eq_true.mpr fun info hi => ?_
    rcases sp.insts info hi with rfl | ⟨B, hB, st, hst, rfl⟩
    · rfl
    · obtain ⟨⟨d, hd⟩, ⟨tys, hty, hlen⟩, -⟩ := (sp.blockC B hB).2 st hst
      have htys : tysOf f st = tys := by simp [tysOf, hty]
      simp only [infoOf, dataOf, hd, Compile.instE_of_functionE hs.subsetE hB hst, Bool.true_and,
        beq_self_eq_true, ctxResTysOk, hty, htys, decide_true, hlen]
  · refine List.all_eq_true.mpr fun x _ => ?_
    split
    · rename_i r hr; simp [sp.regEq x r hr]
    · rfl
  · refine List.all_eq_true.mpr fun x _ => ?_
    split
    · rename_i t ht
      have h1 := sp.regTy x
      rw [ht] at h1
      cases hr : ctx.valueReg? x with
      | none => rw [hr] at h1; cases h1
      | some r => simp [sp.regEq x r hr]
    · rfl
  · refine List.all_eq_true.mpr fun x _ => ?_
    split
    · rename_i d hd
      obtain ⟨bi, B, j, stm, h1, h2, h3, rfl⟩ := sp.defOf x d hd
      obtain ⟨info, hi, hc, hr⟩ := sp.facts.stmt bi B j stm h1 h2
      simp [hi, hc, hr, h3]
    · rfl
  · refine List.all_eq_true.mpr fun info hi => List.all_eq_true.mpr fun t ht => ?_
    rcases sp.insts info hi with rfl | ⟨B, hB, st, hst, rfl⟩
    · simp [placeholder] at ht
    · simp only [infoOf, List.mem_map] at ht
      obtain ⟨ty, hty, rfl⟩ := ht
      exact ofClif_e (((sp.blockC B hB).2 st hst).2.2 ty hty)
  · refine List.all_eq_true.mpr fun x _ => ?_
    split
    · rename_i t ht
      rcases sp.tyOf x t ht with ⟨B, hB, q, hq, -, rfl⟩ | ⟨B, hB, st, hst, m, ty, -, hty, rfl⟩
      · exact ofClif_e ((sp.blockC B hB).1 q hq)
      · exact ofClif_e (((sp.blockC B hB).2 st hst).2.2 ty (List.mem_of_getElem? hty))
    · rfl
  · refine List.all_eq_true.mpr fun info hi => ?_
    obtain ⟨ii, hii, e⟩ := List.getElem_of_mem hi
    have hget : ctx.insts[ii]? = some info := by
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hii, e]
    split <;> (try rfl) <;> (rename_i h; exact decide_eq_true (haddr ii info _ _ hget h rfl))

end Backend.Proof.Driver
