module

public import FV.Backend.Proof.LowerLoopRun
public import FV.Backend.Proof.DriverCheckTy

@[expose] public section

/-!
# `lowerFunction`'s statement and terminator loops, typed (S11e5 Stage C, slice 3)

`LowerLoopRun.lean` with the value registers of a float-capable context: `lowerFunction` gives
value `x` the register `ctx.valueReg? x`, which `buildCtx` makes `vregOf ctx x = .vreg x
(valClassOf ctx x)` (`CtxSpec.regEqT`, on every input, not only on integer contexts). The typed
models (`segOfT`, `brEdgesT`, `ArgsOkT`, `tryEdgeArgT`, `TryDestOkT`, `paramsOfT`, `jumpArgsOfT`,
`edgeBlocksT`, `TermOutT`) are the integer ones with `vregOf ctx` in place of `.vreg · .int`; the
loop lemmas (`stmtLoopT`, `destLoopT`, `tryLoopT`, `termPart_okT`) need no integer premise.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Prep

/-- `buildCtx`'s value registers are `vregOf ctx` (the class of the value's type). -/
theorem CtxSpec.regEqT {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x := by
  intro x r h
  obtain ⟨t, ht, rfl⟩ := sp.regEq x r h
  simp [vregOf, valClassOf, ht]

/-! ## The result loop -/

theorem resLoopT {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x) :
    ∀ (rs : List Nat) (rss : List (List Reg)) (d : DState) (ex : Array MInst) (d' : DState)
      (ex' : Array MInst), forIn (rs.zip rss) (d, ex) (resBody ctx) = .ok (d', ex') →
      d' = { d with alias := (stmtAl rs rss).foldl aliasStep d.alias } ∧
      ex'.toList = ex.toList ++ extraOfT ctx rs rss ∧ ∀ p ∈ rs.zip rss, ∃ x, p.2 = [x]
  | [], rss, d, ex, d', ex', h => by
    simp only [List.zip_nil_left, List.forIn_nil, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [stmtAl, extraOfT]
  | r :: rs, [], d, ex, d', ex', h => by
    simp only [List.zip_nil_right, List.forIn_nil, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [stmtAl, extraOfT]
  | r :: rs, o :: rss, d, ex, d', ex', h => by
    rw [List.zip_cons_cons, List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i st hst
    unfold resBody at hst
    simp only at hst
    split at hst
    · rename_i vr hvr
      have evr := hreg r vr hvr
      subst evr
      simp only [vregOf] at hst
      split at hst
      · rename_i o' c
        try simp only at hst
        simp only [pure, Except.pure, Except.ok.injEq] at hst
        subst hst
        obtain ⟨h1, h2, h3⟩ := resLoopT hreg rs rss _ _ d' ex' h
        refine ⟨by rw [h1]; simp [stmtAl, List.zip_cons_cons, aliasStep], by
          rw [h2]; simp [extraOfT, List.zip_cons_cons], fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨_, rfl⟩
        · exact h3 p hp
      · rename_i out hne
        simp only [pure, Except.pure, Except.ok.injEq] at hst
        subst hst
        obtain ⟨h1, h2, h3⟩ := resLoopT hreg rs rss _ _ d' ex' h
        refine ⟨by rw [h1]; simp [stmtAl, List.zip_cons_cons, List.filterMap_cons]; split <;> simp_all, by
          rw [h2]; simp [extraOfT, vregOf, List.zip_cons_cons], fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨_, rfl⟩
        · exact h3 p hp
      · cases hst
    · cases hst

/-! ## The statement loop -/

/-- A statement's segment before renaming (typed result copies). -/
def segOfT (ctx : Ctx) (q : Clif.Stmt × SLow) : List MInst :=
  q.2.st'.emitted.toList ++ extraOfT ctx q.1.results q.2.rss

/-- The invariant of the statement loop after `j` statements (typed). -/
def SInvT (ctx : Ctx) (start : Nat) (ss : List Clif.Stmt) (d : DState) (code : Array MInst) (j : Nat)
    (s : DState × Array MInst) : Prop :=
  ∃ sls, lowStmts (stmtCall ctx) start (ss.take j) d.st = some (sls, s.1.st) ∧
    s.1.blocks = d.blocks ∧ s.1.edges = d.edges ∧ s.1.nextLabel = d.nextLabel ∧
    s.1.alias = (((ss.take j).zip sls).flatMap fun q => stmtAl q.1.results q.2.rss).foldl aliasStep d.alias ∧
    s.2.toList = code.toList ++ ((ss.take j).zip sls).flatMap (segOfT ctx) ∧
    s.1.st.emitted = #[] ∧ ResOk (ss.take j) sls

theorem stmtLoopT {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {k : Nat} {B : Clif.Block} (hB : f.blocks[k]? = some B)
    {d : DState} {code : Array MInst} (he : d.st.emitted = #[]) {r : DState × Array MInst}
    (h : forIn (List.range' (blockStart f k) B.body.length) (d, code) (stmtBody ctx) = .ok r) :
    SInvT ctx (blockStart f k) B.body d code B.body.length r := by
  have := forIn_inv (stmtBody ctx) (List.range' (blockStart f k) B.body.length)
    (SInvT ctx (blockStart f k) B.body d code) ?_ ?_ (d, code) r ?_ h
  · simpa using this
  · intro j i s s' hj hP hs
    have hjl : j < B.body.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1; simpa using this
    rw [List.getElem?_range' hjl] at hj
    · simp only [Nat.one_mul, Option.some.injEq] at hj
      subst hj
      obtain ⟨stm, hstm⟩ : ∃ stm, B.body[j]? = some stm :=
        ⟨_, List.getElem?_eq_getElem hjl⟩
      obtain ⟨sls, hl, hbl, hed, hnl, hal, hcode, hem, hres⟩ := hP
      have htake : B.body.take (j + 1) = B.body.take j ++ [stm] := by
        rw [List.take_add_one, hstm]; rfl
      have hlen : (B.body.take j).length = j := by simp; omega
      have hsls : sls.length = j := by rw [lowStmts_len hl, hlen]
      obtain ⟨info, hinfo, hic, hir⟩ := sp.facts.stmt k B j stm hB hstm
      unfold stmtBody at hs
      simp only [bind, Except.bind] at hs
      split at hs
      · cases hs
      rename_i res hrun
      obtain ⟨out, st, n⟩ := res
      simp only [getElem!_of hinfo] at hs
      split at hs
      · rename_i rss
        split at hs
        · cases hs
        rename_i hcnt
        split at hs
        · cases hs
        rename_i q hq
        simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hs
        subst hs
        obtain ⟨q1, q2⟩ := q
        obtain ⟨e1, e2, e3⟩ := resLoopT sp.regEqT _ _ _ _ _ _ hq
        subst e1
        have hs0 : { s.1.st with emitted := #[] } = s.1.st := by
          rcases hst : s.1.st; simp only [hst] at hem; simp [hem]
        rw [hs0] at hrun
        have hl1 : lowStmts (stmtCall ctx) (blockStart f k + j) [stm] s.1.st =
            some ([⟨s.1.st, rss, st⟩], { st with emitted := #[] }) := by
          simp only [lowStmts, stmtCall]
          rw [hs0, hrun]; rfl
        refine ⟨sls ++ [⟨s.1.st, rss, st⟩], ?_, hbl, hed, hnl, ?_, ?_, rfl, ?_⟩
        · rw [htake, lowStmts_append, hl, Option.bind_some, hlen, hl1]; rfl
        · simp only
          rw [hal, htake, List.zip_append (by rw [hlen, hsls]), List.flatMap_append, List.foldl_append,
            hir]
          simp
        · simp only
          rw [htake, List.zip_append (by rw [hlen, hsls]), List.flatMap_append]
          simp [segOfT, hcode, hir, e2]
        · intro j' stm' sl hj' hsl
          rw [htake] at hj'
          by_cases hlt : j' < j
          · rw [List.getElem?_append_left (by omega)] at hj'
            rw [List.getElem?_append_left (by omega)] at hsl
            exact hres j' stm' sl hj' hsl
          · rw [List.getElem?_append_right (by omega), hlen] at hj'
            rw [List.getElem?_append_right (by omega), hsls] at hsl
            have hj0 : j' - j = 0 := by
              have := (List.getElem?_eq_some_iff.mp hj').1
              simp only [List.length_singleton] at this; omega
            rw [hj0] at hj' hsl
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hj' hsl
            subst hj' hsl
            refine ⟨?_, fun r rs hm => ?_⟩
            · simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, Bool.not_eq_true',
                List.isEmpty_eq_false_iff, not_and, Decidable.not_not] at hcnt
              rw [← hir]
              by_cases he : info.results = []
              · exact .inr he
              · exact .inl (by
                  have := hcnt
                  simp_all)
            · obtain ⟨x, hx⟩ := e3 (r, rs) (by rw [hir]; exact hm)
              exact ⟨x, hx⟩
      · cases hs
  · intro x b b' hb
    unfold stmtBody at hb
    simp only [bind, Except.bind] at hb
    split at hb
    · cases hb
    split at hb
    · split at hb
      · cases hb
      split at hb
      · cases hb
      · simp [pure, Except.pure] at hb
    · cases hb
  · exact ⟨[], by simp [lowStmts], rfl, rfl, rfl, by simp, by simp, he,
      fun j stm sl h1 h2 => by simp at h2⟩

/-! ## Successors -/

theorem blockArgRegs_okT {f : Clif.Function} {ctx : Ctx}
    (hreg : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x) {bc : Clif.BlockCall}
    {args : Array Reg} (h : blockArgRegs ctx f bc = .ok args) :
    ∃ tb, f.block? bc.block = some tb ∧ tb.params.length = bc.args.length ∧
      (∀ a ∈ bc.args, ctx.valueReg? a = some (vregOf ctx a)) ∧
      args = (bc.args.map fun a => vregOf ctx a).toArray := by
  unfold blockArgRegs at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i tb htb
    split at h
    · cases h
    rename_i hc
    obtain ⟨hsz, hel⟩ := amapM_ok h
    have hrg : ∀ a ∈ bc.args, ctx.valueReg? a = some (vregOf ctx a) := by
      intro a ha
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem ha
      obtain ⟨y, hy, -⟩ := hel i a (by simp [List.getElem?_eq_getElem hi, e])
      cases hv : ctx.valueReg? a with
      | none => simp only [hv] at hy; cases hy
      | some r => rw [hreg a r hv]
    refine ⟨tb, htb, by simpa using hc, hrg, ?_⟩
    apply Array.ext
    · simp [hsz]
    · intro i h1 h2
      have hi : i < bc.args.length := by simpa using h2
      obtain ⟨y, hy, hy'⟩ := hel i bc.args[i] (by simp [List.getElem?_eq_getElem hi])
      rw [hrg _ (List.getElem_mem hi)] at hy
      simp only [pure, Except.pure, Except.ok.injEq] at hy
      rw [Array.getElem?_eq_getElem h1] at hy'
      simp only [Option.some.injEq] at hy'
      rw [hy', ← hy]; simp
  · cases h

/-- The edge blocks of a `brif`/`br_table`'s successors `bcs` with labels `ls` (typed). -/
def brEdgesT (f : Clif.Function) (ctx : Ctx) (bcs : List Clif.BlockCall) (ls : List Label) :
    List VBlock :=
  (bcs.zip ls).filterMap fun (bc, l) =>
    if bc.args.isEmpty then none else (blockIdx? f bc.block).map fun tl =>
      { label := l, insts := #[.jump tl], branchArgs := (bc.args.map fun a => vregOf ctx a).toArray }

/-- The facts `LoopFactsT.args` records of successors `bcs`. -/
def ArgsOkT (f : Clif.Function) (ctx : Ctx) (bcs : List Clif.BlockCall) : Prop :=
  ∀ bc ∈ bcs, ∃ tb, f.block? bc.block = some tb ∧ (bc.args ≠ [] → tb.params.length = bc.args.length) ∧
    ∀ a ∈ bc.args, ctx.valueReg? a = some (vregOf ctx a)

theorem destLoopT {f : Clif.Function} {ctx : Ctx}
    (hreg : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x) :
    ∀ (bcs : List Clif.BlockCall) (d : DState) (tg : Array Label) (d' : DState) (tg' : Array Label),
      forIn bcs (d, tg) (destBody f ctx) = .ok (d', tg') →
      ∃ ts, edgeTargets f bcs d.nextLabel = some (ts, d'.nextLabel) ∧ tg'.toList = tg.toList ++ ts ∧
        d'.edges.toList = d.edges.toList ++ brEdgesT f ctx bcs ts ∧ d'.st = d.st ∧ d'.alias = d.alias ∧
        d'.blocks = d.blocks ∧ ArgsOkT f ctx bcs
  | [], d, tg, d', tg', h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, by simp, by simp [brEdgesT], rfl, rfl, rfl, fun bc h => by simp at h⟩
  | bc :: bcs, d, tg, d', tg', h => by
    rw [List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i st hst
    unfold destBody at hst
    simp only [bind, Except.bind] at hst
    split at hst
    · cases hst
    rename_i tl htl
    have hidx := blockIdxE_ok htl
    obtain ⟨tb, htb, -⟩ := block?_of_idx hidx
    split at hst
    · rename_i hemp
      simp only [pure, Except.pure, Except.ok.injEq] at hst
      subst hst
      obtain ⟨ts, h1, h2, h3, h4, h5, h6, h7⟩ := destLoopT hreg bcs _ _ d' tg' h
      have hae : bc.args = [] := by simpa using hemp
      refine ⟨tl :: ts, ?_, by rw [h2]; simp, by rw [h3]; simp [brEdgesT, hae], h4, h5, h6, ?_⟩
      · simp only [edgeTargets, hidx, hae, List.isEmpty_nil, ite_true]
        rw [h1]; rfl
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨tb, htb, fun h => absurd hae h, by simp [hae]⟩
        · exact h7 b hb
    · rename_i hemp
      split at hst
      · cases hst
      rename_i args hargs
      simp only [pure, Except.pure, Except.ok.injEq] at hst
      subst hst
      obtain ⟨ts, h1, h2, h3, h4, h5, h6, h7⟩ := destLoopT hreg bcs _ _ d' tg' h
      obtain ⟨tb', htb', hcnt, hrg, rfl⟩ := blockArgRegs_okT hreg hargs
      have hne : bc.args.isEmpty = false := by simpa using hemp
      have hne' : bc.args ≠ [] := by simpa using hemp
      refine ⟨d.nextLabel :: ts, ?_, by rw [h2]; simp, by
          rw [h3]; simp [edgeD, brEdgesT, hne', hidx, List.zip_cons_cons],
        h4, h5, h6, ?_⟩
      · simp only [edgeTargets, hidx, hne]
        simp only [edgeD] at h1
        rw [h1]; rfl
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨tb', htb', fun _ => hcnt, hrg⟩
        · exact h7 b hb

/-- The register `lowerFunction` passes for a `try_call` successor argument (typed). -/
def tryEdgeArgT (ctx : Ctx) (rets pays : List Reg) : Clif.TryArg → Reg
  | .val v => vregOf ctx v
  | .ret i => rets.getD i .xzr
  | .exn i => pays.getD i .xzr

/-- The edge blocks of a `try_call`'s successors (typed). -/
def tryEdgesT (f : Clif.Function) (ctx : Ctx) (ds : List Clif.TryDest) (ls : List Label)
    (rets pays : List Reg) : List VBlock :=
  (ds.zip ls).filterMap fun (td, l) => (blockIdx? f td.block).map fun tl =>
    { label := l, insts := #[.jump tl], branchArgs := (td.args.map (tryEdgeArgT ctx rets pays)).toArray }

/-- What `lowerFunction` checks of a `try_call` successor argument at position `k` (typed). -/
def ArgOkT (ctx : Ctx) (nh nrets npays k : Nat) : Clif.TryArg → Prop
  | .val v => ctx.valueReg? v = some (vregOf ctx v)
  | .ret i => ¬ k < nh ∧ i < nrets
  | .exn i => k ≠ nh ∧ i < npays

/-- What `lowerFunction` checks of a `try_call` successor `td` at position `k` (typed). -/
def TryDestOkT (f : Clif.Function) (ctx : Ctx) (nh nrets npays k : Nat) (td : Clif.TryDest) : Prop :=
  (∃ tb, f.block? td.block = some tb ∧ tb.params.length = td.args.length) ∧
  ∀ a ∈ td.args, ArgOkT ctx nh nrets npays k a

theorem tryArgE_okT {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x)
    {rets pays : Array Reg} {nh k : Nat} {a : Clif.TryArg} {r : Reg}
    (h : tryArgE ctx rets pays nh k a = .ok r) :
    r = tryEdgeArgT ctx rets.toList pays.toList a ∧ ArgOkT ctx nh rets.size pays.size k a := by
  cases a with
  | val v =>
    simp only [tryArgE] at h
    cases hv : ctx.valueReg? v with
    | none => rw [hv] at h; cases h
    | some r' =>
      rw [hv] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have := hreg v _ hv
      subst this
      exact ⟨rfl, hv⟩
  | ret i =>
    simp only [tryArgE] at h
    split at h
    · cases h
    · rename_i hk
      cases hr : rets[i]? with
      | none => rw [hr] at h; cases h
      | some r' =>
        rw [hr] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hi := (Array.getElem?_eq_some_iff.mp hr).1
        refine ⟨?_, hk, hi⟩
        simp only [tryEdgeArgT]
        rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, hr]; rfl
  | exn i =>
    simp only [tryArgE] at h
    split at h
    · cases h
    · rename_i hk
      cases hr : pays[i]? with
      | none => rw [hr] at h; cases h
      | some r' =>
        rw [hr] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hi := (Array.getElem?_eq_some_iff.mp hr).1
        refine ⟨?_, by simpa using hk, hi⟩
        simp only [tryEdgeArgT]
        rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, hr]; rfl

theorem tryLoopT {f : Clif.Function} {ctx : Ctx}
    (hreg : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x) {rets pays : Array Reg} {nh : Nat} :
    ∀ (ds : List Clif.TryDest) (n : Nat) (d : DState) (tg : Array Label) (d' : DState) (tg' : Array Label),
      forIn (ds.zipIdx n) (d, tg) (tryBody f ctx rets pays nh) = .ok (d', tg') →
      (∀ td ∈ ds, (blockIdx? f td.block).isSome) ∧
      tg'.toList = tg.toList ++ (List.range ds.length).map (d.nextLabel + ·) ∧
      d'.nextLabel = d.nextLabel + ds.length ∧
      d'.edges.toList = d.edges.toList ++
        tryEdgesT f ctx ds ((List.range ds.length).map (d.nextLabel + ·)) rets.toList pays.toList ∧
      d'.st = d.st ∧ d'.alias = d.alias ∧ d'.blocks = d.blocks ∧
      ∀ i td, ds[i]? = some td → TryDestOkT f ctx nh rets.size pays.size (n + i) td
  | [], n, d, tg, d', tg', h => by
    simp only [List.zipIdx_nil, List.forIn_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ h => by simp at h, by simp, by simp, by simp [tryEdgesT], rfl, rfl, rfl,
      fun i td h => by simp at h⟩
  | td :: ds, n, d, tg, d', tg', h => by
    rw [List.zipIdx_cons, List.forIn_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i st hst
    unfold tryBody at hst
    simp only [bind, Except.bind] at hst
    split at hst
    · cases hst
    rename_i tl htl
    have hidx := blockIdxE_ok htl
    split at hst
    · rename_i tb htb
      split at hst
      · cases hst
      rename_i hcnt
      split at hst
      · cases hst
      rename_i args hargs
      simp only [pure, Except.pure, Except.ok.injEq] at hst
      subst hst
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := tryLoopT hreg ds (n + 1) _ _ d' tg' h
      obtain ⟨hsz, hel⟩ := amapM_ok hargs
      have hargs' : ∀ (i : Nat) (a : Clif.TryArg), td.args[i]? = some a → ∃ r : Reg, args[i]? = some r ∧
          r = tryEdgeArgT ctx rets.toList pays.toList a ∧ ArgOkT ctx nh rets.size pays.size n a := by
        intro i a ha
        obtain ⟨y, hy, hy'⟩ := hel i a (by simpa using ha)
        exact ⟨y, hy', tryArgE_okT hreg hy⟩
      have hargsEq : args = (td.args.map (tryEdgeArgT ctx rets.toList pays.toList)).toArray := by
        apply Array.ext
        · simp [hsz]
        · intro i h1 h2
          have hi : i < td.args.length := by simpa using h2
          obtain ⟨r, hr, e, -⟩ := hargs' i td.args[i] (List.getElem?_eq_getElem hi)
          rw [Array.getElem?_eq_getElem h1] at hr
          simp only [Option.some.injEq] at hr
          rw [hr, e]; simp
      have hrange : ∀ m : Nat, (List.range (m + 1)).map (d.nextLabel + ·) =
          d.nextLabel :: (List.range m).map (d.nextLabel + 1 + ·) := by
        intro m
        rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, Nat.add_zero]
        congr 1
        apply List.map_congr_left
        intro x _; simp only [Function.comp]; omega
      simp only [edgeD] at h1 h2 h3 h4 h5 h6
      refine ⟨?_, ?_, ?_, ?_, h4, h5, h6, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · rw [hidx]; rfl
        · exact h0 t ht
      · rw [h1, List.length_cons, hrange]; simp
      · rw [h2, List.length_cons]; omega
      · rw [h3, List.length_cons, hrange]
        simp [tryEdgesT, List.zip_cons_cons, hidx, hargsEq]
      · intro i t hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          refine ⟨⟨tb, htb, by simpa using hcnt⟩, fun a ha => ?_⟩
          obtain ⟨i, hi, e⟩ := List.getElem_of_mem ha
          obtain ⟨r, -, -, hm⟩ := hargs' i a (by rw [List.getElem?_eq_getElem hi, e])
          simpa using hm
        | succ i =>
          have := h7 i t (by simpa using hi)
          rwa [show n + 1 + i = n + (i + 1) by omega] at this
    · cases hst

/-! ## The terminator -/

theorem paramsMapM_okT {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x)
    {ps : List (Clif.ValueId × Clif.Ty)} {params : Array Reg}
    (h : ps.toArray.mapM (fun (p : Clif.ValueId × Clif.Ty) => match p with
      | (v, _) => match ctx.valueReg? v with
        | some r => (pure r : Except String Reg)
        | none => throw s!"unknown value v{v}") = .ok params) :
    params = (ps.map fun p => vregOf ctx p.1).toArray := by
  obtain ⟨hsz, hel⟩ := amapM_ok h
  apply Array.ext
  · simp [hsz]
  · intro i h1 h2
    have hi : i < ps.length := by simpa using h2
    obtain ⟨y, hy, hy'⟩ := hel i ps[i] (by simp [List.getElem?_eq_getElem hi])
    rw [Array.getElem?_eq_getElem h1] at hy'
    simp only [Option.some.injEq] at hy'
    cases hv : ctx.valueReg? ps[i].1 with
    | none => simp only [hv] at hy; cases hy
    | some r =>
      simp only [hv, pure, Except.pure, Except.ok.injEq] at hy
      rw [hy', ← hy, hreg _ _ hv]; simp

/-- The parameters of block `bi` (`B`), typed. -/
def paramsOfT (ctx : Ctx) (bi : Nat) (B : Clif.Block) : Array Reg :=
  if bi = 0 then #[] else (B.params.map fun p => vregOf ctx p.1).toArray

/-- The branch arguments of block `B`, typed. -/
def jumpArgsOfT (ctx : Ctx) (B : Clif.Block) : Array Reg :=
  match B.term with
  | .jump bc => (bc.args.map fun a => vregOf ctx a).toArray
  | _ => #[]

theorem paramsPart_okT {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x)
    {b : Clif.Block} {bi : Nat} {code : Array MInst} {d : DState} {st : LState} {n : List Isle.RuleId}
    {jumpArgs : Array Reg} {emitted : Array MInst} {d' : DState}
    (h : paramsPart ctx b bi code d st n jumpArgs emitted = .ok (.yield d')) :
    d' = blockD d st n (mkVB bi (code ++ emitted) (paramsOfT ctx bi b) jumpArgs) := by
  unfold paramsPart at h
  split at h
  · rename_i h0
    simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at h
    rw [← h]
    have : bi = 0 := by simpa using h0
    simp [paramsOfT, this, mkVB]
  · rename_i h0
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i params hp
    simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at h
    rw [← h, paramsMapM_okT hreg hp]
    have : bi ≠ 0 := by simpa using h0
    simp [paramsOfT, this, mkVB]

theorem finishBlock_okT {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = vregOf ctx x)
    {b : Clif.Block} {bi ti : Nat} {code : Array MInst} {d : DState} {ctx' : Ctx}
    {targets : Array Label} {jumpArgs : Array Reg} {tryInfo : Option TryInfo} {d' : DState}
    (h : finishBlock ctx b bi ti code d ctx' targets jumpArgs tryInfo = .ok (.yield d')) :
    ∃ out st n, runTerm ctx' (termCall b.term ti targets.toList).1 (termCall b.term ti targets.toList).2
        { d.st with emitted := #[] } = .ok (some out, st, n) ∧
      (∀ t, tryInfo = some t → ∃ c, st.emitted.back? = some (.call c)) ∧
      d' = blockD d st n (mkVB bi (code ++ emOf tryInfo st) (paramsOfT ctx bi b) jumpArgs) := by
  unfold finishBlock at h
  rw [termArgsOf_eq] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i res hrun
  obtain ⟨out, st, n⟩ := res
  simp only at h
  split at h
  · cases h
  rename_i hout
  cases out with
  | none => simp at hout
  | some out =>
  refine ⟨out, st, n, hrun, ?_⟩
  cases tryInfo with
  | none =>
    exact ⟨(fun _ h' => nomatch h'), paramsPart_okT hreg h⟩
  | some t =>
    simp only at h
    split at h
    · rename_i c hc
      have e := paramsPart_okT hreg h
      refine ⟨fun t' _ => ⟨c, hc⟩, ?_⟩
      have : st.emitted.pop.push (MInst.tryCall c t) = emOf (some t) st := by
        simp only [emOf, tryFix]
        rw [back_toList, hc]
        apply Array.ext'
        simp [Array.toList_pop]
      rw [e, this]
    · cases h

/-- The edge blocks `lowerFunction` creates for block `B` (lowered as `L`), typed. -/
def edgeBlocksT (f : Clif.Function) (ctx : Ctx) (B : Clif.Block) (L : BLow) : List VBlock :=
  match B.term, L.tl with
  | .tryCall _ _ et, some T | .tryCallIndirect _ _ et, some T =>
    (et.dests.zip L.targets).filterMap fun (td, l) => (blockIdx? f td.block).map fun tl =>
      { label := l, insts := #[.jump tl],
        branchArgs := (td.args.map (tryEdgeArgT ctx T.regs.1 T.regs.2)).toArray }
  | .jump _, _ => []
  | t, _ => ((dests t).zip L.targets).filterMap fun (bc, l) =>
    if bc.args.isEmpty then none else (blockIdx? f bc.block).map fun tl =>
      { label := l, insts := #[.jump tl], branchArgs := (bc.args.map fun a => vregOf ctx a).toArray }

theorem edgeBlocks_otherT {f : Clif.Function} {ctx : Ctx} {B : Clif.Block} (L : BLow)
    (hnj : ∀ bc, B.term ≠ .jump bc) (hnt : B.term.isTry = false) :
    edgeBlocksT f ctx B L = brEdgesT f ctx (dests B.term) L.targets := by
  unfold edgeBlocksT
  cases h : B.term <;> rw [h] at hnt hnj <;> cases L.tl <;>
    first | rfl | exact absurd rfl (hnj _) | (simp [Clif.Terminator.isTry] at hnt)

theorem edgeBlocks_jumpT {f : Clif.Function} {ctx : Ctx} {B : Clif.Block} (L : BLow)
    {bc : Clif.BlockCall} (h : B.term = .jump bc) : edgeBlocksT f ctx B L = [] := by
  unfold edgeBlocksT; rw [h]

theorem edgeBlocks_tryT {f : Clif.Function} {ctx : Ctx} {B : Clif.Block} (L : BLow)
    {et : Clif.ExnTable} (ht : IsTryWith B.term et) {T : TryLow} (hT : L.tl = some T) :
    edgeBlocksT f ctx B L = tryEdgesT f ctx et.dests L.targets T.regs.1 T.regs.2 := by
  unfold edgeBlocksT
  rcases ht with ⟨fn, args, h⟩ | ⟨c, args, h⟩ <;> rw [h, hT] <;> rfl

/-- What the terminator part of a block's lowering yields (typed). -/
structure TermOutT (f : Clif.Function) (ctx : Ctx) (B : Clif.Block) (k ti : Nat) (code : Array MInst)
    (ds : DState) (data : V) (d' : DState) (targets : List Label) (tl : Option TryLow) (tst' : LState)
    (nl' : Nat) : Prop where
  low : lowTerm f (termCallF ctx) (tryCallF ctx) ti B.term ds.st ds.nextLabel =
    some (data, targets, tl, tst', nl')
  st : d'.st = { tst' with emitted := #[] }
  nl : d'.nextLabel = nl'
  alias : d'.alias = ds.alias
  edges : ∀ L : BLow, L.targets = targets → L.tl = tl →
    d'.edges.toList = ds.edges.toList ++ edgeBlocksT f ctx B L
  blocks : d'.blocks = ds.blocks.push
    (mkVB k (code ++ (tsegOf tl tst').toArray) (paramsOfT ctx k B) (jumpArgsOfT ctx B))
  args : ArgsOkT f ctx (dests B.term)
  tryArgs : ∀ et, IsTryWith B.term et → ∃ T, tl = some T ∧ ∀ i td, et.dests[i]? = some td →
    TryDestOkT f ctx et.handlers.length T.regs.1.length T.regs.2.length i td
  tryLast : ∀ T, tl = some T → ∃ c, tst'.emitted.back? = some (.call c)

theorem jumpArgsOfT_other {ctx : Ctx} {B : Clif.Block} (hnj : ∀ bc, B.term ≠ .jump bc) :
    jumpArgsOfT ctx B = #[] := by
  unfold jumpArgsOfT; split
  · rename_i bc h; exact absurd h (hnj bc)
  · rfl

theorem termOtherT {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {B : Clif.Block} {k stop : Nat} {code : Array MInst}
    {ds : DState} {data : V} {d' : DState} (he : ds.st.emitted = #[])
    (hnj : ∀ bc, B.term ≠ .jump bc) (hnt : B.term.isTry = false)
    (hdata : termData (abiTerm f B.term) = .ok data)
    (h : (do
      let s ← forIn (destsOf B.term) (ds, (#[] : Array Label)) (destBody f ctx)
      finishBlock ctx B k (stop - 1) code s.1 (termCtx ctx (stop - 1) data) s.2 #[] none) =
        .ok (.yield d')) :
    ∃ targets tl tst' nl', TermOutT f ctx B k (stop - 1) code ds data d' targets tl tst' nl' := by
  have hreg := sp.regEqT
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i s hs
  obtain ⟨d1, tg⟩ := s
  obtain ⟨ts, hedge, htg, hed, hst, hal, hbl, hargs⟩ := destLoopT hreg _ ds #[] d1 tg hs
  obtain ⟨out, st, n, hrun, -, rfl⟩ := finishBlock_okT hreg h
  simp only at hrun
  rw [hst, st_eta he, htg] at hrun
  simp only [List.nil_append] at hrun htg
  rw [destsOf_eq] at hedge hargs hed
  have hlow : lowTerm f (termCallF ctx) (tryCallF ctx) (stop - 1) B.term ds.st ds.nextLabel =
      some (data, ts, none, st, d1.nextLabel) := by
    rw [lowTerm_nontry hnt, hdata, targetsOf_other hnj, hedge]
    simp only
    rw [show termCallF ctx (stop - 1) data B.term ts ds.st =
      runTerm (termCtx ctx (stop - 1) data) (termCall B.term (stop - 1) ts).1
        (termCall B.term (stop - 1) ts).2 ds.st from rfl, hrun]
  refine ⟨ts, none, st, d1.nextLabel, ⟨hlow, rfl, rfl, hal, fun L hL _ => ?_, ?_, hargs,
    fun et het => absurd (isTry_of het) (by rw [hnt]; simp), (fun T hT => nomatch hT)⟩⟩
  · simp only [blockD]
    rw [hed, edgeBlocks_otherT L hnj hnt, hL]
  · simp [blockD, emOf, tsegOf, fixTry, jumpArgsOfT_other hnj, hbl]

theorem termTryT {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {B : Clif.Block} {k stop : Nat} {code : Array MInst}
    {ds : DState} {data : V} {d' : DState} {et : Clif.ExnTable}
    (ht : IsTryWith B.term et) (hdata : tryCallData f B.term = .ok data)
    (h : tryTerm f ctx B k (stop - 1) code ds (termCtx ctx (stop - 1) data) et = .ok (.yield d')) :
    ∃ targets tl tst' nl', TermOutT f ctx B k (stop - 1) code ds data d' targets tl tst' nl' := by
  have hreg := sp.regEqT
  unfold tryTerm at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i q hexC
  obtain ⟨sig, items⟩ := q
  -- the typed operand of an integer `try_call` (`tryCallData` succeeded) is the integer one
  have hex : exnTableOpnd f et = .ok (sig, items) := by
    obtain ⟨s', i', he'⟩ : ∃ s' i', exnTableOpnd f et = .ok (s', i') := by
      rcases ht with ⟨fn, args, h'⟩ | ⟨c, args, h'⟩ <;> rw [h'] at hdata
      · obtain ⟨s', i', -, he', -⟩ := tryCallData_spec hdata; exact ⟨s', i', he'⟩
      · exact tryCallIndData_spec hdata
    have hC := exnTableOpndC_of he'
    rw [hexC] at hC
    cases hC
    exact he'
  have hrc := sigRets_classes_int (sigIntB_iff.mp (exnTableOpnd_int hex)).2
  simp only at h
  split at h
  · rename_i retsL paysL st1 htrC
    have htr : tryRegsOf sig ds.st = some ((retsL, paysL), st1) := by
      rw [← tryRegsOfC_eq hrc]; exact htrC
    split at h
    · cases h
    split at h
    · cases h
    rename_i s hs
    obtain ⟨d1, tg⟩ := s
    obtain ⟨hall, htg, hnl, hed, hst, hal, hbl, hdest⟩ := tryLoopT hreg et.dests 0 _ #[] d1 tg hs
    simp only at h
    split at h
    · rename_i t hti
      obtain ⟨out, st, n, hrun, hlast, rfl⟩ := finishBlock_okT hreg h
      simp only at hrun hst htg hnl hed hal
      rw [hst, htg] at hrun
      simp only [List.nil_append] at hrun htg hti hed
      rw [htg] at hti
      have htt : tryTargets f et.dests ds.nextLabel =
          some ((List.range et.dests.length).map (ds.nextLabel + ·), ds.nextLabel + et.dests.length) := by
        unfold tryTargets
        simp only [List.all_eq_true.mpr hall, ↓reduceIte]
      have hlow : lowTerm f (termCallF ctx) (tryCallF ctx) (stop - 1) B.term ds.st ds.nextLabel =
          some (data, (List.range et.dests.length).map (ds.nextLabel + ·),
            some ⟨t, sig, items, (retsL, paysL), st1⟩, st, ds.nextLabel + et.dests.length) := by
        rw [lowTerm_try ht, hdata, hex, htt]
        simp only
        rw [htr]
        simp only
        rw [hti]
        simp only
        rw [show tryCallF ctx (stop - 1) data (retsL, paysL) ((List.range et.dests.length).map (ds.nextLabel + ·))
            { st1 with emitted := #[] } =
          runTerm (tryCtx ctx (stop - 1) data (retsL, paysL)) "lower_branch"
            [.inst (stop - 1), .labels ((List.range et.dests.length).map (ds.nextLabel + ·))]
            { st1 with emitted := #[] } from rfl]
        have e2 : termCall B.term (stop - 1) ((List.range et.dests.length).map (ds.nextLabel + ·)) =
            ("lower_branch", [.inst (stop - 1), .labels ((List.range et.dests.length).map (ds.nextLabel + ·))]) := by
          rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] <;> rfl
        rw [e2] at hrun
        have e3 : tryCtx ctx (stop - 1) data (retsL, paysL) =
            { termCtx ctx (stop - 1) data with tryRegs := (retsL, paysL) } := rfl
        rw [e3, hrun]
      refine ⟨_, _, st, _, ⟨hlow, rfl, by simp [blockD, hnl], by simp [blockD, hal],
        fun L hL hT => ?_, ?_, ?_, fun et' het' => ?_, fun T hT => ?_⟩⟩
      · simp only [blockD]
        rw [hed, edgeBlocks_tryT L ht hT, hL]
      · simp only [blockD, hbl, emOf, tsegOf, fixTry]
        rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> simp [jumpArgsOfT, h']
      · rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] <;> intro b hb <;> simp [dests] at hb
      · rw [isTryWith_eq ht het']
        refine ⟨_, rfl, fun i td hi => ?_⟩
        have := hdest i td hi
        simpa using this
      · simp only [Option.some.injEq] at hT
        exact hlast t rfl
    · cases h
  · cases h

theorem termPart_okT {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {B : Clif.Block} {k stop : Nat} {code : Array MInst}
    {ds : DState} {data : V} {d' : DState} (he : ds.st.emitted = #[]) (hdata : DataOk f B.term data)
    (h : termPart f ctx B k stop code ds data = .ok (.yield d')) :
    (∀ vs, B.term = .ret vs → sretRet f = [] → sigRets f.sig = f.sig.returns) ∧
    ∃ targets tl tst' nl', TermOutT f ctx B k (stop - 1) code ds data d' targets tl tst' nl' := by
  have hreg := sp.regEqT
  unfold termPart at h
  by_cases hsret : sretBad f B.term = true
  · simp only [hsret, ↓reduceIte] at h; cases h
  simp only [hsret, Bool.false_eq_true, ↓reduceIte] at h
  refine ⟨fun vs hv hs => ?_, ?_⟩
  · rw [hv] at hsret
    simp only [sretBad, hs, List.isEmpty_nil, Bool.and_true, Bool.true_and, bne_iff_ne, ne_eq,
      Decidable.not_not] at hsret
    simpa using hsret
  generalize ht : B.term = t at h hdata
  cases t with
  | jump bc =>
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i jargs hj
    split at h
    · cases h
    rename_i tl htl
    obtain ⟨out, st, n, hrun, -, rfl⟩ := finishBlock_okT hreg h
    obtain ⟨tb, htb, hcnt, hrg, rfl⟩ := blockArgRegs_okT hreg hj
    have hidx := blockIdxE_ok htl
    rw [st_eta he] at hrun
    have hlow : lowTerm f (termCallF ctx) (tryCallF ctx) (stop - 1) B.term ds.st ds.nextLabel =
        some (data, [tl], none, st, ds.nextLabel) := by
      rw [lowTerm_nontry (by rw [ht]; rfl), ht]
      simp only [DataOk] at hdata
      simp only [hdata, targetsOf, hidx, Option.map_some]
      have e : ((#[] : Array Label).push tl).toList = [tl] := rfl
      rw [e, ht] at hrun
      rw [show termCallF ctx (stop - 1) data (Clif.Terminator.jump bc) [tl] ds.st =
        runTerm (termCtx ctx (stop - 1) data) (termCall (Clif.Terminator.jump bc) (stop - 1) [tl]).1
          (termCall (Clif.Terminator.jump bc) (stop - 1) [tl]).2 ds.st from rfl, hrun]
    refine ⟨[tl], none, st, ds.nextLabel, ⟨hlow, rfl, rfl, rfl, fun L _ _ => ?_, ?_, ?_,
      fun et het => ?_, (fun T hT => nomatch hT)⟩⟩
    · simp [blockD, edgeBlocks_jumpT L ht]
    · simp [blockD, emOf, tsegOf, fixTry, jumpArgsOfT, ht]
    · rw [ht]; intro b hb
      simp only [dests, List.mem_singleton] at hb; subst hb
      exact ⟨tb, htb, fun _ => hcnt, hrg⟩
    · rw [ht] at het; rcases het with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
  | tryCall fn args et =>
    simp only [DataOk] at h hdata
    rw [← ht] at hdata
    exact termTryT sp (.inl ⟨fn, args, ht⟩) hdata h
  | tryCallIndirect c args et =>
    simp only [DataOk] at h hdata
    rw [← ht] at hdata
    exact termTryT sp (.inr ⟨c, args, ht⟩) hdata h
  | brif c t e =>
    simp only [DataOk] at h hdata
    rw [← ht] at h hdata
    exact termOtherT sp he (by rw [ht]; intro bc h; cases h) (by rw [ht]; rfl) hdata h
  | brTable x dflt tbl =>
    simp only [DataOk] at h hdata
    rw [← ht] at h hdata
    exact termOtherT sp he (by rw [ht]; intro bc h; cases h) (by rw [ht]; rfl) hdata h
  | ret vs =>
    simp only [DataOk] at h hdata
    rw [← ht] at h hdata
    exact termOtherT sp he (by rw [ht]; intro bc h; cases h) (by rw [ht]; rfl) hdata h
  | trap c =>
    simp only [DataOk] at h hdata
    rw [← ht] at h hdata
    exact termOtherT sp he (by rw [ht]; intro bc h; cases h) (by rw [ht]; rfl) hdata h
  | returnCall fn args =>
    simp only [DataOk, abiTerm, termData] at hdata
    cases hdata

end Backend.Proof.Driver
