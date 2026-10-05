import FV.Backend.Proof.LowerLoopCtx
import FV.Backend.Proof.IselFlow

/-!
# `lowerFunction`'s loop, simulated

The loop of `lowerFunction'` (`LowerLoopCode.lean`) over the blocks computes what `lowBlocks`
records: the statements' segments, the terminator's lowering, the edge blocks, the label counter
and the aliases (`blocks_step`, `loop_sim`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Prep

/-! ## Helpers -/

theorem amode_mapRegs_id (m : AMode) : m.mapRegs id = m := by
  cases m <;> rfl

theorem condBr_mapRegs_id (k : CondBrKind) : k.mapRegs id = k := by
  cases k <;> rfl

theorem mapRegs_id (i : MInst) : i.mapRegs id = i := by
  cases i
  case call info =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> first | rfl | simp [MInst.mapRegs]
  case tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> first | rfl | simp [MInst.mapRegs]
  all_goals first | rfl | simp [MInst.mapRegs, amode_mapRegs_id, condBr_mapRegs_id]

theorem mapRegs_id_fun : MInst.mapRegs id = id := funext mapRegs_id

theorem map_mapRegs_id (l : List MInst) : l.map (MInst.mapRegs id) = l := by
  rw [mapRegs_id_fun, List.map_id]

theorem back_toList {α : Type} (a : Array α) : a.toList.getLast? = a.back? := by
  rw [Array.back?_eq_getElem?, List.getLast?_eq_getElem?]; simp

theorem getElem!_of {α : Type} [Inhabited α] {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) :
    a[i]! = x := by
  simp [getElem!_def, h]

/-! ## The recorded lowering with its end state -/

/-- `lowBlocks`, also returning the final state and next edge label. -/
def lowB (f : Clif.Function) (call : StmtCall) (tcall : TermCallF) (ycall : TryCallF) :
    Nat → List Clif.Block → LState → Nat → Option (List BLow × LState × Nat)
  | _, [], st, nl => some ([], st, nl)
  | start, B :: Bs, st, nl =>
    match lowStmts call start B.body st with
    | none => none
    | some (sls, stE) =>
      match lowTerm f tcall ycall (start + B.body.length) B.term { stE with emitted := #[] } nl with
      | some (data, targets, tl, tst', nl') =>
        (lowB f call tcall ycall (start + B.body.length + 1) Bs { tst' with emitted := #[] } nl').map
          fun r => (⟨start, sls, data, targets, { stE with emitted := #[] }, tst', tl⟩ :: r.1, r.2)
      | none => none

theorem lowBlocks_eq (f : Clif.Function) (call : StmtCall) (tcall : TermCallF) (ycall : TryCallF) :
    ∀ (Bs : List Clif.Block) (start : Nat) (st : LState) (nl : Nat),
      lowBlocks f call tcall ycall start Bs st nl = (lowB f call tcall ycall start Bs st nl).map (·.1)
  | [], _, _, _ => rfl
  | B :: Bs, start, st, nl => by
    simp only [lowBlocks, lowB]
    rcases lowStmts call start B.body st with _ | ⟨sls, stE⟩
    · rfl
    · dsimp only
      rcases lowTerm f tcall ycall (start + B.body.length) B.term { stE with emitted := #[] } nl with
        _ | ⟨data, targets, tl, tst', nl'⟩
      · rfl
      · dsimp only
        rw [lowBlocks_eq f call tcall ycall Bs]
        cases lowB f call tcall ycall _ Bs _ _ <;> rfl

theorem lowB_cons (f : Clif.Function) (call : StmtCall) (tcall : TermCallF) (ycall : TryCallF)
    (start : Nat) (B : Clif.Block) (Bs : List Clif.Block) (st : LState) (nl : Nat) :
    lowB f call tcall ycall start (B :: Bs) st nl =
      match lowStmts call start B.body st with
      | none => none
      | some (sls, stE) =>
        match lowTerm f tcall ycall (start + B.body.length) B.term { stE with emitted := #[] } nl with
        | some (data, targets, tl, tst', nl') =>
          (lowB f call tcall ycall (start + B.body.length + 1) Bs { tst' with emitted := #[] } nl').map
            fun r => (⟨start, sls, data, targets, { stE with emitted := #[] }, tst', tl⟩ :: r.1, r.2)
        | none => none := rfl

theorem lowB_append (f : Clif.Function) (call : StmtCall) (tcall : TermCallF) (ycall : TryCallF)
    (Cs : List Clif.Block) : ∀ (Bs : List Clif.Block) (start : Nat) (st : LState) (nl : Nat),
    lowB f call tcall ycall start (Bs ++ Cs) st nl =
      (lowB f call tcall ycall start Bs st nl).bind fun r =>
        (lowB f call tcall ycall (start + bsl Bs Bs.length) Cs r.2.1 r.2.2).map fun q =>
          (r.1 ++ q.1, q.2)
  | [], start, st, nl => by
    simp only [List.nil_append, bsl, List.take_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    simp only [lowB, Option.bind_some]
    cases lowB f call tcall ycall start Cs st nl <;> rfl
  | B' :: Bs, start, st, nl => by
    rw [List.cons_append, lowB_cons f call tcall ycall start B' (Bs ++ Cs),
      lowB_cons f call tcall ycall start B' Bs]
    rcases lowStmts call start B'.body st with _ | ⟨sls, stE⟩
    · rfl
    · dsimp only
      rcases lowTerm f tcall ycall (start + B'.body.length) B'.term { stE with emitted := #[] } nl with
        _ | ⟨data, targets, tl, tst', nl'⟩
      · rfl
      · dsimp only
        rw [lowB_append f call tcall ycall Cs Bs]
        cases lowB f call tcall ycall _ Bs _ _ with
        | none => rfl
        | some r =>
          simp only [Option.bind_some, Option.map_some, List.length_cons, bsl_cons]
          rw [show start + B'.body.length + 1 + bsl Bs Bs.length =
            start + (B'.body.length + 1 + bsl Bs Bs.length) by omega]
          cases lowB f call tcall ycall (start + (B'.body.length + 1 + bsl Bs Bs.length)) Cs r.2.1 r.2.2 <;>
            rfl

theorem lowStmts_cons (call : StmtCall) (ii : Nat) (s : Clif.Stmt) (ss : List Clif.Stmt) (st : LState) :
    lowStmts call ii (s :: ss) st =
      match call ii { st with emitted := #[] } with
      | .ok (out, st', _) =>
        match regsOf out with
        | some rss =>
          (lowStmts call (ii + 1) ss { st' with emitted := #[] }).map fun (sls, stE) =>
            (⟨{ st with emitted := #[] }, rss, st'⟩ :: sls, stE)
        | none => none
      | .error _ => none := rfl

theorem lowStmts_append (call : StmtCall) (ts : List Clif.Stmt) : ∀ (ss : List Clif.Stmt) (ii : Nat) (st : LState),
    lowStmts call ii (ss ++ ts) st =
      (lowStmts call ii ss st).bind fun p =>
        (lowStmts call (ii + ss.length) ts p.2).map fun q => (p.1 ++ q.1, q.2)
  | [], ii, st => by
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    simp only [lowStmts, Option.bind_some]
    cases lowStmts call ii ts st <;> rfl
  | s' :: ss, ii, st => by
    rw [List.cons_append, lowStmts_cons call ii s' (ss ++ ts), lowStmts_cons call ii s' ss]
    rcases call ii { st with emitted := #[] } with _ | ⟨out, st', tr⟩
    · rfl
    · dsimp only
      cases regsOf out with
      | none => rfl
      | some rss =>
        dsimp only
        rw [lowStmts_append call ts ss]
        cases lowStmts call (ii + 1) ss _ with
        | none => rfl
        | some r =>
          simp only [Option.bind_some, Option.map_some, List.length_cons]
          rw [show ii + 1 + ss.length = ii + (ss.length + 1) by omega]
          cases lowStmts call (ii + (ss.length + 1)) ts r.2 <;> rfl

/-! ## The result loop -/

/-- The aliases of a statement with results `results` lowered to `rss` (`aliasOf`'s inner part). -/
def stmtAl (results : List Nat) (rss : List (List Reg)) : List (Nat × Nat) :=
  (results.zip rss).filterMap fun (r, rs) => match rs with
    | [.vreg out _] => some (r, out)
    | _ => none

theorem aliasOf_eq (f : Clif.Function) (bl : List BLow) :
    aliasOf f bl = (f.blocks.zip bl).flatMap fun (p : Clif.Block × BLow) =>
      (p.1.body.zip p.2.sl).flatMap fun (q : Clif.Stmt × SLow) => stmtAl q.1.results q.2.rss := rfl

theorem resLoop {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int) :
    ∀ (rs : List Nat) (rss : List (List Reg)) (d : DState) (ex : Array MInst) (d' : DState)
      (ex' : Array MInst), forIn (rs.zip rss) (d, ex) (resBody ctx) = .ok (d', ex') →
      d' = { d with alias := (stmtAl rs rss).foldl aliasStep d.alias } ∧
      ex'.toList = ex.toList ++ extraOf rs rss ∧ ∀ p ∈ rs.zip rss, ∃ x, p.2 = [x]
  | [], rss, d, ex, d', ex', h => by
    simp only [List.zip_nil_left, List.forIn_nil, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [stmtAl, extraOf]
  | r :: rs, [], d, ex, d', ex', h => by
    simp only [List.zip_nil_right, List.forIn_nil, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [stmtAl, extraOf]
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
      split at hst
      · rename_i o' c
        simp only at hst
        simp only [pure, Except.pure, Except.ok.injEq] at hst
        subst hst
        obtain ⟨h1, h2, h3⟩ := resLoop hreg rs rss _ _ d' ex' h
        refine ⟨by rw [h1]; simp [stmtAl, List.zip_cons_cons, aliasStep], by
          rw [h2]; simp [extraOf, List.zip_cons_cons], fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨_, rfl⟩
        · exact h3 p hp
      · rename_i out hne
        simp only [pure, Except.pure, Except.ok.injEq] at hst
        subst hst
        obtain ⟨h1, h2, h3⟩ := resLoop hreg rs rss _ _ d' ex' h
        refine ⟨by rw [h1]; simp [stmtAl, List.zip_cons_cons, List.filterMap_cons]; split <;> simp_all, by
          rw [h2]; simp [extraOf, List.zip_cons_cons], fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨_, rfl⟩
        · exact h3 p hp
      · cases hst
    · cases hst

/-! ## The statement loop -/

/-- A statement's segment before renaming. -/
def segOf (q : Clif.Stmt × SLow) : List MInst := q.2.st'.emitted.toList ++ extraOf q.1.results q.2.rss

/-- The facts `LoopFacts.results` records, for statements `ss` lowered as `sls`. -/
def ResOk (ss : List Clif.Stmt) (sls : List SLow) : Prop :=
  ∀ (j : Nat) (stm : Clif.Stmt) (sl : SLow), ss[j]? = some stm → sls[j]? = some sl →
    (sl.rss.length = stm.results.length ∨ stm.results = []) ∧
    ∀ (r : Nat) (rs : List Reg), (r, rs) ∈ stm.results.zip sl.rss → ∃ x, rs = [x]

/-- The invariant of the statement loop after `j` statements (from `d`, `code`). -/
def SInv (ctx : Ctx) (start : Nat) (ss : List Clif.Stmt) (d : DState) (code : Array MInst) (j : Nat)
    (s : DState × Array MInst) : Prop :=
  ∃ sls, lowStmts (stmtCall ctx) start (ss.take j) d.st = some (sls, s.1.st) ∧
    s.1.blocks = d.blocks ∧ s.1.edges = d.edges ∧ s.1.nextLabel = d.nextLabel ∧
    s.1.alias = (((ss.take j).zip sls).flatMap fun q => stmtAl q.1.results q.2.rss).foldl aliasStep d.alias ∧
    s.2.toList = code.toList ++ ((ss.take j).zip sls).flatMap segOf ∧
    s.1.st.emitted = #[] ∧ ResOk (ss.take j) sls

theorem lowStmts_len {call : StmtCall} {ii : Nat} {ss : List Clif.Stmt} {st : LState} {sls : List SLow}
    {stE : LState} (h : lowStmts call ii ss st = some (sls, stE)) : sls.length = ss.length :=
  (lowStmts_spec h).1

theorem stmtLoop {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {k : Nat} {B : Clif.Block} (hB : f.blocks[k]? = some B)
    {d : DState} {code : Array MInst} (he : d.st.emitted = #[]) {r : DState × Array MInst}
    (h : forIn (List.range' (blockStart f k) B.body.length) (d, code) (stmtBody ctx) = .ok r) :
    SInv ctx (blockStart f k) B.body d code B.body.length r := by
  have := forIn_inv (stmtBody ctx) (List.range' (blockStart f k) B.body.length)
    (SInv ctx (blockStart f k) B.body d code) ?_ ?_ (d, code) r ?_ h
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
        obtain ⟨e1, e2, e3⟩ := resLoop sp.regEq _ _ _ _ _ _ hq
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
          simp [segOf, hcode, hir, e2]
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

theorem blockIdxE_ok {f : Clif.Function} {b tl : Nat} (h : blockIdxE f b = .ok tl) :
    blockIdx? f b = some tl := by
  unfold blockIdxE at h
  unfold blockIdx?
  split at h
  · cases h; assumption
  · cases h

theorem blockIdxE_of {f : Clif.Function} {b tl : Nat} (h : blockIdx? f b = some tl) :
    blockIdxE f b = .ok tl := by
  unfold blockIdxE; unfold blockIdx? at h; rw [h]; rfl

theorem block?_of_idx {f : Clif.Function} {b tl : Nat} (h : blockIdx? f b = some tl) :
    ∃ tb, f.block? b = some tb ∧ f.blocks[tl]? = some tb := by
  unfold blockIdx? at h
  obtain ⟨hl, hp, hlt⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨f.blocks[tl], ?_, List.getElem?_eq_getElem hl⟩
  unfold Clif.Function.block?
  rw [List.find?_eq_some_iff_getElem]
  exact ⟨hp, tl, hl, rfl, fun j hj => by simpa using hlt j hj⟩

theorem blockArgRegs_ok {f : Clif.Function} {ctx : Ctx}
    (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int) {bc : Clif.BlockCall}
    {args : Array Reg} (h : blockArgRegs ctx f bc = .ok args) :
    ∃ tb, f.block? bc.block = some tb ∧ tb.params.length = bc.args.length ∧
      (∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a .int)) ∧
      args = (bc.args.map fun a => Reg.vreg a .int).toArray := by
  unfold blockArgRegs at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i tb htb
    split at h
    · cases h
    rename_i hc
    obtain ⟨hsz, hel⟩ := amapM_ok h
    have hrg : ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a .int) := by
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

/-- The edge blocks of a `brif`/`br_table`'s successors `bcs` with labels `ls`. -/
def brEdges (f : Clif.Function) (bcs : List Clif.BlockCall) (ls : List Label) : List VBlock :=
  (bcs.zip ls).filterMap fun (bc, l) =>
    if bc.args.isEmpty then none else (blockIdx? f bc.block).map fun tl =>
      { label := l, insts := #[.jump tl], branchArgs := (bc.args.map fun a => Reg.vreg a .int).toArray }

/-- The facts `LoopFacts.args` records of successors `bcs`. -/
def ArgsOk (f : Clif.Function) (ctx : Ctx) (bcs : List Clif.BlockCall) : Prop :=
  ∀ bc ∈ bcs, ∃ tb, f.block? bc.block = some tb ∧ (bc.args ≠ [] → tb.params.length = bc.args.length) ∧
    ∀ a ∈ bc.args, ctx.valueReg? a = some (.vreg a .int)

theorem destLoop {f : Clif.Function} {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int) :
    ∀ (bcs : List Clif.BlockCall) (d : DState) (tg : Array Label) (d' : DState) (tg' : Array Label),
      forIn bcs (d, tg) (destBody f ctx) = .ok (d', tg') →
      ∃ ts, edgeTargets f bcs d.nextLabel = some (ts, d'.nextLabel) ∧ tg'.toList = tg.toList ++ ts ∧
        d'.edges.toList = d.edges.toList ++ brEdges f bcs ts ∧ d'.st = d.st ∧ d'.alias = d.alias ∧
        d'.blocks = d.blocks ∧ ArgsOk f ctx bcs
  | [], d, tg, d', tg', h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, by simp, by simp [brEdges], rfl, rfl, rfl, fun bc h => by simp at h⟩
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
      obtain ⟨ts, h1, h2, h3, h4, h5, h6, h7⟩ := destLoop hreg bcs _ _ d' tg' h
      have hae : bc.args = [] := by simpa using hemp
      refine ⟨tl :: ts, ?_, by rw [h2]; simp, by rw [h3]; simp [brEdges, hae], h4, h5, h6, ?_⟩
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
      obtain ⟨ts, h1, h2, h3, h4, h5, h6, h7⟩ := destLoop hreg bcs _ _ d' tg' h
      obtain ⟨tb', htb', hcnt, hrg, rfl⟩ := blockArgRegs_ok hreg hargs
      have hne : bc.args.isEmpty = false := by simpa using hemp
      have hne' : bc.args ≠ [] := by simpa using hemp
      refine ⟨d.nextLabel :: ts, ?_, by rw [h2]; simp, by
          rw [h3]; simp [edgeD, brEdges, hne', hidx, List.zip_cons_cons],
        h4, h5, h6, ?_⟩
      · simp only [edgeTargets, hidx, hne]
        simp only [edgeD] at h1
        rw [h1]; rfl
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨tb', htb', fun _ => hcnt, hrg⟩
        · exact h7 b hb

/-- The edge blocks of a `try_call`'s successors `ds` with labels `ls` (return/payload vregs
`rets`, `pays`). -/
def tryEdges (f : Clif.Function) (ds : List Clif.TryDest) (ls : List Label) (rets pays : List Reg) :
    List VBlock :=
  (ds.zip ls).filterMap fun (td, l) => (blockIdx? f td.block).map fun tl =>
    { label := l, insts := #[.jump tl], branchArgs := (td.args.map (tryEdgeArg rets pays)).toArray }

/-- What `lowerFunction` checks of a `try_call` successor argument at position `k`. -/
def ArgOk (ctx : Ctx) (nh nrets npays k : Nat) : Clif.TryArg → Prop
  | .val v => ctx.valueReg? v = some (.vreg v .int)
  | .ret i => ¬ k < nh ∧ i < nrets
  | .exn i => k ≠ nh ∧ i < npays

/-- What `lowerFunction` checks of a `try_call` successor `td` at position `k` (`nh` handlers). -/
def TryDestOk (f : Clif.Function) (ctx : Ctx) (nh nrets npays k : Nat) (td : Clif.TryDest) : Prop :=
  (∃ tb, f.block? td.block = some tb ∧ tb.params.length = td.args.length) ∧
  ∀ a ∈ td.args, ArgOk ctx nh nrets npays k a

theorem tryArgE_ok {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int)
    {rets pays : Array Reg} {nh k : Nat} {a : Clif.TryArg} {r : Reg}
    (h : tryArgE ctx rets pays nh k a = .ok r) :
    r = tryEdgeArg rets.toList pays.toList a ∧ ArgOk ctx nh rets.size pays.size k a := by
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
        simp only [tryEdgeArg]
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
        simp only [tryEdgeArg]
        rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, hr]; rfl

theorem tryLoop {f : Clif.Function} {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int)
    {rets pays : Array Reg} {nh : Nat} :
    ∀ (ds : List Clif.TryDest) (n : Nat) (d : DState) (tg : Array Label) (d' : DState) (tg' : Array Label),
      forIn (ds.zipIdx n) (d, tg) (tryBody f ctx rets pays nh) = .ok (d', tg') →
      (∀ td ∈ ds, (blockIdx? f td.block).isSome) ∧
      tg'.toList = tg.toList ++ (List.range ds.length).map (d.nextLabel + ·) ∧
      d'.nextLabel = d.nextLabel + ds.length ∧
      d'.edges.toList = d.edges.toList ++
        tryEdges f ds ((List.range ds.length).map (d.nextLabel + ·)) rets.toList pays.toList ∧
      d'.st = d.st ∧ d'.alias = d.alias ∧ d'.blocks = d.blocks ∧
      ∀ i td, ds[i]? = some td → TryDestOk f ctx nh rets.size pays.size (n + i) td
  | [], n, d, tg, d', tg', h => by
    simp only [List.zipIdx_nil, List.forIn_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ h => by simp at h, by simp, by simp, by simp [tryEdges], rfl, rfl, rfl,
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
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := tryLoop hreg ds (n + 1) _ _ d' tg' h
      obtain ⟨hsz, hel⟩ := amapM_ok hargs
      have hargs' : ∀ (i : Nat) (a : Clif.TryArg), td.args[i]? = some a → ∃ r : Reg, args[i]? = some r ∧
          r = tryEdgeArg rets.toList pays.toList a ∧ ArgOk ctx nh rets.size pays.size n a := by
        intro i a ha
        obtain ⟨y, hy, hy'⟩ := hel i a (by simpa using ha)
        exact ⟨y, hy', tryArgE_ok hreg hy⟩
      have hargsEq : args = (td.args.map (tryEdgeArg rets.toList pays.toList)).toArray := by
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
        simp [tryEdges, List.zip_cons_cons, hidx, hargsEq]
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

theorem foldl_inv' {α β : Type} (g : β → α → β) (P : β → Prop) (h : ∀ b a, P b → P (g b a)) :
    ∀ (l : List α) (b : β), P b → P (l.foldl g b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_inv' g P h l (g b a) (h b a hb)

theorem tryRegsOf_mono {sig : Clif.Signature} {st st' : LState} {r : List Reg × List Reg}
    (h : tryRegsOf sig st = some (r, st')) : st.nextVreg ≤ st'.nextVreg ∧ st'.emitted = st.emitted := by
  unfold tryRegsOf at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  rename_i ps hps
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have P1 := foldl_inv' (fun (x : Array Reg × LState) (_ : Reg) =>
      ((x.1.push (x.2.fresh .int).1, (x.2.fresh .int).2) : Array Reg × LState))
    (fun x => st.nextVreg ≤ x.2.nextVreg ∧ x.2.emitted = st.emitted)
    (fun b a hb => ⟨Nat.le_trans hb.1 (by simp [LState.fresh]), by simp [LState.fresh, hb.2]⟩) ps (#[], st)
    ⟨Nat.le_refl _, rfl⟩
  refine foldl_inv' _ (fun (x : Array Reg × LState) => st.nextVreg ≤ x.2.nextVreg ∧
    x.2.emitted = st.emitted) ?_ _ _ P1
  intro b a hb
  split
  · exact hb
  · exact ⟨Nat.le_trans hb.1 (by simp [LState.fresh]), by simp [LState.fresh, hb.2]⟩

theorem st_eta {st : LState} (h : st.emitted = #[]) : { st with emitted := #[] } = st := by
  rcases st with ⟨a, b, c, d⟩; simp only at h; simp [h]

theorem paramsMapM_ok {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int)
    {ps : List (Clif.ValueId × Clif.Ty)} {params : Array Reg}
    (h : ps.toArray.mapM (fun (p : Clif.ValueId × Clif.Ty) => match p with
      | (v, _) => match ctx.valueReg? v with
        | some r => (pure r : Except String Reg)
        | none => throw s!"unknown value v{v}") = .ok params) :
    params = (ps.map fun p => Reg.vreg p.1 .int).toArray := by
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

/-- The terminator's segment of a block before renaming (`tseg id`). -/
def tsegOf (tl : Option TryLow) (tst' : LState) : List MInst := fixTry tl tst'.emitted.toList

/-- A block. -/
def mkVB (l : Label) (insts : Array MInst) (params branchArgs : Array Reg) : VBlock :=
  { label := l, insts, params, branchArgs }

/-- The parameters of block `bi` (`B`). -/
def paramsOf (bi : Nat) (B : Clif.Block) : Array Reg :=
  if bi = 0 then #[] else (B.params.map fun p => Reg.vreg p.1 .int).toArray

/-- The branch arguments of block `B`. -/
def jumpArgsOf (B : Clif.Block) : Array Reg :=
  match B.term with
  | .jump bc => (bc.args.map fun a => Reg.vreg a .int).toArray
  | _ => #[]

theorem paramsPart_ok {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int)
    {b : Clif.Block} {bi : Nat} {code : Array MInst} {d : DState} {st : LState} {n : List Isle.RuleId}
    {jumpArgs : Array Reg} {emitted : Array MInst} {d' : DState}
    (h : paramsPart ctx b bi code d st n jumpArgs emitted = .ok (.yield d')) :
    d' = blockD d st n (mkVB bi (code ++ emitted) (paramsOf bi b) jumpArgs) := by
  unfold paramsPart at h
  split at h
  · rename_i h0
    simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at h
    rw [← h]
    have : bi = 0 := by simpa using h0
    simp [paramsOf, this, mkVB]
  · rename_i h0
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i params hp
    simp only [pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at h
    rw [← h, paramsMapM_ok hreg hp]
    have : bi ≠ 0 := by simpa using h0
    simp [paramsOf, this, mkVB]

theorem termArgsOf_eq (t : Clif.Terminator) (ti : Nat) (targets : Array Label) :
    termArgsOf t ti targets = termCall t ti targets.toList := by
  cases t <;> rfl

/-- The terminator's code after `lowerFunction`'s `tryCall` replacement. -/
def emOf (tryInfo : Option TryInfo) (st : LState) : Array MInst :=
  match tryInfo with
  | none => st.emitted
  | some t => (tryFix t st.emitted.toList).toArray

theorem finishBlock_ok {ctx : Ctx} (hreg : ∀ x r, ctx.valueReg? x = some r → r = .vreg x .int)
    {b : Clif.Block} {bi ti : Nat} {code : Array MInst} {d : DState} {ctx' : Ctx}
    {targets : Array Label} {jumpArgs : Array Reg} {tryInfo : Option TryInfo} {d' : DState}
    (h : finishBlock ctx b bi ti code d ctx' targets jumpArgs tryInfo = .ok (.yield d')) :
    ∃ out st n, runTerm ctx' (termCall b.term ti targets.toList).1 (termCall b.term ti targets.toList).2
        { d.st with emitted := #[] } = .ok (some out, st, n) ∧
      (∀ t, tryInfo = some t → ∃ c, st.emitted.back? = some (.call c)) ∧
      d' = blockD d st n (mkVB bi (code ++ emOf tryInfo st) (paramsOf bi b) jumpArgs) := by
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
    exact ⟨(fun _ h' => nomatch h'), paramsPart_ok hreg h⟩
  | some t =>
    simp only at h
    split at h
    · rename_i c hc
      have e := paramsPart_ok hreg h
      refine ⟨fun t' _ => ⟨c, hc⟩, ?_⟩
      have : st.emitted.pop.push (MInst.tryCall c t) = emOf (some t) st := by
        simp only [emOf, tryFix]
        rw [back_toList, hc]
        apply Array.ext'
        simp [Array.toList_pop]
      rw [e, this]
    · cases h

/-- The terminator data `lowerFunction` computes for `t`. -/
def DataOk (f : Clif.Function) (t : Clif.Terminator) (data : V) : Prop :=
  match t with
  | .tryCall .. | .tryCallIndirect .. => tryCallData f t = .ok data
  | _ => termData (abiTerm f t) = .ok data

theorem lowTerm_nontry {f : Clif.Function} {tc : TermCallF} {yc : TryCallF} {ti : Nat}
    {t : Clif.Terminator} (hnt : t.isTry = false) (tst : LState) (nl : Nat) :
    lowTerm f tc yc ti t tst nl =
      match termData (abiTerm f t), targetsOf f t nl with
      | .ok data, some (targets, nl') =>
        match tc ti data t targets tst with
        | .ok (some _, tst', _) => some (data, targets, none, tst', nl')
        | _ => none
      | _, _ => none := by
  cases t <;> simp_all [Clif.Terminator.isTry] <;> rfl

theorem lowTerm_try {f : Clif.Function} {tc : TermCallF} {yc : TryCallF} {ti : Nat}
    {t : Clif.Terminator} {et : Clif.ExnTable} (ht : IsTryWith t et) (tst : LState) (nl : Nat) :
    lowTerm f tc yc ti t tst nl =
      match tryCallData f t, exnTableOpnd f et, tryTargets f et.dests nl with
      | .ok data, .ok (sig, items), some (targets, nl') =>
        match tryRegsOf sig tst with
        | some (trs, st1) =>
          match tryInfoOf sig items targets with
          | some info =>
            match yc ti data trs targets { st1 with emitted := #[] } with
            | .ok (some _, tst', _) => some (data, targets, some ⟨info, sig, items, trs, st1⟩, tst', nl')
            | _ => none
          | none => none
        | none => none
      | _, _, _ => none := by
  rcases ht with ⟨fn, args, rfl⟩ | ⟨c, args, rfl⟩ <;> rfl

theorem destsOf_eq (t : Clif.Terminator) : destsOf t = dests t := by cases t <;> rfl

theorem targetsOf_other {f : Clif.Function} {t : Clif.Terminator} (hnj : ∀ bc, t ≠ .jump bc) (nl : Nat) :
    targetsOf f t nl = edgeTargets f (dests t) nl := by
  cases t <;> first | rfl | exact absurd rfl (hnj _)

theorem edgeBlocks_other {f : Clif.Function} {B : Clif.Block} (L : BLow) (hnj : ∀ bc, B.term ≠ .jump bc)
    (hnt : B.term.isTry = false) : edgeBlocks f B L = brEdges f (dests B.term) L.targets := by
  unfold edgeBlocks
  cases h : B.term <;> rw [h] at hnt hnj <;> cases L.tl <;>
    first | rfl | exact absurd rfl (hnj _) | (simp [Clif.Terminator.isTry] at hnt)

theorem edgeBlocks_jump {f : Clif.Function} {B : Clif.Block} (L : BLow) {bc : Clif.BlockCall}
    (h : B.term = .jump bc) : edgeBlocks f B L = [] := by
  unfold edgeBlocks; rw [h]

theorem edgeBlocks_try {f : Clif.Function} {B : Clif.Block} (L : BLow) {et : Clif.ExnTable}
    (ht : IsTryWith B.term et) {T : TryLow} (hT : L.tl = some T) :
    edgeBlocks f B L = tryEdges f et.dests L.targets T.regs.1 T.regs.2 := by
  unfold edgeBlocks
  rcases ht with ⟨fn, args, h⟩ | ⟨c, args, h⟩ <;> rw [h, hT] <;> rfl

/-- What the terminator part of a block's lowering yields. -/
structure TermOut (f : Clif.Function) (ctx : Ctx) (B : Clif.Block) (k ti : Nat) (code : Array MInst)
    (ds : DState) (data : V) (d' : DState) (targets : List Label) (tl : Option TryLow) (tst' : LState)
    (nl' : Nat) : Prop where
  low : lowTerm f (termCallF ctx) (tryCallF ctx) ti B.term ds.st ds.nextLabel =
    some (data, targets, tl, tst', nl')
  st : d'.st = { tst' with emitted := #[] }
  nl : d'.nextLabel = nl'
  alias : d'.alias = ds.alias
  edges : ∀ L : BLow, L.targets = targets → L.tl = tl →
    d'.edges.toList = ds.edges.toList ++ edgeBlocks f B L
  blocks : d'.blocks = ds.blocks.push (mkVB k (code ++ (tsegOf tl tst').toArray) (paramsOf k B) (jumpArgsOf B))
  args : ArgsOk f ctx (dests B.term)
  tryArgs : ∀ et, IsTryWith B.term et → ∃ T, tl = some T ∧ ∀ i td, et.dests[i]? = some td →
    TryDestOk f ctx et.handlers.length T.regs.1.length T.regs.2.length i td
  tryLast : ∀ T, tl = some T → ∃ c, tst'.emitted.back? = some (.call c)

theorem blockD_fields (d : DState) (st : LState) (n : List Isle.RuleId) (vb : VBlock) :
    (blockD d st n vb).st = { st with emitted := #[] } ∧ (blockD d st n vb).nextLabel = d.nextLabel ∧
    (blockD d st n vb).alias = d.alias ∧ (blockD d st n vb).edges = d.edges ∧
    (blockD d st n vb).blocks = d.blocks.push vb := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem jumpArgsOf_other {B : Clif.Block} (hnj : ∀ bc, B.term ≠ .jump bc) : jumpArgsOf B = #[] := by
  unfold jumpArgsOf; split
  · rename_i bc h; exact absurd h (hnj bc)
  · rfl

theorem isTryWith_eq {t : Clif.Terminator} {et et' : Clif.ExnTable} (h : IsTryWith t et)
    (h' : IsTryWith t et') : et' = et := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rcases h' with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h' <;> rfl

theorem isTry_of {t : Clif.Terminator} {et : Clif.ExnTable} (h : IsTryWith t et) : t.isTry = true := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

theorem termOther {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {B : Clif.Block} {k stop : Nat} {code : Array MInst}
    {ds : DState} {data : V} {d' : DState} (he : ds.st.emitted = #[])
    (hnj : ∀ bc, B.term ≠ .jump bc) (hnt : B.term.isTry = false)
    (hdata : termData (abiTerm f B.term) = .ok data)
    (h : (do
      let s ← forIn (destsOf B.term) (ds, (#[] : Array Label)) (destBody f ctx)
      finishBlock ctx B k (stop - 1) code s.1 (termCtx ctx (stop - 1) data) s.2 #[] none) =
        .ok (.yield d')) :
    ∃ targets tl tst' nl', TermOut f ctx B k (stop - 1) code ds data d' targets tl tst' nl' := by
  have hreg := sp.regEq
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i s hs
  obtain ⟨d1, tg⟩ := s
  obtain ⟨ts, hedge, htg, hed, hst, hal, hbl, hargs⟩ := destLoop hreg _ ds #[] d1 tg hs
  obtain ⟨out, st, n, hrun, -, rfl⟩ := finishBlock_ok hreg h
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
    rw [hed, edgeBlocks_other L hnj hnt, hL]
  · simp [blockD, emOf, tsegOf, fixTry, jumpArgsOf_other hnj, hbl]

theorem termTry {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {B : Clif.Block} {k stop : Nat} {code : Array MInst}
    {ds : DState} {data : V} {d' : DState} {et : Clif.ExnTable}
    (ht : IsTryWith B.term et) (hdata : tryCallData f B.term = .ok data)
    (h : tryTerm f ctx B k (stop - 1) code ds (termCtx ctx (stop - 1) data) et = .ok (.yield d')) :
    ∃ targets tl tst' nl', TermOut f ctx B k (stop - 1) code ds data d' targets tl tst' nl' := by
  have hreg := sp.regEq
  unfold tryTerm at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i q hex
  obtain ⟨sig, items⟩ := q
  simp only at h
  split at h
  · rename_i retsL paysL st1 htr
    split at h
    · cases h
    split at h
    · cases h
    rename_i s hs
    obtain ⟨d1, tg⟩ := s
    obtain ⟨hall, htg, hnl, hed, hst, hal, hbl, hdest⟩ := tryLoop hreg et.dests 0 _ #[] d1 tg hs
    simp only at h
    split at h
    · rename_i t hti
      obtain ⟨out, st, n, hrun, hlast, rfl⟩ := finishBlock_ok hreg h
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
        rw [hed, edgeBlocks_try L ht hT, hL]
      · simp only [blockD, hbl, emOf, tsegOf, fixTry]
        rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> simp [jumpArgsOf, h']
      · rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> rw [h'] <;> intro b hb <;> simp [dests] at hb
      · rw [isTryWith_eq ht het']
        refine ⟨_, rfl, fun i td hi => ?_⟩
        have := hdest i td hi
        simpa using this
      · simp only [Option.some.injEq] at hT
        exact hlast t rfl
    · cases h
  · cases h

theorem termPart_ok {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (sp : CtxSpec f ctx ranges st0) {B : Clif.Block} {k stop : Nat} {code : Array MInst}
    {ds : DState} {data : V} {d' : DState} (he : ds.st.emitted = #[]) (hdata : DataOk f B.term data)
    (h : termPart f ctx B k stop code ds data = .ok (.yield d')) :
    (∀ vs, B.term = .ret vs → sretRet f = [] → sigRets f.sig = f.sig.returns) ∧
    ∃ targets tl tst' nl', TermOut f ctx B k (stop - 1) code ds data d' targets tl tst' nl' := by
  have hreg := sp.regEq
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
    obtain ⟨out, st, n, hrun, -, rfl⟩ := finishBlock_ok hreg h
    obtain ⟨tb, htb, hcnt, hrg, rfl⟩ := blockArgRegs_ok hreg hj
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
    · simp [blockD, edgeBlocks_jump L ht]
    · simp [blockD, emOf, tsegOf, fixTry, jumpArgsOf, ht]
    · rw [ht]; intro b hb
      simp only [dests, List.mem_singleton] at hb; subst hb
      exact ⟨tb, htb, fun _ => hcnt, hrg⟩
    · rw [ht] at het; rcases het with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'
  | tryCall fn args et =>
    simp only [DataOk] at h hdata
    rw [← ht] at hdata
    exact termTry sp (.inl ⟨fn, args, ht⟩) hdata h
  | tryCallIndirect c args et =>
    simp only [DataOk] at h hdata
    rw [← ht] at hdata
    exact termTry sp (.inr ⟨c, args, ht⟩) hdata h
  | brif c t e =>
    simp only [DataOk] at h hdata
    rw [← ht] at h hdata
    exact termOther sp he (by rw [ht]; intro bc h; cases h) (by rw [ht]; rfl) hdata h
  | brTable x dflt tbl =>
    simp only [DataOk] at h hdata
    rw [← ht] at h hdata
    exact termOther sp he (by rw [ht]; intro bc h; cases h) (by rw [ht]; rfl) hdata h
  | ret vs =>
    simp only [DataOk] at h hdata
    rw [← ht] at h hdata
    exact termOther sp he (by rw [ht]; intro bc h; cases h) (by rw [ht]; rfl) hdata h
  | trap c =>
    simp only [DataOk] at h hdata
    rw [← ht] at h hdata
    exact termOther sp he (by rw [ht]; intro bc h; cases h) (by rw [ht]; rfl) hdata h
  | returnCall fn args =>
    simp only [DataOk, abiTerm, termData] at hdata
    cases hdata

end Backend.Proof.Driver
