import FV.Backend.Proof.LowerSpec
import FV.Backend.Proof.TryRegs

/-!
# Completeness of `lowerCheck`: facts for `shapeOk_complete`

Construction facts the shape check needs, independent of the ISLE rules: `buildCtx`'s first
fresh vreg is `Function.freshValue` (`buildCtx_fresh`); renaming the identity-renamed code
(`pre`, `seg`, `tseg` at `id`) by `R` is the code renamed by `R`; parameters are not statement
results under SSA (`param_not_result`); the keys and members of `aliasOf`; the edge blocks of a
recorded terminator lowering carry the consecutive labels its lowering allocated
(`lowTerm_edges`), and along `lowBlocks` the states only grow (`lowBlocks_thread`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-! ## `buildCtx` -/

theorem forIn_ok_yield {α : Type} (l : List α) (g : α → Nat → Nat) (m : Nat) :
    forIn (m := Except String) l m (fun a s => Except.ok (ForInStep.yield (g a s))) =
      Except.ok (l.foldl (fun s a => g a s) m) :=
  List.forIn_pure_yield_eq_foldl (m := Except String) _ _

/-- `buildCtx`'s first fresh vreg (its `maxV`) is `Function.freshValue`. -/
theorem buildCtx_fresh {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) : st0.nextVreg = f.freshValue := by
  unfold buildCtx at hb
  simp only [bind, Except.bind, pure, Except.pure, forIn_ok_yield] at hb
  split at hb
  · cases hb
  · split at hb
    · cases hb
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hb
      obtain ⟨-, -, rfl⟩ := hb
      rfl

/-! ## Renaming the recorded code -/

theorem shape_mapRegs_id (i : MInst) : i.mapRegs id = i := by
  have ha : ∀ m : AMode, m.mapRegs id = m := fun m => by cases m <;> rfl
  have hk : ∀ k : CondBrKind, k.mapRegs id = k := fun k => by cases k <;> rfl
  cases i with
  | call info => obtain ⟨d, u, df⟩ := info; cases d <;> simp [MInst.mapRegs]
  | tryCall info ti => obtain ⟨d, u, df⟩ := info; cases d <;> simp [MInst.mapRegs]
  | _ => simp only [MInst.mapRegs, ha, hk, id] <;> simp

theorem shape_map_mapRegs_id (R : Reg → Reg) (ms : List MInst) :
    (ms.map (MInst.mapRegs id)).map (MInst.mapRegs R) = ms.map (MInst.mapRegs R) := by
  simp [List.map_map, Function.comp_def, shape_mapRegs_id]

theorem pre_map (f : Clif.Function) (R : Reg → Reg) (bi : Nat) :
    (pre f id bi).map (MInst.mapRegs R) = pre f R bi := by
  unfold pre
  split
  · simp only [List.map_cons, MInst.mapRegs, entryRegs, entryLoads, List.map_filterMap]
    congr 2
    · congr 1
      funext q
      unfold entryRegOf
      split <;> rfl
    · congr 1
      funext q
      unfold entryLoadOf
      split <;> rfl
  · rfl

theorem seg_map (f : Clif.Function) (R : Reg → Reg) (bl : List BLow) (bi j : Nat) :
    (seg f id bl bi j).map (MInst.mapRegs R) = seg f R bl bi j := by
  unfold seg
  split
  · split
    · exact shape_map_mapRegs_id R _
    · rfl
  · rfl

theorem tseg_map (R : Reg → Reg) (bl : List BLow) (bi : Nat) :
    (tseg id bl bi).map (MInst.mapRegs R) = tseg R bl bi := by
  unfold tseg
  split
  · exact shape_map_mapRegs_id R _
  · rfl

/-- The renamed instructions of a raw block are the `R`-renamed code. -/
theorem rawBlock_insts (f : Clif.Function) (R : Reg → Reg) (bl : List BLow) (bi : Nat)
    (B : Clif.Block) :
    ((rawBlock f bl bi B).insts.map (MInst.mapRegs R)).toList =
      pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten ++ tseg R bl bi := by
  simp only [rawBlock, Array.toList_map, List.map_append, pre_map, tseg_map, List.map_flatten,
    List.map_map, Function.comp_def, seg_map]

/-! ## Values -/

/-- Under SSA, a block parameter is no statement result. -/
theorem param_not_result {f : Clif.Function} (hssa : (valueDefs f).Nodup) {B B' : Clif.Block}
    (hB : B ∈ f.blocks) (hB' : B' ∈ f.blocks) {x : Nat} (hx : x ∈ B.params.map (·.1))
    (hx' : x ∈ B'.body.flatMap (·.results)) : False := by
  unfold valueDefs at hssa
  obtain ⟨hin, hpw⟩ := List.pairwise_flatMap.mp hssa
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
  obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hB'
  rcases Nat.lt_trichotomy i i' with h | rfl | h
  · exact List.pairwise_iff_getElem.mp hpw i i' hi hi' h x (List.mem_append_left _ hx) x
      (List.mem_append_right _ hx') rfl
  · have := hin _ (List.getElem_mem hi)
    exact (List.pairwise_append.mp this).2.2 x hx x hx' rfl
  · exact List.pairwise_iff_getElem.mp hpw i' i hi' hi h x (List.mem_append_right _ hx') x
      (List.mem_append_left _ hx) rfl

/-- The keys of `aliasOf` are statement results. -/
theorem aliasOf_key {f : Clif.Function} {bl : List BLow} {p : Nat × Nat} (hp : p ∈ aliasOf f bl) :
    ∃ B ∈ f.blocks, ∃ stm ∈ B.body, p.1 ∈ stm.results := by
  unfold aliasOf at hp
  obtain ⟨⟨B, L⟩, hBL, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨⟨stm, sl⟩, hss, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨⟨r, rs⟩, hrr, hp⟩ := List.mem_filterMap.mp hp
  refine ⟨B, (List.of_mem_zip hBL).1, stm, (List.of_mem_zip hss).1, ?_⟩
  have hr := (List.of_mem_zip hrr).1
  rcases rs with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · simp at hp
  · cases x <;> simp at hp
    subst hp; exact hr
  · simp at hp

/-- A statement result returned in a vreg is an alias. -/
theorem aliasOf_mem {f : Clif.Function} {bl : List BLow} {bi : Nat} {B : Clif.Block} {L : BLow}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) {j : Nat} {stm : Clif.Stmt} {sl : SLow}
    (hs : B.body[j]? = some stm) (hsl : L.sl[j]? = some sl) {r out : Nat} {c : RegClass}
    (hm : (r, [Reg.vreg out c]) ∈ stm.results.zip sl.rss) : (r, out) ∈ aliasOf f bl := by
  unfold aliasOf
  refine List.mem_flatMap.mpr ⟨(B, L), ?_, List.mem_flatMap.mpr ⟨(stm, sl), ?_, ?_⟩⟩
  · exact List.mem_of_getElem? (by rw [List.getElem?_zip_eq_some]; exact ⟨hB, hL⟩)
  · exact List.mem_of_getElem? (by rw [List.getElem?_zip_eq_some]; exact ⟨hs, hsl⟩)
  · exact List.mem_filterMap.mpr ⟨_, hm, rfl⟩

/-! ## Edge blocks -/

/-- The edge block of a branch successor (`edgeBlocks`, non-`try_call`). -/
def edgeOfBc (f : Clif.Function) (p : Clif.BlockCall × Label) : Option VBlock :=
  if p.1.args.isEmpty then none else (blockIdx? f p.1.block).map fun tl =>
    { label := p.2, insts := #[.jump tl], branchArgs := (p.1.args.map fun a => Reg.vreg a .int).toArray }

/-- The edge block of a `try_call` successor (`edgeBlocks`). -/
def edgeOfTry (f : Clif.Function) (T : TryLow) (p : Clif.TryDest × Label) : Option VBlock :=
  (blockIdx? f p.1.block).map fun tl =>
    { label := p.2, insts := #[.jump tl], branchArgs := (p.1.args.map (tryEdgeArg T.regs.1 T.regs.2)).toArray }

theorem shape_edgeBlocks_try {f : Clif.Function} {B : Clif.Block} {L : BLow} {et : Clif.ExnTable}
    {T : TryLow} (ht : IsTryWith B.term et) (hT : L.tl = some T) :
    edgeBlocks f B L = (et.dests.zip L.targets).filterMap (edgeOfTry f T) := by
  unfold edgeBlocks
  rcases ht with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h, hT] <;> rfl

theorem shape_edgeBlocks_jump {f : Clif.Function} {B : Clif.Block} {L : BLow} {bc : Clif.BlockCall}
    (ht : B.term = .jump bc) : edgeBlocks f B L = [] := by
  unfold edgeBlocks
  rw [ht]

theorem shape_edgeBlocks_other {f : Clif.Function} {B : Clif.Block} {L : BLow}
    (ht : B.term.isTry = false) (hj : ∀ bc, B.term ≠ .jump bc) :
    edgeBlocks f B L = ((dests B.term).zip L.targets).filterMap (edgeOfBc f) := by
  unfold edgeBlocks
  cases h : B.term with
  | jump bc => exact absurd h (hj bc)
  | tryCall => rw [h] at ht; cases ht
  | tryCallIndirect => rw [h] at ht; cases ht
  | _ => rfl

theorem shape_targetsOf_other {f : Clif.Function} {t : Clif.Terminator} (hj : ∀ bc, t ≠ .jump bc)
    (nl : Nat) : targetsOf f t nl = edgeTargets f (dests t) nl := by
  cases t with
  | jump bc => exact absurd rfl (hj bc)
  | _ => rfl

/-- `edgeTargets`: one label per successor, an existing target, the target itself without
arguments, the consecutive edge labels otherwise. -/
theorem edgeTargets_spec {f : Clif.Function} :
    ∀ {bcs : List Clif.BlockCall} {nl : Nat} {ts : List Label} {nl' : Nat},
      edgeTargets f bcs nl = some (ts, nl') →
      ts.length = bcs.length ∧ nl ≤ nl' ∧
      (∀ p ∈ bcs.zip ts, ∃ tl, blockIdx? f p.1.block = some tl ∧ (p.1.args = [] → p.2 = tl)) ∧
      ((bcs.zip ts).filterMap (edgeOfBc f)).map (·.label) = List.range' nl (nl' - nl) := by
  intro bcs
  induction bcs with
  | nil =>
    intro nl ts nl' h
    simp only [edgeTargets, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons bc bcs ih =>
    intro nl ts nl' h
    simp only [edgeTargets] at h
    cases hb : blockIdx? f bc.block with
    | none => rw [hb] at h; cases h
    | some tl =>
      rw [hb] at h
      simp only at h
      by_cases he : bc.args.isEmpty = true
      · simp only [he, ite_true] at h
        cases hr : edgeTargets f bcs nl with
        | none => rw [hr] at h; cases h
        | some q =>
          obtain ⟨ts0, nl0⟩ := q
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2, h3, h4⟩ := ih hr
          refine ⟨by simp [h1], h2, fun p hp => ?_, ?_⟩
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨tl, hb, fun _ => rfl⟩
            · exact h3 p hp
          · simp only [List.zip_cons_cons, List.filterMap_cons, edgeOfBc, he, ite_true]
            exact h4
      · simp only [he, ite_false, Bool.false_eq_true] at h
        cases hr : edgeTargets f bcs (nl + 1) with
        | none => rw [hr] at h; cases h
        | some q =>
          obtain ⟨ts0, nl0⟩ := q
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2, h3, h4⟩ := ih hr
          refine ⟨by simp [h1], by omega, fun p hp => ?_, ?_⟩
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨tl, hb, fun h0 => absurd (by simp [show bc.args = [] from h0]) he⟩
            · exact h3 p hp
          · simp only [List.zip_cons_cons, List.filterMap_cons, edgeOfBc, he, Bool.false_eq_true,
              ite_false, hb, Option.map_some, List.map_cons]
            rw [h4, show nl0 - nl = (nl0 - (nl + 1)) + 1 by omega, List.range'_succ]

theorem tryTargets_spec {f : Clif.Function} {ds : List Clif.TryDest} {nl : Nat} {ts : List Label}
    {nl' : Nat} (h : tryTargets f ds nl = some (ts, nl')) :
    ts = List.range' nl ds.length ∧ nl' = nl + ds.length ∧
      ∀ d ∈ ds, (blockIdx? f d.block).isSome = true := by
  unfold tryTargets at h
  split at h
  · rename_i hall
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, rfl, fun d hd => List.all_eq_true.mp hall d hd⟩
    rw [List.range'_eq_map_range]
  · cases h

theorem edgeOfTry_labels {f : Clif.Function} {T : TryLow} :
    ∀ {ds : List Clif.TryDest} {ls : List Label}, ds.length = ls.length →
      (∀ d ∈ ds, (blockIdx? f d.block).isSome = true) →
      ((ds.zip ls).filterMap (edgeOfTry f T)).map (·.label) = ls := by
  intro ds
  induction ds with
  | nil => intro ls h _; cases ls <;> simp_all
  | cons d ds ih =>
    intro ls hlen hall
    cases ls with
    | nil => cases hlen
    | cons l ls =>
      obtain ⟨tl, htl⟩ := Option.isSome_iff_exists.mp (hall d List.mem_cons_self)
      simp only [List.zip_cons_cons, List.filterMap_cons, edgeOfTry, htl, Option.map_some,
        List.map_cons]
      exact congrArg _ (ih (by simpa using hlen) fun d' hd' => hall d' (List.mem_cons_of_mem _ hd'))

theorem try_or (t : Clif.Terminator) : t.isTry = false ∨ ∃ et, IsTryWith t et := by
  cases t with
  | tryCall fn args et => exact .inr ⟨et, .inl ⟨fn, args, rfl⟩⟩
  | tryCallIndirect c args et => exact .inr ⟨et, .inr ⟨c, args, rfl⟩⟩
  | _ => exact .inl rfl

/-- A non-`try_call` terminator's labels are `targetsOf`'s. -/
theorem lowTerm_targets {f : Clif.Function} {tcall : TermCallF} {ycall : TryCallF} {ti : Nat}
    {t : Clif.Terminator} {tst : LState} {nl : Nat} {data : V} {targets : List Label}
    {tl : Option TryLow} {tst' : LState} {nl' : Nat} (ht : t.isTry = false)
    (h : lowTerm f tcall ycall ti t tst nl = some (data, targets, tl, tst', nl')) :
    targetsOf f t nl = some (targets, nl') := by
  cases t with
  | tryCall => cases ht
  | tryCallIndirect => cases ht
  | _ =>
    simp only [lowTerm] at h
    split at h
    · rename_i data0 targets0 nl0 hd htg
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact htg
      · cases h
    · cases h

/-- The edge blocks of a recorded terminator lowering carry the labels it allocated. -/
theorem lowTerm_edges {f : Clif.Function} {tcall : TermCallF} {ycall : TryCallF} {ti : Nat}
    {B : Clif.Block} {tst : LState} {nl : Nat} {data : V} {targets : List Label}
    {tl : Option TryLow} {tst' : LState} {nl' : Nat}
    (h : lowTerm f tcall ycall ti B.term tst nl = some (data, targets, tl, tst', nl'))
    {L : BLow} (hLt : L.targets = targets) (hLl : L.tl = tl) :
    (edgeBlocks f B L).map (·.label) = List.range' nl (nl' - nl) ∧ nl ≤ nl' := by
  rcases try_or B.term with ht | ⟨et, ht⟩
  · have htg := lowTerm_targets ht h
    by_cases hj : ∃ bc, B.term = .jump bc
    · obtain ⟨bc, hj⟩ := hj
      rw [shape_edgeBlocks_jump hj]
      rw [hj] at htg
      simp only [targetsOf, Option.map_eq_some_iff, Prod.mk.injEq] at htg
      obtain ⟨_, _, -, rfl⟩ := htg
      simp
    · have hj' : ∀ bc, B.term ≠ .jump bc := fun bc e => hj ⟨bc, e⟩
      rw [shape_edgeBlocks_other ht hj', hLt]
      rw [shape_targetsOf_other hj'] at htg
      obtain ⟨-, h2, -, h4⟩ := edgeTargets_spec htg
      exact ⟨h4, h2⟩
  · obtain ⟨T, hT, -, -, htt, -⟩ := (lowTerm_spec h).2 et ht
    obtain ⟨rfl, rfl, hall⟩ := tryTargets_spec htt
    rw [shape_edgeBlocks_try ht (hLl.trans hT), hLt,
      edgeOfTry_labels (by simp) hall]
    exact ⟨by simp, by omega⟩


/-! ## `try_call` -/

/-- `exnTableOpnd`'s signature is the declared one. -/
theorem exnTableOpnd_sig {f : Clif.Function} {et : Clif.ExnTable} {sig : Clif.Signature}
    {items : List (Option Nat)} (h : exnTableOpnd f et = .ok (sig, items)) :
    f.sigDecls.lookup et.sig = some sig := by
  unfold exnTableOpnd at h
  cases hs : f.sigDecls.lookup et.sig with
  | none => simp [hs] at h
  | some sig' =>
    simp only [hs] at h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rfl

theorem tryFix_ne_nil (info : TryInfo) {ms : List MInst} (h : ms ≠ []) : tryFix info ms ≠ [] := by
  unfold tryFix
  split <;> simp_all

/-- In a list whose labels are the positions, a member sits at its label. -/
theorem get_label {all : List VBlock} (h : ∀ i (hi : i < all.length), all[i].label = i)
    {eb : VBlock} (hm : eb ∈ all) : all[eb.label]? = some eb := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  rw [h i hi]
  exact List.getElem?_eq_getElem hi

/-! ## The states along `lowBlocks` -/

section Thread
variable {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF}
  (hc : ∀ ii s o s' tr, call ii s = .ok (o, s', tr) → s.nextVreg ≤ s'.nextVreg)
  (htc : ∀ ti d t ts s o s' tr, tcall ti d t ts s = .ok (o, s', tr) → s.nextVreg ≤ s'.nextVreg)
  (hyc : ∀ ti d trs ts s o s' tr, ycall ti d trs ts s = .ok (o, s', tr) → s.nextVreg ≤ s'.nextVreg)
include hc

theorem lowStmts_thread :
    ∀ {ss : List Clif.Stmt} {ii : Nat} {st : LState} {sls : List SLow} {stE : LState},
      lowStmts call ii ss st = some (sls, stE) →
      (∀ sl ∈ sls, sl.st.emitted = #[] ∧ st.nextVreg ≤ sl.st.nextVreg) ∧
        st.nextVreg ≤ stE.nextVreg := by
  intro ss
  induction ss with
  | nil =>
    intro ii st sls stE h
    simp only [lowStmts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons s ss ih =>
    intro ii st sls stE h
    simp only [lowStmts] at h
    cases hrun : call ii { st with emitted := #[] } with
    | error e => rw [hrun] at h; cases h
    | ok q =>
      obtain ⟨out, st', tr'⟩ := q
      rw [hrun] at h
      have hm := hc _ _ _ _ _ hrun
      simp only at hm
      cases hout : regsOf out with
      | none => simp only [hout] at h; cases h
      | some rss =>
        cases hrec : lowStmts call (ii + 1) ss { st' with emitted := #[] } with
        | none => simp only [hout, hrec, Option.map_none] at h; cases h
        | some q =>
          obtain ⟨sls', stE'⟩ := q
          simp only [hout, hrec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := ih hrec
          simp only at h1 h2
          refine ⟨fun sl hsl => ?_, by omega⟩
          rcases List.mem_cons.mp hsl with rfl | hsl
          · exact ⟨rfl, Nat.le_refl _⟩
          · have := h1 sl hsl; exact ⟨this.1, by omega⟩

omit hc in
include htc hyc in
theorem lowTerm_nextVreg {f : Clif.Function} {ti : Nat} {t : Clif.Terminator} {tst : LState}
    {nl : Nat} {data : V} {targets : List Label} {tl : Option TryLow} {tst' : LState} {nl' : Nat}
    (h : lowTerm f tcall ycall ti t tst nl = some (data, targets, tl, tst', nl')) :
    tst.nextVreg ≤ tst'.nextVreg := by
  rcases try_or t with ht | ⟨et, ht⟩
  · obtain ⟨-, -, out, tr, hr⟩ := (lowTerm_spec h).1 ht
    exact htc _ _ _ _ _ _ _ _ hr
  · obtain ⟨T, -, -, he, -, hr, -, out, tr, hy⟩ := (lowTerm_spec h).2 et ht
    obtain ⟨-, -, h1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) hr
    have := hyc _ _ _ _ _ _ _ _ hy
    simp only at this
    omega

include htc hyc in
/-- Along `lowBlocks`: the edge blocks carry consecutive labels from `nl`; every statement
starts with nothing emitted; the states only grow. -/
theorem lowBlocks_thread {f : Clif.Function} :
    ∀ {Bs : List Clif.Block} {start : Nat} {st : LState} {nl : Nat} {bl : List BLow},
      lowBlocks f call tcall ycall start Bs st nl = some bl →
      (∃ k, ((Bs.zip bl).flatMap fun p => edgeBlocks f p.1 p.2).map (·.label) =
        List.range' nl k) ∧
      ∀ L ∈ bl, (∀ sl ∈ L.sl, sl.st.emitted = #[] ∧ st.nextVreg ≤ sl.st.nextVreg) ∧
        st.nextVreg ≤ L.tst.nextVreg := by
  intro Bs
  induction Bs with
  | nil =>
    intro start st nl bl h
    simp only [lowBlocks, Option.some.injEq] at h
    subst h
    exact ⟨⟨0, by simp⟩, fun L h => by simp at h⟩
  | cons B Bs ih =>
    intro start st nl bl h
    simp only [lowBlocks] at h
    cases hstm : lowStmts call start B.body st with
    | none => rw [hstm] at h; cases h
    | some q =>
      obtain ⟨sls, stE⟩ := q
      rw [hstm] at h
      simp only at h
      cases hterm : lowTerm f tcall ycall (start + B.body.length) B.term { stE with emitted := #[] } nl with
      | none => rw [hterm] at h; cases h
      | some q =>
        obtain ⟨data, targets, tl, tst', nl'⟩ := q
        rw [hterm] at h
        simp only at h
        cases hrec : lowBlocks f call tcall ycall (start + B.body.length + 1) Bs
            { tst' with emitted := #[] } nl' with
        | none => rw [hrec] at h; cases h
        | some bl' =>
          rw [hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨⟨k, hk⟩, hL⟩ := ih hrec
          obtain ⟨hs1, hs2⟩ := lowStmts_thread hc hstm
          have ht := lowTerm_nextVreg htc hyc hterm
          simp only at ht
          obtain ⟨he1, he2⟩ := lowTerm_edges hterm (L := ⟨start, sls, data, targets,
            { stE with emitted := #[] }, tst', tl⟩) rfl rfl
          refine ⟨⟨nl' - nl + k, ?_⟩, fun L hL' => ?_⟩
          · simp only [List.zip_cons_cons, List.flatMap_cons, List.map_append, he1, hk]
            have := List.range'_append (s := nl) (m := nl' - nl) (n := k) (step := 1)
            rwa [show nl + 1 * (nl' - nl) = nl' by omega] at this
          · rcases List.mem_cons.mp hL' with rfl | hL'
            · exact ⟨hs1, by simp only; omega⟩
            · obtain ⟨h1, h2⟩ := hL L hL'
              simp only at h1 h2
              exact ⟨fun sl hsl => ⟨(h1 sl hsl).1, by have := (h1 sl hsl).2; omega⟩, by omega⟩

end Thread

end Backend.Proof.Driver
