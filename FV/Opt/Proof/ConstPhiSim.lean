import FV.Opt.ConstPhi
import FV.Opt.Proof.GvnEditX
import FV.Opt.Proof.UnreachableX

/-!
# Constant-phi removal is sound (#990): `Opt.ConstPhi.cpOk_simX`

`cpOk f sol = true → FunSimX f (apply f sol)`: the rewrite of an accepted solution simulates `f`,
`call_indirect` and `try_call`/`try_call_indirect` included, and so `run f` simulates `f` for
every `f` (`run_simX`). The solver is not trusted: the proof uses only the facts `cpOk` checks
(`CpFacts`).

The frames are related at the same program point (`CRel`): the target executes the source's
statements and terminator renamed by the solution (`rename m`), its edges drop the arguments at
the removed positions (`filterTerm`), and for every value `v` available in the source
(`Opt.Avail`, by the run-time invariant `Opt.Inv` of the well-formed `f`) the target holds at
`rename m v` the source's value of `v`. For a kept value this is equality; for a removed
parameter `p` it says that `p` holds the value of its solution `v`. Each step is matched by one
step. Statements read equal operands and bind the same results; a result is never the solution
of an available removed parameter (`rename_not_result`). On an edge, a kept parameter receives
the same argument; a removed parameter receives an argument that renames to its solution, whose
value the target holds; the solution's definition strictly dominates the parameter's block, so
it is not a parameter of the destination (`rename_not_param`). A `try_call` binds its results
at each side's fresh value (the windows of `Opt.IsSimW`), above every value the relation reads.
-/

namespace Opt.ConstPhi

open Clif Opt

/-! ## Flags -/

theorem filt_map {α β : Type} (h : α → β) :
    ∀ (ks : List Bool) (xs : List α), filt ks (xs.map h) = (filt ks xs).map h
  | b :: bs, x :: xs => by cases b <;> simp [filt, filt_map h bs xs]
  | [], xs => rfl
  | _ :: _, [] => rfl

theorem filt_filter {α β : Type} (P : α → Bool) (h : α → β) :
    ∀ (l : List α), filt (l.map P) (l.map h) = (l.filter P).map h
  | [] => rfl
  | a :: l => by cases hp : P a <;> simp [filt, hp, filt_filter P h l]

theorem length_filt_filter {α β : Type} (P : α → Bool) :
    ∀ (xs : List α) (vs : List β), xs.length = vs.length →
      (filt (xs.map P) vs).length = (xs.filter P).length
  | [], [], _ => rfl
  | x :: xs, v :: vs, h => by
    cases hp : P x <;>
      simp [filt, hp, length_filt_filter P xs vs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem getMany_filt {fr : Frame} :
    ∀ (ks : List Bool) (xs : List ValueId) {vs : List Val}, fr.getMany xs = .ok vs →
      fr.getMany (filt ks xs) = .ok (filt ks vs)
  | [], xs, vs, h => h
  | _ :: _, [], vs, h => by
    simp only [Frame.getMany] at h; cases h; rfl
  | b :: bs, x :: xs, vs, h => by
    simp only [Frame.getMany, Res.bind_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨v, hv, vs', hvs, rfl⟩ := h
    have ih := getMany_filt bs xs hvs
    cases b
    · simpa [filt] using ih
    · simp only [filt, ite_true, Frame.getMany, hv, ih]; rfl

/-- Binding the kept parameters to the kept arguments: each kept parameter gets its value. -/
theorem setMany_filter_eq (P : ValueId → Bool) :
    ∀ (xs : List ValueId) (vs : List Val) (r r' r1 r1' : Regs), r.setMany xs vs = some r1 →
      r'.setMany (xs.filter P) (filt (xs.map P) vs) = some r1' →
      ∀ y ∈ xs, P y = true → r1' y = r1 y
  | [], _, _, _, _, _, _, _, y, hy, _ => by cases hy
  | _ :: _, [], _, _, _, _, h, _, _, _, _ => by simp [Regs.setMany] at h
  | x :: xs, v :: vs, r, r', r1, r1', h1, h2, y, hy, hp => by
    simp only [Regs.setMany_cons] at h1
    by_cases hx : P x = true
    · simp only [List.map_cons, hx, List.filter_cons_of_pos, filt, ite_true,
        Regs.setMany_cons] at h2
      by_cases hyx : y ∈ xs
      · exact setMany_filter_eq P xs vs _ _ _ _ h1 h2 y hyx hp
      · have hyx' : y ∉ xs.filter P := fun hm => hyx (List.mem_filter.1 hm).1
        have : y = x := by simpa [hyx] using hy
        subst this
        rw [((setMany_spec h1).2 y).1 hyx, ((setMany_spec h2).2 y).1 hyx']
        simp
    · have hx' : P x = false := by simpa using hx
      simp only [List.map_cons, List.filter_cons, hx', filt, Bool.false_eq_true,
        ite_false] at h2
      have hyx : y ∈ xs := by
        rcases List.mem_cons.1 hy with rfl | h
        · rw [hp] at hx'; cases hx'
        · exact h
      exact setMany_filter_eq P xs vs _ _ _ _ h1 h2 y hyx hp

theorem resolve_filt (b : ValueId) :
    ∀ (ks : List Bool) (l : List TryArg) {xs : List ValueId}, resolve b l = .ok xs →
      resolve b (filt ks l) = .ok (filt ks xs)
  | [], l, xs, h => h
  | _ :: _, [], xs, h => by simp only [resolve] at h; cases h; rfl
  | k :: ks, a :: l, xs, h => by
    simp only [resolve, Res.bind_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    have ih := resolve_filt b ks l hxs
    cases k
    · simpa [filt] using ih
    · simp only [filt, ite_true, resolve, hx, ih]; rfl

theorem resolve_val (b : ValueId) :
    ∀ (l : List TryArg) {xs : List ValueId}, resolve b l = .ok xs →
      ∀ (n : Nat) x, l[n]? = some (TryArg.val x) → xs[n]? = some x
  | [], xs, _, n, x, hn => by simp at hn
  | a :: l, xs, h, n, x, hn => by
    simp only [resolve, Res.bind_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨y, hy, xs', hxs, rfl⟩ := h
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      simp only [Res.pure_eq_ok] at hy
      simp [hy]
    | succ n => simpa using resolve_val b l hxs n x (by simpa using hn)

theorem tryNormal_filter (k : Std.HashMap BlockId (List Bool)) {et : ExnTable} {b : ValueId}
    {bc : BlockCall} (h : tryNormal et b = .ok bc) :
    tryNormal (filterEt k et) b = .ok { bc with args := filt (keepOf k bc.block) bc.args } := by
  rw [tryNormal_eq] at h ⊢
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨args, ha, rfl⟩ := h
  simp only [filterEt, filterTD, resolve_filt b _ _ ha, Res.ok_bind]
  rfl

/-! ## Maps -/

theorem solMap_get_aux (x v : ValueId) :
    ∀ (l : List (ValueId × ValueId)) (m : Std.HashMap ValueId ValueId),
      (l.foldl (fun m (p : ValueId × ValueId) => m.insert p.1 p.2) m)[x]? = some v →
        m[x]? = some v ∨ (x, v) ∈ l
  | [], m, h => .inl h
  | q :: l, m, h => by
    rcases solMap_get_aux x v l _ h with h | h
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i he
        simp only [beq_iff_eq] at he
        cases h; subst he; exact .inr (by simp)
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

theorem solMap_get {sol : List (ValueId × ValueId)} {x v : ValueId}
    (h : (solMap sol)[x]? = some v) : (x, v) ∈ sol := by
  rcases solMap_get_aux x v sol {} h with h | h
  · simp at h
  · exact h

theorem rename_of_not {m : Std.HashMap ValueId ValueId} {x : ValueId} (h : m.contains x = false) :
    rename m x = x := by
  rw [Std.HashMap.contains_eq_isSome_getElem?] at h
  simp only [rename]
  cases hx : m[x]? with
  | none => rfl
  | some _ => rw [hx] at h; cases h

theorem get_of_contains {m : Std.HashMap ValueId ValueId} {x : ValueId} (h : m.contains x = true) :
    m[x]? = some (rename m x) := by
  rw [Std.HashMap.contains_eq_isSome_getElem?] at h
  simp only [rename]
  cases hx : m[x]? with
  | none => rw [hx] at h; cases h
  | some _ => rfl

theorem keepMap_aux (m : Std.HashMap ValueId ValueId) (id : BlockId) :
    ∀ (l : List Block) (acc : Std.HashMap BlockId (List Bool)),
      (l.foldl (fun acc b => if acc.contains b.id then acc
        else acc.insert b.id (b.params.map fun p => !m.contains p.1)) acc)[id]? =
      if acc.contains id then acc[id]? else
        (l.find? (·.id == id)).map (fun b => b.params.map fun p => !m.contains p.1)
  | [], acc => by
    simp only [List.foldl_nil, List.find?_nil, Option.map_none]
    split
    · rfl
    · rename_i h
      rw [Std.HashMap.contains_eq_isSome_getElem?] at h
      cases hx : acc[id]? with
      | none => rfl
      | some _ => rw [hx] at h; simp at h
  | b :: l, acc => by
    simp only [List.foldl_cons]
    rw [keepMap_aux m id l]
    by_cases hb : acc.contains b.id = true
    · simp only [hb, ite_true, List.find?_cons]
      by_cases he : b.id = id
      · subst he; simp [hb]
      · have hbe : (b.id == id) = false := by simp [he]
        simp [hbe]
    · simp only [hb, Bool.false_eq_true, ite_false, List.find?_cons, Std.HashMap.contains_insert,
        Std.HashMap.getElem?_insert]
      by_cases he : b.id = id
      · subst he; simp [hb]
      · have hbe : (b.id == id) = false := by simp [he]
        simp [hbe]

theorem keepMap_get (m : Std.HashMap ValueId ValueId) (f : Function) (id : BlockId) :
    (keepMap m f)[id]? = (f.block? id).map (fun b => b.params.map fun p => !m.contains p.1) := by
  unfold keepMap
  rw [keepMap_aux]
  simp [Function.block?]

theorem keepOf_block {m : Std.HashMap ValueId ValueId} {f : Function} {id : BlockId} {b : Block}
    (h : f.block? id = some b) :
    keepOf (keepMap m f) id = b.params.map fun p => !m.contains p.1 := by
  simp [keepOf, keepMap_get, h]

/-! ## The rewritten function -/

/-- `apply` with the solution as a map. -/
def cpFun (m : Std.HashMap ValueId ValueId) (f : Function) : Function :=
  { f with blocks := f.blocks.map (cpBlock m (keepMap m f)) }

theorem apply_eq (f : Function) (sol : List (ValueId × ValueId)) :
    apply f sol = cpFun (solMap sol) f := rfl

section
variable (m : Std.HashMap ValueId ValueId) (f : Function)

theorem cpFun_block? (id : BlockId) :
    (cpFun m f).block? id = (f.block? id).map (cpBlock m (keepMap m f)) := by
  simp only [cpFun, Function.block?, List.find?_map]
  rfl

theorem cpFun_entry? : (cpFun m f).entry? = f.entry?.map (cpBlock m (keepMap m f)) := by
  simp [cpFun, Function.entry?]

theorem cpFun_blocks_get (i : Nat) :
    (cpFun m f).blocks[i]? = f.blocks[i]?.map (cpBlock m (keepMap m f)) := by
  simp [cpFun]

end

theorem renStmt_results (σ : ValueId → ValueId) (s : Stmt) : (renStmt σ s).results = s.results := rfl

/-- A value `f` defines and the solution keeps is below the rewritten function's fresh value. -/
theorem lt_cpFun_freshValue {m : Std.HashMap ValueId ValueId} {f : Function} {v : ValueId}
    {s : Nat × Nat} (hd : (v, s) ∈ defSites f) (hk : m.contains v = false) :
    v < (cpFun m f).freshValue := by
  obtain ⟨i, b, hb, hp⟩ := mem_defSites.1 hd
  have hbm : cpBlock m (keepMap m f) b ∈ (cpFun m f).blocks :=
    List.mem_map_of_mem (List.mem_of_getElem? hb)
  rcases hp with ⟨p, hp, hpv, -⟩ | ⟨j, st, hst, hv, -⟩
  · have := (lt_freshValue hbm).1 p (List.mem_filter.2 ⟨hp, by simp [hpv, hk]⟩)
    rwa [hpv] at this
  · exact (lt_freshValue hbm).2 (renStmt (rename m) st)
      (List.mem_map_of_mem (List.mem_of_getElem? hst)) v (by rw [renStmt_results]; exact hv)

/-! ## What `cpOk` establishes -/

/-- The facts of `cpOk` the proof uses. -/
structure CpFacts (m : Std.HashMap ValueId ValueId) (f : Function) (D : WfData) : Prop where
  wf : Wf f D
  key : ∀ x, m.contains x = true → ∃ bp dv t, D.dm x = some (bp, 0) ∧ bp ≠ 0 ∧
    m.contains (rename m x) = false ∧ D.dm (rename m x) = some (dv, t) ∧ dv ≠ bp ∧
    Anc D.idom dv bp
  edge : ∀ (i : Nat) (b : Block), f.blocks[i]? = some b → ∀ e ∈ edges b.term, ∀ (j : Nat) (db : Block),
    D.index e.1 = some j → f.blocks[j]? = some db → db.params.length = e.2.length ∧
    ∀ (n : Nat) p a, db.params[n]? = some p → e.2[n]? = some a → m.contains p.1 = true →
      ∃ x, a = some x ∧ rename m x = rename m p.1

theorem cpOk_facts {f : Function} {sol : List (ValueId × ValueId)} (h : cpOk f sol = true) :
    ∃ fi, check f = .ok fi ∧ CpFacts (solMap sol) f (wfData f fi) := by
  unfold cpOk at h
  split at h
  · cases h
  rename_i fi hfi
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hkeys, hedges⟩, -⟩, -⟩ := h
  refine ⟨fi, hfi, wf_of_check hfi, fun x hx => ?_, fun i b hb e he j db hj hdb => ?_⟩
  · have hmem := solMap_get (get_of_contains hx)
    simp only [keysOk, Bool.and_eq_true, List.all_eq_true] at hkeys
    have h1 := hkeys.2 _ hmem
    simp only [Bool.not_eq_true'] at h1
    obtain ⟨hnc, h2⟩ := h1
    split at h2
    · rename_i bp dv t hp hv
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
      obtain ⟨⟨hbp, hdv⟩, ha⟩ := h2
      exact ⟨bp, dv, t, by simpa [wfData, Std.HashMap.get?_eq_getElem?] using hp, hbp, hnc,
        by simpa [wfData, Std.HashMap.get?_eq_getElem?] using hv, hdv, ancB_sound ha⟩
    · cases h2
  · simp only [edgesOk, List.all_eq_true] at hedges
    have h1 := hedges b (List.mem_of_getElem? hb) e he
    have hj' : fi.cfg.index[e.1]? = some j := by
      simpa [wfData, Std.HashMap.get?_eq_getElem?] using hj
    obtain ⟨dst, args⟩ := e
    simp only at h1 hj' ⊢
    simp only [hj', hdb, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
    obtain ⟨hlen, hall⟩ := h1
    refine ⟨hlen, fun n p a hp ha hc => ?_⟩
    have hz : (p, a) ∈ db.params.zip args :=
      List.mem_iff_getElem?.2 ⟨n, by simp [List.getElem?_zip_eq_some, hp, ha]⟩
    have h2 := hall _ hz
    simp only [hc, Bool.not_true, Bool.false_or] at h2
    split at h2
    · rename_i x
      exact ⟨x, rfl, by simpa using h2⟩
    · cases h2

/-! ## Where renamed values are defined -/

section
variable {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} (hF : CpFacts m f D)
include hF

/-- A statement result is not a removed parameter. -/
theorem rename_result {bi k : Nat} {b : Block} {st : Stmt} {v : ValueId}
    (hb : f.blocks[bi]? = some b) (hst : b.body[k]? = some st) (hv : v ∈ st.results) :
    rename m v = v := by
  cases hc : m.contains v
  · exact rename_of_not hc
  · obtain ⟨bp, -, -, hp, -⟩ := hF.key v hc
    rw [site_result hF.wf hb hst hv] at hp
    simp at hp

/-- The renaming of an available value is not a result of the statement at that point: a
removed parameter's solution is defined in a strict dominator of the parameter's block. -/
theorem rename_not_result {bi k : Nat} {b : Block} {st : Stmt} {v : ValueId}
    (hb : f.blocks[bi]? = some b) (hst : b.body[k]? = some st) (hv : Avail D bi k v) :
    rename m v ∉ st.results := by
  cases hc : m.contains v
  · rw [rename_of_not hc]; exact avail_not_result hF.wf hb hst hv
  · obtain ⟨bp, dv, t, hp, -, -, hd, hne, ha⟩ := hF.key v hc
    intro hr
    rw [site_result hF.wf hb hst hr] at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    obtain ⟨d0, t0, hv0, hva⟩ := hv
    rw [hp] at hv0
    simp only [Option.some.injEq, Prod.mk.injEq] at hv0
    obtain ⟨rfl, rfl⟩ := hv0
    rcases hva with ⟨he, -⟩ | ⟨hne2, ha2⟩
    · exact hne he.symm
    · exact hne2 (Anc.antisymm hF.wf.rank ha2 ha)

/-- The renaming of a value available at the start of block `j`, unless it is a kept parameter
of `j`, is not a parameter of `j`. -/
theorem rename_not_param {j : Nat} {b2 : Block} {v : ValueId} (hj : f.blocks[j]? = some b2)
    (hv : Avail D j 0 v) (hk : D.dm v = some (j, 0) → m.contains v = true) :
    rename m v ∉ b2.params.map (·.1) := by
  intro hm
  obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
  have hsite := site_param hF.wf hj hp
  rw [hpv] at hsite
  cases hc : m.contains v
  · rw [rename_of_not hc] at hsite
    rw [hk hsite] at hc; cases hc
  · obtain ⟨bp, dv, t, hp0, -, -, hd, hne, ha⟩ := hF.key v hc
    rw [hsite] at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    obtain ⟨d0, t0, hv0, hva⟩ := hv
    rw [hp0] at hv0
    simp only [Option.some.injEq, Prod.mk.injEq] at hv0
    obtain ⟨rfl, rfl⟩ := hv0
    rcases hva with ⟨he, -⟩ | ⟨hne2, ha2⟩
    · exact hne he.symm
    · exact hne2 (Anc.antisymm hF.wf.rank ha2 ha)

/-- The renaming of an available value is below the rewritten function's fresh value. -/
theorem rename_lt {bi k : Nat} {v : ValueId} (hv : Avail D bi k v) :
    rename m v < (cpFun m f).freshValue := by
  obtain ⟨d, t, hd, -⟩ := hv
  cases hc : m.contains v
  · rw [rename_of_not hc]
    exact lt_cpFun_freshValue (hF.wf.sitesRev _ _ hd) hc
  · obtain ⟨-, dv, t', -, -, hnc, hd', -⟩ := hF.key v hc
    exact lt_cpFun_freshValue (hF.wf.sitesRev _ _ hd') hnc

end

/-! ## The relation -/

/-- Frames at the same program point of block `bi` (module doc). -/
structure CRel (m : Std.HashMap ValueId ValueId) (f : Function) (D : WfData)
    (syms : String → Option Nat) (fr fr' : Frame) (bi k : Nat) : Prop where
  inv : Inv f D syms fr bi k
  func : fr'.func = cpFun m f
  body : fr'.body = fr.body.map (renStmt (rename m))
  term : fr'.term = filterTerm (keepMap m f) (mapTerm (rename m) fr.term)
  slots : fr'.slots = fr.slots
  agree : ∀ v, Avail D bi k v → fr'.regs (rename m v) = fr.regs v

/-- The frame relation of the simulation. -/
def CR (m : Std.HashMap ValueId ValueId) (f : Function) (D : WfData) (syms : String → Option Nat)
    (fr fr' : Frame) : Prop :=
  ∃ bi k, CRel m f D syms fr fr' bi k

theorem CRel.globals {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} {syms : String → Option Nat}
    {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k) :
    fr'.func.globals = fr.func.globals := by
  rw [h.func, h.inv.func]; rfl

theorem CRel.externs {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} {syms : String → Option Nat}
    {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k) :
    fr'.func.externs = fr.func.externs := by
  rw [h.func, h.inv.func]; rfl

theorem CRel.sigDecls {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} {syms : String → Option Nat}
    {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k) :
    fr'.func.sigDecls = fr.func.sigDecls := by
  rw [h.func, h.inv.func]; rfl

theorem CRel.sig {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} {syms : String → Option Nat}
    {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k) :
    fr'.func.sig = fr.func.sig := by
  rw [h.func, h.inv.func]; rfl

section
variable {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} (hF : CpFacts m f D)
  {syms : String → Option Nat}
include hF

/-- A statement other than a call steps in lock-step. -/
theorem CRel.stmt {fr fr' : Frame} {bi k : Nat} {mm : Mem} {s : Stmt} {ss : List Stmt}
    (h : CRel m f D syms fr fr' bi k) (hm : mm.symbols = syms) (hs : fr.body = s :: ss)
    (hnc : ∀ fn args, s.inst ≠ .call fn args) :
    (∀ fr1 m1, lstep fr mm = .next fr1 m1 → ∃ fr1', lstep fr' mm = .next fr1' m1 ∧
      CRel m f D syms fr1 fr1' bi (k + 1)) ∧
    (∀ c, lstep fr mm = .trap c → lstep fr' mm = .trap c) := by
  obtain ⟨b, hbi, hbody, -, -⟩ := h.inv.block
  have hs0 := hs
  rw [hbody] at hs
  obtain ⟨hsk, -, -⟩ := drop_eq_cons hs
  have ht : fr'.body = renStmt (rename m) s :: ss.map (renStmt (rename m)) := by
    rw [h.body, hs0]; rfl
  have hops : ∀ x ∈ operands s.inst, fr'.regs (rename m x) = fr.regs x :=
    fun x hx => h.agree x (hF.wf.uses bi b hbi k s hsk x hx)
  have hev := evalInst_rename (mem := mm) h.globals h.externs h.slots hops
  have hnc' := mapOperands_not_call (σ := rename m) hnc
  rw [lstep_inst hs0 hnc, lstep_inst ht hnc']
  refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_⟩
  · cases he : evalInst fr mm s.inst with
    | trap c => rw [he] at hl; cases hl
    | stuck msg => rw [he] at hl; cases hl
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl
      simp only [LRes.ofRes] at hl
      split at hl
      · rename_i regs hset
        cases hl
        have he' := Res.norm_eq_ok hev he
        obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vals)
          (setMany_spec hset).1
        simp only [renStmt] at he' ⊢
        rw [he']
        simp only [LRes.ofRes, hset']
        refine ⟨_, rfl, ⟨?_, h.func, rfl, h.term, h.slots, ?_⟩⟩
        · exact Inv.results hF.wf h.inv hs0 (fun ts0 h0 => evalInst_types he h0)
            (fun hp => by
              obtain ⟨-, a, rfl, ha⟩ := evalInst_pure hp he
              exact ⟨a, rfl, by rw [evalNode_mem (m := mm) hp (by rw [hm]; rfl)]; exact ha⟩) hset
        · intro v hv
          rcases avail_succ hF.wf hbi hsk hv with hr | hv'
          · rw [rename_result hF hbi hsk hr]
            exact (setMany_same hset hset' v hr).symm
          · show regs' (rename m v) = regs v
            rw [((setMany_spec hset').2 _).1 (rename_not_result hF hbi hsk hv'),
              ((setMany_spec hset).2 _).1 (avail_not_result hF.wf hbi hsk hv'), h.agree v hv']
      · cases hl
  · cases he : evalInst fr mm s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' =>
      rw [he] at hl; cases hl
      simp only [renStmt]
      rw [Res.norm_eq_trap hev he]; rfl

/-- A call: the same callee and arguments; the continuations are related. -/
theorem CRel.call {fr fr' : Frame} {bi k : Nat} {mm : Mem} {ext : ExtFunc} {vals : List Val}
    {rs : List ValueId} {rest : List Stmt} (h : CRel m f D syms fr fr' bi k)
    (hl : lstep fr mm = .call ext vals rs rest) :
    lstep fr' mm = .call ext vals rs (rest.map (renStmt (rename m))) ∧
      Cont (CR m f D syms) { fr with body := rest } rs
        { fr' with body := rest.map (renStmt (rename m)) } rs (AbiParam.tys ext.sig.returns) := by
  obtain ⟨s, fn, args, hs0, hc, hrs, hca⟩ := lstep_call_inv hl
  subst hrs
  obtain ⟨b, hbi, hbody, -, -⟩ := h.inv.block
  have hs := hs0
  rw [hbody] at hs
  obtain ⟨hsk, -, -⟩ := drop_eq_cons hs
  have ht : fr'.body = renStmt (rename m) s :: rest.map (renStmt (rename m)) := by
    rw [h.body, hs0]; rfl
  have hops : ∀ x ∈ operands s.inst, fr'.regs (rename m x) = fr.regs x :=
    fun x hx => h.agree x (hF.wf.uses bi b hbi k s hsk x hx)
  have hca' := Res.norm_eq_ok (callArgs_rename (σ := rename m) (fr := fr) (fr' := fr') (fn := fn)
    h.externs (fun x hx => hops x (by rw [hc]; exact hx))) hca
  have htc : (renStmt (rename m) s).inst = .call fn (args.map (rename m)) := by
    simp [renStmt, hc, mapOperands]
  refine ⟨by rw [lstep_call ht htc, hca']; rfl, ?_⟩
  intro vs regs hty hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vs)
    (setMany_spec hset).1
  refine ⟨regs', hset', bi, k + 1, ?_, h.func, rfl, h.term, h.slots, ?_⟩
  · have hext : sigOf f fn = some ext.sig := by
      simp only [callArgs, Res.bind_eq_ok, Res.ofOption_eq_ok] at hca
      obtain ⟨e, he, _, _, _, _, hpe⟩ := hca
      simp only [Res.pure_eq_ok, Prod.mk.injEq] at hpe
      obtain ⟨rfl, -⟩ := hpe
      rw [h.inv.func] at he
      simp only [sigOf]
      rw [show f.externs.lookup fn = f.extern? fn from rfl, he]; rfl
    refine Inv.results (fr := fr) (st := s) (rest := rest) hF.wf h.inv hs0 (fun ts0 h0 => ?_)
      (fun hp => by rw [hc] at hp; cases hp) hset
    rw [hc, Inst.resultTypes, hext] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    rw [← h0, hty]; rfl
  · intro v hv
    rcases avail_succ hF.wf hbi hsk hv with hr | hv'
    · rw [rename_result hF hbi hsk hr]
      exact (setMany_same hset hset' v hr).symm
    · show regs' (rename m v) = regs v
      rw [((setMany_spec hset').2 _).1 (rename_not_result hF hbi hsk hv'),
        ((setMany_spec hset).2 _).1 (avail_not_result hF.wf hbi hsk hv'), h.agree v hv']

end

/-! ## Edges -/

theorem inv_atEnd {f : Function} {D : WfData} {syms : String → Option Nat} {fr : Frame} {bi k : Nat} (h : Inv f D syms fr bi k) (hs : fr.body = []) :
    ∃ b, f.blocks[bi]? = some b ∧ k = b.body.length ∧ fr.term = b.term := by
  obtain ⟨b, hb, hbody, hterm, hk⟩ := h.block
  rw [hs] at hbody
  have := congrArg List.length hbody
  simp at this
  exact ⟨b, hb, by omega, hterm⟩


section
variable {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} (hF : CpFacts m f D)
  {syms : String → Option Nat}
include hF

/-- **Branching**: given the argument values of the source edge, the target edge's arguments
are the kept ones, and each removed position's argument is the value the target holds at its
parameter's renaming, both frames enter the destination at related points. -/
theorem enterAt {fr fr' fr1 : Frame} {bi k : Nat} (hinv : Inv f D syms fr bi k)
    (hs : fr.body = []) (hfunc : fr'.func = cpFun m f) (hsl : fr'.slots = fr.slots)
    (hagree : ∀ v, Avail D bi k v → fr'.regs (rename m v) = fr.regs v)
    {bc bc' : BlockCall} (hsucc : bc.block ∈ termSuccs fr.term) (he : enterBlock fr bc = .ok fr1)
    (hblk : bc'.block = bc.block)
    (hargs : ∀ vs, fr.getMany bc.args = .ok vs →
      fr'.getMany bc'.args = .ok (filt (keepOf (keepMap m f) bc.block) vs) ∧
      ∀ b2, f.block? bc.block = some b2 → ∀ (n : Nat) p, b2.params[n]? = some p →
        m.contains p.1 = true → fr'.regs (rename m p.1) = vs[n]?) :
    ∃ fr1', enterBlock fr' bc' = .ok fr1' ∧ CR m f D syms fr1 fr1' := by
  obtain ⟨b, hbi, hk, hterm⟩ := inv_atEnd hinv hs
  subst hk
  obtain ⟨j, b2, hj, hb2, hinv1⟩ := Inv.enter hF.wf hinv hs hsucc he
  obtain ⟨b2x, args, regs, hb2x, hga, hty, hset, rfl⟩ := enterBlock_ok he
  rw [hinv.func, hb2] at hb2x; cases hb2x
  obtain ⟨hga', hrem⟩ := hargs args hga
  rw [keepOf_block hb2] at hga'
  let P : ValueId → Bool := fun y => !m.contains y
  have hgb : fr'.func.block? bc'.block = some (cpBlock m (keepMap m f) b2) := by
    rw [hfunc, hblk, cpFun_block?, hb2]; rfl
  have hxsf : (cpBlock m (keepMap m f) b2).params.map (·.1) = (b2.params.map (·.1)).filter P := by
    simp only [cpBlock, List.filter_map]; rfl
  have hks : b2.params.map (fun p => !m.contains p.1) = (b2.params.map (·.1)).map P := by
    rw [List.map_map]; rfl
  have hty' : (filt (b2.params.map fun p => !m.contains p.1) args).map (·.ty) =
      (cpBlock m (keepMap m f) b2).params.map (·.2) := by
    rw [← filt_map, hty, filt_filter]; rfl
  have hlen := (setMany_spec hset).1
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs)
    (xs := (cpBlock m (keepMap m f) b2).params.map (·.1))
    (vs := filt (b2.params.map fun p => !m.contains p.1) args) (by
      rw [hxsf, hks, length_filt_filter P _ _ hlen])
  have he' := enterBlock_of hgb hga' hty' hset'
  refine ⟨_, he', j, 0, hinv1, hfunc, rfl, rfl, hsl, fun v hv => ?_⟩
  show regs' (rename m v) = regs v
  have hbid : b2.id = bc.block := by obtain ⟨_, _, h0⟩ := block?_index hF.wf hb2; exact h0
  have hnot : ∀ y, y ∈ (cpBlock m (keepMap m f) b2).params.map (·.1) → y ∈ b2.params.map (·.1) := by
    intro y hy
    obtain ⟨p', hp', he'⟩ := List.mem_map.1 hy
    exact List.mem_map.2 ⟨p', (List.mem_filter.1 hp').1, he'⟩
  by_cases hdv : D.dm v = some (j, 0)
  · obtain ⟨b4, p, hb4, hp, hpv⟩ := site_param' hF.wf hdv
    rw [hj] at hb4; cases hb4
    have hvm : v ∈ b2.params.map (·.1) := List.mem_map.2 ⟨p, hp, hpv⟩
    cases hc : m.contains v
    · rw [rename_of_not hc]
      rw [hxsf, hks] at hset'
      exact setMany_filter_eq P _ _ _ _ _ _ hset hset' v hvm (by simp [P, hc])
    · obtain ⟨n, hn, hrv⟩ := ((setMany_spec hset).2 v).2 hvm
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
      obtain ⟨q, hq, hqv⟩ := hn
      subst hqv
      rw [((setMany_spec hset').2 _).1 (fun hm => rename_not_param hF hj hv (fun _ => hc) (hnot _ hm)),
        hrem b2 hb2 n q hq hc, hrv]
  · have hvp := avail_pred hF.wf hbi hj (by rw [hbid, ← hterm]; exact hsucc) hv hdv
    have hn2 : v ∉ b2.params.map (·.1) := by
      intro hm
      obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
      exact hdv (by rw [← hpv]; exact site_param hF.wf hj hp)
    rw [((setMany_spec hset').2 _).1 (fun hm => rename_not_param hF hj hv
        (fun h => absurd h hdv) (hnot _ hm)),
      ((setMany_spec hset).2 _).1 hn2, hagree v hvp]

/-- The values the terminator reads hold in the target at their renamings. -/
theorem CRel.termOps {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) : ∀ x ∈ termOperands fr.term, fr'.regs (rename m x) = fr.regs x ∧
      x < f.freshValue ∧ rename m x < (cpFun m f).freshValue := by
  obtain ⟨b, hbi, hk, hterm⟩ := inv_atEnd h.inv hs
  subst hk
  intro x hx
  rw [hterm] at hx
  have hav := hF.wf.termUses bi b hbi x hx
  exact ⟨h.agree x hav, avail_lt hF.wf hav, rename_lt hF hav⟩

/-- The arguments of a plain edge (`jump`, `brif`, `br_table`). -/
theorem CRel.plainArgs {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) {bc : BlockCall} (hedge : (bc.block, bc.args.map some) ∈ edges fr.term)
    (hops : ∀ x ∈ bc.args, x ∈ termOperands fr.term) :
    ∀ vs, fr.getMany bc.args = .ok vs →
      fr'.getMany (filterBC (keepMap m f) (mapBlockCall (rename m) bc)).args =
        .ok (filt (keepOf (keepMap m f) bc.block) vs) ∧
      ∀ b2, f.block? bc.block = some b2 → ∀ (n : Nat) p, b2.params[n]? = some p →
        m.contains p.1 = true → fr'.regs (rename m p.1) = vs[n]? := by
  intro vs hvs
  have hT := h.termOps hF hs
  obtain ⟨b, hbi, hk, hterm⟩ := inv_atEnd h.inv hs
  refine ⟨?_, fun b2 hb2 n p hp hc => ?_⟩
  · exact getMany_filt _ _ (Res.norm_eq_ok (getMany_rename fun x hx => (hT x (hops x hx)).1) hvs)
  · obtain ⟨j, hj, hid⟩ := block?_index hF.wf hb2
    have hidx : D.index bc.block = some j := by rw [← hid]; exact hF.wf.ids j b2 hj
    rw [hterm] at hedge
    obtain ⟨hlen, hpos⟩ := hF.edge bi b hbi _ hedge j b2 hidx hj
    have hn : n < bc.args.length := by
      have := (List.getElem?_eq_some_iff.1 hp).1
      simp only [List.length_map] at hlen; omega
    have hx0 : bc.args[n]? = some bc.args[n] := List.getElem?_eq_getElem hn
    obtain ⟨x, hx, hσ⟩ := hpos n p (some bc.args[n]) hp (by simp [hx0]) hc
    cases hx
    rw [← hσ, (hT _ (hops _ (List.mem_of_getElem? hx0))).1]
    exact (getMany_ok hvs).2 n _ hx0

/-- The terminators step in lock-step. -/
theorem CRel.termStep {fr fr' : Frame} {bi k : Nat} {mm : Mem} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) :
    (∀ fr1 m1, lstep fr mm = .next fr1 m1 → ∃ fr1', lstep fr' mm = .next fr1' m1 ∧
      CR m f D syms fr1 fr1') ∧
    (∀ vals, lstep fr mm = .ret vals → lstep fr' mm = .ret vals) ∧
    (∀ ext vals, lstep fr mm = .tail ext vals → lstep fr' mm = .tail ext vals) ∧
    (∀ c, lstep fr mm = .trap c → lstep fr' mm = .trap c) := by
  have ht : fr'.body = [] := by rw [h.body, hs]; rfl
  have hT := h.termOps hF hs
  have hget : ∀ x ∈ termOperands fr.term, ∀ a, fr.get x = .ok a → fr'.get (rename m x) = .ok a := by
    intro x hx a ha
    simp only [Frame.get, (hT x hx).1] at ha ⊢
    simpa [Res.ofOption_eq_ok] using ha
  have henter := fun {bc} hsucc hedge hops {fr1} (he : enterBlock fr bc = .ok fr1) =>
    enterAt hF h.inv hs h.func h.slots h.agree (bc' := filterBC (keepMap m f)
      (mapBlockCall (rename m) bc)) hsucc he rfl (h.plainArgs hF hs hedge hops)
  rw [lstep_term hs, lstep_term ht, h.term]
  cases hT' : fr.term with
  | jump d =>
    rw [hT'] at hget henter
    simp only [mapTerm, filterTerm]
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun c hl => ?_⟩ <;>
      cases he : enterBlock fr d <;> rw [he] at hl <;> simp only [LRes.ofRes] at hl <;>
      (try cases hl)
    · obtain ⟨fr1', he', hr⟩ := henter (by simp [termSuccs]) (by simp [edges])
        (fun x hx => by simpa [termOperands] using hx) he
      exact ⟨fr1', by rw [he']; rfl, hr⟩
    · exact absurd he (enterBlock_not_trap _ _ _)
  | brif c t e =>
    rw [hT'] at hget henter
    simp only [mapTerm, filterTerm]
    have hsel : ∀ cv : Val, (if Sem.truthy cv.bits then filterBC (keepMap m f) (mapBlockCall (rename m) t)
        else filterBC (keepMap m f) (mapBlockCall (rename m) e)) =
        filterBC (keepMap m f) (mapBlockCall (rename m) (if Sem.truthy cv.bits then t else e)) := by
      intro cv; split <;> rfl
    have hgt : ∀ c', fr.get c ≠ .trap c' := fun c' => by simp [Frame.get_ne_trap]
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : fr.get c with
      | trap c'' => exact absurd hc (hgt c'')
      | stuck _ => rw [hc] at hl; cases hl
      | ok cv =>
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        cases he : enterBlock fr (if Sem.truthy cv.bits then t else e) with
        | trap c'' => exact absurd he (enterBlock_not_trap _ _ _)
        | stuck _ => rw [he] at hl; cases hl
        | ok fr1x =>
          rw [he] at hl; simp only [LRes.ofRes] at hl
          first
          | (cases hl; done)
          | (simp only [LRes.next.injEq] at hl
             obtain ⟨rfl, rfl⟩ := hl
             rw [hget c (by simp [termOperands]) cv hc]; simp only [LRes.ofRes]
             obtain ⟨fr1', he', hr⟩ := henter (by split <;> simp [termSuccs])
               (by split <;> simp [edges])
               (fun x hx => by
                 simp only [termOperands, List.mem_cons, List.mem_append]
                 split at hx <;> simp [hx]) he
             rw [hsel, he']
             exact ⟨fr1', rfl, hr⟩)
  | brTable x d tbl =>
    rw [hT'] at hget henter
    simp only [mapTerm, filterTerm]
    have hgt : ∀ c', fr.get x ≠ .trap c' := fun c' => by simp [Frame.get_ne_trap]
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : fr.get x with
      | trap c'' => exact absurd hc (hgt c'')
      | stuck _ => rw [hc] at hl; cases hl
      | ok xv =>
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        cases he : enterBlock fr (tbl[xv.toNat]?.getD d) with
        | trap c'' => exact absurd he (enterBlock_not_trap _ _ _)
        | stuck _ => rw [he] at hl; cases hl
        | ok fr1x =>
          rw [he] at hl; simp only [LRes.ofRes] at hl
          first
          | (cases hl; done)
          | (simp only [LRes.next.injEq] at hl
             obtain ⟨rfl, rfl⟩ := hl
             rw [hget x (by simp [termOperands]) xv hc]; simp only [LRes.ofRes]
             have hsel : ((tbl.map (mapBlockCall (rename m))).map (filterBC (keepMap m f)))[xv.toNat]?.getD
                 (filterBC (keepMap m f) (mapBlockCall (rename m) d)) =
                 filterBC (keepMap m f) (mapBlockCall (rename m) (tbl[xv.toNat]?.getD d)) := by
               rw [List.getElem?_map, List.getElem?_map]; cases tbl[xv.toNat]? <;> rfl
             have hmem : tbl[xv.toNat]?.getD d = d ∨ tbl[xv.toNat]?.getD d ∈ tbl := by
               cases hq : tbl[xv.toNat]? with
               | none => exact .inl rfl
               | some q => exact .inr (List.mem_of_getElem? hq)
             obtain ⟨fr1', he', hr⟩ := henter (by
                 simp only [termSuccs, List.mem_cons, List.mem_map]
                 rcases hmem with hm | hm
                 · exact .inl (by rw [hm])
                 · exact .inr ⟨_, hm, rfl⟩)
               (by
                 simp only [edges, List.mem_cons, List.mem_map]
                 rcases hmem with hm | hm
                 · exact .inl (by rw [hm])
                 · exact .inr ⟨_, hm, rfl⟩)
               (fun y hy => by
                 simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
                 rcases hmem with hm | hm
                 · rw [hm] at hy; exact .inl (.inr hy)
                 · exact .inr ⟨_, hm, hy⟩) he
             rw [hsel, he']
             exact ⟨fr1', rfl, hr⟩)
  | ret xs =>
    simp only [mapTerm, filterTerm]
    have hg := getMany_rename (fr := fr) (fr' := fr') (σ := rename m) (xs := xs)
      (fun x hx => (hT x (by rw [hT']; exact hx)).1)
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : fr.getMany xs with
      | trap c'' => exact absurd hc (getMany_not_trap _ _ _)
      | stuck _ => rw [hc] at hl; cases hl
      | ok vs =>
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        first
        | (cases hl; done)
        | (simp only [LRes.ret.injEq] at hl; subst hl; rw [Res.norm_eq_ok hg hc]; rfl)
  | returnCall fn args =>
    simp only [mapTerm, filterTerm]
    have hg := tailArgs_rename (fr := fr) (fr' := fr') (σ := rename m) (fn := fn) (args := args)
      h.externs h.sig (fun x hx => (hT x (by rw [hT']; exact hx)).1)
    refine ⟨fun fr1 m1 hl => ?_, fun vals hl => ?_, fun _ _ hl => ?_, fun c' hl => ?_⟩
    all_goals cases hc : tailArgs fr fn args with
      | trap c'' =>
        rw [hc] at hl
        first
        | (cases hl; done)
        | (cases hl; rw [Res.norm_eq_trap hg hc]; rfl)
      | stuck _ => rw [hc] at hl; cases hl
      | ok p =>
        obtain ⟨e, vs⟩ := p
        rw [hc] at hl; simp only [LRes.ofRes] at hl
        first
        | (cases hl; done)
        | (simp only [LRes.tail.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
           rw [Res.norm_eq_ok hg hc]; rfl)
  | tryCall _ _ _ =>
    refine ⟨fun _ _ hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun _ hl => ?_⟩ <;> cases hl
  | tryCallIndirect _ _ _ =>
    refine ⟨fun _ _ hl => ?_, fun _ hl => ?_, fun _ _ hl => ?_, fun _ hl => ?_⟩ <;> cases hl
  | trap c =>
    simp only [mapTerm, filterTerm]
    exact ⟨(fun _ _ hl => by cases hl), (fun _ hl => by cases hl), (fun _ _ hl => by cases hl),
      (fun _ hl => hl)⟩

end

/-! ## `try_call` -/

theorem dests_normal (et : ExnTable) : et.normal ∈ et.dests := by simp [ExnTable.dests]

section
variable {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} (hF : CpFacts m f D)
  {syms : String → Option Nat}
include hF

/-- After a `try_call` returns: the results are bound at each side's fresh value and both frames
enter the normal-return successor, the target with the kept arguments. -/
theorem CRel.tcont {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) (hw : Win fr fr') {et : ExnTable} {n : Nat} {bc bc' : BlockCall}
    {rtys : List Ty} (hedge : (et.normal.block, et.normal.args.map argVal) ∈ edges fr.term)
    (hsucc : et.normal.block ∈ termSuccs fr.term)
    (hvals : ∀ x ∈ et.normal.vals, x ∈ termOperands fr.term)
    (hbc : tryNormal et fr.func.freshValue = .ok bc)
    (hbc' : tryNormal (filterEt (keepMap m f) (et.mapVals (rename m))) fr'.func.freshValue = .ok bc') :
    TCont (CR m f D syms) fr (tryRets n fr.func.freshValue) bc fr' (tryRets n fr'.func.freshValue)
      bc' rtys := by
  have hf := h.inv.func
  have hg := h.func
  have hT := h.termOps hF hs
  have hbc0 := hbc
  rw [tryNormal_eq] at hbc0
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at hbc0
  obtain ⟨bargs, hres, rfl⟩ := hbc0
  intro vs regs _ hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := tryRets n fr'.func.freshValue)
    (vs := vs) (by have := (setMany_spec hset).1; simp only [tryRets, List.length_map,
      List.length_range] at this ⊢; exact this)
  refine ⟨regs', hset', fun fr1 he1 => ?_⟩
  have hlo : ∀ v < f.freshValue, regs v = fr.regs v := by
    intro v hv
    refine ((setMany_spec hset).2 v).1 fun hm => ?_
    obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : fr.func.freshValue + j = v := he
    rw [hf] at he'
    exact no_window' he' hv
  have hlo' : ∀ v < (cpFun m f).freshValue, regs' v = fr'.regs v := by
    intro v hv
    refine ((setMany_spec hset').2 v).1 fun hm => ?_
    obtain ⟨j, -, he⟩ := List.mem_map.1 hm
    have he' : fr'.func.freshValue + j = v := he
    rw [hg] at he'
    exact no_window' he' hv
  have hinvA : Inv f D syms { fr with regs } bi k := h.inv.regs_congr hF.wf hlo
  have hagreeA : ∀ v, Avail D bi k v →
      ({ fr' with regs := regs' } : Frame).regs (rename m v) = ({ fr with regs } : Frame).regs v := by
    intro v hv
    show regs' _ = regs _
    rw [hlo' _ (rename_lt hF hv), hlo _ (avail_lt hF.wf hv)]
    exact h.agree v hv
  obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair (rename m) (et := et)
    (et' := et.mapVals (rename m)) rfl (b2 := fr'.func.freshValue) hbc
  have hf2 := tryNormal_filter (keepMap m f) hbc2
  rw [hbc'] at hf2
  cases hf2
  refine enterAt (fr' := { fr' with regs := regs' }) hF hinvA hs hg h.slots hagreeA hsucc he1
    (by simpa using hblk) ?_
  intro vs1 hga
  refine ⟨?_, fun b2 hb2 i p hp hc => ?_⟩
  · have hga' : Frame.getMany { fr' with regs := regs' } bc2.args = .ok vs1 := by
      refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y hxy => ?_) hga
      simp only
      rcases hxy with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
      · rw [hx, hy]
        obtain ⟨h1, h2, h3⟩ := hT v (hvals v hv)
        rw [hlo' _ h3, hlo _ h2, h1]
      · rw [hx, hy, setMany_tryRets hset i, setMany_tryRets hset' i]
        split
        · rfl
        · exact (hw i).symm
    rw [hblk]
    exact getMany_filt _ _ hga'
  · obtain ⟨j, hj, hid⟩ := block?_index hF.wf hb2
    have hid' : b2.id = et.normal.block := hid
    have hidx : D.index et.normal.block = some j := by rw [← hid']; exact hF.wf.ids j b2 hj
    obtain ⟨bb, hbi, -, hterm⟩ := inv_atEnd h.inv hs
    rw [hterm] at hedge
    obtain ⟨hlen, hpos⟩ := hF.edge bi bb hbi _ hedge j b2 hidx hj
    have hn : i < et.normal.args.length := by
      have := (List.getElem?_eq_some_iff.1 hp).1
      simp only [List.length_map] at hlen; omega
    have hx0 : et.normal.args[i]? = some et.normal.args[i] := List.getElem?_eq_getElem hn
    obtain ⟨x, hx, hσ⟩ := hpos i p (argVal et.normal.args[i]) hp (by simp [hx0]) hc
    have hval : et.normal.args[i] = .val x := by
      cases ha : et.normal.args[i] with
      | val v => rw [ha] at hx; simp only [argVal, Option.some.injEq] at hx; rw [hx]
      | ret _ => rw [ha] at hx; simp [argVal] at hx
      | exn _ => rw [ha] at hx; simp [argVal] at hx
    have hbargs : bargs[i]? = some x := resolve_val _ _ hres i x (by rw [hx0, hval])
    have hxv : x ∈ et.normal.vals := by
      simp only [TryDest.vals]
      exact List.mem_filterMap.2 ⟨.val x, by rw [← hval]; exact List.getElem_mem hn, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hT x (hvals x hxv)
    show regs' (rename m p.1) = vs1[i]?
    rw [← hσ, hlo' _ h3, h1, ← hlo _ h2]
    exact (getMany_ok hga).2 i x hbargs

/-- **The frame relation is a simulation with windows.** -/
theorem CR.isSimW : IsSimW syms (CR m f D syms) where
  toIsSim := {
    frame := by
      rintro fr fr' ⟨bi, k, h⟩
      exact ⟨h.slots, h.sig⟩
    next := by
      rintro fr fr' mm fr1 m1 ⟨bi, k, h⟩ hm hl
      cases hs : fr.body with
      | nil =>
        obtain ⟨fr1', hl', hr⟩ := (h.termStep hF (mm := mm) hs).1 fr1 m1 hl
        exact ⟨fr1', .single hl', hr⟩
      | cons s ss =>
        have hnc : ∀ fn args, s.inst ≠ .call fn args :=
          fun fn args hc => (lstep_call_of_call hs hc).1 fr1 m1 hl
        obtain ⟨fr1', hl', hr⟩ := (h.stmt hF hm hs hnc).1 fr1 m1 hl
        exact ⟨fr1', .single hl', bi, k + 1, hr⟩
    call := by
      rintro fr fr' mm ext vals rs rest ⟨bi, k, h⟩ hm hl
      obtain ⟨hl', hk⟩ := h.call hF hl
      exact ⟨fr', rs, _, .refl _ _, hl', hk⟩
    ret := by
      rintro fr fr' mm vals ⟨bi, k, h⟩ hm hl
      exact ⟨fr', .refl _ _, (h.termStep hF (mm := mm) (lstep_ret_inv hl)).2.1 vals hl⟩
    tail := by
      rintro fr fr' mm ext vals ⟨bi, k, h⟩ hm hl
      exact ⟨fr', .refl _ _, (h.termStep hF (mm := mm) (lstep_tail_inv hl)).2.2.1 ext vals hl⟩
    trap := by
      rintro fr fr' mm c ⟨bi, k, h⟩ hm hl
      cases hs : fr.body with
      | nil => exact ⟨fr', mm, .refl _ _, (h.termStep hF (mm := mm) hs).2.2.2 c hl⟩
      | cons s ss =>
        have hnc : ∀ fn args, s.inst ≠ .call fn args :=
          fun fn args hc => (lstep_call_of_call hs hc).2 c hl
        exact ⟨fr', mm, .refl _ _, (h.stmt hF hm hs hnc).2 c hl⟩ }
  ci := by
    rintro fr fr' mm st rest sig callee args d a vals ⟨bi, k, h⟩ - - - hm hb hi hca
    exfalso
    obtain ⟨b, hbi, h1, -, -⟩ := h.inv.block
    rw [h1] at hb
    obtain ⟨hk, -, -⟩ := drop_eq_cons hb
    exact hF.wf.noCI hbi hk sig callee args hi
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr' mm fn args et n base bc ext vals ⟨bi, k, h⟩ - - hw hm hb ht htc hca
      have ht' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hterm' : fr'.term = .tryCall fn (args.map (rename m))
          (filterEt (keepMap m f) (et.mapVals (rename m))) := by
        rw [h.term, ht]; rfl
      have hT := h.termOps hF hb
      rw [ht] at hT
      obtain ⟨e0, s0, he0, hs0, hc0, rfl, hbc, rfl⟩ := tcArgs_ok.1 htc
      obtain ⟨bc2, hbc2, -, -⟩ := tryNormal_pair (rename m) (et := et)
        (et' := et.mapVals (rename m)) rfl (b2 := fr'.func.freshValue) hbc
      have hbc' := tryNormal_filter (keepMap m f) hbc2
      have htc' : tcArgs fr' fn (filterEt (keepMap m f) (et.mapVals (rename m))) =
          .ok (e0.sig.returns.length, fr'.func.freshValue,
            { block := bc2.block, args := filt (keepOf (keepMap m f) bc2.block) bc2.args }) := by
        refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', rfl⟩
        · rw [← he0]; simp only [Function.extern?, h.externs]
        · rw [← hs0, h.sigDecls]; rfl
      have hca' : callArgs fr' fn (args.map (rename m)) = .ok (ext, vals) :=
        Res.norm_eq_ok (callArgs_rename h.externs
          (fun x hx => (hT x (by simp [termOperands, hx])).1)) hca
      refine ⟨fr', fn, args.map (rename m), _, _, _, .refl _ _, ht', hterm', htc', hca', ?_⟩
      exact h.tcont hF hb hw (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
        (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
        (fun x hx => by rw [ht]; exact normal_vals_sub x hx) hbc hbc'
    · rintro fr fr' mm callee args et n base bc d a vals ⟨bi, k, h⟩ - - hw hm hb ht htc hca
      have ht' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hterm' : fr'.term = .tryCallIndirect (rename m callee) (args.map (rename m))
          (filterEt (keepMap m f) (et.mapVals (rename m))) := by
        rw [h.term, ht]; rfl
      have hT := h.termOps hF hb
      rw [ht] at hT
      obtain ⟨s0, hs0, rfl, hbc, rfl⟩ := ticArgs_ok.1 htc
      obtain ⟨bc2, hbc2, -, -⟩ := tryNormal_pair (rename m) (et := et)
        (et' := et.mapVals (rename m)) rfl (b2 := fr'.func.freshValue) hbc
      have hbc' := tryNormal_filter (keepMap m f) hbc2
      have htc' : ticArgs fr' (filterEt (keepMap m f) (et.mapVals (rename m))) =
          .ok (s0.returns.length, fr'.func.freshValue,
            { block := bc2.block, args := filt (keepOf (keepMap m f) bc2.block) bc2.args }) :=
        ticArgs_ok.2 ⟨s0, by rw [← hs0, h.sigDecls]; rfl, rfl, hbc', rfl⟩
      have hca' : ciArgs fr' (filterEt (keepMap m f) (et.mapVals (rename m))).sig (rename m callee)
          (args.map (rename m)) = .ok (d, a, vals) :=
        ciArgs_rename h.sigDecls
          (fun x hx => (hT x (by
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp [termOperands]
            · simp [termOperands, hx])).1) hca
      refine ⟨fr', rename m callee, args.map (rename m), _, _, _, .refl _ _, ht', hterm', htc', hca', ?_⟩
      exact h.tcont hF hb hw (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
        (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
        (fun x hx => by rw [ht]; exact normal_vals_sub' x hx) hbc hbc'

end

/-! ## The theorems -/

/-- **Constant-phi removal is sound**: the rewrite of a solution `cpOk` accepts simulates the
function, `call_indirect` and `try_call`/`try_call_indirect` included. -/
theorem cpOk_simX {f : Function} {sol : List (ValueId × ValueId)} (h : cpOk f sol = true) :
    FunSimX f (apply f sol) := by
  obtain ⟨fi, -, hF⟩ := cpOk_facts h
  rw [apply_eq]
  refine FunSimX.ofW rfl rfl rfl rfl fun syms => ⟨_, CR.isSimW hF (syms := syms), fun b hb => ?_⟩
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  have hkeep : ∀ p ∈ b.params, (solMap sol).contains p.1 = false := by
    intro p hp
    cases hc : (solMap sol).contains p.1
    · rfl
    · obtain ⟨bp, -, -, hd, hbp, -⟩ := hF.key p.1 hc
      rw [site_param hF.wf hb0 hp] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      exact absurd hd.1.symm hbp
  have hpar : (cpBlock (solMap sol) (keepMap (solMap sol) f) b).params = b.params := by
    simp only [cpBlock]
    exact List.filter_eq_self.2 (fun p hp => by simp [hkeep p hp])
  refine ⟨cpBlock _ _ b, by rw [cpFun_entry?, hb]; rfl, hpar,
    fun args regs slots hty hr hsl => ⟨0, 0, Inv.entry hF.wf hb hty hr hsl, rfl, rfl, rfl, rfl,
      fun v hv => ?_⟩⟩
  obtain ⟨b1, p, hb1, hp, hpv⟩ := site_param' hF.wf (avail_entry hF.wf hv)
  rw [hb0] at hb1; cases hb1
  show regs (rename (solMap sol) v) = regs v
  rw [← hpv, rename_of_not (hkeep p hp)]

/-- `runCore` simulates every function: the unreachable blocks removed (`removeUnreachable`,
under the fresh-value guard) and, when `cpOk` accepts it, the solution applied. -/
theorem runCore_simX (f : Function) : FunSimX f (runCore f) := by
  unfold runCore
  by_cases hc : freshOkB f = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
    have h1 := removeUnreachable_simX f hc
    split
    · rename_i h2
      simp only [Bool.and_eq_true] at h2
      exact h1.trans (cpOk_simX h2.2)
    · exact h1
  · have hc' : freshOkB f = false := by simpa using hc
    simp only [hc', Bool.not_false, ite_true]
    exact FunSimX.refl f

/-- **The pass simulates every function.** -/
theorem run_simX (f : Function) : FunSimX f (run f) := by
  show FunSimX f (if keepsShapeB f (runCore f) then runCore f else f)
  split
  · exact runCore_simX f
  · exact FunSimX.refl f

end Opt.ConstPhi
