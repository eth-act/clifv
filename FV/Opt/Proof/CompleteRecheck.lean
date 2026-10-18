import FV.Opt.Proof.CompleteLicm
import FV.Opt.Proof.DomFacts

/-!
# Re-checking after `removeUnreachable` (M1)

`Opt.optimizeReport` re-checks the simplify stage's output `g1` after `removeUnreachable`:
`simpOk` has established `wfCert g1 fi.cfg types` against the *input's* CFG `fi.cfg`, but the
skeleton rules may have deleted edges, so blocks may have become unreachable and dominance may
have changed. `Opt.check_removeUnreachable_of_wfCert` shows that `check` accepts
`removeUnreachable f` whenever `f` passes the certificate against *some* CFG (with unique
definitions, the entry signature, branch arities and argument types, and `br_table` index types),
given the facts `Opt.DomFacts` of the new dominator tree.

The argument:
* the edge certificate makes every tree ancestor (in `cfg.idom`) of a block a dominator of it in
  `f`'s graph (`Opt.reachAvoid_not_anc`), and every tree ancestor of a reachable block reachable
  (`Opt.reach_anc`);
* `removeUnreachableRaw` keeps the reachable blocks; block `i'` of the output is block `i` of `f`
  (`Opt.Corr`), and the output's graph is `f`'s graph restricted to the kept blocks
  (`Opt.corr_edge`), so every kept block stays reachable and dominance is kept;
* with `DomFacts.complete`, every old tree ancestor is an ancestor in the new tree
  (`Opt.anc_transfer`): the certificate facts `Wf` hold over the output's own `checkCore` data,
  and `checkCore` succeeds (`Opt.coreOk_of_wf`).
-/

namespace Opt

open Clif

/-! ## Tree ancestors along paths -/

section Tree

variable {succs : Array (List Nat)} {idom : Array (Option Nat)}

theorem anc_zero (hroot : idom[0]?.join = none) {d : Nat} (h : Anc idom d 0) : d = 0 := by
  cases h with
  | refl => rfl
  | up hc _ => rw [hroot] at hc; cases hc

/-- A tree ancestor of a reachable block is reachable (edge certificate). -/
theorem reach_anc (hroot : idom[0]?.join = none)
    (hedge : ∀ u x, x ∈ succs[u]! → ∀ y, idom[x]?.join = some y → Anc idom y u) {x : Nat}
    (h : Reach succs x) : ∀ d, Anc idom d x → Reach succs d := by
  induction h with
  | entry => intro d hd; rw [anc_zero hroot hd]; exact .entry
  | @step u x hu hx ih =>
    intro d hd
    by_cases hdx : d = x
    · subst hdx; exact .step hu hx
    · obtain ⟨y, hy, hdy⟩ := hd.strict hdx
      exact ih d (hdy.trans (hedge u x hx y hy))

/-- **Tree ancestors dominate**: a block reachable while avoiding `d` does not have `d` as a tree
ancestor (edge certificate). -/
theorem reachAvoid_not_anc (hroot : idom[0]?.join = none)
    (hedge : ∀ u x, x ∈ succs[u]! → ∀ y, idom[x]?.join = some y → Anc idom y u) {d x : Nat}
    (h : ReachAvoid succs d x) : ¬ Anc idom d x := by
  induction h with
  | entry hd0 => intro h; exact hd0 (anc_zero hroot h)
  | @step u x _ hx hxd ih =>
    intro h
    obtain ⟨y, hy, hdy⟩ := h.strict (Ne.symm hxd)
    exact ih (hdy.trans (hedge u x hx y hy))

end Tree

/-! ## Reachability in `Cfg.build` -/

theorem build_size' (g : Function) : (Cfg.build g).size = g.blocks.length := by
  simp [Cfg.size, Cfg.build]

theorem succs_lt_of_mem {g : Function} {u x : Nat} (h : x ∈ (Cfg.build g).succs[u]!) :
    u < g.blocks.length := by
  rcases Nat.lt_or_ge u g.blocks.length with hu | hu
  · exact hu
  · have : (Cfg.build g).succs[u]! = [] := by
      simp [getElem!_def, Array.getElem?_eq_none (by rw [build_succs_size]; omega)]; rfl
    rw [this] at h; cases h

theorem reach_reachable {g : Function} (hn : g.blocks ≠ []) {z : Nat}
    (h : Reach (Cfg.build g).succs z) : (Cfg.build g).reachable z = true := by
  have hn' : (Cfg.build g).succs.size ≠ 0 := by
    rw [build_succs_size]; intro h0; exact hn (List.eq_nil_of_length_eq_zero h0)
  obtain ⟨h0, hcl⟩ := postorder_closed _ (build_succs_lt g) hn'
  have hm : z ∈ (Cfg.postorder (Cfg.build g).succs).toList := by
    induction h with
    | entry => exact h0
    | step _ hx ih => exact (hcl _ ih).2 _ hx
  have hz := (hcl z hm).1
  rw [build_succs_size] at hz
  exact (build_reachable_iff g hz).2 hm

theorem reachable_reach {g : Function} {z : Nat} (hz : z < g.blocks.length)
    (h : (Cfg.build g).reachable z = true) : Reach (Cfg.build g).succs z :=
  postorder_reach _ z ((build_reachable_iff g hz).1 h)

theorem reachable_lt {g : Function} {z : Nat}
    (h : (Cfg.build g).reachable z = true) : z < g.blocks.length := by
  rcases Nat.lt_or_ge z g.blocks.length with hz | hz
  · exact hz
  exfalso
  have hr : ((Cfg.build g).rpoNum[z]?.join).isSome = true := h
  rw [build_rpoNum, ← Array.foldl_toList, Array.toList_zipIdx] at hr
  have key : ∀ (l : List (Nat × Nat)) (r : Array (Option Nat)), r.size = g.blocks.length →
      (l.foldl (fun r (x : Nat × Nat) => r.set! x.1 (some x.2)) r).size = g.blocks.length := by
    intro l; induction l with
    | nil => intro r hr; exact hr
    | cons x l ih => intro r hr; exact ih _ (by simp [hr])
  have hs := key ((Cfg.build g).rpo.toList.zipIdx) (Array.replicate g.blocks.length none) (by simp)
  rw [Array.getElem?_eq_none (by omega)] at hr
  cases hr

/-- The block index of a function with unique block ids has one entry per block. -/
theorem index_fold_size (l : List (BlockId × Nat)) (hl : (l.map (·.1)).Nodup)
    (m : Std.HashMap BlockId Nat) (hm : ∀ x ∈ l, m.contains x.1 = false) :
    (l.foldl (fun m (x : BlockId × Nat) => if m.contains x.1 then m else m.insert x.1 x.2) m).size =
      m.size + l.length := by
  induction l generalizing m with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons] at hl
    have hx := hm x (List.mem_cons_self ..)
    simp only [List.foldl_cons, hx, Bool.false_eq_true, ite_false]
    rw [ih hl.2 _ (fun y hy => ?_)]
    · rw [Std.HashMap.size_insert]
      simp only [Std.HashMap.mem_iff_contains, hx, Bool.false_eq_true, ite_false, List.length_cons]
      omega
    · rw [Std.HashMap.contains_insert, hm y (List.mem_cons_of_mem _ hy)]
      have : y.1 ≠ x.1 := fun he => hl.1 (he ▸ List.mem_map_of_mem hy)
      simpa using Ne.symm this

theorem build_index_size {g : Function} (hn : (blockIds g).Nodup) :
    (Cfg.build g).index.size = (Cfg.build g).size := by
  show (Array.foldl (fun (m : Std.HashMap BlockId Nat) (x : BlockId × Nat) =>
    if m.contains x.1 then m else m.insert x.1 x.2) ∅
      (Array.map (fun x : Block => x.id) g.blocks.toArray).zipIdx).size = _
  rw [← Array.foldl_toList, Array.toList_zipIdx, index_fold_size]
  · simp [build_size']
  · simpa [blockIds] using hn
  · intro x _; simp

theorem termCalls_succ {t : Terminator} {bc : BlockCall} (h : bc ∈ termCalls t) :
    bc.block ∈ termSuccs t := by
  cases t <;> simp_all [termCalls, termSuccs]
  all_goals first
    | (rcases h with rfl | rfl <;> simp)
    | (rcases h with rfl | h; · simp
       · exact .inr ⟨bc, h, rfl⟩)

/-! ## The kept blocks -/

/-- Block `i'` of `removeUnreachableRaw f` is block `i` of `f`. -/
def Corr (f : Function) (i' i : Nat) : Prop :=
  ∃ b, (removeUnreachableRaw f).blocks[i']? = some b ∧ f.blocks[i]? = some b

section Kept

variable {f : Function}

theorem blk_idx_unique {g : Function} (hids : (blockIds g).Nodup) {i j : Nat} {b b' : Block}
    (hi : g.blocks[i]? = some b) (hj : g.blocks[j]? = some b') (he : b.id = b'.id) : i = j := by
  have h1 := build_index_of_nodup hids (j := i) (id := b.id) (by simp [blockIds, hi])
  have h2 := build_index_of_nodup hids (j := j) (id := b.id) (by simp [blockIds, hj, he])
  rw [h1] at h2; exact Option.some.inj h2

theorem raw_ids (hids : (blockIds f).Nodup) : (blockIds (removeUnreachableRaw f)).Nodup :=
  ((raw_sublist f).map _).nodup hids

theorem Corr.inj_old (hids : (blockIds f).Nodup) {i' i j : Nat} (h1 : Corr f i' i)
    (h2 : Corr f i' j) : i = j := by
  obtain ⟨b, hb, hi⟩ := h1
  obtain ⟨b2, hb2, hj⟩ := h2
  rw [hb] at hb2; cases hb2
  exact blk_idx_unique hids hi hj rfl

theorem Corr.inj_new (hids : (blockIds f).Nodup) {i' j' i : Nat} (h1 : Corr f i' i)
    (h2 : Corr f j' i) : i' = j' := by
  obtain ⟨b, hb, hi⟩ := h1
  obtain ⟨b2, hb2, hj⟩ := h2
  rw [hi] at hj; cases hj
  exact blk_idx_unique (raw_ids hids) hb hb2 rfl

theorem corr_of_new {i' : Nat} {b : Block} (hb : (removeUnreachableRaw f).blocks[i']? = some b) :
    ∃ i, Corr f i' i ∧ f.blocks[i]? = some b ∧ (Cfg.build f).reachable i = true := by
  obtain ⟨i, hi, hr⟩ := mem_raw.1 (List.mem_of_getElem? hb)
  exact ⟨i, ⟨b, hb, hi⟩, hi, hr⟩

theorem corr_of_old {i : Nat} {b : Block} (hb : f.blocks[i]? = some b)
    (hr : (Cfg.build f).reachable i = true) :
    ∃ i', Corr f i' i ∧ (removeUnreachableRaw f).blocks[i']? = some b := by
  obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.1 (mem_raw.2 ⟨i, hb, hr⟩)
  exact ⟨i', ⟨b, hi', hb⟩, hi'⟩

theorem Corr.reachable (hids : (blockIds f).Nodup) {i' i : Nat} (h : Corr f i' i) :
    (Cfg.build f).reachable i = true := by
  obtain ⟨b, hb, hi⟩ := h
  obtain ⟨j, hj, -, hr⟩ := corr_of_new hb
  rw [Corr.inj_old hids ⟨b, hb, hi⟩ hj]; exact hr

theorem corr_zero (hn : f.blocks ≠ []) : Corr f 0 0 := by
  cases hfb : f.blocks with
  | nil => exact absurd hfb hn
  | cons b0 rest =>
    have hr0 : (Cfg.build f).reachable 0 = true := reach_reachable hn .entry
    refine ⟨b0, ?_, by rw [hfb]; rfl⟩
    simp only [removeUnreachableRaw]
    rw [hfb]
    simp [List.zipIdx_cons, hr0]

/-- **The output's graph is the input's graph restricted to the kept blocks.** -/
theorem corr_edge (hids : (blockIds f).Nodup) {u' u x' x : Nat} (hu : Corr f u' u)
    (hx : Corr f x' x) :
    x' ∈ (Cfg.build (removeUnreachableRaw f)).succs[u']! ↔ x ∈ (Cfg.build f).succs[u]! := by
  obtain ⟨b, hbG, hbf⟩ := hu
  obtain ⟨bx, hxG, hxf⟩ := hx
  rw [build_succs_mem _ hbG, build_succs_mem f hbf]
  have key : ∀ id, (Cfg.build (removeUnreachableRaw f)).index.get? id = some x' ↔
      (Cfg.build f).index.get? id = some x := by
    intro id
    simp only [Std.HashMap.get?_eq_getElem?]
    constructor
    · intro h
      have := (build_index_lt h).2
      simp only [blockIds, List.getElem?_map, hxG, Option.map_some, Option.some.injEq] at this
      subst this
      exact build_index_of_nodup hids (by simp [blockIds, hxf])
    · intro h
      have := (build_index_lt h).2
      simp only [blockIds, List.getElem?_map, hxf, Option.map_some, Option.some.injEq] at this
      subst this
      exact build_index_of_nodup (raw_ids hids) (by simp [blockIds, hxG])
  simp only [key]

end Kept

/-! ## The certificate's tree in the input -/

section Old

variable {f : Function} {cfg : Cfg} {types : Std.HashMap ValueId Ty}

/-- The certificate data of `wfCert f cfg types`. -/
def oldData (f : Function) (cfg : Cfg) (types : Std.HashMap ValueId Ty) : WfData :=
  wfData f { cfg, types, defBlock := {}, pureDef := {} }

theorem old_wf (hw : wfCert f cfg types = true) : Wf f (oldData f cfg types) :=
  wfCert_sound (info := { cfg, types, defBlock := {}, pureDef := {} }) hw

theorem old_ids (hw : wfCert f cfg types = true) : (blockIds f).Nodup := by
  have := blocksOkB_of_wfCert hw
  simp only [blocksOkB, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

/-- The edge certificate on the edges of `Cfg.build f`. -/
theorem old_edge (hw : wfCert f cfg types = true) :
    ∀ u x, x ∈ (Cfg.build f).succs[u]! → ∀ y, cfg.idom[x]?.join = some y → Anc cfg.idom y u := by
  intro u x hx y hy
  have hul := succs_lt_of_mem hx
  obtain ⟨b, hb⟩ : ∃ b, f.blocks[u]? = some b := ⟨_, List.getElem?_eq_getElem hul⟩
  obtain ⟨id, hid, hix⟩ := (build_succs_mem f hb).1 hx
  obtain ⟨j, b', -, hbj, hid', hanc⟩ := (old_wf hw).edges u b hb id hid
  have hj : (Cfg.build f).index.get? id = some j := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact build_index_of_nodup (old_ids hw) (by simp [blockIds, hbj, hid'])
  rw [hix] at hj; cases hj
  exact hanc y hy

end Old

/-! ## Transfer to the output -/

section Transfer

variable {f : Function} {cfg : Cfg} {types : Std.HashMap ValueId Ty}
  (hD : DomFacts (Cfg.build (removeUnreachableRaw f)))
  (hw : wfCert f cfg types = true) (hu : UniqueDefs f) (hn : f.blocks ≠ [])

include hw hn in
/-- Every kept block is reachable in the output. -/
theorem raw_reach {x : Nat} (h : Reach (Cfg.build f).succs x) :
    ∃ x', Corr f x' x ∧ Reach (Cfg.build (removeUnreachableRaw f)).succs x' := by
  induction h with
  | entry => exact ⟨0, corr_zero hn, .entry⟩
  | @step u x hu' hx ih =>
    obtain ⟨u', hcu, hru⟩ := ih
    have hrx := reach_reachable hn (.step hu' hx)
    obtain ⟨bx, hbx⟩ : ∃ bx, f.blocks[x]? = some bx :=
      ⟨_, List.getElem?_eq_getElem (reachable_lt hrx)⟩
    obtain ⟨x', hcx, -⟩ := corr_of_old hbx hrx
    exact ⟨x', hcx, .step hru ((corr_edge (old_ids hw) hcu hcx).2 hx)⟩

theorem raw_ne_nil (hn : f.blocks ≠ []) : (removeUnreachableRaw f).blocks ≠ [] := by
  obtain ⟨b, hb, -⟩ := corr_zero hn
  intro h; rw [h] at hb; cases hb

include hw hn in
theorem raw_reachable {i' : Nat} (hi : i' < (removeUnreachableRaw f).blocks.length) :
    (Cfg.build (removeUnreachableRaw f)).reachable i' = true := by
  obtain ⟨i, hci, hb, hr⟩ := corr_of_new (List.getElem?_eq_getElem hi)
  obtain ⟨x', hcx, hrx⟩ := raw_reach hw hn (reachable_reach (reachable_lt hr) hr)
  rw [Corr.inj_new (old_ids hw) hci hcx]
  exact reach_reachable (raw_ne_nil hn) hrx

include hw hn in
/-- A path avoiding `d'` in the output is a path avoiding `d` in the input. -/
theorem reachAvoid_back {d' d : Nat} (hd : Corr f d' d) {x' : Nat}
    (h : ReachAvoid (Cfg.build (removeUnreachableRaw f)).succs d' x') :
    ∀ x, Corr f x' x → ReachAvoid (Cfg.build f).succs d x := by
  have hids := old_ids hw
  induction h with
  | entry hd0 =>
    intro x hx
    rw [← Corr.inj_old hids (corr_zero hn) hx]
    refine .entry fun h0 => hd0 ?_
    subst h0
    exact Corr.inj_new hids hd (corr_zero hn)
  | @step u' x' hru hx' hxd ih =>
    intro x hcx
    have hul := succs_lt_of_mem hx'
    obtain ⟨u, hcu, -, -⟩ := corr_of_new (List.getElem?_eq_getElem hul)
    refine .step (ih u hcu) ((corr_edge hids hcu hcx).1 hx') fun he => hxd ?_
    subst he
    exact Corr.inj_new hids hcx hd

include hD hw hn in
/-- **Tree ancestors are kept**: an ancestor in the certificate's tree is an ancestor in the
output's dominator tree. -/
theorem anc_transfer {i' i d' d : Nat} (hi : Corr f i' i) (hd : Corr f d' d)
    (ha : Anc cfg.idom d i) : Anc (Cfg.build (removeUnreachableRaw f)).idom d' i' := by
  obtain ⟨b, hb, -⟩ := id hi
  obtain ⟨bd, hbd, -⟩ := id hd
  have hil := (List.getElem?_eq_some_iff.1 hb).1
  have hdl := (List.getElem?_eq_some_iff.1 hbd).1
  refine hD.complete d' i' (raw_reachable hw hn hil) (by rw [build_size']; exact hdl) fun h => ?_
  exact reachAvoid_not_anc (idom := cfg.idom) (old_wf hw).root (old_edge hw)
    (reachAvoid_back hw hn hd h i hi) ha

include hu in
theorem raw_unique : UniqueDefs (removeUnreachableRaw f) := by
  unfold UniqueDefs at hu ⊢
  rw [defSites_fst] at hu ⊢
  exact (Sublist.flatMap' (raw_sublist f) _).nodup hu

include hw in
theorem raw_arity : Arity (removeUnreachableRaw f) := by
  intro b hb st hst
  obtain ⟨i, hi, -⟩ := mem_raw.1 hb
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hst
  obtain ⟨ts, hts, hlen, -⟩ := (old_wf hw).results i b hi j st hj
  exact ⟨ts, hts, hlen⟩

include hw hu in
theorem raw_nodup : ((defList (removeUnreachableRaw f)).map (·.1)).Nodup := by
  rw [← defSites_map_fst (raw_arity hw)]; exact raw_unique hu

/-- The output's `checkCore` data. -/
abbrev newData (f : Function) : WfData :=
  wfData (removeUnreachableRaw f) (coreInfo (removeUnreachableRaw f))

include hw in
/-- The certificate's types are the types of the definitions of the output. -/
theorem tm_agree {e : DefEv} (he : e ∈ defList (removeUnreachableRaw f)) :
    types.get? e.1 = some e.2.1 := by
  have hW := old_wf hw
  obtain ⟨i', b, hb, ⟨p, hp, rfl⟩ | ⟨st, hst, hes⟩⟩ := mem_defList.1 he
  · obtain ⟨i, -, hi, -⟩ := corr_of_new hb
    exact hW.params i b hi p hp
  · obtain ⟨i, -, hi, -⟩ := corr_of_new hb
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hst
    obtain ⟨ts, hts, hlen, htm⟩ := hW.results i b hi j st hj
    have hts' : stmtTys (removeUnreachableRaw f) st = some ts := hts
    unfold stmtEvs at hes
    rw [hts'] at hes
    obtain ⟨⟨r, t⟩, hz, rfl⟩ := List.mem_map.1 hes
    obtain ⟨n, hn'⟩ := List.mem_iff_getElem?.1 hz
    rw [List.getElem?_zip_eq_some] at hn'
    have := htm n r hn'.1
    rw [hn'.2] at this
    exact this

include hw hu in
theorem types_eq {v : ValueId} (hv : v ∈ (defList (removeUnreachableRaw f)).map (·.1)) :
    (defsState (removeUnreachableRaw f)).1.get? v = types.get? v := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
  rw [tm_agree hw he, Std.HashMap.get?_eq_getElem?]
  exact ((defsState_get _ (raw_nodup hw hu)).1 e he).1

include hw hu in
theorem new_defined {v : ValueId} {s : Nat × Nat} (h : (newData f).dm v = some s) :
    v ∈ (defList (removeUnreachableRaw f)).map (·.1) := by
  have hs := (defMap_get_iff (raw_unique hu) v s).1 h
  rw [← defSites_map_fst (raw_arity hw)]
  exact List.mem_map_of_mem (f := (·.1)) hs

theorem site_transfer {v : ValueId} {d d' t : Nat} (hs : (v, (d, t)) ∈ defSites f)
    (hd : Corr f d' d) : (v, (d', t)) ∈ defSites (removeUnreachableRaw f) := by
  obtain ⟨b, hbG, hbf⟩ := hd
  obtain ⟨i, b0, hb0, h⟩ := mem_defSites.1 hs
  rw [mem_defSites]
  refine ⟨d', b, hbG, ?_⟩
  rcases h with ⟨p, hp, hpv, he⟩ | ⟨j, st, hst, hv, he⟩
  · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    rw [hbf] at hb0; cases hb0
    exact .inl ⟨p, hp, hpv, rfl⟩
  · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    rw [hbf] at hb0; cases hb0
    exact .inr ⟨j, st, hst, hv, rfl⟩

theorem site_block {v : ValueId} {d t : Nat} (hs : (v, (d, t)) ∈ defSites f) :
    ∃ b, f.blocks[d]? = some b := by
  obtain ⟨i, b, hb, h⟩ := mem_defSites.1 hs
  rcases h with ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ <;>
  · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, -⟩ := he
    exact ⟨b, hb⟩

include hD hw hu hn in
/-- **Availability is kept.** -/
theorem avail_transfer {i' i k : Nat} {v : ValueId} (hi : Corr f i' i)
    (hA : Avail (oldData f cfg types) i k v) : Avail (newData f) i' k v := by
  have hids := old_ids hw
  have hW := old_wf hw
  obtain ⟨d, t, hdm, h⟩ := hA
  have hs := hW.sitesRev v (d, t) hdm
  rcases h with ⟨rfl, ht⟩ | ⟨hne, ha⟩
  · exact ⟨i', t, (defMap_get_iff (raw_unique hu) v _).2 (site_transfer hs hi), .inl ⟨rfl, ht⟩⟩
  · have hri := hi.reachable hids
    have hil : i < f.blocks.length := reachable_lt hri
    have hrd := reach_reachable hn
      (reach_anc (idom := cfg.idom) hW.root (old_edge hw) (reachable_reach hil hri) d ha)
    obtain ⟨bd, hbd⟩ := site_block hs
    obtain ⟨d', hcd, -⟩ := corr_of_old hbd hrd
    refine ⟨d', t, (defMap_get_iff (raw_unique hu) v _).2 (site_transfer hs hcd),
      .inr ⟨fun he => hne ?_, anc_transfer hD hw hn hi hcd ha⟩⟩
    subst he; exact Corr.inj_old hids hcd hi

include hD hw hu hn in
/-- **The output satisfies the certificate facts** over its own `checkCore` data. -/
theorem raw_wf : Wf (removeUnreachableRaw f) (newData f) := by
  have hids := old_ids hw
  have hW := old_wf hw
  have hn' := raw_nodup hw hu
  refine { ids := ?_, sites := ?_, sitesRev := ?_, root := ?_, rank := ?_, params := ?_,
           uses := ?_, results := ?_, pure := ?_, termUses := ?_, edges := ?_ }
  · intro i' b hb
    show (Cfg.build (removeUnreachableRaw f)).index.get? b.id = some i'
    rw [Std.HashMap.get?_eq_getElem?]
    exact build_index_of_nodup (raw_ids hids) (by simp [blockIds, hb])
  · exact fun v s hs => (defMap_get_iff (raw_unique hu) v s).2 hs
  · exact fun v s hs => (defMap_get_iff (raw_unique hu) v s).1 hs
  · exact hD.root
  · exact hD.rank
  · exact fun i b hb p hp => tm_param hn' hb hp
  · intro i' b hb j st hst v hv
    obtain ⟨i, hci, hbi, -⟩ := corr_of_new hb
    exact avail_transfer hD hw hu hn hci (hW.uses i b hbi j st hst v hv)
  · intro i' b hb j st hst
    obtain ⟨i, -, hbi, -⟩ := corr_of_new hb
    obtain ⟨ts, hts, hlen, -⟩ := hW.results i b hbi j st hst
    exact ⟨ts, hts, hlen, fun n r hr => tm_result hn' hb (List.mem_of_getElem? hst) hts hlen hr⟩
  · intro i' b hb j st hst hp
    obtain ⟨i, hci, hbi, -⟩ := corr_of_new hb
    rw [← hW.pure i b hbi j st hst hp]
    apply pureTyped_congr _ rfl rfl
    intro x hx
    obtain ⟨d, t, hd, -⟩ := avail_transfer hD hw hu hn hci (hW.uses i b hbi j st hst x hx)
    exact types_eq hw hu (new_defined hw hu hd)
  · intro i' b hb v hv
    obtain ⟨i, hci, hbi, -⟩ := corr_of_new hb
    exact avail_transfer hD hw hu hn hci (hW.termUses i b hbi v hv)
  · intro i' b hb id hid
    obtain ⟨i, hci, hbi, hri⟩ := corr_of_new hb
    obtain ⟨j, b', -, hbj, hid', -⟩ := hW.edges i b hbi id hid
    have hjs : j ∈ (Cfg.build f).succs[i]! := (build_succs_mem f hbi).2 ⟨id, hid, by
      rw [Std.HashMap.get?_eq_getElem?]
      exact build_index_of_nodup hids (by simp [blockIds, hbj, hid'])⟩
    have hil := reachable_lt hri
    have hrj := reach_reachable hn (.step (reachable_reach hil hri) hjs)
    obtain ⟨j', hcj, hbj'⟩ := corr_of_old hbj hrj
    refine ⟨j', b', ?_, hbj', hid', fun y hy => ?_⟩
    · show (Cfg.build (removeUnreachableRaw f)).index.get? id = some j'
      rw [Std.HashMap.get?_eq_getElem?]
      exact build_index_of_nodup (raw_ids hids) (by simp [blockIds, hbj', hid'])
    · have hil' := (List.getElem?_eq_some_iff.1 hb).1
      exact hD.edge i' j' (raw_reachable hw hn hil') ((corr_edge hids hci hcj).2 hjs) y hy

include hD hw hu hn in
/-- **`checkCore` accepts the output.** -/
theorem raw_coreOk
    (hentry : ∀ b, f.blocks.head? = some b → b.params.map (·.2) = f.sig.params.map (·.ty))
    (hcalls : ∀ b ∈ f.blocks, ∀ bc ∈ termCalls b.term, ∀ b' ∈ f.blocks, b'.id = bc.block →
      (b'.params.length == bc.args.length &&
        (b'.params.zip bc.args).all fun x => types.get? x.2 == some x.1.2) = true)
    (hbr : ∀ b ∈ f.blocks, brTableOk types b.term) : CoreOk (removeUnreachableRaw f) := by
  have hids := old_ids hw
  have hwf := raw_wf hD hw hu hn
  have hlen0 : 0 < (removeUnreachableRaw f).blocks.length := by
    obtain ⟨b, hb, -⟩ := corr_zero hn
    exact (List.getElem?_eq_some_iff.1 hb).1
  have hterm : ∀ (i' : Nat) (b : Block), (removeUnreachableRaw f).blocks[i']? = some b → ∀ v ∈ termOperands b.term,
      (defsState (removeUnreachableRaw f)).1.get? v = types.get? v := by
    intro i' b hb v hv
    obtain ⟨d, t, hd, -⟩ := hwf.termUses i' b hb v hv
    exact types_eq hw hu (new_defined hw hu hd)
  refine coreOk_of_wf (by rw [build_size']; exact hlen0) (build_index_size (raw_ids hids))
    (fun i hi => raw_reachable hw hn (by rw [build_size'] at hi; exact hi)) ?_ ?_ hwf ?_ ?_
  · rw [defsOk_iff]
    exact ⟨raw_arity hw, (allAlong_evC_iff _ _).2 ⟨fun e _ => by simp, raw_nodup hw hu⟩⟩
  · obtain ⟨b0, hb0G, hb0f⟩ := corr_zero hn
    have : (removeUnreachableRaw f).blocks.toArray[0]! = b0 := by
      simp [getElem!_def, List.getElem?_toArray, hb0G]
    rw [this]
    exact hentry b0 (by rw [List.head?_eq_getElem?]; exact hb0f)
  · intro i' b hb bc hbc
    obtain ⟨j', b', hj', hbj', hid', -⟩ := hwf.edges i' b hb bc.block (termCalls_succ hbc)
    refine ⟨j', hj', ?_⟩
    have harr : (removeUnreachableRaw f).blocks.toArray[j']! = b' := by
      simp [getElem!_def, List.getElem?_toArray, hbj']
    rw [harr]
    have h := hcalls b ((raw_sublist f).subset (List.mem_of_getElem? hb)) bc hbc b'
      ((raw_sublist f).subset (List.mem_of_getElem? hbj')) hid'
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h ⊢
    refine ⟨h.1, fun x hx => ?_⟩
    rw [hterm i' b hb x.2 (termCalls_args hbc (List.of_mem_zip hx).2)]
    exact h.2 x hx
  · intro b hb
    obtain ⟨i', hb'⟩ := List.mem_iff_getElem?.1 hb
    have h := hbr b ((raw_sublist f).subset hb)
    revert h
    cases ht : b.term <;> simp only [brTableOk, imp_self]
    intro h
    rw [hterm i' b hb' _ (brTable_operand ht)]; exact h

end Transfer

/-- **`check` accepts `removeUnreachable f`** when `f` passes the certificate against some CFG
`cfg` (as the simplify validator `simpOk` establishes, with the input's CFG), its values are
defined once, the entry block's parameters match the signature, branch arities and argument
types (by `types`) match the targets' parameters, and `br_table` indices are `i32` — given the
facts `DomFacts` of the output's dominator tree. -/
theorem check_removeUnreachable_of_wfCert {f : Function} {cfg : Cfg}
    {types : Std.HashMap ValueId Ty}
    (hD : DomFacts (Cfg.build (removeUnreachableRaw f)))
    (hw : wfCert f cfg types = true) (hu : UniqueDefs f) (hn : f.blocks ≠ [])
    (hentry : ∀ b, f.blocks.head? = some b → b.params.map (·.2) = f.sig.params.map (·.ty))
    (hcalls : ∀ b ∈ f.blocks, ∀ bc ∈ termCalls b.term, ∀ b' ∈ f.blocks, b'.id = bc.block →
      (b'.params.length == bc.args.length &&
        (b'.params.zip bc.args).all fun x => types.get? x.2 == some x.1.2) = true)
    (hbr : ∀ b ∈ f.blocks, brTableOk types b.term) :
    check (removeUnreachable f) = .ok (coreInfo (removeUnreachable f)) := by
  rw [removeUnreachable_eq_raw (blocksOkB_of_wfCert hw)]
  have hw' : wfCert (removeUnreachableRaw f) (coreInfo (removeUnreachableRaw f)).cfg
      (coreInfo (removeUnreachableRaw f)).types = true :=
    wfCert_complete (raw_wf hD hw hu hn)
  exact (check_ok_iff _ _).2 ⟨raw_coreOk hD hw hu hn hentry hcalls hbr, rfl, hw'⟩

end Opt

namespace Opt.CompleteRecheckWitness

open Clif

/-- Before simplification: `block0` branches on `v0` to `block1` or `block2`, both jump to
`block3`, which returns `v0`. -/
def fn0 : Function where
  name := "w"
  sig := { params := [{ ty := .i32 }], returns := [{ ty := .i32 }] }
  blocks := [{ id := 0, params := [(0, .i32)], term := .brif 0 { block := 1 } { block := 2 } },
    { id := 1, term := .jump { block := 3 } }, { id := 2, term := .jump { block := 3 } },
    { id := 3, term := .ret [0] }]

/-- After a skeleton rewrite of the branch into `jump block1`: `block2` is unreachable, and
`block1` now dominates `block3`. -/
def fn : Function :=
  { fn0 with blocks := [{ id := 0, params := [(0, .i32)], term := .jump { block := 1 } },
    { id := 1, term := .jump { block := 3 } }, { id := 2, term := .jump { block := 3 } },
    { id := 3, term := .ret [0] }] }

theorem idom_eq : (Cfg.build (removeUnreachableRaw fn)).idom = #[none, some 0, some 1] := by
  native_decide

theorem succs_eq : (Cfg.build (removeUnreachableRaw fn)).succs = #[[1], [2], []] := by
  native_decide

theorem rpoNum_eq : (Cfg.build (removeUnreachableRaw fn)).rpoNum = #[some 0, some 1, some 2] := by
  native_decide

theorem size_eq : (Cfg.build (removeUnreachableRaw fn)).size = 3 := by native_decide

theorem idom_lt {b x : Nat} (h : (Cfg.build (removeUnreachableRaw fn)).idom[b]?.join = some x) :
    (b = 1 ∧ x = 0) ∨ (b = 2 ∧ x = 1) := by
  rw [idom_eq] at h
  rcases b with _ | _ | _ | b <;> simp at h
  · exact .inl ⟨rfl, h.symm⟩
  · exact .inr ⟨rfl, h.symm⟩

/-- The facts of the output's dominator tree, checked on the concrete CFG. -/
theorem domFacts : DomFacts (Cfg.build (removeUnreachableRaw fn)) where
  lt b x h := by
    rw [size_eq]; rcases idom_lt h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  root := by rw [idom_eq]; rfl
  rank b x h := by
    rw [rpoNum_eq]; rcases idom_lt h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  edge u x hu hx y hy := by
    have hul := reachable_lt hu
    have hl : (removeUnreachableRaw fn).blocks.length = 3 := by native_decide
    rw [hl] at hul
    rw [succs_eq] at hx
    rcases u with _ | _ | _ | u
    · simp at hx; subst hx
      rcases idom_lt hy with ⟨h, rfl⟩ | ⟨h, -⟩
      · exact .refl _
      · cases h
    · simp at hx; subst hx
      rcases idom_lt hy with ⟨h, -⟩ | ⟨-, rfl⟩
      · cases h
      · exact .refl _
    · simp at hx
    · omega
  complete a b hb ha hra := by
    have hbl := reachable_lt hb
    have hl : (removeUnreachableRaw fn).blocks.length = 3 := by native_decide
    rw [hl] at hbl
    rw [size_eq] at ha
    have h01 : 1 ∈ (Cfg.build (removeUnreachableRaw fn)).succs[0]! := by rw [succs_eq]; decide
    have anc : ∀ a b, ancB #[none, some 0, some 1] 3 a b = true →
        Anc (Cfg.build (removeUnreachableRaw fn)).idom a b := by
      intro a b h; rw [idom_eq]; exact ancB_sound h
    rcases a with _ | _ | _ | a <;> rcases b with _ | _ | _ | b
    all_goals first
      | omega
      | exact anc _ _ (by decide)
      | exact absurd (.entry (by decide)) hra
      | exact absurd (.step (.entry (by decide)) h01 (by decide)) hra

/-- Non-vacuity of `check_removeUnreachable_of_wfCert`: `fn` (whose branch was rewritten, making
`block2` unreachable and changing the dominator of `block3` from `block0` to `block1`) passes the
certificate against the CFG of `fn0`, and `check` accepts `removeUnreachable fn`. -/
theorem witness :
    (removeUnreachable fn).blocks.map (·.id) = [0, 1, 3] ∧
    (Cfg.build fn0).idom[3]! = some 0 ∧ (Cfg.build (removeUnreachable fn)).idom[2]! = some 1 ∧
    wfCert fn (Cfg.build fn0) (defsState fn0).1 = true ∧
    check (removeUnreachable fn) = .ok (coreInfo (removeUnreachable fn)) := by
  have hw : wfCert fn (Cfg.build fn0) (defsState fn0).1 = true := by native_decide
  refine ⟨by native_decide, by native_decide, by native_decide, hw, ?_⟩
  refine check_removeUnreachable_of_wfCert domFacts hw (by unfold UniqueDefs; native_decide)
    (by simp [fn, fn0]) ?_ (by native_decide) ?_
  · intro b hb
    simp only [fn, List.head?_cons, Option.some.injEq] at hb
    subst hb; rfl
  · intro b hb
    simp only [fn, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> trivial

end Opt.CompleteRecheckWitness
