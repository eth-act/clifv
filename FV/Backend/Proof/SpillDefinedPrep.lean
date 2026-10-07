import FV.Backend.Proof.SpillDefined
import FV.Backend.Proof.KillPrep
import FV.Backend.Proof.SpillEdgesPrep

/-!
# Definedness sets across `prepare`

`defAvail_prepare`: on `lowerFunction`'s VCode (`LowOk`), definedness sets `M` of the input with
nothing defined on entry give definedness sets `M'` of `prepare`'s output with nothing defined on
entry. A block of the output takes the set of the block of the input it comes from (`srcOf`: a
kept block's label is its index in the input), an edge block `jump l` splitting an edge `b → l`
takes the set `M l` of its target. Retargeting keeps operands, so a kept block defines what it did;
its entry stores only grow (`entryStored_prep`, as in `killFreeB_prepare`). A split edge leaves a
block with at least two successors, hence without branch arguments: the target of a split edge
has no parameter defined by the edge, so `M l` holds at the end of `b` and passes unchanged through
the parameterless edge block and its `jump` (no defs, no branch arguments) into `l`.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

namespace DefPrep

/-! ## Monotonicity of the definedness transfer -/

theorem defInst_mono (i : MInst) {A A' : Nat → Bool} (hA : ∀ x, A x = true → A' x = true)
    {v : Nat} (h : defInst i A v = true) : defInst i A' v = true := by
  cases hop : i.operands with
  | error _ => simp only [defInst, hop] at h ⊢; exact hA v h
  | ok ops =>
    simp only [defInst, hop] at h ⊢
    by_cases hc : ((ops.toList.filter (·.kind == .def)).any (·.vreg == v)) = true
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact hA v h

theorem defInst_ge (i : MInst) {A : Nat → Bool} {v : Nat} (h : A v = true) :
    defInst i A v = true := by
  cases hop : i.operands with
  | error _ => simp only [defInst, hop]; exact h
  | ok ops =>
    simp only [defInst, hop]
    by_cases hc : ((ops.toList.filter (·.kind == .def)).any (·.vreg == v)) = true
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact h

theorem foldl_mono : ∀ (l : List MInst) {A A' : Nat → Bool}, (∀ x, A x = true → A' x = true) →
    ∀ x, l.foldl (fun A i => defInst i A) A x = true → l.foldl (fun A i => defInst i A) A' x = true
  | [], _, _, hA => hA
  | i :: l, _, _, hA => foldl_mono l (fun _ => defInst_mono i hA)

theorem foldl_ge : ∀ (l : List MInst) {A : Nat → Bool} {x : Nat}, A x = true →
    l.foldl (fun A i => defInst i A) A x = true
  | [], _, _, h => h
  | i :: l, _, _, h => foldl_ge l (defInst_ge i h)

theorem defAt_mono (insts : Array MInst) {A A' : Nat → Bool}
    (hA : ∀ x, A x = true → A' x = true) (k : Nat) :
    ∀ x, defAt insts A k x = true → defAt insts A' k x = true :=
  foldl_mono _ hA

theorem defAt_ge (insts : Array MInst) {A : Nat → Bool} (k : Nat) {x : Nat} (h : A x = true) :
    defAt insts A k x = true :=
  foldl_ge _ h

theorem defInst_ops {i i' : MInst} (h : i'.operands = i.operands) (A : Nat → Bool) :
    defInst i' A = defInst i A := by
  funext v; simp only [defInst, h]

theorem foldl_ops : ∀ (l l' : List MInst), l'.map MInst.operands = l.map MInst.operands →
    ∀ A : Nat → Bool, l'.foldl (fun A i => defInst i A) A = l.foldl (fun A i => defInst i A) A
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | i :: l, i' :: l', h, A => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.foldl_cons]
    rw [defInst_ops h.1]
    exact foldl_ops l l' h.2 _

/-- Definedness through instructions with the same operands. -/
theorem defAt_ops {xs ys : Array MInst}
    (h : xs.toList.map MInst.operands = ys.toList.map MInst.operands) (A : Nat → Bool) (k : Nat) :
    defAt xs A k = defAt ys A k := by
  unfold defAt
  exact foldl_ops _ _ (by rw [List.map_take, List.map_take, h]) A

theorem ops_get {xs ys : Array MInst}
    (h : xs.toList.map MInst.operands = ys.toList.map MInst.operands) {k : Nat} {i : MInst}
    (hi : xs[k]? = some i) : ∃ j, ys[k]? = some j ∧ j.operands = i.operands := by
  have := congrArg (·[k]?) h
  simp only [List.getElem?_map, Array.getElem?_toList, hi, Option.map_some] at this
  cases hy : ys[k]? with
  | none => rw [hy] at this; cases this
  | some j => rw [hy] at this; exact ⟨j, rfl, (Option.some.inj this).symm⟩

/-! ## Edges -/

theorem edgeAvail_mono {vb vb' sb sb' : VBlock} {A A' : Nat → Bool} (hp : sb'.params = sb.params)
    (ha : vb'.branchArgs = vb.branchArgs) (hA : ∀ x, A x = true → A' x = true) {v : Nat}
    (h : edgeAvail vb sb A v = true) : edgeAvail vb' sb' A' v = true := by
  unfold edgeAvail at *
  rw [hp, ha]
  cases hk : (sb.params.toList.map Reg.homeNum).idxOf? v with
  | none => rw [hk] at h; exact hA v h
  | some k =>
    rw [hk] at h
    simp only at h ⊢
    cases hb : vb.branchArgs[k]? with
    | none => rw [hb] at h; cases h
    | some a => rw [hb] at h; exact hA _ h

/-- Along an edge without branch arguments, a vreg delivered to the target is defined at the end
of the source. -/
theorem edgeAvail_noArgs {vb sb : VBlock} {A : Nat → Bool} (ha : vb.branchArgs = #[]) {v : Nat}
    (h : edgeAvail vb sb A v = true) : A v = true := by
  unfold edgeAvail at h
  split at h
  · rw [ha] at h; simp at h
  · exact h

theorem edgeAvail_noParams {vb sb : VBlock} {A : Nat → Bool} (hp : sb.params = #[]) (v : Nat) :
    edgeAvail vb sb A v = A v := by
  simp [edgeAvail, hp]

theorem jump_noUse {l : Label} {ops : Array Operand} (h : (MInst.jump l).operands = .ok ops)
    {o : Operand} (ho : o ∈ ops.toList) (hu : o.kind = .use) : False := by
  have e : useVregs (.jump l) = [] := rfl
  simp only [useVregs, h] at e
  have : o.vreg ∈ (ops.toList.filter (·.kind == .use)).map (·.vreg) :=
    List.mem_map.mpr ⟨o, List.mem_filter.mpr ⟨ho, by simp [hu]⟩, rfl⟩
  rw [e] at this
  cases this

/-! ## The witness sets -/

/-- The block of the input whose definedness set block `vb` of `prepare`'s output takes (`n`: the
first edge-block label): a kept block's label, an edge block's target. -/
def srcOf (n : Nat) (vb : VBlock) : Nat :=
  if vb.label < n then vb.label else
    match vb.insts.back? with
    | some (.jump l) => l
    | _ => 0

/-- The definedness sets of the blocks `V` of `prepare`'s output, from those `M` of the input. -/
def prepSets (V : Array VBlock) (n : Nat) (M : Nat → Nat → Bool) (q v : Nat) : Bool :=
  match V[q]? with
  | some vb => M (srcOf n vb) v
  | none => false

theorem prepSets_of {V : Array VBlock} {n : Nat} {M : Nat → Nat → Bool} {q : Nat} {vb : VBlock}
    (h : V[q]? = some vb) : prepSets V n M q = M (srcOf n vb) := by
  funext v; simp [prepSets, h]

theorem srcOf_jump {n lbl : Nat} {l : Label} (h : n ≤ lbl) :
    srcOf n { label := lbl, insts := #[.jump l] } = l := by
  simp [srcOf, Array.back?, Nat.not_lt.mpr h]

end DefPrep

open KillPrep DefPrep

section main
variable {vc : VCode} (hv : LowOk vc) {ss0 ps0 ss1 ps1 ss2 : Array (Array Nat)} {next : Nat}
  {B E : Array VBlock}
  (hc0 : vc.cfg = .ok (ss0, ps0))
  (hc1 : ({ vc with blocks := Prep.keep vc.blocks (reachable ss0) } : VCode).cfg = .ok (ss1, ps1))
  (cs2 : Prep.CfgSpec (B ++ E) ss2)
  (hS : Prep.SInv (Prep.keep vc.blocks (reachable ss0))
    (Prep.next0Of (Prep.keep vc.blocks (reachable ss0))) (Prep.keep vc.blocks (reachable ss0)).size
    (next, B, E))

local notation "V1" => Prep.keep vc.blocks (reachable ss0)
local notation "N0" => Prep.next0Of (Prep.keep vc.blocks (reachable ss0))
local notation "V3" => Array.map (fun i => (B ++ E)[i]!) (rpo ss2)

include hS in
theorem srcOf_kept {k : Nat} (hk : k < (V1).size) (hkB : k < B.size) :
    srcOf N0 B[k] = (V1)[k].label := by
  simp only [srcOf, (b_fields hS hk hkB).1, Prep.lt_next0 hk, ↓reduceIte]

include hS in
theorem srcOf_E {e : Nat} {eb : VBlock} (he : E[e]? = some eb) :
    ∃ l, eb.insts = #[.jump l] ∧ srcOf N0 eb = l := by
  obtain ⟨h1, -, -, l, h4⟩ := e_blk hS he
  refine ⟨l, h4, ?_⟩
  have hn : ¬ (N0 + e < N0) := by omega
  unfold srcOf
  rw [h1, h4]
  simp [Array.back?, hn]

include hS in
/-- A kept block's instructions have the operands of the input block's. -/
theorem ops_kept {k : Nat} (hk : k < (V1).size) (hkB : k < B.size) :
    B[k].insts.toList.map MInst.operands = (V1)[k].insts.toList.map MInst.operands := by
  rcases hS.rw k hk hkB with h | ⟨t, t', ls, h1, -, h3, h4, -⟩
  · rw [h]
  · rw [h4]
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp h1
    rw [hys, Array.pop_push]
    simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
      (setTargets_inv h3).1]

include hv hc0 hc1 cs2 hS in
/-- **The entry stores of a kept block grow** across `prepare` (`killFreeB_prepare`). -/
theorem entryStored_prep {ss3 ps3 : Array (Array Nat)}
    (hns : NoSplit V1 B ss1 ps1)
    (hc3 : ({ vc with blocks := V3 } : VCode).cfg = .ok (ss3, ps3))
    (hed : EdgesOk { vc with blocks := V3 } ss3 ps3)
    {b k : Nat} (hk : k < (V1).size) (hkB : k < B.size) (hvb : (V3)[b]? = some B[k])
    {b0 : Nat} (hb0 : b0 < vc.blocks.size) (e0 : (V1)[k] = vc.blocks[b0]) {v : Nat}
    (hst : v ∈ entryStored vc ss0 ps0 b0) :
    v ∈ entryStored { vc with blocks := V3 } ss3 ps3 b := by
  have cs0 := Prep.cfg_spec hc0
  have cs1 : Prep.CfgSpec (V1) ss1 := Prep.cfg_spec hc1
  have cs3 : Prep.CfgSpec (V3) ss3 := Prep.cfg_spec hc3
  have hd := hv.prepDomain
  obtain ⟨h10, -, hn1, hn2, hR, hRn, -⟩ := basics hv cs0 cs2 hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hRre⟩ := Prep.facts_basic hd cs0 cs2 hS
  have hs0 : ss0.size ≠ 0 := by rw [cs0.size]; have := hv.nonempty; omega
  have hb0' := Array.getElem?_eq_getElem hb0
  have hlb0 : vc.blocks[b0].label = b0 := hv.labels b0 _ hb0'
  obtain ⟨b1, hb1, e1, hmk⟩ := Prep.keep_src hk
  obtain rfl : b1 = b0 := by
    rw [← hv.labels b1 _ (Array.getElem?_eq_getElem hb1), ← e1, e0, hlb0]
  -- the only predecessor `p` of `b0`, a `try_call`, successor number `j`
  obtain ⟨p, vp, sp, j, hpp, hvp, hsp, hj, hmem⟩ := entryStored_inv hst
  obtain ⟨hjlt, hjget, -⟩ := List.idxOf?_eq_some_iff.mp hj
  have hspj : sp[j]? = some b1 := by
    rw [Array.getElem?_eq_getElem (by simpa using hjlt)]; simpa using hjget
  obtain ⟨t, tsp, ht, -, hts, htsz, hlt⟩ := cs0.blk p vp hvp
  rw [hsp] at hts; cases hts
  have hjl : j < t.targets.length := by
    rw [← htsz]; exact (Array.getElem?_eq_some_iff.mp hspj).1
  have htj : t.targets[j]? = some b1 := by
    obtain ⟨k', hk', hlab⟩ := hlt j _ (List.getElem?_eq_getElem hjl)
    rw [hspj] at hk'; cases hk'
    obtain ⟨hb0'', hlb⟩ := Prep.lab_some hlab
    rw [List.getElem?_eq_getElem hjl, ← hlb, hv.labels b1 _ (Array.getElem?_eq_getElem hb0'')]
  obtain ⟨info, ti, rfl⟩ := tryCall_of_termEdgeDefs ht
    (fun h => by rw [h] at hmem; simp at hmem) (fun h => by rw [h] at htj; simp at htj)
  -- `p` is reachable
  have hr0 : Prep.Reach ss0 b1 := (Prep.reachable_spec (Prep.succsIn_of cs0) hs0).2.2.2 b1 hmk
  have hrp : Prep.Reach ss0 p := by
    cases hr0 with
    | entry => exact absurd (List.mem_of_getElem? htj) (hv.noEntry p vp _ hvp ht)
    | step hr hs =>
      obtain ⟨sb, j', hsb, hj'⟩ := mem_getElem! hs
      obtain ⟨rfl, -⟩ := preds_single hc0 hsb hj' hpp
      exact hr
  obtain ⟨kp, hkp, hpl, ekp, hr1⟩ := Prep.reach01 cs0 cs1 hd.labels hv.nonempty hrp
  obtain ⟨-, hr2⟩ := Prep.reach12 hS cs1 cs2 hn1 h10 hr1
  have hvp' : vc.blocks[p] = vp :=
    Option.some.inj ((Array.getElem?_eq_getElem hpl).symm.trans hvp)
  obtain ⟨hkpB, t0, t', ht0, ht', -, -, -, -, -, hsame, -, -⟩ := Prep.blk2 hS cs1 hkp
  rw [ekp, hvp', ht] at ht0
  cases ht0
  -- in the kept blocks, `kp → k` is the only edge into `k`: it is not split
  have hlabk : Prep.lab (V1) b1 = some k :=
    Prep.lab_of hn1 hk (by rw [e0, hlb0])
  obtain ⟨t1, ts1, ht1, -, hts1, -, hl1⟩ := cs1.blk kp _ (Array.getElem?_eq_getElem hkp)
  rw [ekp, hvp', ht] at ht1
  cases ht1
  obtain ⟨k', hk', hlab'⟩ := hl1 j b1 htj
  rw [hlabk] at hlab'
  cases hlab'
  have hps1 : ps1[k]? = some #[kp] := by
    refine preds_one hc1 hk hts1 hk' fun q sq j2 hq hj2 => ?_
    obtain ⟨vbq, tq, lq, hvbq, htq, htqj, hlabq⟩ := succ3 cs1 hq hj2
    obtain ⟨hkq, hlq⟩ := Prep.lab_some hlabq
    have hqV : q < (V1).size := (Array.getElem?_eq_some_iff.mp hvbq).1
    obtain ⟨bq, hbq, eq, -⟩ := Prep.keep_src hqV
    have hvbq' : vbq = vc.blocks[bq] := by
      rw [← eq]; exact (Option.some.inj ((Array.getElem?_eq_getElem hqV).symm.trans hvbq)).symm
    subst hvbq'
    have hlq' : b1 = lq := by rw [← hlq, e0, hlb0]
    subst hlq'
    obtain ⟨tq', sq0, htq', -, hsq0, -, hlq0⟩ := cs0.blk bq _ (Array.getElem?_eq_getElem hbq)
    rw [htq] at htq'
    cases htq'
    obtain ⟨u, hu, hlabu⟩ := hlq0 j2 _ htqj
    have hub : b1 = u := by
      rw [Prep.lab_of hd.labels hb1 hlb0] at hlabu; exact Option.some.inj hlabu
    subst hub
    obtain ⟨rfl, -⟩ := preds_single hc0 hsq0 hu hpp
    obtain ⟨-, huj⟩ := preds_single hc0 hsp hspj hpp
    refine ⟨Prep.lbl_inj hn1 hqV hkp (by rw [eq, ekp]), ?_⟩
    rw [hsq0] at hsp
    cases hsp
    exact huj j2 hu
  have hss1 : (ss1[kp]! : Array Nat)[j]? = some k := by
    rw [show (ss1[kp]! : Array Nat) = ts1 by simp [getElem!_def, hts1]]; exact hk'
  have hnot : ¬ (ps1[k]! : Array Nat).size > 1 := by
    rw [show (ps1[k]! : Array Nat) = #[kp] by simp [getElem!_def, hps1]]; simp
  have htj' := hns kp hkp hkpB _ t' j k b1 (by rw [ekp, hvp', ht]) ht' htj hss1 hnot
  obtain ⟨ti', rfl⟩ : ∃ ti', t' = .tryCall info ti' := by
    rcases hsame with h | h
    · exact ⟨ti, h⟩
    · exact setTargets_tryCall h
  -- in the output: the block `q` of `kp` is the only predecessor of `b`, successor number `j`
  obtain ⟨q, hq, hRq, -⟩ := Prep.lab3 hR hn2 hRn (hRre kp hr2)
  have hq3 : (V3)[q]? = some B[kp] := by
    obtain ⟨hi, e⟩ := Prep.v3_get hR hq
    rw [e]; congr 1; simp only [hRq]; exact Array.getElem_append_left hkpB
  obtain ⟨t3, ts3, ht3, -, hts3, -, hl3⟩ := cs3.blk q _ hq3
  rw [ht'] at ht3
  cases ht3
  obtain ⟨u, hu, hlabu⟩ := hl3 j b1 htj'
  have hub : u = b := by
    have hb3 : b < (V3).size := (Array.getElem?_eq_some_iff.mp hvb).1
    have := Prep.lab_of (Prep.lbls3 hR hn2 hRn) hb3 (l := b1) (by
      rw [Option.some.inj ((Array.getElem?_eq_getElem hb3).symm.trans hvb),
        (b_fields hS hk hkB).1, e0, hlb0])
    rw [this] at hlabu; exact (Option.some.inj hlabu).symm
  subst hub
  have hps3 : ps3[u]? = some #[q] :=
    (hed.tryEdge q B[kp] info ti' ts3 u hq3 ht').2 hts3
      (by simpa using Array.mem_of_getElem? hu)
  obtain ⟨-, huj3⟩ := preds_single hc3 hts3 hu hps3
  have hidx : ts3.toList.idxOf? u = some j :=
    idxOf?_of_unique (by simpa using hu) (fun j' h => huj3 j' (by simpa using h))
  rw [entryStored_of (vc := { vc with blocks := V3 }) hps3 hq3 hts3 hidx,
    termEdgeDefs_same (vb := vp) ht ht' hsame j]
  simpa using hmem

end main

/-- **Definedness sets across `prepare`**: definedness sets of `lowerFunction`'s VCode (`LowOk`)
with nothing defined on entry give such sets of `prepare`'s output. -/
theorem defAvail_prepare {vc vcp : VCode} (hv : LowOk vc) (hp : prepare vc = .ok vcp)
    {M : Nat → Nat → Bool} (hM : DefAvail vc M) (h0 : ∀ v, M 0 v = false) :
    ∃ M', DefAvail vcp M' ∧ ∀ v, M' 0 v = false := by
  have hed := edgesOk_prepare hv hp
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl, hns⟩ :=
    prepare_facts_ns hp
  have cs0 := Prep.cfg_spec hc0
  have cs1 : Prep.CfgSpec (Prep.keep vc.blocks (reachable ss0)) ss1 := Prep.cfg_spec hc1
  have cs2 : Prep.CfgSpec (B ++ E) ss2 := Prep.cfg_spec hc2
  obtain ⟨h10, hV0, hn1, hn2, hR, hRn, hR0⟩ := basics hv cs0 cs2 hS
  -- the sets of the kept blocks' starts grow
  have hstart : ∀ succs preds,
      ({ vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } : VCode).cfg = .ok (succs, preds) →
      ∀ q k (hk : k < (Prep.keep vc.blocks (reachable ss0)).size) (hkB : k < B.size) b0
        (hb0 : b0 < vc.blocks.size),
      ((rpo ss2).map fun i => (B ++ E)[i]!)[q]? = some B[k] →
      (Prep.keep vc.blocks (reachable ss0))[k] = vc.blocks[b0] → ∀ x,
      defStart vc ss0 ps0 M b0 x = true →
      defStart { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! } succs preds
        (prepSets ((rpo ss2).map fun i => (B ++ E)[i]!)
          (Prep.next0Of (Prep.keep vc.blocks (reachable ss0))) M) q x = true := by
    intro succs preds hc3 q k hk hkB b0 hb0 hq e0 x hx
    unfold defStart at hx ⊢
    rw [prepSets_of hq, srcOf_kept hS hk hkB, e0, hv.labels b0 _ (Array.getElem?_eq_getElem hb0)]
    simp only [Bool.or_eq_true, List.contains_iff_mem] at hx ⊢
    rcases hx with hx | hx
    · exact .inl hx
    · exact .inr (entryStored_prep hv hc0 hc1 cs2 hS hns hc3 (hed succs preds hc3) hk hkB hq hb0
        e0 hx)
  refine ⟨prepSets ((rpo ss2).map fun i => (B ++ E)[i]!)
    (Prep.next0Of (Prep.keep vc.blocks (reachable ss0))) M, ⟨?_, ?_⟩, ?_⟩
  · -- uses
    intro succs preds hc3 q vb' k i' ops hvb' hi' hops o ho hu
    change ((rpo ss2).map fun i => (B ++ E)[i]!)[q]? = some vb' at hvb'
    rcases cls3 hv cs0 cs1 cs2 hS hvb' with ⟨kk, hk, hkB, -, rfl⟩ | ⟨e, -, he, -⟩
    · obtain ⟨b0, hb0, e0, -⟩ := v1_vc hv hk
      have hops_eq := ops_kept hS hk hkB
      rw [e0] at hops_eq
      obtain ⟨i, hi, hio⟩ := ops_get hops_eq hi'
      have := hM.uses ss0 ps0 hc0 b0 _ k i ops (Array.getElem?_eq_getElem hb0) hi
        (by rw [hio, hops]) o ho hu
      rw [defAt_ops hops_eq]
      exact defAt_mono _ (hstart succs preds hc3 q kk hk hkB b0 hb0 hvb' e0) k _ this
    · obtain ⟨-, -, -, l, hl⟩ := e_blk hS he
      rw [hl] at hi'
      have hk0 : k = 0 := by
        have := (Array.getElem?_eq_some_iff.mp hi').1; simp at this; omega
      subst hk0
      simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi'
      subst hi'
      exact (jump_noUse hops ho hu).elim
  · -- edges
    intro succs preds hc3 q vb' ss' s sb' hvb' hss hs hsb' v hv'
    change ((rpo ss2).map fun i => (B ++ E)[i]!)[q]? = some vb' at hvb'
    change ((rpo ss2).map fun i => (B ++ E)[i]!)[s]? = some sb' at hsb'
    have cs3 : Prep.CfgSpec ((rpo ss2).map fun i => (B ++ E)[i]!) succs := Prep.cfg_spec hc3
    obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hs
    have hj' : ss'[j]? = some s := by simp [← hjs]
    obtain ⟨vb'', t3, l', hvb'', ht3, htj3, hlab⟩ := succ3 cs3 hss hj'
    rw [hvb'] at hvb''; cases hvb''
    obtain ⟨hsl, hsl'⟩ := Prep.lab_some hlab
    have hsbl : sb'.label = l' := by
      rw [← hsl', Option.some.inj ((Array.getElem?_eq_getElem hsl).symm.trans hsb')]
    rw [prepSets_of hsb'] at hv'
    -- a target below the edge labels is a kept block, taking the set of its label
    have hkept : ∀ l, l < Prep.next0Of (Prep.keep vc.blocks (reachable ss0)) → sb'.label = l →
        l < vc.blocks.size ∧ sb'.params = vc.blocks[l]!.params ∧ srcOf
          (Prep.next0Of (Prep.keep vc.blocks (reachable ss0))) sb' = l := by
      intro l hl hsl
      rcases cls3 hv cs0 cs1 cs2 hS hsb' with ⟨k', hk', hkB', -, rfl⟩ | ⟨e, -, he, -⟩
      · obtain ⟨hl', hp', -⟩ := b_fields hS hk' hkB'
        obtain ⟨b', hb', e', hlb'⟩ := v1_vc hv hk'
        have hbl : b' = l := by rw [← hlb', ← hl', hsl]
        subst hbl
        refine ⟨hb', ?_, by rw [srcOf_kept hS hk' hkB', hlb']⟩
        rw [hp', e', getElem!_pos vc.blocks b' hb']
      · have := (e_blk hS he).1
        lomega
    rcases cls3 hv cs0 cs1 cs2 hS hvb' with ⟨kk, hk, hkB, -, rfl⟩ |
      ⟨e, -, he, ⟨l'', l1, kk, m, hkk, -, t1, -, he', ht1, -, -, hm, h2⟩⟩
    · obtain ⟨hkB0, t, t', ht, ht', -, -, -, hsz, -, -, -, hrel⟩ := Prep.blk2 hS cs1 hk
      rw [ht'] at ht3
      cases ht3
      obtain ⟨l, hl, hc⟩ := hrel j l' htj3
      obtain ⟨-, -, -, hlN⟩ := tgt_v1 cs1 hk ht hl
      obtain ⟨b0, hb0, e0, -⟩ := v1_vc hv hk
      have hb0' := Array.getElem?_eq_getElem hb0
      rw [e0] at ht
      obtain ⟨t0, ts0, ht0, -, hts0, -, hl0⟩ := cs0.blk b0 _ hb0'
      rw [ht] at ht0; cases ht0
      obtain ⟨u, hu, hlabu⟩ := hl0 j l hl
      obtain ⟨hul, hlu⟩ := Prep.lab_some hlabu
      have hul' : u = l := by rw [← hlu, hv.labels u _ (Array.getElem?_eq_getElem hul)]
      subst hul'
      have hum : u ∈ ts0.toList := by simpa using Array.mem_of_getElem? hu
      have hEo := hM.edges ss0 ps0 hc0 b0 _ ts0 u _ hb0' hts0 hum
        (Array.getElem?_eq_getElem hul) v
      have hops_eq := ops_kept hS hk hkB
      rw [e0] at hops_eq
      have hAA : ∀ x, defAt vc.blocks[b0].insts (defStart vc ss0 ps0 M b0)
          vc.blocks[b0].insts.size x = true →
          defAt B[kk].insts (defStart { vc with blocks := (rpo ss2).map fun i => (B ++ E)[i]! }
            succs preds (prepSets ((rpo ss2).map fun i => (B ++ E)[i]!)
              (Prep.next0Of (Prep.keep vc.blocks (reachable ss0))) M) q)
            B[kk].insts.size x = true := by
        intro x hx
        rw [hsz, e0, defAt_ops hops_eq]
        exact defAt_mono _ (hstart succs preds hc3 q kk hk hkB b0 hb0 hvb' e0) _ _ hx
      rcases hc with rfl | ⟨h2, e, he⟩
      · -- an edge kept as is
        obtain ⟨-, hpar, hsrc⟩ := hkept _ hlN hsbl
        rw [hsrc] at hv'
        refine edgeAvail_mono (vb := vc.blocks[b0]) (sb := vc.blocks[l']) ?_ ?_ hAA (hEo hv')
        · rw [hpar, getElem!_pos vc.blocks l' hul]
        · rw [(b_fields hS hk hkB).2.2, e0]
      · -- a split edge: through the edge block
        have hlE := (e_blk hS he).1
        simp only at hlE
        rcases cls3 hv cs0 cs1 cs2 hS hsb' with ⟨k', hk', hkB', -, rfl⟩ | ⟨e2, -, he2, -⟩
        · rw [(b_fields hS hk' hkB').1] at hsbl
          have := Prep.lt_next0 hk'
          lomega
        · have hlE2 := (e_blk hS he2).1
          have : e2 = e := by lomega
          subst this
          rw [he] at he2
          cases he2
          rw [srcOf_jump (n := Prep.next0Of (Prep.keep vc.blocks (reachable ss0))) (lbl := l')
            (by lomega)] at hv'
          rw [edgeAvail_noParams rfl]
          exact hAA _ (edgeAvail_noArgs (hv.multi hb0' ht h2) (hEo hv'))
    · -- an edge block `jump l1`
      rw [he'] at he
      cases he
      simp [Array.back?] at ht3
      subst ht3
      have hj0 : j = 0 := by
        have := (List.getElem?_eq_some_iff.mp htj3).1; simp [MInst.targets] at this; omega
      subst hj0
      cases htj3
      obtain ⟨-, -, -, hlN⟩ := tgt_v1 cs1 hkk ht1 hm
      obtain ⟨-, hpar, hsrc⟩ := hkept _ hlN hsbl
      rw [hsrc] at hv'
      obtain ⟨b1, hb1, e1, -⟩ := v1_vc hv hkk
      rw [e1] at ht1
      have hpar0 : sb'.params = #[] := by
        rw [hpar]
        obtain ⟨hl1, -⟩ := hkept _ hlN hsbl
        rw [getElem!_pos vc.blocks l' hl1]
        exact hv.noArgs b1 _ t1 _ _ (Array.getElem?_eq_getElem hb1)
          (hv.multi (Array.getElem?_eq_getElem hb1) ht1 h2) ht1 (List.mem_of_getElem? hm)
          (Array.getElem?_eq_getElem hl1)
      rw [edgeAvail_noParams hpar0]
      refine defAt_ge _ _ ?_
      unfold defStart
      rw [prepSets_of hvb']
      obtain ⟨l2, hl2, hsrc2⟩ := srcOf_E hS he'
      simp only at hl2
      rw [hsrc2]
      cases hl2
      simp [hv']
  · -- nothing defined on entry
    intro v
    have hRs : 0 < (rpo ss2).size := (Array.getElem?_eq_some_iff.mp hR0).1
    have h0B : 0 < B.size := by rw [hS.size]; exact h10
    have hV30 : ((rpo ss2).map fun i => (B ++ E)[i]!)[0]? = some B[0] := by
      obtain ⟨hi, e⟩ := Prep.v3_get hR hRs
      rw [e]; congr 1
      have : (rpo ss2)[0] = 0 := Option.some.inj ((Array.getElem?_eq_getElem hRs).symm.trans hR0)
      simp only [this]
      exact Array.getElem_append_left h0B
    have hV1vc : (Prep.keep vc.blocks (reachable ss0))[0] = vc.blocks[0]'hv.nonempty :=
      Option.some.inj ((Array.getElem?_eq_getElem h10).symm.trans
        (hV0.trans (Array.getElem?_eq_getElem hv.nonempty)))
    rw [prepSets_of hV30, srcOf_kept hS h10 h0B, hV1vc,
      hv.labels 0 _ (Array.getElem?_eq_getElem hv.nonempty)]
    exact h0 v

end Backend.Proof.Spill
