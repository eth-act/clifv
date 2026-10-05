import FV.Backend.Proof.SpillStep4Args

/-!
# The spill allocation's dataflow invariant (V4 (a), step 4): `spillStep4`

**`spillStep4 : SpillStep4`**: on a VCode with a CFG, the local facts (`SpillLocalOk`) and
availability sets `D` (`SpillAvail`) make the spill allocation `AllocChecked`, with the
in-states `inState` (`SpillStep4State.lean`): the checker context is the spill allocation's own,
every block's run from its in-state passes the checker (`verify_block`: the saves and entry
stores `pre_runs`, each instruction `inst_runs`, the argument copies before a `jump`
`argMoves_runs`) and feeds every successor's in-state (`edge_noargs`, `edge_args`); the entry
in-state is `EntryOk` (`inState_entryOk`).

`spillStep4_witness`: the premises hold together on a two-block VCode with a block argument.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof

/-- The checker context of the spill allocation. -/
def spillCtx (vc : VCode) (succs : Array (Array Nat)) : CheckCtx :=
  { vc, succs, rf := spillAlloc vc, size := stN vc }

/-- The argument copies in front of block `bi`'s last instruction (`spillAlloc`). -/
def argMovesOf (vc : VCode) (succs : Array (Array Nat)) (bi : Nat) (vb : VBlock) : List RItem :=
  match succs[bi]? with
  | some #[t] => match vc.blocks[t]? with
    | some tb => spillArgMoves (spillHomes vc) vb tb
    | none => []
  | _ => []

/-- The items of instruction `x.2` (`x.1`) of block `bi` (`spillAlloc`). -/
def bodyItem (vc : VCode) (succs : Array (Array Nat)) (bi : Nat) (vb : VBlock) (x : MInst × Nat) :
    List RItem :=
  (if x.2 + 1 == vb.insts.size && !vb.branchArgs.isEmpty then argMovesOf vc succs bi vb else []) ++
    spillInst (spillHomes vc) x.2 x.1

theorem spillAlloc_block {vc : VCode} {succs preds : Array (Array Nat)}
    (hcfg : vc.cfg = .ok (succs, preds)) {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    (spillAlloc vc).blocks[b]? = some (((if b == 0 then spillSaves else []) ++
      spillEntryStores (spillHomes vc) vc succs preds b ++
      vb.insts.toList.zipIdx.flatMap (bodyItem vc succs b vb)).toArray) := by
  unfold spillAlloc
  rw [hcfg]
  dsimp only
  rw [Array.getElem?_mapIdx, hvb]
  rfl

theorem spillAlloc_size (vc : VCode) : (spillAlloc vc).blocks.size = vc.blocks.size := by
  unfold spillAlloc; split <;> exact Array.size_mapIdx

theorem argMovesOf_eq {vc : VCode} {succs : Array (Array Nat)} {b t : Nat} {vb tb : VBlock}
    (hss : succs[b]? = some #[t]) (htb : vc.blocks[t]? = some tb) :
    argMovesOf vc succs b vb = spillArgMoves (spillHomes vc) vb tb := by
  unfold argMovesOf
  rw [hss]
  show (match vc.blocks[t]? with
    | some tb => spillArgMoves (spillHomes vc) vb tb
    | none => []) = _
  rw [htb]

theorem keptPairs_nil (i : MInst) : keptPairs i [] = [] := by
  unfold keptPairs; split <;> simp

theorem availAt_zero (insts : Array MInst) (A : Nat → Bool) : availAt insts A 0 = A := rfl

section
variable {vc : VCode} {succs preds : Array (Array Nat)} {D : Nat → Nat → Bool}
  (hcfg : vc.cfg = .ok (succs, preds)) (hloc : SpillLocalOk vc) (hav : SpillAvail vc D)
  {c : CheckCtx} (hcvc : c.vc = vc) (hcs : c.succs = succs)
  (hsl : c.rf.spillSlots = (spillHomes vc).size + maxArgs vc) (hsv : c.rf.saved = calleeSaved)
  {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb)
include hcfg hloc hav hcvc hcs hsl hsv hvb

/-- **The last instruction** of a block (with the argument copies in front of a `jump` with
arguments): its items pass the checker and the out-state feeds every successor's in-state. -/
theorem last_runs {k : Nat} {i : MInst} (hi : vb.insts[k]? = some i) (hk : k + 1 = vb.insts.size)
    {a : AState} (hg : Good vc (availAt vb.insts (availStart vc succs preds D b) k) a) :
    Runs c vb k (bodyItem vc succs b vb (i, k)) a fun k' a' => k' = vb.insts.size ∧
      ∀ s ∈ (c.succs[b]?.getD #[]).toList, ∃ e, c.edge b s a' = .ok e ∧
        (inState vc succs preds D s).le e = true := by
  have hE := hloc.2.2 succs preds hcfg
  obtain ⟨ops, hops, hok, hrets⟩ := hloc.1 b vb k i hvb hi
  obtain ⟨T, hT, hTt⟩ := cfg_last hcfg hvb
  obtain ⟨-, hTk⟩ := back_get hT
  rw [show vb.insts.size - 1 = k by omega, hi] at hTk
  have hiT : i = T := Option.some.inj hTk
  subst hiT
  have huse := fun o ho hu => hav.uses succs preds hcfg b vb k i ops hvb hi hops o ho hu
  by_cases hba : vb.branchArgs = #[]
  · have hbi : bodyItem vc succs b vb (i, k) = spillInst (spillHomes vc) k i := by
      simp [bodyItem, hba]
    rw [hbi]
    exact (inst_runs hsl hsv (by omega) hi hops hok hrets (fun _ => hTt) (opFacts hloc hvb hi hops)
      huse hg).mono fun k' a' ⟨e1, hg', hkept⟩ => ⟨by omega,
        edge_noargs hcfg hloc hav hcvc hcs hvb hba hT hTt hops hok
          (by rw [← hk, availAt_succ hi]; exact hg') hkept⟩
  · obtain ⟨⟨i', hi', hops'⟩, t, tb, hss, htb, hsz, hcls, hnd⟩ := hE.args b vb hvb hba
    rw [hT] at hi'
    cases hi'
    rw [hops] at hops'
    cases hops'
    -- not a `Rets`: it has a successor
    have hnr : ∀ us, i ≠ .rets us := by
      intro us he
      obtain ⟨t', ts, ht', -, hts, hlen, -⟩ := (Prep.cfg_spec hcfg).blk b vb hvb
      rw [hT] at ht'
      cases ht'
      rw [hss] at hts
      cases hts
      subst he
      simp [MInst.targets] at hlen
    have hie : vb.branchArgs.isEmpty = false := by
      rw [Bool.eq_false_iff]; intro h; exact hba (Array.isEmpty_iff.mp h)
    have hsi : spillInst (spillHomes vc) k i = [.op k (spillLocs #[] i.clobbers)] := by
      rw [spillInst_eq hops, restoresOf_other hnr]
      simp [loadMoves, storeMoves, keptPairs_nil]
    have hbi : bodyItem vc succs b vb (i, k) =
        spillArgMoves (spillHomes vc) vb tb ++ [.op k (spillLocs #[] i.clobbers)] := by
      simp only [bodyItem, hk, BEq.rfl, hie, Bool.not_false, Bool.and_self, ↓reduceIte,
        argMovesOf_eq hss htb, hsi]
    rw [hbi]
    have hnil : ((#[] : Array Operand).zip (spillLocs #[] i.clobbers)).toList = [] := by simp
    refine Runs.append (argMoves_runs hloc hsl hvb htb hsz hcls hnd (by omega) hg)
      fun k1 a2 ⟨e1, _, sv2, np2, pa2⟩ => ?_
    subst k1
    have keep3 : ∀ l x, l.isReg = false → x ∈ a2.get l →
        x ∈ (transferOp i ((#[] : Array Operand).zip (spillLocs #[] i.clobbers)).toList a2).get l :=
      fun l x hl hx => transferOp_keep (fun y hy => by rw [hnil] at hy; cases hy)
        (fun r _ he => by rw [← he] at hl; cases hl) hx (fun y hy => by rw [hnil] at hy; cases hy)
    refine Runs.op (by omega) hi hops (stepOp_of (checkStatic_spill c _ hok)
      (fun p hp => by rw [hnil] at hp; cases hp) (by rw [hnil]; rfl)
      (retCheck_other hnr _)) ⟨by omega, ?_⟩
    have hA : availAt vb.insts (availStart vc succs preds D b) vb.insts.size =
        availAt vb.insts (availStart vc succs preds D b) k := by
      funext v
      rw [← hk, availAt_succ hi, availInst_eq hops]
      simp [isDefOf]
    exact edge_args hcfg hloc hav hcvc hcs hvb hss htb hba hT hops hsz hnd hA
      (fun r hr => keep3 _ _ rfl (sv2 r hr))
      (fun v cl n hv hc hn hp => keep3 _ _ rfl (np2 v cl n hv hc hn hp))
      (fun kk ar p har hp hA' => by
        have := pa2 kk ar p har hp hA'
        obtain ⟨y, cy, hpy, -, m, hm⟩ := regFacts hloc htb
          (List.mem_append_left _ (List.mem_of_getElem? (by simpa using hp)))
        rw [hpy, (show Reg.homeNum (.vreg y cy) = y from rfl),
          (show Reg.homeCls (.vreg y cy) = cy from rfl), spillHome_eq hm] at this ⊢
        exact keep3 _ _ rfl this)

/-- **The instructions of a block** from instruction `k` on. -/
theorem body_runs : ∀ (L : List MInst) (x : MInst) (k : Nat) (a : AState),
    (∀ j y, (x :: L)[j]? = some y → vb.insts[k + j]? = some y) →
    k + (L.length + 1) = vb.insts.size →
    Good vc (availAt vb.insts (availStart vc succs preds D b) k) a →
    Runs c vb k (((x :: L).zipIdx k).flatMap (bodyItem vc succs b vb)) a fun k' a' =>
      k' = vb.insts.size ∧ ∀ s ∈ (c.succs[b]?.getD #[]).toList, ∃ e, c.edge b s a' = .ok e ∧
        (inState vc succs preds D s).le e = true := by
  intro L
  induction L with
  | nil =>
    intro x k a hget hlen hg
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact last_runs hcfg hloc hav hcvc hcs hsl hsv hvb (by simpa using hget 0 x rfl)
      (by simpa using hlen) hg
  | cons y L ih =>
    intro x k a hget hlen hg
    have hi : vb.insts[k]? = some x := by simpa using hget 0 x rfl
    obtain ⟨ops, hops, hok, hrets⟩ := hloc.1 b vb k x hvb hi
    simp only [List.length_cons] at hlen
    have hk1 : k + 1 ≠ vb.insts.size := by omega
    rw [List.zipIdx_cons, List.flatMap_cons]
    have hbi : bodyItem vc succs b vb (x, k) = spillInst (spillHomes vc) k x := by
      have : (k + 1 == vb.insts.size) = false := by simpa using hk1
      simp [bodyItem, this]
    rw [hbi]
    refine Runs.append (inst_runs hsl hsv (by omega) hi hops hok hrets (fun h => absurd h hk1)
      (opFacts hloc hvb hi hops)
      (fun o ho hu => hav.uses succs preds hcfg b vb k x ops hvb hi hops o ho hu) hg)
      fun k' a' ⟨e1, hg', _⟩ => ?_
    subst e1
    exact ih y (k + 1) a'
      (fun j z hz => by
        have := hget (j + 1) z (by simpa using hz)
        rwa [show k + (j + 1) = k + 1 + j by omega] at this)
      (by omega) (by rw [availAt_succ hi]; exact hg')

end

/-- **Every block verifies** from its in-state. -/
theorem verify_block {vc : VCode} {succs preds : Array (Array Nat)} {D : Nat → Nat → Bool}
    (hcfg : vc.cfg = .ok (succs, preds)) (hloc : SpillLocalOk vc) (hav : SpillAvail vc D)
    {b : Nat} (hb : b < vc.blocks.size) :
    (spillCtx vc succs).verifyBlock (insOf vc succs preds D) b = .ok () := by
  have hvb : vc.blocks[b]? = some vc.blocks[b] := Array.getElem?_eq_getElem hb
  generalize vc.blocks[b] = vb at hvb
  obtain ⟨T, hT, -⟩ := cfg_last hcfg hvb
  obtain ⟨hpos, -⟩ := back_get hT
  have hsl := spillAlloc_slots vc
  have hsv := spillAlloc_saved vc
  have hrun : Runs (spillCtx vc succs) vb 0 (((if b == 0 then spillSaves else []) ++
      spillEntryStores (spillHomes vc) vc succs preds b) ++
      vb.insts.toList.zipIdx.flatMap (bodyItem vc succs b vb)) (inState vc succs preds D b)
      fun k a => k = vb.insts.size ∧ ∀ s ∈ ((spillCtx vc succs).succs[b]?.getD #[]).toList,
        ∃ e, (spillCtx vc succs).edge b s a = .ok e ∧ (inState vc succs preds D s).le e = true :=
    Runs.append (pre_runs (D := D) hcfg hloc (c := spillCtx vc succs) hsl hsv (b := b)
    (vb := vb) (Nat.ne_of_lt hpos)) fun k a ⟨hk, hg⟩ => by
      subst hk
      obtain ⟨x, L, hxL⟩ : ∃ x L, vb.insts.toList = x :: L := by
        cases h : vb.insts.toList with
        | nil =>
          have := congrArg List.length h
          rw [Array.length_toList, List.length_nil] at this
          omega
        | cons x L => exact ⟨x, L, rfl⟩
      rw [hxL]
      exact body_runs hcfg hloc hav rfl rfl hsl hsv hvb L x 0 a
        (fun j y hy => by rw [Nat.zero_add, ← Array.getElem?_toList, hxL]; exact hy)
        (by
          have := congrArg List.length hxL
          rw [Array.length_toList, List.length_cons] at this
          omega)
        (by rw [availAt_zero]; exact hg)
  obtain ⟨o, ho, hfin⟩ := Runs.run hrun
  refine verifyBlock_of (out := o) (insOf_get hb) ?_ fun s hs => ?_
  · unfold CheckCtx.runBlock
    rw [show (spillCtx vc succs).vc = vc from rfl, show (spillCtx vc succs).rf = spillAlloc vc from rfl,
      hvb, spillAlloc_block hcfg hvb]
    dsimp only
    rw [List.toList_toArray]
    exact ho
  · obtain ⟨e, he, hle⟩ := hfin s hs
    have hs' : s < vc.blocks.size := by
      obtain ⟨ss, hss⟩ := cfg_succs_some hcfg hb
      rw [show (spillCtx vc succs).succs = succs from rfl, hss, Option.getD_some] at hs
      exact cfg_succ_lt hcfg hss hs
    exact ⟨e, _, he, insOf_get hs', hle⟩

/-- **Step 4 of V4 (a)**: the spill allocation of a VCode with a CFG, the local facts and
availability sets is `AllocChecked`. -/
theorem spillStep4 : SpillStep4 := by
  intro vc D ⟨succs, preds, hcfg⟩ hloc hav
  have hE := hloc.2.2 succs preds hcfg
  exact ⟨spillCtx vc succs, insOf vc succs preds D,
    inState vc succs preds D 0, ⟨rfl, rfl, ⟨preds, hcfg⟩, spillAlloc_size vc, hE.entry.1,
      insOf_get (Nat.pos_of_ne_zero hE.entry.1), fun b hb => verify_block hcfg hloc hav hb⟩,
    inState_entryOk hE.entry.2.1⟩

end Backend.Proof.Spill
