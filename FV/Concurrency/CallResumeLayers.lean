import FV.Concurrency.IselResume
import FV.Concurrency.CallResumeQ

/-!
# Layers 3, 4a and 4b resuming after a call (#473, (2c) of the generic call theorem)

The caller's relations at a call (layer 3's `PMatch`, layer 4a's `Match` of the allocation
checker, layer 4b's `Q`) are rebuilt after the callee's return by **one step of the `call`
under the external semantics returning the callee's outputs and the caller's state after the
return** (`IselResume.xcallX`; the world after the call is that state):

* `mstep_call` (layer 4b → 4a): from `Q` at the `call` item and a state `y` preserving the
  caller's live locations outside the call's clobbers (callee-saved registers, spill slots) and
  the low halves of the clobbered callee-saved registers (`ckeep`), the allocated code's `call`
  steps (`MStep`, the outputs the def locations' values in `y`) to a store holding `y`'s live
  locations;
* `alloc_call_vstep` (layer 4a): the allocation checker's step (`sim_step_at`) at an `op` item;
* `pmatch_call`, `prep_vstep_next` (layer 3): at a `call`, `prepare`'s relation is the block
  correspondence; a step to the next instruction of the prepared code is one of the original;
* **`resume_layers`**: layers 3, 4a and 4b after the return together — from the relations at the
  call and the callee's return, the original VCode's `call` steps to a configuration related
  (`PMatch`, the checker's `Match`, `Q`) to the allocated code's after the call, at the world
  `y`.
-/

namespace Concurrency.CallResumeL

open Arm ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread AllocThread
  ArmAllocThread E2E IselResume

/-! ## `writeM` with the values of a function of the locations -/

theorem writeM_fun {V : Type} (g : Loc → V) :
    ∀ (dl : List ((Operand × Loc) × V)) (m : Loc → V), (∀ p ∈ dl, p.2 = g p.1.2) →
      ∀ l, writeM m dl l = if dl.any (·.1.2 == l) then g l else m l
  | [], m, _, l => by simp [writeM]
  | p :: dl, m, h, l => by
    have ih := writeM_fun g dl (upd m p.1.2 p.2) (fun q hq => h q (List.mem_cons_of_mem _ hq)) l
    simp only [writeM, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases hd : dl.any (·.1.2 == l) = true
    · simp [hd]
    · simp only [Bool.not_eq_true] at hd
      rw [hd]
      by_cases hl : l = p.1.2
      · subst hl; simp [upd, h p List.mem_cons_self]
      · have : (p.1.2 == l) = false := by simpa [beq_iff_eq] using Ne.symm hl
        simp [upd, hl, this, hd]

theorem calleeSaved_allocatable : ∀ c ∈ calleeSaved, c.allocatable = true := by decide

/-! ## A call has at most one def operand per def (#587: `csem` keeps `info.defs.length` results) -/

/-- The operand collector of `MInst.operands`. -/
private def collectD (s : OpSpec) (r : Reg) : StateT (Array Operand) (Except String) Reg := do
  match r with
  | .vreg n cls => modify (·.push ⟨n, cls, s.kind, s.pos, s.con⟩); pure r
  | _ =>
    if r.allocatable then throw s!"allocatable real register {repr r} as an operand"
    else pure r

private theorem operands_eqD (i : MInst) :
    i.operands = (do let (_, ops) ← (MInst.visitOperands collectD i).run #[]; pure ops) := rfl

/-- The number of def operands. -/
private def nDef (s : Array Operand) : Nat := (s.toList.filter Operand.isDef).length

/-- A collector step pushes at most `k` def operands. -/
private structure DefLe {α : Type} (k : Nat) (x : StateT (Array Operand) (Except String) α) :
    Prop where
  run : ∀ s a s', x.run s = .ok (a, s') → nDef s' ≤ nDef s + k

private theorem DefLe.pure' {α : Type} (a : α) :
    DefLe 0 (Pure.pure a : StateT (Array Operand) (Except String) α) :=
  ⟨fun s c s' h => by cases h; omega⟩

private theorem DefLe.bind {α β : Type} {k1 k2 : Nat} {x : StateT (Array Operand) (Except String) α}
    {f : α → StateT (Array Operand) (Except String) β} (hx : DefLe k1 x)
    (hf : ∀ a, DefLe k2 (f a)) : DefLe (k1 + k2) (x >>= f) := by
  refine ⟨fun s c s'' h => ?_⟩
  rw [StateT.run_bind] at h
  cases hr : x.run s with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨a, s'⟩ := p
    rw [hr] at h
    have := hx.run s a s' hr
    have := (hf a).run s' c s'' h
    omega

private theorem DefLe.map {α β : Type} {k : Nat} (g : α → β)
    {x : StateT (Array Operand) (Except String) α} (hx : DefLe k x) : DefLe k (g <$> x) := by
  rw [map_eq_pure_bind]
  have := DefLe.bind hx fun a => DefLe.pure' (g a)
  simpa using this

private theorem DefLe.mono {α : Type} {k k' : Nat} {x : StateT (Array Operand) (Except String) α}
    (hx : DefLe k x) (h : k ≤ k') : DefLe k' x :=
  ⟨fun s a s' hr => by have := hx.run s a s' hr; omega⟩

private theorem DefLe.collect (sp : OpSpec) (r : Reg) :
    DefLe (if sp.kind = .def then 1 else 0) (collectD sp r) := by
  refine ⟨fun s a s' h => ?_⟩
  cases r
  case vreg n c =>
    simp only [collectD, StateT.run, modify, modifyGet, MonadStateOf.modifyGet] at h
    cases h
    simp only [nDef, Array.toList_push, List.filter_append, List.length_append]
    cases hk : sp.kind <;> simp [List.filter_cons, Operand.isDef, hk]
  all_goals
    simp only [collectD] at h
    split at h
    · cases h
    · cases h; omega

private theorem DefLe.collectUse (sp : OpSpec) (r : Reg) (hk : sp.kind = .use) :
    DefLe 0 (collectD sp r) := by
  have := DefLe.collect sp r
  rw [hk] at this
  simpa using this

private theorem DefLe.collectOne (sp : OpSpec) (r : Reg) : DefLe 1 (collectD sp r) :=
  (DefLe.collect sp r).mono (by split <;> omega)

private theorem DefLe.mapM' {α β : Type} {k : Nat} {F : α → StateT (Array Operand) (Except String) β}
    (h : ∀ a, DefLe k (F a)) : ∀ l : List α, DefLe (k * l.length) (l.mapM F)
  | [] => by simpa using DefLe.pure' ([] : List β)
  | a :: l => by
    rw [List.mapM_cons]
    have := DefLe.bind (h a) fun b =>
      DefLe.bind (DefLe.mapM' h l) fun bs => DefLe.pure' (b :: bs)
    refine this.mono ?_
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- **A call's def operands** are at most its defs (a def in a real register adds none). -/
theorem call_defs_le {info : CallInfo} {ops : Array Operand}
    (h : (MInst.call info).operands = .ok ops) :
    (ops.toList.filter Operand.isDef).length ≤ info.defs.length := by
  have hv : DefLe info.defs.length (MInst.visitOperands collectD (.call info)) := by
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands] <;> apply DefLe.mono <;>
      (repeat'
        first
        | exact DefLe.pure' _
        | exact DefLe.collectUse _ _ rfl
        | exact DefLe.collectOne _ _
        | apply DefLe.mapM'
        | apply DefLe.map
        | apply DefLe.bind
        | intro _) <;>
      simp [OpSpec.use, OpSpec.fixedUse, OpSpec.fixedDef]
  rw [operands_eqD] at h
  cases hr : (MInst.visitOperands collectD (.call info)).run #[] with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨i₀, ops'⟩ := p
    rw [hr] at h
    cases h
    have := hv.run #[] i₀ ops hr
    simpa [nDef] using this

/-! ## Layer 4b to 4a: the allocated `call` step -/

/-- **The allocated code's `call` step after the callee's return** (module doc). -/
theorem mstep_call {R : RL} {s y : ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {info : CallInfo}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hk : k + 1 < vb.insts.size) {ops : Array Operand} (hops : (MInst.call info).operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hpres : ∀ l, ValidLoc l → Live R.rf l → (∀ c ∈ (MInst.call info).clobbers, l ≠ .reg c) →
      locVal R.fr y l = locVal R.fr s l)
    (hkeep : ∀ c ∈ (MInst.call info).clobbers, c ∈ calleeSaved →
      ckeep c (regVal y c) = ckeep c (regVal s c))
    (X : ExtSem) (y' : ArmState) :
    ∃ m', MStep R.vc (csem R.F R.ctx
        (xcallX X ((((ops.zip allocs).toList.filter (·.1.isDef))).map fun p => locVal R.fr y p.2) y'))
        ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) (.run ⟨b, its, m', y'⟩) ∧
      ∀ l, ValidLoc l → Live R.rf l → m' l = locVal R.fr y l := by
  classical
  have hst := q_stRel hq
  let D := ((ops.zip allocs).toList.filter (·.1.isDef))
  let outs := D.map fun p => locVal R.fr y p.2
  let early := (D.zip outs).filter (·.1.1.isEarly)
  let late := (D.zip outs).filter (·.1.1.isLate)
  let clob := (MInst.call info).clobbers
  let m1 := writeM m early
  let m2 : Loc → CV := fun l => if ∃ c ∈ clob, l = .reg c then locVal R.fr y l else m1 l
  have hzip : ∀ p ∈ D.zip outs, p.2 = locVal R.fr y p.1.2 := by
    intro p hp
    have : D.zip outs = D.map fun q => (q, locVal R.fr y q.2) := by
      simp only [outs]
      clear hp
      induction D with
      | nil => rfl
      | cons q D ih => simp [ih]
    rw [this] at hp
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
    rfl
  have hearly : ∀ p ∈ early, p.2 = locVal R.fr y p.1.2 :=
    fun p hp => hzip p ((List.mem_filter.mp hp).1)
  have hlate : ∀ p ∈ late, p.2 = locVal R.fr y p.1.2 :=
    fun p hp => hzip p ((List.mem_filter.mp hp).1)
  have hm1 := writeM_fun (locVal R.fr y) early m hearly
  have hm' := writeM_fun (locVal R.fr y) late m2 hlate
  have hD : D.length ≤ info.defs.length := by
    have := congrArg List.length (pairs_fst hsz.symm Operand.isDef)
    rw [List.length_map] at this
    rw [this]; exact call_defs_le hops
  refine ⟨writeM m2 late, ?_, fun l hv hlive => ?_⟩
  · refine MStep.op hvb hi hops hsz ?_ (by simp [outs, D]) (HavocOuts.refl _ _ _) ⟨?_, ?_⟩ (.next hk)
    · have hO : outs.length ≤ info.defs.length := by simp only [outs, List.length_map]; exact hD
      simp only [csem, xcallX, Option.map_some]
      congr 2
      exact List.take_of_length_le hO
    · intro l hl
      simp only [m2]
      rw [if_neg (fun ⟨c, hc, he⟩ => hl c hc he)]
    · intro c hc hcs
      simp only [m2]
      rw [if_pos ⟨c, hc, rfl⟩]
      show ckeep c (regVal y c) = ckeep c (writeM m early (.reg c))
      rw [hm1]
      split
      · rfl
      · rw [hst.store (.reg c) (fun r e => by cases e; exact calleeSaved_allocatable c hcs) trivial]
        exact hkeep c hc hcs
  · rw [hm']
    split
    · rfl
    · simp only [m2]
      split
      · rfl
      · rename_i hnc
        show writeM m early l = _
        rw [hm1]
        split
        · rfl
        · rw [hst.store l hv hlive]
          exact (hpres l hv hlive fun c hc he => hnc ⟨c, hc, he⟩).symm

/-! ## Layer 4a: the checker's step -/

/-- **The allocation checker's step at an item whose instruction falls through**
(`AllocThread.alloc_back`'s `op` case without events: `op_sound`): the VCode steps to the next
instruction, matched to the allocated code's configuration after the item. -/
theorem alloc_call_vstep {V W : Type} {vc : VCode} {rf : RFunc} {sem : ISem V W}
    {keep : Reg → V → V} {c : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    {r₀ : Reg → V} (hc : CheckedAt vc rf c ins a0) {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m m' : Loc → V} {w y : W} {b' k' : Nat} {ρ : Nat → V} {w'' : W}
    (hm : MatchRun c ins keep r₀ ⟨b, .op k allocs :: its, m, w⟩ ⟨b', k', ρ, w''⟩)
    {vb : VBlock} {i : MInst} (hvb : vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hnx : ∀ u w0 r, sem i u w0 = some r → r.2.2 = .next)
    (hs : MStep vc sem keep rf (.run ⟨b, .op k allocs :: its, m, w⟩) (.run ⟨b, its, m', y⟩)) :
    ∃ ρ', VStep vc sem (.run ⟨b', k', ρ, w''⟩) (.run ⟨b, k + 1, ρ', y⟩) ∧
      MatchRun c ins keep r₀ ⟨b, its, m', y⟩ ⟨b, k + 1, ρ', y⟩ := by
  obtain ⟨hb, hw, vb', a, out, hvb', hrun, hinv, hedges⟩ := hm
  simp only at hb hw hvb' hrun hinv hedges
  subst hb hw
  obtain ⟨-, hk, i', ops', a', hi', hops', hstep, hrun'⟩ := runItems_op hrun
  subst hk
  have hvbV : vc.blocks[b]? = some vb' := by rw [← hc.vc_eq]; exact hvb'
  rw [hvbV] at hvb; cases hvb
  rw [hi] at hi'; cases hi'
  cases hs with
  | @op _ _ _ _ _ _ vb1 i1 ops outs outs' w' ctl m2 _ hvb1 hi1 hops1 hsz hsem hlen hho hclob hnext =>
    rw [hvbV] at hvb1; cases hvb1
    rw [hi] at hi1; cases hi1
    rw [hops'] at hops1; cases hops1
    obtain ⟨_, huse, hinv', -⟩ := op_sound hstep hinv hlen hho hclob
    rw [huse] at hsem hnext
    have hlen' : outs.length = (ops'.toList.filter Operand.isDef).length := by
      rw [hlen, ← pairs_fst hsz.symm, List.length_map]
    have hctl := hnx _ _ _ hsem
    simp only at hctl
    subst hctl
    cases hnext with
    | next hk1 =>
      rw [tryForget_of_ne (ctl := .next) (fun _ e => nomatch e)] at hinv'
      exact ⟨_, VStep.step hvbV hi hops' hsem hlen' (VNext.next hk1), rfl, rfl, _, _, out, hvb',
        hrun', hinv', hedges⟩

/-! ## Layer 3 -/

section prep
variable {vc vcp : VCode} {L : Nat → Prop} {ss ss' : Array (Array Nat)}

/-- **At a `call` of the prepared code, `prepare`'s relation is the block correspondence.** -/
theorem pmatch_call {sem : ISem CV ArmState} {ev : MInst → List CV → ArmState → List Ev}
    {src : VConf CV ArmState} {b' k : Nat} {ρ : Nat → CV} {w : ArmState} {vb' : VBlock}
    {info : CallInfo} (hm : PMatch vc vcp sem ev L ss' src (.run ⟨b', k, ρ, w⟩))
    (hvb' : vcp.blocks[b']? = some vb') (hi : vb'.insts[k]? = some (.call info)) :
    ∃ b, src = .run ⟨b, k, ρ, w⟩ ∧ L b ∧ sigmaOf vc vcp b = some b' := by
  cases hm with
  | blk hLb hσ => exact ⟨_, rfl, hLb, hσ⟩
  | pend _ _ _ _ _ _ _ _ _ _ _ _ heb hebi =>
    rw [heb] at hvb'; cases hvb'
    rw [hebi] at hi; cases hi

/-- **A step of the prepared code to its next instruction is one of the original.** -/
theorem prep_vstep_next (H : PrepFacts vc vcp L ss ss') {sem : ISem CV ArmState}
    (hds : DriverSemG sem) {b b' k : Nat} (hLb : L b) (hσ : sigmaOf vc vcp b = some b')
    {ρ ρ' : Nat → CV} {w w' : ArmState}
    (hs : VStep vcp sem (.run ⟨b', k, ρ, w⟩) (.run ⟨b', k + 1, ρ', w'⟩)) :
    VStep vc sem (.run ⟨b, k, ρ, w⟩) (.run ⟨b, k + 1, ρ', w'⟩) := by
  obtain ⟨vb, vb', hvb, hvb', -, -, hsz, hins, -⟩ := (H.kept b b' hLb hσ).blocks
  cases hs with
  | step hvb1 hi' hops hsem hlen hnext =>
    rw [hvb'] at hvb1; cases hvb1
    have hklt : k < vb.insts.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hi').1
    obtain ⟨i, hi⟩ : ∃ i, vb.insts[k]? = some i := ⟨_, Array.getElem?_eq_getElem hklt⟩
    obtain ⟨i'', hi'', hsame⟩ := hins k i hi
    rw [hi'] at hi''; cases hi''
    obtain ⟨hops', hsem', -⟩ := sameInst_facts' hds hsame
    rw [hops'] at hops
    rw [hsem'] at hsem
    cases hnext with
    | next hlt => exact .step hvb hi hops hsem hlen (.next (by rw [← hsz]; exact hlt))

end prep

/-! ## Layers 3, 4a and 4b together -/

/-- **Layers 3, 4a and 4b after a call's return** (module doc). -/
theorem resume_layers {R : RL} (hR : R.Wf) {vc : VCode} {L : Nat → Prop}
    {ss ss' : Array (Array Nat)} (H3 : PrepFacts vc R.vc L ss ss')
    {ev : MInst → List CV → ArmState → List Ev} {c : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} {r₀ : Reg → CV} (hc : CheckedAt R.vc R.rf c ins a0)
    {x y : ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} {ρ : Nat → CV} {src : VConf CV ArmState}
    (hP : PMatch vc R.vc R.sem ev L ss' src (.run ⟨b, k, ρ, w⟩))
    (hA : MatchRun c ins ckeep r₀ ⟨b, .op k allocs :: its, m, w⟩ ⟨b, k, ρ, w⟩)
    (hq : Q R x (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {info : CallInfo}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hk : k + 1 < vb.insts.size) {ops : Array Operand} (hops : (MInst.call info).operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hpres : ∀ l, ValidLoc l → Live R.rf l → (∀ c ∈ (MInst.call info).clobbers, l ≠ .reg c) →
      locVal R.fr y l = locVal R.fr x l)
    (hkeep : ∀ c ∈ (MInst.call info).clobbers, c ∈ calleeSaved →
      ckeep c (regVal y c) = ckeep c (regVal x c))
    (hpc : Arm.r .PC y = Arm.r .PC x + 4#64) (herr : Arm.r .ERR y = .None)
    (hsp : spOf y = spOf x) (hmem : ∀ a, R.FK a → y.mem a = x.mem a)
    (hprog : y.program = x.program) (hfp : xreg 29 y = xreg 29 x) (X : ExtSem) :
    ∃ b0 m' ρ', src = .run ⟨b0, k, ρ, w⟩ ∧
      VStep vc (csem R.F R.ctx (xcallX X
        ((((ops.zip allocs).toList.filter (·.1.isDef))).map fun p => locVal R.fr y p.2) y))
        (.run ⟨b0, k, ρ, w⟩) (.run ⟨b0, k + 1, ρ', y⟩) ∧
      PMatch vc R.vc R.sem ev L ss' (.run ⟨b0, k + 1, ρ', y⟩) (.run ⟨b, k + 1, ρ', y⟩) ∧
      MatchRun c ins ckeep r₀ ⟨b, its, m', y⟩ ⟨b, k + 1, ρ', y⟩ ∧
      Q R y (.run ⟨b, its, m', y⟩) := by
  obtain ⟨m', hms, hst'⟩ := mstep_call hq hvb hi hk hops hsz hpres hkeep X y
  obtain ⟨ρ', hv4, hA'⟩ := alloc_call_vstep hc hA hvb hi (fun u w0 r h => by
    simp only [csem, xcallX, Option.map_some, Option.some.injEq] at h
    subst h; rfl) hms
  obtain ⟨b0, rfl, hLb, hσ⟩ := pmatch_call hP hvb hi
  exact ⟨b0, m', ρ', rfl, prep_vstep_next H3 (driverSem_csem _ _ _).toDriverSemG hLb hσ hv4,
    .blk hLb hσ, hA', CallSeg.resumeQW hR hq hvb hi hpc herr hsp hmem hprog hfp hst'
      (SameWorld.refl _ _)⟩

end Concurrency.CallResumeL
