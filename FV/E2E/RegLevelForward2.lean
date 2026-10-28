import FV.E2E.RegLevelCorrectCW
import FV.E2E.RegLevelCorrectU

/-!
# Two allocated-code runs realised jointly along a pair VCode run (SEM1 #537, item (3))

The determinism clause compares two machine runs of one activation index by index. Their segment
chains must have the same shapes step by step (`docs/plans/uninit.md` §5.9, "the shapes of the two
runs' chains"). The checker relation `Match` pins the block of every running configuration and
matches a move by no VCode step and an op by exactly one; the shape after an `MStep` is a function
of the shape before and of the block (or end kind) reached. So two runs related to the two
projections of a pair VCode run, whose steps reach configurations at the same place, stay
shape-equal. Two chains built independently cannot be aligned afterwards (the chain does not
record the VCode index), so the two machine runs are built jointly:

* `MConf.BlkEq`, **`MStep.shapeEq_of_blkEq`**: shape-equal configurations step to shape-equal ones
  when the successors are at the same block (or end kind), for any two semantics;
* `VConf.SameAt`, `PStep` (a step of each VCode run, to configurations at the same place,
  satisfying a pair invariant `PI`);
* `IsSimulationS`: `IsSimulation` with the block of every running configuration and an op matched
  by exactly one VCode step; **`isSimulationS_match`** (`Match`, from `CheckedAt`);
* `RealizesJ`: one segment of both machines, of the same length, from configurations whose
  successors are shape-equal and satisfy `K`;
* **`forward2`**: along a run of pair steps, both machines realise both allocated-code runs, with
  shape-equal configurations at every segment boundary; **`forward2_op`**: at a pair state that
  steps, both advanced past the pending moves to the instruction item.
-/

namespace Backend.Proof

open Backend

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

/-- **Two configurations at the same block** (or both returned, or both halted). -/
def _root_.Backend.MConf.BlkEq : MConf V W → MConf V W → Prop
  | .run s, .run s' => s.b = s'.b
  | .ret .., .ret .. => True
  | .halt _, .halt _ => True
  | _, _ => False

/-- **Shape-equal configurations step to shape-equal ones at the same block**, for any two
semantics (the shape after a step depends only on the shape before and the block reached). -/
theorem MStep.shapeEq_of_blkEq {sem sem' : ISem V W} {c1 c1' c2 c2' : MConf V W}
    (hs : MConf.ShapeEq c1 c1') (h : MStep vc sem keep rf c1 c2)
    (h' : MStep vc sem' keep rf c1' c2') (hb : MConf.BlkEq c2 c2') : MConf.ShapeEq c2 c2' := by
  cases h with
  | move =>
    cases c1' with
    | run s' =>
      obtain ⟨b', its', m', w'⟩ := s'
      obtain ⟨rfl, rfl⟩ := hs
      cases h' with
      | move => exact ⟨rfl, rfl⟩
    | ret => exact hs.elim
    | halt => exact hs.elim
  | op hvb hi hops hsz hsem hlen hho hcl hn =>
    cases c1' with
    | run s' =>
      obtain ⟨b', its', m', w'⟩ := s'
      obtain ⟨rfl, rfl⟩ := hs
      cases h' with
      | op hvb' hi' hops' hsz' hsem' hlen' hho' hcl' hn' =>
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        cases hn with
        | next hk =>
          cases hn' with
          | next => exact ⟨rfl, rfl⟩
          | goto hk' => omega
          | ret => simp only [MConf.BlkEq] at hb
          | halt => simp only [MConf.BlkEq] at hb
        | goto hk hs1 hi1 =>
          cases hn' with
          | next hk' => omega
          | goto _ hs2 hi2 =>
            simp only [MConf.BlkEq] at hb
            subst hb
            rw [hi1] at hi2; cases hi2
            exact ⟨rfl, rfl⟩
          | ret => simp only [MConf.BlkEq] at hb
          | halt => simp only [MConf.BlkEq] at hb
        | ret =>
          cases hn' with
          | ret => trivial
          | _ => simp only [MConf.BlkEq] at hb
        | halt =>
          cases hn' with
          | halt => trivial
          | _ => simp only [MConf.BlkEq] at hb
    | ret => exact hs.elim
    | halt => exact hs.elim

/-- **Two VCode configurations at the same place**: the same block and instruction index, or both
returned, or both halted. -/
def _root_.Backend.VConf.SameAt : VConf V W → VConf V W → Prop
  | .run s, .run s' => s.b = s'.b ∧ s.k = s'.k
  | .ret .., .ret .. => True
  | .halt _, .halt _ => True
  | _, _ => False

/-- **A pair step**: each VCode run steps, to configurations at the same place satisfying the
pair invariant `PI`. -/
def PStep (vc : VCode) (sem sem' : ISem V W) (PI : VConf V W → VConf V W → Prop)
    (p p' : VConf V W × VConf V W) : Prop :=
  VStep vc sem p.1 p'.1 ∧ VStep vc sem' p.2 p'.2 ∧ VConf.SameAt p'.1 p'.2 ∧ PI p'.1 p'.2

variable (vc rf keep) in
/-- **A simulation pinning the block and the op steps**: `IsSimulation`, the related VCode
configuration of a running one is running at the same block, and an op step is matched by
exactly one VCode step. -/
structure IsSimulationS (sem : ISem V W) (R : MConf V W → VConf V W → Prop) : Prop
    extends IsSimulation vc rf sem keep R where
  blk : ∀ {s v}, R (.run s) v → ∃ vs, v = .run vs ∧ vs.b = s.b
  opStep : ∀ {b k a its m w v c'}, R (.run ⟨b, .op k a :: its, m, w⟩) v →
    MStep vc sem keep rf (.run ⟨b, .op k a :: its, m, w⟩) c' → ∃ v', VStep vc sem v v' ∧ R c' v'

/-- Configurations related to VCode configurations at the same place are at the same block. -/
theorem IsSimulationS.blkEq {sem sem' : ISem V W} {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationS vc rf keep sem R) (hR' : IsSimulationS vc rf keep sem' R')
    {c c' : MConf V W} {v v' : VConf V W} (h : R c v) (h' : R' c' v')
    (hs : VConf.SameAt v v') : MConf.BlkEq c c' := by
  cases c with
  | run s =>
    obtain ⟨vs, rfl, hb⟩ := hR.blk h
    cases c' with
    | run s' =>
      obtain ⟨vs', rfl, hb'⟩ := hR'.blk h'
      show s.b = s'.b
      rw [← hb, ← hb']; exact hs.1
    | ret => rw [hR'.ret h'] at hs; exact hs.elim
    | halt => rw [hR'.halt h'] at hs; exact hs.elim
  | ret =>
    rw [hR.ret h] at hs
    cases c' with
    | run s' => obtain ⟨vs', rfl, -⟩ := hR'.blk h'; exact hs.elim
    | ret => trivial
    | halt => rw [hR'.halt h'] at hs; exact hs.elim
  | halt =>
    rw [hR.halt h] at hs
    cases c' with
    | run s' => obtain ⟨vs', rfl, -⟩ := hR'.blk h'; exact hs.elim
    | ret => rw [hR'.ret h'] at hs; exact hs.elim
    | halt => trivial

/-- **One step of both allocated-code runs**: from shape-equal configurations related to `v`,
`v'`, whose VCode steps reach `x`, `x'` at the same place, two `MStep` successors are shape-equal,
and either both were moves (related to `v`, `v'`, smaller measure) or both ops (related to `x`,
`x'`). -/
theorem IsSimulationS.step2 {sem sem' : ISem V W} {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationS vc rf keep sem R) (hR' : IsSimulationS vc rf keep sem' R')
    {c c' : MConf V W} {v v' x x' : VConf V W} (h : R c v) (h' : R' c' v')
    (hsh : MConf.ShapeEq c c') (hx : VStep vc sem v x) (hx' : VStep vc sem' v' x')
    (hsa : VConf.SameAt x x') {e e' : MConf V W} (he : MStep vc sem keep rf c e)
    (he' : MStep vc sem' keep rf c' e') :
    MConf.ShapeEq e e' ∧
      ((R e v ∧ R' e' v' ∧ e.measure < c.measure) ∨ (R e x ∧ R' e' x')) := by
  cases he with
  | @move b src dst its m w =>
    cases c' with
    | run s' =>
      obtain ⟨b', its', m', w'⟩ := s'
      obtain ⟨rfl, rfl⟩ := hsh
      cases he' with
      | move =>
        exact ⟨⟨rfl, rfl⟩, .inl ⟨hR.move h, hR'.move h', by simp [MConf.measure]⟩⟩
    | ret => exact hsh.elim
    | halt => exact hsh.elim
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 e hvb hi hops hsz hsem hlen hho hcl hn =>
    have hs0 : MStep vc sem keep rf (.run ⟨b, .op k allocs :: its, m, w⟩) e :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    cases c' with
    | run s' =>
      obtain ⟨b', its', m', w''⟩ := s'
      obtain ⟨rfl, rfl⟩ := hsh
      obtain ⟨y, hy, hry⟩ := hR.opStep h hs0
      obtain ⟨y', hy', hry'⟩ := hR'.opStep h' he'
      rw [VStep_det hy hx] at hry
      rw [VStep_det hy' hx'] at hry'
      have hsh0 : MConf.ShapeEq (.run ⟨b, .op k allocs :: its, m, w⟩ : MConf V W)
          (.run ⟨b, .op k allocs :: its, m', w''⟩) := ⟨rfl, rfl⟩
      exact ⟨MStep.shapeEq_of_blkEq hsh0 hs0 he' (hR.blkEq hR' hry hry' hsa), .inr ⟨hry, hry'⟩⟩
    | ret => exact hsh.elim
    | halt => exact hsh.elim

end

/-! ## `Match` pins the block and the op steps -/

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {c : CheckCtx} {ins : Array (Option AState)}
  (sem : ISem V W) (keep : Reg → V → V) {r₀ : Reg → V}

/-- **An op item related by `Match` steps with exactly one VCode step** (`sim_step_at`'s op
case). -/
theorem sim_step_op_at {a0 : AState} (hc : CheckedAt vc rf c ins a0) {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → V} {w : W} {vs : VState V W}
    {c' : MConf V W} (hm : MatchRun c ins keep r₀ ⟨b, .op k allocs :: its, m, w⟩ vs)
    (hs : MStep vc sem keep rf (.run ⟨b, .op k allocs :: its, m, w⟩) c') :
    ∃ v', VStep vc sem (.run vs) v' ∧ Match c ins keep r₀ c' v' := by
  obtain ⟨b', k', ρ, w''⟩ := vs
  obtain ⟨hb, hw, vb, a, out, hvb, hrun, hinv, hedges⟩ := hm
  simp only at hb hw
  subst hb hw
  cases hs with
  | @op _ _ allocs its _ _ _ i ops outs outs' w' ctl m2 _ hvb' hi hops hsz hsem hlen hho hclob hnext =>
    rw [hc.vc_eq] at hvb
    rw [hvb] at hvb'
    cases hvb'
    obtain ⟨_, hk, i', ops', a', hi', hops', hstep, hrun'⟩ := runItems_op hrun
    subst hk
    rw [hi] at hi'
    cases hi'
    rw [hops] at hops'
    cases hops'
    obtain ⟨_, huse, hinv', hret⟩ := op_sound hstep hinv hlen hho hclob
    rw [huse] at hsem hnext
    have hlen' : outs.length = (ops.toList.filter Operand.isDef).length := by
      rw [hlen, ← pairs_fst hsz.symm, List.length_map]
    have hvbc : c.vc.blocks[b]? = some vb := by rw [hc.vc_eq]; exact hvb
    cases hnext with
    | next hk1 =>
      rw [tryForget_of_ne (ctl := .next) (fun _ e => nomatch e)] at hinv'
      exact ⟨_, VStep.step hvb hi hops hsem hlen' (VNext.next hk1),
        rfl, rfl, vb, _, out, hvbc, hrun', hinv', hedges⟩
    | ret hus =>
      rw [tryForget_of_ne (ctl := .ret) (fun _ e => nomatch e)] at hinv'
      exact ⟨_, VStep.step hvb hi hops hsem hlen' (VNext.ret hus), rfl, rfl,
        fun r hr => (hinv' _ _ (hret _ hus r hr)).2⟩
    | halt =>
      exact ⟨_, VStep.step hvb hi hops hsem hlen' VNext.halt, rfl⟩
    | goto hk1 hsucc hitems =>
      have hits : its = [] := by
        cases its with
        | nil => rfl
        | cons it its =>
          cases it with
          | move => exact absurd hk1 (runItems_move hrun').1
          | op => exact absurd hk1 (runItems_op hrun').1
      subst hits
      obtain ⟨_, rfl⟩ := runItems_nil hrun'
      obtain ⟨preds, hcfg⟩ := hc.cfg
      obtain ⟨e, a'', hedge, hins, hle⟩ := hedges _ (succOf_mem hcfg hsucc)
      have hcfg' : c.vc.cfg = .ok (c.succs, preds) := by rw [hc.vc_eq]; exact hcfg
      have hinvF := edgeForget_inv hcfg' hvbc hi hk1 hops (by rw [hc.vc_eq]; exact hsucc) hinv'
      obtain ⟨ρ', henv, hinve⟩ := edge_ok hedge hinvF
      rw [hc.vc_eq] at henv
      obtain ⟨items', hitems', hmr⟩ :=
        enter_block_at keep hc (w := w') (edgeEnv_lt henv) hins hle hinve
      rw [hitems] at hitems'
      cases hitems'
      exact ⟨_, VStep.step hvb hi hops hsem hlen' (VNext.goto hk1 hsucc henv), hmr⟩

/-- **`Match` is an `IsSimulationS`** (from verified in-states, as `checkedAt_sound_match`). -/
theorem isSimulationS_match {a0 : AState} (hc : CheckedAt vc rf c ins a0) (m₀ : Loc → V)
    (ρ₀ : Nat → V) (w₀ : W) (hinv0 : Inv keep a0 m₀ ρ₀ (fun r => m₀ (.reg r))) :
    IsSimulationS vc rf keep sem (Match c ins keep (fun r => m₀ (.reg r))) ∧
      Match c ins keep (fun r => m₀ (.reg r)) (MConf.init rf m₀ w₀) (VConf.init ρ₀ w₀) := by
  obtain ⟨hS, hinit, -⟩ := checkedAt_sound_match (sem := sem) hc m₀ ρ₀ w₀ hinv0
  refine ⟨{ hS with blk := ?_, opStep := ?_ }, hinit⟩
  · intro s v h
    cases v with
    | run vs => exact ⟨vs, rfl, h.1.symm⟩
    | ret => exact h.elim
    | halt => exact h.elim
  · intro b k a its m w v c' h hs
    cases v with
    | run vs => exact sim_step_op_at sem keep hc h hs
    | ret => exact h.elim
    | halt => exact h.elim

end

/-! ## The joint forward simulation -/

section
variable {V W S : Type} {vc : VCode} {rf : RFunc} {keep : Reg → V → V}

/-- Joint traces compose. -/
theorem trace_add2 {step step' : S → S} {T : S → S → Prop} {s s' : S} {a b : Nat}
    (ha : ∀ i < a, T (iterN step i s) (iterN step' i s'))
    (hb : ∀ i < b, T (iterN step i (iterN step a s)) (iterN step' i (iterN step' a s'))) :
    ∀ i < a + b, T (iterN step i s) (iterN step' i s') := by
  intro i hi
  by_cases h : i < a
  · exact ha i h
  · have := hb (i - a) (by omega)
    rwa [← iterN_add, ← iterN_add, show a + (i - a) = i by omega] at this

/-- **Two machines realise two allocated-code runs jointly** under `J`: from configurations
satisfying `J` with `MStep` successors, whenever every two successors are shape-equal and satisfy
`K`, the machines reach, after the same number of steps, states satisfying `J` with two `MStep`
successors, every pair of states of the way satisfying the joint trace invariant `T`. -/
def RealizesJ (vc : VCode) (rf : RFunc) (sem sem' : ISem V W) (keep : Reg → V → V)
    (step step' : S → S) (K : MConf V W → MConf V W → Prop)
    (J : S → MConf V W → S → MConf V W → Prop) (T : S → S → Prop) : Prop :=
  ∀ s c s' c' d d', J s c s' c' → MStep vc sem keep rf c d → MStep vc sem' keep rf c' d' →
    (∀ e e', MStep vc sem keep rf c e → MStep vc sem' keep rf c' e' →
      MConf.ShapeEq e e' ∧ K e e') →
    ∃ n e e', MStep vc sem keep rf c e ∧ MStep vc sem' keep rf c' e' ∧
      J (iterN step n s) e (iterN step' n s') e' ∧ ∀ i < n, T (iterN step i s) (iterN step' i s')

theorem forward2_aux {sem sem' : ISem V W} {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationS vc rf keep sem R) (hR' : IsSimulationS vc rf keep sem' R')
    {PI : VConf V W → VConf V W → Prop} {K : MConf V W → MConf V W → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K e e')
    {step step' : S → S} {J : S → MConf V W → S → MConf V W → Prop} {T : S → S → Prop}
    (hJ : RealizesJ vc rf sem sem' keep step step' K J T)
    {p p' : VConf V W × VConf V W} (hp : Star (PStep vc sem sem' PI) p p') :
    ∀ k (c c' : MConf V W) s s', c.measure ≤ k → R c p.1 → R' c' p.2 → PI p.1 p.2 →
      MConf.ShapeEq c c' → J s c s' c' →
      ∃ n d d', J (iterN step n s) d (iterN step' n s') d' ∧ R d p'.1 ∧ R' d' p'.2 ∧
        MConf.ShapeEq d d' ∧ ∀ i < n, T (iterN step i s) (iterN step' i s') := by
  induction hp with
  | refl =>
    exact fun _ c c' s s' _ hr hr' _ hsh hj =>
      ⟨0, c, c', hj, hr, hr', hsh, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | @step p p1 p' h1 _ ih =>
    obtain ⟨hx, hx', hsa, hpi⟩ := h1
    intro k
    induction k with
    | zero =>
      intro c c' s s' hk hr hr' hpi0 hsh hj
      obtain ⟨e, he⟩ := hR.progress hr hx
      obtain ⟨e', he'⟩ := hR'.progress hr' hx'
      obtain ⟨n1, d, d', hd, hd', hj', ht1⟩ := hJ s c s' c' e e' hj he he' fun e e' a b => by
        obtain ⟨hs, hc⟩ := hR.step2 hR' hr hr' hsh hx hx' hsa a b
        refine ⟨hs, ?_⟩
        rcases hc with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
        · exact hK _ _ _ _ h1 h2 hpi0
        · exact hK _ _ _ _ h1 h2 hpi
      obtain ⟨hsh', hc⟩ := hR.step2 hR' hr hr' hsh hx hx' hsa hd hd'
      rcases hc with ⟨-, -, hlt⟩ | ⟨hrd, hrd'⟩
      · omega
      · obtain ⟨n2, f, f', hj2, hr2, hr2', hsh2, ht2⟩ :=
          ih d.measure d d' _ _ (Nat.le_refl _) hrd hrd' hpi hsh' hj'
        exact ⟨n1 + n2, f, f', by rw [iterN_add, iterN_add]; exact hj2, hr2, hr2', hsh2,
          trace_add2 ht1 ht2⟩
    | succ k ihk =>
      intro c c' s s' hk hr hr' hpi0 hsh hj
      obtain ⟨e, he⟩ := hR.progress hr hx
      obtain ⟨e', he'⟩ := hR'.progress hr' hx'
      obtain ⟨n1, d, d', hd, hd', hj', ht1⟩ := hJ s c s' c' e e' hj he he' fun e e' a b => by
        obtain ⟨hs, hc⟩ := hR.step2 hR' hr hr' hsh hx hx' hsa a b
        refine ⟨hs, ?_⟩
        rcases hc with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
        · exact hK _ _ _ _ h1 h2 hpi0
        · exact hK _ _ _ _ h1 h2 hpi
      obtain ⟨hsh', hc⟩ := hR.step2 hR' hr hr' hsh hx hx' hsa hd hd'
      rcases hc with ⟨hrd, hrd', hlt⟩ | ⟨hrd, hrd'⟩
      · obtain ⟨n2, f, f', hj2, hr2, hr2', hsh2, ht2⟩ :=
          ihk d d' _ _ (by omega) hrd hrd' hpi0 hsh' hj'
        exact ⟨n1 + n2, f, f', by rw [iterN_add, iterN_add]; exact hj2, hr2, hr2', hsh2,
          trace_add2 ht1 ht2⟩
      · obtain ⟨n2, f, f', hj2, hr2, hr2', hsh2, ht2⟩ :=
          ih d.measure d d' _ _ (Nat.le_refl _) hrd hrd' hpi hsh' hj'
        exact ⟨n1 + n2, f, f', by rw [iterN_add, iterN_add]; exact hj2, hr2, hr2', hsh2,
          trace_add2 ht1 ht2⟩

/-- **Joint forward simulation.** Along a run of pair steps from configurations related to the
allocated-code configurations (shape-equal, the pair invariant at the start), both machines
realise both runs jointly: after the same number of steps they reach states satisfying `J` at
shape-equal configurations related to the pair run's end. -/
theorem forward2 {sem sem' : ISem V W} {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationS vc rf keep sem R) (hR' : IsSimulationS vc rf keep sem' R')
    {PI : VConf V W → VConf V W → Prop} {K : MConf V W → MConf V W → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K e e')
    {step step' : S → S} {J : S → MConf V W → S → MConf V W → Prop} {T : S → S → Prop}
    (hJ : RealizesJ vc rf sem sem' keep step step' K J T)
    {v v' x x' : VConf V W} (hp : Star (PStep vc sem sem' PI) (v, v') (x, x'))
    {c c' : MConf V W} {s s' : S} (hr : R c v) (hr' : R' c' v') (hpi : PI v v')
    (hsh : MConf.ShapeEq c c') (hj : J s c s' c') :
    ∃ n d d', J (iterN step n s) d (iterN step' n s') d' ∧ R d x ∧ R' d' x' ∧
      MConf.ShapeEq d d' ∧ ∀ i < n, T (iterN step i s) (iterN step' i s') :=
  forward2_aux hR hR' hK hJ hp _ c c' s s' (Nat.le_refl _) hr hr' hpi hsh hj

/-- **Both machines advanced past the pending moves**: at a pair state with a pair step, from
related shape-equal configurations, the machines reach (after the same number of steps) states
satisfying `J` at shape-equal instruction items related to the pair state. -/
theorem forward2_op {sem sem' : ISem V W} {R R' : MConf V W → VConf V W → Prop}
    (hR : IsSimulationS vc rf keep sem R) (hR' : IsSimulationS vc rf keep sem' R')
    {PI : VConf V W → VConf V W → Prop} {K : MConf V W → MConf V W → Prop}
    (hK : ∀ e e' x x', R e x → R' e' x' → PI x x' → K e e')
    {step step' : S → S} {J : S → MConf V W → S → MConf V W → Prop} {T : S → S → Prop}
    (hJ : RealizesJ vc rf sem sem' keep step step' K J T)
    {v v' x x' : VConf V W} (hx : VStep vc sem v x) (hx' : VStep vc sem' v' x')
    (hsa : VConf.SameAt x x') (hpi : PI v v') :
    ∀ k (c c' : MConf V W) s s', c.measure ≤ k → R c v → R' c' v' → MConf.ShapeEq c c' →
      J s c s' c' →
      ∃ n b k a its m w a' its' m' w', J (iterN step n s) (.run ⟨b, .op k a :: its, m, w⟩)
          (iterN step' n s') (.run ⟨b, .op k a' :: its', m', w'⟩) ∧
        R (.run ⟨b, .op k a :: its, m, w⟩) v ∧ R' (.run ⟨b, .op k a' :: its', m', w'⟩) v' ∧
        MConf.ShapeEq (.run ⟨b, .op k a :: its, m, w⟩) (.run ⟨b, .op k a' :: its', m', w'⟩) ∧
        ∀ i < n, T (iterN step i s) (iterN step' i s') := by
  intro k
  induction k with
  | zero =>
    intro c c' s s' hk hr hr' hsh hj
    obtain ⟨e, he⟩ := hR.progress hr hx
    cases he with
    | move => simp [MConf.measure] at hk
    | op =>
      cases c' with
      | run s1 =>
        obtain ⟨b', its', m', w'⟩ := s1
        obtain ⟨rfl, rfl⟩ := hsh
        exact ⟨0, _, _, _, _, _, _, _, _, _, _, hj, hr, hr', ⟨rfl, rfl⟩,
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
      | ret => exact hsh.elim
      | halt => exact hsh.elim
  | succ k ihk =>
    intro c c' s s' hk hr hr' hsh hj
    obtain ⟨e, he⟩ := hR.progress hr hx
    cases he with
    | @move b src dst its m w =>
      cases c' with
      | run s1 =>
        obtain ⟨b', its', m', w'⟩ := s1
        obtain ⟨rfl, rfl⟩ := hsh
        have hm : MStep vc sem keep rf (.run ⟨b, .move src dst :: its, m, w⟩)
            (.run ⟨b, its, upd m dst (m src), w⟩) := MStep.move
        have hm' : MStep vc sem' keep rf (.run ⟨b, .move src dst :: its, m', w'⟩)
            (.run ⟨b, its, upd m' dst (m' src), w'⟩) := MStep.move
        obtain ⟨n1, d, d', hd, hd', hj', ht1⟩ := hJ s _ s' _ _ _ hj hm hm' fun e e' a b' => by
          obtain ⟨hs, -⟩ := hR.step2 hR' hr hr' ⟨rfl, rfl⟩ hx hx' hsa a b'
          refine ⟨hs, ?_⟩
          cases a with
          | move =>
            cases b' with
            | move => exact hK _ _ _ _ (hR.move hr) (hR'.move hr') hpi
        obtain ⟨hsh', -⟩ := hR.step2 hR' hr hr' ⟨rfl, rfl⟩ hx hx' hsa hd hd'
        have hrd : R d v ∧ R' d' v' ∧ d.measure < (MConf.run ⟨b, .move src dst :: its, m, w⟩ :
            MConf V W).measure := by
          cases hd with
          | move => cases hd' with
            | move => exact ⟨hR.move hr, hR'.move hr', by simp [MConf.measure]⟩
        obtain ⟨hrd, hrd', hlt⟩ := hrd
        obtain ⟨n2, b2, k2, a2, its2, m2, w2, a2', its2', m2', w2', hj2, hr2, hr2', hsh2, ht2⟩ :=
          ihk d d' _ _ (by omega) hrd hrd' hsh' hj'
        exact ⟨n1 + n2, b2, k2, a2, its2, m2, w2, a2', its2', m2', w2',
          by rw [iterN_add, iterN_add]; exact hj2, hr2, hr2', hsh2, trace_add2 ht1 ht2⟩
      | ret => exact hsh.elim
      | halt => exact hsh.elim
    | op =>
      cases c' with
      | run s1 =>
        obtain ⟨b', its', m', w'⟩ := s1
        obtain ⟨rfl, rfl⟩ := hsh
        exact ⟨0, _, _, _, _, _, _, _, _, _, _, hj, hr, hr', ⟨rfl, rfl⟩,
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
      | ret => exact hsh.elim
      | halt => exact hsh.elim

end

end Backend.Proof
