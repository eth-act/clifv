import FV.E2E.RegLevelForward2
import FV.Backend.Proof.PerEdgeRegallocSound
import FV.Backend.Proof.RegallocSimulationBy

/-!
# Block- and op-pinning allocation simulations over any code step

`IsSimulationS` (FV/E2E/RegLevelForward2) is the legacy allocation simulation that also pins the
block of every running configuration and matches an op item by exactly one code step; the joint
(two-run) realization lemmas consume it. `IsSimulationSBy` takes the code step as a parameter
(over `IsSimulationBy`), and converts to and from `IsSimulationS`. The per-successor checker's
relation `PerEdge.Match` is such a simulation over `VStepAt` (`PerEdge.isSimulationS_match`), by the
same op-step argument as the legacy one (`PerEdge.sim_step_op_at`).
-/

namespace Backend.Proof

open Backend

section
variable {V W : Type}

variable (vc : VCode) (rf : RFunc) (keep : Reg → V → V) in
/-- `IsSimulationS` with the code step as a parameter. -/
structure IsSimulationSBy (vstep : VConf V W → VConf V W → Prop) (sem : ISem V W)
    (R : MConf V W → VConf V W → Prop) : Prop extends IsSimulationBy vc rf sem keep vstep R where
  blk : ∀ {s v},R (.run s) v → ∃ vs,v = .run vs ∧ vs.b = s.b
  opStep : ∀ {b k a its m w v c'},R (.run ⟨b,.op k a :: its,m,w⟩) v →
    MStep vc sem keep rf (.run ⟨b,.op k a :: its,m,w⟩) c' → ∃ v',vstep v v' ∧ R c' v'

variable {vc : VCode} {rf : RFunc} {keep : Reg → V → V} {sem : ISem V W}

theorem IsSimulationS.toBy {R : MConf V W → VConf V W → Prop} (hR : IsSimulationS vc rf keep sem R) :
    IsSimulationSBy vc rf keep (VStep vc sem) sem R :=
  { toIsSimulationBy := hR.toIsSimulation.toBy,blk := hR.blk,opStep := hR.opStep }

theorem IsSimulationSBy.toLegacy {R : MConf V W → VConf V W → Prop}
    (hR : IsSimulationSBy vc rf keep (VStep vc sem) sem R) : IsSimulationS vc rf keep sem R :=
  { toIsSimulation := hR.toIsSimulationBy.toLegacy,blk := hR.blk,opStep := hR.opStep }

end

end Backend.Proof

namespace Backend.Proof.PerEdge

open Backend

section
variable {V W : Type} {edges : Array (Array (Array Reg))}
  {vc : VCode} {rf : RFunc} {c : CheckCtx} {ins : Array (Option AState)}
  (sem : ISem V W) (keep : Reg → V → V) {r₀ : Reg → V}

private theorem succOf_index {preds : Array (Array Nat)}
    (cfg : vc.cfg = .ok (c.succs,preds)) {b index target : Nat}
    (selected : succOf vc b index = some target) :
    (c.succs[b]?.getD #[])[index]? = some target := by
  simp only [succOf,cfg] at selected
  cases row : c.succs[b]? with
  | none => simp [row] at selected
  | some targets => simpa only [row,Option.bind_some,Option.getD_some] using selected

/-- **An op item related by `Match` steps with exactly one per-successor code step** (the op case
of `sim_step_at`). -/
theorem sim_step_op_at {a0 : AState} (hc : CheckedAt vc edges rf c ins a0) {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → V} {w : W} {vs : VState V W}
    {c' : MConf V W} (hm : MatchRun c edges ins keep r₀ ⟨b,.op k allocs :: its,m,w⟩ vs)
    (hs : MStep vc sem keep rf (.run ⟨b,.op k allocs :: its,m,w⟩) c') :
    ∃ v',VStepAt vc edges sem (.run vs) v' ∧ Match c edges ins keep r₀ c' v' := by
  obtain ⟨b',k',ρ,w''⟩ := vs
  obtain ⟨hb,hw,vb,a,out,hvb,hrun,hinv,hedges⟩ := hm
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
      exact ⟨_, VStepAt.step hvb hi hops hsem hlen' (VNextAt.next hk1),
        rfl, rfl, vb, _, out, hvbc, hrun', hinv', hedges⟩
    | ret hus =>
      rw [tryForget_of_ne (ctl := .ret) (fun _ e => nomatch e)] at hinv'
      exact ⟨_, VStepAt.step hvb hi hops hsem hlen' (VNextAt.ret hus), rfl, rfl,
        fun r hr => (hinv' _ _ (hret _ hus r hr)).2⟩
    | halt =>
      exact ⟨_, VStepAt.step hvb hi hops hsem hlen' VNextAt.halt, rfl⟩
    | @goto j target items hk1 hsucc hitems =>
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
      obtain ⟨e, a'', hedge, hins, hle⟩ := hedges j target (succOf_index hcfg hsucc)
      have hcfg' : c.vc.cfg = .ok (c.succs, preds) := by rw [hc.vc_eq]; exact hcfg
      have hinvF := edgeForget_inv hcfg' hvbc hi hk1 hops (by rw [hc.vc_eq]; exact hsucc) hinv'
      obtain ⟨ρ', henv, hinve⟩ := edge_ok hedge hinvF
      rw [hc.vc_eq] at henv
      obtain ⟨items', hitems', hmr⟩ := enter_block_at keep hc (w := w') (edgeEnv_lt henv) hins hle hinve
      rw [hitems] at hitems'
      cases hitems'
      exact ⟨_, VStepAt.step hvb hi hops hsem hlen' (VNextAt.goto hk1 hsucc henv), hmr⟩

/-- `checkedAt_sound` for the relation `Match` of its proof. -/
theorem checkedAt_sound_match {a0 : AState} (hc : CheckedAt vc edges rf c ins a0) (m₀ : Loc → V)
    (ρ₀ : Nat → V) (w₀ : W) (hinv0 : Inv keep a0 m₀ ρ₀ (fun r => m₀ (.reg r))) :
    IsSimulation vc rf sem keep edges (Match c edges ins keep (fun r => m₀ (.reg r))) ∧
      Match c edges ins keep (fun r => m₀ (.reg r)) (MConf.init rf m₀ w₀) (VConf.init ρ₀ w₀) ∧
      ∀ {vals m} {w : W} {v},Match c edges ins keep (fun r => m₀ (.reg r)) (.ret vals m w) v →
        ∀ r ∈ calleeSaved,keep r (m (.reg r)) = keep r (m₀ (.reg r)) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro cf v c' hR hs
    cases cf with
    | run ms =>
      cases v with
      | run vs =>
        rcases sim_step_at sem keep hc hR hs with ⟨ms', rfl, hmr, hlt⟩ | hr
        · exact .inl ⟨hmr, hlt⟩
        · exact .inr hr
      | ret => exact hR.elim
      | halt => exact hR.elim
    | ret => cases hs
    | halt => cases hs
  · intro cf v v' hR hv
    cases cf with
    | run ms =>
      cases v with
      | run vs => exact sim_progress_at sem keep hc hR hv
      | ret => exact hR.elim
      | halt => exact hR.elim
    | ret => cases v <;> first | exact hR.elim | cases hv
    | halt => cases v <;> first | exact hR.elim | cases hv
  · intro vals m w v hR
    cases v with
    | ret vals' w' => obtain ⟨rfl, rfl, -⟩ := hR; rfl
    | _ => exact hR.elim
  · intro w v hR
    cases v with
    | halt w' => cases hR; rfl
    | _ => exact hR.elim
  · intro s v hR
    cases v with
    | run s' => exact ⟨s', rfl⟩
    | _ => exact hR.elim
  · intro b src dst its m w v hR
    cases v with
    | run vs =>
      obtain ⟨hb, hw, vb, a, out, hvb, hrun, hinv, hedges⟩ := hR
      obtain ⟨-, hrun'⟩ := runItems_move hrun
      exact ⟨hb, hw, vb, _, out, hvb, hrun', Inv_move _ _ hinv, hedges⟩
    | _ => exact hR.elim
  · intro b k a its m w vs hR
    obtain ⟨hb, hw, vb, a, out, hvb, hrun, -⟩ := hR
    obtain ⟨-, hk, -⟩ := runItems_op hrun
    exact ⟨hb.symm, hk.symm, hw.symm⟩
  · obtain ⟨a, out, ha, hrb, hedges⟩ :=
      verifyBlock_ok (hc.blocks 0 (Nat.pos_of_ne_zero hc.nonempty))
    rw [hc.entry] at ha
    cases ha
    obtain ⟨vb, items, hvb, hitems, hrun⟩ := runBlock_ok hrb
    rw [hc.rf_eq] at hitems
    have : rf.blocks[0]! = items := by simp [getElem!_def, hitems]
    simp only [MConf.init, VConf.init, this]
    exact ⟨rfl, rfl, vb, a0, out, hvb, hrun, hinv0, hedges⟩
  · intro vals m w v hR
    cases v with
    | ret => exact hR.2.2
    | _ => exact hR.elim

/-- **The per-successor `Match` is an `IsSimulationSBy` over `VStepAt`.** -/
theorem isSimulationS_match {a0 : AState} (hc : CheckedAt vc edges rf c ins a0) (m₀ : Loc → V)
    (ρ₀ : Nat → V) (w₀ : W) (hinv0 : Inv keep a0 m₀ ρ₀ (fun r => m₀ (.reg r))) :
    IsSimulationSBy vc rf keep (VStepAt vc edges sem) sem (Match c edges ins keep (fun r => m₀ (.reg r))) ∧
      Match c edges ins keep (fun r => m₀ (.reg r)) (MConf.init rf m₀ w₀) (VConf.init ρ₀ w₀) := by
  obtain ⟨hS,hinit,-⟩ := checkedAt_sound_match sem keep hc m₀ ρ₀ w₀ hinv0
  refine ⟨{ toIsSimulationBy := hS.toBy,blk := ?_,opStep := ?_ },hinit⟩
  · intro s v h
    cases v with
    | run vs => exact ⟨vs,rfl,h.1.symm⟩
    | ret => exact h.elim
    | halt => exact h.elim
  · intro b k a its m w v c' h hs
    cases v with
    | run vs => exact sim_step_op_at sem keep hc h hs
    | ret => exact h.elim
    | halt => exact h.elim

end

end Backend.Proof.PerEdge
