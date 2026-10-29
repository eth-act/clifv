module

public import FV.Backend.RegallocPerEdgePrepareCheck
public import FV.Backend.Proof.PerEdgeVCodeSem
public import FV.Backend.Proof.PrepareSound
public import FV.Backend.Proof.RegallocSound

@[expose] public section

/-! Indexed preparation simulation. Structural routes retain the actual chosen
vector in direct cases, or move that vector onto a real synthetic jump after an
identity first copy. Existing single-vector proof variants remain unchanged. -/
namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Proof.Driver

structure KeptAt (vc vcp : VCode) (edges edges' : Array (Array (Array Reg)))
    (ss ss' : Array (Array Nat)) (b b' : Nat) : Prop where
  blocks : ∃ vb vb',vc.blocks[b]? = some vb ∧ vcp.blocks[b']? = some vb' ∧
    vb'.params = vb.params ∧ vb'.branchArgs = vb.branchArgs ∧ vb'.insts.size = vb.insts.size ∧
    (∀ (k : Nat) (i : MInst),vb.insts[k]? = some i → ∃ i',vb'.insts[k]? = some i' ∧ SameInst i i') ∧
    ∃ sb sb',ss[b]? = some sb ∧ ss'[b']? = some sb' ∧
      ∀ (j s : Nat),sb[j]? = some s → ∃ s' t,sigmaOf vc vcp s = some s' ∧ sb'[j]? = some t ∧
        ((t = s' ∧ (edges'[b']?.bind (·[j]?)) = edges[b]?.bind (·[j]?)) ∨
          ((edges'[b']?.bind (·[j]?)) = some #[] ∧
            (∃ eb l,vcp.blocks[t]? = some eb ∧ eb.insts = #[.jump l] ∧ eb.params = #[] ∧ ss'[t]? = some #[s']) ∧
            (edges'[t]?.bind (·[0]?)) = edges[b]?.bind (·[j]?)))

theorem edgeBlockOkAt_sound {vc : VCode} {ss : Array (Array Nat)} {t s : Nat}
    (h : edgeBlockOkAt vc ss t s = true) : ∃ eb l,vc.blocks[t]? = some eb ∧
      eb.insts = #[.jump l] ∧ eb.params = #[] ∧ ss[t]? = some #[s] := by
  unfold edgeBlockOkAt at h
  split at h
  · rename_i eb placed
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨jump,params⟩,successors⟩ := h
    split at jump
    · rename_i l code
      refine ⟨eb,l,placed,?_,params,successors⟩
      rw [← Array.toList_inj,code]
    · cases jump
  · cases h

theorem keptOkAt_sound {vc vcp : VCode} {ss ss' : Array (Array Nat)} {edges edges' : Array (Array (Array Reg))} {b b' : Nat}
    (h : keptOkAt vc vcp edges edges' ss ss' b b' = true) : KeptAt vc vcp edges edges' ss ss' b b' := by
  unfold keptOkAt at h
  split at h
  · rename_i vb vb' hvb hvb'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hp, hba⟩, hsz⟩, hpop⟩, hlast⟩, hsucc⟩ := h
    refine ⟨vb, vb', hvb, hvb', hp, hba, hsz, ?_, ?_⟩
    · intro k i hi
      have hk : k < vb.insts.size := (Array.getElem?_eq_some_iff.mp hi).1
      by_cases hl : k < vb.insts.size - 1
      · refine ⟨i, ?_, .inl rfl⟩
        have e := congrArg (·[k]?) hpop
        simp only [Array.getElem?_pop, hsz, hl, ite_true] at e
        rw [e, hi]
      · have hk' : k = vb.insts.size - 1 := by omega
        subst hk'
        unfold lastOk at hlast
        rw [Array.back?_eq_getElem?, Array.back?_eq_getElem?, hi, hsz] at hlast
        split at hlast
        · rename_i i0 i' h0 h'
          cases h0
          refine ⟨i', h', ?_⟩
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hlast
          exact hlast
        · rename_i h0 _; cases h0
        · rename_i h1 _
          exfalso
          simp_all
    · split at hsucc
      · rename_i sb sb' hsb hsb'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hsucc
        refine ⟨sb, sb', hsb, hsb', fun j s hs => ?_⟩
        have hj : j < sb.size := (Array.getElem?_eq_some_iff.mp hs).1
        have := all_range hsucc.2 hj
        rw [hs] at this
        have hj' : j < sb'.size := by rw [hsucc.1]; exact hj
        have ht : sb'[j]? = some sb'[j] := Array.getElem?_eq_getElem hj'
        rw [ht] at this
        simp only at this
        cases hs' : sigmaOf vc vcp s with
        | none => rw [hs'] at this; cases this
        | some s' =>
          rw [hs'] at this
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
          refine ⟨s', sb'[j], rfl, ht, ?_⟩
          rcases this with ⟨same, arguments⟩ | ⟨⟨empty, edge⟩, arguments⟩
          · exact .inl ⟨same,arguments⟩
          · exact .inr ⟨empty,edgeBlockOkAt_sound edge,arguments⟩
      · cases hsucc
  · cases h


private theorem sameInstG_facts {W : Type} {sem : ISem CV W} (hds : DriverSemG sem)
    {i i' : MInst} (h : SameInst i i') :
    i'.operands = i.operands ∧ trapCode? i' = trapCode? i ∧ sem i' = sem i ∧
      ∀ us,i' = .rets us → i = .rets us := by
  rcases h with rfl | retarget
  · exact ⟨rfl,rfl,rfl,fun _ e => e⟩
  · obtain ⟨operands,trap,_,notRet⟩ := setTargets_facts retarget
    exact ⟨operands,trap,hds.retarget i _ i' retarget,fun us same => absurd same (notRet us)⟩

private def copyWithParams {V : Type} (params : Array Reg) (row : Option (Array Reg))
    (ρ : Nat → V) : Option (Nat → V) := do
  let args ← row
  if args.size = params.size then
    let ps ← (params.toList.mapM vregNum).toOption
    let xs ← (args.toList.mapM vregNum).toOption
    pure (parCopyEnv ρ ps xs)
  else none

private theorem edgeEnvAt_formula {V : Type} {vc : VCode} {edges : Array (Array (Array Reg))}
    {b s j : Nat} {block : VBlock} (placed : vc.blocks[s]? = some block) (ρ : Nat → V) :
    edgeEnvAt vc edges b s j ρ = copyWithParams block.params (edges[b]?.bind (·[j]?)) ρ := by
  unfold edgeEnvAt
  rw [placed]
  rfl

private theorem edgeEnvAt_empty {V : Type} {vc : VCode} {edges : Array (Array (Array Reg))}
    {b s j : Nat} {block : VBlock} (placed : vc.blocks[s]? = some block)
    (params : block.params = #[]) (args : edges[b]?.bind (·[j]?) = some #[]) (ρ : Nat → V) :
    edgeEnvAt vc edges b s j ρ = some ρ := by
  simp [edgeEnvAt,placed,params,args,Except.toOption]
  rfl

section
variable {W : Type} {vc vcp : VCode} {edges edges' : Array (Array (Array Reg))} {sem : ISem CV W}
theorem prep_step (hds : DriverSemG sem) {ss ps ss' ps' : Array (Array Nat)}
    (hcfg : vc.cfg = .ok (ss, ps)) (hcfg' : vcp.cfg = .ok (ss', ps')) {L : Nat → Prop}
    (hL : ∀ (b : Nat) (sb : Array Nat) (j s : Nat), L b → ss[b]? = some sb → sb[j]? = some s → L s)
    (hk : ∀ b b', L b → sigmaOf vc vcp b = some b' → KeptAt vc vcp edges edges' ss ss' b b')
    {b b' k : Nat} {ρ : Nat → CV} {w : W} {s2 : VState CV W}
    (hLb : L b) (hσ : sigmaOf vc vcp b = some b') (h : VStepAt vc edges sem (.run ⟨b, k, ρ, w⟩) (.run s2)) :
    ∃ b2', L s2.b ∧ sigmaOf vc vcp s2.b = some b2' ∧
      Star (VStepAt vcp edges' sem) (.run ⟨b', k, ρ, w⟩) (.run ⟨b2', s2.k, s2.ρ, s2.w⟩) := by
  obtain ⟨vb, vb', hvb, hvb', hpar, hba, hsz, hins, sb, sb', hsb, hsb', hsucc⟩ :=
    (hk b b' hLb hσ).blocks
  cases h with
  | step hvb0 hi hops hsem hlen hnext =>
    rename_i vb0 i ops outs w' ctl
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨i', hi', hsame⟩ := hins k i hi
    obtain ⟨hops', -, hsem', -⟩ := sameInstG_facts hds hsame
    have hops2 : i'.operands = .ok ops := by rw [hops', hops]
    have hsem2 : sem i' ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w = some (outs, w', ctl) := by
      rw [hsem']; exact hsem
    cases hnext with
    | next hlt =>
      refine ⟨b', hLb, hσ, Star.single (VStepAt.step hvb' hi' hops2 hsem2 hlen ?_)⟩
      exact VNextAt.next (by rw [hsz]; exact hlt)
    | goto hlast hsucc0 hedge =>
      rename_i j s ρ2
      rw [succOf_cfg hcfg, hsb] at hsucc0
      simp only [Option.bind_some] at hsucc0
      have hLs := hL b sb j s hLb hsb hsucc0
      obtain ⟨s', t, hs', ht, hroute⟩ := hsucc j s hsucc0
      obtain ⟨vs, vs', hvs, hvs', hpars, hbas, -, -, -⟩ := (hk s s' hLs hs').blocks
      have hsuccT : succOf vcp b' j = some t := by
        rw [succOf_cfg hcfg', hsb']; simpa using ht
      rcases hroute with ⟨rfl,hargs⟩ | ⟨hempty,⟨eb,l,heb,hebi,hebp,hts⟩,hargs⟩
      · -- direct
        have heq : ∀ ρx : Nat → CV, edgeEnvAt vcp edges' b' t j ρx = edgeEnvAt vc edges b s j ρx := by
          intro ρx
          rw [edgeEnvAt_formula hvs',edgeEnvAt_formula hvs,hpars,hargs]
        have hedge' := (heq _).trans hedge
        exact ⟨t, hLs, hs', Star.single (VStepAt.step hvb' hi' hops2 hsem2 hlen
          (VNextAt.goto (by rw [hsz]; exact hlast) hsuccT hedge'))⟩
      · -- through the edge block
        have heq : ∀ ρx : Nat → CV,edgeEnvAt vcp edges' t s' 0 ρx = edgeEnvAt vc edges b s j ρx := by
          intro ρx
          rw [edgeEnvAt_formula hvs',edgeEnvAt_formula hvs,hpars,hargs]
        have hstep1 := VStepAt.step (vc := vcp) (sem := sem) hvb' hi' hops2 hsem2 hlen
          (VNextAt.goto (by rw [hsz]; exact hlast) hsuccT
            (edgeEnvAt_empty heb hebp hempty _))
        have hj0 : eb.insts[0]? = some (.jump l) := by rw [hebi]; rfl
        have hjops : (MInst.jump l).operands = .ok #[] := rfl
        have hjsem : sem (.jump l) ((#[] : Array Operand).toList.filter Operand.isUse |>.map
            (fun o => (writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
              (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) o.vreg)) w' =
            some ([], w', .goto 0) := hds.jump l w'
        have hstep2 := VStepAt.step (vc := vcp) (sem := sem) heb hj0 hjops hjsem rfl
          (VNextAt.goto (by rw [hebi]; rfl) (by rw [succOf_cfg hcfg', hts]; rfl)
            ((heq _).trans hedge))
        refine ⟨s', hLs, hs', .step hstep1 (Star.single ?_)⟩
        simpa [writeV] using hstep2

/-- Runs of `vc` between running states are runs of `vcp` between the counterparts. -/
theorem prep_star (hds : DriverSemG sem) {ss ps ss' ps' : Array (Array Nat)}
    (hcfg : vc.cfg = .ok (ss, ps)) (hcfg' : vcp.cfg = .ok (ss', ps')) {L : Nat → Prop}
    (hL : ∀ (b : Nat) (sb : Array Nat) (j s : Nat), L b → ss[b]? = some sb → sb[j]? = some s → L s)
    (hk : ∀ b b', L b → sigmaOf vc vcp b = some b' → KeptAt vc vcp edges edges' ss ss' b b') :
    ∀ {c c' : VConf CV W}, Star (VStepAt vc edges sem) c c' →
      ∀ (s s2 : VState CV W) b', c = .run s → c' = .run s2 →
        L s.b → sigmaOf vc vcp s.b = some b' → ∃ b2', L s2.b ∧ sigmaOf vc vcp s2.b = some b2' ∧
          Star (VStepAt vcp edges' sem) (.run ⟨b', s.k, s.ρ, s.w⟩) (.run ⟨b2', s2.k, s2.ρ, s2.w⟩) := by
  intro c c' hstar
  induction hstar with
  | refl a =>
    intro s s2 b' h1 h2 hLb hσ
    subst h1; cases h2
    exact ⟨b', hLb, hσ, .refl _⟩
  | @step a mid c2 hst hrest ih =>
    intro s s2 b' h1 h2 hLb hσ
    subst h1 h2
    cases mid with
    | run sm =>
      obtain ⟨sb, sk, sρ, sw⟩ := s
      obtain ⟨bm, hLm, hbm, hs1⟩ := prep_step hds hcfg hcfg' hL hk hLb hσ hst
      obtain ⟨b2', hL2, hb2, hs2⟩ := ih sm s2 bm rfl rfl hLm hbm
      exact ⟨b2', hL2, hb2, hs1.trans hs2⟩
    | ret vals w => cases hrest with | step h _ => cases h
    | halt w => cases hrest with | step h _ => cases h

end

def VTrapFromAt {W : Type} (vc : VCode) (edges : Array (Array (Array Reg))) (sem : ISem CV W) (vs : VState CV W) (c : Clif.TrapCode) :
    Prop :=
  ∃ b k ρ w vb i ops outs w', Star (VStepAt vc edges sem) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
    sem i (vuses ops ρ) w = some (outs, w', .halt) ∧ trapCode? i = some c

/-- From `vs`, the VCode run executes `rets us` with use values `vals`, final world `w`. -/
def VRetFromAt {W : Type} (vc : VCode) (edges : Array (Array (Array Reg))) (sem : ISem CV W) (vs : VState CV W) (us : List (Reg × Reg))
    (vals : List CV) (w : W) : Prop :=
  ∃ b k ρ w₁ vb ops outs, Star (VStepAt vc edges sem) (.run vs) (.run ⟨b, k, ρ, w₁⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.rets us) ∧
    (MInst.rets us).operands = .ok ops ∧ vals = vuses ops ρ ∧
    sem (.rets us) vals w₁ = some (outs, w, .ret)

private theorem checked_facts {vc vcp : VCode} {edges edges' : Array (Array (Array Reg))}
    (h : prepCheckAt vc edges ⟨vcp,edges'⟩ = true) :
    ∃ (ss ps ss' ps' : Array (Array Nat)) (L : Nat → Prop),
      vc.cfg = .ok (ss,ps) ∧ vcp.cfg = .ok (ss',ps') ∧ L 0 ∧ sigmaOf vc vcp 0 = some 0 ∧
      (∀ (b : Nat) (sb : Array Nat) (j target : Nat),L b → ss[b]? = some sb → sb[j]? = some target → L target) ∧
      (∀ b b',L b → sigmaOf vc vcp b = some b' → KeptAt vc vcp edges edges' ss ss' b b') := by
  dsimp only [prepCheckAt] at h
  split at h
  · rename_i ss ps ss' ps' hcfg hcfg'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h0, hl0⟩, hall⟩, -⟩ := h
    let L : Nat → Prop := fun b => b < vc.blocks.size ∧ liveOf ss b = true
    have hchk : ∀ b, L b → ∃ b', sigmaOf vc vcp b = some b' ∧ keptOkAt vc vcp edges edges' ss ss' b b' = true ∧
        (ss[b]?.getD #[]).all (fun s => decide (s < vc.blocks.size) && liveOf ss s) = true := by
      intro b ⟨hlt, hlb⟩
      have := all_range hall hlt
      rw [hlb] at this
      simp only [Bool.not_true, Bool.false_or] at this
      split at this
      · cases this
      · rename_i b' hσ
        simp only [Bool.and_eq_true] at this
        exact ⟨b', hσ, this.1, this.2⟩
    have hk : ∀ b b', L b → sigmaOf vc vcp b = some b' → KeptAt vc vcp edges edges' ss ss' b b' := by
      intro b b' hLb hσ
      obtain ⟨b'', hσ', hkept, -⟩ := hchk b hLb
      rw [hσ] at hσ'; cases hσ'
      exact keptOkAt_sound hkept
    have hL : ∀ (b : Nat) (sb : Array Nat) (j s : Nat), L b → ss[b]? = some sb → sb[j]? = some s → L s := by
      intro b sb j s hLb hsb hs
      obtain ⟨-, -, -, hall'⟩ := hchk b hLb
      rw [hsb, Option.getD_some] at hall'
      have := (Array.all_eq_true_iff_forall_mem.mp hall') s (Array.mem_of_getElem? hs)
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
    have hL0 : L 0 := by
      refine ⟨?_, hl0⟩
      unfold sigmaOf at h0
      split at h0
      · rename_i vb hvb; exact (Array.getElem?_eq_some_iff.mp hvb).1
      · cases h0
    exact ⟨ss,ps,ss',ps',L,hcfg,hcfg',hL0,h0,hL,hk⟩
  · cases h

/-- A real step in the original entry block is matched through the internally
checked direct or synthetic route, retaining its register file and world. -/
theorem prep_entry_step {W : Type} {vc vcp : VCode} {edges edges' : Array (Array (Array Reg))}
    {sem : ISem CV W} (hds : DriverSemG sem) (checked : prepCheckAt vc edges ⟨vcp,edges'⟩ = true)
    {k : Nat} {ρ : Nat → CV} {w : W} {target : VState CV W}
    (h : VStepAt vc edges sem (.run ⟨0,k,ρ,w⟩) (.run target)) :
    ∃ b',sigmaOf vc vcp target.b = some b' ∧
      Star (VStepAt vcp edges' sem) (.run ⟨0,k,ρ,w⟩) (.run ⟨b',target.k,target.ρ,target.w⟩) := by
  obtain ⟨ss,ps,ss',ps',L,cfg,cfg',live0,entry,closed,kept⟩ := checked_facts checked
  obtain ⟨b',_,mapped,steps⟩ := prep_step hds cfg cfg' closed kept live0 entry h
  exact ⟨b',mapped,steps⟩

private theorem star_last {α : Type} {r : α → α → Prop} {a c : α}
    (h : Star r a c) (different : a ≠ c) : ∃ b,Star r a b ∧ r b c := by
  induction h with
  | refl a => exact False.elim (different rfl)
  | @step a mid c first rest ih =>
    by_cases equal : mid = c
    · subst equal
      exact ⟨a,.refl _,first⟩
    · obtain ⟨b,prelude,last⟩ := ih equal
      exact ⟨b,.step first prelude,last⟩

private def IsTerminal {V W : Type} : VConf V W → Prop
  | .run _ => False
  | _ => True

private theorem terminal_step {W : Type} {vc vcp : VCode} {edges edges' : Array (Array (Array Reg))}
    {sem : ISem CV W} (hds : DriverSemG sem) {ss ss' : Array (Array Nat)} {b b' k : Nat}
    {ρ : Nat → CV} {w : W} {target : VConf CV W}
    (kept : KeptAt vc vcp edges edges' ss ss' b b')
    (h : VStepAt vc edges sem (.run ⟨b,k,ρ,w⟩) target)
    (terminal : IsTerminal target) :
    VStepAt vcp edges' sem (.run ⟨b',k,ρ,w⟩) target := by
  obtain ⟨vb,vb',placed,placed',_,_,size,instructions,_⟩ := kept.blocks
  cases h with
  | step block instruction operands semantics length next =>
    rename_i vb0 i ops outs world ctl
    rw [placed] at block
    cases block
    obtain ⟨i',found,same⟩ := instructions k i instruction
    obtain ⟨opEq,_,semEq,_⟩ := sameInstG_facts hds same
    have operands' : i'.operands = .ok ops := opEq.trans operands
    have semantics' : sem i' ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w =
        some (outs,world,ctl) := by rw [semEq]; exact semantics
    cases next with
    | next => exact terminal.elim
    | goto => exact terminal.elim
    | @ret us ret =>
      have ret' : i' = .rets us := by
        rcases same with rfl | retarget
        · exact ret
        · exact False.elim ((setTargets_facts retarget).2.2.1 us ret)
      exact VStepAt.step placed' found operands' semantics' length (.ret ret')
    | halt => exact VStepAt.step placed' found operands' semantics' length .halt

private theorem terminal_star {W : Type} {vc vcp : VCode} {edges edges' : Array (Array (Array Reg))}
    {sem : ISem CV W} (hds : DriverSemG sem) (checked : prepCheckAt vc edges ⟨vcp,edges'⟩ = true)
    {ρ : Nat → CV} {w : W} {target : VConf CV W}
    (h : Star (VStepAt vc edges sem) (VConf.init ρ w) target)
    (terminal : IsTerminal target) :
    Star (VStepAt vcp edges' sem) (VConf.init ρ w) target := by
  obtain ⟨ss,ps,ss',ps',L,cfg,cfg',live0,entry,closed,kept⟩ := checked_facts checked
  have different : VConf.init ρ w ≠ target := by
    intro equal
    rw [← equal] at terminal
    exact terminal
  obtain ⟨last,prelude,step⟩ := star_last h different
  cases last with
  | run state =>
    obtain ⟨b',live,found,prelude'⟩ := prep_star hds cfg cfg' closed kept prelude
      ⟨0,0,ρ,w⟩ state 0 rfl rfl live0 entry
    exact prelude'.trans (.single (terminal_step hds (kept state.b b' live found) step terminal))
  | ret => cases step
  | halt => cases step

/-- Complete returns, including the return instruction itself, survive indexed
preparation with identical values and world, for arbitrary worlds. -/
theorem prep_ret {W : Type} {vc vcp : VCode} {edges edges' : Array (Array (Array Reg))}
    {sem : ISem CV W} (hds : DriverSemG sem) (checked : prepCheckAt vc edges ⟨vcp,edges'⟩ = true)
    {ρ : Nat → CV} {w w' : W} {vals : List CV}
    (h : Star (VStepAt vc edges sem) (VConf.init ρ w) (.ret vals w')) :
    Star (VStepAt vcp edges' sem) (VConf.init ρ w) (.ret vals w') :=
  terminal_star hds checked h trivial

/-- Complete halts survive indexed preparation with identical world. -/
theorem prep_halt {W : Type} {vc vcp : VCode} {edges edges' : Array (Array (Array Reg))}
    {sem : ISem CV W} (hds : DriverSemG sem) (checked : prepCheckAt vc edges ⟨vcp,edges'⟩ = true)
    {ρ : Nat → CV} {w w' : W}
    (h : Star (VStepAt vc edges sem) (VConf.init ρ w) (.halt w')) :
    Star (VStepAt vcp edges' sem) (VConf.init ρ w) (.halt w') :=
  terminal_star hds checked h trivial

theorem prep_sound {W : Type} {vc vcp : VCode} {edges edges' : Array (Array (Array Reg))}
    {sem : ISem CV W} (hds : DriverSemG sem) (h : prepCheckAt vc edges ⟨vcp,edges'⟩ = true)
    (ρ₀ : Nat → CV) (w₀ : W) :
    (∀ us vals w, VRetFromAt vc edges sem ⟨0, 0, ρ₀, w₀⟩ us vals w →
      VRetFromAt vcp edges' sem ⟨0, 0, ρ₀, w₀⟩ us vals w) ∧
    (∀ c, VTrapFromAt vc edges sem ⟨0, 0, ρ₀, w₀⟩ c → VTrapFromAt vcp edges' sem ⟨0, 0, ρ₀, w₀⟩ c) := by
  dsimp only [prepCheckAt] at h
  split at h
  · rename_i ss ps ss' ps' hcfg hcfg'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h0, hl0⟩, hall⟩, -⟩ := h
    let L : Nat → Prop := fun b => b < vc.blocks.size ∧ liveOf ss b = true
    have hchk : ∀ b, L b → ∃ b', sigmaOf vc vcp b = some b' ∧ keptOkAt vc vcp edges edges' ss ss' b b' = true ∧
        (ss[b]?.getD #[]).all (fun s => decide (s < vc.blocks.size) && liveOf ss s) = true := by
      intro b ⟨hlt, hlb⟩
      have := all_range hall hlt
      rw [hlb] at this
      simp only [Bool.not_true, Bool.false_or] at this
      split at this
      · cases this
      · rename_i b' hσ
        simp only [Bool.and_eq_true] at this
        exact ⟨b', hσ, this.1, this.2⟩
    have hk : ∀ b b', L b → sigmaOf vc vcp b = some b' → KeptAt vc vcp edges edges' ss ss' b b' := by
      intro b b' hLb hσ
      obtain ⟨b'', hσ', hkept, -⟩ := hchk b hLb
      rw [hσ] at hσ'; cases hσ'
      exact keptOkAt_sound hkept
    have hL : ∀ (b : Nat) (sb : Array Nat) (j s : Nat), L b → ss[b]? = some sb → sb[j]? = some s → L s := by
      intro b sb j s hLb hsb hs
      obtain ⟨-, -, -, hall'⟩ := hchk b hLb
      rw [hsb, Option.getD_some] at hall'
      have := (Array.all_eq_true_iff_forall_mem.mp hall') s (Array.mem_of_getElem? hs)
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
    have hL0 : L 0 := by
      refine ⟨?_, hl0⟩
      unfold sigmaOf at h0
      split at h0
      · rename_i vb hvb; exact (Array.getElem?_eq_some_iff.mp hvb).1
      · cases h0
    constructor
    · intro us vals w ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩
      obtain ⟨b', hLb, hb', hstar'⟩ := prep_star hds hcfg hcfg' hL hk hstar ⟨0, 0, ρ₀, w₀⟩
        ⟨b, k, ρ, w₁⟩ 0 rfl rfl hL0 h0
      obtain ⟨vb0, vb', hvb0, hvb', -, -, -, hins, -⟩ := (hk b b' hLb hb').blocks
      rw [hvb] at hvb0; cases hvb0
      obtain ⟨i', hi', hsame⟩ := hins k _ hi
      obtain ⟨-, -, -, hrets⟩ := sameInstG_facts hds hsame
      have hi'' : i' = .rets us := by
        rcases hsame with rfl | hst
        · rfl
        · exact absurd rfl ((setTargets_facts hst).2.2.1 us)
      subst hi''
      exact ⟨b', k, ρ, w₁, vb', ops, outs, hstar', hvb', hi', hops, hvals, hsem⟩
    · intro c ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩
      obtain ⟨b', hLb, hb', hstar'⟩ := prep_star hds hcfg hcfg' hL hk hstar ⟨0, 0, ρ₀, w₀⟩
        ⟨b, k, ρ, w⟩ 0 rfl rfl hL0 h0
      obtain ⟨vb0, vb', hvb0, hvb', -, -, -, hins, -⟩ := (hk b b' hLb hb').blocks
      rw [hvb] at hvb0; cases hvb0
      obtain ⟨i', hi', hsame⟩ := hins k i hi
      obtain ⟨hops', htc', hsem', -⟩ := sameInstG_facts hds hsame
      exact ⟨b', k, ρ, w, vb', i', ops, outs, w', hstar', hvb', hi', by rw [hops', hops],
        by rw [hsem']; exact hsem, by rw [htc']; exact htc⟩
  · cases h


end Backend.Proof.PerEdgePrep
