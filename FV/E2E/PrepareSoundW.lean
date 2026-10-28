import FV.Backend.Proof.PrepareSound

/-!
# Soundness of the `prepare` validator for any world (SEM1, `docs/plans/uninit.md` §5.9)

`prep_sound` (`FV/Backend/Proof/PrepareSound.lean`) is stated for `Sem` (the Arm world) with
`DriverSem`, but its proof uses only `DriverSemG`'s `jump` and `retarget`. The counted VCode run
(`csemI`, world `Arm.ArmState × Nat`) needs it for another world: `prep_soundW` is the same
proof (copied: the statement there stays) for `ISem CV W` with `DriverSemG`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

theorem sameInst_factsW {W : Type} {sem : ISem CV W} (hds : DriverSemG sem) {i i' : MInst}
    (h : SameInst i i') :
    i'.operands = i.operands ∧ trapCode? i' = trapCode? i ∧ sem i' = sem i ∧
      ∀ us, i' = .rets us → i = .rets us := by
  rcases h with rfl | h
  · exact ⟨rfl, rfl, rfl, fun _ e => e⟩
  · obtain ⟨h1, h2, -, h4⟩ := setTargets_facts h
    exact ⟨h1, h2, hds.retarget i _ i' h, fun us e => absurd e (h4 us)⟩

section
variable {W : Type} {vc vcp : VCode} {sem : ISem CV W}

/-- `prep_step` for any world. -/
theorem prep_stepW (hds : DriverSemG sem) {ss ps ss' ps' : Array (Array Nat)}
    (hcfg : vc.cfg = .ok (ss, ps)) (hcfg' : vcp.cfg = .ok (ss', ps')) {L : Nat → Prop}
    (hL : ∀ (b : Nat) (sb : Array Nat) (j s : Nat), L b → ss[b]? = some sb → sb[j]? = some s → L s)
    (hk : ∀ b b', L b → sigmaOf vc vcp b = some b' → Kept vc vcp ss ss' b b')
    {b b' k : Nat} {ρ : Nat → CV} {w : W} {s2 : VState CV W}
    (hLb : L b) (hσ : sigmaOf vc vcp b = some b') (h : VStep vc sem (.run ⟨b, k, ρ, w⟩) (.run s2)) :
    ∃ b2', L s2.b ∧ sigmaOf vc vcp s2.b = some b2' ∧
      Star (VStep vcp sem) (.run ⟨b', k, ρ, w⟩) (.run ⟨b2', s2.k, s2.ρ, s2.w⟩) := by
  obtain ⟨vb, vb', hvb, hvb', hpar, hba, hsz, hins, sb, sb', hsb, hsb', hsucc⟩ :=
    (hk b b' hLb hσ).blocks
  cases h with
  | step hvb0 hi hops hsem hlen hnext =>
    rename_i vb0 i ops outs w' ctl
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨i', hi', hsame⟩ := hins k i hi
    obtain ⟨hops', -, hsem', -⟩ := sameInst_factsW hds hsame
    have hops2 : i'.operands = .ok ops := by rw [hops', hops]
    have hsem2 : sem i' ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w = some (outs, w', ctl) := by
      rw [hsem']; exact hsem
    cases hnext with
    | next hlt =>
      refine ⟨b', hLb, hσ, Star.single (VStep.step hvb' hi' hops2 hsem2 hlen ?_)⟩
      exact VNext.next (by rw [hsz]; exact hlt)
    | goto hlast hsucc0 hedge =>
      rename_i j s ρ2
      rw [succOf_cfg hcfg, hsb] at hsucc0
      simp only [Option.bind_some] at hsucc0
      have hLs := hL b sb j s hLb hsb hsucc0
      obtain ⟨s', t, hs', ht, hroute⟩ := hsucc j s hsucc0
      obtain ⟨vs, vs', hvs, hvs', hpars, hbas, -, -, -⟩ := (hk s s' hLs hs').blocks
      have hsuccT : succOf vcp b' j = some t := by
        rw [succOf_cfg hcfg', hsb']; simpa using ht
      rcases hroute with rfl | ⟨hbnil, eb, l, heb, hebi, hebp, hebb, hts⟩
      · have heq : ∀ ρx : Nat → CV, edgeEnv vcp b' t ρx = edgeEnv vc b s ρx := by
          intro ρx
          simp [edgeEnv, hvb, hvb', hvs, hvs', hpars, hba]
        have hedge' := (heq _).trans hedge
        exact ⟨t, hLs, hs', Star.single (VStep.step hvb' hi' hops2 hsem2 hlen
          (VNext.goto (by rw [hsz]; exact hlast) hsuccT hedge'))⟩
      · have hsp : vs.params = #[] := by
          cases hps : vs.params.size with
          | zero => exact Array.eq_empty_of_size_eq_zero hps
          | succ n => simp [edgeEnv, hvb, hvs, hbnil, hps] at hedge
        have hρ2 : ρ2 = (writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
            (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) := by
          rw [edgeEnv_nil hvb hvs hbnil hsp] at hedge
          exact (Option.some.inj hedge).symm
        subst hρ2
        have hstep1 := VStep.step (vc := vcp) (sem := sem) hvb' hi' hops2 hsem2 hlen
          (VNext.goto (by rw [hsz]; exact hlast) hsuccT
            (edgeEnv_nil hvb' heb (by rw [hba]; exact hbnil) hebp _))
        have hj0 : eb.insts[0]? = some (.jump l) := by rw [hebi]; rfl
        have hjops : (MInst.jump l).operands = .ok #[] := rfl
        have hjsem : sem (.jump l) ((#[] : Array Operand).toList.filter Operand.isUse |>.map
            (fun o => (writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
              (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) o.vreg)) w' =
            some ([], w', .goto 0) := hds.jump l w'
        have hstep2 := VStep.step (vc := vcp) (sem := sem) heb hj0 hjops hjsem rfl
          (VNext.goto (by rw [hebi]; rfl) (by rw [succOf_cfg hcfg', hts]; rfl)
            (edgeEnv_nil heb hvs' hebb (by rw [hpars]; exact hsp) _))
        refine ⟨s', hLs, hs', .step hstep1 (Star.single ?_)⟩
        simpa [writeV] using hstep2

/-- `prep_star` for any world. -/
theorem prep_starW (hds : DriverSemG sem) {ss ps ss' ps' : Array (Array Nat)}
    (hcfg : vc.cfg = .ok (ss, ps)) (hcfg' : vcp.cfg = .ok (ss', ps')) {L : Nat → Prop}
    (hL : ∀ (b : Nat) (sb : Array Nat) (j s : Nat), L b → ss[b]? = some sb → sb[j]? = some s → L s)
    (hk : ∀ b b', L b → sigmaOf vc vcp b = some b' → Kept vc vcp ss ss' b b') :
    ∀ {c c' : VConf CV W}, Star (VStep vc sem) c c' →
      ∀ (s s2 : VState CV W) b', c = .run s → c' = .run s2 →
        L s.b → sigmaOf vc vcp s.b = some b' → ∃ b2', L s2.b ∧ sigmaOf vc vcp s2.b = some b2' ∧
          Star (VStep vcp sem) (.run ⟨b', s.k, s.ρ, s.w⟩) (.run ⟨b2', s2.k, s2.ρ, s2.w⟩) := by
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
      obtain ⟨bm, hLm, hbm, hs1⟩ := prep_stepW hds hcfg hcfg' hL hk hLb hσ hst
      obtain ⟨b2', hL2, hb2, hs2⟩ := ih sm s2 bm rfl rfl hLm hbm
      exact ⟨b2', hL2, hb2, hs1.trans hs2⟩
    | ret vals w => cases hrest with | step h _ => cases h
    | halt w => cases hrest with | step h _ => cases h

end

/-- **Soundness of the `prepare` validator for any world** (`prep_sound` for `ISem CV W` with
`DriverSemG`). -/
theorem prep_soundW {W : Type} {vc vcp : VCode} {sem : ISem CV W} (hds : DriverSemG sem)
    (h : prepCheck vc vcp = true) (ρ₀ : Nat → CV) (w₀ : W) :
    (∀ us vals w, VRetFrom vc sem ⟨0, 0, ρ₀, w₀⟩ us vals w →
      VRetFrom vcp sem ⟨0, 0, ρ₀, w₀⟩ us vals w) ∧
    (∀ c, VTrapFrom vc sem ⟨0, 0, ρ₀, w₀⟩ c → VTrapFrom vcp sem ⟨0, 0, ρ₀, w₀⟩ c) := by
  unfold prepCheck at h
  split at h
  · rename_i ss ps ss' ps' hcfg hcfg'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h0, hl0⟩, hall⟩, -⟩ := h
    let L : Nat → Prop := fun b => b < vc.blocks.size ∧ liveOf ss b = true
    have hchk : ∀ b, L b → ∃ b', sigmaOf vc vcp b = some b' ∧ keptOk vc vcp ss ss' b b' = true ∧
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
    have hk : ∀ b b', L b → sigmaOf vc vcp b = some b' → Kept vc vcp ss ss' b b' := by
      intro b b' hLb hσ
      obtain ⟨b'', hσ', hkept, -⟩ := hchk b hLb
      rw [hσ] at hσ'; cases hσ'
      exact keptOk_sound hkept
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
      obtain ⟨b', hLb, hb', hstar'⟩ := prep_starW hds hcfg hcfg' hL hk hstar ⟨0, 0, ρ₀, w₀⟩
        ⟨b, k, ρ, w₁⟩ 0 rfl rfl hL0 h0
      obtain ⟨vb0, vb', hvb0, hvb', -, -, -, hins, -⟩ := (hk b b' hLb hb').blocks
      rw [hvb] at hvb0; cases hvb0
      obtain ⟨i', hi', hsame⟩ := hins k _ hi
      have hi'' : i' = .rets us := by
        rcases hsame with rfl | hst
        · rfl
        · exact absurd rfl ((setTargets_facts hst).2.2.1 us)
      subst hi''
      exact ⟨b', k, ρ, w₁, vb', ops, outs, hstar', hvb', hi', hops, hvals, hsem⟩
    · intro c ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩
      obtain ⟨b', hLb, hb', hstar'⟩ := prep_starW hds hcfg hcfg' hL hk hstar ⟨0, 0, ρ₀, w₀⟩
        ⟨b, k, ρ, w⟩ 0 rfl rfl hL0 h0
      obtain ⟨vb0, vb', hvb0, hvb', -, -, -, hins, -⟩ := (hk b b' hLb hb').blocks
      rw [hvb] at hvb0; cases hvb0
      obtain ⟨i', hi', hsame⟩ := hins k i hi
      obtain ⟨hops', htc', hsem', -⟩ := sameInst_factsW hds hsame
      exact ⟨b', k, ρ, w, vb', i', ops, outs, w', hstar', hvb', hi', by rw [hops', hops],
        by rw [hsem']; exact hsem, by rw [htc']; exact htc⟩
  · cases h

end Backend.Proof.Driver
