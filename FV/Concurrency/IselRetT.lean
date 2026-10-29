import FV.Concurrency.IselDriverT

/-!
# The terminator step on `DriverHypT` (#473, the `rets` end)

`Driver.term_step_abi`/`term_step` restated on `DriverHypT` (their proofs use no `ext` field):
`term_step_abiT`, **`term_stepRT`** — at a matched `return`, the VCode run reaches its `rets`
with the returned values held (`PrefixHold`) and the memory relation at the return.
-/

namespace Concurrency.IselRetT

open Backend Backend.Proof Backend.Proof.Driver Concurrency

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)}

/-- **Terminator step**, with the ABI return values: a `return` also returns the frame's
`sretRet f` values (`abiTerm`), all held by the VCode return's use values. `term_step` is the
CLIF-values-only corollary. -/
theorem term_step_abiT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
        Match f ctx R gn bl A MR slots s' vs') ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w' sv, VRetFrom vc sem ⟨b, k, ρ, w⟩ us outs w' ∧
        RetPins vals us ∧ us.length = outs.length ∧
        s.frame.getMany (sretRet f) = .ok sv ∧ AllHold (vals ++ sv) outs ∧
        MR slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave) ∧
    (∀ c, Clif.step env p s = .trapped c → VTrapFrom vc sem ⟨b, k, ρ, w⟩ c) := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := hm
  simp only at hk hheld hcons hB hmem
  subst hk
  have hjn : j = B.body.length := by
    rw [hbd] at hbody
    have := List.drop_eq_nil_iff.mp hbody
    omega
  subst hjn
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, -, -, htemp, hst0t, hnontry, -, hcode, htne, -, hbargs, hsucc⟩ :=
    H.shape.blk b B L hB hL
  have hBnt : B.term.isTry = false := hterm ▸ hnt
  obtain ⟨htl0, hdata, out, tr, hrunT⟩ := hnontry hBnt
  obtain ⟨ranges, hctx⟩ := H.shape.hctx
  have htlen : TargetsLen B.term L.targets := by
    intro x d tbl hT
    have hs := hsucc
    rw [hT] at hs
    obtain ⟨hlt, -⟩ := hs
    rw [hlt]
    simp [dests]
  have hok := H.terms f ctx (L.start + B.body.length) (abiTerm f B.term) L.data L.targets out
    L.tst L.tst' tr H.shape.ctxInv (brIdxTyped_abiTerm (H.brIdx B (List.mem_of_getElem? hB)))
    (targetsLen_abiTerm htlen) (H.shape.tslot b B L hB hL)
    (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0t) hdata htemp
    (by rw [termCall_abiTerm]; exact hrunT)
  obtain ⟨hargsTA, hnoclobT, -⟩ := H.cert.term b B L hB hL
  have hargsT : ∀ y ∈ termArgs B.term, y ∈ A b B.body.length :=
    fun y hy => hargsTA y (termArgs_abiTerm hy)
  let fr' := restrict s.frame (A b B.body.length)
  let ρ₀ : Nat → CV := fun n => ρ (gn n)
  have hvh : ValsHeld fr' ρ₀ := by
    intro x v hx
    have hxA : x ∈ A b B.body.length := restrict_regs_isSome (by rw [hx]; rfl)
    obtain ⟨v', hv', hh⟩ := hheld x hxA
    rw [restrict_regs_of_mem hxA, hv'] at hx
    cases hx
    exact hh
  have hrun' := hok.run fr' s.mem ρ₀ w
    (by simp [fr', restrict, hfunc, termCtx, H.shape.ctxInv.func]) hvh (dfgCons_termCtx hcons _ _)
    (by simpa [fr', restrict, hslots] using hmem)
  let D : Nat → Prop := fun n => L.tst.nextVreg ≤ n ∧ n < L.tst'.nextVreg
  have hD : ∀ d, D d → gn d = d := fun d hd => H.shape.temps d (by
    have : L.tst.nextVreg ≤ d := hd.1; omega)
  have hdefs : ∀ m ∈ L.tst'.emitted.toList, ∀ d ∈ vdefs m, D d := hok.defs
  have hAg : Agree gn D ρ₀ ρ := fun _ _ => rfl
  have huses_of : UsesOk L.tst fr' L.tst'.emitted.toList →
      ∀ m ∈ L.tst'.emitted.toList, ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
    intro hU m hm u hu
    rcases hU m hm u hu with h | h
    · by_cases h' : u < L.tst'.nextVreg
      · exact .inl ⟨h, h'⟩
      · right
        rw [H.shape.temps u (by omega)]
        intro hd; exact h' hd.2
    · right; exact hnoclobT u (restrict_regs_isSome h)
  have hren := seqRun_rename (sem := sem) (ρ₀ := ρ₀) (ρ := ρ) (w := w) H.shape.ren
    (H.dsem.rename R gn H.shape.ren) hD hdefs
  obtain ⟨hsegat, hsize⟩ := tseg_at hcode
  rw [tseg_eq_none hL htl0] at hsegat hsize htne
  have hstep : Clif.step env p s = Clif.stepTerm env p s B.term := by
    rw [Clif.step_term env p s hbody, hterm]
  -- tracked values keep their registers across the terminator's code
  have hkeep : ∀ {k' i ops ρ₁ w₁ outs w₂ ctl ρ₁'},
      seqRun sem L.tst'.emitted.toList ρ₀ w = some (.stop k' i ops ρ₁ w₁ outs w₂ ctl) →
      Agree gn D (vdefUpd ops outs ρ₁) (vdefUpd (ops.map (rnOp gn)) outs ρ₁') →
      ∀ x ∈ A b B.body.length, vdefUpd (ops.map (rnOp gn)) outs ρ₁' (gn x) = ρ (gn x) := by
    intro k' i ops ρ₁ w₁ outs w₂ ctl ρ₁' hsr hA2 x hx
    have hnd : ¬ D x := by
      have h4 : x < st0.nextVreg := H.cert.small _ _ x hx
      intro hd
      have h3 : L.tst.nextVreg ≤ x := hd.1
      exact absurd (Nat.lt_of_lt_of_le h4 hst0t) (Nat.not_lt.mpr h3)
    rw [← hA2 x (.inr (hnoclobT x hx))]
    exact (seqRun_stop_frame (fun m hm hxm => hnd (hdefs m hm x hxm)) hsr).2
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  have hargsR : ∀ y ∈ termArgs B.term, fr'.regs y = s.frame.regs y :=
    fun y hy => restrict_regs_of_mem (hargsT y hy)
  -- branches
  have hnext_br : dests B.term ≠ [] → ∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, pos f R bl b B.body.length, ρ, w⟩) (.run vs') ∧
        Match f ctx R gn bl A MR slots s' vs' := by
    intro hne s' hs
    rw [hstep] at hs
    obtain ⟨j', bc, fr2, hbi, hbc, hent, rfl⟩ := stepTerm_branch hne hs
    have hbr : (∀ i, L.tst'.emitted.toList.getLast? = some i → i.targets = L.targets) ∧
        ∀ j, branchIdx fr' B.term = .ok j → UsesOk L.tst fr' L.tst'.emitted.toList ∧
          ∃ k i ops ρ₁ w₁ outs w₂,
            seqRun sem L.tst'.emitted.toList ρ₀ w = some (.stop k i ops ρ₁ w₁ outs w₂ (.goto j)) ∧
            k + 1 = L.tst'.emitted.toList.length ∧ MR fr'.slots s.mem w₂ := by
      cases hT : B.term with
      | jump bc0 => rw [hT] at hrun'; exact hrun'
      | brif c t e => rw [hT] at hrun'; exact hrun'
      | brTable x d tbl => rw [hT] at hrun'; exact hrun'
      | _ => rw [hT] at hne; simp [dests] at hne
    obtain ⟨htg, hgo⟩ := hbr
    have hbi' : branchIdx fr' B.term = .ok j' := by
      rw [← hbi]
      cases hT : B.term with
      | brif c t e =>
        rw [hT] at hargsR
        simp only [branchIdx, Clif.Frame.get, hargsR c (by simp [termArgs])]
      | brTable x d tbl =>
        rw [hT] at hargsR
        simp only [branchIdx, Clif.Frame.get, hargsR x (by simp [termArgs])]
      | _ => rfl
    obtain ⟨hU, k', i, ops, ρ₁, w₁, outs, w₂, hsr, hk1, hmr⟩ := hgo j' hbi'
    obtain ⟨ρ₁', hsr', -, hA2⟩ := (hren (huses_of hU) hAg).2 hsr
    obtain ⟨hstar, -, hi, hops, hsem, hlen, -⟩ := seqRun_stop_star hvb hsegat hsr'
    obtain ⟨hmk, -⟩ := seqRun_stop_mem hsr
    have hlast : L.tst'.emitted.toList.getLast? = some i := by
      rw [List.getLast?_eq_getElem?, ← hk1, Nat.add_sub_cancel]; exact hmk
    have hK : pos f R bl b B.body.length + k' + 1 = vb.insts.size := by
      rw [hsize, List.length_map, ← hk1]; omega
    have hback : vb.insts.back? = some (i.mapRegs R) := by
      rw [Array.back?_eq_getElem?, ← hK, Nat.add_sub_cancel]; exact hi
    obtain ⟨ss, ps, hcfg⟩ := H.cfg
    have hsucc_eq : ∀ jj, succOf vc b jj = L.targets[jj]? := fun jj => by
      rw [succOf_eq H.shape.labels hcfg hvb hback, targets_mapRegs, htg i hlast]
    have hρ₂ := hkeep hsr hA2
    have hbcmem : bc ∈ dests B.term := List.mem_of_getElem? hbc
    have hmr' : MR slots s.mem w₂ := by simpa [fr', restrict, hslots] using hmr
    -- the successor
    split at hsucc
    · rename_i bc0 hT
      rw [hT] at hbargs hbc
      obtain ⟨tl, htl, htgs⟩ := hsucc
      have hj0 : j' = 0 ∧ bc = bc0 := by
        cases j' with
        | zero => simp [dests] at hbc; exact ⟨rfl, hbc.symm⟩
        | succ n => simp [dests] at hbc
      obtain ⟨rfl, rfl⟩ := hj0
      obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match_brT H hB hcall hfunc hslots hheld hcons hbcmem
        htl hent hρ₂ hmr'
      obtain ⟨Lt, hLt⟩ := H.blow hTB
      obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
      simp only [hne0, ite_false] at hpt
      have henv := edgeEnv_eq (V := CV) hvb hvbt (xs := bc.args.map gn) (ps := TB.params.map (·.1))
        (by rw [hbargs]; simp [List.map_map, Function.comp_def, H.shape.ren.vreg])
        (by rw [hpt]; simp [List.map_map, Function.comp_def]) (by simp; omega)
        (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
      refine ⟨_, hstar.trans (Star.single (VStep.step hvb hi hops hsem hlen
        (VNext.goto hK (by rw [hsucc_eq, htgs]; rfl) henv))), hM⟩
    · rename_i fn0 args0 et0 hT
      rw [hT] at hBnt; cases hBnt
    · rename_i callee0 args0 et0 hT
      rw [hT] at hBnt; cases hBnt
    · rename_i hnj _ _
      have hbargs' : vb.branchArgs = #[] := by
        rw [hbargs]; split
        · rename_i bc0 hT; exact absurd hT (hnj bc0)
        · rfl
      obtain ⟨hlt, hall⟩ := hsucc
      have hjlt : j' < L.targets.length := by
        rw [hlt]; exact (List.getElem?_eq_some_iff.mp hbc).1
      obtain ⟨tl, htl, hnil, hedge⟩ := hall j' bc L.targets[j'] hbc (List.getElem?_eq_getElem hjlt)
      obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match_brT H hB hcall hfunc hslots hheld hcons hbcmem
        htl hent hρ₂ hmr'
      obtain ⟨Lt, hLt⟩ := H.blow hTB
      obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
      simp only [hne0, ite_false] at hpt
      by_cases hargs0 : bc.args = []
      · have hp0 : TB.params = [] := by
          rw [hargs0] at hlenA; exact List.eq_nil_of_length_eq_zero hlenA.symm
        have henv := edgeEnv_eq (V := CV) hvb hvbt (xs := []) (ps := [])
          (by rw [hbargs']; rfl) (by rw [hpt, hp0]; rfl) rfl (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
        rw [hargs0, hp0] at hM
        refine ⟨_, hstar.trans (Star.single (VStep.step hvb hi hops hsem hlen
          (VNext.goto hK (by rw [hsucc_eq, List.getElem?_eq_getElem hjlt, hnil hargs0]) henv))), hM⟩
      · obtain ⟨eb, heb, hebi, hebp, hebba⟩ := hedge hargs0
        have henv1 := edgeEnv_eq (V := CV) hvb heb (xs := []) (ps := [])
          (by rw [hbargs']; rfl) (by rw [hebp]; rfl) rfl (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
        have henv2 := edgeEnv_eq (V := CV) heb hvbt (xs := bc.args.map gn) (ps := TB.params.map (·.1))
          (by rw [hebba]; simp [List.map_map, Function.comp_def, H.shape.ren.vreg])
          (by rw [hpt]; simp [List.map_map, Function.comp_def]) (by simp; omega)
          (parCopyEnv (vdefUpd (ops.map (rnOp gn)) outs ρ₁') [] [])
        have hpc : parCopyEnv (vdefUpd (ops.map (rnOp gn)) outs ρ₁') [] [] =
            vdefUpd (ops.map (rnOp gn)) outs ρ₁' := rfl
        rw [hpc] at henv2
        have hebback : eb.insts.back? = some (.jump tl) := by rw [hebi]; rfl
        have hstep1 := VStep.step hvb hi hops hsem hlen
          (VNext.goto hK (by rw [hsucc_eq, List.getElem?_eq_getElem hjlt]) henv1)
        have hstep2 : VStep vc sem (.run ⟨L.targets[j'], 0,
            parCopyEnv (vdefUpd (ops.map (rnOp gn)) outs ρ₁') [] [], w₂⟩)
            (.run ⟨tl, 0, parCopyEnv (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
              (TB.params.map (·.1)) (bc.args.map gn), w₂⟩) := by
          rw [hpc]
          refine VStep.step heb (by rw [hebi]; rfl) (i := .jump tl) (ops := #[]) rfl
            (H.dsem.jump tl w₂) rfl (VNext.goto (by rw [hebi]; rfl) ?_ henv2)
          rw [succOf_eq H.shape.labels hcfg heb hebback]; rfl
        exact ⟨_, hstar.trans (.step hstep1 (Star.single hstep2)), hM⟩
  cases hT : B.term with
  | ret xs =>
    rw [hT] at hrun' hstep hargsR hargsTA
    simp only [abiTerm] at hrun' hargsTA
    obtain ⟨hn, htr, hdn⟩ := stepTerm_ret (env := env) (p := p) (s := s) (xs := xs) hcall
    refine ⟨fun s' hs => ?_, fun vals cm hs => ?_, fun c hs => ?_⟩
    · rw [hstep] at hs; exact absurd hs (hn s')
    rotate_left
    · rw [hstep] at hs; exact absurd hs (htr c)
    rw [hstep] at hs
    obtain ⟨hg, hcm⟩ := hdn vals cm hs
    have hg0 : fr'.getMany xs = .ok vals := by
      rw [getMany_congr (fun x hx => hargsR x (by simpa [termArgs] using hx))]; exact hg
    -- the returned `sret` pointer (`abiTerm`) is a tracked value, defined in the frame
    have hyA : ∀ y ∈ sretRet f, y ∈ A b B.body.length :=
      fun y hy => hargsTA y (by simp [termArgs, hy])
    obtain ⟨vs, hvs0⟩ := getMany_append_of (fr := fr') (ys := sretRet f) (xs := []) (vals := [])
      (fun y hy => by
        obtain ⟨v, hv, -⟩ := hheld y (hyA y hy)
        exact ⟨v, by rw [restrict_regs_of_mem (hyA y hy)]; exact hv⟩) rfl
    simp only [List.nil_append] at hvs0
    have hg' := getMany_append hg0 hvs0
    have hvsS : s.frame.getMany (sretRet f) = .ok vs := by
      rw [← hvs0]
      exact (getMany_congr (fun y hy => restrict_regs_of_mem (hyA y hy))).symm
    obtain ⟨hU, k', us, ops, ρ₁, w₁, outs, w₂, hsr, hus, hlen, hall, hmr⟩ := hrun' _ hg'
    obtain ⟨ρ₁', hsr', hA1, -⟩ := (hren (huses_of hU) hAg).2 hsr
    obtain ⟨hstar, -, hi, hops, hsem, -, -⟩ := seqRun_stop_star hvb hsegat hsr'
    obtain ⟨hmk, hopsU⟩ := seqRun_stop_mem hsr
    have hvu : vuses (ops.map (rnOp gn)) ρ₁' = vuses ops ρ₁ := by
      apply vuses_rename hA1
      intro o ho hu
      apply huses_of hU _ (List.mem_of_getElem? hmk) o.vreg
      simp only [vuseNums, hopsU, List.mem_map, List.mem_filter]
      exact ⟨o, ⟨by simpa using ho, hu⟩, rfl⟩
    refine ⟨_, vuses ops ρ₁, w₂, vs, ⟨b, _, ρ₁', w₁, vb, ops.map (rnOp gn), outs, hstar, hvb, hi, hops,
      hvu.symm, by rw [← hvu]; exact hsem⟩, ?_, ?_, hvsS, hall,
      by simpa [fr', restrict, hslots] using hmr, by rw [hcm, hslots]⟩
    · have hvl : vs.length = (sretRet ctx.func).length := by
        rw [H.shape.ctxInv.func]; exact (getMany_spec hvs0).1.symm
      have hvl' : (sretRet (termCtx ctx (L.start + B.body.length) L.data).func).length =
          (sretRet ctx.func).length := by simp [termCtx]
      unfold RetPins
      simp only [List.map_map, List.length_map, Function.comp_def]
      rw [hus, List.length_append, hvl, hvl', Nat.add_sub_cancel]
    · simp only [List.length_map]; rw [hlen]; exact hall.1
  | trap c =>
    rw [hT] at hrun' hstep
    refine ⟨fun s' hs => ?_, fun vals cm hs => ?_, fun c' hs => ?_⟩
    · rw [hstep] at hs; cases hs
    · rw [hstep] at hs; cases hs
    rw [hstep] at hs
    simp only [Clif.stepTerm, Clif.StepResult.trapped.injEq] at hs
    subst hs
    obtain ⟨hU, k', i, ops, ρ₁, w₁, outs, w₂, hsr, htc⟩ := hrun'
    obtain ⟨ρ₁', hsr', -, -⟩ := (hren (huses_of hU) hAg).2 hsr
    obtain ⟨hstar, -, hi, hops, hsem, -, -⟩ := seqRun_stop_star hvb hsegat hsr'
    exact ⟨b, _, ρ₁', w₁, vb, _, _, outs, w₂, hstar, hvb, hi, hops, hsem,
      by rw [trapCode?_mapRegs]; exact htc⟩
  | returnCall fn args => exact absurd hT (H.noTail B hBmem fn args)
  | tryCall _ _ _ => rw [hT] at hBnt; cases hBnt
  | tryCallIndirect _ _ _ => rw [hT] at hBnt; cases hBnt
  | jump bc =>
    have hne : dests B.term ≠ [] := by rw [hT]; simp [dests]
    refine ⟨hnext_br hne, fun vals cm hs => ?_, fun c hs => ?_⟩
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).1 vals cm)
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).2 c)
  | brif c t e =>
    have hne : dests B.term ≠ [] := by rw [hT]; simp [dests]
    refine ⟨hnext_br hne, fun vals cm hs => ?_, fun c hs => ?_⟩
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).1 vals cm)
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).2 c)
  | brTable x d tbl =>
    have hne : dests B.term ≠ [] := by rw [hT]; simp [dests]
    refine ⟨hnext_br hne, fun vals cm hs => ?_, fun c hs => ?_⟩
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).1 vals cm)
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).2 c)

/-- **Terminator step**: returns, traps, branches (a `try_call`: `term_step_try`). -/
theorem term_stepRT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
        Match f ctx R gn bl A MR slots s' vs') ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w', VRetFrom vc sem ⟨b, k, ρ, w⟩ us outs w' ∧
        RetPins vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MR slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave) ∧
    (∀ c, Clif.step env p s = .trapped c → VTrapFrom vc sem ⟨b, k, ρ, w⟩ c) := by
  obtain ⟨T1, T2, T3⟩ := term_step_abiT H hm hbody hnt
  refine ⟨T1, fun vals cm hs => ?_, T3⟩
  obtain ⟨us, outs, w', sv, h1, h2, h3, -, h5, h6, h7⟩ := T2 vals cm hs
  exact ⟨us, outs, w', h1, h2, h3, AllHold.prefix_append h5, h6, h7⟩


end

end Concurrency.IselRetT
