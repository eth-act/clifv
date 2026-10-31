import FV.E2E.RegLevelCorrectU

/-!
# The register-level theorem with unwinding, keeping the trace (S10f, #233)

`regLevelCorrect_coreU` (`FV/E2E/RegLevelCorrectU.lean`) with the facts the linking needs
(`FV/E2E/LinkWorld.lean`'s `ActRet`/`PostTrace`, for the runs with unwinding):

* `regLevelCorrect_coreUT`: the core, keeping the trace of the run (`RLU.GoodXU` at every state
  before the end: no return into the function's own code but with the body's `sp`) and, at an
  exceptional end, the kept addresses `G`, the program, and that the last step leaves the frame by
  unwinding (`UnwExit`).
* `callDescAt`, `UnwExit`: the step of `Unw.ArmStepU X H U T fa` at `u` leaves `u`'s frame by
  unwinding (a call whose callee raises, the personality continuing).
-/

namespace E2E

open Backend Backend.Proof

/-- The hook descriptor of the call instruction at `u` (`bl n`: `some n`, `blr`: `none`). -/
noncomputable def callDescAt (fa : FnAsm) (u : Arm.ArmState) : Option (Option String) :=
  match insnAt fa (progBase u) (Arm.r .PC u) with
  | some (.bl n) => some (some n)
  | some (.blr _) => some none
  | _ => none

/-- **The step of `Unw.ArmStepU X H U T fa` at `u` leaves `u`'s frame by unwinding**: `u` is at a
call whose callee raises and the personality continues the unwinding. -/
def UnwExit (U : Unw.UnwHooks) (T : Unw.FnTables) (fa : FnAsm) (u : Arm.ArmState) : Prop :=
  ∃ d obj t, callDescAt fa u = some d ∧ U.raise d u = some (obj, t) ∧
    Unw.personality T.lsda (Arm.r .PC u + 4 - 1 - progBase u).toNat = .continue

/-- Without raising callees no step leaves a frame by unwinding. -/
theorem not_unwExit_none (T : Unw.FnTables) (fa : FnAsm) (u : Arm.ArmState) :
    ¬ UnwExit Unw.UnwHooks.none T fa u := by
  rintro ⟨d, obj, t, -, h, -⟩
  cases h

/-- **The exceptional end of an activation entered in `s` at `t`** (`ActRet`'s counterpart): an
AAPCS64 return to the caller as the unwinder leaves it (`ArmRet`), the exception object `obj` in
x0, the memory outside `F` and the unmasked fields but x29/`sp` as in the world `w` after the
unwinder restored the raising call, the kept addresses `G` and the program as at entry. -/
structure ActUnw (ra : BitVec 64) (F G : BitVec 64 → Prop) (obj : BitVec 64)
    (w s t : Arm.ArmState) : Prop where
  ret : ArmRet ra s t
  x0 : xreg 0 t = obj
  mem : ∀ a, ¬ F a → t.mem a = w.mem a
  gkeep : ∀ a, G a → t.mem a = s.mem a
  prog : t.program = s.program
  fields : ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f t = Arm.r f w

end E2E

namespace Backend.Proof

open Backend E2E Backend.Proof.UnwindTables
/-! ## The frame row restores only callee-saved registers, x29, x30, `sp`, `pc` -/

/-- A push row of callee-saved registers never names x18. -/
theorem pushRows_ne18 {saves : List Reg} (hsv : ∀ r ∈ saves, r ∈ calleeSaved) {st : Nat}
    {p : Nat × Int} (h : p ∈ (pushRows saves st).map offsetPair) : p.1 ≠ 18 := by
  obtain ⟨d, off⟩ := p
  obtain ⟨r, hr, hd, -⟩ := mem_pushRows h
  rcases calleeSaved_cases (hsv r (saves_of_IF hr)) with ⟨n, rfl, h1, -⟩ | ⟨n, rfl, -, -⟩
  · simp only [Reg.dwarf?, Option.some.injEq] at hd
    subst hd; dsimp only; omega
  · simp only [Reg.dwarf?, Option.some.injEq] at hd
    subst hd; dsimp only; omega

/-- **Unwinding a frame row keeps every unmasked field but x29 and `sp`.** -/
theorem restore_frameRow_fields {saved : List (Nat × Int)} (h18 : ∀ p ∈ saved, p.1 ≠ 18)
    {t t' : Arm.ArmState}
    (h : Unw.restore (frameRow saved) t = some t') :
    ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f t' = Arm.r f t := by
  intro f hf h29 h31
  simp only [Unw.restore, Option.map_eq_some_iff] at h
  obtain ⟨cfa, -, rfl⟩ := h
  cases f with
  | PC => exact absurd trivial hf
  | SFP i => exact absurd trivial hf
  | GPR i =>
    have h18 : i = 18#5 := by
      have n29 : i.toNat ≠ 29 := fun e =>
        h29 (by rw [BitVec.eq_of_toNat_eq (x := i) (y := 29#5) (by simp [e])])
      have n31 : i.toNat ≠ 31 := fun e =>
        h31 (by rw [BitVec.eq_of_toNat_eq (x := i) (y := 31#5) (by simp [e])])
      simp only [Masked, not_or, not_and, Decidable.not_not] at hf
      have hi := i.isLt
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega
    subst h18
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    have hl : (frameRow saved).saved.lookup 18 = none := by
      simp only [frameRow, List.lookup_append]
      rw [List.lookup_eq_none_iff.mpr]
      · rfl
      · intro p hp
        simpa [bne_iff_ne] using (h18 p (List.mem_reverse.mp hp)).symm
    have := Unw.restoreFold_gpr cfa t (n := 18) (by omega) (frameRow saved).saved
    rw [hl] at this
    exact this
  | _ =>
    rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)]
    exact Unw.restoreFold_other cfa t _ (by simp) (by simp) _

/-- **At a state of the old trace no step leaves the frame by unwinding** (a call there is a
normal call: its callee does not raise, `RLU.noRaise_of_goodX`). -/
theorem not_unwExit_of_goodX {R : RLU} (hR : R.Wf)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    {u : Arm.ArmState} (g : R.GoodX u) : ¬ UnwExit R.U R.T R.fa u := by
  rintro ⟨d, obj, t, hd, hr, -⟩
  obtain ⟨x, ⟨j, tt, hj, hpc⟩, -⟩ := g.line
  have hins := insnAt_pc hR hj g.prog hpc
  unfold callDescAt at hd
  rw [hins] at hd
  cases x with
  | bl n =>
    simp only [Option.some.injEq] at hd
    rw [RLU.noRaise_of_goodX hR hU g ⟨j, tt, hj, hpc⟩ (.inl ⟨n, rfl, hd.symm⟩)] at hr
    cases hr
  | blr r =>
    simp only [Option.some.injEq] at hd
    rw [RLU.noRaise_of_goodX hR hU g ⟨j, tt, hj, hpc⟩ (.inr ⟨r, rfl, hd.symm⟩)] at hr
    cases hr
  | _ => cases hd

/-- At an instruction line that is no call the machine with unwinding steps as the old one. -/
theorem RLU.stepU_eq_of_line {R : RLU} (hR : R.Wf) {v : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t)) (hpc : Arm.r .PC v = R.pcOf j)
    (hprog : v.program = R.fb.program R.base) (h1 : ∀ n, x ≠ .bl n) (h2 : ∀ r, x ≠ .blr r) :
    R.stepU v = R.step v := by
  have hins := insnAt_pc hR hj hprog hpc
  simp only [RLU.stepU, RL.step, Unw.ArmStepU, hins]
  cases x with
  | bl n => exact absurd rfl (h1 n)
  | blr r => exact absurd rfl (h2 r)
  | _ => rfl

/-- From the step at a `udf` line on, every state of the machine with unwinding errs
(`RL.udf_stuck`: the `udf` is no call). -/
theorem RLU.udf_stuckU {R : RLU} (hR : R.Wf) {u : Arm.ArmState} {j : Nat}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins (.udf 0xc11f) t))
    (hpc : Arm.r .PC u = R.pcOf j) (hprog : u.program = R.fb.program R.base)
    (herr : Arm.r .ERR u = .None) : ∀ m, Arm.r .ERR (iterN R.stepU (m + 1) u) ≠ .None := by
  obtain ⟨a, ha, hst⟩ := armStepX_ins (X := R.X) (H := R.H) hR.layout hR.lm hR.fit hj rfl hprog hpc
    herr
  obtain ⟨a', ha', he, hp, hpr⟩ := exec_udf_insn ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ u
  rw [ha] at ha'; cases ha'
  have hs : R.step u = Arm.exec_inst a u := hst
  have hpc1 : Arm.r .PC (R.step u) = R.pcOf j := by rw [hs, hp, hpc]
  have hprog1 : (R.step u).program = R.fb.program R.base := by rw [hs, hpr, hprog]
  have herr1 : Arm.r .ERR (R.step u) ≠ .None := by rw [hs]; exact he
  have h0 : R.stepU u = R.step u :=
    RLU.stepU_eq_of_line hR hj hpc hprog (fun _ h => by cases h) (fun _ h => by cases h)
  have hv : ∀ m, iterN R.stepU m (R.step u) = R.step u := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [iterN_add]
      simp only [iterN]
      rw [ih, RLU.stepU_eq_of_line hR hj hpc1 hprog1 (fun _ h => by cases h)
        (fun _ h => by cases h)]
      exact RL.step_udf_err hR hj hpc1 hprog1 herr1
  intro m
  rw [show m + 1 = 1 + m by omega, iterN_add]
  simp only [iterN]
  rw [h0, hv m]
  exact herr1

/-- **`udf` on the machine, with its line**: `trap_udf`'s trap site and its `udf` line. -/
theorem trap_udf_udf {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {code : Clif.TrapCode}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.udf code)) :
    TrapAt R.fb R.base code s ∧
      ∃ j t, R.L[j]? = some (.ins (.udf 0xc11f) t) ∧ Arm.r .PC s = R.pcOf j := by
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, rfl, hit, hsplit,
    hasg, hc1', hops, hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  obtain ⟨rfl, rfl⟩ := assign_none (fun f => rfl) hasg
  obtain rfl : c1 = [.inst (.udf code)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, -⟩ := hl1
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  rw [ftR_plain_append _ _ _ (by simp [Line.plain]) hZ] at hdrop
  have hj := drop_get (Z := []) (by simpa using hdrop)
  exact ⟨trapAt_line hR hj hpc hst.err, _, _, hj, hpc⟩

/-- **A taken `trapIf` on the machine, with the trap site's `udf` line**: `trap_trapIf` with the
trap site's line and program. -/
theorem trap_trapIf_udf {R : RL} (hR : R.Wf) {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {kk : CondBrKind}
    {code : Clif.TrapCode} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.trapIf kk code)) {ops : Array Operand}
    (hops : (MInst.trapIf kk code).operands = .ok ops)
    (hholds : kk.holds (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = true) :
    ∃ n, TrapAt R.fb R.base code (iterN R.step n s) ∧ (∀ i < n, R.GoodX (iterN R.step i s)) ∧
      (∃ j t, R.L[j]? = some (.ins (.udf 0xc11f) t) ∧ Arm.r .PC (iterN R.step n s) = R.pcOf j) ∧
      (iterN R.step n s).program = R.fb.program R.base := by
  have hck := (lowerRFunc_ok hR.alloc).2.2
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops', rfl, hit, hsplit,
    hasg, hc1', hops', hstat, hchk', hc2, h1, h2, htr, hdrop, hpc, hst⟩ := q_op hq hvb hi
  rw [hops] at hops'; cases hops'
  have hkk : ∀ r sz, kk = .zero r sz ∨ kk = .notZero r sz → r.isVregInt = true := by
    intro r sz hr
    have := ctlCheck_inst hck hvb hi
    rcases hr with rfl | rfl <;> simpa [ctlInstOk] using this
  obtain ⟨k', rfl, hkr⟩ := kind_alloc hkk (mk := fun k => MInst.trapIf k code) rfl
    (fun f => rfl) (fun f => rfl) hops hstat hasg m
  obtain rfl : c1 = [.inst (.trapIf k' code)] := by
    rcases hc1' with ⟨h, -, -⟩ | ⟨_, h, -⟩ | ⟨_, h, -⟩
    · exact h
    · cases h
    · cases h
  have hl1 := codeLinesE_single h1
  simp only [MInst.lines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hl1
  obtain ⟨rfl, hpsm⟩ := hl1
  have hZ : ∀ n, (ls2 ++ nxtOf R.af b)[1]? ≠ some (.label (.trap n)) := by
    intro n e
    have hm := List.mem_of_getElem? e
    rcases List.mem_append.1 hm with hm | hm
    · exact codeLinesE_noTrap _ _ _ _ h2 _ hm n rfl
    · simp only [nxtOf] at hm
      split at hm <;> simp at hm
  have hdrop' : R.L.drop j0 = relaxLine R.far (.ins (k'.insn (.trap ps1.traps.size)) none) ++
      (relaxLines R.far (ftList (ls2 ++ nxtOf R.af b)) ++ T) := by
    rw [hdrop, List.singleton_append, ftList_kind_trap k' ps1.traps.size _ hZ, relaxLines_cons,
      List.append_assoc]
  have hform : (∃ c, k'.insn (.trap ps1.traps.size) = .bcond c (.trap ps1.traps.size)) ∨
      (∃ nz w r, k'.insn (.trap ps1.traps.size) = .cbz nz w r (.trap ps1.traps.size)) ∨
      (∃ nz r bit, k'.insn (.trap ps1.traps.size) = .tbz nz r bit (.trap ps1.traps.size)) := by
    cases k' <;> simp [CondBrKind.insn]
  obtain ⟨nst, jl, hnst, hjt, -, -, -, hgx⟩ := reach_rcbX hR hdrop' hform (by simp) true
    (fun env a ha => by rw [kind_brCond hst hkr _ ha, hholds])
    (fun hct env a ha => by rw [kind_brCond_inv hst hkr _ _ hct ha, hholds])
    (by rw [hst.prog]) hpc hst.err hst.sp
  have hjl := hjt rfl
  have hpre : psm.traps.toList <+: R.psF.traps.toList :=
    (codeLinesE_traps h2).trans htr
  have hn : R.psF.traps.toList[ps1.traps.size]? = some (.trap ps1.traps.size, code) := by
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, ← hpsm]
    simp
  obtain ⟨body, psF', hb, hL, -⟩ := emit_block hR.emit
  rw [relaxLines_append, relaxLines_trapLines,
    show emitFar ⟨R.fa.k, R.af.slotBase⟩ R.af = R.far from rfl] at hL
  obtain ⟨body', hb'⟩ := hR.psF
  have hk : R.ctx = ⟨R.fa.k, R.af.slotBase⟩ := rfl
  rw [hk, hb] at hb'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl⟩ := hb'
  obtain ⟨hlab, hudf⟩ := trapLines_get _ _ _ hn
  have hlab' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size]? =
      some (.label (.trap ps1.traps.size)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]; simpa using hlab
  have hudf' : R.L[(relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1]? =
      some (.ins (.udf 0xc11f) (some code)) := by
    simp only [RL.L, hL]; rw [List.getElem?_append_right (by omega)]
    simpa [Nat.add_assoc] using hudf
  have hoff : R.pcOf jl =
      R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    have e1 := labelOffsets_label hR.lm hjl
    have e2 := labelOffsets_label hR.lm hlab'
    simp only [RL.pcOf]
    rw [lineOffset_succ _ _ _ hlab']
    simp only [RL.L] at e1 e2 ⊢
    rw [e1] at e2
    simp only [Option.some.injEq] at e2
    rw [e2]; simp [Line.size]
  have hpcF : Arm.r .PC (iterN R.step nst s) =
      R.pcOf ((relaxLines R.far (ftList body)).length + 2 * ps1.traps.size + 1) := by
    rw [hnst, Arm.r_of_w_same, hoff]
  have herrF : Arm.r .ERR (iterN R.step nst s) = .None := by
    rw [hnst, Arm.r_of_w_different (by simp)]; exact hst.err
  have hprogF : (iterN R.step nst s).program = R.fb.program R.base := by
    rw [hnst, Arm.w_program, hst.prog]
  exact ⟨nst, trapAt_line hR hudf' hpcF herrF, hgx, ⟨_, _, hudf', hpcF⟩, hprogF⟩

/-- **`regLevelCorrect_coreU` keeping the trace, for any trace predicate `P` above `RL.GoodX`
and `RLU.RaiseXF`**: every state of the run before a return, a trap or an exceptional end
satisfies `P` (`Realizes … P`, e.g. `RLU.GoodXUF`); after a trap every state errs; an exceptional
end also keeps the addresses `G` and the program, and its last step leaves the frame by unwinding
(`UnwExit`). -/
theorem regLevelCorrect_coreUTP {R : RLU} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hgot : GotSem R.gv R.X semU) {P : Arm.ArmState → Prop} (hP1 : ∀ u, R.GoodX u → P u)
    (hP2 : ∀ u, R.RaiseXF u → P u)
    (hRz : Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL) P)
    (hrets : ∀ us uses w, semU (.rets us) uses w = csem R.F R.ctx R.X (.rets us) uses w)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem R.F R.ctx R.X i uses w = some (outs, w', .halt))
    (hlsda : R.T.lsda = none ∨ LsdaAt R) (hsite : SiteAt R.toRL) {rows : List (Nat × Cfi)}
    (hrows : unwindRows R.af R.fa = .ok rows) (hcie : R.T.cie = cieInsns)
    (hfde : R.T.fde = insnsFrom 0 rows) (hsaved : savedCheck R.vc R.rf = true)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w, VReturns R.vc semU (ρsel m₀) w₀ us vals w →
      ∃ n, ArmRet ra R.s0 (E2E.runX R.stepU n R.s0) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX R.stepU n R.s0) p = x) ∧
        (∀ a, ¬ R.F a → (E2E.runX R.stepU n R.s0).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX R.stepU n R.s0) = Arm.r f w) ∧
        (∀ a, R.G a → (E2E.runX R.stepU n R.s0).mem a = R.s0.mem a) ∧
        (E2E.runX R.stepU n R.s0).program = R.s0.program ∧
        (∀ i < n, P (E2E.runX R.stepU i R.s0)) ∧
        ¬ UnwExit R.U R.T R.fa (E2E.runX R.stepU (n - 1) R.s0)) ∧
    (∀ c, VTraps R.vc semU (ρsel m₀) w₀ c →
      ∃ n, TrapAt R.fb R.base c (E2E.runX R.stepU n R.s0) ∧
        (∀ i < n, P (E2E.runX R.stepU i R.s0)) ∧
        ∀ m, Arm.r .ERR (E2E.runX R.stepU (n + m + 1) R.s0) ≠ .None) ∧
    (∀ obj w, VUnwinds R.vc semU R.XR (ρsel m₀) w₀ obj w →
      ∃ n, ArmRet ra R.s0 (E2E.runX R.stepU n R.s0) ∧ xreg 0 (E2E.runX R.stepU n R.s0) = obj ∧
        (∀ a, ¬ R.F a → (E2E.runX R.stepU n R.s0).mem a = w.mem a) ∧
        (∀ a, R.G a → (E2E.runX R.stepU n R.s0).mem a = R.s0.mem a) ∧
        (E2E.runX R.stepU n R.s0).program = R.s0.program ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX R.stepU n R.s0) = Arm.r f w) ∧
        (∀ i < n, P (E2E.runX R.stepU i R.s0)) ∧ 0 < n ∧
        UnwExit R.U R.T R.fa (E2E.runX R.stepU (n - 1) R.s0)) := by
  have hf : R.af.frame = true := lowerRFunc_frame hR.alloc
  have hck := (lowerRFunc_ok hR.alloc).2.2
  have hrf : savedCheckRF R.vc R.rf = true := by
    have h := hsaved
    simp only [savedCheck, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨n0, ht0, hq0, hA0, hf0⟩ := q_init hR hent hbe
  have h0 : iterN R.stepU n0 R.s0 = iterN R.step n0 R.s0 := RLU.iterN_stepU hR hU n0 R.s0 ht0
  have ht0U : ∀ i < n0, P (iterN R.stepU i R.s0) := fun i hi => by
    rw [RLU.iterN_stepU hR hU i R.s0 fun i' hi' => ht0 i' (by omega)]
    exact hP1 _ (ht0 i hi)
  have he : ∀ r ∈ calleeSaved, locVal R.fr (iterN R.step n0 R.s0) (.reg r) = regVal R.s0 r :=
    entry_calleeSaved hf0
  obtain ⟨hSim, hinit, hkeep⟩ := checkedAt_sound_match (sem := semU) (keep := ckeep) hcheck
    (locVal R.fr (iterN R.step n0 R.s0)) (ρsel (locVal R.fr (iterN R.step n0 R.s0))) w₀ (hsel _)
  have hRz' := realizes_and hRz
    (P := SavedInv R.rf ckeep (fun r => locVal R.fr (iterN R.step n0 R.s0) (.reg r)))
    fun _ _ hm hp => savedInv_step hrf hm hp
  have hq0' : QA R.toRL (iterN R.stepU n0 R.s0)
      (MConf.init R.rf (locVal R.fr (iterN R.step n0 R.s0)) w₀) ∧
      SavedInv R.rf ckeep (fun r => locVal R.fr (iterN R.step n0 R.s0) (.reg r))
        (MConf.init R.rf (locVal R.fr (iterN R.step n0 R.s0)) w₀ : MConf CV Arm.ArmState) :=
    ⟨.inl ⟨by rw [h0]; exact hq0, hA0⟩, savedInv_init _ _ _ _⟩
  have hfin : ∀ n1 n2 n3, E2E.runX R.stepU (n0 + n1 + n2 + n3) R.s0 =
      iterN R.stepU n3 (iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0))) := by
    intro n1 n2 n3
    rw [runX_eq]
    simp only [iterN_add]
  refine ⟨locVal R.fr (iterN R.step n0 R.s0), fun us vals w hret => ?_, fun c htr => ?_,
    fun obj w' hu => ?_⟩
  · -- a return
    obtain ⟨b, k, ρ, w₁, vb, ops, outs, hstar, hvb, hi, hops, hvals, hsem⟩ := hret
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz' hstar hinit hq0'
    obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hi
    rw [operands_retsC] at hops
    cases hops
    have hsem' := hsem
    rw [hrets] at hsem'
    simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, rfl, -⟩ := hsem'
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w₁⟩) (.ret vals w₁) := by
      rw [hvals]
      refine VStep.step hvb hi (operands_retsC ns) (by rw [hvals] at hsem; exact hsem) ?_
        (VNext.ret rfl)
      rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
    obtain ⟨n2, c', c'', ⟨hq2, -⟩, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz' h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | halt w'' => cases hSim.halt hr3
    | ret uses m' w'' =>
      have hks := hkeep hr3
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        rw [operands_retsC] at hops'; cases hops'
        have hsem3 := hsem2
        rw [hrets] at hsem3
        simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem3
        obtain ⟨rfl, rfl, rfl⟩ := hsem3
        cases hn with
        | ret _ =>
        rw [rets_store hlen2 rfl hho hcl] at hks
        obtain ⟨mt, hq2'⟩ := qa_q hq2
        have hst := q_stRel hq2'
        obtain ⟨n3, ht3, hpc, herr, hsp, hx29, hregs, hsvd, hmem, hfld, hprogF, hvalsM⟩ :=
          ret_machine hR hent hq2 hvb hi
        have e3 := RLU.iterN_stepU hR hU n3 _ ht3
        have ht3U : ∀ i < n3, P (iterN R.stepU i
            (iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0)))) := fun i hi => by
          rw [RLU.iterN_stepU hR hU i _ fun i' hi' => ht3 i' (by omega)]
          exact hP1 _ (ht3 i hi)
        have htr : ∀ i < n0 + n1 + n2 + n3, P (E2E.runX R.stepU i R.s0) := fun i hi => by
          rw [runX_eq]
          exact trace_add ht0U (trace_add ht1 (trace_add ht2 ht3U)) i (by omega)
        have hm0 : ∀ r, locVal R.fr (iterN R.step n0 R.s0) (.reg r) =
            regVal (iterN R.step n0 R.s0) r := fun _ => rfl
        have hn3 : 0 < n3 := by
          rcases Nat.eq_zero_or_pos n3 with h3 | h3
          · subst h3
            exfalso
            have e1 : spv (iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0))) =
                spv R.s0 := hsp
            have e2 : spv (iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0))) =
                spv R.s0 - BitVec.ofNat 64 (frameDrop R.af) := hst.sp
            obtain ⟨hB, hK⟩ := spBody_toNat hR.stack
            have hD : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hf]
            have h3 := congrArg BitVec.toNat (e2.symm.trans e1)
            rw [hB] at h3
            omega
          · exact h3
        have hnot : ¬ UnwExit R.U R.T R.fa (E2E.runX R.stepU (n0 + n1 + n2 + n3 - 1) R.s0) := by
          rw [show n0 + n1 + n2 + n3 - 1 = n0 + n1 + n2 + (n3 - 1) by omega, hfin,
            RLU.iterN_stepU hR hU (n3 - 1) _ fun i hi => ht3 i (by omega)]
          exact not_unwExit_of_goodX hR hU (ht3 (n3 - 1) (by omega))
        refine ⟨n0 + n1 + n2 + n3, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, htr, hnot⟩
        all_goals rw [hfin, e3]
        · exact hpc
        · exact herr
        · exact hsp
        · intro n hn
          simp only [calleeSavedX, List.mem_map, List.mem_range] at hn
          obtain ⟨a, ha, rfl⟩ := hn
          by_cases h29 : a = 10
          · subst h29; exact hx29
          obtain ⟨hcs, hal⟩ := calleeSaved_x (n := 19 + a) (by omega) (by omega)
          by_cases hsv : Reg.x (19 + a) ∈ R.af.saves
          · exact hsvd _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have hne : ∀ q, q < 32 → q ≠ 19 + a →
              Arm.StateField.GPR (rnum (19 + a)) ≠ .GPR (BitVec.ofNat 5 q) :=
            fun q h1 h2 e => rnum_ne (a := 19 + a) (b := q) (by omega) h1 (Ne.symm h2)
              (Arm.StateField.GPR.inj e)
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (hne 29 (by omega) (by omega)) (hne 31 (by omega) (by omega))
            (hne 16 (by omega) (by omega)) (hne 17 (by omega) (by omega)) (by simp)] at k1
          exact setWidth128_inj (k2.trans k1)
        · intro n h8 h16
          obtain ⟨hcs, hal⟩ := calleeSaved_v h8 h16
          by_cases hsv : Reg.v n ∈ R.af.saves
          · exact hsvd _ hsv
          have k1 := hks _ hcs
          simp only [ckeep, hm0] at k1
          have k2 := hregs _ hal hsv
          simp only [regVal] at k1 k2
          rw [hf0 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)] at k1
          show (Arm.r (.SFP (rnum n)) _).setWidth 64 = (Arm.r (.SFP (rnum n)) R.s0).setWidth 64
          rw [k2]
          exact setWidth128_inj k1
        · intro j v p x hj hx
          have e1 := hSim.ret hr3
          simp only [VConf.ret.injEq] at e1
          rw [e1.1] at hx
          exact hvalsM _ (operands_retsC ns) j v p x hj hx
        · intro a ha
          rw [hmem]
          exact hst.world.2.1 a ha
        · intro f hf' h29 h31
          rw [hfld f hf' h29 h31]
          exact hst.world.1 f hf'
        · intro a ha
          rw [hmem]
          exact hst.gkeep a ha
        · rw [hprogF, hst.prog]
          exact hent.program.symm
  · -- a trap
    obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hstar, hvb, hi, hops, hsem, htc⟩ := htr
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz' hstar hinit hq0'
    obtain ⟨hnil, hform⟩ :=
      csem_halt (hhalt _ _ _ _ _ (by rw [htc]; exact Option.some_ne_none _) hsem)
    subst hnil
    have hdefs : ops.toList.filter Operand.isDef = [] := by
      rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
      · rw [udf_ops hops]; rfl
      · exact trapIf_nodefs hops
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w⟩) (.halt w') :=
      VStep.step hvb hi hops hsem (by rw [hdefs]; rfl) VNext.halt
    obtain ⟨n2, c', c'', ⟨hq2, -⟩, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz' h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    cases c'' with
    | run s' => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | ret vs m' w'' => cases hSim.ret hr3
    | halt w'' =>
      cases hms with
      | op hvb' hi' hops' hsz hsem2 hlen2 hho hcl hn =>
        obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
        simp only at hb' hk' hw'
        subst hb' hk' hw'
        rw [hvb] at hvb'; cases hvb'
        rw [hi] at hi'; cases hi'
        have hnr : ∀ us, i ≠ .rets us := by
          intro us h
          rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩ <;> cases h
        have hq2 := (qa_op hq2 hvb hi hnr).1
        have hst2 := q_stRel hq2
        have hstk : ∀ n3, (∀ i < n3, P (iterN R.stepU i
              (iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0))))) →
            (∀ m, Arm.r .ERR (iterN R.stepU (m + 1) (iterN R.stepU n3
              (iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0))))) ≠ .None) →
            (∀ i < n0 + n1 + n2 + n3, P (E2E.runX R.stepU i R.s0)) ∧
            ∀ m, Arm.r .ERR (E2E.runX R.stepU (n0 + n1 + n2 + n3 + m + 1) R.s0) ≠ .None := by
          intro n3 ht3 hs3
          refine ⟨fun i hi => ?_, fun m => ?_⟩
          · rw [runX_eq]
            exact trace_add ht0U (trace_add ht1 (trace_add ht2 ht3)) i (by omega)
          · rw [show n0 + n1 + n2 + n3 + m + 1 = n0 + n1 + n2 + (n3 + (m + 1)) by omega, hfin,
              iterN_add]
            exact hs3 m
        rcases hform with ⟨cd, rfl⟩ | ⟨kk, cd, rfl, -⟩
        · simp only [trapCode?, Option.some.injEq] at htc
          subst htc
          obtain ⟨htrap, j, tt, hj, hpcj⟩ := trap_udf_udf hR hq2 hvb hi
          obtain ⟨h1', h2'⟩ := hstk 0 (fun _ h => absurd h (Nat.not_lt_zero _))
            (RLU.udf_stuckU hR hj hpcj hst2.prog hst2.err)
          exact ⟨n0 + n1 + n2 + 0, by rw [hfin]; exact htrap, h1', h2'⟩
        · cases hn with
          | halt =>
          obtain ⟨-, hform2⟩ := csem_halt (hhalt _ _ _ _ _ (by simp [trapCode?]) hsem2)
          rcases hform2 with ⟨_, e⟩ | ⟨kk', cd', e, hholds⟩
          · cases e
          · cases e
            simp only [trapCode?, Option.some.injEq] at htc
            subst htc
            obtain ⟨n3, htrap, ht3, ⟨j, tt, hj, hpcj⟩, hprog3⟩ :=
              trap_trapIf_udf hR hq2 hvb hi hops' hholds
            have e3 := RLU.iterN_stepU hR hU n3 _ ht3
            have ht3U : ∀ i < n3, P (iterN R.stepU i
                (iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0)))) := fun i hi => by
              rw [RLU.iterN_stepU hR hU i _ fun i' hi' => ht3 i' (by omega)]
              exact hP1 _ (ht3 i hi)
            obtain ⟨h1', h2'⟩ := hstk n3 ht3U (by
              rw [e3]
              exact RLU.udf_stuckU hR hj hpcj hprog3 htrap.err)
            exact ⟨n0 + n1 + n2 + n3, by rw [hfin, e3]; exact htrap, h1', h2'⟩
  · -- an exceptional end: a `call` whose callee raises
    obtain ⟨b, k, ρ, w1, vb, info, ops, outs, hstar, hvb, hi, hops, hraise, hsem, hlen⟩ := hu
    obtain ⟨n1, c1, hq1, hr1, ht1⟩ := forward hSim hRz' hstar hinit hq0'
    have h1 : VStep R.vc semU (.run ⟨b, k, ρ, w1⟩) (.halt w') :=
      VStep.step hvb hi hops hsem hlen VNext.halt
    obtain ⟨n2, c', c'', ⟨hq2, hS2⟩, hr2, hms, hr3, ht2⟩ :=
      forward_last hSim hRz' h1 _ c1 _ (Nat.le_refl _) hr1 hq1
    obtain ⟨u, hu⟩ : ∃ u, iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0)) = u :=
      ⟨_, rfl⟩
    rw [hu] at hq2
    cases hms with
    | move => obtain ⟨_, e⟩ := hSim.run hr3; cases e
    | @op b' k' allocs its m w2 vb' i2 ops2 outs2 outs2' w2' ctl m2 c3 hvb' hi' hops' hsz hsem2
        hlen2 hho hcl hn =>
      obtain ⟨hb', hk', hw'⟩ := hSim.at_op hr2
      simp only at hb' hk' hw'
      subst hb' hk' hw'
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      have hq2 := (qa_op hq2 hvb hi (fun _ h => by cases h)).1
      -- the allocated code reads the VCode's uses: the same raising callee
      have hU0 := matchRun_uses hcheck hr2 (MStep.op hvb hi hops hsz hsem2 hlen2 hho hcl hn) hvb hi
        hops
      obtain ⟨j0, items, pre, regs, i', cA, cB, ls1, ls2, ps1, psm, ps2, T', cc', wh, ops'', hal, hit,
        hsplit, hasg, hc1', hops'', hstat, hchk', hcode2, h1', h2', htr', hdrop, hpc, hst⟩ :=
        q_op hq2 hvb hi
      rw [hops] at hops''; cases hops''
      subst hal
      have hm' : ∀ r, r.allocatable = true → m (.reg r) = regVal u r := fun r hr =>
        hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
      have hraise' : R.XR.raise (callDest info) (useVals ops regs u) w1 = some (obj, w') := by
        rw [← useVals_of_store hstat hm', hU0]
        exact hraise
      have hgg : gotGuard R.gv R.X info (useVals ops regs u) := by
        rw [← useVals_of_store hstat hm', hU0]
        exact (hgot _ _ _ _).1 hsem
      -- the raising callees' contract: the unwinder's state `t` at our call
      have hsite0 : R.vc.CallSite info := ⟨b, vb, k, hvb, .inl hi⟩
      have hcpc := callAt_of_q hq2 hvb hi call_hcall regs i' rfl hasg
      have hraiseU := hU.os info (.call info) hsite0 (.inl rfl) u
        (by rw [hst.sp]; exact RL.K_le hR) (fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha)
        hst.gkeep cc' wh ops regs i' w1 hops hstat hasg hcpc hst.world hst.align hst.err hgg
      obtain ⟨t, hUr, hW, hFK, herrt, hprogt, hoth, hkc⟩ := hraiseU obj w' hraise'
      obtain ⟨hstepU, hRX, hdesc, hxzr⟩ := RLU.stepU_q_raiseF hR hq2 hvb hi (.inl rfl) hUr
      -- the personality continues at a plain call
      obtain ⟨j, x, hj, hpcj, -, hmem⟩ :=
        hsite u b k _ its m w1 vb _ info none hq2 hvb hi (.inl ⟨rfl, rfl⟩)
      have hpers : Unw.personality R.T.lsda (lineOffset R.L j + 4 - 1) = .continue := by
        rcases hlsda with hn | ⟨sites, hcs, hlsda'⟩
        · rw [hn]; rfl
        · rw [hlsda']; exact Unw.personality_plain hcs hmem
      have hne : R.fb.words.toList ≠ [] := by
        obtain ⟨_, wd, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
        intro h
        have : R.fb.words.size = 0 := by simpa using congrArg List.length h
        simp [this] at hk
      have hpb : progBase u = R.base := progBase_eq (by rw [hst.prog]; rfl) hne
      have hfit : lineOffset R.L j + 4 ≤ 2 ^ 64 := by
        have h1' := lineOffset_succ R.L j _ hj
        have h2' := lineOffset_le_size R.L (j + 1)
        have h3' := layout_sum hR.layout
        have h4' := hR.fit
        simp only [Line.size, RL.L] at h1' h2' h3' ⊢
        omega
      have hoff : (Arm.r .PC u + 4 - 1 - progBase u).toNat = lineOffset R.L j + 4 - 1 := by
        rw [hpcj, hpb]
        simp only [RL.pcOf]
        have : R.base + BitVec.ofNat 64 (lineOffset R.L j) + 4 - 1 - R.base =
            BitVec.ofNat 64 (lineOffset R.L j + 3) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
            show (4 : BitVec 64).toNat = 4 from rfl, show (1 : BitVec 64).toNat = 1 from rfl]
          have := R.base.isLt
          omega
        rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
      -- the frame invariant at `t`: the store of `t` and `SavedInv`
      have hFK' : FrameKeep R.FK u t :=
        ⟨hFK.1, fun a ha => hFK.2.1 a ⟨RL.FK_F ha, by rw [hst.sp]; exact RL.FK_not_below hR ha⟩, hFK.2.2⟩
      have hst' : StRel R.toRL t (fun l => match l with | .reg r => regVal t r | l => m l) w' :=
        stRel_after hR hst (fun r _ => rfl)
          (fun l hl => by cases l with | reg r => exact absurd rfl (hl r) | _ => rfl)
          hW herrt hprogt hFK'
      obtain ⟨hpre, hA, -, hB⟩ := hS2
      have hok : (regs.map Loc.reg).all (bodyWritable R.rf.saveRegs) = true :=
        savedCheckRF_body hrf hit _ (mem_bodyOf hsplit rfl _ List.mem_cons_self)
      rw [Array.all_eq_true'] at hok
      have hkeepT : ∀ r ∈ calleeSaved, r ∉ R.rf.saveRegs →
          ckeep r (regVal t r) = ckeep r (regVal u r) := by
        intro r hr hns
        by_cases hc : r ∈ (MInst.call info).clobbers
        · exact hkc r hc hr
        · rw [hoth r (calleeSaved_allocatable hr) (fun p hp _ e => ?_) hc]
          have hp2 : p.2 ∈ regs.toList := by
            rw [Array.toList_zip] at hp
            exact (List.of_mem_zip hp).2
          have hmemr : Loc.reg p.2 ∈ regs.map Loc.reg :=
            Array.mem_map.2 ⟨p.2, Array.mem_toList_iff.1 hp2, rfl⟩
          exact bodyWritable_ne_reg (hok _ hmemr) hr hns (by rw [e])
      have hls0 : RItem.leadSaves (RItem.op k (regs.map Loc.reg) :: its) = [] := rfl
      have hA' : ∀ r ∈ calleeSaved, r ∉ R.rf.saveRegs →
          ckeep r (regVal t r) = ckeep r (locVal R.fr (iterN R.step n0 R.s0) (.reg r)) := by
        intro r hr hns
        rw [hkeepT r hr hns, ← hm' r (calleeSaved_allocatable hr)]
        exact hA r hr hns
      have hinvT : SavedInv R.rf ckeep (fun r => locVal R.fr (iterN R.step n0 R.s0) (.reg r))
          (.run ⟨b, .op k (regs.map Loc.reg) :: its,
            (fun l => match l with | .reg r => regVal t r | l => m l), w'⟩ :
            MConf CV Arm.ArmState) :=
        ⟨hpre, hA', fun r hr => (by rw [hls0] at hr; cases hr), hB⟩
      have hfs : Unw.FrameSaved R.af R.s0 t := frameSaved_of_stRel hR hent hf hsaved he hst' hinvT
      obtain ⟨-, t', hrest, hretA, hprog', hmem'⟩ :=
        Unw.unwind_call_restores hrows hf (List.of_mem_zip hmem).2 hfs herrt
      have hfldT : ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f t' = Arm.r f t := by
        obtain ⟨-, hrow⟩ := unwindRows_frame hrows hf
        rw [hrow _ (List.of_mem_zip hmem).2] at hrest
        exact restore_frameRow_fields
          (fun p hp => pushRows_ne18 (RL.frame_facts hR).2.2.2.1.1 hp) hrest
      have hstep : R.stepU u = Arm.w (.GPR 0#5) obj t' := by
        rw [hstepU]
        simp only [Unw.unwindAt, hoff, hpers, hcie, hfde, hrest]
      -- the trace: the run's states, then the raising call state
      have htsp : ∀ x d obj' t'', R.AtLine u x →
          ((∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none)) →
          R.U.raise d u = some (obj', t'') → spOf t'' = R.spB := by
        intro x d obj' t'' hx hd hr'
        obtain rfl := hdesc x d hx hd
        rw [hUr] at hr'
        cases hr'
        exact hFK.1.trans hst.sp
      have htfp : ∀ x d obj' t'', R.AtLine u x →
          ((∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none)) →
          R.U.raise d u = some (obj', t'') → xreg 29 t'' = spv R.s0 - 16#64 := by
        intro x d obj' t'' hx hd hr'
        obtain rfl := hdesc x d hx hd
        rw [hUr] at hr'
        cases hr'
        exact hFK.2.2.trans (hst.fp hf)
      have hRXX : R.RaiseXF u :=
        ⟨hRX, .inr (.inl (by rw [hstep, Arm.r_of_w_different (by simp)]; exact hretA.pc)),
          fun _ => ⟨by rw [hstep]; exact Unw.armRet_x0 hretA obj,
            by rw [hstep, Arm.w_program, hprog', hprogt, hst.prog]⟩,
          htsp, htfp, fun x hx => ⟨hxzr x hx, hst.code⟩,
          ⟨.call info, info, hsite0, .inl rfl, by rw [hst.sp]; exact RL.K_le hR,
            fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc', wh, ops, regs, i',
            w1, obj, w', hops, hstat, hasg, hcpc, hst.world, hst.align, hst.err, hgg, hraise'⟩⟩
      have hu1 : ∀ i < 1, P (iterN R.stepU i
          (iterN R.stepU n2 (iterN R.stepU n1 (iterN R.stepU n0 R.s0)))) := fun i hi => by
        obtain rfl : i = 0 := by omega
        rw [hu]
        exact hP2 _ hRXX
      have htr : ∀ i < n0 + n1 + n2 + 1, P (E2E.runX R.stepU i R.s0) := fun i hi => by
        rw [runX_eq]
        exact trace_add ht0U (trace_add ht1 (trace_add ht2 hu1)) i (by omega)
      -- the last step leaves the frame by unwinding
      have hexit : UnwExit R.U R.T R.fa u := by
        obtain ⟨x', d, obj', t'', ⟨jx, tt, hjx, hpcx⟩, hd, hr⟩ := hRX.raise
        have hins := insnAt_pc hR hjx hRX.prog hpcx
        refine ⟨d, obj', t'', ?_, hr, by rw [hoff]; exact hpers⟩
        unfold callDescAt
        rw [hins]
        rcases hd with ⟨n, rfl, rfl⟩ | ⟨r, rfl, rfl⟩ <;> rfl
      have hlast : E2E.runX R.stepU (n0 + n1 + n2 + 1 - 1) R.s0 = u := by
        rw [show n0 + n1 + n2 + 1 - 1 = n0 + n1 + n2 + 0 by omega, hfin, hu]
        rfl
      refine ⟨n0 + n1 + n2 + 1, ?_, ?_, ?_, ?_, ?_, ?_, htr, by omega, by rw [hlast]; exact hexit⟩
      all_goals rw [hfin, hu]
      all_goals simp only [iterN]
      all_goals rw [hstep]
      · rw [← hent.lr]
        exact Unw.armRet_x0 hretA obj
      · exact Arm.r_of_w_same
      · intro a ha
        rw [Arm.mem_w_of_mem_eq hmem']
        exact hW.2.1 a ha
      · intro a ha
        rw [Arm.mem_w_of_mem_eq hmem', hFK'.2.1 a (.inr ha)]
        exact hst.gkeep a ha
      · rw [Arm.w_program, hprog', hprogt, hst.prog]
        exact hent.program.symm
      · intro f hf' h29 h31
        have h0 : f ≠ .GPR 0#5 := fun e => hf' (by subst e; simp [Masked])
        rw [Arm.r_of_w_different h0, hfldT f hf' h29 h31]
        exact hW.1 f hf'

/-- **`regLevelCorrect_coreU` keeping the trace**: every state of the run before a return or an
exceptional end satisfies the trace predicate `RLU.GoodXU`; an exceptional end also keeps the
addresses `G` and the program, and its last step leaves the frame by unwinding (`UnwExit`). -/
theorem regLevelCorrect_coreUT {R : RLU} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt R.vc R.rf cc ins a0) {semU : Sem}
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    (hgot : GotSem R.gv R.X semU)
    (hRz : Realizes R.vc R.rf semU ckeep R.stepU (QA R.toRL)
      R.GoodXU)
    (hrets : ∀ us uses w, semU (.rets us) uses w = csem R.F R.ctx R.X (.rets us) uses w)
    (hhalt : ∀ i uses w outs w', trapCode? i ≠ none → semU i uses w = some (outs, w', .halt) →
      csem R.F R.ctx R.X i uses w = some (outs, w', .halt))
    (hlsda : R.T.lsda = none ∨ LsdaAt R) (hsite : SiteAt R.toRL) {rows : List (Nat × Cfi)}
    (hrows : unwindRows R.af R.fa = .ok rows) (hcie : R.T.cie = cieInsns)
    (hfde : R.T.fde = insnsFrom 0 rows) (hsaved : savedCheck R.vc R.rf = true)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW R.F R.vc.EntryArg R.af R.s0 w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV,
    (∀ us vals w, VReturns R.vc semU (ρsel m₀) w₀ us vals w →
      ∃ n, ArmRet ra R.s0 (E2E.runX R.stepU n R.s0) ∧
        (∀ (j : Nat) v p x, us[j]? = some (v, p) → vals[j]? = some x →
          regVal (E2E.runX R.stepU n R.s0) p = x) ∧
        (∀ a, ¬ R.F a → (E2E.runX R.stepU n R.s0).mem a = w.mem a) ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX R.stepU n R.s0) = Arm.r f w) ∧
        (∀ a, R.G a → (E2E.runX R.stepU n R.s0).mem a = R.s0.mem a) ∧
        (E2E.runX R.stepU n R.s0).program = R.s0.program ∧
        (∀ i < n, R.GoodXU (E2E.runX R.stepU i R.s0)) ∧
        ¬ UnwExit R.U R.T R.fa (E2E.runX R.stepU (n - 1) R.s0)) ∧
    (∀ c, VTraps R.vc semU (ρsel m₀) w₀ c →
      ∃ n, TrapAt R.fb R.base c (E2E.runX R.stepU n R.s0)) ∧
    (∀ obj w, VUnwinds R.vc semU R.XR (ρsel m₀) w₀ obj w →
      ∃ n, ArmRet ra R.s0 (E2E.runX R.stepU n R.s0) ∧ xreg 0 (E2E.runX R.stepU n R.s0) = obj ∧
        (∀ a, ¬ R.F a → (E2E.runX R.stepU n R.s0).mem a = w.mem a) ∧
        (∀ a, R.G a → (E2E.runX R.stepU n R.s0).mem a = R.s0.mem a) ∧
        (E2E.runX R.stepU n R.s0).program = R.s0.program ∧
        (∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 →
          Arm.r f (E2E.runX R.stepU n R.s0) = Arm.r f w) ∧
        (∀ i < n, R.GoodXU (E2E.runX R.stepU i R.s0)) ∧ 0 < n ∧
        UnwExit R.U R.T R.fa (E2E.runX R.stepU (n - 1) R.s0)) := by
  obtain ⟨m₀, h1, h2, h3⟩ := regLevelCorrect_coreUTP hR hent hcheck hU hgot (fun _ h => .inl h)
    (fun _ h => .inr h.toRaiseX) hRz hrets hhalt hlsda hsite hrows hcie hfde hsaved hbe ρsel hsel
  exact ⟨m₀, h1, fun c hc => (h2 c hc).imp fun _ h => h.1, h3⟩

end Backend.Proof

namespace E2E

open Backend Backend.Proof

/-- At a state of the old trace the machine's callee of the call line (if any) does not raise
(`RLU.noRaise_of_goodX`, by the call line's descriptor). -/
theorem RLU.noRaise_desc {R : RLU} (hR : R.Wf)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    {u : Arm.ArmState} (g : R.GoodX u) : ∀ d, callDescAt R.fa u = some d → R.U.raise d u = none := by
  intro d hd
  obtain ⟨x, ⟨j, tt, hj, hpc⟩, -⟩ := g.line
  have hins := insnAt_pc hR hj g.prog hpc
  unfold callDescAt at hd
  rw [hins] at hd
  cases x with
  | bl n =>
    simp only [Option.some.injEq] at hd
    exact RLU.noRaise_of_goodX hR hU g ⟨j, tt, hj, hpc⟩ (.inl ⟨n, rfl, hd.symm⟩)
  | blr r =>
    simp only [Option.some.injEq] at hd
    exact RLU.noRaise_of_goodX hR hU g ⟨j, tt, hj, hpc⟩ (.inr ⟨r, rfl, hd.symm⟩)
  | _ => cases hd

theorem mem_callIdx : ∀ (L : List Line) (j : Nat) (ln : Line), L[j]? = some ln → ln.isCall = true →
    j ∈ UnwindTables.callIdx L
  | [], _, _, h, _ => by simp at h
  | l :: L, 0, ln, h, hc => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [UnwindTables.callIdx, hc]
  | l :: L, j + 1, ln, h, hc => by
    simp only [UnwindTables.callIdx, List.mem_append, List.mem_map]
    exact .inr ⟨j, mem_callIdx L j ln (by simpa using h) hc, rfl⟩

/-- The return offset of a call line is one `scanLines` collects. -/
theorem ret_mem_scanLines {L : List Line} {j : Nat} {x : Insn} {t : Option Clif.TrapCode}
    (hj : L[j]? = some (.ins x t)) (hx : (∃ n, x = .bl n) ∨ ∃ r, x = .blr r) :
    lineOffset L j + 4 ∈ (scanLines L 0 [] []).2 := by
  rw [UnwindTables.scanLines_rets_eq]
  simp only [List.reverse_nil, List.nil_append, List.mem_map]
  refine ⟨j, mem_callIdx L j _ hj ?_, by omega⟩
  rcases hx with ⟨n, rfl⟩ | ⟨r, rfl⟩ <;> rfl

/-- **The save slots that unwinding a raising call's frame reads lie in the activation's frame**
(`StackBelow (frameDrop af) (spv s0)`, below the entry `sp`): at the raising call state `u`, for
the unwinder's state `t` of the machine callee's raise, the CFA of the frame row at the call and
every byte of every save slot of the row. -/
def FrameOkU (R : RLU) (u : Arm.ArmState) : Prop :=
  ∀ d obj t, callDescAt R.fa u = some d → R.U.raise d u = some (obj, t) →
    ∀ cfa, (Unw.rowAt R.T.cie R.T.fde (Arm.r .PC u + 4 - 1 - R.base).toNat).cfa? t = some cfa →
      ∀ p ∈ (Unw.rowAt R.T.cie R.T.fde (Arm.r .PC u + 4 - 1 - R.base).toNat).saved, ∀ k < 8,
        StackBelow (frameDrop R.af) (spv R.s0) (cfa + BitVec.ofInt 64 p.2 + BitVec.ofNat 64 k)

/-- **`FrameOkU` at a raising-call state** from the emitted tables (`unwindRows`, the CIE/FDE
of the rows) and the save-slot check (`savedCheck`). -/
theorem frameOkU_of {R : RLU} (hR : R.Wf) {rows : List (Nat × Cfi)}
    (hrows : unwindRows R.af R.fa = .ok rows) (hcie : R.T.cie = UnwindTables.cieInsns)
    (hfde : R.T.fde = UnwindTables.insnsFrom 0 rows) (hsaved : savedCheck R.vc R.rf = true)
    {u : Arm.ArmState} (h : R.RaiseXF u) : FrameOkU R u := by
  intro d obj t hd hr cfa hcfa p hp k hk
  obtain ⟨x, d0, obj0, t0, ⟨j, tt, hj, hpc⟩, hd0, -⟩ := h.raise
  have hins := insnAt_pc hR hj h.prog hpc
  have hdx : (∃ n, x = .bl n ∧ d = some n) ∨ (∃ r, x = .blr r ∧ d = none) := by
    unfold callDescAt at hd
    rw [hins] at hd
    rcases hd0 with ⟨n, rfl, -⟩ | ⟨r, rfl, -⟩
    · simp only [Option.some.injEq] at hd; exact .inl ⟨n, rfl, hd.symm⟩
    · simp only [Option.some.injEq] at hd; exact .inr ⟨r, rfl, hd.symm⟩
  have hsp := h.tsp x d obj t ⟨j, tt, hj, hpc⟩ hdx hr
  have hf : R.af.frame = true := lowerRFunc_frame hR.alloc
  have hdrop : frameDrop R.af = R.af.frameSize + 16 := by simp [frameDrop, hf]
  obtain ⟨-, hrow⟩ := UnwindTables.unwindRows_frame hrows hf
  have hret : lineOffset R.L j + 4 ∈ (scanLines R.fa.lines.toList 0 [] []).2 :=
    ret_mem_scanLines hj (by rcases hdx with ⟨n, rfl, -⟩ | ⟨r, rfl, -⟩
                             · exact .inl ⟨n, rfl⟩
                             · exact .inr ⟨r, rfl⟩)
  have hfit : lineOffset R.L j + 4 ≤ 2 ^ 64 := by
    have h1' := lineOffset_succ R.L j _ hj
    have h2' := lineOffset_le_size R.L (j + 1)
    have h3' := layout_sum hR.layout
    have h4' := hR.fit
    simp only [Line.size, RL.L] at h1' h2' h3' ⊢
    omega
  have hoff : (Arm.r .PC u + 4 - 1 - R.base).toNat = lineOffset R.L j + 4 - 1 := by
    rw [hpc]
    simp only [RL.pcOf]
    have : R.base + BitVec.ofNat 64 (lineOffset R.L j) + 4 - 1 - R.base =
        BitVec.ofNat 64 (lineOffset R.L j + 3) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
        show (4 : BitVec 64).toNat = 4 from rfl, show (1 : BitVec 64).toNat = 1 from rfl]
      have := R.base.isLt
      omega
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hoff, hcie, hfde, hrow _ hret] at hcfa hp
  -- the CFA (x29 + 16) is the entry `sp`
  have hcfa' : cfa = spv R.s0 := by
    have hfp : xreg 29 t + 16#64 = spv R.s0 := by
      rw [h.tfp x d obj t ⟨j, tt, hj, hpc⟩ hdx hr]
      exact BitVec.sub_add_cancel _ _
    have e : (UnwindTables.frameRow ((pushRows R.af.saves 8).map UnwindTables.offsetPair)).cfa? t =
        some (spv R.s0) := by
      simp only [Unw.Row.cfa?, Unw.regVal?, UnwindTables.frameRow]
      rw [← hfp]
      rfl
    rw [e] at hcfa
    exact (Option.some.inj hcfa).symm
  subst hcfa'
  -- the row's offset of `p`: a slot inside the frame
  obtain ⟨o, ho8, hpo⟩ : ∃ o : Nat, o + 8 ≤ R.af.frameSize + 16 ∧
      p.2 = (o : Int) - 16 - R.af.frameSize := by
    simp only [UnwindTables.frameRow, List.mem_append, List.mem_reverse, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl
    · obtain ⟨-, hfs, -, hsvk, -, hcb, -⟩ := RL.frame_facts hR
      obtain ⟨d, off⟩ := p
      obtain ⟨r, hr, -, rfl⟩ := mem_pushRows hp
      have := clobberOff_le hsvk (saves_of_IF hr)
      exact ⟨R.af.frameSize + clobberOff R.af.saves r - clobberBytes R.af.saves, by omega,
        by dsimp only; omega⟩
    · exact ⟨R.af.frameSize + 8, by omega, by dsimp only; omega⟩
    · exact ⟨R.af.frameSize, by omega, by dsimp only; omega⟩
  -- the address
  obtain ⟨hB, hK⟩ := spBody_toNat hR.stack
  rw [hdrop] at hB hK ⊢
  obtain ⟨sb, hsb⟩ : ∃ sb, sb = spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16) := ⟨_, rfl⟩
  have hx : spv R.s0 = sb + BitVec.ofNat 64 (R.af.frameSize + 16) := by
    rw [hsb]; exact (BitVec.sub_add_cancel _ _).symm
  have ha : spv R.s0 + BitVec.ofInt 64 p.2 + BitVec.ofNat 64 k =
      (spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16)) + BitVec.ofNat 64 (o + k) := by
    rw [hpo]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    have := (spv R.s0).isLt
    omega
  rw [ha]
  have hlt := (spv R.s0).isLt
  have ht : ((spv R.s0 - BitVec.ofNat 64 (R.af.frameSize + 16)) + BitVec.ofNat 64 (o + k)).toNat =
      (spv R.s0).toNat - (R.af.frameSize + 16) + (o + k) := by
    rw [BitVec.toNat_add, hB, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o + k < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [StackBelow, ht]
  omega

/-- **The per-state facts of a run with unwinding of the activation with these data**
(`actGoodX`'s counterpart; the fields `lm`, `psF` play no role): a state of the old trace whose
call line's callee does not raise, or a raising-call state with its step facts (`RLU.RaiseXF`). -/
def actGoodXU (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) (base : BitVec 64)
    (s0 : Arm.ArmState) (X : ExtSem) (H : ArmHooks) (XR : XRaise) (U : Unw.UnwHooks)
    (T : Unw.FnTables) (K : Nat) (G : BitVec 64 → Prop) (gv : Nat → String → Prop)
    (u : Arm.ArmState) : Prop :=
  ((⟨⟨vcp, rf, af, fa, fb, {}, base, s0, X, H, {}, K, G, gv⟩, XR, U, T⟩ : RLU).GoodX u ∧
      ∀ d, callDescAt fa u = some d → U.raise d u = none) ∨
    ((⟨⟨vcp, rf, af, fa, fb, {}, base, s0, X, H, {}, K, G, gv⟩, XR, U, T⟩ : RLU).RaiseXF u ∧
      FrameOkU ⟨⟨vcp, rf, af, fa, fb, {}, base, s0, X, H, {}, K, G, gv⟩, XR, U, T⟩ u)

/-- `actGoodXU` from the trace predicate `RLU.GoodXUF`, the raising callees' contract, the
emitted tables and the save-slot check. -/
theorem actGoodXU_of {R : RLU} (hR : R.Wf)
    (hU : CalleeUnwOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.XR R.U R.vc.CallSite R.gv)
    {rows : List (Nat × Cfi)} (hrows : unwindRows R.af R.fa = .ok rows)
    (hcie : R.T.cie = UnwindTables.cieInsns) (hfde : R.T.fde = UnwindTables.insnsFrom 0 rows)
    (hsaved : savedCheck R.vc R.rf = true)
    {u : Arm.ArmState} (h : R.GoodXUF u) :
    actGoodXU R.vc R.rf R.af R.fa R.fb R.base R.s0 R.X R.H R.XR R.U R.T R.K R.G R.gv u := by
  rcases h with g | g
  · exact .inl ⟨g.act, RLU.noRaise_desc hR hU g⟩
  · exact .inr ⟨⟨⟨g.good, g.err, g.prog, g.sp, g.raise⟩, g.next, g.exit, g.tsp, g.tfp, g.blr, g.pre⟩,
      frameOkU_of hR hrows hcie hfde hsaved g⟩

end E2E
