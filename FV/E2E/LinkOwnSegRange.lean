import FV.E2E.LinkOwnGotRun
import FV.E2E.Main
import FV.Backend.Proof.IselShpDriver

/-! # The ranges of the run segments (`SegRangeHyp`)

`segRangeHyp : SegRangeHyp`. Every run segment of the recorded lowering (`Kill.Seg`) defines
only vregs of its range, and calls through a CLIF value's vreg or one of the range:

* the defs: M4's contracts for the driver's runs, `LowerInstOk.defs` (statements),
  `LowerTermOk.defs` (terminators), `LowerTryOk.shape` (a `try_call`: fresh vregs before the call,
  the call's defs among the `try_call`'s result vregs, which `tryRegsOf` allocates right below);
  they come from M4's rule theorems (`instCalls_of_rules`, `termCalls_of_rules`,
  `tryCalls_of_rules`, `tryIndCalls_of_rules`) in a trivial semantic setting (`csem` with no
  memory relation holding, `mrNone`: every memory premise is vacuous), where only the
  semantics-independent `defs`/`shape` fields are used;
* the call targets: a call the ISLE runs emit is `CtlShape`'s `callSym`/`callReg`
  (`Driver.iselCtlHyp`), whose target vreg is a use, and the uses of a run are CLIF values' vregs or
  vregs of the run (`Kill.killRunsHyp`'s `RunKill`).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Kill Backend.Proof.Spill

/-! ## A trivial semantic setting -/

/-- External calls that never return. -/
def xNone : ExtSem := ⟨fun _ _ _ => none, fun _ _ => 0, 0, fun _ _ => Arm.PState.zero⟩

/-- The memory relation that never holds. -/
def mrNone : MemRelT := fun _ _ _ => False

/-- No address is outside the world. -/
def fNone : BitVec 64 → Prop := fun _ => False

/-- The semantics of the setting. -/
noncomputable abbrev semNone : Sem := csem fNone default xNone

theorem le_sum_of_mem' : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | [], _, h => by cases h
  | a :: l, x, h => by
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_sum_of_mem' h
      omega

/-- An outgoing area holding every extern's stack arguments. -/
def outAll (f : Clif.Function) : Nat := (f.externs.map fun e => stackBytes e.2.sig).sum

theorem sigStack_of {f : Clif.Function} {fn : Clif.FnRef} {e : Clif.ExtFunc}
    (he : f.extern? fn = some e) (hl : stackLayoutOk e.sig = true) :
    SigStackOk e.sig (outAll f) := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (lookup_mem he)
  exact ⟨le_sum_of_mem' (List.mem_map.mpr ⟨q, hq, rfl⟩), hl⟩

theorem refines_none : Refines fNone semNone := refines_csem fNone default xNone

theorem mrStable_none : MRStable fNone mrNone := fun _ _ _ _ _ h => h.elim

theorem memRefines_none : MemRefines fNone (default : FnCtx).slotBase (fun _ => none) semNone :=
  memRefines_csem fNone default xNone rfl (fun _ _ h => by cases h)

theorem callsRefine_none (env : Clif.Env) (exts : List Clif.ExtFunc) :
    CallsRefine fNone env exts mrNone semNone :=
  callsRefine_csem (by
    intro ext _ g sl cm w d uses args vals rvals cm' _ _ _ hmr
    exact hmr.elim)

theorem indCallsRefine_none (env : Clif.Env) (sigs : List Clif.Signature) :
    IndCallsRefine env sigs mrNone semNone :=
  indCallsRefine_csem (syms := fun _ => none) (by
    intro sig _ n g sl cm w u args vals rvals cm' _ _ _ _ _ hmr
    exact hmr.elim) (fun _ _ h => by cases h) (fun _ _ _ h => h.elim)

theorem memRelOk_none (f : Clif.Function) :
    MemRelOk fNone (default : FnCtx).slotBase (fun _ => none) f mrNone :=
  ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim, fun _ _ _ h => h.elim,
    fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ h => h.elim⟩

/-! ## Call targets -/

/-- The target vreg of a call the ISLE runs emit is a use. -/
theorem dest_use {N : Nat} {ci : CallInfo} {d : Nat} (h : CtlShape N (.call ci))
    (hd : ci.dest = .reg (.vreg d .int)) : d ∈ useVregs (.call ci) := by
  cases h with
  | callSym nm L D _ => cases hd
  | callReg t L D _ =>
    simp only [CallDest.reg.injEq, Reg.vreg.injEq, and_true] at hd
    subst hd
    unfold useVregs
    rw [operands_call_reg]
    simp [tgtOp]

/-! ## The theorem -/

/-- **The ranges of the run segments.** -/
theorem segRangeHyp : SegRangeHyp := by
  intro p f ctx ranges st0 bl hsub hd hs hb hlb lo mid hi c hseg m hm
  have ha := abiSigsOk_of_inSubset hsub
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  obtain ⟨hC1, hC2, hC3⟩ := Driver.iselCtlHyp f ctx ranges st0 hd hs ha hb
  obtain ⟨hK1, hK2, hK3⟩ := killRunsHyp f ctx ranges st0 hd hs ha hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  obtain ⟨hord, -⟩ := driver_ord hlb
  have hN : st0.nextVreg = ctx.valDef.size := hcf.size.1
  have hvbS : ∀ s : LState, st0.nextVreg ≤ s.nextVreg → ValsBelow ctx s := fun s hs' x r h => by
    have := asm_valueReg_lt hb h
    omega
  -- M4's contracts
  have hIC : InstCalls f semNone mrNone Clif.Env.empty p :=
    instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program refines_none mrStable_none
      (callsRefine_none _ _) (indCallsRefine_none _ _) memRefines_none
      (outB := outAll f) (fun _ _ _ h => h.elim)
      (fun B hB st hst fn args e hi he => sigStack_of he (hs.stackLayout.1 B hB st hst fn args e hi he))
      (memRelOk_none f)
  have hTC : TermCalls semNone mrNone :=
    termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable refines_none mrStable_none
  have hYC : TryCalls f semNone mrNone Clif.Env.empty p (outAll f) :=
    tryCalls_of_rules tryRulesCorrect tryUnmatchable refines_none mrStable_none memRefines_none
      (fun _ _ _ h => h.elim) (callsRefine_none _ _)
  have hYI : TryIndCalls semNone mrNone Clif.Env.empty p (indSigs f) :=
    tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable refines_none mrStable_none
      (indCallsRefine_none _ _)
  obtain ⟨bi, B, L, hB, hL, hk⟩ := hseg
  have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
  rcases hk with ⟨j, sl, hsl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, -, rfl⟩
  · -- a statement's segment
    obtain ⟨hlen, hcs, -, -⟩ := hspec bi B L hB hL
    obtain ⟨stm, hstm⟩ : ∃ stm, B.body[j]? = some stm :=
      ⟨B.body[j]'(by have := (List.getElem?_eq_some_iff.mp hsl).1; omega),
        List.getElem?_eq_getElem _⟩
    have hsm : stm ∈ B.body := List.mem_of_getElem? hstm
    obtain ⟨tr, hrun⟩ := hcs j sl hsl
    rw [hstart bi L hL] at hrun
    obtain ⟨info, hinf, hic, -⟩ := hcf.stmt bi B j stm hB hstm
    have hge : st0.nextVreg ≤ sl.st.nextVreg := ((hord bi L hL).stmt j sl hsl).1
    have he := hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)
    refine ⟨fun d hd => ?_, fun ci d hci hdest => ?_⟩
    · exact (hIC ctx _ info stm.inst sl.st sl.rss sl.st' tr hctx ⟨B, hBm, stm, hsm, rfl⟩
        hs.subsetE hinf hic (indSig_of_subset hsub B hBm stm hsm) he (hvbS _ hge) hrun).defs
        m hm d hd
    · obtain ⟨ms, hms, hsh⟩ := hC1 _ info stm.inst _ _ _ _ hinf hic (hN ▸ hge) hrun
      obtain ⟨-, huse⟩ := asm_runKill (hK1 _ info stm.inst _ _ _ _ hinf hic (hN ▸ hge) hrun).1 he
      rw [he, Array.empty_append] at hms
      have hmms : m ∈ ms := by rw [hms] at hm; simpa using hm
      rcases hci with rfl | ⟨ti, rfl⟩
      · exact (huse _ hm d (dest_use (hsh _ hmms rfl) hdest)).1
      · exact absurd (hsh _ hmms rfl) (fun h => by cases h)
  · -- the terminator's segment
    obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
    obtain ⟨hn, hy⟩ := lowTerm_spec hterm
    have hph := hcf.term bi B hB
    rw [← hstart bi L hL] at hph
    have hti := (Array.getElem?_eq_some_iff.mp hph).1
    have hge : st0.nextVreg ≤ L.tst.nextVreg := (hord bi L hL).term.1
    cases ht : B.term.isTry with
    | false =>
      obtain ⟨htl, hdat, out, tr, hc⟩ := hn ht
      rw [htl] at hm
      simp only [fixTry] at hm
      refine ⟨fun d hd => ?_, fun ci d hci hdest => ?_⟩
      · have htg : TargetsLen B.term L.targets := by
          intro x d' tbl hbt'
          have := lowTerm_targets ht hterm
          rw [hbt'] at this
          have h1 := (edgeTargets_spec (f := f) (bcs := dests (.brTable x d' tbl)) this).1
          simpa [dests] using h1
        have hbt := brIdx_of_ok (hs.ctxFacts ctx ranges st0 hb).1 B hBm
        exact (hTC f ctx _ (abiTerm f B.term) L.data L.targets out L.tst L.tst' tr hctx
          (brIdxTyped_abiTerm hbt) (targetsLen_abiTerm htg) hph (hvbS _ hge) hdat htst
          (by rw [termCall_abiTerm]; exact hc)).defs m hm d hd
      · obtain ⟨ms, hms, hsh⟩ := hC2 _ _ _ _ _ _ _ _ hti hph ht hdat (hN ▸ hge) hc
        obtain ⟨-, huse⟩ := asm_runKill (hK2 _ _ _ _ _ _ _ _ hti hph ht hdat (hN ▸ hge) hc) htst
        rw [htst, Array.empty_append] at hms
        have hmms : m ∈ ms := by rw [hms] at hm; simpa using hm
        rcases hci with rfl | ⟨ti, rfl⟩
        · exact (huse _ hm d (dest_use (hsh _ hmms rfl) hdest)).1
        · exact absurd (hsh _ hmms rfl) (fun h => by cases h)
    | true =>
      obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := isTry_with ht
      obtain ⟨T, hT', hdat, hex, -, hreg, hinfo, out, tr, hc⟩ := hy et het
      rw [hT'] at hm
      simp only [fixTry] at hm
      -- M4's `try_call` contract
      obtain ⟨ci0, hok⟩ : ∃ ci0, LowerTryOk semNone mrNone Clif.Env.empty p
          (tryCtx ctx (L.start + B.body.length) L.data T.regs) ci0 T.info
          { T.st1 with emitted := #[] } L.tst' L.tst'.emitted.toList := by
        rcases het with ⟨fn, args, hBT⟩ | ⟨callee, args, hBT⟩
        · have hdata' : tryCallData f (.tryCall fn args et) = .ok L.data := hBT ▸ hdat
          exact ⟨_, hYC ctx _ fn args et L.data T.sig T.items L.targets T.info T.regs L.tst T.st1
            out L.tst' tr hctx
            (fun e he => sigStack_of he (hs.stackLayout.2 B hBm fn args et e hBT he))
            hdata' hex hph hinfo hreg (hvbS _ hge) hc⟩
        · have hdata' : tryCallData f (.tryCallIndirect callee args et) = .ok L.data := hBT ▸ hdat
          obtain ⟨hsin, h8⟩ := tryIndSig_of_subset hsub B hBm callee args et T.sig hBT
            (Backend.Proof.Driver.exnTableOpnd_sig hex)
          exact ⟨_, hYI f ctx _ callee args et L.data T.sig T.items L.targets T.info T.regs L.tst
            T.st1 out L.tst' tr hctx hdata' hex hsin h8 hph hinfo hreg (hvbS _ hge) hc⟩
      obtain ⟨pre, ci, hms, hpre, hcd⟩ := hok.shape
      have hmono := hok.mono
      obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hex) hreg
      simp only at hmono
      rw [hms, tryFix_append] at hm
      refine ⟨fun d hd => ?_, fun ci' d hci hdest => ?_⟩
      · rcases List.mem_append.mp hm with hm' | hm'
        · have := hpre m hm' d hd
          simp only at this
          omega
        · rw [List.mem_singleton] at hm'
          subst hm'
          rw [vdefs_tryCall] at hd
          have := hcd d hd
          simp only [tryDefRegs, tryCtx, htrs, List.mem_append, List.mem_map, List.mem_range,
            List.mem_cons, Reg.vreg.injEq, and_true, List.mem_nil_iff, or_false] at this
          have hmx : (sigRets T.sig).length ≤ max (sigRets T.sig).length 2 := Nat.le_max_left _ _
          have hm2 : 2 ≤ max (sigRets T.sig).length 2 := Nat.le_max_right _ _
          rcases this with ⟨j, hj, hjd⟩ | hjd | hjd <;> omega
      · obtain ⟨ms', hms', hsh⟩ := hC3 _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het ⟨B, hBm, rfl⟩ hdat
          hex (hN ▸ hge) hreg hc
        obtain ⟨-, huse⟩ := asm_runKill (hK3 _ _ _ _ _ _ _ _ _ _ _ _ _ hti hph het ⟨B, hBm, rfl⟩
          hdat hex (hN ▸ hge) hreg hc).1 rfl
        simp only [Array.empty_append] at hms'
        have hin : ∀ x, x ∈ L.tst'.emitted.toList → x ∈ ms' := fun x hx => by
          rw [hms'] at hx; simpa using hx
        -- the call in question, a call of the rule's code
        obtain ⟨ci1, hci1, hcm⟩ : ∃ ci1, ci1 = ci' ∧ MInst.call ci1 ∈ L.tst'.emitted.toList := by
          rcases List.mem_append.mp hm with hm' | hm'
          · rcases hci with rfl | ⟨ti, rfl⟩
            · exact ⟨ci', rfl, by rw [hms]; exact List.mem_append_left _ hm'⟩
            · exfalso
              have hm'' : MInst.tryCall ci' ti ∈ ms' := hin _ (by rw [hms]; exact List.mem_append_left _ hm')
              exact absurd (hsh _ hm'' rfl) (fun h => by cases h)
          · rw [List.mem_singleton] at hm'
            subst hm'
            rcases hci with h | ⟨ti, h⟩
            · cases h
            · cases h
              exact ⟨_, rfl, by rw [hms]; simp⟩
        subst hci1
        have hu := (huse _ hcm d (dest_use (hsh _ (hin _ hcm) rfl) hdest)).1
        omega

end E2E.LinkCheck
