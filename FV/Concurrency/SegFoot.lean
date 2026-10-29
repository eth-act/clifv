module

public import FV.Concurrency.IselCover
public import FV.Concurrency.VCodeFrame
public import FV.E2E.Lockstep

@[expose] public section

/-!
# The footprint premises along a run (T2h, #311, layer 2e step 2)

`IselCover.RunFoot` asks for the precise footprint (`VCodeThread.ifoot_csem`) at every state the
run of a segment reaches. `ifoot_csem` needs an error-free world, and for a straight-line form
an aligned `sp` and `csemWF`. This file shows that these premises hold along the whole run:

* **`csem_keep`**: a successful `csem` step with control `next` of any instruction but calls
  (a control form, or a straight-line form covered by `csemWF`), from an error-free world with
  an aligned `sp`, ends in an error-free world with the same `sp` (hence aligned):
  - straight-line forms: `straightSem` checks the error, and the canonical run keeps the frame
    (`formOk_sound`'s `FrameKeep`, at the canonical registers, which pass the static check:
    `canon_static`, the memory forms included);
  - the LL/SC loops: `loopSem` checks the error; the use registers x25/x26/x28 are not `sp`, and
    the bodies keep every field but the pc, their registers and the flags (`rmwBody_spec`,
    `casHead_spec`, `stlxr_spec`);
  - the other control forms keep the world, `tls_value` writes only the flags;
* **`runFoot_csem`**: the run of a list of such instructions (control forms or covered forms,
  `Covered`) from an error-free, aligned world has the footprint `cEvs` at every reached state
  (`RunFoot`), given that the TLSDESC flags do not depend on memory (`TlsMemFree`).
-/

namespace Concurrency.SegFoot

open Arm ArmFoot ArmThread VCodeThread Backend Backend.Proof IselCover

/-! ## The canonical allocation passes the static check -/

set_option maxHeartbeats 16000000 in
/-- **The canonical registers of a covered form pass the static check** (memory forms included),
and its use registers are distinct x0–x5 / v registers. -/
theorem canon_static {ctx : FnCtx} {i : MInst} (h : FormOk ctx i = true) (c : CheckCtx) :
    ∃ ops ic, i.operands = .ok ops ∧ i.assign (canonRegs ops) = .ok ic ∧
      c.checkStatic "" ops ((canonRegs ops).map Loc.reg) i.clobbers = .ok () ∧
      (((ops.zip (canonRegs ops)).toList.filter (·.1.isUse)).map (·.2)).Nodup ∧
      ∀ r ∈ ((ops.zip (canonRegs ops)).toList.filter (·.1.isUse)).map (·.2),
        (∃ n, n < 6 ∧ r = .x n) ∨ (∃ n, n < 32 ∧ r = .v n) := by
  unfold FormOk at h
  split at h
  all_goals first
    | (cases h; done)
    | skip
  all_goals (try (
    simp only [Bool.and_eq_true] at h
    obtain ⟨_, h⟩ := h
    unfold memOk at h
    split at h <;> (try (cases h; done))))
  all_goals (
    refine ⟨_, _, rfl, rfl, ?_, ?_, ?_⟩
    rotate_left
    · simp (config := {decide := true}) [canonRegs, canonReg, canonBase, OpSpec.def_, OpSpec.use,
        OpSpec.reuseDef, List.range, List.range.loop, Operand.isUse]
    · simp (config := {decide := true}) [canonRegs, canonReg, canonBase, OpSpec.def_, OpSpec.use,
        OpSpec.reuseDef, List.range, List.range.loop, Operand.isUse]
    simp (config := {decide := true}) [CheckCtx.checkStatic, canonRegs, canonReg, canonBase,
      CheckCtx.checkOperand, CheckCtx.locOk, ensure, Loc.cls?, defConflicts, MInst.clobbers,
      OpSpec.def_, OpSpec.use, OpSpec.reuseDef, List.range, List.range.loop, List.zipIdx, forM, List.forM,
      Reg.allocatable, aarch64Env, bind, Except.bind, pure, Except.pure, Loc.isReg])

/-! ## Straight-line forms keep the error flag and `sp` -/

theorem err_foldl : ∀ (ps : List (Reg × CV)) (s : ArmState),
    Arm.r .ERR (ps.foldl (fun s p => setReg s p.1 p.2) s) = Arm.r .ERR s
  | [], _ => rfl
  | p :: ps, s => by
    simp only [List.foldl_cons]
    rw [err_foldl ps _]
    obtain ⟨r, v⟩ := p
    cases r with
    | x n => simp only [setReg]; rw [Arm.r_of_w_different (by simp)]
    | v n => simp only [setReg]; rw [Arm.r_of_w_different (by simp)]
    | _ => rfl

set_option maxHeartbeats 1000000 in
/-- **A successful canonical run of a covered straight-line form keeps `sp`** (and ends without
error). -/
theorem straight_keep {F : BitVec 64 → Prop} {ctx : FnCtx} (X : ExtSem) {i : MInst}
    (hfo : FormOk ctx i = true) (hctl : i.isCtl = false) {us : List CV}
    (hwf : csemWF ctx i us = true) {w : ArmState} (herr : Arm.r .ERR w = .None)
    (hal : Arm.CheckSPAlignment w) {o : List CV} {w₁ : ArmState} {c : Ctl}
    (h : straightSem F ctx i us w = some (o, w₁, c)) :
    Arm.r .ERR w₁ = .None ∧ Arm.r (.GPR 31#5) w₁ = Arm.r (.GPR 31#5) w := by
  obtain ⟨ops, ic, hops, hic, hcs, hnd, hpl⟩ := canon_static hfo E2E.checkCtx0
  have hsz := canonRegs_size ops
  have hlen : us.length = useCount ops := (by simpa [csemWF, hops] using hwf : _ ∧ _).2
  let R := ((ops.zip (canonRegs ops)).toList.filter (·.1.isUse)).map (·.2)
  have hRl : R.length = us.length := by
    rw [hlen]
    simp only [R, List.length_map, useCount, Array.toList_zip]
    exact len_filter_zip _ _ (by simp [hsz])
  have hplain : ∀ r ∈ R, E2E.PlainReg r := fun r hr => by
    rcases hpl r hr with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · exact .inl ⟨n, by omega, rfl⟩
    · exact .inr ⟨n, hn, rfl⟩
  simp only [straightSem, hops, hic] at h
  split at h
  · rename_i hacc
    split at h
    · rename_i t' hex
      split at h
      · rename_i hok
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        let P := placeUses ops (canonRegs ops) us w
        have hPw : SameWorld F P w :=
          E2E.sameWorld_foldl_setReg R us w w hpl (SameWorld.refl _ _)
        have hal' : Arm.CheckSPAlignment P :=
          align_of_spEq (sw_r_eq hPw (f := .GPR 31#5) (by simp [Masked])).symm hal
        have herr' : Arm.r .ERR P = .None := by
          rw [← sw_r_eq hPw (f := .ERR) (by simp [Masked])]; exact herr
        have hU : placeUses ops (canonRegs ops) (useVals ops (canonRegs ops) P) w =
            placeUses ops (canonRegs ops) us w := by
          rw [E2E.useVals_eq, E2E.placeUses_eq, E2E.placeUses_eq]
          exact E2E.foldl_setReg_reads R us w w hnd hplain hRl
        have hsem : csem F ctx X i (useVals ops (canonRegs ops) P) w =
            some (defVals ops (canonRegs ops) t', t', .next) := by
          rw [csem_of_wf hctl (by simp [csemWF, hfo, hops, useVals_length ops _ hsz]) herr hal]
          simp only [straightSem, hops, hic, hU, hex]
          have hacc' : AccessOk F ctx ic
              (placeUses ops (canonRegs ops) (useVals ops (canonRegs ops) P) w) := by
            rw [hU]; exact hacc
          simp only [hacc', hok, and_self, ite_true]
        obtain ⟨s', -, hW, hK, -⟩ := (formOk_sound (F := F) (X := X) hfo).1 env0 E2E.checkCtx0 ""
          ops (canonRegs ops) ic P w _ t' hops hcs hic hPw hal' herr' hsem
        refine ⟨hok.1, ?_⟩
        have h1 : Arm.r (.GPR 31#5) s' = Arm.r (.GPR 31#5) t' := hW.1 _ (by simp [Masked])
        have h2 : Arm.r (.GPR 31#5) P = Arm.r (.GPR 31#5) w := hPw.1 _ (by simp [Masked])
        have h3 : Arm.r (.GPR 31#5) s' = Arm.r (.GPR 31#5) P := hK.1
        rw [← h1, h3, h2]
      · cases h
    · cases h
  · cases h

/-! ## The LL/SC loops keep the error flag and `sp` -/

open Classical in
theorem loopSem_keep {F : BitVec 64 → Prop} {ty : CTy} {a : CV} {body : List Line}
    {regs : List Reg} {uses : List CV} {defs : List Reg} {w : ArmState}
    {r : List CV × ArmState × Ctl} (h : loopSem F ty a body regs uses defs w = some r)
    (hreg : ∀ p ∈ regs.zip uses, ∀ n, p.1 = .x n → rnum n ≠ 31#5)
    (hbody : AtomTy ty → ∀ t t', Arm.r .ERR t = .None → execLines env0 body t = some t' →
      Arm.r (.GPR 31#5) t' = Arm.r (.GPR 31#5) t) :
    Arm.r .ERR r.2.1 = .None ∧ Arm.r (.GPR 31#5) r.2.1 = Arm.r (.GPR 31#5) w := by
  unfold loopSem at h
  split at h
  · rename_i hc
    split at h
    · rename_i t' ht
      split at h
      · rename_i hok
        cases h
        refine ⟨hok.1, ?_⟩
        rw [hbody hc.1 _ _ (by rw [err_foldl]; exact hc.2.2) ht]
        exact VCodeAddr.r31_foldl _ _ hreg
      · cases h
    · cases h
  · cases h

theorem rmw_body_sp {ty : CTy} (op : AtomicRmwLoopOp) (fl : Clif.MemFlags) (hty : AtomTy ty)
    (t t' : ArmState) (he : Arm.r .ERR t = .None)
    (hx : execLines env0 (rmwLoopBody ty.bits op fl) t = some t') :
    Arm.r (.GPR 31#5) t' = Arm.r (.GPR 31#5) t := by
  obtain ⟨t'', h1, -, -, -, hF, -⟩ := rmwBody_spec hty op fl env0 t he
  rw [hx] at h1
  cases h1
  exact hF _ (by simp) (by simp) (by simp)

theorem casHead_sp {ty : CTy} (fl : Clif.MemFlags) (hty : AtomTy ty)
    (t t' : ArmState) (he : Arm.r .ERR t = .None)
    (hx : execLines env0 (casLoopHead ty.bits fl) t = some t') :
    Arm.r (.GPR 31#5) t' = Arm.r (.GPR 31#5) t := by
  obtain ⟨t'', h1, -, -, hF, -⟩ := casHead_spec hty fl env0 t he
  rw [hx] at h1
  cases h1
  exact hF _ (by simp) (by simp) (by simp)

theorem stlxr_sp {ty : CTy} (fl : Clif.MemFlags) (hty : AtomTy ty)
    (t t' : ArmState) (he : Arm.r .ERR t = .None)
    (hx : execLines env0 [.ins (.stlxr ty.bits (.x 24) (.x 28) (.x 25)) fl.trapCode] t = some t') :
    Arm.r (.GPR 31#5) t' = Arm.r (.GPR 31#5) t := by
  obtain ⟨t'', h1, -, hF, -⟩ := stlxr_spec hty fl env0 t he
  rw [hx] at h1
  cases h1
  exact hF _ (by simp) (by simp)

/-! ## One step -/

/-- **A successful `csem` step keeps the footprint premises**: from an error-free world with an
aligned `sp`, a step with control `next` of a control form or of a straight-line form covered by
`csemWF` (not a call) ends in an error-free world with the same `sp`, hence aligned. -/
theorem csem_keep {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst} {u : List CV}
    {w : ArmState} (hcall : ∀ info, i ≠ .call info) (htry : ∀ info ti, i ≠ .tryCall info ti)
    (hcov : i.isCtl = true ∨ csemWF ctx i u = true) (he : Arm.r .ERR w = .None)
    (hal : Arm.CheckSPAlignment w) {o : List CV} {w' : ArmState}
    (h : csem F ctx X i u w = some (o, w', .next)) :
    Arm.r .ERR w' = .None ∧ Arm.CheckSPAlignment w' ∧
      Arm.r (.GPR 31#5) w' = Arm.r (.GPR 31#5) w := by
  suffices hk : Arm.r .ERR w' = .None ∧ Arm.r (.GPR 31#5) w' = Arm.r (.GPR 31#5) w from
    ⟨hk.1, align_of_spEq hk.2 hal, hk.2⟩
  cases hctl : i.isCtl with
  | false =>
    have hwf : csemWF ctx i u = true := by
      rcases hcov with h' | h'
      · rw [hctl] at h'; cases h'
      · exact h'
    have hfo : FormOk ctx i = true := by
      simp only [csemWF, Bool.and_eq_true] at hwf; exact hwf.1
    rw [csem_of_wf hctl hwf he hal] at h
    exact straight_keep X hfo hctl hwf he hal h
  | true =>
    cases i <;> (try (simp [MInst.isCtl] at hctl; done))
    case call info => exact absurd rfl (hcall info)
    case tryCall info ti => exact absurd rfl (htry info ti)
    case atomicRmwLoop ty op fl _ _ _ _ _ =>
      simp only [csem] at h
      split at h
      · rename_i u x
        simp only [he, ite_true] at h
        have hk := loopSem_keep h (fun p hp n hn => by
            simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
              List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl <;> cases hn <;> decide)
          (fun hty t t' he' hx => rmw_body_sp op fl hty t t' he' hx)
        exact hk
      · cases h
    case atomicCasLoop ty fl _ _ _ _ _ =>
      simp only [csem] at h
      split at h
      · rename_i u e x
        simp only [he, ite_true] at h
        split at h
        · rename_i outs t1 c1 hh
          have hk1 := loopSem_keep hh (fun p hp n hn => by
              simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
                List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl | rfl <;> cases hn <;> decide)
            (fun hty t t' he' hx => casHead_sp fl hty t t' he' hx)
          split at h
          · cases h; exact hk1
          · have hk2 := loopSem_keep h (fun p hp => by simp at hp)
              (fun hty t t' he' hx => stlxr_sp fl hty t t' he' hx)
            exact ⟨hk2.1, hk2.2.trans hk1.2⟩
        · cases h
      · cases h
    case testBitAndBranch =>
      simp only [csem] at h
      split at h
      · simp at h
      · cases h
    case jtSequence =>
      simp only [csem] at h
      split at h
      · split at h
        · simp at h
        · split at h <;> simp at h
      · cases h
    case elfTlsGetAddr =>
      simp only [csem, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      simp [Arm.write_pstate, Arm.r_of_w_different, he]
    all_goals
      simp only [csem, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact ⟨he, rfl⟩

/-! ## Along a run -/

/-- The instructions `runFoot_csem` covers: not a call, and a control form or a covered
straight-line form. -/
def Covered (ctx : FnCtx) (i : MInst) : Prop :=
  (∀ info, i ≠ .call info) ∧ (∀ info ti, i ≠ .tryCall info ti) ∧
    (i.isCtl = true ∨ FormOk ctx i = true)

/-- **The footprint premises hold along the run**: the run of covered instructions from an
error-free world with an aligned `sp` has the precise footprint `cEvs` at every reached state. -/
theorem runFoot_csem {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} (hX : TlsMemFree X) :
    ∀ {ms : List MInst} {ρ : Nat → CV} {w : ArmState}, (∀ i ∈ ms, Covered ctx i) →
      Arm.r .ERR w = .None → Arm.CheckSPAlignment w →
      RunFoot (csem F ctx X) (cEvs F ctx) ms ρ w
  | [], _, _, _, _, _ => trivial
  | i :: ms, ρ, w, hms, he, hal => by
    obtain ⟨hc, ht, hcov⟩ := hms i List.mem_cons_self
    intro ops hops
    have hwf : i.isCtl = false → csemWF ctx i (vuses ops ρ) = true := fun hctl => by
      have hfo : FormOk ctx i = true := by
        rcases hcov with h | h
        · rw [hctl] at h; cases h
        · exact h
      simp [csemWF, hfo, hops, vuses, useCount]
    refine ⟨ifoot_csem hX he hc ht (fun hctl => ⟨hwf hctl, hal⟩), fun outs w' hs => ?_⟩
    have hcov' : i.isCtl = true ∨ csemWF ctx i (vuses ops ρ) = true := by
      cases hi : i.isCtl
      · exact .inr (hwf hi)
      · exact .inl rfl
    obtain ⟨he', hal', -⟩ := csem_keep hc ht hcov' he hal hs
    exact runFoot_csem hX (fun j hj => hms j (List.mem_cons_of_mem _ hj)) he' hal'

end Concurrency.SegFoot
