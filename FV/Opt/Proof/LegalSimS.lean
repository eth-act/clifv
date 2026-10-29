module

public import FV.Opt.Proof.LegalSim

@[expose] public section

/-!
# The simulation steps of `Opt.Legal.check` with stepwise target runs (S10e, #232)

`FV/Opt/Proof/LegalSim.lean` relates a source step to target steps by `TStep`, which is
extensional (`∃ k, ∀ n, runLoop (n + k) A = runLoop n B`): the target frame it names is only
`runLoop`-equivalent to the frame the target run reaches. The run with unwinding
(`Clif.runLoopX`) is not determined by the `runLoop` behaviour (an extern that unwinds is
`stuck` there), so the refinement theorem with unwinding (`FV/Opt/Proof/LegalSimX.lean`) needs
the reached frame itself.

This file repeats the simulation lemmas of `LegalSim.lean` that produce `TStep` (`sim_same` …
`sim_try`, `step_sim`), with `TStep` the stepwise relation: zero or more `next` steps of the
target between states without callers. The proofs are `LegalSim.lean`'s, unchanged: they build
`TStep` only by `TStep.of_lstar`, `TStep.of_step` and `TStep.trans`, which this file provides for
the stepwise relation. `TStep.runLoop` recovers `LegalSim.lean`'s form.
-/

namespace Opt.Legal.S

open Clif Opt Opt.Legalize128 Opt.Legal

/-- The target run from `⟨fr', [], m⟩` reaches `⟨fr1', [], m1⟩` by zero or more `next` steps
between states without callers. -/
inductive TStep (env : Env) (p' : Program) : Frame → Mem → Frame → Mem → Prop
  | refl (fr : Frame) (m : Mem) : TStep env p' fr m fr m
  | step {fr : Frame} {m : Mem} {fr1 : Frame} {m1 : Mem} {fr2 : Frame} {m2 : Mem} :
      Clif.step env p' ⟨fr, [], m⟩ = .next ⟨fr1, [], m1⟩ → TStep env p' fr1 m1 fr2 m2 →
      TStep env p' fr m fr2 m2

theorem TStep.trans {env : Env} {p' : Program} {a b c : Frame} {ma mb mc : Mem}
    (h1 : TStep env p' a ma b mb) (h2 : TStep env p' b mb c mc) : TStep env p' a ma c mc := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem TStep.of_lstar {env : Env} {p' : Program} {fr' fr1' : Frame} {m m1 : Mem}
    (h : LStar fr' m fr1' m1) : TStep env p' fr' m fr1' m1 := by
  induction h with
  | refl => exact .refl _ _
  | step hs _ ih =>
    refine .step ?_ ih
    rw [step_eq_lift_of (s := ⟨_, [], _⟩) hs (fun _ h => by cases h)]
    rfl

theorem TStep.of_step {env : Env} {p' : Program} {fr' fr1' : Frame} {m m1 : Mem}
    (h : Clif.step env p' ⟨fr', [], m⟩ = .next ⟨fr1', [], m1⟩) : TStep env p' fr' m fr1' m1 :=
  .step h (.refl _ _)

/-- `LegalSim.lean`'s `TStep`. -/
theorem TStep.runLoop {env : Env} {p' : Program} {fr' fr1' : Frame} {m m1 : Mem}
    (h : TStep env p' fr' m fr1' m1) :
    ∃ k, ∀ n, Clif.runLoop env p' (n + k) ⟨fr', [], m⟩ = Clif.runLoop env p' n ⟨fr1', [], m1⟩ := by
  induction h with
  | refl => exact ⟨0, fun _ => rfl⟩
  | step hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, fun n => ?_⟩
    rw [show n + (k + 1) = (n + k) + 1 by omega, runLoop_succ, hs]
    exact hk n

/-- What the target does for a source step. -/
def SimOut (C : Ctx) (env : Env) (p' : Program) (fr' : Frame) (m : Mem) : StepResult → Prop
  | .next s1 => s1.callers = [] ∧ MemBounded s1.mem ∧
      ∃ fr1', FRel C s1.frame fr1' ∧ TStep env p' fr' m fr1' s1.mem
  | .done vals m1 => ∃ vals', ExpRel C.rg vals vals' ∧ ∃ k, runLoop env p' k ⟨fr', [], m⟩ = .returned vals' m1
  | .trapped c => ∃ k, runLoop env p' k ⟨fr', [], m⟩ = .trapped c
  | .stuck _ => True

theorem SimOut.pre {C : Ctx} {env : Env} {p' : Program} {fr' fr1' : Frame} {m m1 : Mem}
    {r : StepResult} (ht : TStep env p' fr' m fr1' m1) (hm : m1 = m ∨ ∀ s1, r ≠ .next s1)
    (h : SimOut C env p' fr1' m1 r) : SimOut C env p' fr' m r := by
  obtain ⟨k0, hk0⟩ := ht.runLoop
  cases r with
  | next s1 =>
    rcases hm with rfl | hm
    · obtain ⟨h1, h2, fr2, h3, h4⟩ := h
      exact ⟨h1, h2, fr2, h3, TStep.trans ht h4⟩
    · exact absurd rfl (hm s1)
  | done vals m2 =>
    obtain ⟨vals', h1, k, hk⟩ := h
    exact ⟨vals', h1, k + k0, by rw [hk0, hk]⟩
  | trapped c =>
    obtain ⟨k, hk⟩ := h
    exact ⟨k + k0, by rw [hk0, hk]⟩
  | stuck _ => trivial

/-- **`same`**: the statement itself. -/
theorem sim_same {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) (hpl : planOf C st = some .same) {ts2 : List Stmt}
    (hb' : fr'.body = st :: ts2) (hcode : codeOk C rest fr.term ts2 fr'.term = true) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨hplain, hnc, hnci, hnfa⟩ := planOf_same hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hnd := results_nodup hG.defs hB hst
  have hops : ∀ x ∈ instOps st.inst, fr'.regs x = fr.regs x := fun x hx =>
    hR.peq x (ops_lt hG hB hst hx) (plain_iff.1 (hplain x (List.mem_append_left _ hx)))
  have hev : evalInst fr' m st.inst = evalInst fr m st.inst :=
    evalInst_same hops hR.slots (by rw [hR.func', hR.func]; exact hG.globals)
      (fun t fn h => by rw [hR.func', hR.func]; exact hnfa t fn h)
  rw [step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci]
  have hstep' := step_inst env' p' ⟨fr', [], m⟩ st ts2 hb' hnc hnci
  rw [hev] at hstep'
  cases hr : evalInst fr m st.inst with
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    rw [hr] at hstep'
    simp only [StepResult.ofRes_ok, continueWith] at hstep' ⊢
    cases hs : fr.regs.setMany st.results vals with
    | none => trivial
    | some ρ1 =>
      obtain ⟨ρ1', hs'⟩ := setMany_of_len fr'.regs (setMany_len hs)
      simp only [hs'] at hstep'
      refine ⟨rfl, memBounded_eval hr hM, { fr' with regs := ρ1', body := ts2 }, ?_,
        TStep.of_step hstep'⟩
      refine frel_after hG hR hb hcode hs ?_ ?_ (srcInv_stmt hG.defs hB hst hR.src hr hs)
      · intro v hv _ x hx
        have hpv := plain_iff.1 (hplain v (List.mem_append_right _ hv))
        obtain ⟨i, hi, hvi⟩ := setMany_mem hs hnd hv
        rw [RelV.plain hpv, setMany_get hs' hnd hi, ← hvi, hx]
      · intro w _ hni
        refine setMany_other hs' fun hw => ?_
        have hpw := plain_iff.1 (hplain w (List.mem_append_right _ hw))
        exact hni w hw (res_lt hG hB hst hw) (by simp [img, hpw])
  | trap c =>
    rw [hr] at hstep'
    exact ⟨1, by rw [runLoop_succ, hstep']; rfl⟩
  | stuck msg => trivial

/-- **Pure plans**: the segment runs the pattern. -/
theorem sim_pure {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) {pat : List Stmt} {ins outs : List ValueId}
    (hpl : planOf C st = some (.pure pat ins outs)) {seg ts2 : List Stmt}
    (hseg : pureOk C pat ins outs seg = true) (hb' : fr'.body = seg ++ ts2)
    (hcode : codeOk C rest fr.term ts2 fr'.term = true) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hnd := results_nodup hG.defs hB hst
  obtain ⟨hnc, hnci⟩ := planOf_pure_inst hpl
  rw [step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci]
  cases hr : evalInst fr m st.inst with
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    obtain ⟨rfl, hcov, inVals, ρ0, hH, hrun, hO⟩ := pure_step hG hB hst hpl hR.vrel hR.src hr
    simp only [StepResult.ofRes_ok, continueWith]
    cases hs : fr.regs.setMany st.results vals with
    | none => trivial
    | some ρ1 =>
      obtain ⟨regs', hl, hout, hkeep⟩ := pureOk_run hseg hH.len hrun (fr := fr') hH.get _ ts2
      have hfr' : { fr' with body := seg ++ ts2 } = fr' := by rw [← hb']
      rw [hfr'] at hl
      refine ⟨rfl, hM, { fr' with regs := regs', body := ts2 }, ?_, TStep.of_lstar hl⟩
      refine frel_after hG hR hb hcode hs ?_ ?_ (srcInv_stmt hG.defs hB hst hR.src hr hs)
      · intro v hv _ x hx
        obtain ⟨i, hi, hvi⟩ := setMany_mem hs hnd hv
        exact hO regs' hout i v x hi (by rw [← hvi, hx])
      · intro w hw hni
        refine hkeep w hw fun hwo => ?_
        obtain ⟨r, hr, hwr⟩ := hcov w hwo
        exact hni r hr (res_lt hG hB hst hr) hwr
  | trap c => exact absurd hr (pure_notrap hpl fr m c)
  | stuck msg => trivial

/-- **Split load**: two 8-byte loads of the halves. -/
theorem sim_load {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) {rl rh q : ValueId} {fl : MemFlags} {off : Int}
    (hpl : planOf C st = some (.load rl rh q fl off)) {ts2 : List Stmt}
    (hb' : fr'.body = [S rl (.load .load .i64 fl q off), S rh (.load .load .i64 fl q (off + 8))] ++ ts2)
    (hrl : rl ≠ rh) (hrq : rl ≠ q)
    (hcode : codeOk C rest fr.term ts2 fr'.term = true)
    (hT : ∀ c, step env p ⟨fr, [], m⟩ ≠ .trapped c) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨hi, ⟨r, hrs, hr⟩, hpq, hbig⟩ := planOf_load hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hq : q < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hnc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by rw [hi] at h; cases h
  have hnci : ∀ sig c args, st.inst ≠ .callIndirect sig c args := fun _ _ _ h => by
    rw [hi] at h; cases h
  have hstep := step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci
  rw [hstep] at hT ⊢
  cases hev : evalInst fr m st.inst with
  | stuck msg => trivial
  | trap c => rw [hev] at hT; exact absurd rfl (hT c)
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    have hev' := hev
    rw [hi] at hev'
    simp only [evalInst, Opt.Res.bind_eq_ok, LoadOp.size, Ty.bytes, LoadOp.signed,
      Bool.false_eq_true, ite_false, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev'
    obtain ⟨pv, hpv, u, -, raw, hraw, rfl, rfl⟩ := hev'
    have hraw' : m.load fl (effAddr pv off) 16 (8 * 16) = .ok raw := hraw
    have hA := hM _ _ (mem_load_valid hraw')
    obtain ⟨hlo, hhi⟩ := load_split hbig hraw'
    rw [← effAddr_add8 pv off hA] at hhi
    have hpv' : fr'.regs q = some pv := by
      rw [hR.peq q hq (plain_iff.1 hpq)]; exact get_ok hpv
    simp only [StepResult.ofRes_ok, continueWith, hrs, Regs.setMany_cons, Regs.setMany_nil]
    -- the target: two loads
    have h1 := lstep_eval (fr := fr') (m := m) (st := S rl (.load .load .i64 fl q off))
      (rest := S rh (.load .load .i64 fl q (off + 8)) :: ts2) (by rw [hb']; rfl)
      (fun _ _ h => by cases h) (eval_load64 hpv' hlo) (by simp [S]; rfl)
    have h2 := lstep_eval (fr := ⟨fr'.func, fr'.regs.set rl ⟨.i64, raw.extractLsb' 0 64⟩,
        fr'.slots, S rh (.load .load .i64 fl q (off + 8)) :: ts2, fr'.term⟩) (m := m)
      (st := S rh (.load .load .i64 fl q (off + 8))) (rest := ts2) rfl (fun _ _ h => by cases h)
      (eval_load64 (by simp only; rw [Regs.set_other _ _ (Ne.symm hrq)]; exact hpv') hhi)
      (by simp [S]; rfl)
    refine ⟨rfl, hM, _, ?_, TStep.of_lstar (.step h1 (.step h2 (.refl _ _)))⟩
    have hset : fr.regs.setMany st.results [⟨.i128, BitVec.zeroExtend Ty.i128.width raw⟩] =
        some (fr.regs.set r ⟨.i128, BitVec.zeroExtend Ty.i128.width raw⟩) := by rw [hrs]; rfl
    refine frel_after hG hR hb hcode hset ?_ ?_ (srcInv_stmt hG.defs hB hst hR.src hev hset)
    · intro v hv _ x hx
      rw [hrs, List.mem_singleton] at hv
      subst hv
      simp only [Regs.set_same, Option.some.injEq] at hx
      subst hx
      rw [RelV.pair hr]
      refine ⟨raw.extractLsb' 0 64, raw.extractLsb' 64 64, ?_, ?_, ?_⟩
      · have e : BitVec.zeroExtend Ty.i128.width raw = raw := BitVec.setWidth_eq raw
        rw [e]
        exact congrArg _ (split128 raw).symm
      · rw [Regs.set_other _ _ hrl, Regs.set_same]; rfl
      · simp
    · intro w _ hni
      rw [hrs] at hni
      have := hni r (List.mem_singleton_self _) (res_lt hG hB hst (by rw [hrs]; simp))
      simp only [img, hr, List.mem_cons, List.mem_nil_iff, or_false, not_or] at this
      rw [Regs.set_other _ _ this.2, Regs.set_other _ _ this.1]

/-- **Split store**: two 8-byte stores of the halves. -/
theorem sim_store {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) {xl xh q : ValueId} {fl : MemFlags} {off : Int}
    (hpl : planOf C st = some (.store xl xh q fl off)) {ts2 : List Stmt}
    (hb' : fr'.body = [{ results := [], inst := .store .store .i64 fl xl q off },
      { results := [], inst := .store .store .i64 fl xh q (off + 8) }] ++ ts2)
    (hcode : codeOk C rest fr.term ts2 fr'.term = true)
    (hT : ∀ c, step env p ⟨fr, [], m⟩ ≠ .trapped c) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨⟨x, hi, hx⟩, hrs, hpq, hbig⟩ := planOf_store hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hx0 : x < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hq : q < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hnc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by rw [hi] at h; cases h
  have hnci : ∀ sig c args, st.inst ≠ .callIndirect sig c args := fun _ _ _ h => by
    rw [hi] at h; cases h
  have hstep := step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci
  rw [hstep] at hT ⊢
  cases hev : evalInst fr m st.inst with
  | stuck msg => trivial
  | trap c => rw [hev] at hT; exact absurd rfl (hT c)
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    have hev' := hev
    rw [hi] at hev'
    simp only [evalInst, Opt.Res.bind_eq_ok, StoreOp.size, Ty.bytes, Opt.Res.pure_eq_ok,
      Prod.mk.injEq] at hev'
    obtain ⟨a, ha, pv, hpv, u, -, mem', hst', rfl, rfl⟩ := hev'
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hR.vrel hx0 hx (getAs_ok ha)
    cases val_i128 he
    have hst16 : m.store fl (effAddr pv off) 16 (h ++ l) = .ok mem' := hst'
    have hA := hM _ _ (mem_store_valid hst16)
    obtain ⟨m1, hs1, hs2⟩ := store_split hbig hst16
    rw [append_lo, append_hi, ← effAddr_add8 pv off hA] at *
    have hpv' : fr'.regs q = some pv := by
      rw [hR.peq q hq (plain_iff.1 hpq)]; exact get_ok hpv
    simp only [StepResult.ofRes_ok, continueWith, hrs, Regs.setMany_nil]
    have h1 := lstep_eval (fr := fr') (m := m) (st := { results := [], inst := .store .store .i64 fl xl q off })
      (rest := { results := [], inst := .store .store .i64 fl xh q (off + 8) } :: ts2)
      (by rw [hb']; rfl) (fun _ _ h => by cases h) (eval_store64 hl hpv' hs1) rfl
    have h2 := lstep_eval (fr := ⟨fr'.func, fr'.regs, fr'.slots,
        { results := [], inst := .store .store .i64 fl xh q (off + 8) } :: ts2, fr'.term⟩) (m := m1)
      (st := { results := [], inst := .store .store .i64 fl xh q (off + 8) }) (rest := ts2) rfl
      (fun _ _ h => by cases h) (eval_store64 hh hpv' hs2) rfl
    refine ⟨rfl, memBounded_store hs2 (memBounded_store hs1 hM), _, ?_,
      TStep.of_lstar (.step h1 (.step h2 (.refl _ _)))⟩
    have hset : fr.regs.setMany st.results [] = some fr.regs := by rw [hrs]; rfl
    exact frel_after hG hR hb hcode hset (by rw [hrs]; simp) (fun _ _ _ => rfl)
      (srcInv_stmt hG.defs hB hst hR.src hev hset)

/-- **`div` at `i128`**: a call of the `__*ti3` helper. -/
theorem sim_div {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program} (hH : HelperOk env')
    (hext' : ∀ fn e, C.g.extern? fn = some e → p'.func? e.name = none)
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) {op : DivOp} {xl xh yl yh rl rh : ValueId}
    (hpl : planOf C st = some (.div op xl xh yl yh rl rh)) {fn : FnRef} {ts2 : List Stmt}
    (hb' : fr'.body = { results := [rl, rh], inst := .call fn [xl, xh, yl, yh] } :: ts2)
    (hrl : rl ≠ rh) (hfn : C.g.extern? fn = some (helperExt op))
    (hcode : codeOk C rest fr.term ts2 fr'.term = true) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨x, y, r, hi, hrs, hx, hy, hr⟩ := planOf_div hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hx0 : x < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hy0 : y < C.T0 := ops_lt hG hB hst (by rw [hi]; simp [instOps])
  have hnc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by rw [hi] at h; cases h
  have hnci : ∀ sig c args, st.inst ≠ .callIndirect sig c args := fun _ _ _ h => by
    rw [hi] at h; cases h
  rw [step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci]
  obtain ⟨hf, hhf, hsem⟩ := hH op
  cases hev : evalInst fr m st.inst with
  | stuck msg => trivial
  | ok vm =>
    obtain ⟨vals, mem⟩ := vm
    have hev' := hev
    rw [hi] at hev'
    simp only [evalInst, Opt.Res.bind_eq_ok, Opt.Res.pure_eq_ok, Prod.mk.injEq] at hev'
    obtain ⟨a, ha, b, hb2, res, hres, rfl, rfl⟩ := hev'
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hR.vrel hx0 hx (getAs_ok ha)
    cases val_i128 he
    obtain ⟨bl, bh, he2, hbl, hbh⟩ := pairVal hR.vrel hy0 hy (getAs_ok hb2)
    cases val_i128 he2
    have hsem' := hsem l h bl bh m
    have e : @Sem.div (64 + 64) op (h ++ l) (bh ++ bl) =
        @Sem.div Ty.i128.width op (h ++ l) (bh ++ bl) := rfl
    rw [e] at hsem'
    have hdiv : @Sem.div Ty.i128.width op (h ++ l) (bh ++ bl) = .ok res := by
      revert hres
      cases Sem.div (w := Ty.i128.width) op (h ++ l) (bh ++ bl) with
      | ok v => intro hres; cases hres; rfl
      | error c => intro hres; cases hres
    rw [hdiv] at hsem'
    simp only [StepResult.ofRes_ok, continueWith, hrs, Regs.setMany_cons, Regs.setMany_nil]
    have hstep' := step_extcall (env := env') (p := p') (s := ⟨fr', [], m⟩) hb'
      (by rw [hR.func']; exact hfn)
      (holds_getMany (show Holds fr'.regs [xl, xh, yl, yh]
        [⟨.i64, l⟩, ⟨.i64, h⟩, ⟨.i64, bl⟩, ⟨.i64, bh⟩] from ⟨hl, hh, hbl, hbh, trivial⟩))
      rfl (hext' fn _ hfn) hhf
    simp only [hsem', helperExt, helperSig] at hstep'
    simp only [List.map_cons, List.map_nil, AbiParam.tys, beq_self_eq_true, ite_true,
      continueWith, Regs.setMany_cons, Regs.setMany_nil] at hstep'
    refine ⟨rfl, hM, _, ?_, TStep.of_step hstep'⟩
    have hset : fr.regs.setMany st.results [⟨.i128, res⟩] =
        some (fr.regs.set r ⟨.i128, res⟩) := by rw [hrs]; rfl
    refine frel_after hG hR hb hcode hset ?_ ?_ (srcInv_stmt hG.defs hB hst hR.src hev hset)
    · intro v hv _ z hz
      rw [hrs, List.mem_singleton] at hv
      subst hv
      simp only [Regs.set_same, Option.some.injEq] at hz
      subst hz
      rw [RelV.pair hr]
      refine ⟨res.extractLsb' 0 64, res.extractLsb' 64 64, ?_, ?_, ?_⟩
      · exact congrArg _ (split128 res).symm
      · rw [Regs.set_other _ _ hrl, Regs.set_same]; rfl
      · simp
    · intro w _ hni
      rw [hrs] at hni
      have := hni r (List.mem_singleton_self _) (res_lt hG hB hst (by rw [hrs]; simp))
      simp only [img, hr, List.mem_cons, List.mem_nil_iff, or_false, not_or] at this
      rw [Regs.set_other _ _ this.2, Regs.set_other _ _ this.1]
  | trap c =>
    have hev' := hev
    rw [hi] at hev'
    simp only [evalInst, Opt.Res.bind_eq_trap, getAs_ne_trap, false_or] at hev'
    obtain ⟨a, ha, b, hb2, hres⟩ := hev'
    obtain ⟨l, h, he, hl, hh⟩ := pairVal hR.vrel hx0 hx (getAs_ok ha)
    cases val_i128 he
    obtain ⟨bl, bh, he2, hbl, hbh⟩ := pairVal hR.vrel hy0 hy (getAs_ok hb2)
    cases val_i128 he2
    have hsem' := hsem l h bl bh m
    have e : @Sem.div (64 + 64) op (h ++ l) (bh ++ bl) =
        @Sem.div Ty.i128.width op (h ++ l) (bh ++ bl) := rfl
    rw [e] at hsem'
    have hdiv : @Sem.div Ty.i128.width op (h ++ l) (bh ++ bl) = .error c := by
      revert hres
      cases Sem.div (w := Ty.i128.width) op (h ++ l) (bh ++ bl) with
      | ok v => intro hres; simp [Res.ofExcept] at hres
      | error c' => intro hres; simp [Opt.Res.bind_eq_trap, Res.ofExcept] at hres; rw [hres]
    rw [hdiv] at hsem'
    have hstep' := step_extcall (env := env') (p := p') (s := ⟨fr', [], m⟩) hb'
      (by rw [hR.func']; exact hfn)
      (holds_getMany (show Holds fr'.regs [xl, xh, yl, yh]
        [⟨.i64, l⟩, ⟨.i64, h⟩, ⟨.i64, bl⟩, ⟨.i64, bh⟩] from ⟨hl, hh, hbl, hbh, trivial⟩))
      rfl (hext' fn _ hfn) hhf
    simp only [hsem'] at hstep'
    exact ⟨1, by rw [runLoop_succ, hstep']⟩

/-- The condition pattern on an `i128` condition: the target computes its truth value at the
fresh `c`, keeping every non-fresh value. -/
theorem cond_run {C : Ctx} {fr' : Frame} {m : Mem} {lo hi c : ValueId} {segA rest : List Stmt}
    (hseg : pureOk C Pat.cond [lo, hi] [c] segA = true) {l h : BitVec 64}
    (hl : fr'.regs lo = some ⟨.i64, l⟩) (hh : fr'.regs hi = some ⟨.i64, h⟩) :
    ∃ regs', LStar { fr' with body := segA ++ rest } m { fr' with regs := regs', body := rest } m ∧
      regs' c = some ⟨.i8, Sem.bool8 (Sem.truthy (h ++ l))⟩ ∧
      ∀ w, C.fresh w = false → w ≠ c → regs' w = fr'.regs w := by
  obtain ⟨ρ0, hrun, h2⟩ := pat_cond l h
  obtain ⟨regs', hl', hout, hkeep⟩ := pureOk_run hseg (inVals := [V64 l, V64 h]) rfl hrun
    (fr := fr') (Holds.get (show Holds fr'.regs [lo, hi] [V64 l, V64 h] from ⟨hl, hh, trivial⟩))
    m rest
  exact ⟨regs', hl', hout 0 (by simp) _ h2, fun w hw hwc => hkeep w hw (by simpa using hwc)⟩

/-- **`trapz`/`trapnz` on an `i128` condition**: the condition pattern, then the trap. -/
theorem sim_trap {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) {lo hi : ValueId} {nz : Bool} {code : TrapCode}
    (hpl : planOf C st = some (.trap lo hi nz code)) {segA ts2 : List Stmt} {c : ValueId}
    (hseg : pureOk C Pat.cond [lo, hi] [c] segA = true) (hc : C.fresh c = true)
    (hb' : fr'.body = segA ++
      { results := [], inst := if nz then .trapnz c code else .trapz c code } :: ts2)
    (hcode : codeOk C rest fr.term ts2 fr'.term = true) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨c0, hi, hrs, hc0⟩ := planOf_trap hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hc00 : c0 < C.T0 := ops_lt hG hB hst (by rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [instOps])
  have hnc : ∀ fn args, st.inst ≠ .call fn args := fun _ _ h => by
    rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at h <;> cases h
  have hnci : ∀ sig c args, st.inst ≠ .callIndirect sig c args := fun _ _ _ h => by
    rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at h <;> cases h
  rw [step_inst env p ⟨fr, [], m⟩ st rest hb hnc hnci]
  cases hcv : fr.regs c0 with
  | none =>
    have : evalInst fr m st.inst = .stuck s!"use of undefined value v{c0}" := by
      rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [evalInst, Frame.get, hcv, Res.ofOption, bind, Res.bind]
    rw [this]; trivial
  | some cv =>
    obtain ⟨l, h, rfl, hl, hh⟩ := pairVal hR.vrel hc00 hc0 hcv
    obtain ⟨regs', hls, hcr, hkeep⟩ := cond_run (fr' := fr') (m := m)
      (rest := { results := [], inst := if nz then .trapnz c code else .trapz c code } :: ts2) hseg hl hh
    have hfr : { fr' with body := segA ++
        { results := [], inst := if nz then .trapnz c code else .trapz c code } :: ts2 } = fr' := by
      rw [← hb']
    rw [hfr] at hls
    have hT := TStep.of_lstar (env := env') (p' := p') hls
    refine SimOut.pre hT (.inl rfl) ?_
    have hset : fr.regs.setMany st.results [] = some fr.regs := by rw [hrs]; rfl
    rcases hi with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · -- trapz: continue when the condition holds
      simp only [Bool.false_eq_true, ite_false]
      have hcv' : ({ fr' with regs := regs', body := { results := [], inst := .trapz c code } :: ts2 } :
          Frame).regs c = some ⟨.i8, Sem.bool8 (Sem.truthy (h ++ l))⟩ := hcr
      have hev : evalInst fr m st.inst =
          if Sem.truthy (h ++ l) then .ok ([], m) else .trap code := by
        rw [h1]; simp only [evalInst, Frame.get, hcv, Res.ofOption, bind, Res.bind]; rfl
      have hev' : evalInst { fr' with regs := regs', body := { results := [], inst := .trapz c code } :: ts2 } m (.trapz c code) =
          if Sem.truthy (h ++ l) then .ok ([], m) else .trap code := by
        simp only [evalInst, Frame.get, hcr, Res.ofOption, bind, Res.bind, truthy_bool8']; rfl
      rw [hev]
      by_cases hbt : Sem.truthy (h ++ l) = true
      · rw [if_pos hbt] at hev hev' ⊢
        simp only [StepResult.ofRes_ok, continueWith, hset]
        have h1s := lstep_eval (fr := { fr' with regs := regs', body := { results := [], inst := .trapz c code } :: ts2 }) (m := m) (st := { results := [], inst := .trapz c code })
          (rest := ts2) rfl (fun _ _ h => by cases h) hev' rfl
        refine ⟨rfl, hM, _, ?_, TStep.of_lstar (.single h1s)⟩
        exact frel_after hG hR hb hcode hset (by rw [hrs]; simp)
          (fun w hw _ => hkeep w hw (fresh_ne hc hw)) (srcInv_stmt hG.defs hB hst hR.src hev hset)
      · rw [if_neg hbt] at hev hev' ⊢
        refine ⟨1, ?_⟩
        rw [runLoop_succ, step_inst env' p' ⟨{ fr' with regs := regs', body := { results := [], inst := .trapz c code } :: ts2 }, [], m⟩ { results := [], inst := .trapz c code }
          ts2 rfl (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)]
        simp only [hev']
        rfl
    · -- trapnz: continue when the condition fails
      simp only [ite_true]
      have hcv' : ({ fr' with regs := regs', body := { results := [], inst := .trapnz c code } :: ts2 } :
          Frame).regs c = some ⟨.i8, Sem.bool8 (Sem.truthy (h ++ l))⟩ := hcr
      have hev : evalInst fr m st.inst =
          if Sem.truthy (h ++ l) then .trap code else .ok ([], m) := by
        rw [h1]; simp only [evalInst, Frame.get, hcv, Res.ofOption, bind, Res.bind]; rfl
      have hev' : evalInst { fr' with regs := regs', body := { results := [], inst := .trapnz c code } :: ts2 } m (.trapnz c code) =
          if Sem.truthy (h ++ l) then .trap code else .ok ([], m) := by
        simp only [evalInst, Frame.get, hcr, Res.ofOption, bind, Res.bind, truthy_bool8']; rfl
      rw [hev]
      by_cases hbt : Sem.truthy (h ++ l) = true
      · rw [if_pos hbt] at hev hev' ⊢
        refine ⟨1, ?_⟩
        rw [runLoop_succ, step_inst env' p' ⟨{ fr' with regs := regs', body := { results := [], inst := .trapnz c code } :: ts2 }, [], m⟩ { results := [], inst := .trapnz c code }
          ts2 rfl (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)]
        simp only [hev']
        rfl
      · rw [if_neg hbt] at hev hev' ⊢
        simp only [StepResult.ofRes_ok, continueWith, hset]
        have h1s := lstep_eval (fr := { fr' with regs := regs', body := { results := [], inst := .trapnz c code } :: ts2 }) (m := m) (st := { results := [], inst := .trapnz c code })
          (rest := ts2) rfl (fun _ _ h => by cases h) hev' rfl
        refine ⟨rfl, hM, _, ?_, TStep.of_lstar (.single h1s)⟩
        exact frel_after hG hR hb hcode hset (by rw [hrs]; simp)
          (fun w hw _ => hkeep w hw (fresh_ne hc hw)) (srcInv_stmt hG.defs hB hst hR.src hev hset)

/-- **A call with expanded arguments and results.** -/
theorem sim_call {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program}
    (hEx : ∀ fn e, C.f.extern? fn = some e → ExtRelAt env env' e.name e.sig)
    (hKeep : EnvKeepsBounded env)
    (hsrc : ∀ fn e, C.f.extern? fn = some e → p.func? e.name = none)
    (htgt : ∀ fn e, C.g.extern? fn = some e → p'.func? e.name = none)
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) {fn : FnRef} {e : ExtFunc}
    {args' : List ValueId} {rg : List (List SlotEl)} {rs : List ValueId}
    (hpl : planOf C st = some (.call fn e args' rg rs)) {rs' : List ValueId} {ts2 : List Stmt}
    (hb' : fr'.body = { results := rs', inst := .call fn args' } :: ts2)
    (hrets : retsOk C rg rs rs' = true) (hnd' : rs'.Nodup) {s' : Signature}
    (hs' : sigExp e.sig = some s') (hfn : C.g.extern? fn = some { e with sig := s' })
    (hcode : codeOk C rest fr.term ts2 fr'.term = true) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨args, gs, hi, hrs, hfe, hgs, hrg, hexp⟩ := planOf_call hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hnd := results_nodup hG.defs hB hst
  have hlt : ∀ x ∈ args, x < C.T0 := fun x hx => ops_lt hG hB hst (by rw [hi]; exact hx)
  have hst_eq : st = { results := rs, inst := .call fn args } := by rw [← hi, ← hrs]
  rw [hst_eq] at hb
  rw [hrs] at hnd
  obtain ⟨gs0, rg0, hgs0, hrg0, hpar', hret'⟩ := sigExp_spec hs'
  rw [hgs] at hgs0; cases hgs0
  rw [hrg] at hrg0; cases hrg0
  have hfe' : fr.func.extern? fn = some e := by rw [hR.func]; exact hfe
  rw [step_call env p _ rest rs fn args hb]
  cases hga : fr.getMany args with
  | stuck msg => simp only [stepCall, hfe', hga, Res.ofOption, bind, Res.bind, StepResult.ofRes]; trivial
  | trap c => exact absurd hga (getMany_ne_trap fr args c)
  | ok vals =>
    obtain ⟨vals', hv', hexp'⟩ := expandArgs_holds hR.vrel hR.zero hexp hlt (getMany_holds hga)
    by_cases hty : vals.map (·.ty) ≠ AbiParam.tys e.sig.params
    · have : (vals.map (·.ty) == AbiParam.tys e.sig.params) = false := by simpa using hty
      simp only [stepCall, hfe', hga, Res.ofOption, bind, Res.bind, checkTys, this, Res.check,
        StepResult.ofRes]
      trivial
    have hty : vals.map (·.ty) = AbiParam.tys e.sig.params := by simpa using hty
    have hty' : vals'.map (·.ty) = AbiParam.tys s'.params := by
      rw [hpar', AbiParam.tys, ← expRel_tys (groups_spec hgs) hexp' hty]
    cases henv : env.extern e.name with
    | none =>
      simp only [stepCall, hfe', hga, Res.ofOption, bind, Res.bind, checkTys, hty,
        beq_self_eq_true, Res.check, ite_true, pure, StepResult.ofRes, hsrc fn e hfe, henv]
      trivial
    | some h =>
      rw [← step_call env p _ rest rs fn args hb]
      rw [step_extcall hb hfe' hga hty (hsrc fn e hfe) henv]
      obtain ⟨h', henv', hrel⟩ := hEx fn e hfe h henv
      have hstep' := step_extcall (env := env') (p := p') (s := ⟨fr', [], m⟩) hb'
        (by rw [hR.func']; exact hfn) (holds_getMany hv') hty' (htgt fn _ hfn) henv'
      obtain ⟨hret, htrap⟩ := hrel gs rg hgs hrg vals vals' m hty hexp'
      cases hout : h vals m with
      | stuck msg => trivial
      | outOfFuel => trivial
      | trapped c =>
        simp only [htrap c hout] at hstep'
        exact ⟨1, by rw [runLoop_succ, hstep']⟩
      | returned rv m' =>
        by_cases hrt : rv.map (·.ty) ≠ AbiParam.tys e.sig.returns
        · have : (rv.map (·.ty) == AbiParam.tys e.sig.returns) = false := by simpa using hrt
          simp only [this]
          trivial
        have hrt : rv.map (·.ty) = AbiParam.tys e.sig.returns := by simpa using hrt
        obtain ⟨rv', hout', hexr⟩ := hret rv m' hout hrt
        have hrt' : rv'.map (·.ty) = AbiParam.tys s'.returns := by
          rw [hret', AbiParam.tys, ← expRel_tys (groups_spec hrg) hexr hrt]
        simp only [hout', hrt', beq_self_eq_true, ite_true] at hstep'
        simp only [hrt, beq_self_eq_true, ite_true, continueWith]
        cases hs : fr.regs.setMany rs rv with
        | none => trivial
        | some ρ1 =>
          obtain ⟨hbind, hcov, hlen⟩ := retsOk_bind hrets hexr
          obtain ⟨ρ1', hs1'⟩ := setMany_of_len fr'.regs hlen
          simp only [continueWith, hs1'] at hstep'
          refine ⟨rfl, hKeep e.name h henv vals m rv m' hout hM, _, ?_,
            TStep.of_step hstep'⟩
          have hsrcI : SrcInv C.f ρ1 := by
            refine srcInv_results hG.defs hB hst hR.src (vals := rv) ?_ (fun _ _ h => by
              rw [hst_eq] at h; cases h) (fun _ _ _ h => by rw [hst_eq] at h; cases h)
              (by rw [hst_eq]; exact hs)
            rw [hst_eq]
            simp only [Inst.resultTypes, sigOfF, hfe, Option.map_some, hrt, AbiParam.tys]
          refine frel_after hG hR (st := { results := rs, inst := .call fn args }) hb hcode hs ?_ ?_ hsrcI
          · exact fun v hv _ x hx => hbind (holds_setMany hnd hs) (holds_setMany hnd' hs1') hnd v hv x hx
          · intro w hw hni
            refine setMany_other hs1' fun hwr => ?_
            rcases hcov w hwr with hf | ⟨u, hu, hwu⟩
            · rw [hf] at hw; cases hw
            · exact hni u hu (res_lt hG hB hst (by rw [hst_eq]; exact hu)) hwu

/-- A branch of the source and its rewrite. -/
theorem sim_enter {C : Ctx} (hG : Good C) {env' : Env} {p' : Program} {fr fr' : Frame} {m : Mem}
    (hR : CRel C fr fr') (hM : MemBounded m) {bc bc' : BlockCall} (hbc : bcOk C bc bc' = true)
    (hlt : ∀ x ∈ bc.args, x < C.T0) {k : Frame → StepResult}
    (hk : ∀ fr1, k fr1 = .next ⟨fr1, [], m⟩)
    (htgt : ∀ fr1', enterBlock fr' bc' = .ok fr1' → TStep env' p' fr' m fr1' m) :
    SimOut C env' p' fr' m (StepResult.ofRes (enterBlock fr bc) k) := by
  cases he : enterBlock fr bc with
  | ok fr1 =>
    obtain ⟨fr1', he', hR1⟩ := enter_sim hG hR hbc hlt he
    simp only [StepResult.ofRes_ok, hk]
    exact ⟨rfl, hM, fr1', hR1, htgt fr1' he'⟩
  | trap c => exact absurd he (enterBlock_not_trap _ _ _)
  | stuck msg => trivial

/-- **Terminators.** -/
theorem sim_term {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program} {fr fr' : Frame}
    {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) (hb : fr.body = [])
    (hnt : ∀ fn args et, fr.term ≠ .tryCall fn args et)
    (hnti : ∀ c args et, fr.term ≠ .tryCallIndirect c args et) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨B, hB, -, hterm⟩ := hR.blk
  have hcode := hR.code
  rw [hb] at hcode
  simp only [codeOk] at hcode
  have hlt : ∀ x ∈ termOps fr.term, x < C.T0 := fun x hx => term_ops_lt hG hB (hterm ▸ hx)
  rw [step_term env p _ hb]
  have hstep' : ∀ fr1' m1, fr'.body = [] → stepTerm env' p' ⟨fr', [], m⟩ fr'.term = .next ⟨fr1', [], m1⟩ →
      TStep env' p' fr' m fr1' m1 := fun fr1' m1 hb' h =>
    TStep.of_step (by rw [step_term env' p' _ hb']; exact h)
  cases ht : fr.term <;> cases ht' : fr'.term <;> rw [ht, ht'] at hcode <;>
    simp only [termOk, Bool.false_eq_true] at hcode
  case tryCall.tryCall fn args et _ _ _ => exact absurd ht (hnt fn args et)
  case tryCallIndirect.tryCallIndirect c args et _ _ _ => exact absurd ht (hnti c args et)
  case jump.jump bc bc' =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hcode
    obtain ⟨hts, hbc⟩ := hcode
    simp only [stepTerm]
    refine sim_enter hG hR.toCRel hM hbc (fun x hx => hlt x (by rw [ht]; exact hx))
      (fun _ => rfl) fun fr1' he' => hstep' fr1' m hts (by simp [stepTerm, ht', he'])
  case trap.trap c c' =>
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hcode
    obtain ⟨hts, rfl⟩ := hcode
    exact ⟨1, by rw [runLoop_succ, step_term env' p' _ hts, ht']; rfl⟩
  case brif.brif c t e c' t' e' =>
    simp only [Bool.and_eq_true] at hcode
    obtain ⟨⟨hbt, hbe⟩, hcc⟩ := hcode
    have hltt : ∀ x ∈ t.args, x < C.T0 := fun x hx => hlt x (by rw [ht]; simp [termOps, hx])
    have hlte : ∀ x ∈ e.args, x < C.T0 := fun x hx => hlt x (by rw [ht]; simp [termOps, hx])
    have hc0 : c < C.T0 := hlt c (by rw [ht]; simp [termOps])
    simp only [stepTerm]
    cases hcv : fr.regs c with
    | none => simp only [Frame.get, hcv, Res.ofOption, StepResult.ofRes_stuck]; trivial
    | some cv =>
      have hget : fr.get c = .ok cv := by simp [Frame.get, hcv, Res.ofOption]
      rw [hget, StepResult.ofRes_ok]
      split at hcc
      · rename_i lo hi hp
        simp only [Bool.and_eq_true] at hcc
        obtain ⟨hf, hseg⟩ := hcc
        obtain ⟨l, h, rfl, hl, hh⟩ := pairVal hR.vrel hc0 hp hcv
        obtain ⟨regs', hls, hcr, hkeep⟩ := cond_run (fr' := fr') (m := m) (rest := []) hseg hl hh
        have hfr : { fr' with body := fr'.body ++ [] } = fr' := by simp
        rw [hfr] at hls
        refine SimOut.pre (TStep.of_lstar (env := env') (p' := p') hls) (.inl rfl) ?_
        have hR' := CRel.fresh hG hR.toCRel (fun w hw => hkeep w hw (fresh_ne hf hw)) [] fr'.term
        have hget' : ({ fr' with regs := regs', body := [] } : Frame).get c' =
            .ok ⟨.i8, Sem.bool8 (Sem.truthy (h ++ l))⟩ := by simp [Frame.get, hcr, Res.ofOption]
        by_cases hbt' : @Sem.truthy Ty.i128.width (h ++ l) = true
        · have hbt'' : @Sem.truthy (64 + 64) (h ++ l) = true := hbt'
          rw [if_pos hbt']
          refine sim_enter hG hR' hM hbt hltt (fun _ => rfl) fun fr1' he' => TStep.of_step ?_
          rw [step_term env' p' _ rfl]
          simp only [ht'] at hget' he' ⊢
          simp only [stepTerm, hget', StepResult.ofRes_ok, truthy_bool8', hbt'', ite_true, he']
        · have hbt'' : ¬ @Sem.truthy (64 + 64) (h ++ l) = true := hbt'
          rw [if_neg hbt']
          refine sim_enter hG hR' hM hbe hlte (fun _ => rfl) fun fr1' he' => TStep.of_step ?_
          rw [step_term env' p' _ rfl]
          simp only [ht'] at hget' he' ⊢
          simp only [stepTerm, hget', StepResult.ofRes_ok, truthy_bool8', hbt'', ite_false,
            Bool.false_eq_true, he']
      · rename_i hp
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hcc
        obtain ⟨⟨hts, rfl⟩, hpc⟩ := hcc
        have hget' : fr'.get c' = .ok cv := by
          simp [Frame.get, hR.peq c' hc0 hp, hcv, Res.ofOption]
        by_cases hbt' : Sem.truthy cv.bits = true
        · simp only [hbt', ite_true]
          refine sim_enter hG hR.toCRel hM hbt hltt (fun _ => rfl) fun fr1' he' =>
            hstep' fr1' m hts ?_
          simp only [ht', stepTerm, hget', StepResult.ofRes_ok, hbt', ite_true, he']
        · simp only [hbt', ite_false, Bool.false_eq_true]
          refine sim_enter hG hR.toCRel hM hbe hlte (fun _ => rfl) fun fr1' he' =>
            hstep' fr1' m hts ?_
          simp only [ht', stepTerm, hget', StepResult.ofRes_ok, hbt', ite_false, Bool.false_eq_true,
            he']
  case brTable.brTable x d tbl x' d' tbl' =>
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq, List.all_eq_true] at hcode
    obtain ⟨⟨⟨⟨⟨hts, hxx⟩, hpx⟩, hbd⟩, hlen⟩, hz⟩ := hcode
    have hx0 : x < C.T0 := hlt x (by rw [ht]; simp [termOps])
    have hltb : ∀ i : Nat, ∀ y ∈ (tbl[i]?.getD d).args, y < C.T0 := by
      intro i y hy
      refine hlt y ?_
      rw [ht]
      simp only [termOps, List.mem_cons, List.mem_append, List.mem_flatMap]
      by_cases hi : i < tbl.length
      · rw [List.getElem?_eq_getElem hi] at hy
        first
          | exact .inr ⟨_, List.getElem_mem hi, hy⟩
          | exact .inr (.inr ⟨_, List.getElem_mem hi, hy⟩)
      · rw [List.getElem?_eq_none (by omega)] at hy
        first
          | exact .inl (.inr hy)
          | exact .inr (.inl hy)
    simp only [stepTerm]
    cases hxv : fr.regs x with
    | none => simp only [Frame.get, hxv, Res.ofOption, StepResult.ofRes_stuck]; trivial
    | some xv =>
      have hget : fr.get x = .ok xv := by simp [Frame.get, hxv, Res.ofOption]
      have hget' : fr'.get x' = .ok xv := by
        rw [hxx]; simp [Frame.get, hR.peq x hx0 (plain_iff.1 hpx), hxv, Res.ofOption]
      rw [hget, StepResult.ofRes_ok]
      refine sim_enter hG hR.toCRel hM (bcOk_table hbd hlen (fun a b hab => hz (a, b) hab) _)
        (hltb _) (fun _ => rfl) fun fr1' he' => hstep' fr1' m hts ?_
      simp only [ht', stepTerm, hget', StepResult.ofRes_ok, he']
  case ret.ret vs vs' =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hcode
    obtain ⟨hts, hcode⟩ := hcode
    split at hcode
    · rename_i rg hrg
      simp only [beq_iff_eq] at hcode
      have hltv : ∀ x ∈ vs, x < C.T0 := fun x hx => hlt x (by rw [ht]; simp [termOps, hx])
      simp only [stepTerm]
      cases hga : fr.getMany vs with
      | stuck msg => trivial
      | trap c => exact absurd hga (getMany_ne_trap fr vs c)
      | ok vals =>
        rw [StepResult.ofRes_ok]
        obtain ⟨vals', hv', hexp⟩ := expandArgs_holds hR.vrel hR.zero hcode hltv (getMany_holds hga)
        simp only [returnValues, checkTys]
        by_cases hty : vals.map (·.ty) ≠ AbiParam.tys fr.func.sig.returns
        · have : (vals.map (·.ty) == AbiParam.tys fr.func.sig.returns) = false := by simpa using hty
          simp only [this, Res.check, Bool.false_eq_true, ite_false, StepResult.ofRes_stuck]
          trivial
        have hty : vals.map (·.ty) = AbiParam.tys fr.func.sig.returns := by simpa using hty
        simp only [hty, beq_self_eq_true, Res.check, ite_true, StepResult.ofRes_ok]
        obtain ⟨gs0, rg0, -, hrg0, -, hret'⟩ := sigExp_spec hG.sig
        rw [hrg] at hrg0; cases hrg0
        have hty' : vals'.map (·.ty) = AbiParam.tys fr'.func.sig.returns := by
          rw [hR.func', hret', AbiParam.tys,
            ← expRel_tys (groups_spec hrg) hexp (by rw [← hR.func]; exact hty)]
        refine ⟨vals', by simp [Ctx.rg, hrg, hexp], 1, ?_⟩
        rw [runLoop_succ, step_term env' p' _ hts, ht']
        simp only [stepTerm, holds_getMany hv', StepResult.ofRes_ok, returnValues, checkTys, hty',
          beq_self_eq_true, Res.check, ite_true, hR.slots]
    · cases hcode

/-- **An indirect call of an extern** (`callInd`): source and target run the same statement on
the same values (every operand and result is plain), with the same call-site signature; the
callee address holds no function of either program (the source by `IndExt`, the target by
`EnvOk2.ind`), and the call site's signature resolves alike (`CallIndRel`). -/
theorem sim_callInd {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program}
    (hE : EnvOk2 env env' C p p')
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) {st : Stmt}
    {rest : List Stmt} (hb : fr.body = st :: rest) (hpl : planOf C st = some .callInd)
    {ts2 : List Stmt} (hb' : fr'.body = st :: ts2)
    (hdecl : ∀ sig callee args, st.inst = .callIndirect sig callee args →
      C.g.sigDecls.lookup sig = C.f.sigDecls.lookup sig)
    (hcode : codeOk C rest fr.term ts2 fr'.term = true) (hI : IndExt env p C.f ⟨fr, [], m⟩) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨sig, callee, args, d0, hi, hd0, h128, hplain⟩ := planOf_callInd hpl
  have hdecl := hdecl sig callee args hi
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  have hnd := results_nodup hG.defs hB hst
  have hlt : ∀ x ∈ callee :: args ++ st.results, x < C.T0 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ops_lt hG hB hst (by rw [hi]; exact hx)
    · exact res_lt hG hB hst hx
  have hpeq : ∀ x ∈ callee :: args ++ st.results, fr'.regs x = fr.regs x := fun x hx =>
    hR.peq x (hlt x hx) (plain_iff.1 (hplain x hx))
  have hstep : step env p ⟨fr, [], m⟩ =
      stepCallIndirect env p ⟨fr, [], m⟩ rest st.results sig callee args := by
    simp [step, hb, hi]
  have hstep' : step env' p' ⟨fr', [], m⟩ =
      stepCallIndirect env' p' ⟨fr', [], m⟩ ts2 st.results sig callee args := by
    simp [step, hb', hi]
  rw [hstep]
  have hfd : fr'.func.sigDecls.lookup sig = fr.func.sigDecls.lookup sig := by
    rw [hR.func, hR.func']; exact hdecl
  have hget : fr'.get callee = fr.get callee := by
    simp only [Frame.get, hpeq callee (List.mem_cons_self ..)]
  have hgm : fr'.getMany args = fr.getMany args :=
    getMany_congr fun x hx => hpeq x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
  cases hd : fr.func.sigDecls.lookup sig with
  | none => simp [stepCallIndirect, hd, Res.ofOption, bind, Res.bind, StepResult.ofRes, SimOut]
  | some d =>
  cases hc : fr.get callee with
  | trap c => exact absurd hc (get_ne_trap fr callee c)
  | stuck msg => simp [stepCallIndirect, hd, hc, Res.ofOption, bind, Res.bind, StepResult.ofRes, SimOut]
  | ok cv =>
  cases hcv : cv.as? .i64 with
  | none => simp [stepCallIndirect, hd, hc, hcv, Res.ofOption, bind, Res.bind, StepResult.ofRes, SimOut]
  | some b =>
  cases hv : fr.getMany args with
  | trap c => exact absurd hv (getMany_ne_trap fr args c)
  | stuck msg =>
    simp [stepCallIndirect, hd, hc, hcv, hv, Res.ofOption, bind, Res.bind, StepResult.ofRes, SimOut]
  | ok vals =>
  have hnf := hI.1 st rest sig callee args cv hb hi ⟨B, hB, hst⟩ hc
  rw [← as_i64_toNat hcv] at hnf
  have hsrc : stepCallIndirect env p ⟨fr, [], m⟩ rest st.results sig callee args =
      StepResult.ofRes (callExternAt env p m d b.toNat vals) fun (rv, mem') =>
        continueWith ⟨fr, [], m⟩ rest st.results rv mem' := by
    simp [stepCallIndirect, hd, hc, hcv, hv, Res.ofOption, bind, Res.bind, StepResult.ofRes,
      find_none_of hnf]
  rw [hsrc]
  have hname : IndSite C.f sig := .inl ⟨B, hB, st, hst, callee, args, hi⟩
  obtain ⟨hfn, hrelI⟩ := hE.ind ⟨sig, hname⟩
  have hdf : C.f.sigDecls.lookup sig = some d := by rw [← hR.func]; exact hd
  have hrel := (hrelI sig d hname hdf).plain (by rw [hd0] at hdf; cases hdf; exact h128)
  have hnf' : ∀ g ∈ p'.funcs, m.symbols g.name ≠ some b.toNat := by
    intro g hg
    have : g.name ∈ p'.funcs.map (·.name) := List.mem_map_of_mem hg
    rw [hfn] at this
    obtain ⟨g0, hg0, he⟩ := List.mem_map.mp this
    rw [← he]
    exact hnf g0 hg0
  have htgt : stepCallIndirect env' p' ⟨fr', [], m⟩ ts2 st.results sig callee args =
      StepResult.ofRes (callExternAt env' p' m d b.toNat vals) fun (rv, mem') =>
        continueWith ⟨fr', [], m⟩ ts2 st.results rv mem' := by
    simp [stepCallIndirect, hfd, hd, hget, hc, hcv, hgm, hv, Res.ofOption, bind, Res.bind,
      StepResult.ofRes]
    rw [List.find?_eq_none.mpr ?_]
    intro g hg
    simpa using hnf' g hg
  cases hx : callExternAt env p m d b.toNat vals with
  | stuck msg => trivial
  | trap c =>
    refine ⟨1, ?_⟩
    rw [runLoop_succ, hstep', htgt, (hrel m b.toNat vals).2 c hx]
    rfl
  | ok r =>
  obtain ⟨rv, mem'⟩ := r
  obtain ⟨name, g, hg, hout, hrt⟩ := callExternAt_ok hx
  simp only [StepResult.ofRes_ok, continueWith]
  cases hs : fr.regs.setMany st.results rv with
  | none => trivial
  | some ρ1 =>
    obtain ⟨ρ1', hs'⟩ := setMany_of_len fr'.regs (setMany_len hs)
    have hstep2 : step env' p' ⟨fr', [], m⟩ = .next ⟨{ fr' with regs := ρ1', body := ts2 }, [], mem'⟩ := by
      rw [hstep', htgt, (hrel m b.toNat vals).1 _ hx]
      simp only [StepResult.ofRes_ok, continueWith, hs']
    refine ⟨rfl, hE.keep name g hg vals m rv mem' hout hM,
      { fr' with regs := ρ1', body := ts2 }, ?_, TStep.of_step hstep2⟩
    have hsrcI : SrcInv C.f ρ1 := by
      refine srcInv_results hG.defs hB hst hR.src (vals := rv) ?_ (fun _ _ h => by
        rw [hi] at h; cases h) (fun _ _ _ h => by rw [hi] at h; cases h) hs
      rw [hi]
      simp only [Inst.resultTypes, declOfF, ← hR.func, hd, Option.map_some, hrt, AbiParam.tys]
    refine frel_after hG hR hb hcode hs ?_ ?_ hsrcI
    · intro v hv _ x hx
      have hpv := plain_iff.1 (hplain v (List.mem_append_right _ hv))
      obtain ⟨i, hi', hvi⟩ := setMany_mem hs hnd hv
      rw [RelV.plain hpv, setMany_get hs' hnd hi', ← hvi, hx]
    · intro w _ hni
      refine setMany_other hs' fun hw => ?_
      have hpw := plain_iff.1 (hplain w (List.mem_append_right _ hw))
      exact hni w hw (res_lt hG hB hst hw) (by simp [img, hpw])

/-- What the target does for a source step, possibly after one more source step: the call of a
`try_call` leaves the source at its jump to the normal-return successor, where the frames are
not related (`FRel` is about positions in blocks of `f`); its next step (the jump) is. -/
def SimStep (C : Ctx) (env env' : Env) (p p' : Program) (fr' : Frame) (m : Mem)
    (r : StepResult) : Prop :=
  SimOut C env' p' fr' m r ∨
    ∃ s1, r = .next s1 ∧ s1.callers = [] ∧ MemBounded s1.mem ∧
      ∃ fr1', TStep env' p' fr' m fr1' s1.mem ∧ SimOut C env' p' fr1' s1.mem (step env p s1)

/-- **A `try_call`** (two source steps: the call, then the jump to the normal-return successor):
the target's `try_call` calls the extern with the expanded arguments (`ExtLegal`), its results
at fresh values; after the jumps, the frames are related again. -/
theorem sim_try {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program}
    (hE : EnvOk2 env env' C p p')
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m) (hb : fr.body = [])
    {fn : FnRef} {args : List ValueId} {et : ExnTable} (ht : fr.term = .tryCall fn args et) :
    SimStep C env env' p p' fr' m (step env p ⟨fr, [], m⟩) := by
  obtain ⟨B0, hB0, -, hterm⟩ := hR.blk
  have hlt : ∀ x ∈ args ++ et.vals, x < C.T0 := fun x hx =>
    term_ops_lt hG hB0 (by rw [← hterm, ht]; exact hx)
  have hcode := hR.code
  rw [hb, ht] at hcode
  simp only [codeOk] at hcode
  cases ht' : fr'.term
  all_goals first | (rw [ht'] at hcode; simp [termOk] at hcode; done) | skip
  rename_i fn' args' et'
  rw [ht'] at hcode
  obtain ⟨hts, hfnn, hsig, hblk, hne, hT0f, hT0g, hzg, hcg, e, d', B, s', gs, rg, he, hd', hB,
    hs', hgs, hrg, hfn', htyp, htyr, hexp, hexpT⟩ := termOk_tryCall hcode
  rw [hfnn] at ht'
  obtain ⟨gs0, rg0, hgs0, hrg0, hpar', hret'⟩ := sigExp_spec hs'
  rw [hgs] at hgs0; cases hgs0
  rw [hrg] at hrg0; cases hrg0
  have hfe : fr.func.extern? fn = some e := by rw [hR.func]; exact he
  rw [step_term env p _ hb, ht]
  simp only [stepTerm]
  cases hd : fr.func.sigDecls.lookup et.sig with
  | none => exact .inl (by simp [SimOut, stepTryCall, hfe, hd, Res.ofOption, bind, Res.bind])
  | some d =>
  cases hck : (AbiParam.tys d.params == AbiParam.tys e.sig.params &&
      AbiParam.tys d.returns == AbiParam.tys e.sig.returns) with
  | false =>
    have hckP : ¬(AbiParam.tys d.params = AbiParam.tys e.sig.params ∧
        AbiParam.tys d.returns = AbiParam.tys e.sig.returns) := by simpa using hck
    exact .inl (by simp [SimOut, stepTryCall, hfe, hd, Res.ofOption, bind, Res.bind, Res.check, hckP])
  | true =>
  have hckP : AbiParam.tys d.params = AbiParam.tys e.sig.params ∧
      AbiParam.tys d.returns = AbiParam.tys e.sig.returns := by simpa using hck
  cases hbc : tryNormal et fr.func.freshValue with
  | trap c => exact absurd hbc (tryNormal_ne_trap _ _ c)
  | stuck msg =>
    exact .inl (by simp [SimOut, stepTryCall, hfe, hd, Res.ofOption, bind, Res.bind, Res.check, hckP, hbc])
  | ok bc =>
  rw [stepTryCall_eq hfe hd hck hbc]
  have hbcE := tryNormal_eq hbc
  -- the source call
  have hfeJ : ({ fr with body := [], term := .jump bc } : Frame).func.extern? fn = some e := hfe
  cases hga : fr.getMany args with
  | trap c => exact absurd hga (getMany_ne_trap fr args c)
  | stuck msg =>
    have hgaJ : ({ fr with body := [], term := .jump bc } : Frame).getMany args = .stuck msg :=
      (getMany_congr (fr := fr) (fr' := { fr with body := [], term := .jump bc }) fun _ _ => rfl).trans hga
    exact .inl (by simp [SimOut, stepCall, hfeJ, hgaJ, Res.ofOption, bind, Res.bind])
  | ok vals =>
  have hgaJ : ({ fr with body := [], term := .jump bc } : Frame).getMany args = .ok vals :=
    (getMany_congr (fr := fr) (fr' := { fr with body := [], term := .jump bc }) fun _ _ => rfl).trans hga
  obtain ⟨vals', hv', hexp'⟩ := expandArgs_holds hR.vrel hR.zero hexp
    (fun x hx => hlt x (List.mem_append_left _ hx)) (getMany_holds hga)
  by_cases hty : vals.map (·.ty) ≠ AbiParam.tys e.sig.params
  · exact .inl (by simp [SimOut, stepCall, hfeJ, hgaJ, Res.ofOption, bind, Res.bind, checkTys, hty,
      Res.check])
  have hty : vals.map (·.ty) = AbiParam.tys e.sig.params := by simpa using hty
  have hty' : vals'.map (·.ty) = AbiParam.tys s'.params := by
    rw [hpar', AbiParam.tys, ← expRel_tys (groups_spec hgs) hexp' hty]
  cases henv : env.extern e.name with
  | none =>
    exact .inl (by simp [SimOut, stepCall, hfeJ, hgaJ, Res.ofOption, bind, Res.bind, checkTys, hty,
      Res.check, hE.src fn e he, henv])
  | some h =>
  rw [stepCall_ext (s := ⟨{ fr with body := [], term := .jump bc }, [], m⟩) hfeJ hgaJ hty
    (hE.src fn e he) henv]
  -- the target's `try_call`
  have hfe2 : fr'.func.extern? fn = some { e with sig := s' } := by rw [hR.func']; exact hfn'
  have hd2 : fr'.func.sigDecls.lookup et'.sig = some d' := by rw [hR.func', hsig]; exact hd'
  have hck2 : (AbiParam.tys d'.params == AbiParam.tys ({ e with sig := s' } : ExtFunc).sig.params &&
      AbiParam.tys d'.returns == AbiParam.tys ({ e with sig := s' } : ExtFunc).sig.returns) = true := by
    simp [htyp, htyr]
  have hnoexn := expandTry_noExn hexpT
  have hbc2 := tryNormal_of_noExn (base := fr'.func.freshValue) hnoexn
  generalize hbc'e : (⟨et'.normal.block, et'.normal.args.map (argId fr'.func.freshValue)⟩ :
    BlockCall) = bc' at hbc2
  obtain ⟨h', henv', hrel⟩ := hE.ext fn e he h henv
  have htstep := stepTryCall_eq (env := env') (p := p') (s := ⟨fr', [], m⟩) (args := args')
    hfe2 hd2 hck2 hbc2
  have hgaJ2 : ({ fr' with body := [], term := .jump bc' } : Frame).getMany args' = .ok vals' :=
    (getMany_congr (fr := fr') (fr' := { fr' with body := [], term := .jump bc' }) fun _ _ => rfl).trans
      (holds_getMany hv')
  have hstep2 := stepCall_ext (env := env') (p := p')
    (s := ⟨{ fr' with body := [], term := .jump bc' }, [], m⟩)
    (results := (List.range s'.returns.length).map (fr'.func.freshValue + ·)) (rest := [])
    (args := args') (fn := fn) hfe2 hgaJ2 hty' (hE.tgt fn _ hfn') henv'
  obtain ⟨hret, htrap⟩ := hrel gs rg hgs hrg vals vals' m hty hexp'
  have hT1 : ∀ r, step env' p' ⟨fr', [], m⟩ = r ↔ stepCall env' p'
      ⟨{ fr' with body := [], term := .jump bc' }, [], m⟩ []
      ((List.range s'.returns.length).map (fr'.func.freshValue + ·)) fn args' = r := by
    intro r
    rw [step_term env' p' _ hts, ht']
    simp only [stepTerm]
    rw [htstep]
  cases hout : h vals m with
  | stuck msg => exact .inl trivial
  | outOfFuel => exact .inl trivial
  | trapped c =>
    refine .inl ⟨1, ?_⟩
    rw [runLoop_succ, (hT1 (.trapped c)).2 (by rw [hstep2]; simp only [htrap c hout])]
  | returned rv m' =>
  by_cases hrt : rv.map (·.ty) ≠ AbiParam.tys e.sig.returns
  · have : (rv.map (·.ty) == AbiParam.tys e.sig.returns) = false := by simpa using hrt
    exact .inl (by simp only [this]; trivial)
  have hrt : rv.map (·.ty) = AbiParam.tys e.sig.returns := by simpa using hrt
  obtain ⟨rv', hout', hexr⟩ := hret rv m' hout hrt
  have hrt' : rv'.map (·.ty) = AbiParam.tys s'.returns := by
    rw [hret', AbiParam.tys, ← expRel_tys (groups_spec hrg) hexr hrt]
  simp only [hrt, beq_self_eq_true, ite_true, continueWith]
  have hnrv : rv.length = e.sig.returns.length := by
    have := congrArg List.length hrt; simpa [AbiParam.tys] using this
  have hnrv' : rv'.length = s'.returns.length := by
    have := congrArg List.length hrt'; simpa [AbiParam.tys] using this
  cases hs : fr.regs.setMany ((List.range e.sig.returns.length).map (fr.func.freshValue + ·)) rv with
  | none => exact .inl trivial
  | some ρ1 =>
  obtain ⟨ρ1', hs1'⟩ := setMany_of_len fr'.regs
    (rs := (List.range s'.returns.length).map (fr'.func.freshValue + ·)) (vs := rv')
    (by simp [hnrv'])
  have hfv : fr.func.freshValue = C.f.freshValue := by rw [hR.func]
  have hfv' : fr'.func.freshValue = C.g.freshValue := by rw [hR.func']
  have hstepT : step env' p' ⟨fr', [], m⟩ =
      .next ⟨{ fr' with regs := ρ1', body := [], term := .jump bc' }, [], m'⟩ := by
    refine (hT1 _).2 ?_
    rw [hstep2]
    simp only [hout', hrt', beq_self_eq_true, ite_true, continueWith, hs1']
  have hM1 : MemBounded m' := hE.keep e.name h henv vals m rv m' hout hM
  refine .inr ⟨_, rfl, rfl, hM1, _, TStep.of_step hstepT, ?_⟩
  -- the jumps
  have hCR := crel_bind hG hR.toCRel hs hs1'
    (fun v hv => by have := (mem_range_map hv).1; rw [hfv] at this; omega)
    (fun w hw => fresh_of_ge (base' := C.g.freshValue) hT0g hzg hcg
      (by have := (mem_range_map hw).1; rw [hfv'] at this; exact this))
    [] (.jump bc) [] (.jump bc')
  simp only
  rw [step_term env p _ rfl]
  simp only [stepTerm]
  cases hen : enterBlock { fr with regs := ρ1, body := [], term := .jump bc } bc with
  | trap c => exact absurd hen (enterBlock_not_trap _ _ c)
  | stuck msg => trivial
  | ok fr2 =>
  simp only [StepResult.ofRes_ok]
  obtain ⟨fr2', hen', hR2⟩ := enter_sim_vals hG hCR (bc' := bc') (by rw [← hbc'e, hbcE]; exact hblk)
    (by rw [hbcE]; exact hne) (fun B1 vals1 hB1 hv1 => by
      rw [← hbc'e]
      rw [hbcE] at hB1 hv1
      rw [hB] at hB1
      cases hB1
      refine expandTry_holds hR.vrel hexr (base := fr.func.freshValue)
        (base' := fr'.func.freshValue)
        (fun v hv => setMany_other hs fun hm => by
          have := (mem_range_map hm).1; rw [hfv] at this
          exact absurd hv (Nat.not_lt.mpr (Nat.le_trans hT0f this)))
        (fun i hi => setMany_get hs (range_map_nodup _ _) (getElem?_range_map (hnrv ▸ hi)))
        (fun a ha => setMany_other hs1' fun hm => absurd ha (Nat.not_lt.mpr (mem_range_map hm).1))
        (fun j hj => setMany_get hs1' (range_map_nodup _ _) (getElem?_range_map (hnrv' ▸ hj)))
        (fun v a b hp => by
          obtain ⟨ha, hb⟩ := mem_comps hp
          rw [hfv']; exact ⟨hcg a ha, hcg b hb⟩)
        (by rw [hfv']; exact hT0g) hexpT
        (fun v hv => hlt v (List.mem_append_right _ (List.mem_append_left _ (val_mem_vals hv)))) hv1) hen
  refine ⟨rfl, hM1, fr2', hR2, TStep.of_step ?_⟩
  rw [step_term env' p' _ rfl]
  simp only [stepTerm, hen', StepResult.ofRes_ok]

/-- A `call_indirect` statement of `f` is an indirect call site (`IndSite`). -/
theorem indSite_of_stmt {f : Function} (h : ∃ B ∈ f.blocks, ∃ st ∈ B.body, ∃ sig callee args,
    st.inst = .callIndirect sig callee args) : ∃ sig, IndSite f sig := by
  obtain ⟨B, hB, st, hst, sig, callee, args, hi⟩ := h
  exact ⟨sig, .inl ⟨B, hB, st, hst, callee, args, hi⟩⟩

/-- On the domain of `check` (`indOldB`), a frame of `f` does not end in a `try_call_indirect`. -/
theorem frel_not_tryInd {C : Ctx} {fr fr' : Frame} (hR : FRel C fr fr')
    (hold : indOldB C.f = true) : ∀ c args et, fr.term ≠ .tryCallIndirect c args et := by
  intro c args et ht
  obtain ⟨B, hB, -, hterm⟩ := hR.blk
  simp only [indOldB, List.all_eq_true, Bool.and_eq_true] at hold
  have := (hold B hB).2
  rw [← hterm, ht] at this
  simp at this

/-- On the domain of `check` (`indOldB`), no statement of `f` has the plan `callInd128`. -/
theorem frel_not_callInd128 {C : Ctx} {fr fr' : Frame} (hR : FRel C fr fr')
    (hold : indOldB C.f = true) {st : Stmt} {rest : List Stmt} (hb : fr.body = st :: rest)
    {sig : Nat} {d : Signature} {callee : ValueId} {args : List ValueId}
    {rg : List (List SlotEl)} {rs : List ValueId}
    (hpl : planOf C st = some (.callInd128 sig d callee args rg rs)) : False := by
  obtain ⟨args0, -, hi, -, hd, h128, -⟩ := planOf_callInd128 hpl
  obtain ⟨B, hB, hst⟩ := frel_stmt hR hb
  exact indOldB_not_ind128 hold ⟨sig, d, .inl ⟨B, hB, st, hst, callee, args0, hi⟩, hd, h128⟩

/-- **One source step**, matched by the target (on the domain of `check`, `indOldB`). -/
theorem step_sim {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program}
    (hE : EnvOk2 env env' C p p') (hold : indOldB C.f = true)
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m)
    (hT : MemTrapFree env p ⟨fr, [], m⟩) (hI : IndExt env p C.f ⟨fr, [], m⟩) :
    SimStep C env env' p p' fr' m (step env p ⟨fr, [], m⟩) := by
  cases hb : fr.body with
  | nil =>
    by_cases htc : ∃ fn args et, fr.term = .tryCall fn args et
    · obtain ⟨fn, args, et, ht⟩ := htc
      exact sim_try hG hE hR hM hb ht
    · exact .inl (sim_term hG hR hM hb (fun fn args et h => htc ⟨fn, args, et, h⟩)
        (frel_not_tryInd hR hold))
  | cons st rest =>
    refine .inl ?_
    have hcode0 := hR.code
    rw [hb] at hcode0
    obtain ⟨pl, hpl, hseg, hcode⟩ := code_cons hcode0
    have hbody := take_drop_eq (l := fr'.body) (n := pl.len) rfl
    have hT' : ∀ c, step env p ⟨fr, [], m⟩ = .trapped c →
        (∀ op t fl a o, st.inst ≠ .load op t fl a o) ∧
          (∀ op t fl x a o, st.inst ≠ .store op t fl x a o) := fun c h => hT c st rest h hb
    cases pl with
    | same =>
      rw [segOk_same hseg] at hbody
      exact sim_same hG hR hM hb hpl hbody hcode
    | pure pat ins outs =>
      exact sim_pure hG hR hM hb hpl hseg hbody hcode
    | load rl rh q fl off =>
      obtain ⟨hs, hrl, hrq⟩ := segOk_load hseg
      rw [hs] at hbody
      exact sim_load hG hR hM hb hpl hbody hrl hrq hcode fun c h => by
        obtain ⟨hi, -, -, -⟩ := planOf_load hpl
        exact (hT' c h).1 _ _ _ _ _ hi
    | store xl xh q fl off =>
      rw [segOk_store hseg] at hbody
      exact sim_store hG hR hM hb hpl hbody hcode fun c h => by
        obtain ⟨⟨x, hi, -⟩, -, -, -⟩ := planOf_store hpl
        exact (hT' c h).2 _ _ _ _ _ _ hi
    | div op xl xh yl yh rl rh =>
      obtain ⟨fn, hs, hrl, hfn⟩ := segOk_div hseg
      rw [hs] at hbody
      exact sim_div hG hE.helper hE.tgt hR hM hb hpl hbody hrl hfn hcode
    | call fn e args rg rs =>
      obtain ⟨rs', hs, hrets, hnd', s', hs', hfn⟩ := segOk_call hseg
      rw [hs] at hbody
      exact sim_call hG hE.ext hE.keep hE.src hE.tgt hR hM hb hpl hbody hrets hnd' hs' hfn hcode
    | trap lo hi nz code =>
      obtain ⟨segA, c, hs, hc, hpo⟩ := segOk_trap hseg
      rw [hs, List.append_assoc] at hbody
      exact sim_trap hG hR hM hb hpl hpo hc hbody hcode
    | callInd =>
      obtain ⟨hs, hdecl⟩ := segOk_callInd hseg
      rw [hs] at hbody
      exact sim_callInd hG hE hR hM hb hpl hbody hdecl hcode hI
    | callInd128 sig d callee args rg rs => exact (frel_not_callInd128 hR hold hb hpl).elim

/-- **One source step that is not a `try_call`'s call**, matched by the target (`step_sim`
without its second case; on the domain of `check`, `indOldB`). -/
theorem step_sim_out {C : Ctx} (hG : Good C) {env env' : Env} {p p' : Program}
    (hE : EnvOk2 env env' C p p') (hold : indOldB C.f = true)
    {fr fr' : Frame} {m : Mem} (hR : FRel C fr fr') (hM : MemBounded m)
    (hT : MemTrapFree env p ⟨fr, [], m⟩) (hI : IndExt env p C.f ⟨fr, [], m⟩)
    (hnt : fr.body = [] → ∀ fn args et, fr.term ≠ .tryCall fn args et) :
    SimOut C env' p' fr' m (step env p ⟨fr, [], m⟩) := by
  cases hb : fr.body with
  | nil =>
    exact sim_term hG hR hM hb (fun fn args et h => hnt hb fn args et h) (frel_not_tryInd hR hold)
  | cons st rest =>
    have hcode0 := hR.code
    rw [hb] at hcode0
    obtain ⟨pl, hpl, hseg, hcode⟩ := code_cons hcode0
    have hbody := take_drop_eq (l := fr'.body) (n := pl.len) rfl
    have hT' : ∀ c, step env p ⟨fr, [], m⟩ = .trapped c →
        (∀ op t fl a o, st.inst ≠ .load op t fl a o) ∧
          (∀ op t fl x a o, st.inst ≠ .store op t fl x a o) := fun c h => hT c st rest h hb
    cases pl with
    | same =>
      rw [segOk_same hseg] at hbody
      exact sim_same hG hR hM hb hpl hbody hcode
    | pure pat ins outs =>
      exact sim_pure hG hR hM hb hpl hseg hbody hcode
    | load rl rh q fl off =>
      obtain ⟨hs, hrl, hrq⟩ := segOk_load hseg
      rw [hs] at hbody
      exact sim_load hG hR hM hb hpl hbody hrl hrq hcode fun c h => by
        obtain ⟨hi, -, -, -⟩ := planOf_load hpl
        exact (hT' c h).1 _ _ _ _ _ hi
    | store xl xh q fl off =>
      rw [segOk_store hseg] at hbody
      exact sim_store hG hR hM hb hpl hbody hcode fun c h => by
        obtain ⟨⟨x, hi, -⟩, -, -, -⟩ := planOf_store hpl
        exact (hT' c h).2 _ _ _ _ _ _ hi
    | div op xl xh yl yh rl rh =>
      obtain ⟨fn, hs, hrl, hfn⟩ := segOk_div hseg
      rw [hs] at hbody
      exact sim_div hG hE.helper hE.tgt hR hM hb hpl hbody hrl hfn hcode
    | call fn e args rg rs =>
      obtain ⟨rs', hs, hrets, hnd', s', hs', hfn⟩ := segOk_call hseg
      rw [hs] at hbody
      exact sim_call hG hE.ext hE.keep hE.src hE.tgt hR hM hb hpl hbody hrets hnd' hs' hfn hcode
    | trap lo hi nz code =>
      obtain ⟨segA, c, hs, hc, hpo⟩ := segOk_trap hseg
      rw [hs, List.append_assoc] at hbody
      exact sim_trap hG hR hM hb hpl hpo hc hbody hcode
    | callInd =>
      obtain ⟨hs, hdecl⟩ := segOk_callInd hseg
      rw [hs] at hbody
      exact sim_callInd hG hE hR hM hb hpl hbody hdecl hcode hI
    | callInd128 sig d callee args rg rs => exact (frel_not_callInd128 hR hold hb hpl).elim

end Opt.Legal.S
