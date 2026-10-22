import FV.Concurrency.SegRun
import FV.Backend.Proof.LowerSim

/-!
# Counted runs and the statement step with its endpoint (T2h, #311, layer 2e)

The thread run of a statement's segment (`SegRun.vtrun_patch`) and the driver's simulation of the
statement (`LowerSim.stmt_step`) are both forward `VStep` runs from the same (patched)
configuration. `VStep` is deterministic (`vstep_det`), but `Star` forgets the number of steps,
and `stmt_step` hides which configuration on the run it matches: in a loop the run may pass the
segment's end more than once. So this file counts steps:

* `StarN r n`: `n` steps of `r`; deterministic relations reach one configuration in `n` steps
  (`StarN.det`); `seqRun_fall_starN`: a segment that falls through is `ms.length` steps;
* `vtrun_nil_starN`, **`vtrun_patchN`**: `SegRun.vtrun_nil_star`/`vtrun_patch` with the number of
  steps (the thread trace's length);
* **`stmt_matchN`**: `LowerSim.stmt_step`'s `next` case with the endpoint exposed: the renamed
  segment runs (`seqRun`) to the configuration after it, `seg.length` steps on, which matches the
  CLIF state after the statement. The proof is `stmt_step`'s (`FV/Backend/Proof/LowerSim.lean`),
  restated with the endpoint (that file's statement stays as it is).
-/

namespace Concurrency.IselStep

open Arm ArmThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread SegRun

/-! ## Counted runs -/

/-- **`n` steps of `r`.** -/
inductive StarN {α : Type} (r : α → α → Prop) : Nat → α → α → Prop
  | refl (a : α) : StarN r 0 a a
  | step {n : Nat} {a b c : α} : r a b → StarN r n b c → StarN r (n + 1) a c

section starN
variable {α : Type} {r : α → α → Prop}

theorem StarN.star : ∀ {n : Nat} {a b : α}, StarN r n a b → Star r a b
  | _, _, _, .refl _ => .refl _
  | _, _, _, .step h t => .step h t.star

theorem StarN.trans : ∀ {n m : Nat} {a b c : α}, StarN r n a b → StarN r m b c →
    StarN r (n + m) a c
  | _, _, _, _, _, .refl _, h => by simpa using h
  | _, _, _, _, _, .step h t, h' => by
    rw [Nat.add_right_comm]; exact .step h (t.trans h')

/-- **Deterministic relations reach one configuration in `n` steps.** -/
theorem StarN.det (hdet : ∀ a b c, r a b → r a c → b = c) :
    ∀ {n : Nat} {a b c : α}, StarN r n a b → StarN r n a c → b = c
  | _, _, _, _, .refl _, .refl _ => rfl
  | _, _, _, _, .step h1 t1, .step h2 t2 => by
    rw [hdet _ _ _ h1 h2] at t1
    exact StarN.det hdet t1 t2

/-- Split a counted run. -/
theorem StarN.split : ∀ (n m : Nat) {a c : α}, StarN r (n + m) a c →
    ∃ b, StarN r n a b ∧ StarN r m b c
  | 0, _, _, _, h => ⟨_, .refl _, by simpa using h⟩
  | n + 1, m, _, _, h => by
    rw [Nat.add_right_comm] at h
    cases h with
    | step h1 t =>
      obtain ⟨b, t1, t2⟩ := StarN.split n m t
      exact ⟨b, .step h1 t1, t2⟩

end starN

/-! ## Determinism of `VStep` -/

/-- **`VStep` is deterministic** (one instruction, one semantics result, one successor). -/
theorem vstep_det {V W : Type} {vc : VCode} {sem : ISem V W} {a b c : VConf V W}
    (h1 : VStep vc sem a b) (h2 : VStep vc sem a c) : b = c := by
  cases h1 with
  | step hvb hi hops hsem hlen hn =>
    cases h2 with
    | step hvb' hi' hops' hsem' hlen' hn' =>
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      rw [hsem] at hsem'; cases hsem'
      cases hn with
      | next => cases hn' with
        | next => rfl
      | goto h1 h2 h3 => cases hn' with
        | goto h1' h2' h3' =>
          rw [h2] at h2'; cases h2'
          rw [h3] at h3'; cases h3'
          rfl
      | ret => cases hn' with
        | ret => rfl
      | halt => cases hn' with
        | halt => rfl

/-- `VStep` runs of `n` steps reach one configuration. -/
theorem vstepN_det {V W : Type} {vc : VCode} {sem : ISem V W} {n : Nat} {a b c : VConf V W}
    (h1 : StarN (VStep vc sem) n a b) (h2 : StarN (VStep vc sem) n a c) : b = c :=
  StarN.det (r := VStep vc sem) (fun _ _ _ h1 h2 => vstep_det h1 h2) h1 h2

/-- **A segment that falls through is `ms.length` steps** (`seqRun_fall_star`, counted). -/
theorem seqRun_fall_starN {V W : Type} {vc : VCode} {sem : ISem V W} {b : Nat} {vb : VBlock}
    (hvb : vc.blocks[b]? = some vb) :
    ∀ {ms : List MInst} {k0 : Nat} {ρ : Nat → V} {w : W} {ρ' : Nat → V} {w' : W},
    SegAt vb k0 ms → k0 + ms.length < vb.insts.size →
    seqRun sem ms ρ w = some (.fall ρ' w') →
    StarN (VStep vc sem) ms.length (.run ⟨b, k0, ρ, w⟩) (.run ⟨b, k0 + ms.length, ρ', w'⟩) := by
  intro ms
  induction ms with
  | nil =>
    intro k0 ρ w ρ' w' _ _ h
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl _
  | cons i ms ih =>
    intro k0 ρ w ρ' w' hseg hlt h
    obtain ⟨ops, outs, w₁, hops, hsem, hlen, hrest⟩ := seqRun_cons_fall h
    have hstep : VStep vc sem (.run ⟨b, k0, ρ, w⟩) (.run ⟨b, k0 + 1, vdefUpd ops outs ρ, w₁⟩) :=
      VStep.step hvb hseg.head hops hsem hlen (VNext.next (by simp at hlt; omega))
    have := ih hseg.tail (by simp at hlt ⊢; omega) hrest
    simp only [List.length_cons] at this ⊢
    rw [show k0 + (ms.length + 1) = k0 + 1 + ms.length by omega, Nat.add_comm ms.length 1]
    rw [Nat.add_comm 1 ms.length]
    exact .step hstep this

/-! ## Thread runs as counted forward runs -/

/-- A thread run of steps without events from a running configuration, forward, counted
(`SegRun.vtrun_nil_star`). -/
theorem vtrun_nil_starN {vc : VCode} {sem : ISem CV ArmState}
    {ev : MInst → List CV → ArmState → List Ev} :
    ∀ {c c' : VConf CV ArmState} {tr : List (List Ev)}, VTRun vc sem ev c tr c' →
      (∀ e ∈ tr, e = []) → ∀ m, StarN (VStep vc sem) tr.length (confMem m c) (confMem m c') ∧
        ((confW c').mem = (confW c).mem)
  | _, _, _, .nil, _, m => ⟨.refl _, rfl⟩
  | _, _, _, .cons (c := c) hs hr, he, m => by
    have h0 := he _ List.mem_cons_self
    subst h0
    obtain ⟨ih, ihm⟩ := vtrun_nil_starN hr (fun e h => he e (List.mem_cons_of_mem _ h)) m
    cases c with
    | run s =>
      obtain ⟨b, k, ρ, w⟩ := s
      obtain ⟨vb, i, ops, hb, hi, hops, hf, hst⟩ := vtstep_foot hs
      rw [SegRun.patch_nil] at hf hst
      have hf' : ∀ vb' i' ops', vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' →
          i'.operands = .ok ops' →
          IFoot sem i' ((ops'.toList.filter Operand.isUse).map (ρ ·.vreg)) w [] := by
        intro vb' i' ops' hb' hi' hops'
        rw [hb] at hb'; cases hb'
        rw [hi] at hi'; cases hi'
        rw [hops] at hops'; cases hops'
        exact hf
      obtain ⟨h1, h2⟩ := vstep_setMem hf' hst m
      exact ⟨StarN.step h1 ih, ihm.trans h2⟩
    | ret v w => cases hs
    | halt w => cases hs

/-- **A segment run is a counted forward run from the patched start** (`SegRun.vtrun_patch`
with the number of steps). -/
theorem vtrun_patchN {vc : VCode} {sem : ISem CV ArmState}
    {ev : MInst → List CV → ArmState → List Ev} {c0 c1 c2 c3 : VConf CV ArmState}
    {pre post : List (List Ev)} {evs : List Ev}
    (h1 : VTRun vc sem ev c0 pre c1) (hpre : ∀ e ∈ pre, e = [])
    (h2 : VTStep vc sem ev c1 evs c2)
    (h3 : VTRun vc sem ev c2 post c3) (hpost : ∀ e ∈ post, e = []) :
    StarN (VStep vc sem) (pre.length + 1 + post.length) (patchC evs c0) c3 := by
  have hpre' := vtrun_nil_starN h1 hpre (applyR evs (confW c0).mem)
  have hpost' := vtrun_nil_starN h3 hpost (confW c2).mem
  have e3 : confMem (confW c2).mem c3 = c3 := by rw [← hpost'.2]; exact confMem_self c3
  rw [confMem_self, e3] at hpost'
  rw [Nat.add_assoc]
  refine StarN.trans hpre'.1 ?_
  rw [Nat.add_comm 1]
  refine .step ?_ hpost'.1
  cases c1 with
  | run s =>
    obtain ⟨b, k, ρ, w⟩ := s
    obtain ⟨-, -, -, -, -, -, -, hst⟩ := vtstep_foot h2
    have hm : (confW c0).mem = w.mem := hpre'.2.symm
    simpa [confMem, patch, hm] using hst
  | ret v w => cases h2
  | halt w => cases h2

/-! ## The statement step with its endpoint -/

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)}

/-- **The statement step with its endpoint** (`LowerSim.stmt_step`, `next` case): the segment of
statement `j` of block `b`, renamed, runs from the matched configuration to its end
(`seg.length` steps), which matches the CLIF state after the statement. -/
theorem stmt_matchN (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat)
    {s' : Clif.State} (hs : Clif.step env p s = .next s') :
    ∃ (seg : List MInst) (ρ' : Nat → CV) (w' : W),
      StarN (VStep vc sem) seg.length (.run ⟨b, k, ρ, w⟩) (.run ⟨b, k + seg.length, ρ', w'⟩) ∧
      Match f ctx R gn bl A MR slots s' ⟨b, k + seg.length, ρ', w'⟩ := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := hm
  simp only at hk hheld hcons hB hmem
  subst hk
  obtain ⟨hjlt, hstm, hrest⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, hstmts, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  obtain ⟨⟨info, hinfo, hclif, hres⟩, hemp, hst0, ⟨tr, hrun⟩, halias⟩ := hstmts j stm sl hstm hsl
  obtain ⟨ranges, hctx⟩ := H.shape.hctx
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  have hstmmem : stm ∈ B.body := List.mem_of_getElem? hstm
  have hok := H.insts ctx (L.start + j) info stm.inst sl.st sl.rss sl.st' tr
    H.shape.ctxInv ⟨B, hBmem, stm, hstmmem, rfl⟩ H.subE hinfo hclif (H.indSig B hBmem stm hstmmem) hemp
    (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0) hrun
  rw [hres] at hok
  obtain ⟨hargs, hresults, hnodup, hnext, hnoclob⟩ := H.cert.stmt b B L j stm sl hB hL hstm hsl
  let fr' := restrict s.frame (A b j)
  let ρ₀ : Nat → CV := fun n => ρ (gn n)
  have hvh : ValsHeld fr' ρ₀ := by
    intro x v hx
    have hxA : x ∈ A b j := restrict_regs_isSome (by rw [hx]; rfl)
    obtain ⟨v', hv', hh⟩ := hheld x hxA
    rw [restrict_regs_of_mem hxA, hv'] at hx
    cases hx
    exact hh
  have hrun' := hok.run fr' s.mem ρ₀ w (by simp [fr', restrict, hfunc, H.shape.ctxInv.func])
    hvh hcons (by simpa [fr', restrict, hslots] using hmem)
  have hio : instOutcome env p fr' s.mem stm.inst = instOutcome env p s.frame s.mem stm.inst :=
    instOutcome_congr (fr := s.frame) (fr' := fr') rfl rfl env p s.mem stm.inst
      fun x hx => restrict_regs_of_mem (hargs x hx)
  rw [hio] at hrun'
  have hstep := step_stmt env p s stm rest hbody
    (fun fn args hi e he => H.ext B hBmem stm hstmmem fn args hi e (by rw [← hfunc]; exact he))
    hind
  let D : Nat → Prop := fun n => sl.st.nextVreg ≤ n ∧ n < sl.st'.nextVreg
  have hD : ∀ d, D d → gn d = d := fun d hd => H.shape.temps d (by simp only [D] at hd; omega)
  have hdefs : ∀ m ∈ sl.st'.emitted.toList, ∀ d ∈ vdefs m, D d := hok.defs
  have hAg : Agree gn D ρ₀ ρ := fun _ _ => rfl
  have huses_of : UsesOk sl.st fr' sl.st'.emitted.toList →
      ∀ m ∈ sl.st'.emitted.toList, ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
    intro hU m hm u hu
    rcases hU m hm u hu with h | h
    · by_cases h' : u < sl.st'.nextVreg
      · exact .inl ⟨h, h'⟩
      · right
        rw [H.shape.temps u (by omega)]
        intro hd; exact h' hd.2
    · right; exact hnoclob u (restrict_regs_isSome h)
  have hren := seqRun_rename (sem := sem) (ρ₀ := ρ₀) (ρ := ρ) (w := w) H.shape.ren
    (H.dsem.rename R gn H.shape.ren) hD hdefs
  have hcodeseg := seg_at hcode htne hjlt
  rw [hstep] at hs
  cases hO : instOutcome env p s.frame s.mem stm.inst with
  | trap c => rw [hO] at hs; cases hs
  | stuck m => rw [hO] at hs; cases hs
  | ok r =>
    obtain ⟨vals, cm'⟩ := r
    rw [hO] at hs hrun'
    simp only [Clif.StepResult.ofRes, Clif.continueWith] at hs
    split at hs
    · rename_i regs' hset
      cases hs
      obtain ⟨hU, ρ₀', w', hsr, hrh, hmr⟩ := hrun'
      obtain ⟨ρ', hsr', hAg'⟩ := (hren (huses_of hU) hAg).1 hsr
      have hextra : extraOf stm.results sl.rss = [] := by
        rcases hrh with h0 | ⟨hl, hh⟩
        · rw [h0]; rfl
        · apply extraOf_nil
          intro k rs hk
          have : k < vals.length := by
            have := (List.getElem?_eq_some_iff.mp hk).1; omega
          obtain ⟨out, cls, he, -, -⟩ := hh k rs vals[k] hk (List.getElem?_eq_getElem this)
          exact ⟨out, cls, he⟩
      have hseg : seg f R bl b j = sl.st'.emitted.toList.map (·.mapRegs R) := by
        rw [seg_eq hB hL hstm hsl, hextra, List.append_nil]
      obtain ⟨hsegat, hlt⟩ := hcodeseg
      rw [hseg] at hsegat
      rw [pos_succ, hseg] at hlt
      have hstar := seqRun_fall_starN hvb hsegat (by simpa using hlt) hsr'
      refine ⟨_, ρ', w', hstar, hcall, hfunc, hslots, by simpa [fr', restrict, hslots] using hmr,
        B, j + 1, hB, hterm, hjlt, hrest, ?_, ?_, ?_⟩
      · simp [pos_succ, hseg]
      · -- held
        intro x hx
        rcases hnext x hx with hxA | hxr
        · have hxr : x ∉ stm.results := fun e => (hresults x e).1 hxA
          obtain ⟨v, hv, hh⟩ := hheld x hxA
          refine ⟨v, ?_, ?_⟩
          · show regs' x = some v
            rw [setMany_other hset hxr, hv]
          have hnd : ¬ D x := by
            have h4 : x < st0.nextVreg := H.cert.small b j x hxA
            intro hd
            have h3 : sl.st.nextVreg ≤ x := hd.1
            exact absurd (Nat.lt_of_lt_of_le h4 hst0) (Nat.not_lt.mpr h3)
          have h1 : ρ₀' x = ρ₀ x := seqRun_fall_frame (fun m hm hxm => hnd (hdefs m hm x hxm)) hsr
          have h2 := hAg' x (.inr (hnoclob x hxA))
          show VHolds v (ρ' (gn x))
          rw [← h2, h1]
          exact hh
        · obtain ⟨m, v, hxm, hvm, hrv⟩ := setMany_mem hset hnodup x hxr
          refine ⟨v, hrv, ?_⟩
          rcases hrh with h0 | ⟨hl, hh⟩
          · rw [h0] at hxr; cases hxr
          · have hml : m < sl.rss.length := by
              have := (List.getElem?_eq_some_iff.mp hvm).1; omega
            obtain ⟨out, cls, he, hout, hvo⟩ :=
              hh m sl.rss[m] v (List.getElem?_eq_getElem hml) hvm
            have hal := halias m x out cls hxm (by rw [List.getElem?_eq_getElem hml, he])
            have hcond : D out ∨ ¬ D (gn out) := by
              rcases hout with h | h
              · by_cases h' : out < sl.st'.nextVreg
                · exact .inl ⟨h, h'⟩
                · right; rw [H.shape.temps out (by omega)]; intro hd; exact h' hd.2
              · right; exact hnoclob out (restrict_regs_isSome h)
            show VHolds v (ρ' (gn x))
            rw [hal, ← hAg' out hcond]
            exact hvo
      · -- DFG consistency
        refine ⟨?_, ?_⟩
        rotate_left
        · -- the frame is typed
          intro x t v ht hv
          have hxA' : x ∈ A b (j + 1) := restrict_regs_isSome (by rw [hv]; rfl)
          have hv' : regs' x = some v := by
            have := restrict_regs_of_mem
              (fr := { s.frame with regs := regs', body := rest }) hxA'
            rw [this] at hv; exact hv
          by_cases hxr : x ∈ stm.results
          · obtain ⟨m, v', hxm, hvm, hrv⟩ := setMany_mem hset hnodup x hxr
            have hvv : v' = v := Option.some.inj (hrv.symm.trans hv')
            obtain ⟨tys, hrt, hrty, -⟩ := H.shape.ctxInv.resTys _ info stm.inst hinfo hclif
            have hvt := instOutcome_types hO (by rw [hfunc]; exact hrt)
            have htm : info.resTys[m]? = some (CTy.ofClif v'.ty) := by
              rw [hrty, ← hvt]
              simp [List.getElem?_map, hvm]
            have := H.cert.resTy _ info hinfo m x _ (by rw [hres]; exact hxm) htm
            rw [this] at ht
            rw [← hvv]; exact Option.some.inj ht
          · have hxA : x ∈ A b j := (hnext x hxA').resolve_right hxr
            refine hcons.2 x t v ht ?_
            rw [restrict_regs_of_mem hxA, ← setMany_other hset hxr]
            exact hv'
        intro x d info' cl v hd hinfo' hcl hp hv
        have hxA' : x ∈ A b (j + 1) := restrict_regs_isSome (by rw [hv]; rfl)
        have hv' : regs' x = some v := by
          have := restrict_regs_of_mem
            (fr := { s.frame with regs := regs', body := rest }) hxA'
          rw [this] at hv; exact hv
        have hcl_args := H.cert.closed b (j + 1) x d info' cl hxA' hd hinfo' hcl hp
        rcases hnext x hxA' with hxA | hxr
        · have hxr : x ∉ stm.results := fun e => (hresults x e).1 hxA
          have hvx : (restrict s.frame (A b j)).regs x = some v := by
            rw [restrict_regs_of_mem hxA, ← setMany_other hset hxr]; exact hv'
          obtain ⟨vals0, hev, hlk⟩ := hcons.1 x d info' cl v hd hinfo' hcl hp hvx
          refine ⟨vals0, fun cm => ?_, hlk⟩
          rw [← hev cm]
          refine evalInst_congr ?_ ?_ cm cl ?_
          · rfl
          · rfl
          intro y hy
          have hyA := H.cert.closed b j x d info' cl hxA hd hinfo' hcl hp y hy
          have hyr : y ∉ stm.results := fun e => (hresults y e).1 hyA
          rw [restrict_regs_of_mem (hcl_args y hy), restrict_regs_of_mem hyA]
          exact setMany_other hset hyr
        · have hd' := (hresults x hxr).2
          rw [hd] at hd'
          cases hd'
          rw [hinfo] at hinfo'
          cases hinfo'
          rw [hclif] at hcl
          cases hcl
          have hev : Clif.evalInst s.frame s.mem stm.inst = .ok (vals, cm') := by
            rw [← instOutcome_of_pure (env := env) (p := p) hp]; exact hO
          obtain ⟨-, hall⟩ := evalInst_pure hp hev
          obtain ⟨m, v', hxm, hvm, hrv⟩ := setMany_mem hset hnodup x hxr
          rw [hrv] at hv'
          cases hv'
          refine ⟨vals, fun cm => ?_, ?_⟩
          · rw [← hall cm]
            refine evalInst_congr ?_ ?_ cm _ ?_
            · rfl
            · rfl
            intro y hy
            have hyA := hargs y hy
            have hyr : y ∉ stm.results := fun e => (hresults y e).1 hyA
            rw [restrict_regs_of_mem (hcl_args y hy)]
            exact setMany_other hset hyr
          · rw [hres]
            exact lookup_zip_nodup hnodup (setMany_length hset) m x _ hxm hvm
    · cases hs

end

end Concurrency.IselStep
