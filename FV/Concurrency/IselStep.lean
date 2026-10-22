import FV.Concurrency.SegRun
import FV.Backend.Proof.LowerSim
import FV.Concurrency.SegShape

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

/-- **`n` steps of `r`, each from a configuration satisfying `P`.** -/
inductive StarNP {α : Type} (r : α → α → Prop) (P : α → Prop) : Nat → α → α → Prop
  | refl (a : α) : StarNP r P 0 a a
  | step {n : Nat} {a b c : α} : P a → r a b → StarNP r P n b c → StarNP r P (n + 1) a c

/-- **`n` steps of `r`.** -/
abbrev StarN {α : Type} (r : α → α → Prop) : Nat → α → α → Prop := StarNP r fun _ => True

section starN
variable {α : Type} {r : α → α → Prop} {P Q : α → Prop}

theorem StarNP.star : ∀ {n : Nat} {a b : α}, StarNP r P n a b → Star r a b
  | _, _, _, .refl _ => .refl _
  | _, _, _, .step _ h t => .step h t.star

theorem StarNP.mono (hPQ : ∀ a, P a → Q a) : ∀ {n : Nat} {a b : α}, StarNP r P n a b →
    StarNP r Q n a b
  | _, _, _, .refl _ => .refl _
  | _, _, _, .step hp h t => .step (hPQ _ hp) h (t.mono hPQ)

theorem StarNP.toN {n : Nat} {a b : α} (h : StarNP r P n a b) : StarN r n a b :=
  h.mono fun _ _ => trivial

theorem StarNP.trans : ∀ {n m : Nat} {a b c : α}, StarNP r P n a b → StarNP r P m b c →
    StarNP r P (n + m) a c
  | _, _, _, _, _, .refl _, h => by simpa using h
  | _, _, _, _, _, .step hp h t, h' => by
    rw [Nat.add_right_comm]; exact .step hp h (t.trans h')

/-- **Deterministic relations reach one configuration in `n` steps.** -/
theorem StarNP.det (hdet : ∀ a b c, r a b → r a c → b = c) :
    ∀ {n : Nat} {a b c : α}, StarNP r P n a b → StarNP r Q n a c → b = c
  | _, _, _, _, .refl _, .refl _ => rfl
  | _, _, _, _, .step _ h1 t1, .step _ h2 t2 => by
    rw [hdet _ _ _ h1 h2] at t1
    exact StarNP.det hdet t1 t2

/-- Split a counted run. -/
theorem StarNP.split : ∀ (n m : Nat) {a c : α}, StarNP r P (n + m) a c →
    ∃ b, StarNP r P n a b ∧ StarNP r P m b c
  | 0, _, _, _, h => ⟨_, .refl _, by simpa using h⟩
  | n + 1, m, _, _, h => by
    rw [Nat.add_right_comm] at h
    cases h with
    | step hp h1 t =>
      obtain ⟨b, t1, t2⟩ := StarNP.split n m t
      exact ⟨b, .step hp h1 t1, t2⟩

end starN

/-- The instruction at the configuration has no memory kind. -/
def NoMemAt {W : Type} (vc : VCode) (c : VConf CV W) : Prop :=
  ∀ b k ρ w, c = .run ⟨b, k, ρ, w⟩ → ∀ vb i, vc.blocks[b]? = some vb → vb.insts[k]? = some i →
    Code.akinds i = []

/-- The configuration is at instruction `k0 + i` of block `b`, for some `i < len`. -/
def InSeg {V W : Type} (b k0 len : Nat) (c : VConf V W) : Prop :=
  ∃ i < len, ∃ ρ w, c = .run ⟨b, k0 + i, ρ, w⟩

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
  StarNP.det (r := VStep vc sem) (fun _ _ _ h1 h2 => vstep_det h1 h2) h1 h2

theorem InSeg.succ {V W : Type} {b k0 len : Nat} {c : VConf V W} (h : InSeg b (k0 + 1) len c) :
    InSeg b k0 (len + 1) c := by
  obtain ⟨i, hi, ρ, w, rfl⟩ := h
  exact ⟨i + 1, by omega, ρ, w, by rw [Nat.add_assoc, Nat.add_comm 1 i]⟩

theorem InSeg.zero {V W : Type} (b k0 len : Nat) (hl : 0 < len) (ρ : Nat → V) (w : W) :
    InSeg b k0 len (VConf.run ⟨b, k0, ρ, w⟩) := ⟨0, hl, ρ, w, rfl⟩

/-- **A segment that falls through is `ms.length` steps**, within the segment
(`seqRun_fall_star`, counted). -/
theorem seqRun_fall_starN {V W : Type} {vc : VCode} {sem : ISem V W} {b : Nat} {vb : VBlock}
    (hvb : vc.blocks[b]? = some vb) :
    ∀ {ms : List MInst} {k0 : Nat} {ρ : Nat → V} {w : W} {ρ' : Nat → V} {w' : W},
    SegAt vb k0 ms → k0 + ms.length < vb.insts.size →
    seqRun sem ms ρ w = some (.fall ρ' w') →
    StarNP (VStep vc sem) (InSeg b k0 ms.length) ms.length (.run ⟨b, k0, ρ, w⟩)
      (.run ⟨b, k0 + ms.length, ρ', w'⟩) := by
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
    have := (ih hseg.tail (by simp at hlt ⊢; omega) hrest).mono fun _ h => InSeg.succ h
    simp only [List.length_cons] at this ⊢
    rw [show k0 + (ms.length + 1) = k0 + 1 + ms.length by omega]
    exact .step (InSeg.zero _ _ _ (by omega) _ _) hstep this

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
      exact ⟨StarNP.step trivial h1 ih, ihm.trans h2⟩
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
  refine StarNP.trans hpre'.1 ?_
  rw [Nat.add_comm 1]
  refine .step trivial ?_ hpost'.1
  cases c1 with
  | run s =>
    obtain ⟨b, k, ρ, w⟩ := s
    obtain ⟨-, -, -, -, -, -, -, hst⟩ := vtstep_foot h2
    have hm : (confW c0).mem = w.mem := hpre'.2.symm
    simpa [confMem, patch, hm] using hst
  | ret v w => cases h2
  | halt w => cases h2

/-- A segment that stops at instruction `k`: `k` counted steps to it, within the segment
(`seqRun_stop_star`). -/
theorem seqRun_stop_starN {V W : Type} {vc : VCode} {sem : ISem V W} {b : Nat} {vb : VBlock}
    (hvb : vc.blocks[b]? = some vb) :
    ∀ {ms : List MInst} {k0 : Nat} {ρ : Nat → V} {w : W} {k : Nat} {i : MInst}
      {ops : Array Operand} {ρ₁ : Nat → V} {w₁ : W} {outs : List V} {w₂ : W} {ctl : Ctl},
    SegAt vb k0 ms → seqRun sem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl) →
    StarNP (VStep vc sem) (InSeg b k0 ms.length) k (.run ⟨b, k0, ρ, w⟩)
        (.run ⟨b, k0 + k, ρ₁, w₁⟩) ∧ k < ms.length ∧
      vb.insts[k0 + k]? = some i ∧ i.operands = .ok ops ∧
      sem i (vuses ops ρ₁) w₁ = some (outs, w₂, ctl) ∧
      outs.length = (ops.toList.filter Operand.isDef).length ∧ ctl ≠ .next := by
  intro ms
  induction ms with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ h; simp [seqRun] at h
  | cons i₀ ms ih =>
    intro k0 ρ w k i ops ρ₁ w₁ outs w₂ ctl hseg h
    rcases seqRun_cons_stop h with
      ⟨rfl, rfl, hops, rfl, rfl, hsem, hlen, hne⟩ | ⟨k', ops₀, outs₀, w₃, rfl, hops₀, hsem₀, hlen₀, hrest⟩
    · exact ⟨by simpa using StarNP.refl _, by simp, by simpa using hseg.head, hops, hsem, hlen, hne⟩
    · obtain ⟨hstar, hk, hi, hops, hsem, hlen, hne⟩ := ih hseg.tail hrest
      have hlt : k0 + 1 < vb.insts.size := by
        have := (Array.getElem?_eq_some_iff.mp hi).1; omega
      have hstep : VStep vc sem (.run ⟨b, k0, ρ, w⟩)
          (.run ⟨b, k0 + 1, vdefUpd ops₀ outs₀ ρ, w₃⟩) :=
        VStep.step hvb hseg.head hops₀ hsem₀ hlen₀ (VNext.next hlt)
      refine ⟨?_, by simp; omega, by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hi, hops,
        hsem, hlen, hne⟩
      rw [show k0 + (k' + 1) = k0 + 1 + k' by omega]
      exact .step (InSeg.zero _ _ _ (by simp) _ _) hstep (hstar.mono fun _ h => InSeg.succ h)

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
    ∃ (B : Clif.Block) (j : Nat) (ρ' : Nat → CV) (w' : W), f.blocks[b]? = some B ∧
      B.body[j]? = some stm ∧ k = pos f R bl b j ∧
      StarNP (VStep vc sem) (InSeg b k (seg f R bl b j).length) (seg f R bl b j).length
        (.run ⟨b, k, ρ, w⟩) (.run ⟨b, k + (seg f R bl b j).length, ρ', w'⟩) ∧
      Match f ctx R gn bl A MR slots s' ⟨b, k + (seg f R bl b j).length, ρ', w'⟩ := by
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
      refine ⟨B, j, ρ', w', hB, hstm, rfl, by rw [hseg]; exact hstar, ?_⟩
      rw [hseg]
      refine ⟨hcall, hfunc, hslots, by simpa [fr', restrict, hslots] using hmr,
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

/-- **The terminator step with its endpoint** (`LowerSim.term_step`, branches): the terminator's
code (and an edge block's `jump`) runs from the matched configuration to the successor's first
statement in a counted number of steps, matching the CLIF state after the branch. -/
theorem term_matchN (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false)
    (htk : ∀ L, bl[b]? = some L → ∀ i ∈ L.tst'.emitted.toList, Code.akinds i = [])
    {s' : Clif.State} (hs : Clif.step env p s = .next s') :
    ∃ (n : Nat) (vs' : VState CV W),
      StarNP (VStep vc sem) (NoMemAt vc) n (.run ⟨b, k, ρ, w⟩) (.run vs') ∧ 0 < n ∧
      Match f ctx R gn bl A MR slots s' vs' := by
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
  have hargsR : ∀ y ∈ termArgs B.term, fr'.regs y = s.frame.regs y :=
    fun y hy => restrict_regs_of_mem (hargsT y hy)
  have hne : dests B.term ≠ [] := by
    intro hd
    rw [hstep] at hs
    cases hT : B.term with
    | ret xs => rw [hT] at hs; exact absurd hs ((stepTerm_ret (env := env) (p := p) (s := s)
        (xs := xs) hcall).1 s')
    | trap c => rw [hT] at hs; simp [Clif.stepTerm] at hs
    | returnCall fn args => exact absurd hT (H.noTail B (List.mem_of_getElem? hB) fn args)
    | tryCall _ _ _ => rw [hT] at hBnt; cases hBnt
    | tryCallIndirect _ _ _ => rw [hT] at hBnt; cases hBnt
    | jump bc => rw [hT] at hd; simp [dests] at hd
    | brif c t e => rw [hT] at hd; simp [dests] at hd
    | brTable x d tbl => rw [hT] at hd; simp [dests] at hd
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
  obtain ⟨hstar, -, hi, hops, hsem, hlen, -⟩ := seqRun_stop_starN hvb hsegat hsr'
  obtain ⟨hmk, -⟩ := seqRun_stop_mem hsr
  have hP : ∀ c : VConf CV W, InSeg b (pos f R bl b B.body.length)
      (L.tst'.emitted.toList.map (·.mapRegs R)).length c → NoMemAt vc c := by
    rintro c ⟨i', hi', ρx, wx, rfl⟩ b2 k2 ρ2 w2 he vb2 ins hb2 hins
    cases he
    rw [hvb] at hb2; cases hb2
    rw [hsegat i' hi'] at hins; cases hins
    rw [List.getElem_map, SegShape.akinds_mapRegs]
    exact htk L hL _ (List.getElem_mem _)
  have hPi : NoMemAt vc (.run ⟨b, pos f R bl b B.body.length + k', ρ₁',
      w₁⟩ : VConf CV W) := by
    intro b2 k2 ρ2 w2 he vb2 ins hb2 hins
    cases he
    rw [hvb] at hb2; cases hb2
    rw [hi] at hins; cases hins
    rw [SegShape.akinds_mapRegs]
    exact htk L hL _ (List.mem_of_getElem? hmk)
  have hstar := hstar.mono hP
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
  split at hsucc
  · rename_i bc0 hT
    rw [hT] at hbargs hbc
    obtain ⟨tl, htl, htgs⟩ := hsucc
    have hj0 : j' = 0 ∧ bc = bc0 := by
      cases j' with
      | zero => simp [dests] at hbc; exact ⟨rfl, hbc.symm⟩
      | succ n => simp [dests] at hbc
    obtain ⟨rfl, rfl⟩ := hj0
    obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match_br H hB hcall hfunc hslots hheld hcons hbcmem
      htl hent hρ₂ hmr'
    obtain ⟨Lt, hLt⟩ := H.blow hTB
    obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
    simp only [hne0, ite_false] at hpt
    have henv := edgeEnv_eq (V := CV) hvb hvbt (xs := bc.args.map gn) (ps := TB.params.map (·.1))
      (by rw [hbargs]; simp [List.map_map, Function.comp_def, H.shape.ren.vreg])
      (by rw [hpt]; simp [List.map_map, Function.comp_def]) (by simp; omega)
      (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
    exact ⟨_, _, hstar.trans (StarNP.step hPi (VStep.step hvb hi hops hsem hlen
      (VNext.goto hK (by rw [hsucc_eq, htgs]; rfl) henv)) (.refl _)), by omega, hM⟩
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
    obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match_br H hB hcall hfunc hslots hheld hcons hbcmem
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
      exact ⟨_, _, hstar.trans (StarNP.step hPi (VStep.step hvb hi hops hsem hlen
        (VNext.goto hK (by rw [hsucc_eq, List.getElem?_eq_getElem hjlt, hnil hargs0]) henv))
        (.refl _)), by omega, hM⟩
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
      exact ⟨_, _, hstar.trans (StarNP.step hPi hstep1 (StarNP.step (by
        intro b2 k2 ρ2 w2 he vb2 ins hb2 hins
        cases he
        rw [heb] at hb2; cases hb2
        rw [hebi] at hins; cases hins
        rfl) hstep2 (.refl _))), by omega, hM⟩

end

end Concurrency.IselStep
