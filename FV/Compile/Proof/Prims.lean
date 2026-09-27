import FV.Compile.Proof.Step
import FV.Compile.Proof.Env

/-!
# Simulation of the generator's control-flow primitives

`selectVals` (a `brif` into a join block with parameters) and `errIf` (a `brif` to the
error exit `block1(tag)`), plus the error-exit target predicate `ErrAt`.
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile
open Clif (Val Regs ValueId Frame State Mem Program Function Block Inst Terminator Outcome enterBlock
  StepResult Signature ExtFunc FnRef BlockCall)

/-- The error exit `block1(tag : i8)` of `c.F`, with its parameter id at least `c.n0`. -/
def Ctx.EB (c : Ctx) (blk : Block) (tid : ValueId) : Prop :=
  c.F.block? errBlock = some blk ∧ blk.params = [(tid, .i8)] ∧ c.n0 ≤ tid

/-- The machine has just entered the error exit with tag `e` (registers below `n` as in
`r0`), with the invariant for some heap. -/
def ErrAt (c : Ctx) (e : DSL.Err) (r0 : Regs) (n : Nat) (s : State) : Prop :=
  ∃ blk tid r, c.EB blk tid ∧ s.frame.regs = r.set tid ⟨.i8, e.tag8⟩ ∧ Agree r0 r n ∧
    s.frame.body = blk.body ∧ s.frame.term = blk.term ∧ ∃ H, c.Inv H s

theorem Ctx.Inv.frame {c : Ctx} {H : Heap} {s : State} (hI : c.Inv H s) {fr' : Frame}
    (hf : fr'.func = s.frame.func) (hs : fr'.slots = s.frame.slots) {n : Nat}
    (ha : Agree s.frame.regs fr'.regs n) (hn : c.n0 ≤ n) : c.Inv H { s with frame := fr' } :=
  ⟨hf.trans hI.func, hs.trans hI.slots, hI.callers, hI.mem, hI.slotsOK, hI.bufOK,
    hI.regs.agree ha hn⟩

theorem ErrAt.agree {c : Ctx} {e : DSL.Err} {r0 r1 : Regs} {n m : Nat} {s : State}
    (h : ErrAt c e r1 m s) (ha : Agree r0 r1 n) (hnm : n ≤ m) : ErrAt c e r0 n s := by
  obtain ⟨blk, tid, r, heb, hr, har, hb, ht, H, hI⟩ := h
  exact ⟨blk, tid, r, heb, hr, ha.trans har hnm, hb, ht, H, hI⟩

section
variable {E : Clif.Env} {P : Program}

theorem reach_selectVals {F : Function} {cg : CG} {s : State} {tys : List Clif.Ty}
    {cv : ValueId} {x y : List ValueId} {c : Val} {Vx Vy : List Val}
    {Q : State → Prop} {X : Outcome → Prop}
    (hG : Good F ((selectVals tys cv x y).run cg).2) (hAt : At F cg s.frame)
    (hc : s.frame.regs cv = some c) (hx : RegsHas s.frame.regs x Vx)
    (hy : RegsHas s.frame.regs y Vy) (htx : Vx.map (·.ty) = tys) (hty : Vy.map (·.ty) = tys)
    (k : ∀ fr' : Frame, At F ((selectVals tys cv x y).run cg).2 fr' →
      RegsHas fr'.regs ((selectVals tys cv x y).run cg).1
        (if Clif.Sem.truthy c.bits then Vx else Vy) →
      Agree s.frame.regs fr'.regs cg.nextVal → fr'.func = s.frame.func →
      fr'.slots = s.frame.slots → Reach E P Q X { s with frame := fr' }) :
    Reach E P Q X s := by
  have hrun : (selectVals tys cv x y).run cg =
      (List.range' cg.nextVal tys.length,
        { cg with nextBlock := cg.nextBlock + 1, nextVal := cg.nextVal + tys.length,
                  done := curBlock cg (.brif cv ⟨cg.nextBlock, x⟩ ⟨cg.nextBlock, y⟩) :: cg.done,
                  cur := cg.nextBlock, curParams := (List.range' cg.nextVal tys.length).zip tys,
                  curBody := [] }) := by
    simp only [selectVals, bind_run, newBlock_run, freshFor_run, terminate_run, switchTo_run,
      pure_run]
    rfl
  rw [hrun] at hG k
  obtain ⟨blk, hblk, hparams⟩ := Good.params hG
  have hL : Lk F
      { cg with nextBlock := cg.nextBlock + 1, nextVal := cg.nextVal + tys.length,
                done := curBlock cg (.brif cv ⟨cg.nextBlock, x⟩ ⟨cg.nextBlock, y⟩) :: cg.done,
                curBody := [] } := hG.1
  obtain ⟨hb, ht⟩ := At.term (cg := cg) (List.mem_cons_self) hL hAt
  have hps : (blk.params.map (·.1)) = List.range' cg.nextVal tys.length := by
    rw [hparams, List.map_fst_zip (by simp)]
  have hpt : (blk.params.map (·.2)) = tys := by rw [hparams, List.map_snd_zip (by simp)]
  have hnd : (blk.params.map (·.1)).Nodup := by rw [hps]; exact List.nodup_range'
  have hsel : ∀ (args : List ValueId) (V : List Val), RegsHas s.frame.regs args V →
      V.map (·.ty) = tys → ∃ fr', Clif.enterBlock s.frame ⟨cg.nextBlock, args⟩ = .ok fr' ∧
        At F
          { cg with nextBlock := cg.nextBlock + 1, nextVal := cg.nextVal + tys.length,
                    done := curBlock cg (.brif cv ⟨cg.nextBlock, x⟩ ⟨cg.nextBlock, y⟩) :: cg.done,
                    cur := cg.nextBlock, curParams := (List.range' cg.nextVal tys.length).zip tys,
                    curBody := [] } fr' ∧
        RegsHas fr'.regs (List.range' cg.nextVal tys.length) V ∧
        Agree s.frame.regs fr'.regs cg.nextVal ∧ fr'.func = s.frame.func ∧
        fr'.slots = s.frame.slots := by
    intro args V hV hVt
    have hb' : s.frame.func.block? cg.nextBlock = some blk := by rw [hAt.1]; exact hblk
    obtain ⟨regs', he, hr, ho⟩ := enterBlock_of hb' hV (by rw [hVt, hpt]) hnd
    refine ⟨_, he, At.enter hAt.1 hblk rfl rfl rfl, by rw [← hps]; exact hr, fun z hz => ho z ?_,
      rfl, rfl⟩
    rw [hps]; intro hm; have := (List.mem_range'_1.1 hm).1; omega
  by_cases htr : Clif.Sem.truthy c.bits = true
  · obtain ⟨fr', he, hA, hr, ha, hf, hs⟩ := hsel x Vx hx htx
    refine .next (step_brif hb ht hc (by rw [htr]; exact he)) ?_
    exact k fr' hA (by rw [htr]; exact hr) ha hf hs
  · obtain ⟨fr', he, hA, hr, ha, hf, hs⟩ := hsel y Vy hy hty
    refine .next (step_brif hb ht hc (by simp only [htr]; exact he)) ?_
    exact k fr' hA (by simp only [htr]; exact hr) ha hf hs

/-- Entering the error exit from a branch with the tag in `tv`. -/
theorem enter_err {c : Ctx} {blk : Block} {tid : ValueId} (heb : c.EB blk tid) {fr : Frame}
    (hf : fr.func = c.F) {tv : ValueId} {e : DSL.Err}
    (hv : fr.regs tv = some ⟨.i8, e.tag8⟩) :
    Clif.enterBlock fr ⟨errBlock, [tv]⟩ =
      .ok { fr with regs := fr.regs.set tid ⟨.i8, e.tag8⟩, body := blk.body, term := blk.term } := by
  have hb : fr.func.block? errBlock = some blk := by rw [hf]; exact heb.1
  have := enterBlock_ok (bc := ⟨errBlock, [tv]⟩) (vals := [⟨.i8, e.tag8⟩]) hb (RegsHas.single hv)
    (by rw [heb.2.1]; rfl) (regs' := fr.regs.set tid ⟨.i8, e.tag8⟩) (by rw [heb.2.1]; simp)
  exact this

theorem errIf_run (cv : ValueId) (tag : Nat) (cg : CG) :
    (errIf cv tag).run cg = ((),
      { cg with nextVal := cg.nextVal + 1, nextBlock := cg.nextBlock + 1,
                done := curBlock { cg with curBody := ⟨[cg.nextVal], .iconst .i8 (BitVec.ofNat 8 tag)⟩ ::
                    cg.curBody } (.brif cv ⟨errBlock, [cg.nextVal]⟩ ⟨cg.nextBlock, []⟩) :: cg.done,
                cur := cg.nextBlock, curParams := [], curBody := [] }) := rfl

theorem reach_errIf {c : Ctx} {blk : Block} {tid : ValueId} (heb : c.EB blk tid) {cg : CG}
    {s : State} {cv : ValueId} {b : Val} {e : DSL.Err} {Q : State → Prop} {X : Outcome → Prop}
    (hG : Good c.F ((errIf cv e.tag).run cg).2) (hAt : At c.F cg s.frame)
    (hc : s.frame.regs cv = some b) (hcv : cv < cg.nextVal)
    (kerr : Clif.Sem.truthy b.bits = true → ∀ fr' : Frame, fr'.regs =
        (s.frame.regs.set cg.nextVal ⟨.i8, e.tag8⟩).set tid ⟨.i8, e.tag8⟩ →
      fr'.body = blk.body → fr'.term = blk.term → fr'.func = s.frame.func →
      fr'.slots = s.frame.slots → Reach E P Q X { s with frame := fr' })
    (kok : Clif.Sem.truthy b.bits = false → ∀ fr' : Frame, At c.F ((errIf cv e.tag).run cg).2 fr' →
      fr'.regs = s.frame.regs.set cg.nextVal ⟨.i8, e.tag8⟩ → fr'.func = s.frame.func →
      fr'.slots = s.frame.slots → Reach E P Q X { s with frame := fr' }) :
    Reach E P Q X s := by
  have hG₁ : Good c.F ((iconstN .i8 e.tag).run cg).2 :=
    Bk.bind Bk.newBlock_gg (fun _ => Bk.bind (Bk.terminate_gl _) fun _ => Bk.switchTo_lg _ _)
      _ _ hG
  refine reach_iconst hG₁ hAt fun fr₁ hA₁ hr₁ hf₁ hs₁ => ?_
  rw [errIf_run] at hG kok
  have hL : Lk c.F
      { cg with nextVal := cg.nextVal + 1, nextBlock := cg.nextBlock + 1,
                done := curBlock { cg with curBody := ⟨[cg.nextVal], .iconst .i8 (BitVec.ofNat 8 e.tag)⟩ ::
                    cg.curBody } (.brif cv ⟨errBlock, [cg.nextVal]⟩ ⟨cg.nextBlock, []⟩) :: cg.done,
                curBody := [] } := hG.1
  obtain ⟨hb, ht⟩ := At.term (cg := ((iconstN .i8 e.tag).run cg).2) List.mem_cons_self hL hA₁
  have htv : fr₁.regs cg.nextVal = some ⟨.i8, e.tag8⟩ := by rw [hr₁]; simp; rfl
  have hc₁ : fr₁.regs cv = some b := by
    rw [hr₁, Regs.set_other _ _ (Nat.ne_of_lt hcv)]; exact hc
  by_cases htr : Clif.Sem.truthy b.bits = true
  · refine .next (step_brif (s := { s with frame := fr₁ })
      (fr' := { fr₁ with regs := fr₁.regs.set tid ⟨.i8, e.tag8⟩, body := blk.body, term := blk.term })
      hb ht hc₁ ?_) ?_
    · rw [htr]; exact enter_err heb (hf₁.trans hAt.1) htv
    · refine kerr htr _ ?_ rfl rfl hf₁ hs₁
      simp only [hr₁]; rfl
  · have htr' : Clif.Sem.truthy b.bits = false := by simpa using htr
    obtain ⟨bok, hbok, hpok⟩ := Good.params hG
    simp only at hbok hpok
    have he : Clif.enterBlock fr₁ ⟨cg.nextBlock, []⟩ =
        .ok { fr₁ with body := bok.body, term := bok.term } := by
      have := enterBlock_ok (fr := fr₁) (bc := ⟨cg.nextBlock, []⟩) (vals := [])
        (by rw [hf₁, hAt.1]; exact hbok) rfl (by rw [hpok]; rfl) (regs' := fr₁.regs)
        (by rw [hpok]; rfl)
      exact this
    refine .next (step_brif (s := { s with frame := fr₁ }) hb ht hc₁ (by rw [htr']; exact he)) ?_
    exact kok htr' _ (At.enter (hf₁.trans hAt.1) hbok rfl rfl rfl) hr₁ hf₁ hs₁

end

end Compile.Proof
