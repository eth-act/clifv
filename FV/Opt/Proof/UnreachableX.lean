import FV.Opt.Proof.SimpSim
import FV.Opt.Proof.SimWin
import FV.Opt.Proof.Unreachable
import FV.Opt.OptimizeX

/-!
# `removeUnreachable` refines, `call_indirect` and `try_call` included

`Opt.removeUnreachable_sim` relates a frame of `f` to the same frame running
`g = removeUnreachable f`. With `try_call` the registers differ: each side binds a `try_call`'s
results at its own fresh value (`Clif.Function.freshValue`), and `g`'s may be lower. The frames
here (`UR`) agree on the registers of a set `S` of values: those below `g`'s fresh value, or all
when both fresh values are equal; every operand of `g` is in `S` when `g` reads only values below
its fresh value (`closedB`) or the fresh values are equal (`freshOkB`, the guard of
`optimizeX`). Frames step alike when they agree on the operands of their next statement or
terminator (`lstep_agree`).
-/

namespace Opt

open Clif

/-- `r'` agrees with `r` on the values of `S`. -/
def Agree (S : ValueId → Prop) (r r' : Regs) : Prop := ∀ v, S v → r' v = r v

theorem setMany_agree {S : ValueId → Prop} {r r' r1 : Regs} {xs : List ValueId} {vs : List Val}
    (h : Agree S r r') (h1 : r.setMany xs vs = some r1) :
    ∃ r1', r'.setMany xs vs = some r1' ∧ Agree S r1 r1' := by
  obtain ⟨r1', h1'⟩ := setMany_len (r := r') (setMany_spec h1).1
  refine ⟨r1', h1', fun v hv => ?_⟩
  by_cases hm : v ∈ xs
  · exact setMany_same h1' h1 v hm
  · rw [((setMany_spec h1').2 v).1 hm, ((setMany_spec h1).2 v).1 hm]; exact h v hv

/-- The operands of the next statement or of the terminator. -/
def headOps (fr : Frame) : List ValueId :=
  match fr.body with
  | st :: _ => operands st.inst
  | [] => termOperands fr.term

theorem enterBlock_agree {S : ValueId → Prop} {X Y : Frame} (hf : Y.func = X.func)
    (hr : Agree S X.regs Y.regs) {bc : BlockCall} (hbc : ∀ v ∈ bc.args, S v) {X1 : Frame}
    (h : enterBlock X bc = .ok X1) :
    ∃ Y1, enterBlock Y bc = .ok Y1 ∧ Y1.func = X1.func ∧ Y1.slots = Y.slots ∧
      X1.slots = X.slots ∧ Y1.body = X1.body ∧ Y1.term = X1.term ∧ Agree S X1.regs Y1.regs := by
  obtain ⟨b, args, regs, hb, hga, hty, hset, rfl⟩ := enterBlock_ok h
  obtain ⟨r', hset', hag⟩ := setMany_agree hr hset
  refine ⟨_, enterBlock_of (by rw [hf]; exact hb)
    (by rw [getMany_congr (fun v hv => hr v (hbc v hv))]; exact hga) hty hset',
    hf, rfl, rfl, rfl, rfl, hag⟩

/-- Frames that agree on the operands of their next statement or terminator step alike. -/
theorem lstep_agree {S : ValueId → Prop} {X Y : Frame} {m : Mem} (hf : Y.func = X.func)
    (hsl : Y.slots = X.slots) (hb : Y.body = X.body) (ht : Y.term = X.term)
    (hr : Agree S X.regs Y.regs) (hops : ∀ v ∈ headOps X, S v) :
    (∀ X1 m1, lstep X m = .next X1 m1 → ∃ Y1, lstep Y m = .next Y1 m1 ∧ Y1.func = X1.func ∧
      Y1.slots = X1.slots ∧ Y1.body = X1.body ∧ Y1.term = X1.term ∧ Agree S X1.regs Y1.regs) ∧
    (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) → lstep X m = r →
      lstep Y m = r) := by
  obtain ⟨func, regs, slots, body, term⟩ := X
  obtain ⟨func', regs', slots', body', term'⟩ := Y
  simp only at hf hsl hb ht
  have hf' := hf.symm; have hsl'' := hsl.symm; have hb'' := hb.symm; have ht'' := ht.symm
  subst hf' hsl'' hb'' ht''
  have hg : ∀ xs : List ValueId, (∀ v ∈ xs, S v) →
      Frame.getMany ⟨func, regs', slots, body, term⟩ xs =
        Frame.getMany ⟨func, regs, slots, body, term⟩ xs :=
    fun xs h => getMany_congr (fun v hv => hr v (h v hv))
  have ofEq : lstep ⟨func, regs', slots, body, term⟩ m = lstep ⟨func, regs, slots, body, term⟩ m →
      (∀ X1 m1, lstep ⟨func, regs, slots, body, term⟩ m = .next X1 m1 → ∃ Y1,
        lstep ⟨func, regs', slots, body, term⟩ m = .next Y1 m1 ∧ Y1.func = X1.func ∧
        Y1.slots = X1.slots ∧ Y1.body = X1.body ∧ Y1.term = X1.term ∧ Agree S X1.regs Y1.regs) ∧
      (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) →
        lstep ⟨func, regs, slots, body, term⟩ m = r → lstep ⟨func, regs', slots, body, term⟩ m = r) :=
    fun heq => ⟨fun X1 m1 h => ⟨X1, by rw [heq, h], rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
      fun r _ _ h => by rw [heq, h]⟩
  cases body with
  | cons st rest =>
    have hops' : ∀ v ∈ operands st.inst, S v := hops
    by_cases hc : ∃ fn args, st.inst = .call fn args
    · obtain ⟨fn, args, hi⟩ := hc
      apply ofEq
      rw [lstep_call rfl hi, lstep_call rfl hi]
      have : callArgs ⟨func, regs', slots, st :: rest, term⟩ fn args =
          callArgs ⟨func, regs, slots, st :: rest, term⟩ fn args := by
        unfold callArgs
        rw [hg args (by rw [hi] at hops'; exact hops')]
      rw [this]
    · have hnc : ∀ fn args, st.inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
      have hev : evalInst ⟨func, regs', slots, st :: rest, term⟩ m st.inst =
          evalInst ⟨func, regs, slots, st :: rest, term⟩ m st.inst :=
        evalInst_congr rfl rfl rfl (fun x hx => hr x (hops' x hx))
      rw [lstep_inst rfl hnc, lstep_inst rfl hnc, hev]
      refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
      · cases he : evalInst ⟨func, regs, slots, st :: rest, term⟩ m st.inst with
        | ok p =>
          obtain ⟨vals, m'⟩ := p
          rw [he] at h; simp only [LRes.ofRes] at h ⊢
          cases hs : regs.setMany st.results vals with
          | none => simp only [hs] at h; cases h
          | some regs1 =>
            simp only [hs] at h; cases h
            obtain ⟨r1', hs', hag⟩ := setMany_agree hr hs
            simp only [hs']
            exact ⟨_, rfl, rfl, rfl, rfl, rfl, hag⟩
        | trap c => rw [he] at h; cases h
        | stuck msg => rw [he] at h; cases h
      · cases he : evalInst ⟨func, regs, slots, st :: rest, term⟩ m st.inst with
        | ok p =>
          obtain ⟨vals, m'⟩ := p
          rw [he] at h; simp only [LRes.ofRes] at h
          split at h
          · exact absurd h.symm (hn _ _)
          · exact absurd h.symm (hs _)
        | trap c => simp only [he, LRes.ofRes] at h ⊢; exact h
        | stuck msg => rw [he] at h; exact absurd h.symm (hs _)
  | nil =>
    have hops' : ∀ v ∈ termOperands term, S v := hops
    have hnr : ∀ (k : Frame → LRes) (bc : BlockCall), (∀ fr, ∃ m', k fr = .next fr m') →
        ∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) →
        LRes.ofRes (enterBlock ⟨func, regs, slots, [], term⟩ bc) k ≠ r := by
      intro k bc hk r hn hs h
      cases he : enterBlock ⟨func, regs, slots, [], term⟩ bc with
      | ok X1 =>
        rw [he] at h; simp only [LRes.ofRes] at h
        obtain ⟨m', hm'⟩ := hk X1
        exact hn X1 m' (h ▸ hm')
      | trap c => exact enterBlock_not_trap _ _ _ he
      | stuck msg => rw [he] at h; exact hs msg h.symm
    have henter : ∀ bc : BlockCall, (∀ v ∈ bc.args, S v) → ∀ X1 m1,
        LRes.ofRes (enterBlock ⟨func, regs, slots, [], term⟩ bc) (fun fr' => .next fr' m) =
          .next X1 m1 → ∃ Y1,
        LRes.ofRes (enterBlock ⟨func, regs', slots, [], term⟩ bc) (fun fr' => .next fr' m) =
          .next Y1 m1 ∧ Y1.func = X1.func ∧
        Y1.slots = X1.slots ∧ Y1.body = X1.body ∧ Y1.term = X1.term ∧ Agree S X1.regs Y1.regs := by
      intro bc hbc X1 m1 h
      cases he : enterBlock ⟨func, regs, slots, [], term⟩ bc with
      | ok X2 =>
        rw [he] at h; simp only [LRes.ofRes, LRes.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨Y1, he', h1, h2, h3, h4, h5, h6⟩ :=
          enterBlock_agree (X := ⟨func, regs, slots, [], term⟩) (Y := ⟨func, regs', slots, [], term⟩)
            rfl hr hbc he
        refine ⟨Y1, by rw [he']; rfl, h1, h2.trans h3.symm, h4, h5, h6⟩
      | trap c => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h
    cases term with
    | jump d =>
      refine ⟨fun X1 m1 h => henter d (fun v hv => hops' v hv) X1 m1 h, fun r hn hs h => ?_⟩
      exact absurd h (hnr _ d (fun fr => ⟨m, rfl⟩) r hn hs)
    | brif c t e =>
      have hgc : Frame.get ⟨func, regs', slots, [], .brif c t e⟩ c =
          Frame.get ⟨func, regs, slots, [], .brif c t e⟩ c := by
        have := hr c (hops' c (by simp [termOperands]))
        simp only at this
        simp only [Frame.get, this]
      simp only [lstep, hgc]
      refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
      · cases hcv : Frame.get ⟨func, regs, slots, [], .brif c t e⟩ c with
        | ok cv =>
          simp only [hcv, LRes.ofRes] at h ⊢
          exact henter _ (fun v hv => hops' v (by
            simp only [termOperands, List.mem_cons, List.mem_append]
            split at hv <;> simp [hv])) X1 m1 h
        | trap _ => rw [hcv] at h; cases h
        | stuck _ => rw [hcv] at h; cases h
      · cases hcv : Frame.get ⟨func, regs, slots, [], .brif c t e⟩ c with
        | ok cv =>
          rw [hcv] at h; simp only [LRes.ofRes] at h
          exact absurd h (hnr _ _ (fun fr => ⟨m, rfl⟩) r hn hs)
        | trap _ => simp only [hcv, LRes.ofRes] at h ⊢; exact h
        | stuck msg => rw [hcv] at h; exact absurd h.symm (hs _)
    | brTable x d tbl =>
      have hgx : Frame.get ⟨func, regs', slots, [], .brTable x d tbl⟩ x =
          Frame.get ⟨func, regs, slots, [], .brTable x d tbl⟩ x := by
        have := hr x (hops' x (by simp [termOperands]))
        simp only at this
        simp only [Frame.get, this]
      simp only [lstep, hgx]
      refine ⟨fun X1 m1 h => ?_, fun r hn hs h => ?_⟩
      · cases hcv : Frame.get ⟨func, regs, slots, [], .brTable x d tbl⟩ x with
        | ok xv =>
          simp only [hcv, LRes.ofRes] at h ⊢
          refine henter _ (fun v hv => hops' v ?_) X1 m1 h
          simp only [termOperands, List.mem_cons, List.mem_append, List.mem_flatMap]
          cases hq : tbl[xv.toNat]? with
          | none => rw [hq] at hv; exact .inl (.inr hv)
          | some q => rw [hq] at hv; exact .inr ⟨q, List.mem_of_getElem? hq, hv⟩
        | trap _ => rw [hcv] at h; cases h
        | stuck _ => rw [hcv] at h; cases h
      · cases hcv : Frame.get ⟨func, regs, slots, [], .brTable x d tbl⟩ x with
        | ok xv =>
          rw [hcv] at h; simp only [LRes.ofRes] at h
          exact absurd h (hnr _ _ (fun fr => ⟨m, rfl⟩) r hn hs)
        | trap _ => simp only [hcv, LRes.ofRes] at h ⊢; exact h
        | stuck msg => rw [hcv] at h; exact absurd h.symm (hs _)
    | ret xs =>
      apply ofEq
      simp only [lstep, hg xs hops']
    | returnCall fn args =>
      apply ofEq
      have : tailArgs ⟨func, regs', slots, [], .returnCall fn args⟩ fn args =
          tailArgs ⟨func, regs, slots, [], .returnCall fn args⟩ fn args := by
        unfold tailArgs
        rw [hg args hops']
      simp only [lstep, this]
    | trap c => exact ofEq rfl
    | tryCall fn args et => exact ofEq rfl
    | tryCallIndirect c args et => exact ofEq rfl

/-! ## The relation -/

theorem no_window {a b v j : Nat} (he : a + j = v) (hv : v < b) (hle : b ≤ a) : False := by omega

/-- Every operand of `g` is below its fresh value. -/
theorem closedB_spec {g : Function} (h : closedB g = true) {b : Block} (hb : b ∈ g.blocks) :
    (∀ st ∈ b.body, ∀ v ∈ operands st.inst, v < g.freshValue) ∧
      ∀ v ∈ termOperands b.term, v < g.freshValue := by
  simp only [closedB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨fun st hst v hv => (h b hb).1 st hst v hv, fun v hv => (h b hb).2 v hv⟩

section
variable (f g : Function)

/-- The registers the relation keeps equal. -/
def US (v : ValueId) : Prop := v < g.freshValue ∨ g.freshValue = f.freshValue

/-- A frame of `f` and a frame of `g` at the same program point of a block of `g`, with the
registers of `US` equal. -/
def UR (fr fr' : Frame) : Prop :=
  fr.func = f ∧ fr'.func = g ∧ fr'.slots = fr.slots ∧ fr'.body = fr.body ∧ fr'.term = fr.term ∧
    (∃ b ∈ g.blocks, fr.body <:+ b.body ∧ fr.term = b.term) ∧ Agree (US f g) fr.regs fr'.regs

end

theorem freshValue_le_of_sub {f g : Function} (h : ∀ b ∈ g.blocks, b ∈ f.blocks) :
    g.freshValue ≤ f.freshValue := by
  unfold Function.freshValue
  generalize hgb : g.blocks = gbs
  have h' : ∀ b ∈ gbs, b ∈ f.blocks := hgb ▸ h
  -- the fold of `g` is bounded by every upper bound of the parameters and results it visits
  have key : ∀ (l : List Block), (∀ b ∈ l, b ∈ f.blocks) → ∀ m, m ≤ f.freshValue →
      l.foldl (fun m (b : Block) =>
        let m := b.params.foldl (fun m p => max m (p.1 + 1)) m
        b.body.foldl (fun m st => st.results.foldl (fun m r => max m (r + 1)) m) m) m ≤
        f.freshValue := by
    intro l hl
    induction l with
    | nil => intro m hm; exact hm
    | cons b l ih =>
      intro m hm
      simp only [List.foldl_cons]
      apply ih (fun b' hb' => hl b' (by simp [hb']))
      have hbf := lt_freshValue (hl b (by simp))
      have hp : ∀ (ps : List (ValueId × Ty)) m, (∀ p ∈ ps, p.1 < f.freshValue) → m ≤ f.freshValue →
          ps.foldl (fun m p => max m (p.1 + 1)) m ≤ f.freshValue := by
        intro ps
        induction ps with
        | nil => intro m _ hm; exact hm
        | cons p ps ihp =>
          intro m hps hm
          exact ihp _ (fun q hq => hps q (by simp [hq]))
            (Nat.max_le.2 ⟨hm, hps p (by simp)⟩)
      have hr : ∀ (rs : List ValueId) m, (∀ r ∈ rs, r < f.freshValue) → m ≤ f.freshValue →
          rs.foldl (fun m r => max m (r + 1)) m ≤ f.freshValue := by
        intro rs
        induction rs with
        | nil => intro m _ hm; exact hm
        | cons r rs ihr =>
          intro m hrs hm
          exact ihr _ (fun q hq => hrs q (by simp [hq])) (Nat.max_le.2 ⟨hm, hrs r (by simp)⟩)
      have hs : ∀ (sts : List Stmt) m, (∀ st ∈ sts, ∀ r ∈ st.results, r < f.freshValue) →
          m ≤ f.freshValue →
          sts.foldl (fun m st => st.results.foldl (fun m r => max m (r + 1)) m) m ≤ f.freshValue := by
        intro sts
        induction sts with
        | nil => intro m _ hm; exact hm
        | cons st sts ihs =>
          intro m hsts hm
          exact ihs _ (fun q hq => hsts q (by simp [hq])) (hr _ _ (hsts st (by simp)) hm)
      exact hs _ _ hbf.2 (hp _ _ hbf.1 hm)
  exact key gbs h' 0 (Nat.zero_le _)

theorem removeUnreachable_sigDecls (f : Function) :
    (removeUnreachable f).sigDecls = f.sigDecls := by
  simp only [removeUnreachable]
  split <;> rfl

/-- **`removeUnreachable` refines**, `call_indirect` and `try_call`/`try_call_indirect`
included, when every operand of the result is below its fresh value or the fresh value is
kept (`freshOkB`). -/
theorem removeUnreachable_simX (f : Function) (hC : freshOkB f = true) :
    FunSimX f (removeUnreachable f) := by
  have hsd := removeUnreachable_sigDecls f
  revert hC hsd
  unfold freshOkB removeUnreachable
  by_cases hok : unreachableOk f (removeUnreachableRaw f) = true
  case neg => simp only [hok]; intro _ _; exact FunSimX.refl f
  simp only [hok, ite_true]
  generalize removeUnreachableRaw f = g at hok ⊢
  intro hC hsd
  obtain ⟨hn, hs, hsl, hgl, hex, hhd, hbl⟩ := unreachableOk_spec hok
  have hsub : ∀ b ∈ g.blocks, b ∈ f.blocks := by
    simp only [unreachableOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hok
    exact fun b hb => (hok.2 b hb).1
  have hle := freshValue_le_of_sub hsub
  -- every operand of `g` is in `US f g`
  have hops : ∀ b ∈ g.blocks, (∀ st ∈ b.body, ∀ v ∈ operands st.inst, US f g v) ∧
      ∀ v ∈ termOperands b.term, US f g v := by
    intro b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hC
    rcases hC with hC | hC
    · obtain ⟨h1, h2⟩ := closedB_spec hC hb
      exact ⟨fun st hst v hv => .inl (h1 st hst v hv), fun v hv => .inl (h2 v hv)⟩
    · exact ⟨fun _ _ _ _ => .inr hC, fun _ _ => .inr hC⟩
  have hheadOps : ∀ fr fr', UR f g fr fr' → ∀ v ∈ headOps fr, US f g v := by
    rintro fr fr' ⟨-, -, -, -, -, ⟨b, hb, hsuf, ht⟩, -⟩ v hv
    unfold headOps at hv
    split at hv
    · rename_i st _ hbd
      exact (hops b hb).1 st (hsuf.subset (by rw [hbd]; simp)) v hv
    · rw [ht] at hv; exact (hops b hb).2 v hv
  -- a step of `f`'s frame, run in `g` with `g`'s registers
  have hstep : ∀ fr fr' m, UR f g fr fr' →
      (∀ X1 m1, lstep fr m = .next X1 m1 → ∃ Y1, lstep fr' m = .next Y1 m1 ∧ UR f g X1 Y1) ∧
      (∀ r, (∀ X1 m1, r ≠ .next X1 m1) → (∀ msg, r ≠ .stuck msg) → lstep fr m = r →
        lstep fr' m = r) := by
    intro fr fr' m hr
    obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, ht⟩, hag⟩ := hr
    have hw : lstep { fr with func := g } m = (lstep fr m).withFunc g :=
      lstep_withFunc (by rw [hf, hex]) (by rw [hf, hgl]) (by rw [hf, hs])
        (fun id hid => by rw [hf]; exact (hbl b hb id (ht ▸ hid)).2)
    obtain ⟨hA, hB⟩ := lstep_agree (S := US f g) (X := { fr with func := g }) (Y := fr') (m := m)
      hg hsl' hb' ht' hag (hheadOps fr fr' ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, ht⟩, hag⟩)
    refine ⟨fun X1 m1 h => ?_, fun r hn hns h => ?_⟩
    · have h' : lstep { fr with func := g } m = .next { X1 with func := g } m1 := by
        rw [hw, h]; rfl
      obtain ⟨Y1, hY, h1, h2, h3, h4, h5⟩ := hA _ _ h'
      refine ⟨Y1, hY, (lstep_next_frame h).1.trans hf, h1, h2, h3, h4, ?_, h5⟩
      have hI : FrameInv (fun _ => True) { fr with func := g } :=
        ⟨trivial, b, hb, hsuf, ht⟩
      obtain ⟨-, b2, hb2, hs2, ht2⟩ := lstep_next_inv hI h'
      exact ⟨b2, hb2, hs2, ht2⟩
    · have h' : lstep { fr with func := g } m = r := by
        rw [hw, h]
        cases r <;> first | rfl | exact absurd rfl (hn _ _)
      exact hB r hn hns h'
  refine FunSimX.ofW hn hs hsl hex fun syms => ⟨UR f g, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- `IsSim`
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro fr _ ⟨hf, hg, hsl', -⟩; exact ⟨hsl', by rw [hg, hf, hs]⟩
    · rintro fr fr' m fr1 m1 hr hm hl
      obtain ⟨Y1, hY, hr1⟩ := (hstep fr fr' m hr).1 fr1 m1 hl
      exact ⟨Y1, .single hY, hr1⟩
    · rintro fr fr' m ext vals rs rest hr hm hl
      refine ⟨fr', rs, rest, .refl _ _, (hstep fr fr' m hr).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl, ?_⟩
      obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, ht⟩, hag⟩ := hr
      obtain ⟨st, fn, args, hbd, -, -, -⟩ := lstep_call_inv hl
      intro vs regs _ hset
      obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
      refine ⟨regs', hset', hf, hg, hsl', rfl, ht', ⟨b, hb, ?_, ht⟩, hag'⟩
      exact (List.suffix_cons st rest).trans (hbd ▸ hsuf)
    · rintro fr fr' m vals hr hm hl
      exact ⟨fr', .refl _ _, (hstep fr fr' m hr).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
    · rintro fr fr' m ext vals hr hm hl
      exact ⟨fr', .refl _ _, (hstep fr fr' m hr).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
    · rintro fr fr' m c hr hm hl
      exact ⟨fr', m, .refl _ _, (hstep fr fr' m hr).2 _ (fun _ _ h => by cases h)
        (fun _ h => by cases h) hl⟩
  · -- `call_indirect`
    rintro fr fr' m st rest sig callee args d a vals hr - - - hm hbd hi hca
    obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, ht⟩, hag⟩ := hr
    have hst : st ∈ b.body := hsuf.subset (by rw [hbd]; simp)
    have hopsS := (hops b hb).1 st hst
    rw [hi] at hopsS
    refine ⟨fr', st, rest, sig, callee, args, .refl _ _, by rw [hb', hbd], hi, ?_, ?_⟩
    · rw [← hca]
      unfold ciArgs
      rw [getMany_congr (fr := fr) (fr' := fr') (fun v hv => hag v (hopsS v (by simp [operands, hv])))]
      simp only [Frame.get, hag callee (hopsS callee (by simp [operands])), hg, hf, hsd]
    · intro vs regs _ hset
      obtain ⟨regs', hset', hag'⟩ := setMany_agree hag hset
      refine ⟨regs', hset', hf, hg, hsl', rfl, ht', ⟨b, hb, ?_, ht⟩, hag'⟩
      exact (List.suffix_cons st rest).trans (hbd ▸ hsuf)
  · -- `try_call`, `try_call_indirect`
    have hpost : ∀ (fr fr' : Frame) (n : Nat) (bc bc' : BlockCall) (et : ExnTable)
        (hops' : ∀ v ∈ et.normal.vals, US f g v), UR f g fr fr' → Win fr fr' →
        (∃ b ∈ g.blocks, fr.term = b.term ∧ bc.block ∈ termSuccs b.term) →
        tryNormal et fr.func.freshValue = .ok bc → tryNormal et fr'.func.freshValue = .ok bc' →
        ∀ rtys, TCont (UR f g) fr (tryRets n fr.func.freshValue) bc fr'
          (tryRets n fr'.func.freshValue) bc' rtys := by
      rintro fr fr' n bc bc' et hops' hr hw ⟨b, hb, -, hsucc⟩ hbc hbc' rtys vs regs _ hset
      obtain ⟨hf, hg, hsl', hb', ht', -, hag⟩ := hr
      obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := tryRets n fr'.func.freshValue)
        (vs := vs) (by have := (setMany_spec hset).1; simp only [tryRets, List.length_map,
          List.length_range] at this ⊢; exact this)
      have hW := setMany_tryRets hset
      have hW' := setMany_tryRets hset'
      rw [hf] at hW; rw [hg] at hW'
      -- the registers after binding the results agree on `US`
      have hagr : Agree (US f g) regs regs' := by
        intro v hv
        rcases hv with hv | hv
        · have h1 : v ∉ tryRets n fr.func.freshValue := by
            intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
            have he' : fr.func.freshValue + j = v := he
            rw [hf] at he'; exact no_window he' hv hle
          have h2 : v ∉ tryRets n fr'.func.freshValue := by
            intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
            have he' : fr'.func.freshValue + j = v := he
            rw [hg] at he'; exact no_window he' hv (Nat.le_refl _)
          rw [((setMany_spec hset').2 v).1 h2, ((setMany_spec hset).2 v).1 h1]
          exact hag v (.inl hv)
        · by_cases hv' : f.freshValue ≤ v
          · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hv'
            have := hW' i; rw [hv] at this
            rw [this, hW i]
            split
            · rfl
            · exact hag (f.freshValue + i) (.inr hv)
          · have h1 : v ∉ tryRets n fr.func.freshValue := by
              intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
              have he' : fr.func.freshValue + j = v := he
              rw [hf] at he'; exact hv' (he' ▸ Nat.le_add_right _ _)
            have h2 : v ∉ tryRets n fr'.func.freshValue := by
              intro hm; obtain ⟨j, -, he⟩ := List.mem_map.1 hm
              have he' : fr'.func.freshValue + j = v := he
              rw [hg, hv] at he'; exact hv' (he' ▸ Nat.le_add_right _ _)
            rw [((setMany_spec hset').2 v).1 h2, ((setMany_spec hset).2 v).1 h1]
            exact hag v (.inr hv)
      refine ⟨regs', hset', fun fr1 he => ?_⟩
      obtain ⟨b2, args2, regs2, hb2, hga2, hty2, hs2, rfl⟩ := enterBlock_ok he
      simp only at hb2 hga2 hs2
      obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := fr'.func.freshValue) hbc
      rw [hbc'] at hbc2; cases hbc2
      have hgb : g.block? bc'.block = some b2 := by
        rw [hblk, (hbl b hb _ hsucc).2, ← hf]; exact hb2
      have hga' : Frame.getMany { fr' with regs := regs' } bc'.args = .ok args2 := by
        refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y h => ?_) hga2
        simp only
        rcases h with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
        · rw [hx, hy]; exact hagr v (hops' v hv)
        · rw [hx, hy]; simp only [hf, hg]; rw [hW i, hW' i]
          split
          · rfl
          · have := hw i; rw [hf, hg] at this; exact this.symm
      obtain ⟨regs2', hs2', hag2⟩ := setMany_agree hagr hs2
      refine ⟨_, enterBlock_of (fr := { fr' with regs := regs' }) (by rw [hg]; exact hgb) hga' hty2
        hs2', hf, hg, hsl', rfl, rfl, ⟨b2, block?_mem hgb, List.suffix_refl _, rfl⟩, hag2⟩
    refine ⟨?_, ?_⟩
    · rintro fr fr' m fn args et n base bc ext vals hr - - hw hm hbd ht htc hca
      obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ := hr
      have hopsT := (hops b hb).2
      rw [← htb, ht] at hopsT
      obtain ⟨rfl, hbc⟩ := tcArgs_base htc
      obtain ⟨bc', hbc', -⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := fr'.func.freshValue) hbc
      have htc' : tcArgs fr' fn et = .ok (n, fr'.func.freshValue, bc') := by
        obtain ⟨e0, s0, he0, hs0, hc0, -, -, hn0⟩ := tcArgs_ok.1 htc
        refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', hn0⟩
        · rw [← he0]; simp only [Function.extern?, hg, hf, hex]
        · rw [← hs0, hg, hf, hsd]
      have hca' : callArgs fr' fn args = .ok (ext, vals) := by
        rw [← hca]
        unfold callArgs
        rw [getMany_congr (fr := fr) (fr' := fr') (fun v hv => hag v (hopsT v (by simp [termOperands, hv])))]
        simp only [Function.extern?, hg, hf, hex]
      refine ⟨fr', fn, args, et, _, bc', .refl _ _, by rw [hb', hbd], by rw [ht', ht], htc', hca', ?_⟩
      exact hpost fr fr' n bc bc' et (fun v hv => hopsT v (normal_vals_sub v hv))
        ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ hw
        ⟨b, hb, htb, by rw [← htb, ht]; exact normal_succ hbc⟩ hbc hbc' _
    · rintro fr fr' m callee args et n base bc d a vals hr - - hw hm hbd ht htc hca
      obtain ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ := hr
      have hopsT := (hops b hb).2
      rw [← htb, ht] at hopsT
      obtain ⟨rfl, hbc⟩ := ticArgs_base htc
      obtain ⟨bc', hbc', -⟩ := tryNormal_pair id (et := et) (et' := et)
        (by rw [TryDest.mapVals_id]) (b2 := fr'.func.freshValue) hbc
      have htc' : ticArgs fr' et = .ok (n, fr'.func.freshValue, bc') := by
        obtain ⟨s0, hs0, -, -, hn0⟩ := ticArgs_ok.1 htc
        exact ticArgs_ok.2 ⟨s0, by rw [← hs0, hg, hf, hsd], rfl, hbc', hn0⟩
      have hca' : ciArgs fr' et.sig callee args = .ok (d, a, vals) := by
        rw [← hca]
        unfold ciArgs
        rw [getMany_congr (fr := fr) (fr' := fr')
          (fun v hv => hag v (hopsT v (by simp [termOperands, hv])))]
        simp only [Frame.get, hag callee (hopsT callee (by simp [termOperands])), hg, hf, hsd]
      refine ⟨fr', callee, args, et, _, bc', .refl _ _, by rw [hb', hbd], by rw [ht', ht], htc', hca',
        ?_⟩
      exact hpost fr fr' n bc bc' et (fun v hv => hopsT v (normal_vals_sub' v hv))
        ⟨hf, hg, hsl', hb', ht', ⟨b, hb, hsuf, htb⟩, hag⟩ hw
        ⟨b, hb, htb, by rw [← htb, ht]; exact normal_succ hbc⟩ hbc hbc' _
  · intro b hb
    have hb' : g.entry? = some b := by simpa [Function.entry?, hhd] using hb
    refine ⟨b, hb', rfl, fun args regs slots _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl,
      ⟨b, List.mem_of_mem_head? hb', List.suffix_refl _, rfl⟩, fun _ _ => rfl⟩⟩

end Opt
