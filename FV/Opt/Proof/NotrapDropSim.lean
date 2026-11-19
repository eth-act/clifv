import FV.Opt.NotrapDrop
import FV.Opt.Proof.SimWin
import FV.Opt.Proof.SemFacts
import FV.Clif.NotrapLoad

/-!
# Dropping unused `notrap` loads is sound: `Opt.NotrapDrop.run_simX` (option D, #1017)

`run f` deletes the statements `keep L` rejects (`L = live f`): `notrap` loads and
`Opt.removable` statements none of whose results is in `L`, when the guard holds (`closedB`:
every operand of a kept statement and of a terminator is in `L`; `freshOk`: `L` is below the
output's fresh value, which is at most the input's). The mark phase computing `L` is not trusted.

The frames are related at the same program point (`NRel`): the target's body is the source's
filtered by `keep L`, the terminator is the same, and the target holds the source's value of every
value of `L`. A kept statement steps in lock-step (its operands are in `L`, `closedB`); a deleted
statement is a source-only step: a removable one keeps memory and never traps
(`Opt.evalInst_removable`), a `notrap` load reads without changing memory or is stuck, never traps
(`Clif.evalInst_notrap_load`), and a stuck source step has no obligation; its results are not in
`L`. A `try_call` binds its results at each side's fresh value (the windows of `Opt.IsSimW`), above
`L` (`freshOk`).
-/

namespace Opt.NotrapDrop

open Clif Opt

/-! ## The guard's facts -/

/-- A block with the statements `keep L` rejects removed. -/
def fltB (L : Std.HashSet ValueId) (b : Block) : Block := { b with body := b.body.filter (keep L) }

/-- What the guard of `run` checks. -/
structure Facts (f : Function) (L : Std.HashSet ValueId) : Prop where
  stmts : ∀ b ∈ f.blocks, ∀ st ∈ b.body, keep L st = true →
    ∀ x ∈ operands st.inst, L.contains x = true
  terms : ∀ b ∈ f.blocks, ∀ x ∈ termOperands b.term, L.contains x = true
  fresh : (dropWith f L).freshValue ≤ f.freshValue
  lt : ∀ v, L.contains v = true → v < (dropWith f L).freshValue

theorem facts_of {f : Function} {L : Std.HashSet ValueId} (hc : closedB f L = true)
    (hf : freshOk f L = true) : Facts f L := by
  simp only [closedB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  simp only [freshOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hf
  refine ⟨fun b hb st hst hk x hx => ?_, fun b hb x hx => (hc b hb).2 x hx, hf.1,
    fun v hv => hf.2 v ?_⟩
  · rcases (hc b hb).1 st hst with h | h
    · rw [hk] at h; cases h
    · exact h x hx
  · rw [Std.HashSet.mem_toList]; exact Std.HashSet.mem_iff_contains.2 hv

/-! ## The output's blocks -/

theorem dropWith_blocks (f : Function) (L : Std.HashSet ValueId) :
    (dropWith f L).blocks = f.blocks.map (fltB L) := rfl

theorem dropWith_block? (f : Function) (L : Std.HashSet ValueId) (id : BlockId) :
    (dropWith f L).block? id = (f.block? id).map (fltB L) := by
  simp only [Function.block?, dropWith_blocks, List.find?_map]
  rfl

theorem dropWith_entry? (f : Function) (L : Std.HashSet ValueId) :
    (dropWith f L).entry? = f.entry?.map (fltB L) := by
  simp only [Function.entry?, dropWith_blocks, List.head?_map]

/-! ## Kept and deleted statements -/

theorem not_keep {L : Std.HashSet ValueId} {st : Stmt} (h : keep L st = false) :
    droppable st.inst = true ∧ ∀ r ∈ st.results, L.contains r = false := by
  simp only [keep, Bool.or_eq_false_iff, Bool.not_eq_false', List.any_eq_false,
    Bool.not_eq_true] at h
  exact h

theorem droppable_not_call {i : Inst} (h : droppable i = true) : ∀ fn args, i ≠ .call fn args := by
  intro fn args he; rw [he] at h; cases h

/-- A deleted statement keeps memory and never traps; it gets stuck or binds values. -/
theorem evalInst_droppable {fr : Frame} {mem : Mem} {i : Inst} (h : droppable i = true) :
    (∀ vals mem', evalInst fr mem i = .ok (vals, mem') → mem' = mem) ∧
      ∀ c, evalInst fr mem i ≠ .trap c := by
  simp only [droppable, Bool.or_eq_true] at h
  rcases h with h | h
  · exact evalInst_removable h
  · cases i with
    | load op ty fl p off =>
      have hn : fl.trapCode = none := by simpa [notrapLoad] using h
      rcases evalInst_notrap_load fr mem op ty fl p off hn with ⟨v, hv⟩ | ⟨m, hm⟩
      · refine ⟨fun vals mem' he => ?_, fun c hc => ?_⟩
        · rw [hv] at he; cases he; rfl
        · rw [hv] at hc; cases hc
      · refine ⟨fun vals mem' he => ?_, fun c hc => ?_⟩
        · rw [hm] at he; cases he
        · rw [hm] at hc; cases hc
    | _ => simp [notrapLoad] at h

/-! ## Local steps that are `next` or stuck -/

/-- A local step that is a `next` or stuck. -/
def NS (x : LRes) : Prop := (∃ fr m, x = .next fr m) ∨ ∃ msg, x = .stuck msg

theorem NS.ne_ret {x : LRes} (h : NS x) (vals : List Val) : x ≠ .ret vals := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> intro he <;> cases he

theorem NS.ne_tail {x : LRes} (h : NS x) (e : ExtFunc) (vals : List Val) : x ≠ .tail e vals := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> intro he <;> cases he

theorem NS.ne_trap {x : LRes} (h : NS x) (c : TrapCode) : x ≠ .trap c := by
  rcases h with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> intro he <;> cases he

theorem ofRes_ns {α : Type} {r : Res α} {k : α → LRes} (hr : ∀ c, r ≠ .trap c)
    (hk : ∀ a, NS (k a)) : NS (LRes.ofRes r k) := by
  cases r with
  | ok a => exact hk a
  | trap c => exact absurd rfl (hr c)
  | stuck m => exact .inr ⟨m, rfl⟩

theorem ofRes_eq_next {α : Type} {r : Res α} {k : α → LRes} {fr1 : Frame} {m1 : Mem}
    (h : LRes.ofRes r k = .next fr1 m1) : ∃ a, r = .ok a ∧ k a = .next fr1 m1 := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | trap c => cases h
  | stuck m => cases h

theorem enterBlock_ne_trap' (fr : Frame) (bc : BlockCall) (c : TrapCode) : enterBlock fr bc ≠ .trap c := by
  simp [enterBlock, checkTys]

theorem tailArgs_ne_trap (fr : Frame) (fn : FnRef) (args : List ValueId) (c : TrapCode) :
    tailArgs fr fn args ≠ .trap c := by
  simp [tailArgs, checkTys]

theorem mapVals_id (d : TryDest) : d.mapVals id = d := by
  obtain ⟨b, args⟩ := d
  simp only [TryDest.mapVals, TryDest.mk.injEq, true_and]
  conv => rhs; rw [← List.map_id args]
  apply List.map_congr_left
  intro a _
  cases a <;> rfl

/-! ## The relation -/

/-- Frames at the same program point (module doc). -/
structure NRel (f : Function) (L : Std.HashSet ValueId) (fr fr' : Frame) : Prop where
  func : fr.func = f
  func' : fr'.func = dropWith f L
  slots : fr'.slots = fr.slots
  body : fr'.body = fr.body.filter (keep L)
  term : fr'.term = fr.term
  pp : ∃ b ∈ f.blocks, fr.body <:+ b.body ∧ fr.term = b.term
  agree : ∀ v, L.contains v = true → fr'.regs v = fr.regs v

section
variable {f : Function} {L : Std.HashSet ValueId} (hF : Facts f L)

theorem NRel.globals {fr fr' : Frame} (h : NRel f L fr fr') : fr'.func.globals = fr.func.globals := by
  rw [h.func, h.func']; rfl

theorem NRel.externs {fr fr' : Frame} (h : NRel f L fr fr') : fr'.func.externs = fr.func.externs := by
  rw [h.func, h.func']; rfl

theorem NRel.sigDecls {fr fr' : Frame} (h : NRel f L fr fr') :
    fr'.func.sigDecls = fr.func.sigDecls := by
  rw [h.func, h.func']; rfl

theorem NRel.sig {fr fr' : Frame} (h : NRel f L fr fr') : fr'.func.sig = fr.func.sig := by
  rw [h.func, h.func']; rfl

/-- Binding values at the same results keeps the agreement on `L`. -/
theorem agree_setMany {r r' r1 r1' : Regs} {xs : List ValueId} {vs : List Val}
    (ha : ∀ v, L.contains v = true → r' v = r v) (h1 : r.setMany xs vs = some r1)
    (h1' : r'.setMany xs vs = some r1') : ∀ v, L.contains v = true → r1' v = r1 v := by
  intro v hv
  by_cases hm : v ∈ xs
  · exact (setMany_same h1 h1' v hm).symm
  · rw [((setMany_spec h1').2 v).1 hm, ((setMany_spec h1).2 v).1 hm, ha v hv]

include hF

/-- The operands of a kept statement at the head of the source's body hold equal values. -/
theorem NRel.ops {fr fr' : Frame} (h : NRel f L fr fr') {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) (hk : keep L st = true) :
    ∀ x ∈ operands st.inst, fr'.regs x = fr.regs x := by
  obtain ⟨b, hbm, hsuf, -⟩ := h.pp
  have hst : st ∈ b.body := hsuf.subset (by rw [hb]; simp)
  exact fun x hx => h.agree x (hF.stmts b hbm st hst hk x hx)

/-- The terminator's operands hold equal values. -/
theorem NRel.termOps {fr fr' : Frame} (h : NRel f L fr fr') :
    ∀ x ∈ termOperands fr.term, fr'.regs x = fr.regs x := by
  obtain ⟨b, hbm, -, ht⟩ := h.pp
  intro x hx
  rw [ht] at hx
  exact h.agree x (hF.terms b hbm x hx)

/-- A kept statement other than a call steps in lock-step. -/
theorem NRel.kept {fr fr' : Frame} {mm : Mem} {s : Stmt} {ss : List Stmt}
    (h : NRel f L fr fr') (hs : fr.body = s :: ss) (hk : keep L s = true)
    (hnc : ∀ fn args, s.inst ≠ .call fn args) :
    (∀ fr1 m1, lstep fr mm = .next fr1 m1 → ∃ fr1', lstep fr' mm = .next fr1' m1 ∧
      NRel f L fr1 fr1') ∧
    (∀ c, lstep fr mm = .trap c → lstep fr' mm = .trap c) := by
  have ht : fr'.body = s :: ss.filter (keep L) := by
    rw [h.body, hs, List.filter_cons_of_pos hk]
  have hev : evalInst fr' mm s.inst = evalInst fr mm s.inst :=
    evalInst_congr h.globals h.externs h.slots (h.ops hF hs hk)
  rw [lstep_inst hs hnc, lstep_inst ht hnc, hev]
  refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_⟩
  · cases he : evalInst fr mm s.inst with
    | trap c => rw [he] at hl; cases hl
    | stuck msg => rw [he] at hl; cases hl
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl
      simp only [LRes.ofRes] at hl ⊢
      split at hl
      · rename_i regs hset
        cases hl
        obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vals)
          (setMany_spec hset).1
        simp only [hset']
        refine ⟨_, rfl, ⟨h.func, h.func', h.slots, rfl, h.term, ?_, ?_⟩⟩
        · obtain ⟨b, hbm, hsuf, hterm⟩ := h.pp
          exact ⟨b, hbm, (List.suffix_cons s ss).trans (hs ▸ hsuf), hterm⟩
        · exact agree_setMany h.agree hset hset'
      · cases hl
  · cases he : evalInst fr mm s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' => rw [he] at hl; exact hl

omit hF in
/-- A deleted statement: the source steps alone, keeping memory; it never traps or calls. -/
theorem NRel.deleted {fr fr' : Frame} {mm : Mem} {s : Stmt} {ss : List Stmt}
    (h : NRel f L fr fr') (hs : fr.body = s :: ss) (hk : keep L s = false) :
    (∀ fr1 m1, lstep fr mm = .next fr1 m1 → m1 = mm ∧ NRel f L fr1 fr') ∧
      (∀ c, lstep fr mm ≠ .trap c) ∧ (∀ e vs rs rest, lstep fr mm ≠ .call e vs rs rest) := by
  obtain ⟨hd, hres⟩ := not_keep hk
  have hnc := droppable_not_call hd
  obtain ⟨hmem, hnt⟩ := evalInst_droppable (fr := fr) (mem := mm) hd
  rw [lstep_inst hs hnc]
  refine ⟨fun fr1 m1 hl => ?_, fun c hl => ?_, fun e vs rs rest hl => ?_⟩
  · cases he : evalInst fr mm s.inst with
    | trap c => rw [he] at hl; cases hl
    | stuck msg => rw [he] at hl; cases hl
    | ok p =>
      obtain ⟨vals, m1'⟩ := p
      rw [he] at hl
      simp only [LRes.ofRes] at hl
      split at hl
      · rename_i regs hset
        cases hl
        refine ⟨hmem _ _ he, ⟨h.func, h.func', h.slots, ?_, h.term, ?_, fun v hv => ?_⟩⟩
        · show fr'.body = ss.filter (keep L)
          rw [h.body, hs, List.filter_cons_of_neg (by simp [hk])]
        · obtain ⟨b, hbm, hsuf, hterm⟩ := h.pp
          exact ⟨b, hbm, (List.suffix_cons s ss).trans (hs ▸ hsuf), hterm⟩
        · have hnm : v ∉ s.results := fun hm => by rw [hres v hm] at hv; cases hv
          show fr'.regs v = regs v
          rw [((setMany_spec hset).2 v).1 hnm, h.agree v hv]
      · cases hl
  · cases he : evalInst fr mm s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' => exact hnt c' he
  · cases he : evalInst fr mm s.inst with
    | ok p => rw [he] at hl; obtain ⟨_, _⟩ := p; simp only [LRes.ofRes] at hl; split at hl <;> cases hl
    | stuck msg => rw [he] at hl; cases hl
    | trap c' => rw [he] at hl; cases hl

omit hF in
/-- Entering a block with arguments whose values agree. -/
theorem NRel.enter {fr fr' fr1 : Frame} (h : NRel f L fr fr') {bc : BlockCall} {bc' : BlockCall}
    (hblk : bc'.block = bc.block) (hargs : fr'.getMany bc'.args = fr.getMany bc.args)
    (he : enterBlock fr bc = .ok fr1) :
    ∃ fr1', enterBlock fr' bc' = .ok fr1' ∧ NRel f L fr1 fr1' := by
  obtain ⟨b, args, regs, hb, ha, hty, hset, rfl⟩ := enterBlock_ok he
  rw [h.func] at hb
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := b.params.map (·.1)) (vs := args)
    (setMany_spec hset).1
  have hb' : fr'.func.block? bc'.block = some (fltB L b) := by
    rw [h.func', dropWith_block?, hblk, hb]; rfl
  refine ⟨{ fr' with regs := regs', body := (fltB L b).body, term := b.term }, ?_, ?_⟩
  · simp only [enterBlock, hb', Res.ofOption_some, Res.ok_bind, hargs, ha, checkTys,
      show (fltB L b).params = b.params from rfl, hty, beq_self_eq_true, Res.check_true, hset',
      Res.pure_eq]
    rfl
  · refine ⟨h.func, h.func', h.slots, rfl, rfl, ⟨b, List.mem_of_find?_eq_some hb,
      List.suffix_refl _, rfl⟩, agree_setMany h.agree hset hset'⟩

/-- The terminator steps in lock-step. -/
theorem NRel.termStep {fr fr' : Frame} {mm : Mem} (h : NRel f L fr fr') (hs : fr.body = []) :
    (∀ fr1 m1, lstep fr mm = .next fr1 m1 → ∃ fr1', lstep fr' mm = .next fr1' m1 ∧
      NRel f L fr1 fr1') ∧
    (∀ vals, lstep fr mm = .ret vals → lstep fr' mm = .ret vals) ∧
    (∀ e vals, lstep fr mm = .tail e vals → lstep fr' mm = .tail e vals) ∧
    (∀ c, lstep fr mm = .trap c → lstep fr' mm = .trap c) := by
  have hs' : fr'.body = [] := by rw [h.body, hs]; rfl
  have hops := h.termOps hF
  have hmany : ∀ xs, (∀ x ∈ xs, x ∈ termOperands fr.term) → fr'.getMany xs = fr.getMany xs :=
    fun xs hxs => getMany_congr fun x hx => hops x (hxs x hx)
  have hget : ∀ x ∈ termOperands fr.term, fr'.get x = fr.get x := fun x hx => by
    simp only [Frame.get, hops x hx]
  -- a branch: the source's step is a `next` (related) or stuck
  have hbr : ∀ bc, (∀ x ∈ bc.args, x ∈ termOperands fr.term) →
      (∀ fr1 m1, LRes.ofRes (enterBlock fr bc) (fun fr2 => LRes.next fr2 mm) = .next fr1 m1 →
        ∃ fr1', LRes.ofRes (enterBlock fr' bc) (fun fr2 => LRes.next fr2 mm) = .next fr1' m1 ∧
          NRel f L fr1 fr1') ∧
      NS (LRes.ofRes (enterBlock fr bc) (fun fr2 => LRes.next fr2 mm)) := by
    intro bc hbc
    refine ⟨fun fr1 m1 hl => ?_, ofRes_ns (enterBlock_ne_trap' fr bc) fun a => .inl ⟨a, mm, rfl⟩⟩
    obtain ⟨fr2, he, hk⟩ := ofRes_eq_next hl
    cases hk
    obtain ⟨fr1', he', hr⟩ := h.enter rfl (hmany bc.args hbc) he
    exact ⟨fr1', by rw [he']; rfl, hr⟩
  cases ht : fr.term with
  | jump d =>
    have hl0 : lstep fr mm = LRes.ofRes (enterBlock fr d) (fun fr2 => LRes.next fr2 mm) := by
      rw [lstep_term hs, ht]
    have hl1 : lstep fr' mm = LRes.ofRes (enterBlock fr' d) (fun fr2 => LRes.next fr2 mm) := by
      rw [lstep_term hs', h.term, ht]
    obtain ⟨hn, hns⟩ := hbr d (by rw [ht]; simp [termOperands])
    rw [← hl0] at hn hns
    rw [hl1]
    exact ⟨hn, fun _ hl => absurd hl (hns.ne_ret _), fun _ _ hl => absurd hl (hns.ne_tail _ _),
      fun _ hl => absurd hl (hns.ne_trap _)⟩
  | brif c t e =>
    have hc : fr'.get c = fr.get c := hget c (by rw [ht]; simp [termOperands])
    have hl0 : lstep fr mm = LRes.ofRes (fr.get c) fun cv =>
        LRes.ofRes (enterBlock fr (if Sem.truthy cv.bits then t else e)) fun fr2 => .next fr2 mm := by
      rw [lstep_term hs, ht]
    have hl1 : lstep fr' mm = LRes.ofRes (fr.get c) fun cv =>
        LRes.ofRes (enterBlock fr' (if Sem.truthy cv.bits then t else e)) fun fr2 => .next fr2 mm := by
      rw [lstep_term hs', h.term, ht]
      show LRes.ofRes (fr'.get c) _ = _
      rw [hc]
    have hb : ∀ cv : Val, (∀ x ∈ (if Sem.truthy cv.bits then t else e).args, x ∈ termOperands fr.term) :=
      fun cv x hx => by
        rw [ht]; simp only [termOperands, List.mem_cons, List.mem_append]
        split at hx <;> simp [hx]
    have hns : NS (lstep fr mm) := by
      rw [hl0]; exact ofRes_ns (fun c' h' => (Frame.get_ne_trap _ _ c').1 h') fun cv => (hbr _ (hb cv)).2
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => absurd hl (hns.ne_ret _),
      fun _ _ hl => absurd hl (hns.ne_tail _ _), fun _ hl => absurd hl (hns.ne_trap _)⟩
    rw [hl0] at hl
    obtain ⟨cv, hcv, hk⟩ := ofRes_eq_next hl
    obtain ⟨fr1', hk', hr⟩ := (hbr _ (hb cv)).1 fr1 m1 hk
    exact ⟨fr1', by rw [hl1, hcv]; exact hk', hr⟩
  | brTable x dflt table =>
    have hx : fr'.get x = fr.get x := hget x (by rw [ht]; simp [termOperands])
    have hl0 : lstep fr mm = LRes.ofRes (fr.get x) fun xv =>
        LRes.ofRes (enterBlock fr (table[xv.toNat]?.getD dflt)) fun fr2 => .next fr2 mm := by
      rw [lstep_term hs, ht]
    have hl1 : lstep fr' mm = LRes.ofRes (fr.get x) fun xv =>
        LRes.ofRes (enterBlock fr' (table[xv.toNat]?.getD dflt)) fun fr2 => .next fr2 mm := by
      rw [lstep_term hs', h.term, ht]
      show LRes.ofRes (fr'.get x) _ = _
      rw [hx]
    have hb : ∀ xv : Val, (∀ y ∈ (table[xv.toNat]?.getD dflt).args, y ∈ termOperands fr.term) :=
      fun xv y hy => by
        rw [ht]
        show y ∈ x :: (dflt.args ++ table.flatMap (·.args))
        cases hg : table[xv.toNat]? with
        | none => rw [hg] at hy; exact List.mem_cons_of_mem _ (List.mem_append_left _ hy)
        | some bc =>
          rw [hg] at hy
          exact List.mem_cons_of_mem _ (List.mem_append_right _
            (List.mem_flatMap.2 ⟨bc, List.mem_of_getElem? hg, hy⟩))
    have hns : NS (lstep fr mm) := by
      rw [hl0]; exact ofRes_ns (fun c' h' => (Frame.get_ne_trap _ _ c').1 h') fun xv => (hbr _ (hb xv)).2
    refine ⟨fun fr1 m1 hl => ?_, fun _ hl => absurd hl (hns.ne_ret _),
      fun _ _ hl => absurd hl (hns.ne_tail _ _), fun _ hl => absurd hl (hns.ne_trap _)⟩
    rw [hl0] at hl
    obtain ⟨xv, hxv, hk⟩ := ofRes_eq_next hl
    obtain ⟨fr1', hk', hr⟩ := (hbr _ (hb xv)).1 fr1 m1 hk
    exact ⟨fr1', by rw [hl1, hxv]; exact hk', hr⟩
  | ret xs =>
    have hl0 : lstep fr mm = LRes.ofRes (fr.getMany xs) fun vals => .ret vals := by
      rw [lstep_term hs, ht]
    have hl1 : lstep fr' mm = LRes.ofRes (fr.getMany xs) fun vals => .ret vals := by
      rw [lstep_term hs', h.term, ht]
      show LRes.ofRes (fr'.getMany xs) _ = _
      rw [hmany xs (by rw [ht]; simp [termOperands])]
    rw [hl0, hl1]
    refine ⟨fun _ _ hl => ?_, fun _ hl => hl, fun _ _ hl => ?_, fun _ hl => ?_⟩ <;>
      cases hg : fr.getMany xs <;> rw [hg] at hl <;> cases hl
    exact absurd hg (by simp)
  | returnCall fn args =>
    have hta : tailArgs fr' fn args = tailArgs fr fn args := by
      simp only [tailArgs, Function.extern?, h.externs, h.sig,
        hmany args (by rw [ht]; simp [termOperands])]
    have hl0 : lstep fr mm = LRes.ofRes (tailArgs fr fn args) fun (ext, vals) => .tail ext vals := by
      rw [lstep_term hs, ht]
    have hl1 : lstep fr' mm = LRes.ofRes (tailArgs fr fn args) fun (ext, vals) => .tail ext vals := by
      rw [lstep_term hs', h.term, ht]
      show LRes.ofRes (tailArgs fr' fn args) _ = _
      rw [hta]
    rw [hl0, hl1]
    refine ⟨fun _ _ hl => ?_, fun _ hl => ?_, fun _ _ hl => hl, fun _ hl => ?_⟩ <;>
      cases hg : tailArgs fr fn args <;> rw [hg] at hl <;> cases hl
    exact absurd hg (tailArgs_ne_trap _ _ _ _)
  | trap c =>
    have hl0 : lstep fr mm = .trap c := by rw [lstep_term hs, ht]
    have hl1 : lstep fr' mm = .trap c := by rw [lstep_term hs', h.term, ht]
    rw [hl0, hl1]
    exact ⟨fun _ _ hl => (by cases hl), fun _ hl => (by cases hl), fun _ _ hl => (by cases hl),
      fun _ hl => hl⟩
  | tryCall fn args et =>
    have hl0 : lstep fr mm = .stuck "try_call is handled by step" := by rw [lstep_term hs, ht]
    rw [hl0]
    exact ⟨fun _ _ hl => (by cases hl), fun _ hl => (by cases hl), fun _ _ hl => (by cases hl),
      fun _ hl => (by cases hl)⟩
  | tryCallIndirect c args et =>
    have hl0 : lstep fr mm = .stuck "try_call is handled by step" := by rw [lstep_term hs, ht]
    rw [hl0]
    exact ⟨fun _ _ hl => (by cases hl), fun _ hl => (by cases hl), fun _ _ hl => (by cases hl),
      fun _ hl => (by cases hl)⟩

omit hF in
/-- Binding a call's results keeps the relation. -/
theorem NRel.cont {fr fr' : Frame} (h : NRel f L fr fr') {s : Stmt} {rest : List Stmt}
    (hs : fr.body = s :: rest) (rtys : List Ty) :
    Cont (NRel f L) { fr with body := rest } s.results
      { fr' with body := rest.filter (keep L) } s.results rtys := by
  intro vs regs _ hset
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := s.results) (vs := vs)
    (setMany_spec hset).1
  refine ⟨regs', hset', h.func, h.func', h.slots, rfl, h.term, ?_, agree_setMany h.agree hset hset'⟩
  obtain ⟨b, hbm, hsuf, hterm⟩ := h.pp
  exact ⟨b, hbm, (List.suffix_cons s rest).trans (hs ▸ hsuf), hterm⟩

/-- A call: the same callee and arguments. -/
theorem NRel.call {fr fr' : Frame} {mm : Mem} {ext : ExtFunc} {vals : List Val}
    {rs : List ValueId} {rest : List Stmt} (h : NRel f L fr fr')
    (hl : lstep fr mm = .call ext vals rs rest) :
    lstep fr' mm = .call ext vals rs (rest.filter (keep L)) ∧
      Cont (NRel f L) { fr with body := rest } rs
        { fr' with body := rest.filter (keep L) } rs (AbiParam.tys ext.sig.returns) := by
  obtain ⟨s, fn, args, hs, hc, hrs, hca⟩ := lstep_call_inv hl
  subst hrs
  have hk : keep L s = true := by
    cases hk : keep L s
    · exact absurd hc (droppable_not_call (not_keep hk).1 fn args)
    · rfl
  have ht : fr'.body = s :: rest.filter (keep L) := by
    rw [h.body, hs, List.filter_cons_of_pos hk]
  have hops := h.ops hF hs hk
  have hca' : callArgs fr' fn args = callArgs fr fn args := by
    simp only [callArgs, Function.extern?, h.externs,
      getMany_congr (xs := args) (fun x hx => hops x (by rw [hc]; exact hx))]
  refine ⟨by rw [lstep_call ht hc, hca', hca]; rfl, h.cont hs _⟩

/-- The `try_call` successor: binding the results at each side's fresh value and entering the
normal successor. -/
theorem NRel.tcont {fr fr' : Frame} (h : NRel f L fr fr') (hw : Win fr fr') {et : ExnTable}
    (hvals : ∀ v ∈ et.normal.vals, L.contains v = true) {n : Nat} {bc : BlockCall}
    (hn : tryNormal et fr.func.freshValue = .ok bc) :
    ∃ bc', tryNormal et fr'.func.freshValue = .ok bc' ∧
      ∀ rtys, TCont (NRel f L) fr (tryRets n fr.func.freshValue) bc fr'
        (tryRets n fr'.func.freshValue) bc' rtys := by
  obtain ⟨bc', hn', hblk, hpw⟩ := tryNormal_pair id (et' := et) (mapVals_id _).symm
    (b2 := fr'.func.freshValue) hn
  refine ⟨bc', hn', fun rtys vs regs _ hset => ?_⟩
  obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs) (xs := tryRets n fr'.func.freshValue)
    (vs := vs) (by simp [tryRets, (setMany_spec hset).1.symm])
  have hbase : fr.func.freshValue = f.freshValue := by rw [h.func]
  have hbase' : fr'.func.freshValue = (dropWith f L).freshValue := by rw [h.func']
  -- values of `L` are below both windows
  have hlo : ∀ v, L.contains v = true → regs' v = regs v := by
    intro v hv
    have h1 := hF.lt v hv
    have hn1 : v ∉ tryRets n fr.func.freshValue := fun hm => by
      obtain ⟨j, -, hj⟩ := List.mem_map.1 hm
      have h3 : fr.func.freshValue + j = v := hj
      rw [hbase] at h3
      exact no_window' h3 (Nat.lt_of_lt_of_le h1 hF.fresh)
    have hn2 : v ∉ tryRets n fr'.func.freshValue := fun hm => by
      obtain ⟨j, -, hj⟩ := List.mem_map.1 hm
      have h3 : fr'.func.freshValue + j = v := hj
      rw [hbase'] at h3; exact no_window' h3 h1
    rw [((setMany_spec hset').2 v).1 hn2, ((setMany_spec hset).2 v).1 hn1, h.agree v hv]
  refine ⟨regs', hset', fun fr1 he => ?_⟩
  have hargs : ({ fr' with regs := regs' } : Frame).getMany bc'.args =
      ({ fr with regs } : Frame).getMany bc.args := by
    cases hg : ({ fr with regs } : Frame).getMany bc.args with
    | ok vs1 =>
      refine getMany_pw2 (hpw.imp fun x y hp => ?_) hg
      rcases hp with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
      · rw [hx, hy]; exact hlo v (hvals v hv)
      · rw [hx, hy]
        show regs' (fr'.func.freshValue + i) = regs (fr.func.freshValue + i)
        rw [setMany_tryRets hset', setMany_tryRets hset]
        split
        · rfl
        · exact (hw i).symm
    | trap c =>
      exfalso; exact (Frame.getMany_ne_trap _ _ c).1 hg
    | stuck m =>
      exfalso
      simp only [enterBlock, Res.bind_eq_ok] at he
      obtain ⟨_, _, args, ha, _⟩ := he
      rw [hg] at ha; cases ha
  have hr : NRel f L { fr with regs } { fr' with regs := regs' } :=
    ⟨h.func, h.func', h.slots, h.body, h.term, h.pp, hlo⟩
  exact hr.enter hblk hargs he

end

/-! ## The simulation -/

section
variable {f : Function} {L : Std.HashSet ValueId} (hF : Facts f L) (syms : String → Option Nat)
include hF

theorem isSimW : IsSimW syms (NRel f L) where
  toIsSim := {
    frame := fun h => ⟨h.slots, h.sig⟩
    next := by
      intro fr fr' m fr1 m1 h _ hl
      cases hb : fr.body with
      | nil =>
        obtain ⟨fr1', hl', hr⟩ := (h.termStep hF hb).1 fr1 m1 hl
        exact ⟨fr1', .single hl', hr⟩
      | cons s ss =>
        cases hk : keep L s with
        | false =>
          obtain ⟨hm, hr⟩ := (h.deleted hb hk).1 fr1 m1 hl
          subst hm
          exact ⟨fr', .refl _ _, hr⟩
        | true =>
          have hnc : ∀ fn args, s.inst ≠ .call fn args := by
            intro fn args hc
            rw [lstep_call hb hc] at hl
            cases hca : callArgs fr fn args with
            | ok p => obtain ⟨e, v⟩ := p; rw [hca] at hl; cases hl
            | trap c' => exact absurd hca (callArgs_ne_trap _ _ _ _)
            | stuck msg => rw [hca] at hl; cases hl
          obtain ⟨fr1', hl', hr⟩ := (h.kept hF hb hk hnc).1 fr1 m1 hl
          exact ⟨fr1', .single hl', hr⟩
    call := by
      intro fr fr' m ext vals rs rest h _ hl
      obtain ⟨hl', hk⟩ := h.call hF hl
      exact ⟨fr', rs, rest.filter (keep L), .refl _ _, hl', hk⟩
    ret := by
      intro fr fr' m vals h _ hl
      have hb := lstep_ret_inv hl
      exact ⟨fr', .refl _ _, (h.termStep hF hb).2.1 vals hl⟩
    tail := by
      intro fr fr' m ext vals h _ hl
      have hb := lstep_tail_inv hl
      exact ⟨fr', .refl _ _, (h.termStep hF hb).2.2.1 ext vals hl⟩
    trap := by
      intro fr fr' m c h _ hl
      cases hb : fr.body with
      | nil => exact ⟨fr', m, .refl _ _, (h.termStep hF hb).2.2.2 c hl⟩
      | cons s ss =>
        cases hk : keep L s with
        | false => exact absurd hl ((h.deleted hb hk (mm := m)).2.1 c)
        | true =>
          have hnc : ∀ fn args, s.inst ≠ .call fn args := by
            intro fn args hc
            rw [lstep_call hb hc] at hl
            cases hca : callArgs fr fn args with
            | ok p => obtain ⟨e, v⟩ := p; rw [hca] at hl; cases hl
            | trap c' => exact absurd hca (callArgs_ne_trap _ _ _ _)
            | stuck msg => rw [hca] at hl; cases hl
          exact ⟨fr', m, .refl _ _, (h.kept hF hb hk hnc).2 c hl⟩ }
  ci := by
    intro fr fr' m st rest sig callee args d a vals h _ _ _ _ hb hi hca
    have hk : keep L st = true := by
      cases hk : keep L st
      · have := (not_keep hk).1; rw [hi] at this; cases this
      · rfl
    have ht : fr'.body = st :: rest.filter (keep L) := by
      rw [h.body, hb, List.filter_cons_of_pos hk]
    have hops := h.ops hF hb hk
    rw [hi] at hops
    have hca' : ciArgs fr' sig callee args = ciArgs fr sig callee args := by
      simp only [ciArgs, h.sigDecls, Frame.get, hops callee (by simp [operands]),
        getMany_congr (xs := args) (fun x hx => hops x (by simp [operands, hx]))]
    exact ⟨fr', st, rest.filter (keep L), sig, callee, args, .refl _ _, ht, hi,
      (by rw [hca']; exact hca), h.cont hb _⟩
  tc := {
    call := by
      intro fr fr' m fn args et n base bc ext vals h _ _ hw _ hb ht htc hca
      have hb' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hops := h.termOps hF
      rw [ht] at hops
      obtain ⟨ext0, sig, he, hs, hc, rfl, hn, rfl⟩ := tcArgs_ok.1 htc
      obtain ⟨bc', hn', hk⟩ := h.tcont hF hw (fun v hv => by
        obtain ⟨b, hbm, -, hterm⟩ := h.pp
        rw [ht] at hterm
        exact hF.terms b hbm v (hterm ▸ normal_vals_sub v hv)) (n := ext0.sig.returns.length) hn
      have htc' : tcArgs fr' fn et = .ok (ext0.sig.returns.length, fr'.func.freshValue, bc') :=
        tcArgs_ok.2 ⟨ext0, sig, by rw [Function.extern?, h.externs]; exact he,
          by rw [h.sigDecls]; exact hs, hc, rfl, hn', rfl⟩
      have hca' : callArgs fr' fn args = callArgs fr fn args := by
        simp only [callArgs, Function.extern?, h.externs,
          getMany_congr (xs := args) (fun x hx => hops x (by simp [termOperands, hx]))]
      exact ⟨fr', fn, args, et, _, bc', .refl _ _, hb', (by rw [h.term, ht]), htc',
        (by rw [hca']; exact hca), hk _⟩
    ind := by
      intro fr fr' m callee args et n base bc d a vals h _ _ hw _ hb ht htc hca
      have hb' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hops := h.termOps hF
      rw [ht] at hops
      obtain ⟨sig, hs, rfl, hn, rfl⟩ := ticArgs_ok.1 htc
      obtain ⟨bc', hn', hk⟩ := h.tcont hF hw (fun v hv => by
        obtain ⟨b, hbm, -, hterm⟩ := h.pp
        rw [ht] at hterm
        exact hF.terms b hbm v (hterm ▸ normal_vals_sub' v hv)) (n := sig.returns.length) hn
      have htc' : ticArgs fr' et = .ok (sig.returns.length, fr'.func.freshValue, bc') :=
        ticArgs_ok.2 ⟨sig, by rw [h.sigDecls]; exact hs, rfl, hn', rfl⟩
      have hca' : ciArgs fr' et.sig callee args = ciArgs fr et.sig callee args := by
        simp only [ciArgs, h.sigDecls, Frame.get, hops callee (by simp [termOperands]),
          getMany_congr (xs := args) (fun x hx => hops x (by simp [termOperands, hx]))]
      exact ⟨fr', callee, args, et, _, bc', .refl _ _, hb', (by rw [h.term, ht]), htc',
        (by rw [hca']; exact hca), hk _⟩ }

/-- **The output with the guard's facts simulates the input.** -/
theorem dropWith_simX : FunSimX f (dropWith f L) := by
  refine FunSimX.ofW rfl rfl rfl rfl fun syms => ⟨NRel f L, isSimW hF syms, fun b hb => ?_⟩
  refine ⟨fltB L b, by rw [dropWith_entry?, hb]; rfl, rfl, fun args regs slots _ _ _ => ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨b, List.mem_of_mem_head? hb, List.suffix_refl _, rfl⟩,
    fun _ _ => rfl⟩

end

/-- **The pass simulates every function.** -/
theorem run_simX (f : Function) : FunSimX f (run f) := by
  unfold run
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact dropWith_simX (facts_of h.1.2 h.2)
  · exact FunSimX.refl f

end Opt.NotrapDrop
