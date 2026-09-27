import FV.Compile.Emit
import FV.Compile.Proof.Exec

/-!
# Generator (`CGM`) lemmas

* `*_run`: one-step unfolding of the generator primitives (`rfl`).
* `Lk F cg` / `Good F cg`: the final function `F` contains what the generator has produced so
  far (finished blocks, extern declarations, slots) and, for `Good`, the block under
  construction with the statements emitted so far as a prefix.
* `Bk A B m`: if `B` holds after running `m` then `A` held before. Simulation lemmas assume
  `Good F` for the state *after* the generated code and use `Bk` to get it for every earlier
  state. `A, B ∈ {Lk, Good}`: `terminate` turns `Lk` after into `Good` before, `switchTo`
  turns `Good` after into `Lk` before.
* `At F cg fr`: the frame `fr` executes `F` at the generator position `cg` (the statements of
  the open block emitted so far have run; `fr.body` is the rest of that block in `F`).
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile Clif

/-! ## Unfolding -/

theorem bind_run {α β : Type} (m : CGM α) (f : α → CGM β) (cg : CG) :
    (m >>= f).run cg = (f (m.run cg).1).run (m.run cg).2 := rfl

theorem pure_run {α : Type} (a : α) (cg : CG) : (pure a : CGM α).run cg = (a, cg) := rfl

theorem map_run {α β : Type} (f : α → β) (m : CGM α) (cg : CG) :
    (f <$> m).run cg = (f (m.run cg).1, (m.run cg).2) := rfl

theorem fresh_run (cg : CG) :
    fresh.run cg = (cg.nextVal, { cg with nextVal := cg.nextVal + 1 }) := rfl

theorem emitStmt_run (rs : List ValueId) (i : Inst) (cg : CG) :
    (emitStmt rs i).run cg = ((), { cg with curBody := (⟨rs, i⟩ : Clif.Stmt) :: cg.curBody }) :=
  rfl

theorem inst1_run (i : Inst) (cg : CG) :
    (inst1 i).run cg = (cg.nextVal,
      { cg with nextVal := cg.nextVal + 1, curBody := (⟨[cg.nextVal], i⟩ : Clif.Stmt) :: cg.curBody }) :=
  rfl

theorem iconstN_run (ty : Clif.Ty) (n : Nat) (cg : CG) :
    (iconstN ty n).run cg = (cg.nextVal,
      { cg with nextVal := cg.nextVal + 1,
                curBody := (⟨[cg.nextVal], .iconst ty (BitVec.ofNat ty.width n)⟩ : Clif.Stmt) ::
                  cg.curBody }) := rfl

theorem newBlock_run (cg : CG) :
    newBlock.run cg = (cg.nextBlock, { cg with nextBlock := cg.nextBlock + 1 }) := rfl

/-- The block that `terminate t` finishes. -/
def curBlock (cg : CG) (t : Terminator) : Block :=
  { id := cg.cur, params := cg.curParams, body := cg.curBody.reverse, term := t }

theorem terminate_run (t : Terminator) (cg : CG) :
    (terminate t).run cg = ((), { cg with done := curBlock cg t :: cg.done, curBody := [] }) := rfl

theorem switchTo_run (b : BlockId) (ps : List (ValueId × Clif.Ty)) (cg : CG) :
    (switchTo b ps).run cg = ((), { cg with cur := b, curParams := ps, curBody := [] }) := rfl

theorem newSlot_run (size : Nat) (cg : CG) :
    (newSlot size).run cg = (cg.slots.length,
      { cg with slots := cg.slots ++ [(cg.slots.length, { size, align := some 8 })] }) := rfl

theorem declare_run (name : String) (sig : Signature) (cg : CG) :
    (declare name sig).run cg =
      match cg.externs.find? (fun e => e.2.name == name && e.2.sig == sig) with
      | some (r, _) => (r, cg)
      | none => (cg.externs.length,
          { cg with externs := cg.externs ++ [(cg.externs.length, { name, sig })] }) := by
  unfold declare
  rcases h : cg.externs.find? (fun e => e.2.name == name && e.2.sig == sig) with _ | ⟨r, e⟩ <;>
    simp only [bind_run, show StateT.run (get : CGM CG) cg = (cg, cg) from rfl, h] <;> rfl

/-! ## Containment of the generated code in the final function -/

/-- Everything finished so far is part of `F`. -/
def Lk (F : Function) (cg : CG) : Prop :=
  (∀ b ∈ cg.done, F.block? b.id = some b) ∧ cg.externs <+: F.externs ∧ cg.slots <+: F.slots

/-- `Lk`, and the open block is a block of `F` whose body starts with what was emitted. -/
def Good (F : Function) (cg : CG) : Prop :=
  Lk F cg ∧ ∃ blk, F.block? cg.cur = some blk ∧ blk.params = cg.curParams ∧
    cg.curBody.reverse <+: blk.body

theorem Good.lk {F : Function} {cg : CG} (h : Good F cg) : Lk F cg := h.1

/-- Backward transfer: `B` after running `m` gives `A` before. -/
def Bk (A B : Function → CG → Prop) {α : Type} (m : CGM α) : Prop :=
  ∀ F cg, B F (m.run cg).2 → A F cg

namespace Bk

variable {A B C : Function → CG → Prop} {α β : Type}

theorem bind {m : CGM α} {k : α → CGM β} (h₁ : Bk A B m) (h₂ : ∀ a, Bk B C (k a)) :
    Bk A C (m >>= k) := fun F cg h => h₁ F cg (h₂ _ F _ h)

theorem pure (a : α) : Bk A A (Pure.pure a : CGM α) := fun _ _ h => h

theorem weak_post {m : CGM α} (h : Bk A Lk m) : Bk A Good m := fun F cg h' => h F cg h'.1

theorem weak_pre {m : CGM α} (h : Bk Good B m) : Bk Lk B m := fun F cg h' => (h F cg h').1

theorem map {m : CGM α} {f : α → β} (h : Bk A B m) : Bk A B (f <$> m) := fun F cg h' =>
  h F cg (by rw [map_run] at h'; exact h')

/-- Actions that only touch counters. -/
theorem of_eq {m : CGM α} (h : ∀ cg, (m.run cg).2.done = cg.done ∧ (m.run cg).2.cur = cg.cur ∧
    (m.run cg).2.curParams = cg.curParams ∧ (m.run cg).2.curBody = cg.curBody ∧
    cg.externs <+: (m.run cg).2.externs ∧ cg.slots <+: (m.run cg).2.slots) :
    Bk Good Good m ∧ Bk Lk Lk m := by
  constructor
  · intro F cg ⟨⟨hd, he, hs⟩, blk, hb, hp, hpre⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h cg
    refine ⟨⟨?_, h5.trans he, h6.trans hs⟩, blk, ?_, ?_, ?_⟩
    · rw [← h1]; exact hd
    · rw [← h2]; exact hb
    · rw [hp, h3]
    · rw [← h4]; exact hpre
  · intro F cg ⟨hd, he, hs⟩
    obtain ⟨h1, -, -, -, h5, h6⟩ := h cg
    exact ⟨by rw [← h1]; exact hd, h5.trans he, h6.trans hs⟩

theorem fresh_gg : Bk Good Good fresh := (of_eq fun _ => by simp [fresh_run]).1
theorem fresh_ll : Bk Lk Lk fresh := (of_eq fun _ => by simp [fresh_run]).2
theorem newBlock_gg : Bk Good Good newBlock := (of_eq fun _ => by simp [newBlock_run]).1
theorem newBlock_ll : Bk Lk Lk newBlock := (of_eq fun _ => by simp [newBlock_run]).2
theorem newSlot_gg (n : Nat) : Bk Good Good (newSlot n) :=
  (of_eq fun _ => by simp [newSlot_run]).1
theorem newSlot_ll (n : Nat) : Bk Lk Lk (newSlot n) := (of_eq fun _ => by simp [newSlot_run]).2

theorem declare_eq (name : String) (sig : Signature) (cg : CG) :
    ((declare name sig).run cg).2.done = cg.done ∧ ((declare name sig).run cg).2.cur = cg.cur ∧
    ((declare name sig).run cg).2.curParams = cg.curParams ∧
    ((declare name sig).run cg).2.curBody = cg.curBody ∧
    cg.externs <+: ((declare name sig).run cg).2.externs ∧
    cg.slots <+: ((declare name sig).run cg).2.slots := by
  rw [declare_run]; split <;> simp

theorem declare_gg (name : String) (sig : Signature) : Bk Good Good (declare name sig) :=
  (of_eq (declare_eq name sig)).1
theorem declare_ll (name : String) (sig : Signature) : Bk Lk Lk (declare name sig) :=
  (of_eq (declare_eq name sig)).2

theorem emitStmt_gg (rs : List ValueId) (i : Inst) : Bk Good Good (emitStmt rs i) := by
  intro F cg ⟨hl, blk, hb, hp, hpre⟩
  refine ⟨hl, blk, hb, hp, ?_⟩
  simp only [emitStmt_run, List.reverse_cons] at hpre
  exact (List.prefix_append _ _).trans hpre

theorem emitStmt_ll (rs : List ValueId) (i : Inst) : Bk Lk Lk (emitStmt rs i) := fun _ _ h => h

theorem inst1_gg (i : Inst) : Bk Good Good (inst1 i) :=
  bind fresh_gg fun _ => bind (emitStmt_gg _ _) fun _ => pure _

theorem inst1_ll (i : Inst) : Bk Lk Lk (inst1 i) :=
  bind fresh_ll fun _ => bind (emitStmt_ll _ _) fun _ => pure _

theorem iconstN_gg (ty : Clif.Ty) (n : Nat) : Bk Good Good (iconstN ty n) := inst1_gg _
theorem iconstN_ll (ty : Clif.Ty) (n : Nat) : Bk Lk Lk (iconstN ty n) := inst1_ll _

theorem terminate_gl (t : Terminator) : Bk Good Lk (terminate t) := by
  intro F cg ⟨hd, he, hs⟩
  simp only [terminate_run] at hd he hs
  have hb := hd _ List.mem_cons_self
  refine ⟨⟨fun b hm => hd b (List.mem_cons_of_mem _ hm), he, hs⟩, curBlock cg t, hb, rfl, ?_⟩
  exact List.prefix_refl _

theorem terminate_ll (t : Terminator) : Bk Lk Lk (terminate t) := fun F cg h =>
  (terminate_gl t F cg h).1

theorem switchTo_lg (b : BlockId) (ps : List (ValueId × Clif.Ty)) : Bk Lk Good (switchTo b ps) :=
  fun _ _ h => h.1

theorem switchTo_ll (b : BlockId) (ps : List (ValueId × Clif.Ty)) : Bk Lk Lk (switchTo b ps) :=
  fun _ _ h => h

theorem gg_of_gl {m : CGM α} (h : Bk Good Lk m) : Bk Good Good m := weak_post h

theorem ll_of_gl {m : CGM α} (h : Bk Good Lk m) : Bk Lk Lk m := weak_pre h

theorem mapM {γ : Type} (f : γ → CGM α) (hf : ∀ c, Bk A A (f c)) :
    ∀ l : List γ, Bk A A (l.mapM f)
  | [] => pure _
  | c :: l => by
    rw [List.mapM_cons]
    exact bind (hf c) fun _ => bind (mapM f hf l) fun _ => pure _

theorem foldlM {γ : Type} (f : α → γ → CGM α) (hf : ∀ a c, Bk A A (f a c)) :
    ∀ (l : List γ) (init : α), Bk A A (l.foldlM f init)
  | [], _ => pure _
  | c :: l, init => by
    rw [List.foldlM_cons]
    exact bind (hf init c) fun a => foldlM f hf l a

theorem forM {γ : Type} (f : γ → CGM PUnit) (hf : ∀ c, Bk A A (f c)) :
    ∀ l : List γ, Bk A A (l.forM f)
  | [] => pure _
  | c :: l => by
    show Bk A A (f c >>= fun _ => l.forM f)
    exact bind (hf c) fun _ => forM f hf l

theorem freshFor_gg (tys : List Clif.Ty) : Bk Good Good (freshFor tys) :=
  mapM _ (fun _ => fresh_gg) tys

theorem freshFor_ll (tys : List Clif.Ty) : Bk Lk Lk (freshFor tys) :=
  mapM _ (fun _ => fresh_ll) tys

theorem callFn_gg (name : String) (sig : Signature) (args : List ValueId) :
    Bk Good Good (callFn name sig args) :=
  bind (declare_gg _ _) fun _ => bind (freshFor_gg _) fun _ =>
    bind (emitStmt_gg _ _) fun _ => pure _

theorem callFn_ll (name : String) (sig : Signature) (args : List ValueId) :
    Bk Lk Lk (callFn name sig args) :=
  bind (declare_ll _ _) fun _ => bind (freshFor_ll _) fun _ =>
    bind (emitStmt_ll _ _) fun _ => pure _

theorem errIf_gg (c : ValueId) (tag : Nat) : Bk Good Good (errIf c tag) :=
  bind (iconstN_gg _ _) fun _ => bind newBlock_gg fun _ =>
    bind (terminate_gl _) fun _ => switchTo_lg _ _

theorem errIf_ll (c : ValueId) (tag : Nat) : Bk Lk Lk (errIf c tag) :=
  bind (iconstN_ll _ _) fun _ => bind newBlock_ll fun _ =>
    bind (terminate_ll _) fun _ => switchTo_ll _ _

theorem selectVals_gg (tys : List Clif.Ty) (c : ValueId) (x y : List ValueId) :
    Bk Good Good (selectVals tys c x y) :=
  bind newBlock_gg fun _ => bind (freshFor_gg _) fun _ =>
    bind (terminate_gl _) fun _ => bind (switchTo_lg _ _) fun _ => pure _

theorem selectVals_ll (tys : List Clif.Ty) (c : ValueId) (x y : List ValueId) :
    Bk Lk Lk (selectVals tys c x y) :=
  bind newBlock_ll fun _ => bind (freshFor_ll _) fun _ =>
    bind (terminate_ll _) fun _ => bind (switchTo_ll _ _) fun _ => pure _

end Bk

/-! ## The machine at a generator position -/

/-- Frame `fr` runs `F` at generator position `cg`: the statements `cg` has emitted into the
open block have executed, and `fr.body`/`fr.term` are the rest of that block in `F`. -/
def At (F : Function) (cg : CG) (fr : Frame) : Prop :=
  fr.func = F ∧ ∃ blk, F.block? cg.cur = some blk ∧ blk.body = cg.curBody.reverse ++ fr.body ∧
    fr.term = blk.term

theorem At.congr {F : Function} {cg : CG} {fr fr' : Frame} (h : At F cg fr)
    (hf : fr'.func = fr.func) (hb : fr'.body = fr.body) (ht : fr'.term = fr.term) :
    At F cg fr' := by
  obtain ⟨h1, blk, h2, h3, h4⟩ := h
  exact ⟨hf.trans h1, blk, h2, by rw [hb]; exact h3, ht.trans h4⟩

theorem At.emit {F : Function} {cg cg' : CG} {fr : Frame} {st : Clif.Stmt}
    (hc : cg'.cur = cg.cur) (hb : cg'.curBody = st :: cg.curBody)
    (hG : Good F cg') (hA : At F cg fr) :
    ∃ rest, fr.body = st :: rest ∧ At F cg' { fr with body := rest } := by
  obtain ⟨hf, blk, hblk, hbody, ht⟩ := hA
  obtain ⟨-, blk', hb', -, hpre⟩ := hG
  rw [hc, hblk] at hb'; cases hb'
  rw [hb, List.reverse_cons, hbody] at hpre
  obtain ⟨rest, hr⟩ := (List.prefix_append_right_inj _).1 hpre
  refine ⟨rest, by simpa using hr.symm, hf, blk, hc ▸ hblk, ?_, ht⟩
  rw [hb, List.reverse_cons, List.append_assoc, List.singleton_append, hbody, ← hr]
  simp

theorem At.term {F : Function} {cg cg' : CG} {fr : Frame} {t : Terminator}
    (hd : curBlock cg t ∈ cg'.done) (hL : Lk F cg') (hA : At F cg fr) :
    fr.body = [] ∧ fr.term = t := by
  obtain ⟨hf, blk, hb, hbody, ht⟩ := hA
  have h := hL.1 _ hd
  simp only [curBlock] at h
  rw [hb] at h; cases h
  simp only at hbody ht
  exact ⟨by simpa using hbody, ht⟩

/-- Entering the open block of `cg` (with nothing emitted yet) puts the machine at `cg`. -/
theorem At.enter {F : Function} {cg : CG} {fr : Frame} {blk : Block} (hf : fr.func = F)
    (hb : F.block? cg.cur = some blk) (hcb : cg.curBody = []) (hbody : fr.body = blk.body)
    (ht : fr.term = blk.term) : At F cg fr :=
  ⟨hf, blk, hb, by simp [hbody, hcb], ht⟩

/-- The open block of `cg`, as a block of `F`. -/
theorem Good.params {F : Function} {cg : CG} (hG : Good F cg) :
    ∃ blk, F.block? cg.cur = some blk ∧ blk.params = cg.curParams := by
  obtain ⟨-, blk, hb, hp, -⟩ := hG
  exact ⟨blk, hb, hp⟩

end Compile.Proof
