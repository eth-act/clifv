import FV.Front.Rename

/-!
# Renaming commutes with one step of the CLIF semantics (T7d)

Helper lemmas for `FV/Front/RenameRun.lean`. `Res.erase`/`StepResult.erase` forget the message
of `stuck` (messages name functions and symbols). Every layer of `FV/Clif/Run.lean` run on the
renamed function/memory/state/environment gives the original result renamed, up to erasure:
`evalInst_ren`, `enterFunc_ren`, `enterBlock_ren`, `returnValues_ren`, `callExternAt_ren`,
`stepCall_ren`, `stepCallIndirect_ren`, `stepReturnCall_ren`, `stepTryCall_ren`,
`stepTryCallIndirect_ren`, `stepTerm_ren`, and **`step_ren`**.
-/

namespace Clif

/-! ## Erasing messages -/

namespace Res

/-- Forget the message of `stuck`. -/
def erase {α : Type} : Res α → Res α
  | .stuck _ => .stuck ""
  | r => r

@[simp] theorem erase_ok {α : Type} (a : α) : (Res.ok a).erase = .ok a := rfl
@[simp] theorem erase_trap {α : Type} (c : TrapCode) : (Res.trap c : Res α).erase = .trap c := rfl
@[simp] theorem erase_stuck {α : Type} (m : String) : (Res.stuck m : Res α).erase = .stuck "" :=
  rfl
@[simp] theorem erase_pure {α : Type} (a : α) : (pure a : Res α).erase = pure a := rfl
@[simp] theorem erase_erase {α : Type} (x : Res α) : x.erase.erase = x.erase := by
  cases x <;> rfl
@[simp] theorem erase_bind {α β : Type} (x : Res α) (f : α → Res β) :
    (x >>= f).erase = x.erase >>= fun a => (f a).erase := by
  cases x <;> rfl
@[simp] theorem erase_map {α β : Type} (f : α → β) (x : Res α) :
    (f <$> x).erase = f <$> x.erase := by
  cases x <;> rfl
@[simp] theorem erase_ofOption {α : Type} (msg : String) (o : Option α) :
    (ofOption msg o).erase = ofOption "" o := by
  cases o <;> rfl
@[simp] theorem erase_check (b : Bool) (msg : String) : (check b msg).erase = check b "" := by
  cases b <;> rfl
@[simp] theorem erase_ofExcept {α : Type} (e : Except TrapCode α) :
    (ofExcept e).erase = ofExcept e := by
  cases e <;> rfl

@[simp] theorem map_ok {α β : Type} (f : α → β) (a : α) : f <$> Res.ok a = .ok (f a) := rfl
@[simp] theorem map_trap {α β : Type} (f : α → β) (c : TrapCode) :
    f <$> (Res.trap c : Res α) = .trap c := rfl
@[simp] theorem map_stuck {α β : Type} (f : α → β) (m : String) :
    f <$> (Res.stuck m : Res α) = .stuck m := rfl
@[simp] theorem erase_ite {α : Type} (c : Prop) [Decidable c] (x y : Res α) :
    (if c then x else y).erase = if c then x.erase else y.erase := by
  split <;> rfl
@[simp] theorem map_ite {α β : Type} (f : α → β) (c : Prop) [Decidable c] (x y : Res α) :
    f <$> (if c then x else y) = if c then f <$> x else f <$> y := by
  split <;> rfl
@[simp] theorem ofOption_map {α β : Type} (msg : String) (f : α → β) (o : Option α) :
    ofOption msg (o.map f) = f <$> ofOption msg o := by
  cases o <;> rfl

end Res

/-! ## Names -/

theorem List.lookup_map_snd {α β γ : Type} [BEq α] (f : β → γ) (l : List (α × β)) (k : α) :
    (l.map fun p => (p.1, f p.2)).lookup k = (l.lookup k).map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [List.map_cons, List.lookup_cons]
    cases k == a <;> simp [ih]

@[simp] theorem ExtFunc.rename_name (g : String → String) (e : ExtFunc) :
    (e.rename g).name = g e.name := rfl
@[simp] theorem ExtFunc.rename_sig (g : String → String) (e : ExtFunc) :
    (e.rename g).sig = e.sig := rfl

namespace Function
variable (g : String → String) (f : Function)
@[simp] theorem rename_name : (f.rename g).name = g f.name := rfl
@[simp] theorem rename_sig : (f.rename g).sig = f.sig := rfl
@[simp] theorem rename_slots : (f.rename g).slots = f.slots := rfl
@[simp] theorem rename_sigDecls : (f.rename g).sigDecls = f.sigDecls := rfl
@[simp] theorem rename_blocks : (f.rename g).blocks = f.blocks := rfl
@[simp] theorem rename_block? (b : BlockId) : (f.rename g).block? b = f.block? b := rfl
@[simp] theorem rename_entry? : (f.rename g).entry? = f.entry? := rfl
@[simp] theorem rename_freshValue : (f.rename g).freshValue = f.freshValue := rfl
@[simp] theorem rename_extern? (r : FnRef) :
    (f.rename g).extern? r = (f.extern? r).map (ExtFunc.rename g) :=
  List.lookup_map_snd (ExtFunc.rename g) f.externs r
@[simp] theorem rename_globals_lookup (gv : Nat) :
    (f.rename g).globals.lookup gv = (f.globals.lookup gv).map (GlobalValue.rename g) :=
  List.lookup_map_snd (GlobalValue.rename g) f.globals gv
end Function

namespace Frame
variable (σ : Ren) (fr : Frame)
@[simp] theorem ren_func : (fr.ren σ).func = fr.func.rename σ.fwd := rfl
@[simp] theorem ren_regs : (fr.ren σ).regs = fr.regs := rfl
@[simp] theorem ren_slots : (fr.ren σ).slots = fr.slots := rfl
@[simp] theorem ren_body : (fr.ren σ).body = fr.body := rfl
@[simp] theorem ren_term : (fr.ren σ).term = fr.term := rfl
@[simp] theorem ren_get (x : ValueId) : (fr.ren σ).get x = fr.get x := rfl
@[simp] theorem ren_getAs (x : ValueId) (ty : Ty) : (fr.ren σ).getAs x ty = fr.getAs x ty := rfl
@[simp] theorem ren_getMany (xs : List ValueId) : (fr.ren σ).getMany xs = fr.getMany xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [getMany, ren_get, ih]
end Frame

namespace Mem
variable (σ : Ren) (m : Mem)
@[simp] theorem ren_allocs : (m.ren σ).allocs = m.allocs := rfl
@[simp] theorem ren_bytes : (m.ren σ).bytes = m.bytes := rfl
@[simp] theorem ren_next : (m.ren σ).next = m.next := rfl
@[simp] theorem ren_symbols (n : String) : (m.ren σ).symbols n = m.symbols (σ.bwd n) := rfl
@[simp] theorem ren_load (flags : MemFlags) (addr n w : Nat) :
    (m.ren σ).load flags addr n w = m.load flags addr n w := rfl
@[simp] theorem ren_writeBits {w : Nat} (big : Bool) (addr n : Nat) (x : BitVec w) :
    (m.ren σ).writeBits big addr n x = (m.writeBits big addr n x).ren σ := rfl
@[simp] theorem ren_store {w : Nat} (flags : MemFlags) (addr n : Nat) (x : BitVec w) :
    (m.ren σ).store flags addr n x = Mem.ren σ <$> m.store flags addr n x := by
  show (m.checkAccess flags addr n >>= fun _ => _) = _
  simp only [store, map_bind, map_pure]
  rfl
@[simp] theorem ren_place_none (h : m.place = none) : (m.ren σ).place = none := by
  simp [Mem.ren, h]
@[simp] theorem ren_alloc (size align : Nat) :
    (m.ren σ).alloc size align = ((m.alloc size align).1, (m.alloc size align).2.ren σ) := rfl
@[simp] theorem ren_allocAt (base size : Nat) :
    (m.ren σ).allocAt base size = (m.allocAt base size).ren σ := rfl
@[simp] theorem ren_free (bases : List Nat) : (m.ren σ).free bases = (m.free bases).ren σ := rfl
@[simp] theorem ren_leave : (m.ren σ).leave = m.leave.ren σ := by
  unfold leave
  cases h : m.place <;> simp [Mem.ren, h]
@[simp] theorem ren_ren_symm : (m.ren σ).ren σ.symm = m := by
  obtain ⟨allocs, bytes, next, symbols, place⟩ := m
  cases place <;> simp [Mem.ren, σ.bwd_fwd]
end Mem

@[simp] theorem Ren.fwd_beq (σ : Ren) (a b : String) : (σ.fwd a == σ.fwd b) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp [σ.fwd_eq_iff]

namespace Env
variable (σ : Ren) (E : Env)
@[simp] theorem ren_extern (n : String) :
    (E.ren σ).extern n = (E.extern (σ.bwd n)).map fun h vals m => (h vals (m.ren σ.symm)).ren σ :=
  rfl
@[simp] theorem ren_names : (E.ren σ).names = E.names.map σ.fwd := rfl
@[simp] theorem ren_sigOf (n : String) : (E.ren σ).sigOf n = E.sigOf (σ.bwd n) := rfl
end Env

@[simp] theorem Frame.ren_mk (σ : Ren) (f : Function) (regs : Regs) (slots : List (SlotId × Nat))
    (body : List Stmt) (term : Terminator) :
    Frame.ren σ ⟨f, regs, slots, body, term⟩ = ⟨f.rename σ.fwd, regs, slots, body, term⟩ := rfl

namespace State
variable (σ : Ren) (s : State)
@[simp] theorem ren_frame : (s.ren σ).frame = s.frame.ren σ := rfl
@[simp] theorem ren_callers : (s.ren σ).callers = s.callers.map fun c => (c.1.ren σ, c.2) := rfl
@[simp] theorem ren_mem : (s.ren σ).mem = s.mem.ren σ := rfl
end State

theorem Program.rename_func? (σ : Ren) (p : Program) (n : String) :
    (p.rename σ.fwd).func? (σ.fwd n) = (p.func? n).map (Function.rename σ.fwd) := by
  simp [Program.func?, Program.rename, List.find?_map, Function.comp_def]

theorem Program.rename_externNames (σ : Ren) (p : Program) :
    (p.rename σ.fwd).externNames = p.externNames.map σ.fwd := by
  simp [Program.externNames, Program.rename, Function.rename, List.map_flatMap, List.flatMap_map,
    Function.comp_def]

/-! ## Steps -/

/-- Rename the state or memory of a step result. -/
def StepResult.ren (σ : Ren) : StepResult → StepResult
  | .next s => .next (s.ren σ)
  | .done vals m => .done vals (m.ren σ)
  | r => r

/-- Forget the message of `stuck`. -/
def StepResult.erase : StepResult → StepResult
  | .stuck _ => .stuck ""
  | r => r

namespace StepResult
variable (σ : Ren)
@[simp] theorem ren_next (s : State) : (StepResult.next s).ren σ = .next (s.ren σ) := rfl
@[simp] theorem ren_done (vals : List Val) (m : Mem) :
    (StepResult.done vals m).ren σ = .done vals (m.ren σ) := rfl
@[simp] theorem ren_trapped (c : TrapCode) : (StepResult.trapped c).ren σ = .trapped c := rfl
@[simp] theorem ren_stuck (msg : String) : (StepResult.stuck msg).ren σ = .stuck msg := rfl
@[simp] theorem erase_stuck (msg : String) : (StepResult.stuck msg).erase = .stuck "" := rfl
@[simp] theorem erase_next (s : State) : (StepResult.next s).erase = .next s := rfl
@[simp] theorem erase_done (vals : List Val) (m : Mem) :
    (StepResult.done vals m).erase = .done vals m := rfl
@[simp] theorem erase_trapped (c : TrapCode) : (StepResult.trapped c).erase = .trapped c := rfl

/-- `ofRes` of related results with related continuations. -/
theorem ofRes_ren {α β : Type} {r : Res α} {r' : Res β} (f : α → β) {k : α → StepResult}
    {k' : β → StepResult} (hr : r'.erase = (f <$> r).erase)
    (hk : ∀ a, (k' (f a)).erase = ((k a).ren σ).erase) :
    (StepResult.ofRes r' k').erase = ((StepResult.ofRes r k).ren σ).erase := by
  cases r <;> cases r' <;> simp_all [Res.erase] <;> rfl
end StepResult

theorem bumpSlots_ren (σ : Ren) (slots : List (SlotId × StackSlot)) (m : Mem) :
    bumpSlots slots (m.ren σ) = ((bumpSlots slots m).1, (bumpSlots slots m).2.ren σ) := by
  unfold bumpSlots
  suffices ∀ acc : List (SlotId × Nat) × Mem, slots.foldl _ (acc.1, acc.2.ren σ) =
      ((slots.foldl _ acc).1, (slots.foldl _ acc).2.ren σ) from this ([], m)
  induction slots with
  | nil => intro; rfl
  | cons sl slots ih =>
    intro ⟨a, m⟩
    exact ih (a ++ [(sl.1, (m.alloc sl.2.size (sl.2.align.getD 1)).1)],
      (m.alloc sl.2.size (sl.2.align.getD 1)).2)

theorem placeSlots_ren (σ : Ren) (slots : List (SlotId × StackSlot)) (sp : BitVec 64)
    (off : SlotId → Nat) (m : Mem) :
    placeSlots slots sp off (m.ren σ) =
      ((placeSlots slots sp off m).1, (placeSlots slots sp off m).2.ren σ) := by
  unfold placeSlots
  suffices ∀ acc : List (SlotId × Nat) × Mem, slots.foldl _ (acc.1, acc.2.ren σ) =
      ((slots.foldl _ acc).1, (slots.foldl _ acc).2.ren σ) from this ([], m)
  induction slots with
  | nil => intro; rfl
  | cons sl slots ih =>
    intro ⟨a, m⟩
    exact ih (a ++ [(sl.1, sp.toNat + off sl.1)], m.allocAt (sp.toNat + off sl.1) sl.2.size)

theorem fillSlots_ren (σ : Ren) (slots : List (SlotId × StackSlot)) (sp : BitVec 64)
    (off : SlotId → Nat) (b : Nat → BitVec 8) :
    ∀ m : Mem, fillSlots slots sp off b (m.ren σ) = (fillSlots slots sp off b m).ren σ := by
  unfold fillSlots
  induction slots with
  | nil => intro; rfl
  | cons s ss ih =>
    intro m
    simp only [List.foldl_cons]
    exact ih (m.fillAt (sp.toNat + off s.1) s.2.size b)

theorem initSlots_ren (σ : Ren) (slots : List (SlotId × StackSlot)) (sp : BitVec 64)
    (off : SlotId → Nat) (ini : Option SlotInit) (r : List (SlotId × Nat) × Mem) :
    initSlots slots sp off ini (r.1, r.2.ren σ) =
      ((initSlots slots sp off ini r).1, (initSlots slots sp off ini r).2.ren σ) := by
  obtain ⟨l, ⟨al, by0, nx, sy, pl⟩⟩ := r
  cases ini with
  | none => rfl
  | some ini =>
    by_cases hs : slots.isEmpty
    · simp only [initSlots, hs, if_true]
    · simp only [initSlots, hs, Bool.false_eq_true, if_false, Prod.mk.injEq, true_and]
      rw [← fillSlots_ren]
      cases pl <;> rfl

theorem enterSlots_ren (σ : Ren) (f : Function) (m : Mem) :
    enterSlots (f.rename σ.fwd) (m.ren σ) = ((enterSlots f m).1, (enterSlots f m).2.ren σ) := by
  unfold enterSlots
  cases hp : m.place with
  | none => simp only [Mem.ren_place_none σ m hp, Function.rename_slots]; exact bumpSlots_ren ..
  | some pl =>
    have h : (m.ren σ).place = some { pl with frame := fun n => pl.frame (σ.bwd n) } := by
      simp [Mem.ren, hp]
    simp only [h, Function.rename_name, σ.bwd_fwd, Function.rename_slots]
    cases pl.frame f.name with
    | none => exact bumpSlots_ren σ f.slots { m with place := some { pl with sps := _ } }
    | some p =>
      exact (congrArg (initSlots f.slots _ p.2 pl.init)
        (placeSlots_ren σ f.slots _ p.2 { m with place := some { pl with sps := _ } })).trans
        (initSlots_ren σ f.slots _ p.2 pl.init _)

theorem enterFunc_ren (σ : Ren) (f : Function) (args : List Val) (m : Mem) :
    (enterFunc (f.rename σ.fwd) args (m.ren σ)).erase =
      ((fun r : Frame × Mem => (r.1.ren σ, r.2.ren σ)) <$> enterFunc f args m).erase := by
  unfold enterFunc
  rw [enterSlots_ren]
  generalize enterSlots f m = q
  obtain ⟨sl, m'⟩ := q
  simp [checkTys, map_bind]

@[simp] theorem continueWith_ren (σ : Ren) (s : State) (rest : List Stmt) (results : List ValueId)
    (vals : List Val) (m : Mem) :
    continueWith (s.ren σ) rest results vals (m.ren σ) =
      (continueWith s rest results vals m).ren σ := by
  unfold continueWith
  simp only [State.ren_frame, Frame.ren_regs]
  cases s.frame.regs.setMany results vals <;> rfl

theorem enterBlock_ren (σ : Ren) (fr : Frame) (bc : BlockCall) :
    enterBlock (fr.ren σ) bc = Frame.ren σ <$> enterBlock fr bc := by
  unfold enterBlock
  simp [map_bind]

theorem returnValues_ren (σ : Ren) (s : State) (vals : List Val) (m : Mem) :
    (returnValues (s.ren σ) vals (m.ren σ)).erase = ((returnValues s vals m).ren σ).erase := by
  unfold returnValues
  apply StepResult.ofRes_ren σ id
  · simp [checkTys]
  · intro _
    simp only [State.ren_callers, State.ren_frame, Frame.ren_slots, Mem.ren_free, Mem.ren_leave]
    cases s.callers with
    | nil => rfl
    | cons c callers =>
      obtain ⟨caller, results⟩ := c
      simp only [List.map_cons, Frame.ren_regs]
      cases caller.regs.setMany results vals <;> rfl

theorem evalInst_ren (σ : Ren) (fr : Frame) (m : Mem) (i : Inst) :
    (evalInst (fr.ren σ) (m.ren σ) i).erase =
      ((fun r : List Val × Mem => (r.1, r.2.ren σ)) <$> evalInst fr m i).erase := by
  cases i
  case extend op _ _ => cases op <;> simp [evalInst, map_bind]
  case symbolValue ty gv =>
    cases h : fr.func.globals.lookup gv with
    | none => simp [evalInst, h]
    | some g => cases g <;> simp [evalInst, h, GlobalValue.rename, map_bind, σ.bwd_fwd]
  case tlsValue ty gv =>
    cases h : fr.func.globals.lookup gv with
    | none => simp [evalInst, h]
    | some g => cases g <;> simp [evalInst, h, GlobalValue.rename, map_bind, σ.bwd_fwd]
  case bitcast =>
    simp [evalInst, map_bind, bind_map_left, σ.bwd_fwd]
    congr 1; funext a; split <;> rfl
  all_goals simp [evalInst, map_bind, bind_map_left, σ.bwd_fwd]

namespace Outcome
variable (σ : Ren)
@[simp] theorem ren_returned (vals : List Val) (m : Mem) :
    (Outcome.returned vals m).ren σ = .returned vals (m.ren σ) := rfl
@[simp] theorem ren_trapped (c : TrapCode) : (Outcome.trapped c).ren σ = .trapped c := rfl
@[simp] theorem ren_stuck (msg : String) : (Outcome.stuck msg).ren σ = .stuck msg := rfl
@[simp] theorem ren_outOfFuel : Outcome.outOfFuel.ren σ = .outOfFuel := rfl
@[simp] theorem erase_returned (vals : List Val) (m : Mem) :
    (Outcome.returned vals m).erase = .returned vals m := rfl
@[simp] theorem erase_trapped (c : TrapCode) : (Outcome.trapped c).erase = .trapped c := rfl
@[simp] theorem erase_stuck (msg : String) : (Outcome.stuck msg).erase = .stuck "" := rfl
@[simp] theorem erase_outOfFuel : Outcome.outOfFuel.erase = .outOfFuel := rfl
end Outcome

theorem StepResult.ite_ren (σ : Ren) {c : Prop} {_ : Decidable c} {x y x' y' : StepResult}
    (h : x'.erase = (x.ren σ).erase) (h' : y'.erase = (y.ren σ).erase) :
    (if c then x' else y').erase = ((if c then x else y).ren σ).erase := by
  split <;> assumption

theorem Program.rename_find?_symbols (σ : Ren) (p : Program) (m : Mem) (addr : Nat) :
    (p.rename σ.fwd).funcs.find? (fun f => (m.ren σ).symbols f.name == some addr) =
      (p.funcs.find? fun f => m.symbols f.name == some addr).map (Function.rename σ.fwd) := by
  simp [Program.rename, List.find?_map, Function.comp_def, σ.bwd_fwd]

theorem callExternAt_ren (σ : Ren) (E : Env) (p : Program) (m : Mem) (declared : Signature)
    (addr : Nat) (vals : List Val) :
    (callExternAt (E.ren σ) (p.rename σ.fwd) (m.ren σ) declared addr vals).erase =
      ((fun r : List Val × Mem => (r.1, r.2.ren σ)) <$>
        callExternAt E p m declared addr vals).erase := by
  unfold callExternAt
  have hfind : ((E.ren σ).names ++ (p.rename σ.fwd).externNames).find?
      (fun n => (m.ren σ).symbols n == some addr) =
      ((E.names ++ p.externNames).find? fun n => m.symbols n == some addr).map σ.fwd := by
    simp [Program.rename_externNames, ← List.map_append, List.find?_map, Function.comp_def,
      σ.bwd_fwd]
  rw [hfind]
  cases h1 : (E.names ++ p.externNames).find? fun n => m.symbols n == some addr with
  | none => rfl
  | some name =>
    simp only [Option.map_some, Res.ofOption_some, Res.ok_bind, Env.ren_extern, σ.bwd_fwd,
      Env.ren_sigOf]
    cases h2 : E.extern name with
    | none => rfl
    | some g =>
      simp only [Option.map_some, Res.ofOption_some, Res.ok_bind, Mem.ren_ren_symm]
      cases h3 : g vals m <;> simp [checkTys, map_bind, Outcome.ren]

theorem stepCall_ren (σ : Ren) (E : Env) (p : Program) (s : State) (rest : List Stmt)
    (results : List ValueId) (fn : FnRef) (args : List ValueId) :
    (stepCall (E.ren σ) (p.rename σ.fwd) (s.ren σ) rest results fn args).erase =
      ((stepCall E p s rest results fn args).ren σ).erase := by
  unfold stepCall
  apply StepResult.ofRes_ren σ (fun r : ExtFunc × List Val => (r.1.rename σ.fwd, r.2))
  · simp [checkTys, map_bind, bind_map_left]
  · rintro ⟨ext, vals⟩
    simp only [ExtFunc.rename_name, ExtFunc.rename_sig, Program.rename_func?]
    cases hf : p.func? ext.name with
    | some callee =>
      simp only [Option.map_some, Function.rename_sig]
      refine StepResult.ite_ren σ ?_ rfl
      apply StepResult.ofRes_ren σ (fun r : Frame × Mem => (r.1.ren σ, r.2.ren σ))
      · exact enterFunc_ren ..
      · intro _; rfl
    | none =>
      simp only [Option.map_none, Env.ren_extern, σ.bwd_fwd]
      cases he : E.extern ext.name with
      | none => rfl
      | some h =>
        simp only [Option.map_some, State.ren_mem, Mem.ren_ren_symm]
        cases h vals s.mem <;> simp [Outcome.ren] <;> exact StepResult.ite_ren σ rfl rfl

theorem stepCallIndirect_ren (σ : Ren) (E : Env) (p : Program) (s : State) (rest : List Stmt)
    (results : List ValueId) (sig : Nat) (callee : ValueId) (args : List ValueId) :
    (stepCallIndirect (E.ren σ) (p.rename σ.fwd) (s.ren σ) rest results sig callee args).erase =
      ((stepCallIndirect E p s rest results sig callee args).ren σ).erase := by
  unfold stepCallIndirect
  apply StepResult.ofRes_ren σ id
  · simp [map_bind]
  · rintro ⟨declared, addr, vals⟩
    simp only [id, State.ren_mem, Program.rename_find?_symbols]
    cases hf : p.funcs.find? (fun f => s.mem.symbols f.name == some addr) with
    | some target =>
      simp only [Option.map_some, Function.rename_sig, Function.rename_name]
      refine StepResult.ite_ren σ ?_ rfl
      apply StepResult.ofRes_ren σ (fun r : Frame × Mem => (r.1.ren σ, r.2.ren σ))
      · exact enterFunc_ren ..
      · intro _; rfl
    | none =>
      simp only [Option.map_none]
      apply StepResult.ofRes_ren σ (fun r : List Val × Mem => (r.1, r.2.ren σ))
      · exact callExternAt_ren ..
      · rintro ⟨rvals, mem'⟩; simp only [continueWith_ren]

theorem stepReturnCall_ren (σ : Ren) (E : Env) (p : Program) (s : State) (fn : FnRef)
    (args : List ValueId) :
    (stepReturnCall (E.ren σ) (p.rename σ.fwd) (s.ren σ) fn args).erase =
      ((stepReturnCall E p s fn args).ren σ).erase := by
  unfold stepReturnCall
  apply StepResult.ofRes_ren σ (fun r : ExtFunc × List Val => (r.1.rename σ.fwd, r.2))
  · simp [checkTys, map_bind, bind_map_left]
  · rintro ⟨ext, vals⟩
    simp only [ExtFunc.rename_name, ExtFunc.rename_sig, Program.rename_func?]
    cases hf : p.func? ext.name with
    | some callee =>
      simp only [Option.map_some, Function.rename_sig, State.ren_mem, State.ren_frame,
        Frame.ren_slots, Mem.ren_free, Mem.ren_leave]
      refine StepResult.ite_ren σ ?_ rfl
      apply StepResult.ofRes_ren σ (fun r : Frame × Mem => (r.1.ren σ, r.2.ren σ))
      · exact enterFunc_ren ..
      · intro _; rfl
    | none =>
      simp only [Option.map_none, Env.ren_extern, σ.bwd_fwd]
      cases he : E.extern ext.name with
      | none => rfl
      | some h =>
        simp only [Option.map_some, State.ren_mem, Mem.ren_ren_symm]
        cases h vals s.mem with
        | returned rvals mem' => exact returnValues_ren ..
        | _ => rfl

theorem stepTryCall_ren (σ : Ren) (E : Env) (p : Program) (s : State) (fn : FnRef)
    (args : List ValueId) (et : ExnTable) :
    (stepTryCall (E.ren σ) (p.rename σ.fwd) (s.ren σ) fn args et).erase =
      ((stepTryCall E p s fn args et).ren σ).erase := by
  unfold stepTryCall
  apply StepResult.ofRes_ren σ id
  · simp [map_bind, bind_map_left]
  · rintro ⟨n, base, bc⟩
    exact stepCall_ren σ E p { s with frame := { s.frame with body := [], term := .jump bc } } []
      _ fn args

theorem stepTryCallIndirect_ren (σ : Ren) (E : Env) (p : Program) (s : State) (callee : ValueId)
    (args : List ValueId) (et : ExnTable) :
    (stepTryCallIndirect (E.ren σ) (p.rename σ.fwd) (s.ren σ) callee args et).erase =
      ((stepTryCallIndirect E p s callee args et).ren σ).erase := by
  unfold stepTryCallIndirect
  apply StepResult.ofRes_ren σ id
  · simp [map_bind]
  · rintro ⟨n, base, bc⟩
    exact stepCallIndirect_ren σ E p
      { s with frame := { s.frame with body := [], term := .jump bc } } [] _ et.sig callee args

theorem stepTerm_ren (σ : Ren) (E : Env) (p : Program) (s : State) (t : Terminator) :
    (stepTerm (E.ren σ) (p.rename σ.fwd) (s.ren σ) t).erase =
      ((stepTerm E p s t).ren σ).erase := by
  cases t with
  | jump dest =>
    apply StepResult.ofRes_ren σ (Frame.ren σ)
    · rw [State.ren_frame, enterBlock_ren]
    · intro _; rfl
  | brif c t e =>
    apply StepResult.ofRes_ren σ id
    · simp
    · intro _
      apply StepResult.ofRes_ren σ (Frame.ren σ)
      · rw [State.ren_frame, enterBlock_ren]; rfl
      · intro _; rfl
  | brTable x dflt table =>
    apply StepResult.ofRes_ren σ id
    · simp
    · intro _
      apply StepResult.ofRes_ren σ (Frame.ren σ)
      · rw [State.ren_frame, enterBlock_ren]; rfl
      · intro _; rfl
  | ret xs =>
    apply StepResult.ofRes_ren σ id
    · simp
    · intro vals; exact returnValues_ren ..
  | returnCall fn args => exact stepReturnCall_ren ..
  | trap code => rfl
  | tryCall fn args et => exact stepTryCall_ren ..
  | tryCallIndirect callee args et => exact stepTryCallIndirect_ren ..

/-- **Renaming commutes with a step**, up to the messages of `stuck`. -/
theorem step_ren (σ : Ren) (E : Env) (p : Program) (s : State) :
    (step (E.ren σ) (p.rename σ.fwd) (s.ren σ)).erase = ((step E p s).ren σ).erase := by
  cases hb : s.frame.body with
  | nil =>
    rw [step_term _ _ _ (by simpa using hb), step_term _ _ _ hb]
    exact stepTerm_ren ..
  | cons st rest =>
    have hb' : (s.ren σ).frame.body = st :: rest := by simpa using hb
    obtain ⟨results, inst⟩ := st
    by_cases hc : ∃ fn args, inst = .call fn args
    · obtain ⟨fn, args, rfl⟩ := hc
      rw [step_call _ _ _ _ _ _ _ hb', step_call _ _ _ _ _ _ _ hb]
      exact stepCall_ren ..
    by_cases hci : ∃ sig callee args, inst = .callIndirect sig callee args
    · obtain ⟨sig, callee, args, rfl⟩ := hci
      simp only [step, hb, hb']
      exact stepCallIndirect_ren ..
    have hc' : ∀ fn args, inst ≠ .call fn args := fun fn args h => hc ⟨fn, args, h⟩
    have hci' : ∀ sig callee args, inst ≠ .callIndirect sig callee args :=
      fun sig callee args h => hci ⟨sig, callee, args, h⟩
    rw [step_inst _ _ _ _ _ hb' hc' hci', step_inst _ _ _ _ _ hb hc' hci']
    apply StepResult.ofRes_ren σ (fun r : List Val × Mem => (r.1, r.2.ren σ))
    · exact evalInst_ren ..
    · rintro ⟨vals, mem⟩; simp only [continueWith_ren]
end Clif
