import FV.E2E.LinkPlaceB

/-! # A run depends on the slot-byte table only through the entries it uses (SEM1 #537)

Under the slot-byte oracle (`Place.init = some ini`) the `k`-th placed activation with slots of a
run starts with the bytes `ini.bytes k` (`Clif.initSlots`); nothing else reads the table. So two
tables that agree on the entries a run fills give the same run: **`runLoop_withTable`**: a
returning run from a state whose table is replaced by `b` (`Mem.withTable`, counter, stack
pointers and frames kept) returns the same values and the same memory up to the table, when `b`
agrees with the run's table on the entries `ini.next + 1, …, ini.next + E` of its `E` placed
activations with slots (`NextAdv`, `runLoop_placeB`), and the externs commute with the
replacement (`EnvTable`, e.g. `Env.empty`).

This makes a run under a table that is known only on these entries (the machine's own table
`LinkSys.iniOf`, read off the machine's run) computable: replace it by a computable table that
agrees there.

* `Mem.withTable`, `State.withTable`, `StepResult.withTable`, `Outcome.withTable`;
* `Mem.store_withTable`, `evalInst_withTable`, `enterSlots_withTable`, `enterFunc_withTable`,
  `returnValues_withTable`, `step_withTable` (one step: the same step, given the agreement at the
  entry it fills, if any);
* **`runLoop_withTable`**, **`runWith_withTable`** (from an entry `initState`).
-/

namespace Clif
open Opt

/-- The memory `m` with the byte table of its slot-byte oracle replaced by `b` (the counter, the
stack pointers and the frames kept; no change without the oracle). -/
def Mem.withTable (b : Nat → Nat → BitVec 8) (m : Mem) : Mem :=
  { m with place := m.place.map fun pl => { pl with init := pl.init.map fun i => { i with bytes := b } } }

def State.withTable (b : Nat → Nat → BitVec 8) (s : State) : State := { s with mem := s.mem.withTable b }

def StepResult.withTable (b : Nat → Nat → BitVec 8) : StepResult → StepResult
  | .next s => .next (s.withTable b)
  | .done v m => .done v (m.withTable b)
  | .trapped c => .trapped c
  | .stuck m => .stuck m

def Outcome.withTable (b : Nat → Nat → BitVec 8) : Outcome → Outcome
  | .returned v m => .returned v (m.withTable b)
  | .trapped c => .trapped c
  | .stuck m => .stuck m
  | .outOfFuel => .outOfFuel

/-- **The externs commute with replacing the table** (they do not read it). -/
def EnvTable (env : Env) : Prop :=
  ∀ n g, env.extern n = some g → ∀ b vals m, g vals (m.withTable b) = (g vals m).withTable b

theorem envTable_empty : EnvTable Env.empty := fun _ _ h => by cases h

namespace Mem

variable (b : Nat → Nat → BitVec 8)

@[simp] theorem withTable_bytes (m : Mem) : (m.withTable b).bytes = m.bytes := rfl
@[simp] theorem withTable_allocs (m : Mem) : (m.withTable b).allocs = m.allocs := rfl
@[simp] theorem withTable_symbols (m : Mem) : (m.withTable b).symbols = m.symbols := rfl
@[simp] theorem withTable_next (m : Mem) : (m.withTable b).next = m.next := rfl

theorem load_withTable (m : Mem) (fl : MemFlags) (a n w : Nat) :
    (m.withTable b).load fl a n w = m.load fl a n w := rfl

theorem store_withTable {w : Nat} (m : Mem) (fl : MemFlags) (a n : Nat) (x : BitVec w) :
    (m.withTable b).store fl a n x = Mem.withTable b <$> m.store fl a n x := by
  simp only [Mem.store, map_bind, map_pure]
  rfl

end Mem
@[simp] theorem Res.map_ok' {α β : Type} (f : α → β) (a : α) : f <$> Res.ok a = Res.ok (f a) := rfl
@[simp] theorem Res.map_trap' {α β : Type} (f : α → β) (c : TrapCode) :
    f <$> (Res.trap c : Res α) = Res.trap c := rfl
@[simp] theorem Res.map_stuck' {α β : Type} (f : α → β) (s : String) :
    f <$> (Res.stuck s : Res α) = Res.stuck s := rfl

theorem evalInst_withTable (b : Nat → Nat → BitVec 8) (fr : Frame) (m : Mem) (i : Inst) :
    evalInst fr (m.withTable b) i = (fun r => (r.1, r.2.withTable b)) <$> evalInst fr m i := by
  cases i <;> simp [evalInst, map_bind, Mem.load_withTable, Mem.store_withTable, apply_ite] <;>
    (try split) <;> (try simp) <;> (congr 1; funext a; split <;> simp)

section slots
variable (b : Nat → Nat → BitVec 8)

theorem bumpSlots_withTable (slots : List (SlotId × StackSlot)) (m : Mem) :
    bumpSlots slots (m.withTable b) = ((bumpSlots slots m).1, (bumpSlots slots m).2.withTable b) := by
  unfold bumpSlots
  suffices H : ∀ (ss : List (SlotId × StackSlot)) (l : List (SlotId × Nat)) (m : Mem),
      ss.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
        let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
        (acc.1 ++ [(s.1, base)], m)) (l, m.withTable b) =
      ((ss.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
        let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
        (acc.1 ++ [(s.1, base)], m)) (l, m)).1,
       (ss.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
        let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
        (acc.1 ++ [(s.1, base)], m)) (l, m)).2.withTable b) from H slots [] m
  intro ss
  induction ss with
  | nil => intro l m; rfl
  | cons s ss ih =>
    intro l m
    exact ih (l ++ [(s.1, (m.alloc s.2.size (s.2.align.getD 1)).1)]) (m.alloc s.2.size (s.2.align.getD 1)).2

theorem placeSlots_withTable (slots : List (SlotId × StackSlot)) (sp : BitVec 64)
    (off : SlotId → Nat) (m : Mem) :
    placeSlots slots sp off (m.withTable b) =
      ((placeSlots slots sp off m).1, (placeSlots slots sp off m).2.withTable b) := by
  unfold placeSlots
  suffices H : ∀ (ss : List (SlotId × StackSlot)) (l : List (SlotId × Nat)) (m : Mem),
      ss.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
        (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size))
        (l, m.withTable b) =
      ((ss.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
        (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size)) (l, m)).1,
       (ss.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
        (acc.1 ++ [(s.1, sp.toNat + off s.1)], acc.2.allocAt (sp.toNat + off s.1) s.2.size))
        (l, m)).2.withTable b) from H slots [] m
  intro ss
  induction ss with
  | nil => intro l m; rfl
  | cons s ss ih =>
    intro l m
    exact ih (l ++ [(s.1, sp.toNat + off s.1)]) (m.allocAt (sp.toNat + off s.1) s.2.size)

theorem fillSlots_withTable (slots : List (SlotId × StackSlot)) (sp : BitVec 64)
    (off : SlotId → Nat) (f : Nat → BitVec 8) (m : Mem) :
    fillSlots slots sp off f (m.withTable b) = (fillSlots slots sp off f m).withTable b := by
  unfold fillSlots
  induction slots generalizing m with
  | nil => rfl
  | cons s ss ih => exact ih (m.fillAt (sp.toNat + off s.1) s.2.size f)

theorem placeSlots_place (slots : List (SlotId × StackSlot)) (sp : BitVec 64)
    (off : SlotId → Nat) (m : Mem) : (placeSlots slots sp off m).2.place = m.place :=
  (placeSlots_facts sp off slots ([], m)).1

/-- **Entering a function under a replaced table**: the same slots and memory up to the table,
when the replacement agrees with the table at the entry the activation fills, if it fills one. -/
theorem enterSlots_withTable (f : Function) (m : Mem)
    (hA : ∀ pl ini, m.place = some pl → pl.init = some ini →
      (enterSlots f m).2.place.bind (·.init) = some ini.succ →
      b (ini.next + 1) = ini.bytes (ini.next + 1)) :
    enterSlots f (m.withTable b) = ((enterSlots f m).1, (enterSlots f m).2.withTable b) := by
  cases hp : m.place with
  | none =>
    have hp' : (m.withTable b).place = none := by simp only [Mem.withTable, hp, Option.map_none]
    simp only [enterSlots, hp, hp']
    exact bumpSlots_withTable b f.slots m
  | some pl =>
    have hp' : (m.withTable b).place =
        some { pl with init := pl.init.map (fun i => { i with bytes := b }) } := by
      simp only [Mem.withTable, hp, Option.map_some]
    cases hf : pl.frame f.name with
    | none =>
      simp only [enterSlots, hp, hp', hf]
      exact bumpSlots_withTable b f.slots { m with place := some { pl with sps := pl.sps.headD 0 :: pl.sps } }
    | some q =>
      obtain ⟨d, off⟩ := q
      simp only [enterSlots, hp, hp', hf]
      have e := placeSlots_withTable b f.slots (pl.sps.headD 0 - BitVec.ofNat 64 d) off
        { m with place := some { pl with sps := (pl.sps.headD 0 - BitVec.ofNat 64 d) :: pl.sps } }
      change initSlots f.slots (pl.sps.headD 0 - BitVec.ofNat 64 d) off
          (pl.init.map (fun i => { i with bytes := b }))
          (placeSlots f.slots (pl.sps.headD 0 - BitVec.ofNat 64 d) off
            (Mem.withTable b { m with place := some { pl with
              sps := (pl.sps.headD 0 - BitVec.ofNat 64 d) :: pl.sps } })) = _
      rw [e]
      cases hi : pl.init with
      | none => rfl
      | some ini =>
        simp only [Option.map_some, initSlots]
        by_cases hs : f.slots.isEmpty
        · simp only [hs, ↓reduceIte]
        · simp only [hs, Bool.false_eq_true, ↓reduceIte]
          have hpl := placeSlots_place f.slots (pl.sps.headD 0 - BitVec.ofNat 64 d) off
            { m with place := some { pl with sps := (pl.sps.headD 0 - BitVec.ofNat 64 d) :: pl.sps } }
          have hag : b (ini.next + 1) = ini.bytes (ini.next + 1) := by
            refine hA pl ini hp hi ?_
            simp only [enterSlots, hp, hf, initSlots_place, initPlace, hs, Bool.false_eq_true,
              ↓reduceIte, placeSlots_place]
            simp [Place.advance, hi]
          refine Prod.ext rfl ?_
          simp only [SlotInit.succ]
          rw [hag, ← fillSlots_withTable]
          congr 1
          simp [Mem.withTable, Place.advance, placeSlots_place, SlotInit.succ]

theorem enterSlots_withTable_fst (f : Function) (m : Mem) :
    (enterSlots f (m.withTable b)).1 = (enterSlots f m).1 := by
  cases hp : m.place with
  | none =>
    have hp' : (m.withTable b).place = none := by simp only [Mem.withTable, hp, Option.map_none]
    simp only [enterSlots, hp, hp']
    rw [bumpSlots_withTable]
  | some pl =>
    have hp' : (m.withTable b).place =
        some { pl with init := pl.init.map (fun i => { i with bytes := b }) } := by
      simp only [Mem.withTable, hp, Option.map_some]
    cases hf : pl.frame f.name with
    | none =>
      simp only [enterSlots, hp, hp', hf]
      change (bumpSlots f.slots (Mem.withTable b
        { m with place := some { pl with sps := pl.sps.headD 0 :: pl.sps } })).1 = _
      rw [bumpSlots_withTable]
    | some q =>
      obtain ⟨d, off⟩ := q
      simp only [enterSlots, hp, hp', hf, initSlots_fst]
      change (placeSlots f.slots (pl.sps.headD 0 - BitVec.ofNat 64 d) off (Mem.withTable b
        { m with place := some { pl with
          sps := (pl.sps.headD 0 - BitVec.ofNat 64 d) :: pl.sps } })).1 = _
      rw [placeSlots_withTable]

/-- `enterFunc` without its memory: the entry frame for the slot list `slots`. -/
def enterFrame (f : Function) (args : List Val) (slots : List (SlotId × Nat)) : Res Frame := do
  checkTys s!"arguments of %{f.name}" args (AbiParam.tys f.sig.params)
  let entry ← Res.ofOption s!"%{f.name} has no blocks" f.entry?
  checkTys s!"entry block of %{f.name}" args (entry.params.map (·.2))
  let regs ← Res.ofOption "entry arity" (Regs.empty.setMany (entry.params.map (·.1)) args)
  pure { func := f, regs, slots, body := entry.body, term := entry.term }

theorem enterFunc_eq (f : Function) (args : List Val) (m : Mem) :
    enterFunc f args m = (fun fr => (fr, (enterSlots f m).2)) <$> enterFrame f args (enterSlots f m).1 := by
  simp only [enterFunc, enterFrame, map_bind]
  rfl

/-- **`enterFunc` under a replaced table** (the agreement at the entry it fills, if it returns). -/
theorem enterFunc_withTable (f : Function) (args : List Val) (m : Mem)
    (hA : ∀ r, enterFunc f args m = .ok r → ∀ pl ini, m.place = some pl → pl.init = some ini →
      r.2.place.bind (·.init) = some ini.succ → b (ini.next + 1) = ini.bytes (ini.next + 1)) :
    enterFunc f args (m.withTable b) = (fun r => (r.1, r.2.withTable b)) <$> enterFunc f args m := by
  rw [enterFunc_eq, enterFunc_eq, enterSlots_withTable_fst]
  cases he : enterFrame f args (enterSlots f m).1 with
  | ok fr =>
    have h2 : (enterSlots f (m.withTable b)).2 = (enterSlots f m).2.withTable b := by
      refine congrArg Prod.snd (enterSlots_withTable b f m fun pl ini hp hi hs => ?_)
      exact hA _ (by rw [enterFunc_eq, he]; rfl) pl ini hp hi hs
    simp [h2]
  | trap c => rfl
  | stuck msg => rfl

end slots

section step
variable (b : Nat → Nat → BitVec 8)

@[simp] theorem State.withTable_frame (s : State) : (s.withTable b).frame = s.frame := rfl
@[simp] theorem State.withTable_callers (s : State) : (s.withTable b).callers = s.callers := rfl
@[simp] theorem State.withTable_mem (s : State) : (s.withTable b).mem = s.mem.withTable b := rfl

theorem Mem.leave_withTable (m : Mem) : (m.withTable b).leave = m.leave.withTable b := by
  unfold Mem.leave
  cases h : m.place <;> simp [Mem.withTable, h]

theorem Mem.free_withTable (m : Mem) (bs : List Nat) : (m.withTable b).free bs = (m.free bs).withTable b :=
  rfl

theorem StepResult.ofRes_withTable {α : Type} (r : Res α) (k : α → StepResult) :
    (StepResult.ofRes r k).withTable b = StepResult.ofRes r (fun a => (k a).withTable b) := by
  cases r <;> rfl

theorem continueWith_withTable (s : State) (rest : List Stmt) (results : List ValueId)
    (vals : List Val) (m : Mem) :
    continueWith (s.withTable b) rest results vals (m.withTable b) =
      (continueWith s rest results vals m).withTable b := by
  unfold continueWith
  simp only [State.withTable_frame]
  split <;> rfl

theorem returnValues_withTable (s : State) (vals : List Val) (m : Mem) :
    returnValues (s.withTable b) vals (m.withTable b) = (returnValues s vals m).withTable b := by
  unfold returnValues
  rw [StepResult.ofRes_withTable]
  simp only [State.withTable_frame, State.withTable_callers, Mem.free_withTable, Mem.leave_withTable]
  congr 1
  funext _
  split
  · rfl
  · split <;> rfl

/-- **One step does not read the table but at the entry it fills** (`FillsOk`). -/
def FillsOk (s s1 : State) : Prop :=
  ∀ pl ini, s.mem.place = some pl → pl.init = some ini → s1.mem.place.bind (·.init) = some ini.succ →
    b (ini.next + 1) = ini.bytes (ini.next + 1)

theorem ofRes_withTable_of {α : Type} {r : Res α} {k1 k2 : α → StepResult}
    (h : ∀ a, r = .ok a → k1 a = (k2 a).withTable b) :
    StepResult.ofRes r k1 = (StepResult.ofRes r k2).withTable b := by
  cases r with
  | ok a => exact h a rfl
  | trap => rfl
  | stuck => rfl

theorem ofRes_map' {α β : Type} (f : α → β) (r : Res α) (k : β → StepResult) :
    StepResult.ofRes (f <$> r) k = StepResult.ofRes r (fun a => k (f a)) := by
  cases r <;> rfl

variable {b} in
theorem stepCall_withTable {env : Env} (henv : EnvTable env) (p : Program) (s : State)
    (rest : List Stmt) (results : List ValueId) (fn : FnRef) (args : List ValueId)
    (hA : ∀ s1, stepCall env p s rest results fn args = .next s1 → FillsOk b s s1) :
    stepCall env p (s.withTable b) rest results fn args =
      (stepCall env p s rest results fn args).withTable b := by
  unfold stepCall at hA ⊢
  dsimp only at hA
  simp only [State.withTable_frame]
  refine ofRes_withTable_of b fun ⟨ext, vals⟩ hR => ?_
  rw [hR] at hA
  simp only [StepResult.ofRes] at hA
  cases hpf : p.func? ext.name with
  | some callee =>
    simp only [hpf] at hA ⊢
    split
    · rename_i hc
      simp only [hc, ↓reduceIte] at hA
      rw [State.withTable_mem, enterFunc_withTable b callee vals s.mem ?_, ofRes_map']
      · exact ofRes_withTable_of b fun ⟨fr', mem'⟩ _ => rfl
      · intro r he pl ini hp hi hs
        exact hA _ (by rw [he]) pl ini hp hi hs
    · rfl
  | none =>
    simp only
    cases hx : env.extern ext.name with
    | none => rfl
    | some g =>
      simp only [State.withTable_mem]
      rw [henv _ _ hx]
      cases g vals s.mem with
      | returned rv m' =>
        simp only [Outcome.withTable]
        split
        · exact continueWith_withTable b s rest results rv m'
        · rfl
      | trapped => rfl
      | stuck => rfl
      | outOfFuel => rfl

variable {b} in
theorem callExternAt_withTable {env : Env} (henv : EnvTable env) (p : Program) (m : Mem)
    (d : Signature) (a : Nat) (vals : List Val) :
    callExternAt env p (m.withTable b) d a vals =
      (fun r => (r.1, r.2.withTable b)) <$> callExternAt env p m d a vals := by
  unfold callExternAt
  simp only [Mem.withTable_symbols]
  cases (env.names ++ p.externNames).find? (fun n => m.symbols n == some a) with
  | none => rfl
  | some name =>
    simp only [Res.ofOption_some, Res.ok_bind]
    cases hg : env.extern name with
    | none => rfl
    | some g =>
      simp only [Res.ofOption_some, Res.ok_bind, henv _ _ hg, map_bind]
      congr 1; funext _; congr 1; funext _
      cases g vals m with
      | returned rv m' =>
        simp only [Outcome.withTable]
        split <;> rfl
      | trapped => rfl
      | stuck => rfl
      | outOfFuel => rfl

variable {b} in
theorem stepCallIndirect_withTable {env : Env} (henv : EnvTable env) (p : Program) (s : State)
    (rest : List Stmt) (results : List ValueId) (sig : Nat) (callee : ValueId) (args : List ValueId)
    (hA : ∀ s1, stepCallIndirect env p s rest results sig callee args = .next s1 → FillsOk b s s1) :
    stepCallIndirect env p (s.withTable b) rest results sig callee args =
      (stepCallIndirect env p s rest results sig callee args).withTable b := by
  unfold stepCallIndirect at hA ⊢
  dsimp only at hA
  simp only [State.withTable_frame, State.withTable_mem, Mem.withTable_symbols]
  refine ofRes_withTable_of b fun ⟨declared, addr, vals⟩ hR => ?_
  rw [hR] at hA
  simp only [StepResult.ofRes] at hA
  cases hpf : p.funcs.find? (fun f => s.mem.symbols f.name == some addr) with
  | some target =>
    simp only [hpf] at hA ⊢
    split
    · rename_i hc
      simp only [hc, ↓reduceIte] at hA
      rw [enterFunc_withTable b target vals s.mem ?_, ofRes_map']
      · exact ofRes_withTable_of b fun ⟨fr', mem'⟩ _ => rfl
      · intro r he pl ini hp hi hs
        exact hA _ (by rw [he]) pl ini hp hi hs
    · rfl
  | none =>
    simp only
    rw [callExternAt_withTable henv, ofRes_map']
    exact ofRes_withTable_of b fun ⟨rv, m'⟩ _ => continueWith_withTable b s rest results rv m'

variable {b} in
theorem stepReturnCall_withTable {env : Env} (henv : EnvTable env) (p : Program) (s : State)
    (fn : FnRef) (args : List ValueId)
    (hA : ∀ s1, stepReturnCall env p s fn args = .next s1 → FillsOk b s s1) :
    stepReturnCall env p (s.withTable b) fn args = (stepReturnCall env p s fn args).withTable b := by
  unfold stepReturnCall at hA ⊢
  dsimp only at hA
  simp only [State.withTable_frame]
  refine ofRes_withTable_of b fun ⟨ext, vals⟩ hR => ?_
  rw [hR] at hA
  simp only [StepResult.ofRes] at hA
  cases hpf : p.func? ext.name with
  | some callee =>
    simp only [hpf] at hA ⊢
    split
    · rename_i hc
      simp only [hc, ↓reduceIte] at hA
      rw [State.withTable_mem, Mem.free_withTable, Mem.leave_withTable,
        enterFunc_withTable b callee vals _ ?_, ofRes_map']
      · exact ofRes_withTable_of b fun ⟨fr', mem'⟩ _ => rfl
      · intro r he pl ini hp hi hs
        have hp0 : ∃ pl0, s.mem.place = some pl0 ∧ pl0.init = pl.init := by
          revert hp
          simp only [Mem.leave, Mem.free]
          cases h : s.mem.place with
          | none => simp
          | some pl0 => simp only; intro e; cases e; exact ⟨pl0, rfl, rfl⟩
        obtain ⟨pl0, hp0, hi0⟩ := hp0
        exact hA _ (by rw [he]) pl0 ini hp0 (hi0.trans hi) hs
    · rfl
  | none =>
    simp only
    cases hx : env.extern ext.name with
    | none => rfl
    | some g =>
      simp only [State.withTable_mem]
      rw [henv _ _ hx]
      cases g vals s.mem with
      | returned rv m' => exact returnValues_withTable b s rv m'
      | trapped => rfl
      | stuck => rfl
      | outOfFuel => rfl

variable {b} in
theorem stepTerm_withTable {env : Env} (henv : EnvTable env) (p : Program) (s : State)
    (t : Terminator) (hA : ∀ s1, stepTerm env p s t = .next s1 → FillsOk b s s1) :
    stepTerm env p (s.withTable b) t = (stepTerm env p s t).withTable b := by
  cases t with
  | jump dest => exact ofRes_withTable_of b fun _ _ => rfl
  | brif c t e =>
    exact ofRes_withTable_of b fun _ _ => ofRes_withTable_of b fun _ _ => rfl
  | brTable x d tb =>
    exact ofRes_withTable_of b fun _ _ => ofRes_withTable_of b fun _ _ => rfl
  | ret xs =>
    exact ofRes_withTable_of b fun vals _ => returnValues_withTable b s vals s.mem
  | returnCall fn args => exact stepReturnCall_withTable henv p s fn args hA
  | trap c => rfl
  | tryCall fn args et =>
    simp only [stepTerm, stepTryCall, State.withTable_frame] at hA ⊢
    refine ofRes_withTable_of b fun ⟨n, base, bc⟩ hR => ?_
    rw [hR] at hA
    exact stepCall_withTable henv p { s with frame := { s.frame with body := [], term := .jump bc } }
      [] _ fn args fun s1 h => hA s1 h
  | tryCallIndirect callee args et =>
    simp only [stepTerm, stepTryCallIndirect, State.withTable_frame] at hA ⊢
    refine ofRes_withTable_of b fun ⟨n, base, bc⟩ hR => ?_
    rw [hR] at hA
    exact stepCallIndirect_withTable henv p
      { s with frame := { s.frame with body := [], term := .jump bc } } [] _ et.sig callee args
      fun s1 h => hA s1 h

variable {b} in
/-- **One step under a replaced table** (module doc). -/
theorem step_withTable {env : Env} (henv : EnvTable env) (p : Program) (s : State)
    (hA : ∀ s1, step env p s = .next s1 → FillsOk b s s1) :
    step env p (s.withTable b) = (step env p s).withTable b := by
  unfold step at hA ⊢
  simp only [State.withTable_frame]
  cases hb : s.frame.body with
  | nil =>
    simp only [hb] at hA ⊢
    exact stepTerm_withTable henv p s _ hA
  | cons st rest =>
    simp only [hb] at hA ⊢
    cases hi : st.inst with
    | call fn args =>
      simp only [hi] at hA ⊢
      exact stepCall_withTable henv p s rest st.results fn args hA
    | callIndirect sig callee args =>
      simp only [hi] at hA ⊢
      exact stepCallIndirect_withTable henv p s rest st.results sig callee args hA
    | _ =>
      simp only [State.withTable_mem, evalInst_withTable, ofRes_map']
      exact ofRes_withTable_of b fun r _ => continueWith_withTable b s rest st.results r.1 r.2

end step

/-- An entry state is a state of the program's run (`LInv`). -/
theorem initState_linv {P : Program} {n : String} {vals : List Val} {cm : Mem} {cs : State}
    (hi : initState P n vals cm = .ok cs) : LInv P cs := by
  simp only [initState, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at hi
  obtain ⟨g, hg, ⟨fr, mem'⟩, he, rfl⟩ := hi
  exact ⟨LFrame.enterFunc (Program.func?_some hg).1 he, fun _ h => nomatch h⟩

section run
variable {b : Nat → Nat → BitVec 8}

/-- The slot-byte counter of the rest of a returning run does not go down: a state with the
table `ini.adv e` ends with `ini.adv E`, `e ≤ E`. -/
theorem runLoop_adv_le {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (hk : EnvAdv env) {sps : List (BitVec 64)} {fr : String → Option (Nat × (SlotId → Nat))}
    {ini : SlotInit} {N : Nat} {s : State} {v : List Val} {m : Mem} (hI : LInv P s)
    {l : List (BitVec 64)} {e : Nat} (hs : s.mem.place = some ⟨l ++ sps, fr, some (ini.adv e)⟩)
    (hl : l.length = s.callers.length + 1) (hr : runLoop env P N s = .returned v m) {E : Nat}
    (hm : m.place = some ⟨sps, fr, some (ini.adv E)⟩) : e ≤ E := by
  obtain ⟨e', he'⟩ := runLoop_placeB (ini := ini.adv e) hP hk N s v m hI
    ⟨l, 0, by rw [hs]; rfl, hl⟩ hr
  rw [hm] at he'
  simp only [Option.some.injEq, Place.mk.injEq, SlotInit.adv_adv, true_and] at he'
  have := congrArg SlotInit.next he'
  simp only [SlotInit.adv] at this
  omega

/-- **A returning run under a replaced table** (module doc): from a state with the table
`ini.adv e` (`PlaceInvB`), when `b` agrees with `ini.bytes` on the entries `ini.next + 1, …,
ini.next + E` (`E`: the run's count), the run with `b` returns the same values and memory up to
the table. -/
theorem runLoop_withTable {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (henv : EnvTable env) (hk : EnvAdv env) {sps : List (BitVec 64)}
    {fr : String → Option (Nat × (SlotId → Nat))} {ini : SlotInit} {E : Nat}
    (hb : ∀ x, ini.next < x → x ≤ ini.next + E → b x = ini.bytes x) :
    ∀ (N : Nat) (s : State) (v : List Val) (m : Mem), LInv P s → PlaceInvB sps fr ini s →
      runLoop env P N s = .returned v m → m.place = some ⟨sps, fr, some (ini.adv E)⟩ →
      runLoop env P N (s.withTable b) = .returned v (m.withTable b)
  | 0, _, _, _, _, _, h, _ => by simp at h
  | N + 1, s, v, m, hI, hp, h, hm => by
    rw [runLoop_succ] at h ⊢
    have hs := placeInvB_step hP hk hI hp
    have hstep : step env P (s.withTable b) = (step env P s).withTable b := by
      refine step_withTable henv P s fun s1 hst pl ini' hpl hini hs1 => ?_
      obtain ⟨l, e, hl, hlen⟩ := hp
      rw [hl] at hpl
      cases hpl
      simp only at hini
      cases hini
      obtain ⟨l1, e1, hl1, hlen1⟩ := hs.1 s1 hst
      rw [hl1] at hs1
      simp only [Option.bind_some, Option.some.injEq] at hs1
      have he1 : e1 = e + 1 := by
        have := congrArg SlotInit.next hs1
        simp only [SlotInit.adv, SlotInit.succ] at this
        omega
      rw [hst] at h
      have hle := runLoop_adv_le hP hk (step_next_linv hP hI hst).1 hl1 hlen1 h hm
      simp only [SlotInit.adv]
      exact hb _ (by omega) (by omega)
    rw [hstep]
    cases hst : step env P s with
    | next s1 =>
      rw [hst] at h
      exact runLoop_withTable hP henv hk hb N s1 v m (step_next_linv hP hI hst).1 (hs.1 s1 hst) h hm
    | done v' m' =>
      rw [hst] at h
      cases h
      rfl
    | trapped c => rw [hst] at h; cases h
    | stuck msg => rw [hst] at h; cases h

/-- **The entry state under a replaced table.** -/
theorem initState_withTable {P : Program} {n : String} {vals : List Val} {cm : Mem}
    (hA : ∀ g r, P.func? n = some g → enterFunc g vals cm = .ok r → ∀ pl ini,
      cm.place = some pl → pl.init = some ini → r.2.place.bind (·.init) = some ini.succ →
      b (ini.next + 1) = ini.bytes (ini.next + 1)) :
    initState P n vals (cm.withTable b) = State.withTable b <$> initState P n vals cm := by
  unfold initState
  cases hf : P.func? n with
  | none => rfl
  | some g =>
    simp only [Res.ofOption_some, Res.ok_bind]
    rw [enterFunc_withTable b g vals cm (hA g · hf)]
    cases enterFunc g vals cm <;> rfl

/-- **A returning run from an entry under a replaced table** (module doc): the entry memory `cm`
has the table `ini`, the run returns with the counter advanced by `E`; a table `b` agreeing with
`ini.bytes` on the entries `ini.next + 1, …, ini.next + E` gives the same entry state and run up
to the table. -/
theorem runWith_withTable {P : Program} (hP : ∀ g ∈ P.funcs, LinkFree g) {env : Env}
    (henv : EnvTable env) (hk : EnvAdv env) {n : String} {vals : List Val} {cm : Mem} {cs : State}
    (hi : initState P n vals cm = .ok cs) {pl : Place} {ini : SlotInit} (hp : cm.place = some pl)
    (hi0 : pl.init = some ini) {N : Nat} {v : List Val} {m : Mem}
    (hr : runLoop env P N cs = .returned v m) {E : Nat}
    (hm : m.place = some ⟨pl.sps, pl.frame, some (ini.adv E)⟩)
    (hb : ∀ x, ini.next < x → x ≤ ini.next + E → b x = ini.bytes x) :
    initState P n vals (cm.withTable b) = .ok (cs.withTable b) ∧
      runLoop env P N (cs.withTable b) = .returned v (m.withTable b) := by
  have hinv := initState_placeB hi hp hi0
  have hI : LInv P cs := initState_linv hi
  refine ⟨?_, runLoop_withTable hP henv hk hb N cs v m hI hinv hr hm⟩
  rw [initState_withTable, hi]
  · rfl
  intro g r hg he pl' ini' hp' hi' hs
  rw [hp] at hp'
  cases hp'
  rw [hi0] at hi'
  cases hi'
  obtain ⟨l, e, hl, hlen⟩ := hinv
  -- the entry fills: its counter is `1`, at most the run's
  have hcs : cs.mem = r.2 := by
    simp only [initState, hg, Res.ofOption_some, Res.ok_bind, he] at hi
    cases hi
    rfl
  rw [hcs] at hl
  rw [hl] at hs
  simp only [Option.bind_some, Option.some.injEq] at hs
  have he1 : e = 1 := by
    have := congrArg SlotInit.next hs
    simp only [SlotInit.adv, SlotInit.succ] at this
    omega
  subst he1
  have hle := runLoop_adv_le hP hk hI (hcs ▸ hl) hlen hr hm
  exact hb _ (by omega) (by omega)

end run

end Clif
