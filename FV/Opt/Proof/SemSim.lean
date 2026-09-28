import FV.Clif.Run

/-!
# Function-level forward simulations and program refinement

The pass proofs relate a function `f` to its transform `g` by a *frame relation* `R`
(`Opt.IsSim`): every local step of a source frame (`Opt.lstep`: a non-call statement or a
branch) is matched by zero or more local steps of the related target frame, and calls,
returns, tail calls and traps are matched after zero or more target steps, with the same
observable arguments. `Opt.FunSim f g` packages such an `R` with the entry condition.

`Opt.FunSim.trans` composes simulations (the pipeline), and `Opt.runLoop_refines` lifts a
pointwise `FunSim` between the functions of two programs to their runs (`Clif.runLoop`):
whenever the source returns or traps within `fuel` steps, the target does the same within some
number of steps. Memory is shared (equal) between the two sides; the link-time symbols are a
fixed `syms` (externs keep them, `Opt.EnvKeepsSymbols`).
-/

namespace Opt

open Clif

/-! ## Local steps -/

/-- Result of a local step of a frame. -/
inductive LRes where
  | next (fr : Frame) (mem : Mem)
  | call (ext : ExtFunc) (vals : List Val) (results : List ValueId) (rest : List Stmt)
  | ret (vals : List Val)
  | tail (ext : ExtFunc) (vals : List Val)
  | trap (c : TrapCode)
  | stuck (msg : String)

/-- The prelude of `Clif.stepCall`. -/
def callArgs (fr : Frame) (fn : FnRef) (args : List ValueId) : Res (ExtFunc × List Val) := do
  let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
  let vals ← fr.getMany args
  checkTys s!"arguments of call to %{ext.name}" vals (AbiParam.tys ext.sig.params)
  pure (ext, vals)

/-- The prelude of `Clif.stepReturnCall`. -/
def tailArgs (fr : Frame) (fn : FnRef) (args : List ValueId) : Res (ExtFunc × List Val) := do
  let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
  let vals ← fr.getMany args
  checkTys s!"arguments of return_call to %{ext.name}" vals (AbiParam.tys ext.sig.params)
  Res.check (AbiParam.tys ext.sig.returns == AbiParam.tys fr.func.sig.returns)
    s!"return_call to %{ext.name}: return types differ from the caller's"
  pure (ext, vals)

def LRes.ofRes {α : Type} (r : Res α) (k : α → LRes) : LRes :=
  match r with
  | .ok a => k a
  | .trap c => .trap c
  | .stuck m => .stuck m

@[simp] theorem LRes.ofRes_ok {α : Type} (a : α) (k : α → LRes) : LRes.ofRes (.ok a) k = k a := rfl

/-- Local step of a frame. -/
def lstep (fr : Frame) (mem : Mem) : LRes :=
  match fr.body with
  | [] =>
    match fr.term with
    | .jump d => LRes.ofRes (enterBlock fr d) fun fr' => .next fr' mem
    | .brif c t e => LRes.ofRes (fr.get c) fun cv =>
      LRes.ofRes (enterBlock fr (if Sem.truthy cv.bits then t else e)) fun fr' => .next fr' mem
    | .brTable x dflt table => LRes.ofRes (fr.get x) fun xv =>
      LRes.ofRes (enterBlock fr (table[xv.toNat]?.getD dflt)) fun fr' => .next fr' mem
    | .ret xs => LRes.ofRes (fr.getMany xs) fun vals => .ret vals
    | .returnCall fn args => LRes.ofRes (tailArgs fr fn args) fun (ext, vals) => .tail ext vals
    | .trap c => .trap c
  | st :: rest =>
    match st.inst with
    | .call fn args => LRes.ofRes (callArgs fr fn args) fun (ext, vals) => .call ext vals st.results rest
    | inst => LRes.ofRes (evalInst fr mem inst) fun (vals, mem') =>
      match fr.regs.setMany st.results vals with
      | some regs => .next { fr with regs, body := rest } mem'
      | none => .stuck "result arity mismatch"

/-- The continuation of `Clif.stepCall` after its prelude. -/
def callCont (env : Env) (p : Program) (s : State) (rest : List Stmt) (results : List ValueId)
    (ext : ExtFunc) (vals : List Val) : StepResult :=
  let fr := s.frame
  match p.func? ext.name with
  | some callee =>
    if AbiParam.tys callee.sig.params == AbiParam.tys ext.sig.params &&
        AbiParam.tys callee.sig.returns == AbiParam.tys ext.sig.returns then
      StepResult.ofRes (enterFunc callee vals s.mem) fun (fr', mem') =>
        .next { frame := fr', callers := ({ fr with body := rest }, results) :: s.callers,
                mem := mem' }
    else .stuck s!"signature of %{ext.name} does not match its declaration"
  | none =>
    match env.extern ext.name with
    | some f =>
      match f vals s.mem with
      | .returned rvals mem' =>
        if rvals.map (·.ty) == AbiParam.tys ext.sig.returns then
          continueWith s rest results rvals mem'
        else .stuck s!"extern %{ext.name} returned values of the wrong types"
      | .trapped c => .trapped c
      | .stuck m => .stuck m
      | .outOfFuel => .stuck s!"extern %{ext.name} ran out of fuel"
    | none => .stuck s!"unknown callee %{ext.name}"

/-- The continuation of `Clif.stepReturnCall` after its prelude. -/
def tailCont (env : Env) (p : Program) (s : State) (ext : ExtFunc) (vals : List Val) :
    StepResult :=
  let fr := s.frame
  match p.func? ext.name with
  | some callee =>
    if AbiParam.tys callee.sig.params == AbiParam.tys ext.sig.params &&
        AbiParam.tys callee.sig.returns == AbiParam.tys ext.sig.returns then
      let mem := s.mem.free (fr.slots.map (·.2))
      StepResult.ofRes (enterFunc callee vals mem) fun (fr', mem') =>
        .next { s with frame := fr', mem := mem' }
    else .stuck s!"signature of %{ext.name} does not match its declaration"
  | none =>
    match env.extern ext.name with
    | some f =>
      match f vals s.mem with
      | .returned rvals mem' => returnValues s rvals mem'
      | .trapped c => .trapped c
      | .stuck m => .stuck m
      | .outOfFuel => .stuck s!"extern %{ext.name} ran out of fuel"
    | none => .stuck s!"unknown callee %{ext.name}"

/-- A local step result as a machine step (with callers and memory from `s`). -/
def LRes.lift (env : Env) (p : Program) (s : State) : LRes → StepResult
  | .next fr' m' => .next { s with frame := fr', mem := m' }
  | .call ext vals rs rest => callCont env p s rest rs ext vals
  | .ret vals => returnValues s vals s.mem
  | .tail ext vals => tailCont env p s ext vals
  | .trap c => .trapped c
  | .stuck m => .stuck m

theorem lift_ofRes {α : Type} (env : Env) (p : Program) (s : State) (r : Res α) (k : α → LRes) :
    (LRes.ofRes r k).lift env p s = StepResult.ofRes r (fun a => (k a).lift env p s) := by
  cases r <;> rfl

/-- `Clif.step` is the lifted `lstep`. -/
theorem step_eq_lift (env : Env) (p : Program) (s : State) :
    step env p s = (lstep s.frame s.mem).lift env p s := by
  obtain ⟨⟨func, regs, slots, body, term⟩, callers, mem⟩ := s
  cases body with
  | nil =>
    cases term <;> simp only [lstep, step, stepTerm, lift_ofRes] <;> try rfl
  | cons st rest =>
    simp only [lstep, step]
    cases st.inst <;> simp only [lift_ofRes, stepCall] <;> first
      | rfl
      | (congr 1; funext x; obtain ⟨vals, m'⟩ := x; simp only [continueWith]; split <;> rename_i h <;> simp only [h] <;> rfl)

/-! ## Stuttering steps of the target -/

/-- Zero or more `next` local steps. -/
inductive LStar : Frame → Mem → Frame → Mem → Prop
  | refl (fr : Frame) (m : Mem) : LStar fr m fr m
  | step {fr m fr1 m1 fr2 m2} : lstep fr m = .next fr1 m1 → LStar fr1 m1 fr2 m2 → LStar fr m fr2 m2

theorem LStar.trans {fr m fr1 m1 fr2 m2} (h1 : LStar fr m fr1 m1) (h2 : LStar fr1 m1 fr2 m2) :
    LStar fr m fr2 m2 := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem LStar.single {fr m fr1 m1} (h : lstep fr m = .next fr1 m1) : LStar fr m fr1 m1 :=
  .step h (.refl _ _)

/-- `LStar` runs in `runLoop` with any callers. -/
theorem LStar.runLoop {env : Env} {p : Program} {fr m fr' m'} (h : LStar fr m fr' m') :
    ∃ k, ∀ n cs, runLoop env p (n + k) ⟨fr, cs, m⟩ = runLoop env p n ⟨fr', cs, m'⟩ := by
  induction h with
  | refl => exact ⟨0, fun _ _ => rfl⟩
  | step hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, fun n cs => ?_⟩
    rw [show n + (k + 1) = (n + k) + 1 by omega, runLoop_succ, step_eq_lift]
    simp only [hs, LRes.lift]
    exact hk n cs

/-! ## `Res` inversion -/

@[simp] theorem Res.bind_eq_ok {α β : Type} (r : Res α) (f : α → Res β) (b : β) :
    (r >>= f) = .ok b ↔ ∃ a, r = .ok a ∧ f a = .ok b := by
  cases r <;> simp [bind, Res.bind]

@[simp] theorem Res.bind_eq_trap {α β : Type} (r : Res α) (f : α → Res β) (c : TrapCode) :
    (r >>= f) = .trap c ↔ r = .trap c ∨ ∃ a, r = .ok a ∧ f a = .trap c := by
  cases r <;> simp [bind, Res.bind]

@[simp] theorem Res.ofOption_eq_ok {α : Type} (msg : String) (o : Option α) (a : α) :
    Res.ofOption msg o = .ok a ↔ o = some a := by
  cases o <;> simp [Res.ofOption]

@[simp] theorem Res.check_eq_ok (b : Bool) (msg : String) (u : Unit) :
    Res.check b msg = .ok u ↔ b = true := by
  cases b <;> simp [Res.check]

@[simp] theorem Res.pure_eq_ok {α : Type} (a b : α) : (pure a : Res α) = .ok b ↔ a = b := by
  simp [pure]

theorem Res.ok_inj {α : Type} {a b : α} : (Res.ok a : Res α) = .ok b ↔ a = b := by simp

theorem enterBlock_ok {fr : Frame} {bc : BlockCall} {fr' : Frame} (h : enterBlock fr bc = .ok fr') :
    ∃ b args regs, fr.func.block? bc.block = some b ∧ fr.getMany bc.args = .ok args ∧
      args.map (·.ty) = b.params.map (·.2) ∧ fr.regs.setMany (b.params.map (·.1)) args = some regs ∧
      fr' = { fr with regs, body := b.body, term := b.term } := by
  simp only [enterBlock, Res.bind_eq_ok, Res.ofOption_eq_ok, checkTys, Res.check_eq_ok,
    Res.pure_eq_ok, beq_iff_eq] at h
  obtain ⟨b, hb, args, ha, _, ht, regs, hr, rfl⟩ := h
  exact ⟨b, args, regs, hb, ha, ht, hr, rfl⟩

theorem Mem.store_symbols {w : Nat} {m : Mem} {fl a n} {x : BitVec w} {m'}
    (h : m.store fl a n x = .ok m') : m'.symbols = m.symbols := by
  simp only [Mem.store, Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

theorem evalInst_symbols {fr mem i vals mem'} (h : evalInst fr mem i = .ok (vals, mem')) :
    mem'.symbols = mem.symbols := by
  cases i <;> simp only [evalInst, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
  all_goals (repeat' (first | obtain ⟨_, _, h⟩ := h | split at h)) <;>
    (try simp only [Res.pure_eq_ok, Prod.mk.injEq, Res.bind_eq_ok] at h) <;>
    (repeat' (first | obtain ⟨_, _, h⟩ := h | split at h))
  all_goals first | rfl | exact Mem.store_symbols ‹_›

theorem lstep_next_frame {fr m fr' m'} (h : lstep fr m = .next fr' m') :
    fr'.func = fr.func ∧ fr'.slots = fr.slots ∧ m'.symbols = m.symbols := by
  obtain ⟨func, regs, slots, body, term⟩ := fr
  cases body with
  | nil =>
    simp only [lstep] at h
    cases term <;> simp only [LRes.ofRes] at h <;> (repeat' split at h) <;> (try contradiction) <;>
      (cases h; obtain ⟨_, _, _, _, _, _, _, rfl⟩ := enterBlock_ok ‹_›; exact ⟨rfl, rfl, rfl⟩)
  | cons st rest =>
    simp only [lstep] at h
    split at h
    · simp only [LRes.ofRes] at h; split at h <;> contradiction
    · simp only [LRes.ofRes] at h
      split at h <;> try contradiction
      split at h <;> try contradiction
      cases h
      exact ⟨rfl, rfl, evalInst_symbols ‹_›⟩

theorem LStar.frame {fr m fr' m'} (h : LStar fr m fr' m') :
    fr'.func = fr.func ∧ fr'.slots = fr.slots ∧ m'.symbols = m.symbols := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hs _ ih =>
    obtain ⟨a, b, c⟩ := lstep_next_frame hs
    exact ⟨ih.1.trans a, ih.2.1.trans b, ih.2.2.trans c⟩

/-! ## Function entry -/

/-- The slot allocation of `enterFunc`. -/
def allocSlots (slots : List (SlotId × StackSlot)) (mem : Mem) : List (SlotId × Nat) × Mem :=
  slots.foldl
    (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
      (acc.1 ++ [(s.1, base)], m))
    ([], mem)

theorem allocSlots_ids_aux (slots : List (SlotId × StackSlot)) (acc : List (SlotId × Nat) × Mem) :
    (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
      (acc.1 ++ [(s.1, base)], m)) acc).1.map (·.1) = acc.1.map (·.1) ++ slots.map (·.1) ∧
    (slots.foldl (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
      (acc.1 ++ [(s.1, base)], m)) acc).2.symbols = acc.2.symbols := by
  induction slots generalizing acc with
  | nil => simp
  | cons s ss ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (acc.1 ++ [(s.1, (acc.2.alloc s.2.size (s.2.align.getD 1)).1)],
      (acc.2.alloc s.2.size (s.2.align.getD 1)).2)
    refine ⟨?_, ?_⟩
    · rw [h1]; simp
    · rw [h2]; rfl

theorem allocSlots_ids (slots : List (SlotId × StackSlot)) (mem : Mem) :
    (allocSlots slots mem).1.map (·.1) = slots.map (·.1) ∧
      (allocSlots slots mem).2.symbols = mem.symbols := by
  have := allocSlots_ids_aux slots ([], mem)
  simpa [allocSlots] using this

theorem enterFunc_ok {f : Function} {vals : List Val} {mem : Mem} {fr : Frame} {mem' : Mem}
    (h : enterFunc f vals mem = .ok (fr, mem')) :
    ∃ b regs, f.entry? = some b ∧ vals.map (·.ty) = AbiParam.tys f.sig.params ∧
      vals.map (·.ty) = b.params.map (·.2) ∧
      Regs.empty.setMany (b.params.map (·.1)) vals = some regs ∧
      allocSlots f.slots mem = (fr.slots, mem') ∧
      fr = ⟨f, regs, fr.slots, b.body, b.term⟩ := by
  simp only [enterFunc, checkTys, Res.bind_eq_ok, Res.check_eq_ok, beq_iff_eq,
    Res.ofOption_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨_, h1, b, hb, _, h2, regs, hr, he⟩ := h
  cases he
  exact ⟨b, regs, hb, h1, h2, hr, rfl, rfl⟩

theorem enterFunc_of {f : Function} {vals : List Val} {mem : Mem} {b : Block} {regs : Regs}
    (hb : f.entry? = some b) (h1 : vals.map (·.ty) = AbiParam.tys f.sig.params)
    (h2 : vals.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) vals = some regs) :
    enterFunc f vals mem = .ok (⟨f, regs, (allocSlots f.slots mem).1, b.body, b.term⟩,
      (allocSlots f.slots mem).2) := by
  have h3 : AbiParam.tys f.sig.params = b.params.map (·.2) := h1.symm.trans h2
  simp only [enterFunc, checkTys, h1, h3, hb, hr, beq_self_eq_true, Res.check_true,
    Res.ofOption_some, Res.ok_bind]
  rfl

theorem enterFunc_not_trap (f : Function) (vals : List Val) (mem : Mem) (c : TrapCode) :
    enterFunc f vals mem ≠ .trap c := by
  have hof : ∀ {α : Type} (m : String) (o : Option α), Res.ofOption m o ≠ .trap c := by
    intro α m o; cases o <;> simp [Res.ofOption]
  have hck : ∀ (b : Bool) (m : String), Res.check b m ≠ .trap c := by
    intro b m; cases b <;> simp [Res.check]
  simp [enterFunc, checkTys, Res.bind_eq_trap, hof, hck, pure]

/-! ## Simulations -/

/-- Externs keep the link-time symbols. -/
def EnvKeepsSymbols (env : Env) : Prop :=
  ∀ name f, env.extern name = some f → ∀ vals m rvals m', f vals m = .returned rvals m' →
    m'.symbols = m.symbols

/-- Continuation of a call: binding the returned values (of types `rtys`) keeps `R`. -/
def Cont (R : Frame → Frame → Prop) (fr : Frame) (rs : List ValueId) (fr' : Frame)
    (rs' : List ValueId) (rtys : List Ty) : Prop :=
  ∀ vs regs, vs.map (·.ty) = rtys → fr.regs.setMany rs vs = some regs →
    ∃ regs', fr'.regs.setMany rs' vs = some regs' ∧ R { fr with regs } { fr' with regs := regs' }

/-- `R` is a (stuttering, forward) simulation of frames, in memories whose symbols are `syms`. -/
structure IsSim (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop where
  frame : ∀ {fr fr'}, R fr fr' → fr'.slots = fr.slots ∧ fr'.func.sig = fr.func.sig
  next : ∀ {fr fr' m fr1 m1}, R fr fr' → m.symbols = syms → lstep fr m = .next fr1 m1 →
    ∃ fr1', LStar fr' m fr1' m1 ∧ R fr1 fr1'
  call : ∀ {fr fr' m ext vals rs rest}, R fr fr' → m.symbols = syms →
    lstep fr m = .call ext vals rs rest →
    ∃ fr2 rs' rest', LStar fr' m fr2 m ∧ lstep fr2 m = .call ext vals rs' rest' ∧
      Cont R { fr with body := rest } rs { fr2 with body := rest' } rs' (AbiParam.tys ext.sig.returns)
  ret : ∀ {fr fr' m vals}, R fr fr' → m.symbols = syms → lstep fr m = .ret vals →
    ∃ fr2, LStar fr' m fr2 m ∧ lstep fr2 m = .ret vals
  tail : ∀ {fr fr' m ext vals}, R fr fr' → m.symbols = syms → lstep fr m = .tail ext vals →
    ∃ fr2, LStar fr' m fr2 m ∧ lstep fr2 m = .tail ext vals
  trap : ∀ {fr fr' m c}, R fr fr' → m.symbols = syms → lstep fr m = .trap c →
    ∃ fr2 m2, LStar fr' m fr2 m2 ∧ lstep fr2 m2 = .trap c

/-- `g` simulates `f`: same name, signature and slots, and a simulation relating the entry
frames (same registers and slot bases). -/
structure FunSim (f g : Function) : Prop where
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  sim : ∀ syms, ∃ R, IsSim syms R ∧ ∀ b, f.entry? = some b → ∃ b', g.entry? = some b' ∧
    b'.params = b.params ∧ ∀ args regs (slots : List (SlotId × Nat)),
      args.map (·.ty) = b.params.map (·.2) →
      Regs.empty.setMany (b.params.map (·.1)) args = some regs →
      slots.map (·.1) = f.slots.map (·.1) →
      R ⟨f, regs, slots, b.body, b.term⟩ ⟨g, regs, slots, b'.body, b'.term⟩

theorem IsSim.star {syms R} (hR : IsSim syms R) {fr fr' m fr1 m1} (h : R fr fr')
    (hm : m.symbols = syms) (hs : LStar fr m fr1 m1) :
    ∃ fr1', LStar fr' m fr1' m1 ∧ R fr1 fr1' := by
  induction hs generalizing fr' with
  | refl => exact ⟨fr', .refl _ _, h⟩
  | step h1 _ ih =>
    obtain ⟨fa, ha, hra⟩ := hR.next h hm h1
    obtain ⟨fb, hb, hrb⟩ := ih hra ((lstep_next_frame h1).2.2.trans hm)
    exact ⟨fb, ha.trans hb, hrb⟩

theorem Cont.comp {R₁ R₂ : Frame → Frame → Prop} {a rs b rs' c rs'' rtys}
    (h1 : Cont R₁ a rs b rs' rtys) (h2 : Cont R₂ b rs' c rs'' rtys) :
    Cont (fun x z => ∃ y, R₁ x y ∧ R₂ y z) a rs c rs'' rtys := by
  intro vs regs ht hr
  obtain ⟨regs', hr', h1'⟩ := h1 vs regs ht hr
  obtain ⟨regs'', hr'', h2'⟩ := h2 vs regs' ht hr'
  exact ⟨regs'', hr'', _, h1', h2'⟩

theorem IsSim.comp {syms R₁ R₂} (h1 : IsSim syms R₁) (h2 : IsSim syms R₂) :
    IsSim syms (fun x z => ∃ y, R₁ x y ∧ R₂ y z) where
  frame := by
    rintro _ _ ⟨y, ha, hb⟩
    exact ⟨(h2.frame hb).1.trans (h1.frame ha).1, (h2.frame hb).2.trans (h1.frame ha).2⟩
  next := by
    rintro fr fr'' m fr1 m1 ⟨fr', ha, hb⟩ hm hs
    obtain ⟨fr1', hs1, hr1⟩ := h1.next ha hm hs
    obtain ⟨fr1'', hs2, hr2⟩ := h2.star hb hm hs1
    exact ⟨fr1'', hs2, fr1', hr1, hr2⟩
  call := by
    rintro fr fr'' m ext vals rs rest ⟨fr', ha, hb⟩ hm hs
    obtain ⟨f2, rs', rest', hs1, hc1, hk1⟩ := h1.call ha hm hs
    obtain ⟨g2, hs2, hr2⟩ := h2.star hb hm hs1
    obtain ⟨g3, rs'', rest'', hs3, hc3, hk3⟩ := h2.call hr2 hm hc1
    exact ⟨g3, rs'', rest'', hs2.trans hs3, hc3, hk1.comp hk3⟩
  ret := by
    rintro fr fr'' m vals ⟨fr', ha, hb⟩ hm hs
    obtain ⟨f2, hs1, hc1⟩ := h1.ret ha hm hs
    obtain ⟨g2, hs2, hr2⟩ := h2.star hb hm hs1
    obtain ⟨g3, hs3, hc3⟩ := h2.ret hr2 hm hc1
    exact ⟨g3, hs2.trans hs3, hc3⟩
  tail := by
    rintro fr fr'' m ext vals ⟨fr', ha, hb⟩ hm hs
    obtain ⟨f2, hs1, hc1⟩ := h1.tail ha hm hs
    obtain ⟨g2, hs2, hr2⟩ := h2.star hb hm hs1
    obtain ⟨g3, hs3, hc3⟩ := h2.tail hr2 hm hc1
    exact ⟨g3, hs2.trans hs3, hc3⟩
  trap := by
    rintro fr fr'' m c ⟨fr', ha, hb⟩ hm hs
    obtain ⟨f2, m2, hs1, hc1⟩ := h1.trap ha hm hs
    obtain ⟨g2, hs2, hr2⟩ := h2.star hb hm hs1
    obtain ⟨g3, m3, hs3, hc3⟩ := h2.trap hr2 ((LStar.frame hs1).2.2.trans hm) hc1
    exact ⟨g3, m3, hs2.trans hs3, hc3⟩

theorem IsSim.eq (syms) : IsSim syms (· = ·) where
  frame := by rintro _ _ rfl; exact ⟨rfl, rfl⟩
  next := by rintro _ _ _ fr1 _ rfl _ h; exact ⟨fr1, .single h, rfl⟩
  call := by
    rintro fr _ _ _ _ rs rest rfl _ h
    refine ⟨fr, rs, rest, .refl _ _, h, ?_⟩
    intro vs regs _ hr
    exact ⟨regs, hr, rfl⟩
  ret := by rintro fr _ _ _ rfl _ h; exact ⟨fr, .refl _ _, h⟩
  tail := by rintro fr _ _ _ _ rfl _ h; exact ⟨fr, .refl _ _, h⟩
  trap := by rintro fr _ m _ rfl _ h; exact ⟨fr, m, .refl _ _, h⟩

theorem FunSim.refl (f : Function) : FunSim f f where
  name := rfl
  sig := rfl
  slots := rfl
  sim syms := ⟨_, IsSim.eq syms, fun b hb => ⟨b, hb, rfl, fun _ _ _ _ _ _ => rfl⟩⟩

theorem FunSim.trans {f g h : Function} (h1 : FunSim f g) (h2 : FunSim g h) : FunSim f h where
  name := h2.name.trans h1.name
  sig := h2.sig.trans h1.sig
  slots := h2.slots.trans h1.slots
  sim syms := by
    obtain ⟨R₁, hs1, he1⟩ := h1.sim syms
    obtain ⟨R₂, hs2, he2⟩ := h2.sim syms
    refine ⟨_, hs1.comp hs2, fun b hb => ?_⟩
    obtain ⟨b', hb', hp', hr1⟩ := he1 b hb
    obtain ⟨b'', hb'', hp'', hr2⟩ := he2 b' hb'
    refine ⟨b'', hb'', hp''.trans hp', fun args regs slots ht hr hsl => ?_⟩
    refine ⟨_, hr1 args regs slots ht hr hsl, ?_⟩
    rw [← hp'] at ht hr
    exact hr2 args regs slots ht hr (hsl.trans (by rw [h1.slots]))

/-! ## Programs -/

/-- Pointwise simulation of the functions of two programs. -/
inductive FunsSim : List Function → List Function → Prop
  | nil : FunsSim [] []
  | cons {f g fs gs} : FunSim f g → FunsSim fs gs → FunsSim (f :: fs) (g :: gs)

theorem FunsSim.map {fs : List Function} {T : Function → Function} (h : ∀ f, FunSim f (T f)) :
    FunsSim fs (fs.map T) := by
  induction fs with
  | nil => exact .nil
  | cons f fs ih => exact .cons (h f) ih

theorem FunsSim.find {fs gs : List Function} (h : FunsSim fs gs) (n : String) :
    (∀ f, fs.find? (·.name == n) = some f → ∃ g, gs.find? (·.name == n) = some g ∧ FunSim f g) ∧
      (fs.find? (·.name == n) = none → gs.find? (·.name == n) = none) := by
  induction h with
  | nil => simp
  | @cons f g fs gs hfg _ ih =>
    simp only [List.find?_cons, hfg.name]
    split
    · exact ⟨fun f' hf => by cases hf; exact ⟨g, rfl, hfg⟩, fun h => (by cases h)⟩
    · exact ih

/-- The frame relation of a program pair: some simulation relates the frames. -/
def GR (syms : String → Option Nat) (fr fr' : Frame) : Prop :=
  ∃ R, IsSim syms R ∧ R fr fr'

theorem Cont.mono {R R' : Frame → Frame → Prop} (hR : ∀ a b, R a b → R' a b) {a rs b rs' rtys}
    (h : Cont R a rs b rs' rtys) : Cont R' a rs b rs' rtys := by
  intro vs regs ht hr
  obtain ⟨regs', h1, h2⟩ := h vs regs ht hr
  exact ⟨regs', h1, hR _ _ h2⟩

/-- Suspended callers, related through their continuations; `rtys`: the return types of the
frame above. -/
inductive CallersRel (syms : String → Option Nat) :
    List Ty → List (Frame × List ValueId) → List (Frame × List ValueId) → Prop
  | nil (rtys) : CallersRel syms rtys [] []
  | cons {rtys c rs c' rs' cs cs'} : Cont (GR syms) c rs c' rs' rtys →
      CallersRel syms (AbiParam.tys c.func.sig.returns) cs cs' →
      CallersRel syms rtys ((c, rs) :: cs) ((c', rs') :: cs')

/-- Related machine states. -/
structure SR (syms : String → Option Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem
  symbols : s.mem.symbols = syms
  frame : GR syms s.frame s'.frame
  callers : CallersRel syms (AbiParam.tys s.frame.func.sig.returns) s.callers s'.callers

/-- Source outcomes that the target must reproduce. -/
def OutcomeRefines (o o' : Outcome) : Prop :=
  (∀ vals m, o = .returned vals m → o' = .returned vals m) ∧ (∀ c, o = .trapped c → o' = .trapped c)

theorem funSim_entry {syms f g} (h : FunSim f g) {vals mem fr mem'}
    (he : enterFunc f vals mem = .ok (fr, mem')) :
    ∃ fr', enterFunc g vals mem = .ok (fr', mem') ∧ GR syms fr fr' ∧ mem'.symbols = mem.symbols := by
  obtain ⟨b, regs, hb, h1, h2, hr, hsl, hfr⟩ := enterFunc_ok he
  obtain ⟨R, hR, hent⟩ := h.sim syms
  obtain ⟨b', hb', hp, hrel⟩ := hent b hb
  have hids := allocSlots_ids f.slots mem
  rw [hsl] at hids
  refine ⟨⟨g, regs, fr.slots, b'.body, b'.term⟩, ?_, ⟨R, hR, ?_⟩, hids.2⟩
  · rw [enterFunc_of hb' (by rw [h.sig]; exact h1) (by rw [hp]; exact h2) (by rw [hp]; exact hr),
      h.slots, hsl]
  · rw [hfr]; exact hrel vals regs fr.slots h2 hr hids.1

theorem GR.isSim (syms) : IsSim syms (GR syms) where
  frame := by rintro _ _ ⟨R, hR, h⟩; exact hR.frame h
  next := by
    rintro _ _ _ _ _ ⟨R, hR, h⟩ hm hs
    obtain ⟨fr1', a, b⟩ := hR.next h hm hs
    exact ⟨fr1', a, R, hR, b⟩
  call := by
    rintro _ _ _ _ _ _ _ ⟨R, hR, h⟩ hm hs
    obtain ⟨a, b, c, d, e, k⟩ := hR.call h hm hs
    exact ⟨a, b, c, d, e, k.mono fun x y hxy => ⟨R, hR, hxy⟩⟩
  ret := by rintro _ _ _ _ ⟨R, hR, h⟩ hm hs; exact hR.ret h hm hs
  tail := by rintro _ _ _ _ _ ⟨R, hR, h⟩ hm hs; exact hR.tail h hm hs
  trap := by rintro _ _ _ _ ⟨R, hR, h⟩ hm hs; exact hR.trap h hm hs

/-- Related step results. -/
def StepRel (syms : String → Option Nat) (r r' : StepResult) : Prop :=
  (∀ s1, r = .next s1 → ∃ s1', r' = .next s1' ∧ SR syms s1 s1') ∧
    (∀ vs m, r = .done vs m → r' = .done vs m) ∧ (∀ c, r = .trapped c → r' = .trapped c)

theorem StepRel.trapped {syms c r'} (h : r' = StepResult.trapped c) :
    StepRel syms (.trapped c) r' :=
  ⟨(fun _ h' => by cases h'), (fun _ _ h' => by cases h'), (fun _ h' => by cases h'; exact h)⟩

theorem StepRel.stuck {syms m r'} : StepRel syms (.stuck m) r' :=
  ⟨(fun _ h' => by cases h'), (fun _ _ h' => by cases h'), (fun _ h' => by cases h')⟩

theorem returnValues_rel {syms : String → Option Nat} {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {m : Mem} {vals : List Val} {mem0 : Mem}
    (hsig : fr2.func.sig = s.frame.func.sig) (hsl : fr2.slots = s.frame.slots)
    (hc : CallersRel syms (AbiParam.tys s.frame.func.sig.returns) s.callers cs')
    (hsym : mem0.symbols = syms) :
    StepRel syms (returnValues s vals mem0) (returnValues ⟨fr2, cs', m⟩ vals mem0) := by
  simp only [returnValues, hsig, hsl]
  by_cases hty : vals.map (·.ty) = AbiParam.tys s.frame.func.sig.returns
  · have hck : ∀ w, checkTys w vals (AbiParam.tys s.frame.func.sig.returns) = .ok () := by
      intro w; simp [checkTys, hty]
    simp only [hck, StepResult.ofRes_ok]
    obtain ⟨frame, callers, mem⟩ := s
    simp only at hc ⊢
    cases hc with
    | nil =>
      exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h; rfl), fun _ h => (by cases h)⟩
    | @cons _ c rs c' rs' cs cs' hk hcs =>
      simp only
      cases hsm : c.regs.setMany rs vals with
      | none => exact StepRel.stuck
      | some regs =>
        obtain ⟨regs', hr', hg⟩ := hk vals regs hty hsm
        simp only [hr']
        refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
        cases h
        exact ⟨_, rfl, rfl, by rw [← hsym]; rfl, hg, hcs⟩
  · have hck : ∀ w, ∃ m, checkTys w vals (AbiParam.tys s.frame.func.sig.returns) = .stuck m := by
      intro w; simp [checkTys, hty, Res.check]
    obtain ⟨m1, h1⟩ := hck s!"return values of %{s.frame.func.name}"
    rw [h1]
    exact StepRel.stuck

theorem lstep_tail_returns {fr : Frame} {m : Mem} {ext : ExtFunc} {vals : List Val}
    (h : lstep fr m = .tail ext vals) :
    AbiParam.tys ext.sig.returns = AbiParam.tys fr.func.sig.returns := by
  obtain ⟨func, regs, slots, body, term⟩ := fr
  cases body with
  | cons st rest =>
    simp only [lstep] at h
    split at h
    · simp only [LRes.ofRes] at h; split at h <;> cases h
    · simp only [LRes.ofRes] at h; split at h <;> (try cases h); split at h <;> cases h
  | nil =>
    simp only [lstep] at h
    cases term <;> simp only [LRes.ofRes] at h <;> (repeat' split at h) <;> (try cases h)
    rename_i heq
    simp only [tailArgs, checkTys, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.check_eq_ok,
      beq_iff_eq, Res.pure_eq_ok] at heq
    obtain ⟨_, _, _, _, _, _, _, h1, h2⟩ := heq
    cases h2; exact h1

theorem callCont_rel {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSim p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {ext : ExtFunc} {vals : List Val} {rs rs' : List ValueId}
    {rest rest' : List Stmt} (hsym : s.mem.symbols = syms)
    (hc : CallersRel syms (AbiParam.tys s.frame.func.sig.returns) s.callers cs')
    (hk : Cont (GR syms) { s.frame with body := rest } rs { fr2 with body := rest' } rs'
      (AbiParam.tys ext.sig.returns)) :
    StepRel syms (callCont env p s rest rs ext vals) (callCont env q ⟨fr2, cs', s.mem⟩ rest' rs' ext vals) := by
  obtain ⟨hs, hn⟩ := hP.find ext.name
  simp only [callCont, Program.func?]
  cases hpf : p.funcs.find? (·.name == ext.name) with
  | some callee =>
    obtain ⟨callee', hq, hfs⟩ := hs callee hpf
    simp only [hq, hfs.sig]
    split
    · rename_i hcond
      cases he : enterFunc callee vals s.mem with
      | trap c => exact absurd he (enterFunc_not_trap _ _ _ _)
      | stuck m => exact StepRel.stuck
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSim_entry (syms := syms) hfs he
        simp only [he', StepResult.ofRes_ok]
        refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
        cases h
        have hret : AbiParam.tys callee.sig.returns = AbiParam.tys ext.sig.returns := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
        refine ⟨_, rfl, rfl, hsy.trans hsym, hg, ?_⟩
        obtain ⟨_, _, _, _, _, _, _, this⟩ := enterFunc_ok he
        simp only
        rw [this]
        exact .cons (by rw [hret]; exact hk) hc
    · exact StepRel.stuck
  | none =>
    simp only [hn hpf]
    cases hx : env.extern ext.name with
    | none => exact StepRel.stuck
    | some fx =>
      simp only
      cases hr : fx vals s.mem with
      | trapped c => exact StepRel.trapped rfl
      | stuck m => exact StepRel.stuck
      | outOfFuel => exact StepRel.stuck
      | returned rvals mem' =>
        simp only
        split
        · rename_i hty
          simp only [beq_iff_eq] at hty
          simp only [continueWith]
          cases hsm : s.frame.regs.setMany rs rvals with
          | none => exact StepRel.stuck
          | some regs =>
            obtain ⟨regs', hr', hg⟩ := hk rvals regs hty hsm
            simp only at hr'
            simp only [hr']
            refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
            cases h
            exact ⟨_, rfl, rfl, (hE _ _ hx _ _ _ _ hr).trans hsym, hg, hc⟩
        · exact StepRel.stuck

theorem tailCont_rel {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSim p.funcs q.funcs) {s : State} {fr2 : Frame}
    {cs' : List (Frame × List ValueId)} {ext : ExtFunc} {vals : List Val}
    (hsym : s.mem.symbols = syms)
    (hc : CallersRel syms (AbiParam.tys s.frame.func.sig.returns) s.callers cs')
    (hsig : fr2.func.sig = s.frame.func.sig) (hsl : fr2.slots = s.frame.slots)
    (hret : AbiParam.tys ext.sig.returns = AbiParam.tys s.frame.func.sig.returns) :
    StepRel syms (tailCont env p s ext vals) (tailCont env q ⟨fr2, cs', s.mem⟩ ext vals) := by
  obtain ⟨hs, hn⟩ := hP.find ext.name
  simp only [tailCont, Program.func?]
  cases hpf : p.funcs.find? (·.name == ext.name) with
  | some callee =>
    obtain ⟨callee', hq, hfs⟩ := hs callee hpf
    simp only [hq, hfs.sig, hsl]
    split
    · rename_i hcond
      cases he : enterFunc callee vals (s.mem.free (s.frame.slots.map (·.2))) with
      | trap c => exact absurd he (enterFunc_not_trap _ _ _ _)
      | stuck m => exact StepRel.stuck
      | ok x =>
        obtain ⟨frc, mem'⟩ := x
        obtain ⟨frc', he', hg, hsy⟩ := funSim_entry (syms := syms) hfs he
        simp only [he', StepResult.ofRes_ok]
        refine ⟨fun s1 h => ?_, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
        cases h
        have hr2 : AbiParam.tys callee.sig.returns = AbiParam.tys ext.sig.returns := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond; exact hcond.2
        refine ⟨_, rfl, rfl, hsy.trans hsym, hg, ?_⟩
        obtain ⟨_, _, _, _, _, _, _, this⟩ := enterFunc_ok he
        simp only
        rw [this]
        simp only
        rw [hr2, hret]
        exact hc
    · exact StepRel.stuck
  | none =>
    simp only [hn hpf]
    cases hx : env.extern ext.name with
    | none => exact StepRel.stuck
    | some fx =>
      simp only
      cases hr : fx vals s.mem with
      | trapped c => exact StepRel.trapped rfl
      | stuck m => exact StepRel.stuck
      | outOfFuel => exact StepRel.stuck
      | returned rvals mem' =>
        exact returnValues_rel hsig hsl hc ((hE _ _ hx _ _ _ _ hr).trans hsym)

/-- One source step: either a local `next` step (matched by target stuttering steps), or a step
matched by target stuttering steps followed by one related step. -/
theorem sim_step {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSim p.funcs q.funcs) {s s' : State} (h : SR syms s s') :
    (∃ fr1 m1, lstep s.frame s.mem = .next fr1 m1 ∧ ∃ s1' k,
      (∀ n, runLoop env q (n + k) s' = runLoop env q n s1') ∧
      SR syms { s with frame := fr1, mem := m1 } s1') ∨
    (∃ s2 k, (∀ n, runLoop env q (n + k) s' = runLoop env q n s2) ∧
      StepRel syms (step env p s) (step env q s2)) := by
  obtain ⟨hm, hsym, hg, hc⟩ := h
  have hGR := GR.isSim syms
  obtain ⟨fr', cs', m'⟩ := s'
  simp only at hm hg hc
  subst hm
  rw [step_eq_lift]
  cases hl : lstep s.frame s.mem with
  | next fr1 m1 =>
    left
    obtain ⟨fr1', hst, hr⟩ := hGR.next hg hsym hl
    obtain ⟨k, hk⟩ := LStar.runLoop (env := env) (p := q) hst
    have hf := lstep_next_frame hl
    refine ⟨fr1, m1, rfl, ⟨fr1', cs', m1⟩, k, fun n => hk n cs', rfl, hf.2.2.trans hsym, hr, ?_⟩
    simp only [hf.1]; exact hc
  | call ext vals rs rest =>
    right
    obtain ⟨fr2, rs', rest', hst, hl2, hk⟩ := hGR.call hg hsym hl
    obtain ⟨k, hkr⟩ := LStar.runLoop (env := env) (p := q) hst
    refine ⟨⟨fr2, cs', s.mem⟩, k, fun n => hkr n cs', ?_⟩
    rw [step_eq_lift]
    simp only [hl2, LRes.lift]
    exact callCont_rel hE hP hsym hc hk
  | ret vals =>
    right
    obtain ⟨fr2, hst, hl2⟩ := hGR.ret hg hsym hl
    obtain ⟨k, hkr⟩ := LStar.runLoop (env := env) (p := q) hst
    refine ⟨⟨fr2, cs', s.mem⟩, k, fun n => hkr n cs', ?_⟩
    rw [step_eq_lift]
    simp only [hl2, LRes.lift]
    have hf := LStar.frame hst
    have hs := hGR.frame hg
    exact returnValues_rel (by rw [hf.1]; exact hs.2) (by rw [hf.2.1]; exact hs.1) hc hsym
  | tail ext vals =>
    right
    obtain ⟨fr2, hst, hl2⟩ := hGR.tail hg hsym hl
    obtain ⟨k, hkr⟩ := LStar.runLoop (env := env) (p := q) hst
    refine ⟨⟨fr2, cs', s.mem⟩, k, fun n => hkr n cs', ?_⟩
    rw [step_eq_lift]
    simp only [hl2, LRes.lift]
    have hf := LStar.frame hst
    have hs := hGR.frame hg
    exact tailCont_rel hE hP hsym hc (by rw [hf.1]; exact hs.2) (by rw [hf.2.1]; exact hs.1)
      (lstep_tail_returns hl)
  | trap c =>
    right
    obtain ⟨fr2, m2, hst, hl2⟩ := hGR.trap hg hsym hl
    obtain ⟨k, hkr⟩ := LStar.runLoop (env := env) (p := q) hst
    refine ⟨⟨fr2, cs', m2⟩, k, fun n => hkr n cs', ?_⟩
    rw [step_eq_lift]
    simp only [hl2, LRes.lift]
    exact StepRel.trapped rfl
  | stuck m =>
    right
    exact ⟨_, 0, fun n => rfl, StepRel.stuck⟩

/-- **Program refinement.** If every function of `p` is simulated by the corresponding function
of `q`, related states have related runs: a source run that returns or traps within `n` steps is
matched by a target run of some length. -/
theorem runLoop_refines {syms : String → Option Nat} {env : Env} (hE : EnvKeepsSymbols env)
    {p q : Program} (hP : FunsSim p.funcs q.funcs) :
    ∀ n (s s' : State), SR syms s s' →
      ∃ n', OutcomeRefines (runLoop env p n s) (runLoop env q n' s') := by
  intro n
  induction n with
  | zero => intro s s' _; exact ⟨0, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩
  | succ n ih =>
    intro s s' h
    rcases sim_step hE hP h with ⟨fr1, m1, hl, s1', k, hk, hr⟩ | ⟨s2, k, hk, hr⟩
    · obtain ⟨n1, hn1⟩ := ih _ _ hr
      refine ⟨n1 + k, ?_⟩
      rw [hk, runLoop_succ, step_eq_lift, hl]
      exact hn1
    · rw [runLoop_succ]
      obtain ⟨hn, hd, ht⟩ := hr
      cases hst : step env p s with
      | next s1 =>
        obtain ⟨s1', hs', hr'⟩ := hn s1 hst
        obtain ⟨n1, hn1⟩ := ih _ _ hr'
        refine ⟨n1 + 1 + k, ?_⟩
        rw [hk, runLoop_succ, hs']
        exact hn1
      | done vs m =>
        refine ⟨0 + 1 + k, ?_⟩
        rw [hk, runLoop_succ, hd vs m hst]
        exact ⟨fun _ _ h => h, fun _ h => (by cases h)⟩
      | trapped c =>
        refine ⟨0 + 1 + k, ?_⟩
        rw [hk, runLoop_succ, ht c hst]
        exact ⟨fun _ _ h => (by cases h), fun _ h => h⟩
      | stuck m => exact ⟨0, fun _ _ h => (by cases h), fun _ h => (by cases h)⟩

end Opt
