import FV.Clif.Sem
import FV.Clif.Mem

/-!
# `Clif.run`: executable, fuel-bounded semantics

Structure (bottom-up, each layer separately unfoldable):

* `Clif.Sem.*` — per-opcode functions on `BitVec` (`FV/Clif/Sem.lean`).
* `Clif.evalInst` — one non-call instruction on values and memory: `Res (List Val × Mem)`.
* `Clif.enterBlock` — a branch: parallel assignment of block arguments to block parameters.
* `Clif.step` — one small step of the machine: one statement of the current block, or its
  terminator. Calls push a frame (program functions) or are atomic (`Env` externs).
* `Clif.runLoop` — `step` iterated at most `fuel` times.
* `Clif.run` / `Clif.runWith` — entry points.

`stuck` means a precondition failed: an ill-typed or ill-formed program (unknown value,
block, slot or callee; operand of the wrong type; arity mismatch), a false `notrap` or
`aligned` flag, or a read of uninitialised memory.
-/

namespace Clif

/-- Outcome of running a function. -/
inductive Outcome where
  | returned (vals : List Val) (mem : Mem)
  | trapped (code : TrapCode)
  | stuck (msg : String)
  | outOfFuel
  deriving Inhabited

/-- The returned values, if the outcome is `returned`. -/
def Outcome.returnedVals? : Outcome → Option (List Val)
  | .returned vals _ => some vals
  | _ => none

@[simp] theorem Outcome.returnedVals?_returned (vals : List Val) (mem : Mem) :
    (Outcome.returned vals mem).returnedVals? = some vals := rfl

/-- Semantics of extern callees, by name (without the leading `%`). An extern returning
`outOfFuel` is treated as `stuck`. -/
structure Env where
  extern : String → Option (List Val → Mem → Outcome) := fun _ => none

def Env.empty : Env := {}

instance : Inhabited Env := ⟨Env.empty⟩

/-- SSA register file of one frame. -/
abbrev Regs := ValueId → Option Val

namespace Regs

def empty : Regs := fun _ => none

def set (r : Regs) (x : ValueId) (v : Val) : Regs := fun y => if y = x then some v else r y

/-- Bind `xs` to `vs` (lengths must agree). Later bindings shadow earlier ones. -/
def setMany (r : Regs) : List ValueId → List Val → Option Regs
  | [], [] => some r
  | x :: xs, v :: vs => setMany (r.set x v) xs vs
  | _, _ => none

@[simp] theorem set_same (r : Regs) (x : ValueId) (v : Val) : r.set x v x = some v := by
  simp [set]

@[simp] theorem set_other (r : Regs) {x y : ValueId} (v : Val) (h : y ≠ x) :
    r.set x v y = r y := by
  simp [set, h]

@[simp] theorem setMany_nil (r : Regs) : r.setMany [] [] = some r := rfl

@[simp] theorem setMany_cons (r : Regs) (x : ValueId) (xs : List ValueId) (v : Val)
    (vs : List Val) : r.setMany (x :: xs) (v :: vs) = (r.set x v).setMany xs vs := rfl

end Regs

/-- An activation of a function. -/
structure Frame where
  func : Function
  regs : Regs
  /-- Base address of each stack slot of this activation. -/
  slots : List (SlotId × Nat)
  /-- Remaining statements of the current block. -/
  body : List Stmt
  /-- Terminator of the current block. -/
  term : Terminator

/-- Machine state: the running frame, the suspended callers (each with the result values
of its pending `call`), and memory. -/
structure State where
  frame : Frame
  callers : List (Frame × List ValueId)
  mem : Mem

/-- Result of one step. -/
inductive StepResult where
  | next (s : State)
  | done (vals : List Val) (mem : Mem)
  | trapped (code : TrapCode)
  | stuck (msg : String)

/-! ## Operands -/

namespace Frame

def get (fr : Frame) (x : ValueId) : Res Val :=
  Res.ofOption s!"use of undefined value v{x}" (fr.regs x)

/-- Operand `x` at type `ty`. -/
def getAs (fr : Frame) (x : ValueId) (ty : Ty) : Res (BitVec ty.width) := do
  let v ← fr.get x
  Res.ofOption s!"v{x} has type {v.ty.name}, expected {ty.name}" (v.as? ty)

def getMany (fr : Frame) : List ValueId → Res (List Val)
  | [] => .ok []
  | x :: xs => do
    let v ← fr.get x
    let vs ← fr.getMany xs
    pure (v :: vs)

end Frame

/-- Types of a list of ABI parameters. -/
def AbiParam.tys (ps : List AbiParam) : List Ty := ps.map (·.ty)

/-- `stuck` unless the values have exactly the given types. -/
def checkTys (what : String) (vs : List Val) (tys : List Ty) : Res Unit :=
  Res.check (vs.map (·.ty) == tys) s!"{what}: type/arity mismatch"

/-- Effective address `p + offset`, wrapping modulo 2^64 (p is zero-extended). -/
def effAddr (p : Val) (offset : Int) : Nat := ((p.toNat + offset) % (2 ^ 64 : Int)).toNat

/-! ## Instructions -/

/-- Access size in bytes and extension of a load. -/
def LoadOp.size (ty : Ty) : LoadOp → Nat
  | .load => ty.bytes
  | .uload8 | .sload8 => 1
  | .uload16 | .sload16 => 2
  | .uload32 | .sload32 => 4

def LoadOp.signed : LoadOp → Bool
  | .sload8 | .sload16 | .sload32 => true
  | _ => false

def StoreOp.size (ty : Ty) : StoreOp → Nat
  | .store => ty.bytes
  | .istore8 => 1
  | .istore16 => 2
  | .istore32 => 4

/-- Semantics of one non-`call` instruction: its result values and the new memory. -/
def evalInst (fr : Frame) (mem : Mem) : Inst → Res (List Val × Mem)
  | .iconst ty imm => pure ([⟨ty, imm⟩], mem)
  | .unary op ty x => do
    let a ← fr.getAs x ty
    pure ([⟨ty, Sem.unary op a⟩], mem)
  | .binary op ty x y => do
    let a ← fr.getAs x ty
    if op.isShift then
      let b ← fr.get y
      let r ← Res.ofOption "not a shift" (Sem.shift op a b.bits)
      pure ([⟨ty, r⟩], mem)
    else
      let b ← fr.getAs y ty
      pure ([⟨ty, Sem.binary op a b⟩], mem)
  | .div op ty x y => do
    let a ← fr.getAs x ty
    let b ← fr.getAs y ty
    let r ← Res.ofExcept (Sem.div op a b)
    pure ([⟨ty, r⟩], mem)
  | .overflow op ty x y => do
    let a ← fr.getAs x ty
    let b ← fr.getAs y ty
    let (r, f) := Sem.overflow op a b
    pure ([⟨ty, r⟩, Val.ofBool f], mem)
  | .carry op ty x y c => do
    let a ← fr.getAs x ty
    let b ← fr.getAs y ty
    let cin ← fr.getAs c .i8
    let (r, f) := Sem.carry op a b (Sem.truthy cin)
    pure ([⟨ty, r⟩, Val.ofBool f], mem)
  | .uaddOverflowTrap ty x y code => do
    let a ← fr.getAs x ty
    let b ← fr.getAs y ty
    let r ← Res.ofExcept (Sem.uaddOverflowTrap a b code)
    pure ([⟨ty, r⟩], mem)
  | .icmp cc ty x y => do
    let a ← fr.getAs x ty
    let b ← fr.getAs y ty
    pure ([⟨.i8, Sem.icmp cc a b⟩], mem)
  | .select ty c x y | .selectSpectreGuard ty c x y => do
    let cv ← fr.get c
    let a ← fr.getAs x ty
    let b ← fr.getAs y ty
    pure ([⟨ty, Sem.select cv.bits a b⟩], mem)
  | .bitselect ty c x y => do
    let cv ← fr.getAs c ty
    let a ← fr.getAs x ty
    let b ← fr.getAs y ty
    pure ([⟨ty, Sem.bitselect cv a b⟩], mem)
  | .bmask ty x => do
    let a ← fr.get x
    pure ([⟨ty, Sem.bmask a.bits⟩], mem)
  | .extend op ty x => do
    let a ← fr.get x
    Res.check (a.ty.width < ty.width) "extend must widen"
    match op with
    | .uextend => pure ([⟨ty, Sem.uextend ty.width a.bits⟩], mem)
    | .sextend => pure ([⟨ty, Sem.sextend ty.width a.bits⟩], mem)
  | .ireduce ty x => do
    let a ← fr.get x
    Res.check (ty.width < a.ty.width) "ireduce must narrow"
    pure ([⟨ty, Sem.ireduce ty.width a.bits⟩], mem)
  | .iconcat ty lo hi => do
    let t2 ← Res.ofOption "iconcat: no double-width type" ty.double?
    let l ← fr.getAs lo ty
    let h ← fr.getAs hi ty
    pure ([⟨t2, (Sem.iconcat l h).setWidth t2.width⟩], mem)
  | .isplit ty x => do
    let th ← Res.ofOption "isplit: no half-width type" ty.half?
    let a ← fr.getAs x ty
    let (l, h) := Sem.isplit th.width a
    pure ([⟨th, l⟩, ⟨th, h⟩], mem)
  | .load op ty flags p offset => do
    let pv ← fr.get p
    let n := op.size ty
    Res.check (n ≤ ty.bytes) "load: access wider than result"
    let raw ← mem.load flags (effAddr pv offset) n (8 * n)
    let r : BitVec ty.width :=
      if op.signed then raw.signExtend ty.width else raw.zeroExtend ty.width
    pure ([⟨ty, r⟩], mem)
  | .store op ty flags x p offset => do
    let a ← fr.getAs x ty
    let pv ← fr.get p
    let n := op.size ty
    Res.check (n ≤ ty.bytes) "store: access wider than value"
    let mem' ← mem.store flags (effAddr pv offset) n a
    pure ([], mem')
  | .stackAddr ty slot offset => do
    let base ← Res.ofOption s!"unknown stack slot ss{slot}" (fr.slots.lookup slot)
    pure ([Val.ofInt ty (base + offset)], mem)
  | .atomicRmw op ty flags p x => do
    let pv ← fr.get p
    let a ← fr.getAs x ty
    let addr := effAddr pv 0
    Res.check (addr % ty.bytes == 0) "misaligned atomic access"
    let old ← mem.load flags addr ty.bytes ty.width
    let mem' ← mem.store flags addr ty.bytes (Sem.atomicRmw op old a)
    pure ([⟨ty, old⟩], mem')
  | .atomicCas ty flags p e x => do
    let pv ← fr.get p
    let ev ← fr.getAs e ty
    let a ← fr.getAs x ty
    let addr := effAddr pv 0
    Res.check (addr % ty.bytes == 0) "misaligned atomic access"
    let old ← mem.load flags addr ty.bytes ty.width
    let mem' ← if old == ev then mem.store flags addr ty.bytes a else pure mem
    pure ([⟨ty, old⟩], mem')
  | .atomicLoad ty flags p => do
    let pv ← fr.get p
    let addr := effAddr pv 0
    Res.check (addr % ty.bytes == 0) "misaligned atomic access"
    let v ← mem.load flags addr ty.bytes ty.width
    pure ([⟨ty, v⟩], mem)
  | .atomicStore ty flags x p => do
    let a ← fr.getAs x ty
    let pv ← fr.get p
    let addr := effAddr pv 0
    Res.check (addr % ty.bytes == 0) "misaligned atomic access"
    let mem' ← mem.store flags addr ty.bytes a
    pure ([], mem')
  | .fence => pure ([], mem)
  | .bitcast ty _ x => do
    let a ← fr.getAs x ty
    pure ([⟨ty, a⟩], mem)
  | .call .. => .stuck "evalInst: call is handled by step"
  | .trapz c code => do
    let cv ← fr.get c
    if Sem.truthy cv.bits then pure ([], mem) else .trap code
  | .trapnz c code => do
    let cv ← fr.get c
    if Sem.truthy cv.bits then .trap code else pure ([], mem)
  | .nop => pure ([], mem)

/-! ## Control flow -/

/-- Branch to `bc` from `fr`: evaluate the arguments in the current register file, then bind
them to the target block's parameters (parallel assignment). -/
def enterBlock (fr : Frame) (bc : BlockCall) : Res Frame := do
  let b ← Res.ofOption s!"unknown block block{bc.block}" (fr.func.block? bc.block)
  let args ← fr.getMany bc.args
  checkTys s!"arguments of block{bc.block}" args (b.params.map (·.2))
  let regs ← Res.ofOption "block arity" (fr.regs.setMany (b.params.map (·.1)) args)
  pure { fr with regs, body := b.body, term := b.term }

/-- Start an activation of `f` on `args`: allocate its stack slots (fresh, uninitialised)
and enter its entry block. -/
def enterFunc (f : Function) (args : List Val) (mem : Mem) : Res (Frame × Mem) := do
  checkTys s!"arguments of %{f.name}" args (AbiParam.tys f.sig.params)
  let entry ← Res.ofOption s!"%{f.name} has no blocks" f.entry?
  let (slots, mem') := f.slots.foldl
    (fun (acc : List (SlotId × Nat) × Mem) (s : SlotId × StackSlot) =>
      let (base, m) := acc.2.alloc s.2.size (s.2.align.getD 1)
      (acc.1 ++ [(s.1, base)], m))
    ([], mem)
  checkTys s!"entry block of %{f.name}" args (entry.params.map (·.2))
  let regs ← Res.ofOption "entry arity" (Regs.empty.setMany (entry.params.map (·.1)) args)
  pure ({ func := f, regs, slots, body := entry.body, term := entry.term }, mem')

/-- Bind the results of a statement and continue with the rest of the block. -/
def continueWith (s : State) (rest : List Stmt) (results : List ValueId) (vals : List Val)
    (mem : Mem) : StepResult :=
  match s.frame.regs.setMany results vals with
  | some regs => .next { s with frame := { s.frame with regs, body := rest }, mem }
  | none => .stuck "result arity mismatch"

def StepResult.ofRes {α : Type} (r : Res α) (k : α → StepResult) : StepResult :=
  match r with
  | .ok a => k a
  | .trap c => .trapped c
  | .stuck m => .stuck m

/-- Execute a `call fnN(args)` statement. -/
def stepCall (env : Env) (p : Program) (s : State) (rest : List Stmt) (results : List ValueId)
    (fn : FnRef) (args : List ValueId) : StepResult :=
  let fr := s.frame
  StepResult.ofRes (do
    let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
    let vals ← fr.getMany args
    checkTys s!"arguments of call to %{ext.name}" vals (AbiParam.tys ext.sig.params)
    pure (ext, vals)) fun (ext, vals) =>
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

/-- Return `vals` from the current frame (memory `mem`): free its stack slots, then resume
the caller (binding the results of its pending call) or finish. -/
def returnValues (s : State) (vals : List Val) (mem : Mem) : StepResult :=
  StepResult.ofRes (checkTys s!"return values of %{s.frame.func.name}" vals
      (AbiParam.tys s.frame.func.sig.returns)) fun _ =>
  let mem := mem.free (s.frame.slots.map (·.2))
  match s.callers with
  | [] => .done vals mem
  | (caller, results) :: callers =>
    match caller.regs.setMany results vals with
    | some regs => .next { frame := { caller with regs }, callers, mem }
    | none => .stuck "call result arity mismatch"

/-- Execute `return_call fnN(args)`: the callee replaces the current frame. -/
def stepReturnCall (env : Env) (p : Program) (s : State) (fn : FnRef) (args : List ValueId) :
    StepResult :=
  let fr := s.frame
  StepResult.ofRes (do
    let ext ← Res.ofOption s!"unknown function reference fn{fn}" (fr.func.extern? fn)
    let vals ← fr.getMany args
    checkTys s!"arguments of return_call to %{ext.name}" vals (AbiParam.tys ext.sig.params)
    Res.check (AbiParam.tys ext.sig.returns == AbiParam.tys fr.func.sig.returns)
      s!"return_call to %{ext.name}: return types differ from the caller's"
    pure (ext, vals)) fun (ext, vals) =>
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

/-- Execute the terminator of the current block. -/
def stepTerm (env : Env) (p : Program) (s : State) : Terminator → StepResult
  | .jump dest => StepResult.ofRes (enterBlock s.frame dest) fun fr => .next { s with frame := fr }
  | .brif c t e => StepResult.ofRes (s.frame.get c) fun cv =>
    StepResult.ofRes (enterBlock s.frame (if Sem.truthy cv.bits then t else e)) fun fr =>
      .next { s with frame := fr }
  | .brTable x dflt table => StepResult.ofRes (s.frame.get x) fun xv =>
    StepResult.ofRes (enterBlock s.frame (table[xv.toNat]?.getD dflt)) fun fr =>
      .next { s with frame := fr }
  | .ret xs => StepResult.ofRes (s.frame.getMany xs) fun vals => returnValues s vals s.mem
  | .returnCall fn args => stepReturnCall env p s fn args
  | .trap code => .trapped code

/-- One small step. -/
def step (env : Env) (p : Program) (s : State) : StepResult :=
  match s.frame.body with
  | [] => stepTerm env p s s.frame.term
  | st :: rest =>
    match st.inst with
    | .call fn args => stepCall env p s rest st.results fn args
    | inst => StepResult.ofRes (evalInst s.frame s.mem inst) fun (vals, mem) =>
      continueWith s rest st.results vals mem

@[simp] theorem StepResult.ofRes_ok {α : Type} (a : α) (k : α → StepResult) :
    StepResult.ofRes (.ok a) k = k a := rfl
@[simp] theorem StepResult.ofRes_trap {α : Type} (c : TrapCode) (k : α → StepResult) :
    StepResult.ofRes (.trap c) k = .trapped c := rfl
@[simp] theorem StepResult.ofRes_stuck {α : Type} (m : String) (k : α → StepResult) :
    StepResult.ofRes (.stuck m) k = .stuck m := rfl

theorem step_term (env : Env) (p : Program) (s : State) (h : s.frame.body = []) :
    step env p s = stepTerm env p s s.frame.term := by
  simp [step, h]

theorem step_call (env : Env) (p : Program) (s : State) (rest : List Stmt)
    (results : List ValueId) (fn : FnRef) (args : List ValueId)
    (h : s.frame.body = { results, inst := .call fn args } :: rest) :
    step env p s = stepCall env p s rest results fn args := by
  simp [step, h]

/-- A non-`call` statement steps by `evalInst`. -/
theorem step_inst (env : Env) (p : Program) (s : State) (st : Stmt) (rest : List Stmt)
    (h : s.frame.body = st :: rest) (hc : ∀ fn args, st.inst ≠ .call fn args) :
    step env p s = StepResult.ofRes (evalInst s.frame s.mem st.inst) fun (vals, mem) =>
      continueWith s rest st.results vals mem := by
  unfold step
  rw [h]
  cases hi : st.inst with
  | call fn args => exact absurd hi (hc fn args)
  | _ => simp only [hi]

/-- Iterate `step` at most `fuel` times. -/
def runLoop (env : Env) (p : Program) : Nat → State → Outcome
  | 0, _ => .outOfFuel
  | fuel + 1, s =>
    match step env p s with
    | .next s' => runLoop env p fuel s'
    | .done vals mem => .returned vals mem
    | .trapped c => .trapped c
    | .stuck m => .stuck m

@[simp] theorem runLoop_zero (env : Env) (p : Program) (s : State) :
    runLoop env p 0 s = .outOfFuel := rfl

theorem runLoop_succ (env : Env) (p : Program) (fuel : Nat) (s : State) :
    runLoop env p (fuel + 1) s =
      match step env p s with
      | .next s' => runLoop env p fuel s'
      | .done vals mem => .returned vals mem
      | .trapped c => .trapped c
      | .stuck m => .stuck m := rfl

/-- Initial state for calling `f` on `args` with memory `mem`. -/
def initState (p : Program) (f : String) (args : List Val) (mem : Mem) : Res State := do
  let fn ← Res.ofOption s!"unknown function %{f}" (p.func? f)
  let (fr, mem') ← enterFunc fn args mem
  pure { frame := fr, callers := [], mem := mem' }

/-- Run `f` on `args` from memory `mem` for at most `fuel` steps. -/
def runWith (env : Env) (p : Program) (f : String) (args : List Val) (mem : Mem) (fuel : Nat) :
    Outcome :=
  match initState p f args mem with
  | .ok s => runLoop env p fuel s
  | .trap c => .trapped c
  | .stuck m => .stuck m

/-- Run `f` on `args` from empty memory for at most `fuel` steps. -/
def run (env : Env) (p : Program) (f : String) (args : List Val) (fuel : Nat) : Outcome :=
  runWith env p f args Mem.empty fuel

end Clif
