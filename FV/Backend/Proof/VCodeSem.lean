import FV.Backend.RegallocCheck

/-!
# Abstract semantics of VCode and of allocated code (M6 proof)

Both semantics are parametric in the values `V`, the *world* `W` (everything an instruction
may read or write that is not an allocatable location: memory outside the frame, NZCV, the
call/trap log, ...) and the instruction semantics `sem : ISem V W`. An instruction is seen
only through its **operand view** (`MInst.operands`: uses/defs with positions and
constraints, `MInst.clobbers`) and the uninterpreted transfer `sem i uses w`, which returns
the values of the def operands, the new world and a control outcome.

* **VCode** (`VStep`): vregs are an infinite register file `ρ : Nat → V`; an instruction
  reads its use vregs, writes its def vregs (early defs, then late defs, each in operand
  order); a branch to successor `s` performs the block's branch arguments as a parallel copy
  into the parameters of `s`.
* **Allocated code** (`MStep`): a location store `m : Loc → V` (registers, spill slots,
  callee-save slots). An item is a `move` (`m[dst ↦ m src]`) or an original instruction
  `op k allocs`, which reads its uses from their allocated locations, writes early defs,
  havocs its clobbers (`Clobbered`: any value, except that a callee-saved register keeps its
  `keep`-part, AAPCS64's "callee preserves the low 64 bits of v8–v15"), then writes late defs.
  No parallel copy on edges: the allocator's moves do that.

`Rets` returns the values of its uses; `halt` (a trap) stops with the world. The two
semantics share `sem`, so equal inputs give equal outputs: observables (calls with their
arguments, memory effects, traps, branch decisions) are whatever `sem` records in `W`.
-/

namespace Backend.Proof

open Backend

/-- Control outcome of one instruction. -/
inductive Ctl where
  /-- fall through to the next instruction of the block -/
  | next
  /-- branch to successor number `j` of the block (the block's terminator) -/
  | goto (j : Nat)
  /-- return (only a `Rets` may return) -/
  | ret
  /-- stop with the world (a trap) -/
  | halt
  deriving DecidableEq, Repr

/-- Abstract instruction semantics: from the values of the use operands (in operand order)
and the world, the values of the def operands (in operand order), the new world and the
control outcome; `none` when the instruction has no defined behaviour. -/
abbrev ISem (V W : Type) := MInst → List V → W → Option (List V × W × Ctl)

def _root_.Backend.Operand.isUse (o : Operand) : Bool := o.kind == .use
def _root_.Backend.Operand.isDef (o : Operand) : Bool := o.kind == .def
def _root_.Backend.Operand.isEarly (o : Operand) : Bool := o.pos == .early
def _root_.Backend.Operand.isLate (o : Operand) : Bool := o.pos == .late

/-- Function update. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (x : β) : α → β :=
  fun b => if b = a then x else f b

section
variable {V W : Type}

/-- Write `(operand, value)` pairs into the vreg file, in order. -/
def writeV (ρ : Nat → V) (dv : List (Operand × V)) : Nat → V :=
  dv.foldl (fun ρ p => upd ρ p.1.vreg p.2) ρ

/-- Write `((operand, location), value)` triples into the location store, in order. -/
def writeM (m : Loc → V) (dl : List ((Operand × Loc) × V)) : Loc → V :=
  dl.foldl (fun m p => upd m p.1.2 p.2) m

/-- The parallel copy `ps := xs` (reads the old file). -/
def parCopyEnv (ρ : Nat → V) (ps xs : List Nat) : Nat → V :=
  fun v => match (ps.zip xs).lookup v with
    | some x => ρ x
    | none => ρ v

/-- Successor number `j` of block `b` (by the CFG of `vc`). -/
def succOf (vc : VCode) (b j : Nat) : Option Nat :=
  match vc.cfg with
  | .ok (ss, _) => ss[b]?.bind (·[j]?)
  | .error _ => none

/-- The vreg file entering successor `s` of block `b`: the branch arguments of `b` copied in
parallel into the parameters of `s`. -/
def edgeEnv (vc : VCode) (b s : Nat) (ρ : Nat → V) : Option (Nat → V) := do
  let vb ← vc.blocks[b]?
  let sb ← vc.blocks[s]?
  if vb.branchArgs.size = sb.params.size then
    let ps ← (sb.params.toList.mapM vregNum).toOption
    let xs ← (vb.branchArgs.toList.mapM vregNum).toOption
    pure (parCopyEnv ρ ps xs)
  else none

/-! ## VCode -/

structure VState (V W : Type) where
  b : Nat
  /-- index of the next instruction in block `b` -/
  k : Nat
  ρ : Nat → V
  w : W

inductive VConf (V W : Type) where
  | run (s : VState V W)
  | ret (vals : List V) (w : W)
  | halt (w : W)

variable (vc : VCode) (sem : ISem V W)

/-- Where control goes after instruction `k` (of `n`) of block `b`. -/
inductive VNext (b k n : Nat) (i : MInst) (uses : List V) (ρ : Nat → V) (w : W) :
    Ctl → VConf V W → Prop
  | next : k + 1 < n → VNext b k n i uses ρ w .next (.run ⟨b, k + 1, ρ, w⟩)
  | goto {j s ρ'} : k + 1 = n → succOf vc b j = some s → edgeEnv vc b s ρ = some ρ' →
      VNext b k n i uses ρ w (.goto j) (.run ⟨s, 0, ρ', w⟩)
  | ret {us} : i = .rets us → VNext b k n i uses ρ w .ret (.ret uses w)
  | halt : VNext b k n i uses ρ w .halt (.halt w)

/-- One VCode step: execute instruction `k` of block `b`. -/
inductive VStep : VConf V W → VConf V W → Prop
  | step {b k ρ w vb i ops outs w' ctl c'} :
      vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      sem i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w = some (outs, w', ctl) →
      outs.length = (ops.toList.filter Operand.isDef).length →
      VNext vc b k vb.insts.size i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg))
        (writeV (writeV ρ (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isEarly)))
          (((ops.toList.filter Operand.isDef).zip outs).filter (·.1.isLate))) w' ctl c' →
      VStep (.run ⟨b, k, ρ, w⟩) c'

/-! ## Allocated code -/

structure MState (V W : Type) where
  b : Nat
  /-- the remaining items of block `b` -/
  its : List RItem
  m : Loc → V
  w : W

inductive MConf (V W : Type) where
  | run (s : MState V W)
  | ret (vals : List V) (m : Loc → V) (w : W)
  | halt (w : W)

variable (keep : Reg → V → V)

/-- `m'` is `m` after clobbering the registers `clob`: other locations are unchanged; a
clobbered callee-saved register keeps its `keep`-part. -/
def Clobbered (clob : List Reg) (m m' : Loc → V) : Prop :=
  (∀ l, (∀ c ∈ clob, l ≠ .reg c) → m' l = m l) ∧
  (∀ c ∈ clob, c ∈ calleeSaved → keep c (m' (.reg c)) = keep c (m (.reg c)))

variable (rf : RFunc)

/-- Where control goes after the item `op k _` (instruction `k` of `n`) of block `b`. -/
inductive MNext (b k n : Nat) (i : MInst) (uses : List V) (its : List RItem) (m : Loc → V)
    (w : W) : Ctl → MConf V W → Prop
  | next : k + 1 < n → MNext b k n i uses its m w .next (.run ⟨b, its, m, w⟩)
  | goto {j s items} : k + 1 = n → succOf vc b j = some s → rf.blocks[s]? = some items →
      MNext b k n i uses its m w (.goto j) (.run ⟨s, items.toList, m, w⟩)
  | ret {us} : i = .rets us → MNext b k n i uses its m w .ret (.ret uses m w)
  | halt : MNext b k n i uses its m w .halt (.halt w)

/-- One step of the allocated code: execute the next item of the current block. -/
inductive MStep : MConf V W → MConf V W → Prop
  | move {b src dst its m w} :
      MStep (.run ⟨b, .move src dst :: its, m, w⟩) (.run ⟨b, its, upd m dst (m src), w⟩)
  | op {b k allocs its m w vb i ops outs w' ctl m2 c'} :
      vc.blocks[b]? = some vb → vb.insts[k]? = some i → i.operands = .ok ops →
      allocs.size = ops.size →
      sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w = some (outs, w', ctl) →
      outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length →
      Clobbered keep i.clobbers
        (writeM m ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isEarly)))
        m2 →
      MNext vc rf b k vb.insts.size i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) its
        (writeM m2 ((((ops.zip allocs).toList.filter (·.1.isDef)).zip outs).filter (·.1.1.isLate)))
        w' ctl c' →
      MStep (.run ⟨b, .op k allocs :: its, m, w⟩) c'

end

/-- Reflexive-transitive closure. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star r a a
  | step {a b c : α} : r a b → Star r b c → Star r a c

theorem Star.trans {α : Type} {r : α → α → Prop} {a b c : α} :
    Star r a b → Star r b c → Star r a c := by
  intro h1 h2
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem Star.single {α : Type} {r : α → α → Prop} {a b : α} (h : r a b) : Star r a b :=
  .step h (.refl b)

end Backend.Proof
