/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

# Untrusted proof search: co-execution of the Arm code and the CLIF function

From each cut point (function entry, Arm join points) the generator walks every Arm path to
the next cut point, return, or trap, executing the CLIF function alongside:

* the Arm side instruction by instruction (value numbering, `Gen/Arm.lean`);
* the CLIF side lazily, only when an event needs it: a memory access (`load`/`store` are
  synchronised with the Arm access), a call, a return, a trap, or arriving at a cut point.
  A CLIF `brif` is taken once its direction is determined on the samples consistent with the
  Arm path so far;
* at a cut point, the relation (which register holds which CLIF value, callee-saved entry
  value, stack offset, or constant) is read off the value numbering.

Each walk is emitted as a Lean tactic script (`GoodF.stepEq`, `GoodF.stmt`, `GoodF.brif`, …).
Nothing here is trusted: the scripts are checked by Lean.
-/
import FV.Validate.Gen.Arm
import FV.Clif
import Std.Data.HashMap

namespace Validate.Gen

open Std

/-- Description of an Arm register at a cut point. -/
inductive Desc where
  /-- The low `w` bits are CLIF value `v`. -/
  | clif (v : Nat) (w : Nat)
  /-- The entry value of register `j`. -/
  | entry (j : Nat)
  /-- `A.sp0 + c`. -/
  | spOff (c : BitVec 64)
  | const (c : BitVec 64)
  deriving BEq, Inhabited, Repr

/-- The relation at a cut point. -/
structure CutInv where
  off : Nat
  block : Nat
  /-- Registers 0..31 (31 = SP). -/
  regs : Array (Option Desc)
  /-- CLIF atoms `x<v>` with their types. -/
  atoms : Array (Nat × Clif.Ty)
  /-- CLIF values known to be constants. -/
  consts : Array (Nat × Clif.Ty × BitVec 64)
  deriving Inhabited

/-- Static information about the function being validated. -/
structure FnInfo where
  F : Clif.Function
  /-- Lean name prefix of the CLIF function constant. -/
  fname : String
  words : Array UInt32
  base : Nat
  traps : Array (Nat × Clif.TrapCode)
  valTy : HashMap Nat Clif.Ty
  /-- CLIF live-in values of each block. -/
  liveIn : HashMap Nat (Array Nat)
  cuts : Array Nat
  deriving Inhabited

structure CState where
  block : Nat
  idx : Nat
  regs : HashMap Nat Nat
  deriving Inhabited

structure Path where
  pc : Nat
  arm : AState
  clif : CState
  live : Array Bool
  /-- CLIF has finished (returned / trapped): the goal is a `Reach`. -/
  reach : Bool := false
  /-- A CLIF terminator was executed since the cut point. -/
  termDone : Bool := false
  /-- Names of path hypotheses. -/
  hyps : Array String := #[]
  steps : Nat := 0
  deriving Inhabited

structure GS where
  arena : Arena := {}
  out : Array String := #[]
  fresh : Nat := 0
  /-- Cut invariants, indexed like `FnInfo.cuts`. -/
  invs : Array (Option CutInv) := #[]
  /-- Cut indices whose invariant changed and must be (re-)explored. -/
  dirty : Array Nat := #[]
  /-- Nodes of entry values of x0..x31. -/
  entryNodes : Array Nat := #[]
  /-- Whether each `#vstep` needs the SP-alignment hypothesis. -/
  spSteps : HashMap Nat Bool := {}
  deriving Inhabited

abbrev GM := ReaderT FnInfo (StateT GS (Except String))

def liftSym {α : Type} (m : SymM α) : GM α := do
  let s ← get
  match m.run s.arena with
  | .ok (a, ar) => set { s with arena := ar }; pure a
  | .error e => throw e

def gfail {α : Type} (msg : String) : GM α := throw msg

def emit (ind : Nat) (line : String) : GM Unit :=
  modify fun s => { s with out := s.out.push (String.ofList (List.replicate (2 * ind) ' ') ++ line) }

def freshName (pfx : String) : GM String := do
  let s ← get
  set { s with fresh := s.fresh + 1 }
  return s!"{pfx}{s.fresh}"

def hexN (n : Nat) : String := hex n

def tyName : Clif.Ty → String
  | .i8 => "Clif.Ty.i8" | .i16 => "Clif.Ty.i16" | .i32 => "Clif.Ty.i32" | .i64 => "Clif.Ty.i64"
  | .i128 => "Clif.Ty.i128"

/-! ## CLIF values on samples -/

/-- Evaluate a non-call, non-memory instruction on every sample (with the real CLIF
semantics). Returns result nodes and, per sample, whether it trapped. -/
def clifEval (st : Clif.Stmt) (c : CState) : GM (Array Nat × Array Bool) := do
  let info ← read
  let mut resVals : Array (Array (BitVec 64)) := Array.replicate st.results.length #[]
  let mut traps : Array Bool := #[]
  -- operand sample values
  let regsNodes := c.regs
  let mut nodeVals : HashMap Nat (Array (BitVec 64)) := {}
  for (v, nd) in regsNodes.toList do
    nodeVals := nodeVals.insert v (← liftSym (vals nd))
  for k in [0:nSamples] do
    let regs : Clif.Regs := fun v =>
      match nodeVals.get? v, info.valTy.get? v with
      | some vs, some ty => some ⟨ty, BitVec.ofNat ty.width vs[k]!.toNat⟩
      | _, _ => none
    let fr : Clif.Frame := ⟨info.F, regs, [], [], .trap .intDivz⟩
    match Clif.evalInst fr Clif.Mem.empty st.inst with
    | .ok (vs, _) =>
      traps := traps.push false
      for j in [0:st.results.length] do
        let v := vs[j]?.map (fun x => BitVec.ofNat 64 x.bits.toNat) |>.getD 0
        resVals := resVals.modify j (·.push v)
    | .trap _ =>
      traps := traps.push true
      for j in [0:st.results.length] do resVals := resVals.modify j (·.push 0)
    | .stuck m => gfail s!"CLIF evaluation stuck on a sample: {m}"
  let mut nodes := #[]
  for vs in resVals do
    -- fold constants
    let n ← match vs[0]? with
      | some v0 => if vs.all (· == v0) && (st.inst matches .iconst ..) then liftSym (mkConst v0)
                   else liftSym (addNode { shape := .other, vals := vs })
      | none => liftSym (mkConst 0)
    nodes := nodes.push n
  return (nodes, traps)

def isTrapping : Clif.Inst → Bool
  | .div .. | .uaddOverflowTrap .. | .trapz .. | .trapnz .. => true
  | _ => false

def isMem : Clif.Inst → Bool
  | .load .. | .store .. | .atomicRmw .. | .atomicCas .. | .atomicLoad .. | .atomicStore .. => true
  | _ => false

/-- Truthiness of node `n` on the live samples: `some b` if the same on all of them. -/
def liveBool (live : Array Bool) (n : Nat) : GM (Option Bool) := do
  let vs ← liftSym (vals n)
  let mut r : Option Bool := none
  for k in [0:nSamples] do
    if live[k]! then
      let b := vs[k]! != 0
      match r with
      | none => r := some b
      | some b' => if b != b' then return none
  return r

end Validate.Gen

namespace Validate.Gen

open Std

/-! ## Hypothesis names used by the scripts -/

def cutHyps (inv : CutInv) : Array String := Id.run do
  let mut hs := #["hprog", "herr", "hsp", "hmem", "hal", "hpres", "hgot", "hvs", "hpc"]
  for (v, _) in inv.atoms do hs := hs.push s!"hr{v}"
  for (v, _, _) in inv.consts do hs := hs.push s!"hk{v}"
  for i in [0:32] do
    if inv.regs[i]!.isSome then hs := hs.push s!"hf{i}"
  hs

def clifHyps (inv : CutInv) : Array String := Id.run do
  let mut hs := #[]
  for (v, _) in inv.atoms do hs := hs.push s!"hr{v}"
  for (v, _, _) in inv.consts do hs := hs.push s!"hk{v}"
  hs

def joinC (xs : Array String) : String := ", ".intercalate xs.toList

/-- Tactic closing an inconsistent case. -/
def bvContra : String :=
  "exfalso; clear IH; simp (config := {decide := true, failIfUnchanged := false}) only " ++
  "[state_simp_rules, vsimp, vsem] at *; bv_decide"

/-! ## Segment context -/

structure Seg where
  /-- The cut this segment starts from. -/
  inv : CutInv
  cutIdx : Nat
  deriving Inhabited

abbrev SM := ReaderT Seg GM

def segHyps (p : Path) : SM String := do
  let s ← read
  return joinC ((cutHyps s.inv) ++ p.hyps)

def clifList (p : Path) : SM String := do
  let s ← read
  return joinC (clifHyps s.inv ++ p.hyps)

/-! ## CLIF execution -/

def curBlock (c : CState) : SM Clif.Block := do
  let info ← (read : GM FnInfo)
  match info.F.block? c.block with
  | some b => pure b
  | none => gfail s!"no CLIF block {c.block}"

/-- Emit and perform one non-call, non-memory CLIF statement. `trapOK` is the proof of the
trap side when the statement traps on every live sample. -/
def execStmt (p : Path) (ind : Nat) (st : Clif.Stmt) : SM Path := do
  let (nodes, traps) ← clifEval st p.clif
  emit ind s!"apply GoodF.stmt rfl; vclif [{← clifList p}]"
  let mut regs := p.clif.regs
  for (v, n) in st.results.zip nodes.toList do regs := regs.insert v n
  let p' := { p with clif := { p.clif with idx := p.clif.idx + 1, regs } }
  if isTrapping st.inst then
    let liveTrap := (List.range nSamples).any fun k => p.live[k]! && traps[k]!
    if liveTrap then gfail s!"CLIF statement traps on this path but the Arm code does not: {repr st.inst}"
    match st.inst with
    | .div .sdiv .. =>
      let hz ← freshName "hz"
      emit ind s!"refine ⟨fun {hz} => by {bvContra}, fun {hz} => ⟨fun {hz}o => by {bvContra}, fun {hz}o => ?_⟩⟩"
      return { p' with hyps := p'.hyps.push hz |>.push s!"{hz}o" }
    | _ =>
      let hz ← freshName "hz"
      emit ind s!"refine ⟨fun {hz} => by {bvContra}, fun {hz} => ?_⟩"
      return { p' with hyps := p'.hyps.push hz }
  return p'

/-- Advance CLIF through pure statements, `jump`s and determined `brif`s, stopping at the first
statement or terminator it cannot execute, or on entering block `stopAt` (after at least one
terminator). -/
partial def advance (p : Path) (ind : Nat) (stopAt : Option Nat := none) (fuel : Nat := 10000) :
    SM Path := do
  if fuel == 0 then gfail "CLIF loops without Arm progress"
  let b ← curBlock p.clif
  match b.body[p.clif.idx]? with
  | some st =>
    if isMem st.inst || (st.inst matches .call ..) then return p
    if isTrapping st.inst then
      let (_, traps) ← clifEval st p.clif
      if (List.range nSamples).any fun k => p.live[k]! && traps[k]! then return p
    let p ← execStmt p ind st
    advance p ind stopAt (fuel - 1)
  | none =>
    match b.term with
    | .jump dest => do
      let p ← takeEdge p ind dest (fun info => joinC (#[s!"{info.fname}.block_{dest.block}",
        s!"{info.fname}.params_{dest.block}"])) s!"refine GoodF.jump (n := n) ?_"
      if stopAt == some dest.block then return p
      advance p ind stopAt (fuel - 1)
    | .brif c t e => do
      let some cn := p.clif.regs.get? c | gfail s!"brif on unknown v{c}"
      match ← liveBool p.live cn with
      | none => return p
      | some dir =>
        let info ← (read : GM FnInfo)
        emit ind s!"refine GoodF.brif (n := n) ?_; vclif [{← clifList p}, {info.fname}.block_{t.block}, {info.fname}.params_{t.block}, {info.fname}.block_{e.block}, {info.fname}.params_{e.block}]"
        let hc ← freshName "hc"
        if dir then emit ind s!"refine ⟨fun {hc} => ?_, fun {hc} => by {bvContra}⟩"
        else emit ind s!"refine ⟨fun {hc} => by {bvContra}, fun {hc} => ?_⟩"
        let dest := if dir then t else e
        let p := { p with hyps := p.hyps.push hc }
        let p ← enter p dest
        if stopAt == some dest.block then return p
        advance p ind stopAt (fuel - 1)
    | _ => return p
where
  takeEdge (p : Path) (ind : Nat) (dest : Clif.BlockCall) (lemmas : FnInfo → String) (tac : String) :
      SM Path := do
    let info ← (read : GM FnInfo)
    emit ind s!"{tac}; vclif [{← clifList p}, {lemmas info}]"
    enter p dest
  enter (p : Path) (dest : Clif.BlockCall) : SM Path := do
    let info ← (read : GM FnInfo)
    let some nb := info.F.block? dest.block | gfail s!"no block {dest.block}"
    let mut regs := p.clif.regs
    let mut argNodes := #[]
    for a in dest.args do
      let some n := p.clif.regs.get? a | gfail s!"branch argument v{a} unknown"
      argNodes := argNodes.push n
    for ((v, _), n) in nb.params.zip argNodes.toList do regs := regs.insert v n
    return { p with clif := { block := dest.block, idx := 0, regs }, termDone := true }

end Validate.Gen

namespace Validate.Gen

open Std

/-! ## Relation at a cut point -/

/-- Describe the Arm registers of `p` (all samples: path-independent facts only). -/
def describe (p : Path) : SM (Array (Option Desc)) := do
  let info ← (read : GM FnInfo)
  let gs ← get
  let live := (info.liveIn.get? p.clif.block).getD #[]
  -- candidate CLIF values: live-in first, then the others; wider first
  let mut cands : Array (Nat × Nat × Nat) := #[]   -- (v, width, node)
  for (v, nd) in p.clif.regs.toList do
    let w := (info.valTy.get? v).map (·.width) |>.getD 64
    cands := cands.push (v, w, nd)
  cands := cands.qsort fun (v1, w1, _) (v2, w2, _) =>
    let l1 := live.contains v1
    let l2 := live.contains v2
    if l1 != l2 then l1 else if w1 != w2 then w1 > w2 else v1 < v2
  let sp0 := gs.entryNodes[31]!
  let mut out := #[]
  for i in [0:32] do
    let n := p.arm.regs[i]!
    let mut d : Option Desc := none
    if let some c ← liftSym (constOf? n) then d := some (.const c)
    if d.isNone && i != 31 then
      for (v, w, nd) in cands do
        if d.isNone then
          if (← liftSym (constOf? nd)).isNone && (← liftSym (agree w n nd)) then d := some (.clif v w)
    if d.isNone then
      for j in [0:31] do
        if d.isNone && (← liftSym (agree 64 n gs.entryNodes[j]!)) then d := some (.entry j)
    if d.isNone then
      if let some c ← liftSym (constDiff n sp0) then d := some (.spOff c)
    out := out.push d
  return out

/-- Build the invariant of a cut point from a path arriving there. -/
def mkInv (p : Path) (off : Nat) : SM CutInv := do
  let info ← (read : GM FnInfo)
  let regs ← describe p
  let live := (info.liveIn.get? p.clif.block).getD #[]
  let mut atoms : Array (Nat × Clif.Ty) := #[]
  let mut consts : Array (Nat × Clif.Ty × BitVec 64) := #[]
  let mut needed : Array Nat := live
  for d in regs do
    if let some (.clif v _) := d then if !needed.contains v then needed := needed.push v
  for v in needed do
    let some ty := info.valTy.get? v | gfail s!"no type for v{v}"
    let some nd := p.clif.regs.get? v | gfail s!"live value v{v} has no value at cut {off}"
    match ← liftSym (constOf? nd) with
    | some c => consts := consts.push (v, ty, maskW ty.width c)
    | none => atoms := atoms.push (v, ty)
  -- facts about constants-valued CLIF values must not be claimed through registers
  return { off, block := p.clif.block, regs, atoms, consts }

/-- Keep only the facts of `a` that `b` also has. -/
def intersect (a b : CutInv) : CutInv × Bool := Id.run do
  let mut regs := a.regs
  let mut changed := false
  for i in [0:32] do
    if a.regs[i]! != b.regs[i]! && a.regs[i]!.isSome then
      regs := regs.set! i none
      changed := true
  -- atoms: live-in atoms stay; drop atoms no longer referenced
  (({ a with regs }), changed)

end Validate.Gen
