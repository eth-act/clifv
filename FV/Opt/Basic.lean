import FV.Clif.Syntax
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Mid-end basics: operands, pure nodes, substitutions

Vocabulary shared by the passes of `FV/Opt` (`docs/contracts/midend.md`):

* `Inst.operands` / `Inst.mapOperands`: the values an instruction reads, and renaming them.
* `Inst.isPure`: the *pure nodes* — single-result instructions whose `Clif.evalInst` neither
  reads nor writes memory, never traps and does not depend on anything but its operands
  (and, for `stack_addr`/`symbol_value`, on per-activation constants). On a well-formed
  function (`Opt.check`) their evaluation cannot be `stuck` either (except `symbol_value` of
  an undefined symbol, which is why LICM does not hoist it). All other instructions form the
  *skeleton* and are never moved, removed (except dead `Inst.removable` ones) or duplicated.
* `Subst`: a renaming of values `v ↦ w` meaning "every use of `v` may read `w` instead".
-/

namespace Opt

open Clif

deriving instance Hashable for Clif.Ty, Clif.UnaryOp, Clif.BinaryOp, Clif.DivOp,
  Clif.OverflowOp, Clif.CarryOp, Clif.ExtendOp, Clif.LoadOp, Clif.StoreOp, Clif.AtomicRmwOp,
  Clif.TrapCode, Clif.Endianness, Clif.MemFlags, Clif.IntCC, Clif.Inst

/-- The values an instruction reads, in operand order. -/
def operands : Inst → List ValueId
  | .iconst .. | .stackAddr .. | .fence | .nop | .symbolValue .. => []
  | .unary _ _ x | .bmask _ x | .extend _ _ x | .ireduce _ x | .isplit _ x
  | .load _ _ _ x _ | .atomicLoad _ _ x | .bitcast _ _ x | .trapz x _ | .trapnz x _ => [x]
  | .binary _ _ x y | .div _ _ x y | .overflow _ _ x y | .uaddOverflowTrap _ x y _
  | .icmp _ _ x y | .iconcat _ x y | .store _ _ _ x y _ | .atomicRmw _ _ _ x y
  | .atomicStore _ _ x y => [x, y]
  | .carry _ _ x y c => [x, y, c]
  | .select _ c x y | .selectSpectreGuard _ c x y | .bitselect _ c x y => [c, x, y]
  | .atomicCas _ _ p e x => [p, e, x]
  | .call _ args => args

/-- Rename the operands of an instruction (results are not part of `Inst`). -/
def mapOperands (f : ValueId → ValueId) : Inst → Inst
  | .iconst ty i => .iconst ty i
  | .unary op ty x => .unary op ty (f x)
  | .binary op ty x y => .binary op ty (f x) (f y)
  | .div op ty x y => .div op ty (f x) (f y)
  | .overflow op ty x y => .overflow op ty (f x) (f y)
  | .carry op ty x y c => .carry op ty (f x) (f y) (f c)
  | .uaddOverflowTrap ty x y code => .uaddOverflowTrap ty (f x) (f y) code
  | .icmp cc ty x y => .icmp cc ty (f x) (f y)
  | .select ty c x y => .select ty (f c) (f x) (f y)
  | .selectSpectreGuard ty c x y => .selectSpectreGuard ty (f c) (f x) (f y)
  | .bitselect ty c x y => .bitselect ty (f c) (f x) (f y)
  | .bmask ty x => .bmask ty (f x)
  | .extend op ty x => .extend op ty (f x)
  | .ireduce ty x => .ireduce ty (f x)
  | .iconcat ty lo hi => .iconcat ty (f lo) (f hi)
  | .isplit ty x => .isplit ty (f x)
  | .load op ty fl p off => .load op ty fl (f p) off
  | .store op ty fl x p off => .store op ty fl (f x) (f p) off
  | .stackAddr ty s off => .stackAddr ty s off
  | .call fn args => .call fn (args.map f)
  | .atomicRmw op ty fl p x => .atomicRmw op ty fl (f p) (f x)
  | .atomicCas ty fl p e x => .atomicCas ty fl (f p) (f e) (f x)
  | .atomicLoad ty fl p => .atomicLoad ty fl (f p)
  | .atomicStore ty fl x p => .atomicStore ty fl (f x) (f p)
  | .fence => .fence
  | .bitcast ty fl x => .bitcast ty fl (f x)
  | .trapz c code => .trapz (f c) code
  | .trapnz c code => .trapnz (f c) code
  | .nop => .nop
  | .symbolValue ty gv => .symbolValue ty gv

/-- Pure nodes (see the module doc). `select_spectre_guard` is kept in the skeleton, as a
barrier Cranelift also never rewrites away. -/
def isPure : Inst → Bool
  | .iconst .. | .unary .. | .binary .. | .icmp .. | .select .. | .bitselect .. | .bmask ..
  | .extend .. | .ireduce .. | .iconcat .. | .bitcast .. | .stackAddr .. | .symbolValue .. => true
  | _ => false

/-- Instructions DCE may delete when none of their results is used: the pure nodes, and the
non-trapping, memory-free multi-result arithmetic (and `nop`). -/
def removable (i : Inst) : Bool :=
  isPure i || match i with
    | .overflow .. | .carry .. | .isplit .. | .nop => true
    | _ => false

def mapBlockCall (f : ValueId → ValueId) (bc : BlockCall) : BlockCall :=
  { bc with args := bc.args.map f }

def termOperands : Terminator → List ValueId
  | .jump d => d.args
  | .brif c t e => c :: t.args ++ e.args
  | .brTable x d t => x :: d.args ++ t.flatMap (·.args)
  | .ret vs => vs
  | .returnCall _ args => args
  | .trap _ => []

def mapTerm (f : ValueId → ValueId) : Terminator → Terminator
  | .jump d => .jump (mapBlockCall f d)
  | .brif c t e => .brif (f c) (mapBlockCall f t) (mapBlockCall f e)
  | .brTable x d t => .brTable (f x) (mapBlockCall f d) (t.map (mapBlockCall f))
  | .ret vs => .ret (vs.map f)
  | .returnCall fn args => .returnCall fn (args.map f)
  | .trap c => .trap c

/-- Successor blocks of a terminator (with repetitions, in order). -/
def termSuccs : Terminator → List BlockId
  | .jump d => [d.block]
  | .brif _ t e => [t.block, e.block]
  | .brTable _ d t => d.block :: t.map (·.block)
  | .ret _ | .returnCall .. | .trap _ => []

/-- A value renaming. Chains `v ↦ w ↦ u` are followed (`Subst.find`); the passes only ever
map a value to one defined strictly before it in dominance order, so chains are finite. -/
abbrev Subst := Std.HashMap ValueId ValueId

/-- Follow a substitution chain (bounded by the map size, so total even on a cyclic map). -/
def Subst.find (s : Subst) (v : ValueId) : ValueId := Id.run do
  let mut x := v
  for _ in [0:s.size + 1] do
    match s.get? x with
    | some y => x := y
    | none => return x
  return x

/-- Apply a substitution to every operand and branch argument of a function. Parameters and
results are unchanged. -/
def Subst.apply (s : Subst) (f : Function) : Function :=
  if s.isEmpty then f else
  let g := s.find
  { f with blocks := f.blocks.map fun b =>
      { b with body := b.body.map (fun st => { st with inst := mapOperands g st.inst }),
               term := mapTerm g b.term } }

/-- Largest value id defined or used in `f` (0 if none); fresh values start above it. -/
def maxValue (f : Function) : ValueId :=
  f.blocks.foldl (fun m b =>
    let m := b.params.foldl (fun m p => max m p.1) m
    let m := b.body.foldl (fun m st =>
      (st.results ++ operands st.inst).foldl max m) m
    (termOperands b.term).foldl max m) 0

/-- Number of instructions (statements, not terminators) of a function. -/
def instCount (f : Function) : Nat := f.blocks.foldl (· + ·.body.length) 0

end Opt
