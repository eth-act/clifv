import FV.Opt.Rules
import FV.Clif.Run

/-!
# A small hand-written rule set (stand-in for the exported Cranelift `simplify` rules)

Same interface as the exported rules (`Opt.SimplifyFn`), used for testing the driver and as a
fallback. The rules are a subset of Cranelift's `cprop.isle` / `arithmetic.isle` /
`bitops.isle` / `icmp.isle` / `selects.isle`, restricted to integer scalars:

* `cprop`: a pure node whose operands are all constants is replaced by the constant that
  `Clif.evalInst` computes for it (so this rule is correct by construction), `subsume`;
* identities: `x+0 x-0 x|0 x^0 x*1 x&-1 x<<0 …  ⇒ x`, `x-x x^x x*0 x&0 ⇒ 0`,
  `x&x x|x ⇒ x`, `--x ~~x ⇒ x`, `select c x x ⇒ x`, `icmp cc x x ⇒ 0/1`, `subsume`;
* canonicalisation: constants to the right of commutative operators; `x - k ⇒ x + (-k)`;
* reassociation of constants: `(x + k1) + k2 ⇒ x + (k1+k2)`;
* strength reduction: `x * 2^k ⇒ x << k`.
-/

namespace Opt.HandRules

open Clif

/-- A frame whose registers are the given constants (for evaluating pure nodes). -/
def constFrame (regs : Regs) : Frame :=
  { func := default, regs, slots := [], body := [], term := .trap .intDivz }

/-- Evaluate a pure node on constant operands (not `stack_addr`/`symbol_value`). -/
def fold (cst : ValueId → Option Val) (n : Inst) : Option Val :=
  match n with
  | .stackAddr .. | .symbolValue .. | .iconst .. => none
  | _ =>
    if !isPure n || !(operands n).all (cst · |>.isSome) then none else
    match evalInst (constFrame cst) Mem.empty n with
    | .ok ([r], _) => if r.ty == .i128 then none else some r
    | _ => none

def isCommutative : BinaryOp → Bool
  | .iadd | .imul | .band | .bor | .bxor | .umulhi | .smulhi
  | .smin | .smax | .umin | .umax | .uaddSat | .saddSat => true
  | _ => false

/-- `x op 0 = x` (right identity 0). -/
def rightZeroId : BinaryOp → Bool
  | .iadd | .isub | .bor | .bxor | .ishl | .ushr | .sshr | .rotl | .rotr => true
  | _ => false

/-- The exponent `k` if `x = 2^k` with `k > 0`. -/
def log2? (x : Nat) : Option Nat :=
  let k := Nat.log2 x
  if k > 0 && 2 ^ k == x then some k else none

def simplify : SimplifyFn := fun {σ} enodes typeOf make st0 v => Id.run do
  let mut st : σ := st0
  let mut out : Array (ValueId × Bool) := #[]
  let mut names : Array String := #[]
  let cstIn := fun (st : σ) (x : ValueId) =>
    (enodes st x).findSome? fun | .iconst t i => some (Val.mk t i) | _ => none
  let isC := fun (st : σ) (x : ValueId) (k : Int) => match cstIn st x with
    | some c => c.bits == BitVec.ofInt c.ty.width k
    | none => false
  let mkConst := fun (st : σ) (t : Ty) (k : Int) => make st (.iconst t (BitVec.ofInt t.width k))
  for n in enodes st0 v do
    -- cprop
    if let some r := fold (cstIn st) n then
      let (w, st') := make st (.iconst r.ty r.bits)
      st := st'; out := out.push (w, true); names := names.push "cprop"
      continue
    match n with
    | .binary op t x y =>
      if rightZeroId op && isC st y 0 then
        out := out.push (x, true); names := names.push "x_op_zero"
      else if isCommutative op && op != .umulhi && op != .smulhi && isC st x 0 &&
          (op == .iadd || op == .bor || op == .bxor) then
        out := out.push (y, true); names := names.push "zero_op_x"
      else if op == .imul && isC st y 1 then
        out := out.push (x, true); names := names.push "x_mul_one"
      else if op == .band && isC st y (-1) then
        out := out.push (x, true); names := names.push "x_and_ones"
      else if (op == .band || op == .bor || op == .smin || op == .smax || op == .umin ||
          op == .umax) && x == y then
        out := out.push (x, true); names := names.push "x_op_x_idem"
      else if (op == .isub || op == .bxor) && x == y && t != .i128 then
        let (w, st') := mkConst st t 0
        st := st'; out := out.push (w, true); names := names.push "x_op_x_zero"
      else if (op == .imul || op == .band) && isC st y 0 && t != .i128 then
        let (w, st') := mkConst st t 0
        st := st'; out := out.push (w, true); names := names.push "x_op_zero_zero"
      else if isCommutative op && (cstIn st x).isSome && (cstIn st y).isNone then
        let (w, st') := make st (.binary op t y x)
        st := st'; out := out.push (w, false); names := names.push "commute_const_right"
      else if op == .isub && t != .i128 then
        if let some k := cstIn st y then
          let (c, st1) := mkConst st t (-k.toInt)
          let (w, st2) := make st1 (.binary .iadd t x c)
          st := st2; out := out.push (w, false); names := names.push "isub_const_to_iadd"
      else if op == .iadd && t != .i128 then
        match cstIn st y with
        | some k2 =>
          -- (x + k1) + k2
          let inner := (enodes st x).findSome? fun
            | .binary .iadd _ a b => (cstIn st b).map (a, ·)
            | _ => none
          if let some (a, k1) := inner then
            let (c, st1) := mkConst st t (k1.toInt + k2.toInt)
            let (w, st2) := make st1 (.binary .iadd t a c)
            st := st2; out := out.push (w, false); names := names.push "iadd_reassoc_const"
        | none => pure ()
      else if op == .imul && t != .i128 then
        if let some k := cstIn st y then
          if let some s := log2? k.toNat then
            let (c, st1) := mkConst st t s
            let (w, st2) := make st1 (.binary .ishl t x c)
            st := st2; out := out.push (w, false); names := names.push "imul_pow2_to_ishl"
    | .unary op _ x =>
      if op == .ineg || op == .bnot then
        let inner := (enodes st x).findSome? fun
          | .unary op' _ a => if op' == op then some a else none
          | _ => none
        if let some a := inner then
          out := out.push (a, true); names := names.push "double_negation"
    | .select _ _ x y =>
      if x == y then
        out := out.push (x, true); names := names.push "select_same"
    | .icmp cc _ x y =>
      if x == y then
        let r : Int := match cc with
          | .eq | .uge | .ule | .sge | .sle => 1
          | _ => 0
        let (w, st') := mkConst st .i8 r
        st := st'; out := out.push (w, true); names := names.push "icmp_same"
    | _ => pure ()
  let _ := typeOf
  return .ok (out.toList, names.toList, st)


end Opt.HandRules
