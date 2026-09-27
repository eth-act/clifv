import FV.Clif.Syntax

/-!
# The emitter subset E (`clif-subset-v1`, `docs/contracts/clif-subset.md`)

`Compile.onlySubsetE p` holds iff every instruction, terminator, type and memory flag of `p`
is in list E: integer types `i8 … i64`; the opcodes of the E table; memory flags limited to
`notrap`/`aligned` (little-endian, no `readonly`/`can_move`).
-/

namespace Compile

open Clif

def tyE (t : Ty) : Bool := t != .i128

def unaryE : UnaryOp → Bool
  | .ineg | .bnot | .clz | .ctz | .popcnt => true
  | _ => false

def binaryE : BinaryOp → Bool
  | .iadd | .isub | .imul | .umulhi | .smulhi | .band | .bor | .bxor
  | .ishl | .ushr | .sshr | .rotl | .rotr => true
  | _ => false

def flagsE (f : MemFlags) : Bool :=
  f.endianness.isNone && !f.readonly && !f.canMove &&
    (f.trapCode.isNone || f.trapCode == some .heapOob)

def instE : Inst → Bool
  | .iconst ty _ => tyE ty
  | .unary op ty _ => unaryE op && tyE ty
  | .binary op ty _ _ => binaryE op && tyE ty
  | .div _ ty _ _ => tyE ty
  | .icmp _ ty _ _ => tyE ty
  | .extend _ ty _ => tyE ty
  | .ireduce ty _ => tyE ty
  | .load _ ty f _ _ => tyE ty && flagsE f
  | .store _ ty f _ _ _ => tyE ty && flagsE f
  | .stackAddr ty _ _ => tyE ty
  | .call _ _ => true
  | _ => false

def termE : Terminator → Bool
  | .jump _ | .brif _ _ _ | .brTable _ _ _ | .ret _ | .trap _ => true
  | .returnCall _ _ => false

def sigE (s : Signature) : Bool :=
  s.params.all (tyE ·.ty) && s.returns.all (tyE ·.ty)

def functionE (f : Function) : Bool :=
  sigE f.sig && f.globals.isEmpty && f.externs.all (sigE ·.2.sig) &&
    f.blocks.all fun b =>
      b.params.all (tyE ·.2) && b.body.all (instE ·.inst) && termE b.term

/-- Every function of `p` uses only subset E. -/
def onlySubsetE (p : Program) : Bool := p.funcs.all functionE

end Compile
