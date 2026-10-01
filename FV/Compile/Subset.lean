import FV.Clif.Syntax

/-!
# The emitter subset E (`clif-subset-v2`, `docs/contracts/clif-subset.md`)

`Compile.onlySubsetE p` holds iff every instruction, terminator, type and memory flag of `p`
is in list E: integer types `i8 … i64`; the opcodes of the E table; memory flags limited to
`notrap`/`aligned` (little-endian, no `readonly`/`can_move`).
-/

namespace Compile

open Clif

def tyE (t : Ty) : Bool := t != .i128

def unaryE : UnaryOp → Bool
  | .ineg | .bnot | .clz | .ctz | .popcnt | .bitrev => true
  | _ => false

/-- `bswap` needs at least two bytes (the reader's `iSwappable` = i16..i128). -/
def unaryTyE : UnaryOp → Ty → Bool
  | .bswap, t => t != .i8 && t != .i128
  | op, t => unaryE op && tyE t

def binaryE : BinaryOp → Bool
  | .iadd | .isub | .imul | .umulhi | .smulhi | .band | .bor | .bxor
  | .ishl | .ushr | .sshr | .rotl | .rotr
  | .smin | .smax | .umin | .umax => true
  | _ => false

def flagsE (f : MemFlags) : Bool :=
  f.endianness.isNone && !f.canMove &&
    (f.trapCode.isNone || f.trapCode == some .heapOob)

def instE : Inst → Bool
  | .iconst ty _ => tyE ty
  | .unary op ty _ => unaryTyE op ty
  | .binary op ty _ _ => binaryE op && tyE ty
  | .div _ ty _ _ => tyE ty
  | .icmp _ ty _ _ => tyE ty
  | .extend _ ty _ => tyE ty
  | .ireduce ty _ => tyE ty
  | .load _ ty f _ _ => tyE ty && flagsE f
  | .store _ ty f _ _ _ => tyE ty && flagsE f
  | .stackAddr ty _ _ => tyE ty
  | .select ty _ _ _ => tyE ty
  | .symbolValue ty _ => ty == .i64
  | .nop => true
  | .call _ _ => true
  -- rust-route step 4: indirect calls (of externs: `E2E.InSubset`, `TrapsExplicit.indirect`)
  -- and function addresses
  | .callIndirect _ _ _ => true
  | .funcAddr ty _ => ty == .i64
  -- `bmask`, the atomics (single-threaded: `ldar`/`stlr`, the LL/SC loops of `atomic_rmw` and
  -- `atomic_cas`; Cranelift's non-LSE lowering) and `fence`
  | .bmask ty _ => tyE ty
  | .atomicLoad ty f _ => tyE ty && flagsE f
  | .atomicStore ty f _ _ => tyE ty && flagsE f
  | .atomicRmw _ ty f _ _ => tyE ty && flagsE f
  | .atomicCas ty f _ _ _ => tyE ty && flagsE f
  | .fence => true
  | _ => false

/-- Global values: only `symbol %name[+offset]` (the target of `symbol_value`). -/
def globalE : GlobalValue → Bool
  | .symbol .. => true
  | _ => false

def termE : Terminator → Bool
  | .jump _ | .brif _ _ _ | .brTable _ _ _ | .ret _ | .trap _ => true
  | .returnCall _ _ => false
  -- `try_call`/`try_call_indirect` of an extern: inside the end-to-end theorem for its normal
  -- return (the landing pads and the LSDA are trusted, `docs/contracts/e2e.md`)
  | .tryCall .. => true
  | .tryCallIndirect .. => true

def sigE (s : Signature) : Bool :=
  s.params.all (tyE ·.ty) && s.returns.all (tyE ·.ty)

def functionE (f : Function) : Bool :=
  sigE f.sig && f.globals.all (globalE ·.2) && f.externs.all (sigE ·.2.sig) &&
    f.blocks.all fun b =>
      b.params.all (tyE ·.2) && b.body.all (instE ·.inst) && termE b.term

/-- Every function of `p` uses only subset E. -/
def onlySubsetE (p : Program) : Bool := p.funcs.all functionE

/-- `instE` of every statement of a subset-E function. -/
theorem instE_of_functionE {f : Function} (hE : functionE f = true) {b : Block} (hb : b ∈ f.blocks)
    {st : Stmt} (hst : st ∈ b.body) : instE st.inst = true := by
  simp only [functionE, Bool.and_eq_true, List.all_eq_true] at hE
  exact (hE.2 b hb).1.2 st hst

end Compile
