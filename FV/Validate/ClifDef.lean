/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

# `#clif_def`: a CLIF function as a Lean constant, by parsing its text

`#clif_def F "<text of one CLIF function>"` runs the M0 parser (`Clif.parse`) at elaboration
time and adds

* `F.b<k> : Clif.Block` for every block `block<k>` (the parsed block, as a literal),
* `F : Clif.Function` (the parsed function; its block list refers to the constants above),
* `F.block_<k> : F.block? k = some F.b<k>` (by `rfl`).

The validator states its theorems about `F`, so the link between the `.clif` text and the
Lean value is the M0 parser (trusted, PLAN.md §5).
-/
import Lean
import Lean.Elab.Deriving.ToExpr
import FV.Clif

namespace Validate

open Lean Elab Command Meta

deriving instance Lean.ToExpr for Clif.Ty
deriving instance Lean.ToExpr for Clif.TrapCode
deriving instance Lean.ToExpr for Clif.Endianness
deriving instance Lean.ToExpr for Clif.MemFlags
deriving instance Lean.ToExpr for Clif.IntCC
deriving instance Lean.ToExpr for Clif.UnaryOp
deriving instance Lean.ToExpr for Clif.BinaryOp
deriving instance Lean.ToExpr for Clif.DivOp
deriving instance Lean.ToExpr for Clif.OverflowOp
deriving instance Lean.ToExpr for Clif.CarryOp
deriving instance Lean.ToExpr for Clif.ExtendOp
deriving instance Lean.ToExpr for Clif.LoadOp
deriving instance Lean.ToExpr for Clif.StoreOp
deriving instance Lean.ToExpr for Clif.AtomicRmwOp
deriving instance Lean.ToExpr for Clif.BlockCall

/-- `iconst` carries a width-dependent immediate, so `Inst` gets a hand-written instance. -/
def instToExpr : Clif.Inst → Expr
  | .iconst ty imm =>
    let w := mkApp (mkConst ``Clif.Ty.width) (toExpr ty)
    mkApp2 (mkConst ``Clif.Inst.iconst) (toExpr ty)
      (mkApp2 (mkConst ``BitVec.ofNat) w (mkRawNatLit imm.toNat))
  | .unary op ty x => mkApp3 (mkConst ``Clif.Inst.unary) (toExpr op) (toExpr ty) (toExpr x)
  | .binary op ty x y =>
    mkApp4 (mkConst ``Clif.Inst.binary) (toExpr op) (toExpr ty) (toExpr x) (toExpr y)
  | .div op ty x y => mkApp4 (mkConst ``Clif.Inst.div) (toExpr op) (toExpr ty) (toExpr x) (toExpr y)
  | .overflow op ty x y =>
    mkApp4 (mkConst ``Clif.Inst.overflow) (toExpr op) (toExpr ty) (toExpr x) (toExpr y)
  | .carry op ty x y c =>
    mkApp5 (mkConst ``Clif.Inst.carry) (toExpr op) (toExpr ty) (toExpr x) (toExpr y) (toExpr c)
  | .uaddOverflowTrap ty x y code =>
    mkApp4 (mkConst ``Clif.Inst.uaddOverflowTrap) (toExpr ty) (toExpr x) (toExpr y) (toExpr code)
  | .icmp cc ty x y => mkApp4 (mkConst ``Clif.Inst.icmp) (toExpr cc) (toExpr ty) (toExpr x) (toExpr y)
  | .select ty c x y => mkApp4 (mkConst ``Clif.Inst.select) (toExpr ty) (toExpr c) (toExpr x) (toExpr y)
  | .selectSpectreGuard ty c x y =>
    mkApp4 (mkConst ``Clif.Inst.selectSpectreGuard) (toExpr ty) (toExpr c) (toExpr x) (toExpr y)
  | .bitselect ty c x y =>
    mkApp4 (mkConst ``Clif.Inst.bitselect) (toExpr ty) (toExpr c) (toExpr x) (toExpr y)
  | .bmask ty x => mkApp2 (mkConst ``Clif.Inst.bmask) (toExpr ty) (toExpr x)
  | .extend op ty x => mkApp3 (mkConst ``Clif.Inst.extend) (toExpr op) (toExpr ty) (toExpr x)
  | .ireduce ty x => mkApp2 (mkConst ``Clif.Inst.ireduce) (toExpr ty) (toExpr x)
  | .iconcat ty lo hi => mkApp3 (mkConst ``Clif.Inst.iconcat) (toExpr ty) (toExpr lo) (toExpr hi)
  | .isplit ty x => mkApp2 (mkConst ``Clif.Inst.isplit) (toExpr ty) (toExpr x)
  | .load op ty fl p off =>
    mkApp5 (mkConst ``Clif.Inst.load) (toExpr op) (toExpr ty) (toExpr fl) (toExpr p) (toExpr off)
  | .store op ty fl x p off =>
    mkAppN (mkConst ``Clif.Inst.store)
      #[toExpr op, toExpr ty, toExpr fl, toExpr x, toExpr p, toExpr off]
  | .stackAddr ty s off => mkApp3 (mkConst ``Clif.Inst.stackAddr) (toExpr ty) (toExpr s) (toExpr off)
  | .call fn args => mkApp2 (mkConst ``Clif.Inst.call) (toExpr fn) (toExpr args)
  | .atomicRmw op ty fl p x =>
    mkApp5 (mkConst ``Clif.Inst.atomicRmw) (toExpr op) (toExpr ty) (toExpr fl) (toExpr p) (toExpr x)
  | .atomicCas ty fl p e x =>
    mkApp5 (mkConst ``Clif.Inst.atomicCas) (toExpr ty) (toExpr fl) (toExpr p) (toExpr e) (toExpr x)
  | .atomicLoad ty fl p => mkApp3 (mkConst ``Clif.Inst.atomicLoad) (toExpr ty) (toExpr fl) (toExpr p)
  | .atomicStore ty fl x p =>
    mkApp4 (mkConst ``Clif.Inst.atomicStore) (toExpr ty) (toExpr fl) (toExpr x) (toExpr p)
  | .fence => mkConst ``Clif.Inst.fence
  | .bitcast ty fl x => mkApp3 (mkConst ``Clif.Inst.bitcast) (toExpr ty) (toExpr fl) (toExpr x)
  | .trapz c code => mkApp2 (mkConst ``Clif.Inst.trapz) (toExpr c) (toExpr code)
  | .trapnz c code => mkApp2 (mkConst ``Clif.Inst.trapnz) (toExpr c) (toExpr code)
  | .nop => mkConst ``Clif.Inst.nop

instance : ToExpr Clif.Inst where
  toExpr := instToExpr
  toTypeExpr := mkConst ``Clif.Inst

deriving instance Lean.ToExpr for Clif.Terminator
deriving instance Lean.ToExpr for Clif.Stmt
deriving instance Lean.ToExpr for Clif.Block
deriving instance Lean.ToExpr for Clif.ArgExt
deriving instance Lean.ToExpr for Clif.ArgPurpose
deriving instance Lean.ToExpr for Clif.AbiParam
deriving instance Lean.ToExpr for Clif.CallConv
deriving instance Lean.ToExpr for Clif.Signature
deriving instance Lean.ToExpr for Clif.StackSlot
deriving instance Lean.ToExpr for Clif.GlobalValue
deriving instance Lean.ToExpr for Clif.ExtFunc

/-- Parse exactly one function from `src`. -/
def parseOne (src : String) : Except String Clif.Function := do
  let p ← Clif.parse src
  match p.funcs with
  | [f] => pure f
  | fs => throw s!"expected one function, found {fs.length}"

private def addDef (name : Name) (type value : Expr) : CommandElabM Unit := liftTermElabM do
  addAndCompile <| Declaration.defnDecl
    { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }

/-- `#clif_def F "src"` (see the module doc). -/
elab "#clif_def " id:ident src:str : command => do
  let F := id.getId
  let f ← match parseOne src.getString with
    | .ok f => pure f
    | .error e => throwError "#clif_def: {e}"
  let blockTy := mkConst ``Clif.Block
  let mut blockConsts : Array Expr := #[]
  for b in f.blocks do
    let n := F ++ Name.mkSimple s!"b{b.id}"
    addDef n blockTy (toExpr b)
    blockConsts := blockConsts.push (mkConst n)
  let blocks ← liftTermElabM <| mkListLit blockTy blockConsts.toList
  let value := mkAppN (mkConst ``Clif.Function.mk)
    #[toExpr f.name, toExpr f.sig, toExpr f.slots, toExpr f.globals, toExpr f.externs, blocks,
      mkApp (mkConst ``List.nil [0]) (mkConst ``Clif.RunCommand)]
  addDef F (mkConst ``Clif.Function) value
  for b in f.blocks do
    let n := F ++ Name.mkSimple s!"block_{b.id}"
    let lhs := mkApp2 (mkConst ``Clif.Function.block?) (mkConst F) (toExpr b.id)
    let rhs := mkApp2 (mkConst ``Option.some [0]) blockTy (mkConst (F ++ Name.mkSimple s!"b{b.id}"))
    liftTermElabM do
      let type ← mkEq lhs rhs
      let value ← mkEqRefl rhs
      addDecl <| Declaration.thmDecl { name := n, levelParams := [], type, value }

end Validate
