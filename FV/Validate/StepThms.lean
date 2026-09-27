/-
Copyright (c) 2026 fv-compiler-rust contributors.
Released under Apache 2.0 license.

# Per-instruction step theorems over an abstract program

Adapted from LNSym's `#genStepEqTheorems` (`FV/Arm/Tactics/StepThms.lean`, Amazon, Apache 2.0):
the same decode-by-reduction and the same simp set normalise `exec_inst`, but the program is
not a global constant. `#vstep pfx addr word` adds

```
theorem pfx.s_<addr> {P : Program} {s : ArmState} (h_prog : s.program = P)
    (h_find : P.find? <addr>#64 = some <word>#32) (h_pc : r .PC s = <addr>#64)
    (h_err : r .ERR s = .None) [(h_sp : CheckSPAlignment s)] :
    stepi s = <effects of the instruction, as `w`/`write_mem_bytes` updates of s>
```

so that a function's code can be placed inside any larger linked program `P`. The
`CheckSPAlignment` hypothesis is present exactly when the instruction's semantics depends on it
(SP-based memory accesses); it removes the alignment-fault branch.
-/
import Lean
import FV.Arm.Tactics.StepThms

namespace Validate

open Lean Meta Elab Command Arm

theorem stepi_eq_of_find {P : Program} {s : ArmState} {addr : _root_.BitVec 64}
    {raw : _root_.BitVec 32} {inst : ArmInst} (h_prog : s.program = P)
    (h_find : P.find? addr = some raw) (h_pc : r .PC s = addr) (h_err : r .ERR s = .None)
    (h_decode : decode_raw_inst raw = some inst) :
    stepi s = exec_inst inst s :=
  stepi_eq_of_fetch_inst_of_decode_raw_inst s addr raw inst h_err h_pc
    (fetch_inst_eq_of_prgram_eq_of_map_find h_prog h_find) h_decode

/-- Does `e` mention constant `n`? -/
private def mentions (e : Expr) (n : Name) : Bool := (e.find? fun e => e.isConstOf n).isSome

/-- Build the statement and proof of the step theorem for `word` at `addr`. -/
def mkStepThm (addr : _root_.BitVec 64) (word : _root_.BitVec 32) : MetaM (Expr × Expr) := do
  let optInst ← reduceDecodeInstExpr (toExpr word)
  let_expr Option.some _ inst := optInst
    | throwError "#vstep: {word} does not decode ({optInst})"
  let progTy := mkConst ``Arm.Program
  let bv64 := mkApp (mkConst ``_root_.BitVec) (toExpr 64)
  let bv32 := mkApp (mkConst ``_root_.BitVec) (toExpr 32)
  withLocalDecl `P .implicit progTy fun P =>
  withLocalDecl `s .implicit (mkConst ``Arm.ArmState) fun s =>
  withLocalDeclD `h_prog (SymContext.h_program_type s P) fun h_prog => do
  let findTy ← mkEq (mkAppN (mkConst ``Arm.Map.find? [0, 0]) #[bv64, bv32,
      (← synthInstance (mkApp (mkConst ``DecidableEq [1]) bv64)), P, toExpr addr])
    (toExpr (some word))
  withLocalDeclD `h_find findTy fun h_find =>
  withLocalDeclD `h_pc (SymContext.h_pc_type s (toExpr addr)) fun h_pc =>
  withLocalDeclD `h_err (SymContext.h_err_type s) fun h_err => do
    let armInstTy := mkConst ``Arm.ArmInst
    let h_decode := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) armInstTy)
      (mkApp2 (mkConst ``Option.some [0]) armInstTy inst)
    let proof := mkAppN (mkConst ``stepi_eq_of_find)
      #[P, s, toExpr addr, toExpr word, inst, h_prog, h_find, h_pc, h_err, h_decode]
    let type ← inferType proof
    let simpWith (extra : Array Expr) : MetaM Simp.Result := do
      let decls ← [h_pc, h_err].filterMapM fun e => return (← getLCtx).findFVar? e
      let (ctx, simprocs) ← LNSymSimpContext
        (config := {decide := true, ground := false})
        (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
        (decls := decls.toArray) (exprs := extra)
        (decls_to_unfold := #[``Arm.exec_inst])
      let ⟨res, _⟩ ← simp type ctx simprocs
      return res
    let res ← simpWith #[]
    let_expr Eq _ _ sem := res.expr
      | throwError "#vstep: could not normalise the semantics of {word}: {res.expr}"
    if mentions sem ``Arm.CheckSPAlignment then
      withLocalDeclD `h_sp (mkApp (mkConst ``Arm.CheckSPAlignment) s) fun h_sp => do
        let res ← simpWith #[h_sp]
        let proof ← res.mkCast proof
        let hs := #[P, s, h_prog, h_find, h_pc, h_err, h_sp]
        return (← mkForallFVars hs res.expr, ← mkLambdaFVars hs proof)
    else
      let proof ← res.mkCast proof
      let hs := #[P, s, h_prog, h_find, h_pc, h_err]
      return (← mkForallFVars hs res.expr, ← mkLambdaFVars hs proof)

/-- `#vstep pfx addr word`: add theorem `pfx.s_<addr in hex>` (see the module doc). -/
elab "#vstep " pfx:ident addr:num word:num : command => liftTermElabM do
  let a : _root_.BitVec 64 := _root_.BitVec.ofNat 64 addr.getNat
  let wd : _root_.BitVec 32 := _root_.BitVec.ofNat 32 word.getNat
  let (type, value) ← mkStepThm a wd
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  let name := pfx.getId ++ Name.mkSimple ("s_" ++ String.ofList (Nat.toDigits 16 a.toNat))
  addDecl <| Declaration.thmDecl { name, type, value, levelParams := [] }

end Validate
