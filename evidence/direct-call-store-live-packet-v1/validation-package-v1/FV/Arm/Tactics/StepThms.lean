/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Alex Keizer
-/
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in namespace Arm, the in-file example moved to FVTest.Arm.Sym.StepThms.
import Lean
import FV.Arm.Map
import FV.Arm.Decode
import FV.Arm.Exec
import FV.Arm.Tactics.Common
import FV.Arm.Tactics.Simp
import FV.Arm.Tactics.Sym.ProgramInfo

namespace Arm

open Lean Lean.Expr Lean.Meta Lean.Elab Lean.Elab.Command
open SymContext (h_pc_type h_program_type h_err_type)

/-
Command to autogenerate fetch, decode, execute, and stepi theorems for
a given program.
Invocation:
#genStepEqTheorems <program_map>

For every address `<addr>` of the program `<program_map>` a theorem
`<program_map>.stepi_eq_0x<addr>` is added to the environment; see `reduceStepi`
for its statement.
-/


/- When true, prints the names of the generated theorems. -/
initialize registerTraceClass `gen_step.print_names
/- When true, prints debugging information. -/
initialize registerTraceClass `gen_step.debug
/- When true, prints the number of heartbeats taken per theorem. -/
initialize registerTraceClass `gen_step.debug.heartBeats
/- When true, prints the time taken at various steps of generation. -/
initialize registerTraceClass `gen_step.debug.timing

/-- Assuming that `rawInst` is indeed the right result, construct a proof that
  `fetch_inst addr state = some rawInst`
given that `state.program = program` -/
private def fetchLemma (state program h_program : Expr)
    (addr : _root_.BitVec 64) (rawInst : _root_.BitVec 32) : Expr :=
  let someRawInst := toExpr (some rawInst)
  mkAppN (mkConst ``Arm.fetch_inst_eq_of_prgram_eq_of_map_find) #[
    state,
    program,
    toExpr addr,
    someRawInst,
    h_program,
    mkApp2 (.const ``Eq.refl [1])
      (mkApp (.const ``Option [0]) <|
        mkApp (.const ``_root_.BitVec []) (toExpr 32))
      someRawInst
  ]

-- /-! ## `reduceDecodeInst` -/

/-- `canonicalizeBitVec e` recursively walks over expression `e` to convert any
occurrences of:
  `BitVec.ofFin w (Fin.mk x _)`
to the canonical form:
  `BitVec.ofNat w x` (i.e., `x#w`)

Such expressions tend to result from using `reduce` or
`simp` with `{ground := true}`.
You can call `canonicalizeBitVec` after these functions to ensure you don't
needlessly expose `BitVec` internal details -/
-- TODO: should this canonicalize to `BitVec.ofNatLt` instead,
--       as the current transformation loses information?
partial def canonicalizeBitVec (e : Expr) : MetaM Expr := do
  match_expr e with
    | _root_.BitVec.ofFin w i =>
        let_expr Fin.mk _ x _h := i | fallback
        let w ←
          if w.hasFVar || w.hasMVar then
            pure w
          else
            withTransparency .all <| reduce w
            -- ^^ NOTE: potentially expensive reduction
        return mkApp2 (mkConst ``_root_.BitVec.ofNat) w x
    | _ => fallback
  where
    fallback : MetaM Expr := do
      let fn   := e.getAppFn
      let args  ← e.getAppArgs.mapM canonicalizeBitVec
      return mkAppN fn args

/-- Given an expr `rawInst` of type `BitVec 32`,
return an expr of type `Option ArmInst` representing what `rawInst` decodes to.
The resulting expr is guaranteed to be def-eq to `decode_raw_inst $rawInst` -/
def reduceDecodeInstExpr (rawInst : Expr) : MetaM Expr := do
  let expr := mkApp (mkConst ``Arm.decode_raw_inst) rawInst
  let expr ← withTransparency .all <| reduce expr
  -- ^^ NOTE: possibly expensive reduction
  canonicalizeBitVec expr

/-! ## StepThmsM Monad -/

abbrev StepThmsM.CacheKey := _root_.BitVec 32
abbrev StepThmsM.CacheM := MonadCacheT CacheKey Expr MetaM
abbrev StepThmsM := ProgramInfoT <| MonadCacheT StepThmsM.CacheKey Expr MetaM

@[inherit_doc ProgramInfoT.run]
abbrev StepThmsM.run (name : Name) (k : StepThmsM α) (persist : Bool := true) : MetaM α :=
  MonadCacheT.run <| ProgramInfoT.run name k persist

open StepThmsM in
/-- Given a (reflected) raw instruction,
return an expr of type `Option ArmInst` representing what `rawInst` decodes to.
The resulting expr is guaranteed to be def-eq to `decode_raw_inst $rawInst`.

Results are cached so that the same instruction is not reduced multiple times -/
def reduceDecodeInst (rawInst : _root_.BitVec 32) : CacheM Expr :=
  checkCache (rawInst) fun _ =>
    reduceDecodeInstExpr (toExpr rawInst)

open ProgramInfoT InstInfoT

/-! ## reduceStepiToExecInst -/

/-- Given a program and an address, and optionally the corresponding
raw and decoded instructions, construct and return first the expression:
```
∀ {s} (h_program : s.program = <progam>) (h_pc : r .PC s = <addr>)
  (h_err : r .ERR s = .None),
  stepi s = <reduced form of `exec_inst <inst> s`>
```
and then a proof of this fact.
That is, in
  `let ⟨type, value⟩ ← reduceStepi ...`
`value` is an expr whose type is `type` -/
def reduceStepi (addr : _root_.BitVec 64) : StepThmsM (Expr × Expr) := do
  let pi : ProgramInfo ← get
  let ⟨_, type, proof⟩ ← modifyInstInfoAt addr <| getInstSemantics fun _ => do
    let rawInst ← getRawInst

    let inst ← getDecodedInst <| fun _ => do
      let optInst ← reduceDecodeInst rawInst
      let_expr Option.some _ inst := optInst
        | let some := mkConst ``Option.some [1]
          throwError "Expected an application of {some}, found:\n\t{optInst}"
      pure inst

    withLocalDecl `s .implicit (mkConst ``Arm.ArmState) <| fun s =>
    withLocalDeclD `h_program (h_program_type s pi.expr)  <| fun h_program =>
    withLocalDeclD `h_pc      (h_pc_type s (toExpr addr)) <| fun h_pc =>
    withLocalDeclD `h_err     (h_err_type s)              <| fun h_err => do
      let h_fetch  := fetchLemma s pi.expr h_program addr rawInst
      let h_decode :=
        let armInstTy := mkConst ``Arm.ArmInst
        mkApp2 (mkConst ``Eq.refl [1])
          (mkApp (mkConst ``Option [0]) armInstTy)
          (mkApp2 (mkConst ``Option.some [0]) armInstTy inst)

      let proof := -- stepi s = exec_inst <inst> s
        mkAppN (mkConst ``Arm.stepi_eq_of_fetch_inst_of_decode_raw_inst) #[
          s, toExpr addr, toExpr rawInst, inst,
          h_err, h_pc, h_fetch, h_decode
        ]
      let type ← inferType proof

      let (ctx, simprocs) ← do
        let localDecls ← do
          let hs := #[h_pc, h_err]
          pure <| hs.filterMap (← getLCtx).findFVar?
        LNSymSimpContext
          (config := {decide := true, ground := false})
          (simp_attrs := #[`minimal_theory, `bitvec_rules, `state_simp_rules])
          (decls := localDecls)
          (decls_to_unfold := #[``Arm.exec_inst])

      let ⟨simpRes, _⟩ ← simp type ctx simprocs

      let_expr Eq _ _ sem := simpRes.expr
        | let eq ← mkEq (← mkFreshExprMVar none) (← mkFreshExprMVar none)
          throwError "Failed to normalize instruction semantics. Expected {eq}, but found:\n\t{simpRes.expr}"
      let sem ← mkLambdaFVars #[s] sem

      let proof ← simpRes.mkCast proof -- stepi s = <reduced to `w ...`>
      let hs := #[s, h_program, h_pc, h_err]
      let proof ← mkLambdaFVars hs proof
      let type  ← mkForallFVars hs simpRes.expr
      return ⟨sem, type, proof⟩
  return ⟨type, proof⟩

def genStepEqTheorems : StepThmsM Unit := do
  let pi ← get
  for ⟨addr, instInfo⟩ in pi.instructions do
    let startTime ← IO.monoMsNow
    let inst := instInfo.rawInst

    trace[gen_step.debug] "[genStepEqTheorems] Generating theorem for address {addr.toHex}\
      with instruction {inst.toHex}"
    let name := let addr_str := Arm.BitVec.toHexWithoutLeadingZeroes addr
                Name.str pi.name ("stepi_eq_0x" ++ addr_str)
    let ⟨type, value⟩ ← reduceStepi addr

    trace[gen_step.debug.timing] "[genStepEqTheorems] reduced in: {(← IO.monoMsNow) - startTime}ms"
    let value ← instantiateMVars value
    let type ← instantiateMVars type
    addDecl <| Declaration.thmDecl {
      name, type, value,
      levelParams := []
    }
    trace[gen_step.print_names] "[genStepEqTheorems] Theorem added: {name}"
    trace[gen_step.debug.timing] "[genStepEqTheorems] added to environment in: {(← IO.monoMsNow) - startTime}ms"

/-- `#genProgramInfo program` ensures the `ProgramInfo` for `program`
has been generated and persistently cached in the enviroment -/
elab "#genProgramInfo" program:ident : command => liftTermElabM do
  let _ ← ProgramInfo.lookupOrGenerate (← realizeGlobalConstNoOverloadWithInfo program)

/-- `#genStepEqTheorems program` generates, for every instruction address `0x<addr>` of
the concrete `program : Program` (a global definition), the theorem
```
program.stepi_eq_0x<addr> {s : ArmState} (h_program : s.program = program)
    (h_pc : r StateField.PC s = <addr>#64) (h_err : r StateField.ERR s = StateError.None) :
  stepi s = <semantics of the instruction at <addr>, as `w`/`write_mem_bytes` updates of s>
```
These are the theorems that `sym_n` uses. -/
elab "#genStepEqTheorems" program:term : command => liftTermElabM do
  let .const name _ ← Elab.Term.elabTerm program (mkConst ``Arm.Program)
    | throwError "Expected a constant, found: {program}"

  StepThmsM.run name (persist := true) <|
    genStepEqTheorems

end Arm
