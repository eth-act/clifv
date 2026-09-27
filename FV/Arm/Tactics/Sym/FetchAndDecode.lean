/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Alex Keizer
-/
-- Modified by fv-compiler-rust (2026): ported to Lean v4.34.1, module prefix FV.Arm, wrapped in namespace Arm.
import FV.Arm.State
import FV.Arm.Tactics.Common
import FV.Arm.Tactics.Sym.ProgramInfo

namespace Arm

open Lean Meta
open Elab.Tactic Elab.Term

initialize
  Lean.registerTraceClass `Sym.reduceFetchInst

def reduceFetchInst? (addr : _root_.BitVec 64) (s : Expr) :
    MetaM (_root_.BitVec 32 × Expr) := do
  let ⟨programHyp, program⟩ ← findProgramHyp s
  let programInfo ← try ProgramInfo.lookupOrGenerate program catch err =>
    throwErrorAt
      err.getRef
      "Could not generate ProgramInfo for {program}:\n\n{err.toMessageData}"

  let some rawInst := programInfo.getRawInstAt? addr
    | throwError "No instruction found at address {addr}"

  trace[Sym.reduceFetchInst] "{Lean.checkEmoji} reduced to: {rawInst}"

  -- Now, construct the proof
  let proof := mkAppN (mkConst ``Arm.fetch_inst_eq_of_prgram_eq_of_map_find) #[
    s,
    mkConst program,
    toExpr addr,
    toExpr (some rawInst),
    programHyp.toExpr,
    mkApp2 (.const ``Eq.refl [1])
      (mkApp (.const ``Option [0]) <|
        mkApp (.const ``_root_.BitVec []) (toExpr 32))
      (toExpr (some rawInst))
  ]
  trace[Sym.reduceFetchInst] "{Lean.checkEmoji} found a proof:\n\t{proof}"
  return ⟨rawInst, proof⟩

simproc reduceFetchInst (fetch_inst _ _) := fun e => do
  trace[Sym.reduceFetchInst] "⚙️ simplifying {e}"
  let_expr Arm.fetch_inst addr s := e
    | return .continue
  let addr ← reflectBitVecLiteral 64 addr

  try
    let ⟨x, proof?⟩ ← reduceFetchInst? addr s
    return .done {expr := toExpr (some x), proof?}
  catch err =>
    trace[Sym.reduceFetchInst] "{Lean.crossEmoji} {err.toMessageData}"
    return .continue

end Arm
