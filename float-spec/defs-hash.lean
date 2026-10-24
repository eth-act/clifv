import FV.Float
import Lean
/-! Prints every constant declared in the FV/Float cone (`FV.Float`, `FV.Float.*`) in a
toolchain-independent structural form: kind, universe parameters, type, and for definitions and
opaques the value, as kernel terms with binder names dropped (theorem proofs are omitted; the
bridge only needs the statements and the definitions; `noConfusion` helpers: see below).
scripts/float-spec.sh runs this under the root toolchain (`lake env lean` in the
root, v4.34.1: what the compiler uses) and under float-spec's toolchain (v4.35.0: what
FVFloatSpec's theorems are about) and requires identical output (docs/contracts/float.md,
"Trust"). -/
open Lean

partial def ser : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar f => s!"(fvar {f.name})"
  | .mvar m => s!"(mvar {m.name})"
  | .sort u => s!"(sort {u})"
  | .const n us => s!"(c {n} {us})"
  | .app f a => s!"({ser f} {ser a})"
  | .lam _ t b bi => s!"(lam {repr bi} {ser t} {ser b})"
  | .forallE _ t b bi => s!"(pi {repr bi} {ser t} {ser b})"
  | .letE _ t v b nd => s!"(let {nd} {ser t} {ser v} {ser b})"
  | .lit (.natVal k) => s!"(nat {k})"
  | .lit (.strVal s) => s!"(str {repr s})"
  | .mdata _ e => ser e
  | .proj s i e => s!"(proj {s} {i} {ser e})"

def serConst : ConstantInfo → String
  | .defnInfo d => s!"def {d.levelParams} {ser d.type} := {ser d.value}"
  | .opaqueInfo d => s!"opaque {d.levelParams} {ser d.type} := {ser d.value}"
  | .thmInfo d => s!"theorem {d.levelParams} {ser d.type}"
  | .axiomInfo d => s!"axiom {d.levelParams} {ser d.type}"
  | .inductInfo d => s!"inductive {d.levelParams} {ser d.type} {d.numParams} {d.numIndices} {d.ctors}"
  | .ctorInfo d => s!"ctor {d.levelParams} {ser d.type} {d.cidx} {d.numFields}"
  | .recInfo d => s!"rec {d.levelParams} {ser d.type}"
  | .quotInfo d => s!"quot {ser d.type}"

#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let inCone (m : Name) := m == `FV.Float || (`FV.Float).isPrefixOf m
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    unless inCone mods[idx.toNat]! do continue
    -- `T.noConfusion`/`T.noConfusionType` of enum inductives are built from core's
    -- `noConfusionEnum`/`noConfusionTypeEnum`, whose signature changed in v4.35.0. They only
    -- serve proofs of constructor disjointness, so compare their types, not their values; the
    -- check below fails if any other compared constant mentions them.
    if n.getString! == "noConfusion" || n.getString! == "noConfusionType" then
      out := out.push s!"{n} auxiliary {ser ci.type}"
    else
      let s := serConst ci
      if (s.splitOn ".noConfusion").length > 1 then
        throwError "{n} mentions a noConfusion helper; compare it differently"
      out := out.push s!"{n} {s}"
  for l in out.qsort (· < ·) do IO.println l
