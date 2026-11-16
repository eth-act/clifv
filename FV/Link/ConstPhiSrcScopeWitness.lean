import FV.Link.ConstPhiCompile
import FV.E2E.SrcScopeDefs

/-!
# Constant-phi removal and the source domain: the shape of #1042

`FnInput.cp` (`FV/Link/ConstPhiCompile.lean`) prints a constant-phi-removed function after the
`i128` legalisation, so the source program of `LinkSpec.cp S` (`LinkInput.srcProg`, the files'
functions as parsed) holds that function legalised and every other function as the bundle wrote
it. When the changed function has an `i128` in its signature, the declarations of it in its
callers (`i128`) and its signature there (`i64` pairs) disagree: `declSigB` fails on the
compiled input's source program although the bundle's program is in the source domain and the
compiled (legalised) program's declarations agree.

The input: `f(i128, i64) -> i64`, whose `block1(v2)` receives only `v1` (a constant phi), and its
caller `g`, which declares `f` with its signature. `lean-link --verified` therefore decides the
source domain it requires on the bundle's program (`src_in`) and asks `SrcScopeB` of the compiled
input (`cp_src_out`) only on the routes that name `_source` theorems, which are instantiated
there (#1042).
-/

namespace Link.ConstPhiSrcScopeWitness

open E2E.LinkCheck

def fT : String :=
  "function %f(i128, i64) -> i64 {\nblock0(v0: i128, v1: i64):\n    jump block1(v1)\n\nblock1(v2: i64):\n    return v2\n}\n"

def gT : String :=
  "function %g(i128, i64) -> i64 {\n    fn0 = %f(i128, i64) -> i64\nblock0(v0: i128, v1: i64):\n    v2 = call fn0(v0, v1)\n    return v2\n}\n"

def S : LinkSpec :=
  { funcs := [{ clif := fT, ra := "" }, { clif := gT, ra := "" }], names := ["f", "g"],
    sizes := [1, 1], outside := [], symNames := [], R := 4096 }

/-- Constant-phi removal changes `f` (its printed form parses back to it) and keeps `g`. -/
theorem cp_changed : S.cpChanged = ["f"] ∧ S.cpFallbacks = [] := by
  native_decide -- witness: native_decide

/-- **The bundle's program is in the source domain.** -/
theorem src_in : SrcScopeB S.input0 = true := by native_decide -- witness: native_decide

/-- **The compiled input's source program is not**: there `f` is the printed legalised function,
`(i64, i64, i64) -> i64`, while `g` still declares `f(i128, i64) -> i64`; `g` fails `declSigB`. -/
theorem cp_src_out : SrcScopeB S.cp.input0 = false ∧
    (S.cp.input0.srcProg.func? "f").map (Clif.Print.signature ·.sig) =
      some "(i64, i64, i64) -> i64" ∧
    (S.cp.input0.srcProg.func? "g").map (fun g => g.externs.map (Clif.Print.signature ·.2.sig)) =
      some ["(i128, i64) -> i64"] ∧
    S.cp.input0.srcProg.funcs.map (fun g => (g.name, declSigB S.cp.input0.srcProg g)) =
      [("f", true), ("g", false)] := by
  native_decide -- witness: native_decide

/-- The compiled program (every function legalised) has agreeing declarations: the compiler's own
input conditions (`progScopeB`'s `declSigB`) are not what fails. -/
theorem cp_prog_declSig : S.cp.input0.prog.funcs.all (declSigB S.cp.input0.prog) = true := by
  native_decide -- witness: native_decide

end Link.ConstPhiSrcScopeWitness
