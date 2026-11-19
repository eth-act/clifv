import FV.Backend.Proof.LowerLoopCtxT
import FV.Backend.Proof.IselFmaFamily
import FV.Compile.FmaNegYFree

/-!
# #35: `Compile.fmaNegYFree` gives `FmaNegYFree` of `buildCtx`'s context

The context's instructions are `buildCtx`'s entries of `f`'s statements (`CtxSpec.inst_of`), and
a value's defining instruction lists it among its results (`CtxInvT.defInst`): an `fneg` that
defines an `fma`'s second operand in the context is an `fneg` statement of `f` with that operand
among its results, which `Compile.fmaNegYFree` excludes.
-/

namespace Backend.Proof

open Backend Backend.Proof.Driver

/-- **Soundness of `Compile.fmaNegYFree` for `buildCtx`'s context.** -/
theorem fmaNegYFree_of_buildCtx {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hT : Compile.fmaNegYFree f = true) (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hinv : CtxInvT f ctx) : FmaNegYFree ctx := by
  have sp := ctxSpec_of hb
  intro ii info ty x y z hi hc ty' w hd
  obtain ⟨B, hB, s, hs, -, hsi⟩ := sp.inst_of hi hc
  unfold Ctx.defClif? at hd
  cases hj : ctx.defInst? y with
  | none => simp [hj] at hd
  | some j =>
    obtain ⟨info', hi', hy⟩ := hinv.defInst y j hj
    simp only [hj, hi', Option.bind_eq_bind, Option.bind_some] at hd
    obtain ⟨B', hB', s', hs', rfl, hsi'⟩ := sp.inst_of hi' hd
    exact Compile.fmaNegYFree_sound hT hB hs hsi.symm hB' hs' hsi'.symm hy

end Backend.Proof
