import FV.Backend.Proof.IselCovExt
import FV.Backend.Proof.IselFlowData
import FV.Backend.Proof.LowerLoopCtx

/-!
# Form coverage of the ISLE lowering (V3): the context's instruction data is clean

`Clean ctx` (every `ctx.insts` entry's data holds no register and no uncovered `MInst`) for
`buildCtx`'s context (`clean_of_build`: placeholders and `instData` of statements) and its
extensions by a terminator's data (`clean_termCtx`, `clean_tryCtx`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver

/-- **`buildCtx`'s context is clean**: its entries are the terminators' placeholders and the
statements' `instData`. -/
theorem clean_of_build {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) : Clean ctx := by
  have sp := ctxSpec_of hb
  intro i info hi
  rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
    rfl | ⟨B, hB, s, hs, rfl⟩
  · exact ⟨rfl, rfl⟩
  · obtain ⟨d, hd⟩ := ((sp.blockC B hB).2 s hs).1
    have hdo : (infoOf f s).data = d := by
      show dataOf f s = d
      unfold dataOf
      rw [hd]
    rw [hdo]
    exact ⟨(instData_ok hd).1, instData_covV hd⟩

/-- Setting a terminator slot to clean data keeps the context clean. -/
theorem clean_set {ctx : Ctx} (hcl : Clean ctx) {ti : Nat} {data : V} (hr : data.regsIn = [])
    (hc : covV data = true) : Clean (termCtx ctx ti data) := by
  intro j info hj
  by_cases hji : j = ti
  · subst hji
    by_cases hlt : j < ctx.insts.size
    · have : (termCtx ctx j data).insts[j]? = some ⟨data, [], [], none⟩ := by
        show (ctx.insts.set! j _)[j]? = _
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt]
      rw [this] at hj
      cases hj
      exact ⟨hr, hc⟩
    · have : (termCtx ctx j data).insts = ctx.insts := by
        show ctx.insts.set! j _ = _
        rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
        simp [hlt]
      rw [this] at hj
      exact hcl j info hj
  · rw [termCtx_insts_ne hji] at hj
    exact hcl j info hj

/-- A terminator's data at its slot keeps the context clean. -/
theorem clean_termCtx {ctx : Ctx} (hcl : Clean ctx) {t : Clif.Terminator} {data : V}
    (hd : termData t = .ok data) (ti : Nat) : Clean (termCtx ctx ti data) :=
  clean_set hcl (termData_ok hd).1 (termData_covV hd)

/-- A `try_call`'s data at its slot keeps the context clean. -/
theorem clean_tryCtx {f : Clif.Function} {ctx : Ctx} (hcl : Clean ctx) {t : Clif.Terminator}
    {data : V} (hd : tryCallData f t = .ok data) (ti : Nat) (trs : List Reg × List Reg) :
    Clean (tryCtx ctx ti data trs) :=
  clean_set hcl (tryCallData_ok hd).1 (tryCallData_covV hd)

end Backend.Proof.Cov
