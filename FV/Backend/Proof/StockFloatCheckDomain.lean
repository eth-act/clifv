import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.LowerLoopCtx

/-! # The `Stock.buildCtx` float check keeps the original accepted domain (S11e3, #140)

S11e3 adds one check to `Stock.buildCtx`: after `Backend.buildCtx`, a context with an `f32`/`f64`
value (a value of class other than `.int`) is rejected (`"f32/f64 value"`). This file shows that the
check rejects nothing else:

* `buildCtx_int_domain`: whenever every value type of `Backend.buildCtx f`'s context has class
  `.int`, `Stock.buildCtx f` is exactly the definition without the check (allocation requests, then
  `finishCtx`), so every input whose values are integers — every input of the integer-only type
  universe before S11b — is accepted or rejected as before, with the same result;
* `buildCtx_functionE_domain`: the same for every function in the compiler's source scope
  (`Compile.functionE`), whose values are integers;
* `buildCtx_int_domain_witness`: a concrete integer function on which both sides succeed. -/

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver

/-- **Domain preservation of the float check**: on a context whose values are all of class
`.int`, `Stock.buildCtx` equals the definition without the check. -/
theorem buildCtx_int_domain {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hold : Backend.buildCtx f = .ok (ctx, ranges, st0))
    (hint : ∀ x t, ctx.valueType? x = some t → t.valClass = .int) :
    Stock.buildCtx f = (do
      let requests ← allocationRequests f ranges
      pure (finishCtx ctx ranges (allocateRequests ctx.valTy.size ctx.insts.size requests))) := by
  have hc : (ctx.valTy.toList.any fun o => o.any (·.valClass != .int)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    simp only [List.any_eq_true, Array.mem_toList_iff] at h
    obtain ⟨o, ho, hb⟩ := h
    obtain ⟨x, hx, rfl⟩ := Array.mem_iff_getElem.mp ho
    cases hv : ctx.valTy[x] with
    | none => rw [hv] at hb; simp at hb
    | some t =>
      rw [hv] at hb
      have ht : ctx.valueType? x = some t := by
        simp [Ctx.valueType?, Array.getElem?_eq_getElem hx, hv]
      simp [hint x t ht] at hb
  simp only [Stock.buildCtx, hold, bind, Except.bind, hc, Bool.false_eq_true, ite_false, pure,
    Except.pure]

/-- Every function in the source scope `Compile.functionE` that `Backend.buildCtx` accepts passes the
float check: `Stock.buildCtx` is the definition without it. -/
theorem buildCtx_functionE_domain {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hE : Compile.functionE f = true)
    (hold : Backend.buildCtx f = .ok (ctx, ranges, st0)) :
    Stock.buildCtx f = (do
      let requests ← allocationRequests f ranges
      pure (finishCtx ctx ranges (allocateRequests ctx.valTy.size ctx.insts.size requests))) :=
  buildCtx_int_domain hold fun x t ht =>
    valClass_of_eCTys ((ctxSpec_of hold).ctxE hE x t ht)

private def domainFixture : Clif.Function := {
  name := "int_domain"
  sig := { params := [⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩] }
  blocks := [
    { id := 7, params := [(7, .i64)], term := .jump ⟨9, [7]⟩ },
    { id := 9, params := [(2, .i32)], term := .ret [2] }] }

private def domainOld : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx domainFixture).toOption.getD (sinkCtx, #[], { nextVreg := 0, classes := #[] })

/-- Non-vacuity of `buildCtx_int_domain`: an integer function whose `Backend.buildCtx` succeeds
(`i64` and `i32` values), and on which `Stock.buildCtx` with the check equals the definition
without it and succeeds. -/
theorem buildCtx_int_domain_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState)
      (result : Ctx × Array (Nat × Nat) × State),
      Backend.buildCtx f = .ok (ctx, ranges, st0) ∧
      (∀ x t, ctx.valueType? x = some t → t.valClass = .int) ∧
      Stock.buildCtx f = .ok result ∧
      Stock.buildCtx f = (do
        let requests ← allocationRequests f ranges
        pure (finishCtx ctx ranges (allocateRequests ctx.valTy.size ctx.insts.size requests))) := by
  have hold : Backend.buildCtx domainFixture = .ok domainOld := rfl
  have hint : ∀ x t, domainOld.1.valueType? x = some t → t.valClass = .int := by
    intro x t ht
    have hE : Compile.functionE domainFixture = true := by decide +kernel
    exact valClass_of_eCTys ((ctxSpec_of hold).ctxE hE x t ht)
  have hok : ∃ r, Stock.buildCtx domainFixture = .ok r :=
    ⟨(Stock.buildCtx domainFixture).toOption.getD (sinkCtx, #[], sinkState), rfl⟩
  obtain ⟨r, hr⟩ := hok
  exact ⟨domainFixture, domainOld.1, domainOld.2.1, domainOld.2.2, r, hold, hint, hr,
    buildCtx_int_domain hold hint⟩


end Backend.Stock.Proof
