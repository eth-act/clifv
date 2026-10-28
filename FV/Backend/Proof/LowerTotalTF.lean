import FV.Backend.Proof.LowerTotalT
import FV.Backend.Proof.LowerLoopCtxTF
import FV.Clif.FloatFacts

/-!
# Totality of the lowering driver on the float scope (S11f, #35)

`lowerFunction_okTF`: `lowerFunction_okT` with the float scope `Compile.functionETF`
(`LowerScopeTF`) for the typed movement scope: `lowerFunction_okG` with `blockC_ofTF` —
`instData` accepts the S11f float operations of `Compile.instETF` (`instData_okTF`) and their
result types are `valTyOk` (`tysOf_okTF`; an `fcmp`'s is `i8`, a saturating conversion's
`i32`/`i64`, the others' `f32`/`f64`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- The instructions of the float scope: the typed movement scope's, or a float operation of
`fArithET`, `fCvtET` or `fCmpET`. -/
theorem instETF_cases {i : Clif.Inst} (h : Compile.instETF i = true) :
    Compile.instET i = true ∨ ∃ op ty args, i = .float op ty args ∧
      (Compile.fArithET i = true ∨ Compile.fCvtET i = true ∨ Compile.fCmpET i = true) := by
  cases i with
  | float op ty args =>
    simp only [Compile.instETF, Compile.instETA, Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact .inl h
    · exact .inr ⟨op, ty, args, rfl, .inl h⟩
    · exact .inr ⟨op, ty, args, rfl, .inr (.inl h)⟩
    · exact .inr ⟨op, ty, args, rfl, .inr (.inr h)⟩
  | _ => exact .inl (by simpa [Compile.instETF, Compile.instETA, Compile.fArithET, Compile.fCvtET,
      Compile.fCmpET] using h)

set_option maxRecDepth 10000 in
/-- **`instData` succeeds on a statement of the float scope** satisfying `stmtInB`: the typed
movement scope's (`instData_okT`) and the float operations `instData` admits by construction. -/
theorem instData_okTF {f : Clif.Function} {s : Clif.Stmt} (hT : Compile.instETF s.inst = true)
    (hs : stmtInB f s = true) : ∃ d, instData f s.inst = .ok d := by
  rcases instETF_cases hT with h | ⟨op, ty, args, he, hk⟩
  · exact instData_okT h hs
  rw [he]
  rw [he] at hk
  rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;> cases op <;>
    simp_all [Compile.fArithET, Compile.fCvtET, Compile.fCmpET, instData, fBinaryOpcode,
      fUnaryOpcode, fCvtOpcode, pure, Except.pure]

/-- The result types of a statement of the float scope satisfying `stmtInB` are types `buildCtx`
admits, for a function with integer externs. -/
theorem tysOf_okTF {f : Clif.Function} (hXE : f.externs.all (Compile.sigE ·.2.sig) = true)
    {s : Clif.Stmt} (hi : Compile.instETF s.inst = true) (hs : stmtInB f s = true) :
    ∀ t ∈ tysOf f s, valTyOk t = true := by
  rcases instETF_cases hi with h | ⟨op, ty, args, he, hk⟩
  · exact tysOf_okTB hXE h hs
  intro t ht
  simp only [tysOf, he, Clif.resultTypes_float, Option.getD_some, List.mem_singleton] at ht
  subst ht
  rw [he] at hk
  rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;> cases op <;> cases ty <;>
    simp_all [Compile.fArithET, Compile.fCvtET, Compile.fCmpET, Clif.floatResTy, valTyOk, eTy,
      fTyOk, fCvtTyOk, fBinaryOpcode, fUnaryOpcode, fCvtOpcode, Clif.Ty.isFloat, Clif.Ty.isInt]

/-- `blockC_ofT` on the float scope. -/
theorem blockC_ofTF {f : Clif.Function} (hETF : Compile.functionETF f = true)
    (hst : ∀ B ∈ f.blocks, ∀ s ∈ B.body, stmtInB f s = true) : ∀ B ∈ f.blocks, BlockC f B := by
  intro B hB
  obtain ⟨-, hX, hbl, -⟩ := functionETF_parts hETF
  have h := hbl B hB
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hp, hb⟩, -⟩ := h
  refine ⟨fun q hq => valTyOk_of_tyM (hp q hq), fun s hs => ?_⟩
  have hi := hb s hs
  have hin := hst B hB s hs
  refine ⟨instData_okTF hi hin, ?_, fun t ht => valTyOk_of_tyM ?_⟩
  · have h1 := hin
    unfold stmtInB at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨h1, -⟩ := h1
    split at h1
    · rename_i tys hty
      exact ⟨tys, hty, by simpa using h1⟩
    · cases h1
  · have := tysOf_okTF hX hi hin t ht
    cases t <;> simp_all [valTyOk, eTy, Compile.tyM, Compile.tyE, Clif.Ty.isInt, Clif.Ty.isFloat]

/-- **Totality of the lowering driver on the float scope** (`lowerFunction_okT` with
`Compile.functionETF`, `LowerScopeTF`): `lowerFunction` succeeds as soon as the ISLE runs on
`buildCtx`'s context make progress (`IselProg`). -/
theorem lowerFunction_okTF {f : Clif.Function} (hs : LowerScopeTF f)
    (hsig : sigAbiOk f.sig = true) (hdom : dominatedB f = true)
    (har : Spill.arityOkB f = true) (hent : Spill.entryParamsB f = true)
    (hin : driverInB f = true)
    (hprog : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) → IselProg f ctx) :
    ∃ vc, lowerFunction f = .ok vc := by
  obtain ⟨hsig', -, hbl, -⟩ := functionETF_parts hs.subsetTF
  exact lowerFunction_okG (blockC_ofTF hs.subsetTF) hsig'
    (fun B hB => by have h := hbl B hB; simp only [Bool.and_eq_true] at h; exact h.2)
    hs.nonempty hs.tryRet hsig hdom har hent hin hprog

end Backend.Proof.Driver
