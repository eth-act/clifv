import FV.Backend.Proof.IselCmpRoot

/-!
# S11f: scalar float arithmetic roots over float-capable contexts

The `lower` roots of the scalar float arithmetic (`lower.isle:485-559`, `2176`), proven over
`CtxInvT` (`LowerRuleOkT`) against the shared IEEE core: CLIF's `Inst.float` (`Clif.evalFloat`,
`FV/Clif/FSem.lean`) and the Arm instruction the rule emits (`ispec`'s `fpu2Val`/`fpu1Val`/
`fcmpFlags`, the Arm model's `exec_fp_data_processing_{one,two}_source`/`exec_fp_compare`) are the
same `IEEE` functions with `FPCR = 0`, so each rule is a statement about one function:

* `fpu_rrr` (`FpuRRR`, `fadd/fsub/fmul/fdiv/fmin/fmax sd, sn, sm` / `… dd, dn, dm`): `fadd` 662
  (`rule_lower_485`), `fsub` 664 (493), `fmul` 666 (501), `fdiv` 668 (509), `fmin` 670 (517),
  `fmax` 672 (525);
* `fpu_rr` (`FpuRR`): `sqrt` 674 (533), `fneg` 676 (541), `fabs` 678 (549) at the result's scalar
  size, `fpromote` 679 (554, `fcvt dd, sn`), `fdemote` 680 (559, `fcvt sd, dn`);
* `fcmp` 951 (2176): `lower_cond_result_bool (emit_fcmp cc x y)`, i.e. `fcmp` then `cset` of
  `fp_cond_code cc` (`emit_fcmp_okT`, `IselCmpFcmp`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Instruction data -/

theorem variantNames_Fadd : (variantNames 151)[113]? = some "Fadd" := rfl
theorem variantNames_Fsub : (variantNames 151)[114]? = some "Fsub" := rfl
theorem variantNames_Fmul : (variantNames 151)[115]? = some "Fmul" := rfl
theorem variantNames_Fdiv : (variantNames 151)[116]? = some "Fdiv" := rfl
theorem variantNames_Fmin : (variantNames 151)[122]? = some "Fmin" := rfl
theorem variantNames_Fmax : (variantNames 151)[123]? = some "Fmax" := rfl
theorem variantNames_Sqrt : (variantNames 151)[117]? = some "Sqrt" := rfl
theorem variantNames_Fneg : (variantNames 151)[119]? = some "Fneg" := rfl
theorem variantNames_Fabs : (variantNames 151)[120]? = some "Fabs" := rfl
theorem variantNames_Fpromote : (variantNames 151)[143]? = some "Fpromote" := rfl
theorem variantNames_Fdemote : (variantNames 151)[144]? = some "Fdemote" := rfl

/-- An instruction whose opcode name is a float operation's is that float operation. -/
theorem instNames_float {c : Clif.Inst} {s : String} (hs : s ∈ fOpNames) (h : (instNames c).2 = s) :
    ∃ op ty args, c = .float op ty args ∧ fOpc op = s := by
  cases c
  case float op ty args => exact ⟨op, ty, args, rfl, h⟩
  all_goals exfalso
  all_goals subst h
  all_goals simp only [instNames, fOpNames] at hs
  all_goals first
    | (simp at hs; done)
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at hs; done)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at hs; done)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at hs; done)
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at hs; done)

/-- A matched `Binary` of a float opcode `n` is the two-operand float operation named `n`, at a
type `instData` admits. -/
theorem instData_fbin_inv {f : Clif.Function} {cl : Clif.Inst} {ko : Nat} {fs : List V}
    {op : Clif.FOp} {n : String} (hop : fBinaryOpcode op = some n)
    (hko : (variantNames 151)[ko]? = some n)
    (h : instData f cl = .ok (.data 152 2 (.data 151 ko [] :: fs))) :
    ∃ ty x y, cl = .float op ty [x, y] ∧ fTyOk op ty = true ∧ fs = [.values [x, y]] := by
  obtain ⟨-, ho⟩ := instData_inv_names h
  rw [hko] at ho
  have hn : n ∈ fOpNames := by
    cases op <;> simp [fBinaryOpcode] at hop <;> subst hop <;> decide
  obtain ⟨op', ty, args, rfl, hop'⟩ := instNames_float hn (Option.some.inj ho).symm
  obtain rfl : op' = op := by
    cases op <;> simp [fBinaryOpcode] at hop <;> subst hop <;> cases op' <;> simp [fOpc] at hop' <;>
      rfl
  cases op <;> simp [fBinaryOpcode] at hop <;> subst hop <;>
    rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;>
    simp only [instData, fBinaryOpcode, fUnaryOpcode, throw, throwThe, MonadExceptOf.throw,
      reduceCtorEq] at h
  all_goals
    split at h
    · rename_i hok
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq] at h3
      exact ⟨ty, x, y, rfl, hok, h3.2⟩
    · simp only [reduceCtorEq] at h

/-- A matched `Unary` of a float opcode `n` is the one-operand float operation named `n`, at a
type `instData` admits. -/
theorem instData_fun_inv {f : Clif.Function} {cl : Clif.Inst} {ko : Nat} {fs : List V}
    {op : Clif.FOp} {n : String} (hop : fUnaryOpcode op = some n)
    (hko : (variantNames 151)[ko]? = some n)
    (h : instData f cl = .ok (.data 152 29 (.data 151 ko [] :: fs))) :
    ∃ ty x, cl = .float op ty [x] ∧ fTyOk op ty = true ∧ fs = [.value x] := by
  obtain ⟨-, ho⟩ := instData_inv_names h
  rw [hko] at ho
  have hn : n ∈ fOpNames := by
    cases op <;> simp [fUnaryOpcode] at hop <;> subst hop <;> decide
  obtain ⟨op', ty, args, rfl, hop'⟩ := instNames_float hn (Option.some.inj ho).symm
  obtain rfl : op' = op := by
    cases op <;> simp [fUnaryOpcode] at hop <;> subst hop <;> cases op' <;> simp [fOpc] at hop' <;>
      rfl
  cases op <;> simp [fUnaryOpcode] at hop <;> subst hop <;>
    rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;>
    simp only [instData, fBinaryOpcode, fUnaryOpcode, throw, throwThe, MonadExceptOf.throw,
      reduceCtorEq] at h
  all_goals
    split at h
    · rename_i hok
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      simp only [List.cons.injEq] at h3
      exact ⟨ty, x, rfl, hok, h3.2⟩
    · simp only [reduceCtorEq] at h

end Backend.Proof
