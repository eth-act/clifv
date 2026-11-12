import FV.E2E.NonVacuity
import FV.E2E.LowerDirect
import FV.Backend.Proof.FormsCoverComplete

/-!
# Non-vacuity of `backend_correct_final` for indirect calls with stack-passed arguments (S5, #29)

`source` makes a `call_indirect` whose call-site signature has ten `i64` parameters: x0..x7 and
two in the outgoing area. Before S5 such a function was outside the theorem
(`Backend.indSigsOk source = false`, "indirect call with stack-passed arguments"); it is now in
`InSubset` (`Backend.verifiable`, `InSubset.of_verifiable`), the pipeline compiles it, and
`backend_correct_final` applies with every contract premise discharged by the witness callees
(`backend_correct_final_witness`), in an environment whose externs return nothing and keep the
memory. The checks are closed computations (`native_decide`), as in the other witnesses.
-/

namespace E2E.IndStackWitness

open Backend Backend.Proof Backend.Proof.Driver

/-- The witness's source: an indirect call with ten arguments. -/
def sourceSrc : String := "function %ci_stack(i64, i64) system_v {
    sig0 = (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) system_v
block0(v0: i64, v1: i64):
    call_indirect sig0, v0(v1, v1, v1, v1, v1, v1, v1, v1, v1, v1)
    return
}"

/-- The witness function. -/
def source : Clif.Function :=
  match (Clif.parseFile sourceSrc).funcs[0]? with
  | some p => match p.func with
    | .ok f => f
    | .error _ => default
  | none => default

def vc : VCode := (lowerFunction source).toOption.getD default
def vcp : VCode := (Backend.prepare vc).toOption.getD default
def rf : RFunc := spillAlloc vcp
def af : AFunc := (lowerRFunc vcp rf).toOption.getD default
def fa : FnAsm := (emitFunc 0 af).toOption.getD default
def fb : FnBin := fa.layout.toOption.getD default

/-! The closed checks: the input conditions, the pipeline's success, a ten-parameter indirect
call-site signature that the pre-S5 scope rejected, and the witness callees' shape premises. -/

theorem c_dom : dominatedB source = true := by native_decide
theorem c_scope : lowerScopeB source = true := by native_decide
theorem c_verifiable : Backend.verifiable source = true := by native_decide
theorem c_preS5 : Backend.indSigsOk source = false := by native_decide
theorem c_big : (indSigs source).any (fun s => decide (8 < s.params.length)) = true := by
  native_decide
theorem c_rets : (indSigs source).all (fun s => (sigRets s).isEmpty && s.returns.isEmpty) = true := by
  native_decide
theorem c_externs : source.externs.isEmpty = true := by native_decide
theorem c_noTry : source.blocks.all (fun B => !B.term.isTry) = true := by native_decide
theorem c_lower : (lowerFunction source).isOk = true := by native_decide
theorem c_prepare : (Backend.prepare vc).isOk = true := by native_decide
theorem c_alloc : (checkAlloc vcp rf).isOk = true := by native_decide
theorem c_lowerR : (lowerRFunc vcp rf).isOk = true := by native_decide
theorem c_emit : (emitFunc 0 af).isOk = true := by native_decide
theorem c_layout : fa.layout.isOk = true := by native_decide

theorem ok_getD {α : Type} {e : Except String α} {d : α} (h : e.isOk = true) :
    e = .ok (e.toOption.getD d) := by
  cases e <;> simp_all [Except.isOk, Except.toBool, Except.toOption]

theorem ok_unit {e : Except String Unit} (h : e.isOk = true) : e = .ok () := by
  cases e <;> simp_all [Except.isOk, Except.toBool]

/-- The facts the final theorem needs, from the closed checks. -/
theorem facts :
    InSubset ({ funcs := [] } : Clif.Program) source ∧ Compiled source 0 vc vcp rf af fa fb ∧
      FormsCovered ⟨fa.k, af.slotBase⟩ vcp ∧ (∀ B ∈ source.blocks, B.term.isTry = false) ∧
      (∀ ext ∈ source.externs.map (·.2), sigRets ext.sig = [] ∧ ext.sig.returns = []) ∧
      (∀ sig ∈ indSigs source, sigRets sig = [] ∧ sig.returns = []) ∧
      Backend.indSigsOk source = false ∧ ∃ s ∈ indSigs source, 8 < s.params.length := by
  have hl' : lowerFunction source = .ok vc := ok_getD c_lower
  have hp' : Backend.prepare vc = .ok vcp := ok_getD c_prepare
  have hc : Compiled source 0 vc vcp rf af fa fb :=
    Compiled.of_lowerB c_dom c_scope hl' hp' (ok_unit c_alloc) (ok_getD c_lowerR)
      (ok_getD c_emit) (ok_getD c_layout)
  have hnt := c_noTry
  have hret := c_rets
  have hbig := c_big
  have hext := c_externs
  simp only [List.all_eq_true, Bool.not_eq_true', Bool.and_eq_true, List.isEmpty_iff,
    List.any_eq_true, decide_eq_true_eq] at hnt hret hbig hext
  refine ⟨InSubset.of_verifiable c_verifiable (fun _ => rfl), hc,
    formsCovered_completeB c_scope hl' hp' _, hnt, ?_, hret, c_preS5, hbig⟩
  intro ext hext'
  simp [hext] at hext'

/-- An environment whose externs return nothing and keep the memory. -/
def env : Clif.Env := { extern := fun _ => some fun _ m => .returned [] m }

theorem env_noop : ∀ n G, env.extern n = some G → ∀ vals cm rvals cm',
    G vals cm = .returned rvals cm' → cm' = cm := by
  intro n G hG vals cm rvals cm' h
  simp only [env, Option.some.injEq] at hG
  subst hG
  simp only [Clif.Outcome.returned.injEq] at h
  exact h.2.symm

/-- **`backend_correct_final` for a `call_indirect` with stack-passed arguments**: the Arm code
of `source` (ten call arguments, two of them in the outgoing area) refines its CLIF run, from
the run premises alone; every contract premise is discharged by the witness callees
(`backend_correct_final_witness`). -/
theorem backend_correct_final_ind_stack {syms : String → Option Nat} {K : Nat} (hK : 32 ≤ K)
    (g h tp : BitVec 64)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn source.sig args s) (hcs : ClifEntry source args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, af.slotBase, (RAFrame.compute vcp rf).intBase⟩ source cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env ({ funcs := [] } : Clif.Program) cs) (fuel : Nat) :
    ArmRefines fb base ra (ArmStepX (witnessX (witnessSym syms) tp)
      (witnessHooks g h (witnessSym syms) tp) fa) s
      (Clif.runLoop env ({ funcs := [] } : Clif.Program) fuel cs) := by
  obtain ⟨hsub, hc, hcov, hnt, hsig, hisig, -, -⟩ := facts
  exact backend_correct_final_witness hsub hc hK g h tp hcov hnt hsig hisig
    (fun _ _ G hG => env_noop _ G hG) (fun _ _ n G hG => env_noop n G hG) rfl hent hres hbe hargs
    hcs hrel htr fuel

end E2E.IndStackWitness
