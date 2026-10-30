import FV.Backend.Proof.StockLowerProjection
import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.StockCastDispatch
import FV.Backend.Proof.IselExclData
import FV.Backend.Proof.IselFamily

/-!
# The diverging rules of `lower` do not match scalar statements

`stock_runTerm_lower_of_backend` transports a baseline `lower` run to Stock when the eight rules of
`lower` that use a diverging term (`lowerDiverging`) cannot match the instruction's arguments. Here
each of them fails on a source statement whose opcode name is not a call, splat or return, whose
extend opcode only comes from an extend statement, and whose function has no load statement: the
calls, splat and return by their primary opcode, the extend-of-load look-through roots by the
missing load.
-/

namespace Backend.Stock.Proof.LowerProjection
open Backend Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A rule whose primary source opcode differs from the instruction's cannot match it. -/
theorem argsFail_of_opcode {ctx : Ctx} {r : Rule} {code : Nat}
    (parsed : sourceRuleOpcode program r = some code) {i : Nat} {info : IInfo} {kf c : Nat}
    {opfs rest : List V} (source : ctx.insts[i]? = some info)
    (data : info.data = .data 152 kf (.data 151 c opfs :: rest)) (ne : c ≠ code) :
    ArgsFail program (Backend.sem ctx) r [.inst i] := by
  intro st env matched
  obtain ⟨info',kf',opfs',rest',source',data'⟩ := stock_opcode_args_match data_program parsed matched
  have same := Option.some.inj (source.symm.trans source')
  subst same
  have equal := V.data.inj (data.symm.trans data')
  have opEq := V.data.inj (List.cons.inj equal.2.2).1
  exact ne opEq.2.1

/-- A mapped source statement whose opcode name differs from a rule's opcode name cannot match
the rule's argument patterns. -/
theorem argsFail_of_name {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx) {r : Rule}
    {code : Nat} {name : String} (parsed : sourceRuleOpcode program r = some code)
    (named : (variantNames 151)[code]? = some name) (hk : code ≠ 59 ∧ code ≠ 60)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) (other : (instNames inst).2 ≠ name) :
    ArgsFail program (Backend.sem ctx) r [.inst i] := by
  have hdata := mapped.data i info inst source clif
  obtain ⟨kf,ko,fs,shape,-⟩ := instData_shape (mapped.instE i info inst source clif) hdata
  refine argsFail_of_opcode parsed source shape ?_
  intro same
  subst same
  rw [shape] at hdata
  have names := (instData_inv_names hdata (Or.inr hk)).2
  rw [named] at names
  exact other (Option.some.inj names).symm

/-- The opcode name of a subset-E instruction that is not a call is not a call's, a splat's or a
return's. -/
theorem instNames_not_call {inst : Clif.Inst} (hE : Compile.instE inst = true)
    (call : ∀ fn args, inst ≠ .call fn args) (ind : ∀ sig callee args, inst ≠ .callIndirect sig callee args) :
    (instNames inst).2 ≠ "Call" ∧ (instNames inst).2 ≠ "CallIndirect" ∧ (instNames inst).2 ≠ "Splat" ∧
      (instNames inst).2 ≠ "Return" := by
  cases inst
  all_goals first
    | (exfalso; exact call _ _ rfl)
    | (exfalso; exact ind _ _ _ rfl)
    | (simp [Compile.instE] at hE; done)
    | (simp [instNames]; done)
    | skip
  case unary op ty x =>
    simp only [instNames]
    cases op <;> simp [unaryOpcode]
  case binary op ty x y =>
    simp only [instNames]
    cases op <;> simp [binaryOpcode]
  case div op _ _ _ => cases op <;> simp [instNames, divOpcode]
  case load op _ _ _ _ => cases op <;> simp [instNames, loadOpcode]
  case store op _ _ _ _ _ => cases op <;> simp [instNames, storeOpcode]
  case extend op _ _ => cases op <;> simp [instNames]

/-- The primary opcode and its name of a diverging rule of `lower`, as a checked table. -/
def divergingName (r : Rule) : Bool :=
  match sourceRuleOpcode program r with
  | some c =>
    c != 59 && c != 60 &&
      match (variantNames 151)[c]? with
      | some n =>
        if r.id == 810 || r.id == 815 then n == "Uextend"
        else if r.id == 824 then n == "Sextend"
        else ["Call","CallIndirect","Splat","Return"].contains n
      | none => false
  | none => false

set_option maxRecDepth 100000 in
theorem lower_diverging_names :
    (program.rulesOf 686).all (fun r => !lowerDiverging.contains r.id || divergingName r) = true := by
  rw [data_program.r686]
  decide +kernel

private theorem extend_rule {r : Rule} (hr : r ∈ program.rulesOf 686) (hid : r.id = 810 ∨ r.id = 815 ∨ r.id = 824) :
    r = rule_lower_1272 ∨ r = rule_lower_1300 ∨ r = rule_lower_1359 := by
  have nodup := lower_ids_nodup
  rw [show TId.lower = 686 from rfl] at nodup
  rcases hid with h | h | h
  · exact .inl (eq_of_mem_of_id nodup hr (by rw [data_program.r686]; decide +kernel) h)
  · exact .inr (.inl (eq_of_mem_of_id nodup hr (by rw [data_program.r686]; decide +kernel) h))
  · exact .inr (.inr (eq_of_mem_of_id nodup hr (by rw [data_program.r686]; decide +kernel) h))

/-- Every diverging rule of `lower` fails on a source statement that is not a call, splat or
return, whose extend opcode comes only from an extend statement, in a context without load
statements. -/
theorem lower_diverging_args_fail {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    (noLoad : ∀ (j : Nat) (info : IInfo) (cl : Clif.Inst), ctx.insts[j]? = some info → info.clif = some cl →
      (instNames cl).1 ≠ "LoadNoOffset" ∧ (instNames cl).1 ≠ "Load")
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst)
    (names : ∀ n ∈ ["Call","CallIndirect","Splat","Return"], (instNames inst).2 ≠ n)
    (extend : (instNames inst).2 = "Uextend" ∨ (instNames inst).2 = "Sextend" →
      ∃ sg ty x, inst = .extend (ScalarCast.extendOp sg) ty x) :
    ∀ r ∈ program.rulesOf 686, r.id ∈ lowerDiverging → ArgsFail program (Backend.sem ctx) r [.inst i] := by
  intro r hr hdiv
  have h := List.all_eq_true.mp lower_diverging_names r hr
  simp only [List.contains_iff_mem.mpr hdiv, Bool.not_true, Bool.false_or] at h
  unfold divergingName at h
  cases hparsed : sourceRuleOpcode program r with
  | none => rw [hparsed] at h; cases h
  | some c =>
    rw [hparsed] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨h59, h60⟩, h⟩ := h
    cases hn : (variantNames 151)[c]? with
    | none => rw [hn] at h; cases h
    | some n =>
      rw [hn] at h
      by_cases hext : r.id = 810 ∨ r.id = 815 ∨ r.id = 824
      · have hrule := extend_rule hr hext
        by_cases same : (instNames inst).2 = n
        · have isExt : (instNames inst).2 = "Uextend" ∨ (instNames inst).2 = "Sextend" := by
            rcases hext with e | e | e <;> simp [e] at h <;> simp [same, h]
          obtain ⟨sg, ty, x, rfl⟩ := extend isExt
          exact CastComplete.stock_extend_load_args_fail mapped noLoad sg source clif hrule
        · exact argsFail_of_name mapped hparsed hn ⟨h59, h60⟩ source clif same
      · have hcall : n ∈ ["Call","CallIndirect","Splat","Return"] := by
          simp only [not_or] at hext
          obtain ⟨e1, e2, e3⟩ := hext
          have : r.id ≠ 810 ∧ r.id ≠ 815 := ⟨e1, e2⟩
          simp [e1, e2, e3] at h
          simpa using h
        exact argsFail_of_name mapped hparsed hn ⟨h59, h60⟩ source clif (names n hcall)
end Backend.Stock.Proof.LowerProjection
