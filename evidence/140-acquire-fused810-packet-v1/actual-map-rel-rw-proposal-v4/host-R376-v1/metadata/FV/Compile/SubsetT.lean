import FV.Compile.Subset
import FV.Backend.Isel

/-!
# The typed movement scope (S11e5 Stage C, slice 1)

`Compile.functionET f`: subset E with the value types widened to `f32`/`f64` (`tyM`) for the
values whose defining instruction is data movement (the S11e4 roots): float constants
(`f32const`; `f64const` without the literal pool, `f64PoolFree`), `load`/`store` of a float,
`select` of floats, `bitcast`, block parameters, the function's parameters and returns. Integer
operations keep E's integer types (`tyE`), calls keep integer signatures, and the operands in
integer positions (`intOperands`, `termIntOperands`: the CLIF verifier's typing) are never
values `f` defines with a float type (`floatDefs`, `opsTypedT`).

This is a variant scope beside `functionE` (which stays integer-only); `functionET_of_functionE`:
every function of subset E is in it.
-/

namespace Compile

open Clif

/-- The admissible value types of the typed scope: E's integers, `f32` and `f64`. -/
def tyM (t : Ty) : Bool := tyE t || t.isFloat

/-- An `f64` constant `constant_f64` lowers without the literal pool (inst.isle:4264-4274: zero,
an `fmov` immediate (`fpModImm?`), a value below `2^32` (`constant_f32`), or zero low 32 bits
(`mov x; fmov d`)); the last rule's `emit_u64_le_const` is not modelled. -/
def f64PoolFree (n : Nat) : Bool :=
  n == 0 || (Backend.fpModImm? n .size64).isSome || decide (n < 2 ^ 32) || n % 2 ^ 32 == 0

/-- The instructions of the typed scope: `instE`, and the float data movement of S11e4. -/
def instET : Inst → Bool
  | .iconst ty imm => tyE ty || ty == .f32 || (ty == .f64 && f64PoolFree imm.toNat)
  | .load op ty f _ _ => flagsE f && (tyE ty || (ty.isFloat && op == .load))
  | .store op ty f _ _ _ => flagsE f && (tyE ty || (ty.isFloat && op == .store))
  | .select ty _ _ _ => tyM ty
  | .bitcast ty _ _ => tyM ty
  | i => instE i

/-- The S11f float arithmetic whose `lower` roots are proven (`Backend.LowerRulesCorrectFT`):
`fadd`/`fsub`/`fmul`/`fdiv`/`fmin`/`fmax` with two operands and `sqrt`/`fneg`/`fabs`/`fpromote`/
`fdemote` with one, at the types `instData` admits (`Backend.fTyOk`: `f32`/`f64`, `fpromote.f64`,
`fdemote.f32`). Not `fcmp` (its `fp_cond_code` conditions are not proven). -/
def fArithET : Inst → Bool
  | .float op ty args =>
    (match args with
     | [_, _] => (Backend.fBinaryOpcode op).isSome
     | [_] => (Backend.fUnaryOpcode op).isSome
     | _ => false) && Backend.fTyOk op ty
  | _ => false

/-- The typed scope's instructions with the S11f float arithmetic (`instET`, `fArithET`): the
instruction set of the arithmetic-admitting exclusion (`Backend.Proof.InstScopeTA`,
`lower_nonroot_nomatchTA`). -/
def instETA (i : Inst) : Bool := instET i || fArithET i

theorem instETA_of_instET {i : Inst} (h : instET i = true) : instETA i = true := by
  simp [instETA, h]

/-- A signature of the typed scope: parameters and returns of admissible types. -/
def sigET (s : Signature) : Bool :=
  s.params.all (tyM ·.ty) && s.returns.all (tyM ·.ty)

/-- The operands of an instruction the CLIF verifier types as integers (as
`Backend.Proof.intArgs`, `intArgs_eq_intOperands`). -/
def intOperands : Inst → List Nat
  | .unary _ _ x | .extend _ _ x | .ireduce _ x | .bmask _ x => [x]
  | .binary _ _ x y | .div _ _ x y | .icmp _ _ x y => [x, y]
  | .load _ _ _ p _ | .atomicLoad _ _ p => [p]
  | .store _ ty _ x p _ => if ty.isFloat then [p] else [x, p]
  | .select ty c x y => if ty.isFloat then [c] else [c, x, y]
  | .atomicStore _ _ x p => [x, p]
  | .atomicRmw _ _ _ p x => [p, x]
  | .atomicCas _ _ p e x => [p, e, x]
  | .call _ args => args
  | .callIndirect _ c args => c :: args
  | _ => []

/-- The operands of a terminator in integer positions: a branch condition, a `br_table`
index, the callee and arguments of a `try_call` (calls are integer-only). -/
def termIntOperands : Terminator → List Nat
  | .brif c _ _ => [c]
  | .brTable x _ _ => [x]
  | .tryCall _ args _ => args
  | .tryCallIndirect c args _ => c :: args
  | _ => []

/-- `call_indirect` (its results have its declared signature's types, integers by
`instData`'s `sigIntB`). -/
def isCallIndirect : Inst → Bool
  | .callIndirect .. => true
  | _ => false

/-- The values `f` defines with a float type: block parameters and statement results (the
result types `buildCtx` uses; a `call_indirect`'s are integers by `instData`, so it is not
listed). -/
def floatDefs (f : Function) : List ValueId :=
  f.blocks.flatMap fun b =>
    (b.params.filter (·.2.isFloat)).map (·.1) ++
    b.body.flatMap fun s =>
      if isCallIndirect s.inst then [] else
        ((s.results.zip ((s.inst.resultTypes (fun r => (f.extern? r).map (·.sig))
          (f.sigDecls.lookup ·)).getD [])).filter (·.2.isFloat)).map (·.1)

/-- The operands in integer positions are not float-defined values. -/
def opsTypedT (f : Function) : Bool :=
  let fd := floatDefs f
  f.blocks.all fun b =>
    b.body.all (fun s => (intOperands s.inst).all fun x => !fd.contains x) &&
      (termIntOperands b.term).all fun x => !fd.contains x

/-- Every definition of `f` with whether its type is a float: block parameters, statement
results at the result types `buildCtx` uses; a `call_indirect`'s results are integers
(`instData`'s `sigIntB`). -/
def defFloats (f : Function) : List (ValueId × Bool) :=
  f.blocks.flatMap fun b =>
    b.params.map (fun p => (p.1, p.2.isFloat)) ++
    b.body.flatMap fun s =>
      if isCallIndirect s.inst then s.results.map (·, false) else
        (s.results.zip ((s.inst.resultTypes (fun r => (f.extern? r).map (·.sig))
          (f.sigDecls.lookup ·)).getD [])).map fun p => (p.1, p.2.isFloat)

/-- Value `a` passed where type `ty` is expected has `ty`'s register class: every definition
of `a` is a float iff `ty` is. -/
def argClassOk (df : List (ValueId × Bool)) (a : ValueId) (ty : Ty) : Bool :=
  df.all fun p => p.1 != a || p.2 == ty.isFloat

/-- The successors of a branch (`jump`, `brif`, `br_table`). -/
def blockCalls : Terminator → List BlockCall
  | .jump bc => [bc]
  | .brif _ t e => [t, e]
  | .brTable _ d tbl => d :: tbl
  | _ => []

/-- **Edge and return classes**: branch arguments and a `try_call`'s value arguments have the
class of their target block's parameters, returned values the class of the signature's
returns (the CLIF verifier's typing of block calls and `return`). -/
def edgeClassOk (f : Function) : Bool :=
  let df := defFloats f
  f.blocks.all fun b =>
    (blockCalls b.term).all (fun bc => match f.block? bc.block with
      | some tb => (bc.args.zip tb.params).all fun (a, p) => argClassOk df a p.2
      | none => true) &&
    (match b.term with
      | .tryCall _ _ et | .tryCallIndirect _ _ et => et.dests.all fun td =>
        match f.block? td.block with
        | some tb => (td.args.zip tb.params).all fun
          | (.val v, p) => argClassOk df v p.2
          | _ => true
        | none => true
      | .ret vs => (vs.zip f.sig.returns).all fun (v, p) => argClassOk df v p.ty
      | _ => true)

/-- **The typed movement scope.** -/
def functionET (f : Function) : Bool :=
  sigET f.sig && f.globals.all (globalE ·.2) && f.externs.all (sigE ·.2.sig) &&
    f.blocks.all (fun b =>
      b.params.all (tyM ·.2) && b.body.all (instET ·.inst) && termE b.term) &&
    opsTypedT f && edgeClassOk f

/-! ## Integer specialization -/

theorem tyM_of_tyE {t : Ty} (h : tyE t = true) : tyM t = true := by simp [tyM, h]

theorem instET_of_instE {i : Inst} (h : instE i = true) : instET i = true := by
  cases i <;> simp_all [instE, instET, tyM]

theorem sigET_of_sigE {s : Signature} (h : sigE s = true) : sigET s = true := by
  simp only [sigE, sigET, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨fun p hp => tyM_of_tyE (h.1 p hp), fun p hp => tyM_of_tyE (h.2 p hp)⟩

theorem lookup_mem {f : Function} {fn : FnRef} {e : ExtFunc} (he : f.extern? fn = some e) :
    (fn, e) ∈ f.externs := by
  unfold Function.extern? at he
  generalize f.externs = l at he
  induction l with
  | nil => simp [List.lookup] at he
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : fn = k
    · subst hk; simp [List.lookup] at he; simp [he]
    · simp only [List.lookup, show (fn == k) = false from by simpa using hk] at he
      exact List.mem_cons_of_mem _ (ih he)

/-- The non-`call_indirect` result types of an `instE` instruction under integer externs are
not floats. -/
theorem resTy_not_float_of_instE {f : Function} (hx : f.externs.all (sigE ·.2.sig) = true)
    {i : Inst} (hi : instE i = true) (hc : isCallIndirect i = false) :
    ∀ t ∈ (i.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).getD [],
      t.isFloat = false := by
  intro t ht
  cases i with
  | call fn args =>
    cases he : f.extern? fn with
    | none => simp [Inst.resultTypes, he] at ht
    | some e =>
      simp only [Inst.resultTypes, he, Option.map_some, Option.getD_some, List.mem_map] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      have hm : (fn, e) ∈ f.externs := lookup_mem he
      have hs := List.all_eq_true.mp hx _ hm
      simp only [sigE, Bool.and_eq_true, List.all_eq_true] at hs
      have := hs.2 p hp
      revert this; cases p.ty <;> decide
  | callIndirect => simp [isCallIndirect] at hc
  | unary op ty x =>
    cases op <;> simp_all [Inst.resultTypes, instE, unaryTyE, unaryE, tyE] <;>
      (subst ht; revert hi; cases ty <;> decide)
  | _ =>
    simp_all [Inst.resultTypes, instE, tyE, binaryE, flagsE] <;>
      first
      | (subst ht; rfl)
      | (subst ht; revert hi; rename_i ty _; cases ty <;> decide)
      | (revert hi; rename_i ty; subst ht; cases ty <;> decide)
      | skip

/-- Subset E defines no float values. -/
theorem floatDefs_of_functionE {f : Function} (hE : functionE f = true) : floatDefs f = [] := by
  simp only [functionE, Bool.and_eq_true, List.all_eq_true] at hE
  obtain ⟨⟨⟨-, -⟩, hx⟩, hb⟩ := hE
  simp only [floatDefs, List.flatMap_eq_nil_iff, List.append_eq_nil_iff, List.map_eq_nil_iff,
    List.filter_eq_nil_iff]
  intro b hbm
  refine ⟨fun q hq => ?_, fun s hs => ?_⟩
  · have := (hb b hbm).1.1 q hq
    revert this; simp only [tyE]; cases q.2 <;> decide
  · split
    · rfl
    · rename_i hc
      simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff]
      intro p hp
      have hi := (hb b hbm).1.2 s hs
      have := resTy_not_float_of_instE (List.all_eq_true.mpr hx) hi (by simpa using hc) p.2
        (List.of_mem_zip hp).2
      revert this; cases p.2 <;> decide

theorem isFloat_of_tyE {t : Ty} (h : tyE t = true) : t.isFloat = false := by
  revert h; cases t <;> decide

/-- Subset E defines only integer values. -/
theorem defFloats_of_functionE {f : Function} (hE : functionE f = true) :
    ∀ p ∈ defFloats f, p.2 = false := by
  simp only [functionE, Bool.and_eq_true, List.all_eq_true] at hE
  obtain ⟨⟨⟨-, -⟩, hx⟩, hb⟩ := hE
  intro p hp
  simp only [defFloats, List.mem_flatMap, List.mem_append, List.mem_map] at hp
  obtain ⟨b, hbm, hp⟩ := hp
  rcases hp with ⟨q, hq, rfl⟩ | ⟨s, hs, hp⟩
  · exact isFloat_of_tyE ((hb b hbm).1.1 q hq)
  · split at hp
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hp; rfl
    · rename_i hc
      obtain ⟨⟨r, t⟩, hm, rfl⟩ := List.mem_map.mp hp
      exact resTy_not_float_of_instE (List.all_eq_true.mpr hx) ((hb b hbm).1.2 s hs)
        (by simpa using hc) t (List.of_mem_zip hm).2

theorem argClassOk_of_int {df : List (ValueId × Bool)} (hdf : ∀ p ∈ df, p.2 = false) (a : ValueId)
    {ty : Ty} (ht : ty.isFloat = false) : argClassOk df a ty = true :=
  List.all_eq_true.mpr fun p hp => by
    simp only [hdf p hp, ht, beq_self_eq_true, Bool.or_true]

/-- **Subset E is in the typed scope.** -/
theorem functionET_of_functionE {f : Function} (hE : functionE f = true) :
    functionET f = true := by
  have hfd := floatDefs_of_functionE hE
  have hdf := defFloats_of_functionE hE
  simp only [functionE, Bool.and_eq_true, List.all_eq_true] at hE
  obtain ⟨⟨⟨hs, hg⟩, hx⟩, hb⟩ := hE
  have hblk : ∀ {bid tb}, f.block? bid = some tb → ∀ p ∈ tb.params, p.2.isFloat = false :=
    fun htb p hp => isFloat_of_tyE ((hb _ (List.mem_of_find?_eq_some htb)).1.1 p hp)
  simp only [functionET, opsTypedT, edgeClassOk, hfd, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨sigET_of_sigE hs, hg⟩, hx⟩, fun b hbm => ?_⟩, fun b _ => ?_⟩, fun b _ => ⟨?_, ?_⟩⟩
  · exact ⟨⟨fun q hq => tyM_of_tyE ((hb b hbm).1.1 q hq),
      fun s hs => instET_of_instE ((hb b hbm).1.2 s hs)⟩, (hb b hbm).2⟩
  · simp
  · intro bc _
    split
    · rename_i tb htb
      exact List.all_eq_true.mpr fun ap hm =>
        argClassOk_of_int hdf _ (hblk htb _ (List.of_mem_zip hm).2)
    · rfl
  · split
    · refine List.all_eq_true.mpr fun td _ => ?_
      split
      · rename_i tb htb
        refine List.all_eq_true.mpr fun ap hm => ?_
        split
        · exact argClassOk_of_int hdf _ (hblk htb _ (List.of_mem_zip hm).2)
        · rfl
      · rfl
    · refine List.all_eq_true.mpr fun td _ => ?_
      split
      · rename_i tb htb
        refine List.all_eq_true.mpr fun ap hm => ?_
        split
        · exact argClassOk_of_int hdf _ (hblk htb _ (List.of_mem_zip hm).2)
        · rfl
      · rfl
    · simp only [sigE, Bool.and_eq_true, List.all_eq_true] at hs
      exact List.all_eq_true.mpr fun vp hm =>
        argClassOk_of_int hdf _ (isFloat_of_tyE (hs.2 _ (List.of_mem_zip hm).2))
    · rfl

end Compile
