import FV.Backend.Proof.IselExclSound
import FV.Backend.Proof.LowerLoopCtxT

/-!
# Excluded root rules over float-capable contexts (S11e5 Stage C)

`IselExcl` proves that the root rules of `lower` outside the closure never match an instruction
of an integer context (`CtxInv`): the abstract checker `fails` describes instructions by E
opcodes (`eOps`) and E result and value types (`eCTys`). In a float-capable context (`CtxInvT`,
instructions in the typed scope `InstScopeT`) values and results also have the types `f32` and
`f64`, and the instructions also have the opcodes `f32const`, `f64const` and `bitcast`. Widening
the types alone is too coarse: the float `bnot`/`band`/`bor`/`bxor` rules (`rule_lower_1381`,
`1415`, `1452`, `1519`) test a float result type of an E opcode. The checker `failsT` keeps the
correlation: an instruction with a float result has a float-movement opcode (`floatOps`:
`f32const`, `f64const`, `load`, `select`, `bitcast`; `inst_split`). It also looks into the
fields of a `bitcast` (`opShapeT`), for `bitcast_i128_simdfp` (`rule_lower_2784`, an `i128`
operand).

* `exclOkT_program`: every root rule of `lower` is a closure root or passes `failsT` (one kernel
  decision over the exported rule list);
* `lower_nonroot_nomatchT`: a root rule outside the closure matches no instruction of a
  float-capable context whose function's externs have integer signatures (`Compile.functionET`);
  `lower_nonroot_nomatchT_calls`: the same when only the callees of the context's `call`
  statements have integer signatures (`CallsE`; S11e6: a `try_call`'s callee may take and
  return floats).

The checker is stated once over the opcode lists (`failsTG p iOps fOps`) and proven sound
(`failsTG_sound`) in a context whose instructions `InstSplit S` describes (an instruction of the
scope `S` has an integer result with an opcode of `iOps` or a float result with one of `fOps`);
`failsT` is its instance at `opsT`/`floatOps` (`inst_split`, scope `Compile.instET`). S11f:

* `exclOkTA_program`, `lower_nonroot_nomatchTA`: the same with the float arithmetic among the
  instructions (`InstScopeTA`, scope `Compile.instETA`; float-result opcodes `floatOpsA`,
  `inst_splitA`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- Abstract values over float-capable contexts (`AV`, with the data's opcode set). -/
inductive AVT where
  /-- `.inst j` for an instruction `j` of the context with CLIF instruction `c` and data
  `instData f c`. -/
  | inst
  /-- The `InstructionData` of an instruction of the scope with an opcode of `ops`. -/
  | data (ops : List Nat)
  /-- A CLIF value `.value x`. -/
  | value
  /-- `.values xs` with `n` values. -/
  | values (n : Nat)
  /-- `.ty t` with `t ∈ ts`. -/
  | tys (ts : List CTy)
  /-- Exactly this value. -/
  | exact (v : V)
  /-- Anything. -/
  | any

/-- The values an abstract value describes, in the context `ctx` of `f`, for the instruction
scope `S` (the `.data` of an instruction `c` with `S c`). -/
def AVT.HoldsS (S : Clif.Inst → Bool) (f : Clif.Function) (ctx : Ctx) : AVT → V → Prop
  | .inst, v => ∃ j info c, v = .inst j ∧ ctx.insts[j]? = some info ∧ info.clif = some c ∧
      instData f c = .ok info.data
  | .data ops, v => ∃ c, S c = true ∧ instData f c = .ok v ∧
      ∃ kf ko fs, v = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ ops
  | .value, v => ∃ x, v = .value x
  | .values n, v => ∃ xs, v = .values xs ∧ xs.length = n
  | .tys ts, v => ∃ t ∈ ts, v = .ty t
  | .exact w, v => v = w
  | .any, _ => True

/-- `AVT.HoldsS` position by position (lists of the same length). -/
def AVT.HoldsAllS (S : Clif.Inst → Bool) (f : Clif.Function) (ctx : Ctx) :
    List AVT → List V → Prop
  | [], [] => True
  | a :: as, v :: vs => a.HoldsS S f ctx v ∧ AVT.HoldsAllS S f ctx as vs
  | _, _ => False

/-- The values an abstract value describes over the typed scope (`Compile.instET`). -/
abbrev AVT.Holds (f : Clif.Function) (ctx : Ctx) : AVT → V → Prop :=
  AVT.HoldsS Compile.instET f ctx

/-- `AVT.Holds` position by position (lists of the same length). -/
abbrev AVT.HoldsAll (f : Clif.Function) (ctx : Ctx) : List AVT → List V → Prop :=
  AVT.HoldsAllS Compile.instET f ctx

/-- The opcodes of the typed scope's instructions: E's, `f32const`, `f64const`, `bitcast`. -/
def opsT : List Nat := eOps ++ [VIdx.Opcode.F32const, VIdx.Opcode.F64const, VIdx.Opcode.Bitcast]

/-- The opcodes of the typed scope's instructions with a float result. -/
def floatOps : List Nat :=
  [VIdx.Opcode.F32const, VIdx.Opcode.F64const, VIdx.Opcode.Load, VIdx.Opcode.Select,
   VIdx.Opcode.Bitcast]

/-- The opcodes of the S11f float arithmetic `instData` builds (`fOpc`; float results). -/
def arithOps : List Nat :=
  [VIdx.Opcode.Fadd, VIdx.Opcode.Fsub, VIdx.Opcode.Fmul, VIdx.Opcode.Fdiv, VIdx.Opcode.Fmin,
   VIdx.Opcode.Fmax, VIdx.Opcode.Sqrt, VIdx.Opcode.Fneg, VIdx.Opcode.Fabs, VIdx.Opcode.Fpromote,
   VIdx.Opcode.Fdemote, VIdx.Opcode.Ceil, VIdx.Opcode.Floor, VIdx.Opcode.Trunc,
   VIdx.Opcode.Nearest]

/-- The float-result opcodes with the float arithmetic (`InstScopeTA`). -/
def floatOpsA : List Nat := floatOps ++ arithOps

/-- The float types. -/
def fTys : List CTy := [.float 32, .float 64]

/-- The fields the checker needs (`opShape`, and a `bitcast`'s value). -/
def opShapeT (ko : Nat) : Option (List AVT) :=
  if ko == VIdx.Opcode.Uextend || ko == VIdx.Opcode.Sextend then some [.value]
  else if ko == VIdx.Opcode.Store then some [.values 2, .any, .any]
  else if ko == VIdx.Opcode.Bitcast then some [.value, .any]
  else none

section
variable (p : Program)

mutual
/-- `q` cannot match any value that `a` describes (`fails` over float-capable contexts), where an
instruction with an integer (or no) result has an opcode of `iOps` and one with a float result
an opcode of `fOps`. -/
def failsTG (iOps fOps : List Nat) (a : AVT) : Pattern → Bool
  | .bind _ _ q => failsTG iOps fOps a q
  | .and _ qs => failsAnyTG iOps fOps a qs
  | .constPrim ty n =>
    match primTy ty n with
    | none => true
    | some c =>
      match a with
      | .tys ts => ts.all fun t => !(V.ty t == c)
      | .exact v => !(v == c)
      | _ => false
  | .term ty t args =>
    match termOf p t with
    | .error _ => true
    | .ok term =>
      match term.kind with
      | .enumVariant k =>
        match a with
        | .data ops =>
          match args with
          | .term _ oT [] :: rest =>
            match termOf p oT with
            | .error _ => true
            | .ok oterm =>
              match oterm.kind with
              | .enumVariant ko =>
                !(ops.contains ko) ||
                  match opShapeT ko with
                  | some sh => failsArgsTG iOps fOps sh rest
                  | none => false
              | _ => false
          | _ => false
        | .exact v =>
          match v with
          | .data ty' k' fs =>
            !(ty' == ty) || !(k == k') || failsArgsTG iOps fOps (fs.map .exact) args
          | _ => false
        | _ => false
      | .decl flags _ (some (.external _ _)) =>
        if flags.isMulti then true else
        match a with
        | .inst =>
          if term.id == TId.inst_data_value then
            failsArgsTG iOps fOps [.tys (.invalid :: eCTys), .data iOps] args &&
              failsArgsTG iOps fOps [.tys fTys, .data fOps] args
          else flagOff term.id
        | .value =>
          if term.id == TId.def_inst then failsArgsTG iOps fOps [.inst] args
          else if term.id == TId.value_type then failsArgsTG iOps fOps [.tys mCTys] args
          else false
        | .values n =>
          if term.id == TId.value_array_2 && n == 2 then failsArgsTG iOps fOps [.value, .value] args
          else false
        | .tys ts =>
          ts.all fun t0 =>
            match tyExtract term.id t0 with
            | some (.ok fs) => failsArgsTG iOps fOps (fs.map .exact) args
            | some _ => true
            | none => false
        | .exact (.ty t0) =>
          match tyExtract term.id t0 with
          | some (.ok fs) => failsArgsTG iOps fOps (fs.map .exact) args
          | some _ => true
          | none => false
        | _ => false
      | _ => false
  | _ => false

/-- Some pattern of `qs` cannot match (an `and`). -/
def failsAnyTG (iOps fOps : List Nat) (a : AVT) : List Pattern → Bool
  | [] => false
  | q :: qs => failsTG iOps fOps a q || failsAnyTG iOps fOps a qs

/-- Some pattern of `qs` cannot match the value at its position. -/
def failsArgsTG (iOps fOps : List Nat) : List AVT → List Pattern → Bool
  | a :: as, q :: qs => failsTG iOps fOps a q || failsArgsTG iOps fOps as qs
  | _, _ => false
end

/-- `failsTG` over the typed scope (`InstScopeT`): integer-result opcodes `opsT`, float-result
opcodes `floatOps`. -/
abbrev failsT (a : AVT) (q : Pattern) : Bool := failsTG p opsT floatOps a q
/-- `failsAnyTG` over the typed scope. -/
abbrev failsAnyT (a : AVT) (qs : List Pattern) : Bool := failsAnyTG p opsT floatOps a qs
/-- `failsArgsTG` over the typed scope. -/
abbrev failsArgsT (as : List AVT) (qs : List Pattern) : Bool := failsArgsTG p opsT floatOps as qs

/-- A root rule of `lower` is in the closure or cannot match an instruction of a float-capable
context. -/
def exclOkT (r : Rule) : Bool :=
  closureRootIds.contains r.id ||
    match r.args with
    | [q] => failsT p .inst q
    | _ => false

/-- A root rule of `lower` is in the closure or cannot match an instruction of a float-capable
context whose instructions may also be the S11f float arithmetic (`InstScopeTA`). -/
def exclOkTA (r : Rule) : Bool :=
  closureRootIds.contains r.id ||
    match r.args with
    | [q] => failsTG p opsT floatOpsA .inst q
    | _ => false

end

set_option maxRecDepth 100000 in
/-- Every root rule of `lower` is a closure root or cannot match an instruction of a
float-capable context (checked). -/
theorem exclOkT_program : (program.rulesOf TId.lower).all (exclOkT program) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every root rule of `lower` is a closure root or cannot match an instruction of a
float-capable context with the float arithmetic (checked). -/
theorem exclOkTA_program : (program.rulesOf TId.lower).all (exclOkTA program) = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-! ## The data of a typed-scope instruction -/

/-- The data of an instruction whose names are among `L` has an opcode of `ops` when every pair
of `L` names a format and an opcode of `ops`. -/
theorem data_of_names {c : Clif.Inst} {d : V} {rest : List V}
    (hd : d = instDataV (instNames c).1 (opcodeV (instNames c).2 :: rest)) {L : List (String × String)}
    (hm : instNames c ∈ L) {ops : List Nat}
    (hL : L.all (fun pr => match variantIdx 152 pr.1, variantIdx 151 pr.2 with
      | some _, some ko => ops.contains ko
      | _, _ => false) = true) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ ops := by
  have hm' := List.all_eq_true.mp hL _ hm
  generalize instNames c = pr at hm' hd
  obtain ⟨n1, n2⟩ := pr
  unfold instDataV opcodeV mkVariant at hd
  cases h1 : variantIdx 152 n1 with
  | none => simp only [h1] at hm'; cases hm'
  | some kf =>
    cases h2 : variantIdx 151 n2 with
    | none => simp only [h1, h2] at hm'; cases hm'
    | some ko =>
      simp only [h1, h2] at hm' hd
      exact ⟨kf, ko, rest, hd, List.contains_iff_mem.mp hm'⟩

/-- The format and opcode names of the typed scope's float movement (`load`, `store`, `select`,
`bitcast`). -/
def mNamePairs : List (String × String) :=
  [("Load", "Load"), ("Store", "Store"), ("Ternary", "Select"), ("LoadNoOffset", "Bitcast")]

set_option maxRecDepth 20000 in
theorem mNamePairs_idx : mNamePairs.all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => opsT.contains ko
    | _, _ => false) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem mNamePairs_float : [("Load", "Load"), ("Ternary", "Select"), ("LoadNoOffset", "Bitcast")].all
    (fun pr => match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => floatOps.contains ko
    | _, _ => false) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem eNamePairs_idxT : eNamePairs.all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => opsT.contains ko
    | _, _ => false) = true := by
  decide +kernel

/-- The data of a float constant. -/
theorem instData_iconst_float {f : Clif.Function} {ty : Clif.Ty} {imm : BitVec ty.width} {d : V}
    (hf : ty.isFloat = true) (h : instData f (.iconst ty imm) = .ok d) :
    ∃ rest, d = .data 152 33 (.data 151 59 [] :: rest) ∨ d = .data 152 34 (.data 151 60 [] :: rest) := by
  have he : eTy ty = false := by cases ty <;> simp_all [eTy, Clif.Ty.isFloat, Clif.Ty.isInt]
  simp only [instData] at h
  split at h
  · rename_i h'; rw [he] at h'; cases h'
  · split at h
    · rename_i hf'
      subst hf'
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨_, .inl (by rw [← h, instDataV_UnaryIeee32, opcodeV_F32const])⟩
    · split at h
      · rename_i hf'
        subst hf'
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨_, .inr (by rw [← h, instDataV_UnaryIeee64, opcodeV_F64const])⟩
      · simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h

/-- The names of a typed-scope instruction's data are among `eNamePairs ++ mNamePairs`. -/
theorem instNames_memT {f : Clif.Function} {c : Clif.Inst} {d : V} (hT : Compile.instET c = true)
    (h : instData f c = .ok d) : instNames c ∈ eNamePairs ++ mNamePairs := by
  by_cases hE : Compile.instE c = true
  · exact List.mem_append_left _ (instNames_mem hE h)
  cases c
  case iconst => simp [instNames, eNamePairs]
  case load op _ _ _ _ => cases op <;> simp [instNames, loadOpcode, eNamePairs]
  case store op _ _ _ _ _ => cases op <;> simp [instNames, storeOpcode, eNamePairs]
  case select => simp [instNames, eNamePairs]
  case bitcast => simp [instNames, mNamePairs]
  all_goals exact absurd hT (by simpa [Compile.instET] using hE)

/-- **The data of a typed-scope instruction**: format `kf`, opcode `ko ∈ opsT`, fields `fs`. -/
theorem instData_shapeT {f : Clif.Function} {c : Clif.Inst} {d : V}
    (hT : Compile.instET c = true) (h : instData f c = .ok d) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ opsT := by
  rcases instData_names h with ⟨rest, hd⟩ | ⟨ty, imm, rfl, hfl, rest, hd | hd⟩
  · exact data_of_names hd (instNames_memT hT h)
      (by rw [List.all_append, eNamePairs_idxT, mNamePairs_idx]; rfl)
  · exact ⟨_, _, _, hd, by simp [opsT]⟩
  · exact ⟨_, _, _, hd, by simp [opsT]⟩

theorem float_of_ofClif {t : Clif.Ty} (h : CTy.ofClif t ∈ fTys) : t.isFloat = true := by
  cases t <;> simp_all [fTys, CTy.ofClif, Clif.Ty.isFloat]

/-- **The callees of a context's `call` statements have integer signatures** (`Compile.sigE`;
S11e6). It is what the typed exclusion uses of `f.externs.all sigE` (`callsE_of_externs`): a
`call`'s results are integers. The callee of a `try_call` (a terminator) is not constrained. -/
def CallsE (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (fn : Clif.FnRef) (args : List Nat) (e : Clif.ExtFunc),
    ctx.insts[ii]? = some info → info.clif = some (.call fn args) → f.extern? fn = some e →
    Compile.sigE e.sig = true

/-- Integer externs give `CallsE`. -/
theorem callsE_of_externs {f : Clif.Function} (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    (ctx : Ctx) : CallsE f ctx :=
  fun _ _ _ _ _ _ _ he => List.all_eq_true.mp hx _ (Compile.lookup_mem he)

/-- The callee condition of `CallsE` at one instruction. -/
theorem CallsE.at {f : Clif.Function} {ctx : Ctx} (h : CallsE f ctx) {j : Nat} {info : IInfo}
    {c : Clif.Inst} (hi : ctx.insts[j]? = some info) (hc : info.clif = some c) :
    ∀ fn args, c = .call fn args → ∀ e, f.extern? fn = some e → Compile.sigE e.sig = true := by
  intro fn args he e hx
  subst he
  exact h j info fn args e hi hc hx

/-- The result types of an instruction other than `call` do not depend on the externs. -/
theorem resultTypes_noncall {i : Clif.Inst} (h : ∀ fn args, i ≠ .call fn args)
    (g g' : Clif.FnRef → Option Clif.Signature) (d : Nat → Option Clif.Signature) :
    i.resultTypes g d = i.resultTypes g' d := by
  cases i
  case call fn args => exact absurd rfl (h fn args)
  case float op _ _ => cases op <;> rfl
  all_goals rfl

/-- `Compile.resTy_not_float_of_instE` when only the instruction's callee (if a `call`) has an
integer signature. -/
theorem resTy_not_float_calls {f : Clif.Function} {i : Clif.Inst}
    (hcx : ∀ fn args, i = .call fn args → ∀ e, f.extern? fn = some e → Compile.sigE e.sig = true)
    (hi : Compile.instE i = true) (hc : Compile.isCallIndirect i = false) :
    ∀ t ∈ (i.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).getD [],
      t.isFloat = false := by
  by_cases hcl : ∃ fn args, i = .call fn args
  · obtain ⟨fn, args, rfl⟩ := hcl
    intro t ht
    cases he : f.extern? fn with
    | none => simp [Clif.Inst.resultTypes, he] at ht
    | some e =>
      simp only [Clif.Inst.resultTypes, he, Option.map_some, Option.getD_some, List.mem_map] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      have hs := hcx fn args rfl e he
      simp only [Compile.sigE, Bool.and_eq_true, List.all_eq_true] at hs
      have := hs.2 p hp
      revert this; cases p.ty <;> decide
  · intro t ht
    rw [resultTypes_noncall (fun fn args he => hcl ⟨fn, args, he⟩) _
      (fun r => (({ f with externs := [] } : Clif.Function).extern? r).map (·.sig))] at ht
    exact Compile.resTy_not_float_of_instE (f := { f with externs := [] }) rfl hi hc t ht

/-- **An instruction with a float result has a float-movement opcode** (its callee, if a
`call`, with an integer signature; a `call_indirect`'s results are integers by `instData`). -/
theorem floatRes_op_calls {f : Clif.Function} {c : Clif.Inst}
    (hcx : ∀ fn args, c = .call fn args → ∀ e, f.extern? fn = some e → Compile.sigE e.sig = true)
    (hT : Compile.instET c = true) {d : V} (h : instData f c = .ok d)
    {tys : List Clif.Ty}
    (hty : c.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys)
    {t : Clif.Ty} (ht : t ∈ tys) (hf : t.isFloat = true) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ floatOps := by
  by_cases hE : Compile.instE c = true
  · exfalso
    cases hci : Compile.isCallIndirect c
    · have := resTy_not_float_calls hcx hE hci t (by rw [hty]; exact ht)
      rw [hf] at this; cases this
    · cases c with
      | callIndirect sig cl args =>
        cases hl : f.sigDecls.lookup sig with
        | none => simp [Clif.Inst.resultTypes, hl] at hty
        | some sg =>
          simp only [Clif.Inst.resultTypes, hl, Option.map_some, Option.some.injEq] at hty
          subst hty
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
          have := List.all_eq_true.mp (sigIntB_iff.mp (instData_callIndirect_int h hl)).2 q hq
          revert this hf; cases q.ty <;> decide
      | _ => simp [Compile.isCallIndirect] at hci
  have hfl : ∀ (L : List (String × String)), instNames c ∈ L →
      L.all (fun pr => match variantIdx 152 pr.1, variantIdx 151 pr.2 with
        | some _, some ko => floatOps.contains ko
        | _, _ => false) = true →
      (∀ ty imm, c ≠ .iconst ty imm) →
      ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ floatOps := by
    intro L hm hL hnc
    rcases instData_names h with ⟨rest, hd⟩ | ⟨ty, imm, he, -⟩
    · exact data_of_names hd hm hL
    · exact absurd he (hnc ty imm)
  cases c
  case iconst ty imm =>
    have hty' : tys = [ty] := by simpa [Clif.Inst.resultTypes] using hty.symm
    subst hty'
    obtain rfl := List.mem_singleton.mp ht
    obtain ⟨rest, hd | hd⟩ := instData_iconst_float hf h
    · exact ⟨_, _, _, hd, by simp [floatOps]⟩
    · exact ⟨_, _, _, hd, by simp [floatOps]⟩
  case load op ty fl p off =>
    have hty' : tys = [ty] := by simpa [Clif.Inst.resultTypes] using hty.symm
    subst hty'
    obtain rfl := List.mem_singleton.mp ht
    cases op
    case load => exact hfl _ (by simp [instNames, loadOpcode]) mNamePairs_float (by simp)
    all_goals
      exfalso
      have hne : eTy t = false := by
        revert hf; cases t <;> simp [eTy, Clif.Ty.isFloat, Clif.Ty.isInt]
      simp only [instData, hne, hf] at h
      simp (config := { decide := true }) [throw, throwThe, MonadExceptOf.throw] at h
  case select ty cnd x y =>
    exact hfl _ (by simp [instNames]) mNamePairs_float (by simp)
  case bitcast ty fl x =>
    exact hfl _ (by simp [instNames]) mNamePairs_float (by simp)
  case store => simp [Clif.Inst.resultTypes] at hty; subst hty; cases ht
  all_goals exact absurd hT (by simpa [Compile.instET] using hE)

/-- **An instruction with a float result has a float-movement opcode** (externs with integer
signatures; a `call_indirect`'s results are integers by `instData`). -/
theorem floatRes_op {f : Clif.Function} (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    {c : Clif.Inst} (hT : Compile.instET c = true) {d : V} (h : instData f c = .ok d)
    {tys : List Clif.Ty}
    (hty : c.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) = some tys)
    {t : Clif.Ty} (ht : t ∈ tys) (hf : t.isFloat = true) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ floatOps :=
  floatRes_op_calls (fun _ _ _ e he => List.all_eq_true.mp hx _ (Compile.lookup_mem he)) hT h hty ht hf

/-! ## The fields -/

set_option maxRecDepth 20000 in
theorem variantNames_Bitcast_ex : (variantNames 151)[VIdx.Opcode.Bitcast]? = some "Bitcast" := rfl

theorem instNames_bitcast_ex {c : Clif.Inst} (h : (instNames c).2 = "Bitcast") :
    ∃ ty fl x, c = .bitcast ty fl x := by
  cases c <;> simp only [instNames] at h <;>
    first
    | exact ⟨_, _, _, rfl⟩
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at h)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at h)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at h)
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at h)
    | (rename_i op _ _; cases op <;> simp at h)
    | simp at h

theorem AV.holdsAll_toT {S : Clif.Inst → Bool} {f : Clif.Function} {ctx : Ctx} {fs : List V} :
    ∀ {sh : List AV}, (∀ a ∈ sh, a = .value ∨ a = .any ∨ ∃ n, a = .values n) →
      AV.HoldsAll f ctx sh fs → ∀ {sh' : List AVT},
      sh' = sh.map (fun | .value => .value | .values n => .values n | _ => .any) →
      AVT.HoldsAllS S f ctx sh' fs := by
  intro sh
  induction sh generalizing fs with
  | nil => intro _ h sh' hs; subst hs; cases fs <;> simp_all [AV.HoldsAll, AVT.HoldsAllS]
  | cons a sh ih =>
    intro hsh h sh' hs
    subst hs
    cases fs with
    | nil => cases h
    | cons v fs =>
      obtain ⟨ha, hr⟩ := h
      refine ⟨?_, ih (fun b hb => hsh b (List.mem_cons_of_mem _ hb)) hr rfl⟩
      rcases hsh a List.mem_cons_self with rfl | rfl | ⟨n, rfl⟩
      · exact ha
      · trivial
      · exact ha

/-- **The fields `opShapeT` promises.** -/
theorem instData_fieldsT {S : Clif.Inst → Bool} {f : Clif.Function} {ctx : Ctx} {c : Clif.Inst}
    {kf ko : Nat} {fs : List V} (h : instData f c = .ok (.data 152 kf (.data 151 ko [] :: fs)))
    {sh : List AVT} (hsh : opShapeT ko = some sh) : AVT.HoldsAllS S f ctx sh fs := by
  unfold opShapeT at hsh
  split at hsh
  · rename_i hp
    cases hsh
    have hs : opShape ko = some [.value] := by unfold opShape; simp only [hp, ↓reduceIte]
    exact AV.holdsAll_toT (by simp) (instData_fields (ctx := ctx) h hs) rfl
  · split at hsh
    · rename_i hn hp
      cases hsh
      have hs : opShape ko = some [.values 2, .any, .any] := by
        unfold opShape; simp only [hn, hp, ↓reduceIte, Bool.false_eq_true]
      exact AV.holdsAll_toT (by simp) (instData_fields (ctx := ctx) h hs) rfl
    · split at hsh
      · rename_i _ _ hk
        cases hsh
        have hko := beq_iff_eq.mp hk
        subst hko
        have ho := (instData_inv_names h (.inr (by decide))).2
        rw [variantNames_Bitcast_ex] at ho
        obtain ⟨ty, fl, x, rfl⟩ := instNames_bitcast_ex (Option.some.inj ho).symm
        simp only [instData] at h
        split at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
          injection h3 with _ h4
          subst h4
          exact ⟨⟨x, rfl⟩, trivial, trivial⟩
        · cases h
      · cases hsh

/-! ## Soundness of the checker -/

/-- **The checker's view of a context's instructions** (scope `S`): an instruction with an
integer (or no) result has an opcode of `iOps`, one with a float result an opcode of `fOps`. -/
def InstSplit (S : Clif.Inst → Bool) (f : Clif.Function) (ctx : Ctx) (iOps fOps : List Nat) :
    Prop :=
  ∀ {j : Nat} {info : IInfo} {c : Clif.Inst}, ctx.insts[j]? = some info → info.clif = some c →
    instData f c = .ok info.data →
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧
        (AVT.data iOps).HoldsS S f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧ (AVT.data fOps).HoldsS S f ctx info.data)

section
variable {p : Program} {f : Clif.Function} {ctx : Ctx}

theorem holdsAllT_exact {S : Clif.Inst → Bool} (fs : List V) :
    AVT.HoldsAllS S f ctx (fs.map .exact) fs := by
  induction fs with
  | nil => trivial
  | cons v fs ih => exact ⟨rfl, ih⟩

/-- `inst_split` for one typed-scope instruction (the callees of the context's `call`s with
integer signatures). -/
theorem inst_split1_calls (hctx : CtxInvT f ctx) (hx : CallsE f ctx)
    {j : Nat} {info : IInfo} {c : Clif.Inst} (hT : Compile.instET c = true)
    (hi : ctx.insts[j]? = some info) (hc : info.clif = some c) (hd : instData f c = .ok info.data) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧ (AVT.data opsT).Holds f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧ (AVT.data floatOps).Holds f ctx info.data) := by
  obtain ⟨tys, hty, hres, -⟩ := hctx.resTys j info c hi hc
  cases hh : info.resTys with
  | nil =>
    obtain ⟨kf, ko, fs, he, hko⟩ := instData_shapeT hT hd
    exact .inl ⟨List.mem_cons_self, c, hT, hd, kf, ko, fs, he, hko⟩
  | cons t0 ts =>
    simp only [List.head?_cons, Option.getD_some]
    have ht0 : t0 ∈ mCTys := hctx.resTysM j info hi t0 (by rw [hh]; exact List.mem_cons_self)
    by_cases hf : t0 ∈ fTys
    · right
      refine ⟨hf, c, hT, hd, ?_⟩
      rw [hres] at hh
      obtain ⟨t, ht, rfl⟩ : ∃ t ∈ tys, CTy.ofClif t = t0 := by
        cases tys with
        | nil => cases hh
        | cons t tys => simp only [List.map_cons, List.cons.injEq] at hh; exact ⟨t, List.mem_cons_self, hh.1⟩
      exact floatRes_op_calls (hx.at hi hc) hT hd hty ht (float_of_ofClif hf)
    · left
      refine ⟨List.mem_cons_of_mem _ ?_, c, hT, hd, instData_shapeT hT hd⟩
      simp only [mCTys, List.mem_append] at ht0
      rcases ht0 with h | h
      · exact h
      · exact absurd h hf

/-- `inst_split` for one typed-scope instruction. -/
theorem inst_split1 (hctx : CtxInvT f ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    {j : Nat} {info : IInfo} {c : Clif.Inst} (hT : Compile.instET c = true)
    (hi : ctx.insts[j]? = some info) (hc : info.clif = some c) (hd : instData f c = .ok info.data) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧ (AVT.data opsT).Holds f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧ (AVT.data floatOps).Holds f ctx info.data) :=
  inst_split1_calls hctx (callsE_of_externs hx ctx) hT hi hc hd

/-- **An instruction of the context** (the callees of its `call`s with integer signatures): an
integer (or no) result with an opcode of the typed scope, or a float result with a
float-movement opcode. -/
theorem inst_split_calls (hctx : CtxInvT f ctx) (hsc : InstScopeT ctx)
    (hx : CallsE f ctx) {j : Nat} {info : IInfo} {c : Clif.Inst}
    (hi : ctx.insts[j]? = some info)
    (hc : info.clif = some c) (hd : instData f c = .ok info.data) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧ (AVT.data opsT).Holds f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧ (AVT.data floatOps).Holds f ctx info.data) :=
  inst_split1_calls hctx hx (hsc j info c hi hc) hi hc hd

/-- **An instruction of the context**: an integer (or no) result with an opcode of the typed
scope, or a float result with a float-movement opcode. -/
theorem inst_split (hctx : CtxInvT f ctx) (hsc : InstScopeT ctx)
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true) {j : Nat} {info : IInfo} {c : Clif.Inst}
    (hi : ctx.insts[j]? = some info)
    (hc : info.clif = some c) (hd : instData f c = .ok info.data) :
    (info.resTys.head?.getD .invalid ∈ (.invalid :: eCTys) ∧ (AVT.data opsT).Holds f ctx info.data) ∨
      (info.resTys.head?.getD .invalid ∈ fTys ∧ (AVT.data floatOps).Holds f ctx info.data) :=
  inst_split_calls hctx hsc (callsE_of_externs hx ctx) hi hc hd

section
variable {S : Clif.Inst → Bool} {iOps fOps : List Nat} (hctx : CtxInvT f ctx)
  (hsp : InstSplit S f ctx iOps fOps)
include hctx hsp

-- `failsAnyTG_sound`/`failsArgsTG_sound` use the section's hypotheses only through
-- `failsTG_sound`
set_option linter.unusedSectionVars false

mutual
/-- **Soundness of the checker**: `failsTG p iOps fOps a q` means `q` matches no value `a`
describes (scope `S`), in a context whose instructions `InstSplit` describes. -/
theorem failsTG_sound : ∀ (q : Pattern) (a : AVT) (v : V) (st : LState) (env env' : Interp.Env V),
    failsTG p iOps fOps a q = true → a.HoldsS S f ctx v →
    matchPat p (sem ctx) st q v env = .ok (some env') → False
  | .bind ty x q, a, v, st, env, env', hf, ha, hm => by
    rw [failsTG.eq_1] at hf
    exact failsTG_sound q a v st _ env' hf ha (matchPat_bind_inv hm).2
  | .and ty qs, a, v, st, env, env', hf, ha, hm => by
    rw [failsTG.eq_2] at hf
    rw [matchPat.eq_7] at hm
    exact failsAnyTG_sound qs a v st env env' hf ha hm
  | .constPrim ty n, a, v, st, env, env', hf, ha, hm => by
    rw [matchPat.eq_5, prim_sem_ex] at hm
    rw [failsTG.eq_3] at hf
    cases hp : primTy ty n with
    | none => rw [hp] at hm; cases hm
    | some c =>
      rw [hp] at hm hf
      simp only [pure, Except.pure, eq_sem_ex] at hm
      have hne : (v == c) = false := by
        cases a with
        | tys ts =>
          obtain ⟨t, ht, rfl⟩ := ha
          simpa using List.all_eq_true.mp hf t ht
        | exact w => cases ha; simpa using hf
        | _ => simp at hf
      simp [hne] at hm
  | .term ty t args, a, v, st, env, env', hf, ha, hm => by
    rw [failsTG.eq_def] at hf
    try dsimp only at hf
    cases ht : termOf p t with
    | error e => exact matchPat_termOf_error ht hm
    | ok term =>
      rw [ht] at hf
      simp only at hf
      cases hk : term.kind with
      | struct => rw [hk] at hf; simp at hf
      | enumVariant k =>
        rw [hk] at hf
        obtain ⟨fs, hu, hma⟩ := matchPat_enum_inv ht hk hm
        cases a with
        | data ops =>
          obtain ⟨c, -, hc, kf, ko, fs0, rfl, hko⟩ := ha
          simp only [sem, beq_iff_eq] at hu
          split at hu
          · rename_i hty
            subst hty
            obtain ⟨rfl, rfl⟩ := Option.some.inj hu
            simp only at hf
            split at hf
            · rename_i ty2 oT rest
              obtain ⟨e1, hm1, hm2⟩ := matchArgs_cons_inv hma
              cases hot : termOf p oT with
              | error e => exact matchPat_termOf_error hot hm1
              | ok oterm =>
                rw [hot] at hf
                simp only at hf
                cases hok : oterm.kind with
                | enumVariant ko' =>
                  rw [hok] at hf
                  obtain ⟨fs1, hu1, -⟩ := matchPat_enum_inv hot hok hm1
                  simp only [sem, beq_iff_eq] at hu1
                  split at hu1
                  · obtain ⟨rfl, -⟩ := Option.some.inj hu1
                    try dsimp only at hf
                    rw [List.contains_iff_mem.mpr hko, Bool.not_true, Bool.false_or] at hf
                    cases hsh : opShapeT ko with
                    | none => rw [hsh] at hf; cases hf
                    | some sh =>
                      rw [hsh] at hf
                      exact failsArgsTG_sound rest sh fs0 st e1 env' hf (instData_fieldsT hc hsh) hm2
                  · cases hu1
                | _ => rw [hok] at hf; simp at hf
            · cases hf
          · cases hu
        | exact w =>
          cases ha
          try dsimp only at hf
          cases v with
          | data ty' k' fs' =>
            simp only [sem, beq_iff_eq] at hu
            split at hu
            · rename_i hty
              obtain ⟨rfl, rfl⟩ := Option.some.inj hu
              simp only [hty, beq_self_eq_true, Bool.not_true, Bool.false_or] at hf
              exact failsArgsTG_sound args _ _ st env env' hf (holdsAllT_exact _) hma
            · cases hu
          | _ => simp at hf
        | _ => simp at hf
      | decl flags c ex =>
        rw [hk] at hf
        cases ex with
        | none => simp at hf
        | some ex =>
          cases ex with
          | internal form => simp at hf
          | external fn inf =>
            simp only at hf
            cases hmu : flags.isMulti
            · rw [hmu] at hf
              simp only [Bool.false_eq_true, ↓reduceIte] at hf
              obtain ⟨fs, hx', hma⟩ := matchPat_extract_inv ht hk hmu hm
              rw [sem_extract] at hx'
              cases a with
              | inst =>
                obtain ⟨j, info, c, rfl, hi, hc, hd⟩ := ha
                try dsimp only at hf
                split at hf
                · rename_i hid
                  obtain ⟨info', hi', rfl⟩ := ext_idv_inv (beq_iff_eq.mp hid) hx'
                  rw [hi] at hi'
                  cases hi'
                  simp only [Bool.and_eq_true] at hf
                  rcases hsp hi hc hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact failsArgsTG_sound args _ [.ty (info.resTys.head?.getD .invalid), info.data] st
                      env env' hf.1 ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
                  · exact failsArgsTG_sound args _ [.ty (info.resTys.head?.getD .invalid), info.data] st
                      env env' hf.2 ⟨⟨_, h1, rfl⟩, h2, trivial⟩ hma
                · rw [ext_flagOff hf] at hx'; cases hx'
              | value =>
                obtain ⟨x, rfl⟩ := ha
                try dsimp only at hf
                split at hf
                · rename_i hid
                  obtain ⟨i, hdi, rfl⟩ := ext_def_inst_inv (beq_iff_eq.mp hid) hx'
                  obtain ⟨info, hi, -⟩ := hctx.defInst x i hdi
                  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hctx.defClif x i info hdi hi)
                  exact failsArgsTG_sound args _ [.inst i] st env env' hf
                    ⟨⟨i, info, c, rfl, hi, hc, hctx.data i info c hi hc⟩, trivial⟩ hma
                · split at hf
                  · rename_i _ hid
                    obtain ⟨t, hvt, rfl⟩ := ext_value_type_inv (beq_iff_eq.mp hid) hx'
                    exact failsArgsTG_sound args _ [.ty t] st env env' hf
                      ⟨⟨t, hctx.valTyM x t hvt, rfl⟩, trivial⟩ hma
                  · cases hf
              | values n =>
                obtain ⟨xs, rfl, hn⟩ := ha
                try dsimp only at hf
                split at hf
                · rename_i hid
                  simp only [Bool.and_eq_true, beq_iff_eq] at hid
                  obtain ⟨hid, rfl⟩ := hid
                  match xs, hn with
                  | [x, y], _ =>
                    rw [ext_value_array_2_ex hid] at hx'
                    cases hx'
                    exact failsArgsTG_sound args _ [.value x, .value y] st env env' hf
                      ⟨⟨x, rfl⟩, ⟨y, rfl⟩, trivial⟩ hma
                · cases hf
              | tys ts =>
                obtain ⟨t0, ht0, rfl⟩ := ha
                try dsimp only at hf
                have h0 := List.all_eq_true.mp hf t0 ht0
                cases hte : tyExtract term.id t0 with
                | none => rw [hte] at h0; cases h0
                | some r =>
                  rw [tyExtract_sound hte] at hx'
                  subst hx'
                  rw [hte] at h0
                  exact failsArgsTG_sound args _ _ st env env' h0 (holdsAllT_exact _) hma
              | exact w =>
                cases ha
                try dsimp only at hf
                cases v with
                | ty t0 =>
                  try dsimp only at hf
                  cases hte : tyExtract term.id t0 with
                  | none => rw [hte] at hf; cases hf
                  | some r =>
                    rw [tyExtract_sound hte] at hx'
                    subst hx'
                    rw [hte] at hf
                    exact failsArgsTG_sound args _ _ st env env' hf (holdsAllT_exact _) hma
                | _ => simp at hf
              | _ => simp at hf
            · exact matchPat_multi ht hk hmu hm
  | .var .., _, _, _, _, _, hf, _, _ => by simp [failsTG] at hf
  | .constBool .., _, _, _, _, _, hf, _, _ => by simp [failsTG] at hf
  | .constInt .., _, _, _, _, _, hf, _, _ => by simp [failsTG] at hf
  | .wildcard .., _, _, _, _, _, hf, _, _ => by simp [failsTG] at hf

theorem failsAnyTG_sound : ∀ (qs : List Pattern) (a : AVT) (v : V) (st : LState)
    (env env' : Interp.Env V), failsAnyTG p iOps fOps a qs = true → a.HoldsS S f ctx v →
    matchAll p (sem ctx) st qs v env = .ok (some env') → False
  | [], _, _, _, _, _, hf, _, _ => by simp [failsAnyTG] at hf
  | q :: qs, a, v, st, env, env', hf, ha, hm => by
    rw [failsAnyTG.eq_2, Bool.or_eq_true] at hf
    obtain ⟨e1, h1, h2⟩ := matchAll_cons_inv_ex hm
    rcases hf with hf | hf
    · exact failsTG_sound q a v st env e1 hf ha h1
    · exact failsAnyTG_sound qs a v st e1 env' hf ha h2

theorem failsArgsTG_sound : ∀ (qs : List Pattern) (as : List AVT) (vs : List V) (st : LState)
    (env env' : Interp.Env V), failsArgsTG p iOps fOps as qs = true →
    AVT.HoldsAllS S f ctx as vs →
    matchArgs p (sem ctx) st qs vs env = .ok (some env') → False
  | [], _, _, _, _, _, hf, _, _ => by cases ‹List AVT› <;> simp [failsArgsTG] at hf
  | q :: qs, [], _, _, _, _, hf, _, _ => by simp [failsArgsTG] at hf
  | q :: qs, a :: as, vs, st, env, env', hf, hav, hm => by
    rw [failsArgsTG.eq_1, Bool.or_eq_true] at hf
    match vs, hav with
    | v :: vs, ⟨ha, hrest⟩ =>
      obtain ⟨e1, h1, h2⟩ := matchArgs_cons_inv hm
      rcases hf with hf | hf
      · exact failsTG_sound q a _ st env e1 hf ha h1
      · exact failsArgsTG_sound qs as _ st e1 env' hf hrest h2
end

end

section
variable (hctx : CtxInvT f ctx) (hsc : InstScopeT ctx) (hx : CallsE f ctx)
include hctx hsc hx

/-- **Soundness of the checker** (the callees of the context's `call`s with integer
signatures): `failsT p a q` means `q` matches no value `a` describes. -/
theorem failsT_sound_calls : ∀ (q : Pattern) (a : AVT) (v : V) (st : LState)
    (env env' : Interp.Env V), failsT p a q = true → a.Holds f ctx v →
    matchPat p (sem ctx) st q v env = .ok (some env') → False :=
  failsTG_sound (S := Compile.instET) hctx (inst_split_calls hctx hsc hx)

theorem failsAnyT_sound_calls : ∀ (qs : List Pattern) (a : AVT) (v : V) (st : LState)
    (env env' : Interp.Env V), failsAnyT p a qs = true → a.Holds f ctx v →
    matchAll p (sem ctx) st qs v env = .ok (some env') → False :=
  failsAnyTG_sound (S := Compile.instET) hctx (inst_split_calls hctx hsc hx)

theorem failsArgsT_sound_calls : ∀ (qs : List Pattern) (as : List AVT) (vs : List V) (st : LState)
    (env env' : Interp.Env V), failsArgsT p as qs = true → AVT.HoldsAll f ctx as vs →
    matchArgs p (sem ctx) st qs vs env = .ok (some env') → False :=
  failsArgsTG_sound (S := Compile.instET) hctx (inst_split_calls hctx hsc hx)

end

variable (hctx : CtxInvT f ctx) (hsc : InstScopeT ctx)
  (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
include hctx hsc hx

/-- **Soundness of the checker**: `failsT p a q` means `q` matches no value `a` describes. -/
theorem failsT_sound : ∀ (q : Pattern) (a : AVT) (v : V) (st : LState) (env env' : Interp.Env V),
    failsT p a q = true → a.Holds f ctx v →
    matchPat p (sem ctx) st q v env = .ok (some env') → False :=
  failsT_sound_calls hctx hsc (callsE_of_externs hx ctx)

theorem failsAnyT_sound : ∀ (qs : List Pattern) (a : AVT) (v : V) (st : LState)
    (env env' : Interp.Env V), failsAnyT p a qs = true → a.Holds f ctx v →
    matchAll p (sem ctx) st qs v env = .ok (some env') → False :=
  failsAnyT_sound_calls hctx hsc (callsE_of_externs hx ctx)

theorem failsArgsT_sound : ∀ (qs : List Pattern) (as : List AVT) (vs : List V) (st : LState)
    (env env' : Interp.Env V), failsArgsT p as qs = true → AVT.HoldsAll f ctx as vs →
    matchArgs p (sem ctx) st qs vs env = .ok (some env') → False :=
  failsArgsT_sound_calls hctx hsc (callsE_of_externs hx ctx)

end

/-- **The root rules of `lower` outside the closure never match an instruction of a
float-capable context** (instructions in the typed scope, the callees of its `call`s with integer
signatures). -/
theorem lower_nonroot_nomatchT_calls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeT ctx) (hx : CallsE f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hroot : closureRootIds.contains r.id = false) :
    ∀ cfg m s0 env s1, (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env, s1) := by
  intro cfg m s0 env' s1 hmatch
  have hok := List.all_eq_true.mp exclOkT_program r hr
  simp only [exclOkT, hroot, Bool.false_or] at hok
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
    split at hok
    · rename_i q hargs
      rw [hargs] at ha
      obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
      exact failsT_sound_calls hctx hsc hx q .inst _ _ _ _ hok
        ⟨ii, info, inst, rfl, hi, hc, hctx.data ii info inst hi hc⟩ h1
    · cases hok

/-- **The root rules of `lower` outside the closure never match an instruction of a
float-capable context** (instructions in the typed scope, externs with integer signatures). -/
theorem lower_nonroot_nomatchT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeT ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hroot : closureRootIds.contains r.id = false) :
    ∀ cfg m s0 env s1, (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env, s1) :=
  lower_nonroot_nomatchT_calls hctx hsc (callsE_of_externs hx ctx) hi hc hr hroot

/-! ## With the float arithmetic (S11f) -/

/-- The instructions of a context are in the typed scope with the S11f float arithmetic
(`Compile.instETA`). -/
def InstScopeTA (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → Compile.instETA inst = true

theorem InstScopeT.toA {ctx : Ctx} (h : InstScopeT ctx) : InstScopeTA ctx :=
  fun ii info inst hi hc => Compile.instETA_of_instET (h ii info inst hi hc)

/-- The format and opcode names of the S11f float arithmetic (`fFmt`, `fOpc`). -/
def aNamePairs : List (String × String) :=
  [("Binary", "Fadd"), ("Binary", "Fsub"), ("Binary", "Fmul"), ("Binary", "Fdiv"),
   ("Binary", "Fmin"), ("Binary", "Fmax"), ("Unary", "Sqrt"), ("Unary", "Fneg"),
   ("Unary", "Fabs"), ("Unary", "Fpromote"), ("Unary", "Fdemote"), ("Unary", "Ceil"),
   ("Unary", "Floor"), ("Unary", "Trunc"), ("Unary", "Nearest")]

set_option maxRecDepth 20000 in
theorem aNamePairs_float : aNamePairs.all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => floatOpsA.contains ko
    | _, _ => false) = true := by
  decide +kernel

/-- An admitted float arithmetic instruction has a binary or unary float opcode. -/
theorem fArithET_op {op : Clif.FOp} {ty : Clif.Ty} {args : List Nat}
    (h : Compile.fArithET (.float op ty args) = true) :
    (fBinaryOpcode op).isSome = true ∨ (fUnaryOpcode op).isSome = true := by
  simp only [Compile.fArithET, Bool.and_eq_true] at h
  obtain ⟨h, -⟩ := h
  split at h
  · exact .inl h
  · exact .inr h
  · cases h

/-- **The data of an S11f float arithmetic instruction**: a float-result opcode (`floatOpsA`). -/
theorem instData_shapeA {f : Clif.Function} {c : Clif.Inst} {d : V}
    (hA : Compile.fArithET c = true) (h : instData f c = .ok d) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ floatOpsA := by
  cases c with
  | float op ty args =>
    rcases instData_names h with ⟨rest, hd⟩ | ⟨ty', imm, he, -⟩
    · refine data_of_names hd ?_ aNamePairs_float
      rcases fArithET_op hA with ho | ho <;>
        cases op <;> simp [fBinaryOpcode, fUnaryOpcode] at ho <;> simp [instNames, fFmt, fOpc, aNamePairs]
    · cases he
  | _ => simp [Compile.fArithET] at hA

/-- The result type of an S11f float arithmetic instruction is its float controlling type. -/
theorem fArith_resTy {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {j : Nat}
    {info : IInfo} {c : Clif.Inst} (hA : Compile.fArithET c = true) (hi : ctx.insts[j]? = some info)
    (hc : info.clif = some c) : info.resTys.head?.getD .invalid ∈ fTys := by
  cases c with
  | float op ty args =>
    have hty : ty.isFloat = true := by
      simp only [Compile.fArithET, Bool.and_eq_true] at hA
      revert hA; cases op <;> cases ty <;> simp [fTyOk, Clif.Ty.isFloat]
    obtain ⟨tys, htys, hres, -⟩ := hctx.resTys j info _ hi hc
    rcases fArithET_op hA with ho | ho <;> cases op <;> simp [fBinaryOpcode, fUnaryOpcode] at ho <;>
      simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys <;> subst htys <;>
      rw [hres] <;> revert hty <;> cases ty <;> simp [fTys, CTy.ofClif, Clif.Ty.isFloat]
  | _ => simp [Compile.fArithET] at hA

/-- **An instruction of a context with the float arithmetic**: as `inst_split`, the arithmetic
among the float-result opcodes (`floatOpsA`). -/
theorem inst_splitA_calls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTA ctx) (hx : CallsE f ctx) :
    InstSplit Compile.instETA f ctx opsT floatOpsA := by
  intro j info c hi hc hd
  have hTA := hsc j info c hi hc
  have hT := hTA
  simp only [Compile.instETA, Bool.or_eq_true] at hT
  rcases hT with hT | hA
  · rcases inst_split1_calls hctx hx hT hi hc hd with ⟨h1, c', hT', hc', kf, ko, fs, he, hko⟩ |
      ⟨h1, c', hT', hc', kf, ko, fs, he, hko⟩
    · exact .inl ⟨h1, c', Compile.instETA_of_instET hT', hc', kf, ko, fs, he, hko⟩
    · exact .inr ⟨h1, c', Compile.instETA_of_instET hT', hc', kf, ko, fs, he,
        List.mem_append_left _ hko⟩
  · obtain ⟨kf, ko, fs, he, hko⟩ := instData_shapeA hA hd
    exact .inr ⟨fArith_resTy hctx hA hi hc, c, hTA, hd, kf, ko, fs, he, hko⟩

theorem inst_splitA {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hsc : InstScopeTA ctx)
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true) :
    InstSplit Compile.instETA f ctx opsT floatOpsA :=
  inst_splitA_calls hctx hsc (callsE_of_externs hx ctx)

/-- **The root rules of `lower` outside the closure never match an instruction of a
float-capable context with the float arithmetic** (instructions in `InstScopeTA`, the callees
of its `call`s with integer signatures). -/
theorem lower_nonroot_nomatchTA_calls {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTA ctx) (hx : CallsE f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hroot : closureRootIds.contains r.id = false) :
    ∀ cfg m s0 env s1, (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env, s1) := by
  intro cfg m s0 env' s1 hmatch
  have hok := List.all_eq_true.mp exclOkTA_program r hr
  simp only [exclOkTA, hroot, Bool.false_or] at hok
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
    split at hok
    · rename_i q hargs
      rw [hargs] at ha
      obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
      exact failsTG_sound hctx (inst_splitA_calls hctx hsc hx) q .inst _ _ _ _ hok
        ⟨ii, info, inst, rfl, hi, hc, hctx.data ii info inst hi hc⟩ h1
    · cases hok

/-- **The root rules of `lower` outside the closure never match an instruction of a
float-capable context with the float arithmetic** (instructions in `InstScopeTA`, externs with
integer signatures). -/
theorem lower_nonroot_nomatchTA {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    (hsc : InstScopeTA ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} (hr : r ∈ program.rulesOf TId.lower) (hroot : closureRootIds.contains r.id = false) :
    ∀ cfg m s0 env s1, (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env, s1) :=
  lower_nonroot_nomatchTA_calls hctx hsc (callsE_of_externs hx ctx) hi hc hr hroot

end Backend.Proof
