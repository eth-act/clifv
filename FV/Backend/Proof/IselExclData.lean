import FV.Backend.Proof.IselExclBase

/-!
# Excluded root rules: facts about E instructions and the extractors the checker uses

* `closureRoot_eq`: `closureRoot` is membership in the literal `closureRootIds`.
* `instData_shape`: the data of an E instruction is `InstructionData.K (Opcode.O) fs` with `O` an
  E opcode (`eOps`); `instData_fields`: the fields `opShape` promises.
* Extractor facts (`externExtract`) on the abstract values of `AV`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## Closure roots -/

theorem closureRootIds_eq :
    (Closure.rules.toList.filter (·.isRoot)).map (·.rule) = closureRootIds := by
  decide +kernel

theorem closureRoot_eq (r : Rule) : closureRoot r = closureRootIds.contains r.id := by
  rw [closureRoot, ← closureRootIds_eq, ← Array.any_toList]
  generalize Closure.rules.toList = l
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.any_cons, List.filter_cons, ih]
    cases hc : c.isRoot
    · simp only [Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.true_and, ↓reduceIte, List.map_cons, List.contains_cons]
      congr 1
      exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)

/-! ## The data of an E instruction -/

/-- The `InstructionData` format and opcode names of the E instructions (`instNames`). -/
def eNamePairs : List (String × String) :=
  [("UnaryImm", "Iconst"),
   ("Unary", "Ineg"), ("Unary", "Bnot"), ("Unary", "Clz"), ("Unary", "Ctz"), ("Unary", "Popcnt"),
   ("Unary", "Bswap"), ("Unary", "Bitrev"),
   ("Binary", "Iadd"), ("Binary", "Isub"), ("Binary", "Imul"), ("Binary", "Umulhi"),
   ("Binary", "Smulhi"), ("Binary", "Band"), ("Binary", "Bor"), ("Binary", "Bxor"),
   ("Binary", "Ishl"), ("Binary", "Ushr"), ("Binary", "Sshr"), ("Binary", "Rotl"),
   ("Binary", "Rotr"), ("Binary", "Smin"), ("Binary", "Smax"), ("Binary", "Umin"),
   ("Binary", "Umax"),
   ("Binary", "Udiv"), ("Binary", "Sdiv"), ("Binary", "Urem"), ("Binary", "Srem"),
   ("IntCompare", "Icmp"), ("Unary", "Uextend"), ("Unary", "Sextend"), ("Unary", "Ireduce"),
   ("Load", "Load"), ("Load", "Uload8"), ("Load", "Sload8"), ("Load", "Uload16"),
   ("Load", "Sload16"), ("Load", "Uload32"), ("Load", "Sload32"),
   ("Store", "Store"), ("Store", "Istore8"), ("Store", "Istore16"), ("Store", "Istore32"),
   ("Ternary", "Select"), ("NullAry", "Nop"), ("UnaryGlobalValue", "SymbolValue"),
   ("StackAddr", "StackAddr"), ("Call", "Call"),
   ("CallIndirect", "CallIndirect"), ("FuncAddr", "FuncAddr"),
   -- agent/fv-fallback: `bmask` and the atomic opcodes (unverified, outside `E2E.InSubset`)
   ("Unary", "Bmask"), ("LoadNoOffset", "AtomicLoad"), ("StoreNoOffset", "AtomicStore"),
   ("AtomicRmw", "AtomicRmw"), ("AtomicCas", "AtomicCas"), ("NullAry", "Fence"),
   -- agent/fv-lcheck-tls: `tls_value` (unverified, outside `E2E.InSubset`)
   ("UnaryGlobalValue", "TlsValue")]

theorem unaryOpcode_mem {op : Clif.UnaryOp} {n : String} (h : unaryOpcode op = some n) :
    ("Unary", n) ∈ eNamePairs := by
  cases op <;> simp only [unaryOpcode, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp [eNamePairs]

theorem binaryOpcode_mem {op : Clif.BinaryOp} {n : String} (h : binaryOpcode op = some n) :
    ("Binary", n) ∈ eNamePairs := by
  cases op <;> simp only [binaryOpcode, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    simp [eNamePairs]

/-- The names of an E instruction's data are among `eNamePairs`. -/
theorem instNames_mem {f : Clif.Function} {c : Clif.Inst} {d : V} (h : instData f c = .ok d) :
    instNames c ∈ eNamePairs := by
  cases c
  all_goals first
    | (simp only [instData, throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
    | skip
  case unary op ty x =>
    simp only [instNames]
    cases hn : unaryOpcode op with
    | none => simp only [instData, hn, throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
    | some n => exact unaryOpcode_mem hn
  case binary op ty x y =>
    simp only [instNames]
    cases hn : binaryOpcode op with
    | none => simp only [instData, hn, throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
    | some n => exact binaryOpcode_mem hn
  case callIndirect sig callee args =>
    simp only [instNames]
    exact by simp [eNamePairs]
  case funcAddr ty fn =>
    cases ty with
    | i64 =>
      simp only [instNames]
      exact by simp [eNamePairs]
    | _ => simp [instData, throw, throwThe, MonadExceptOf.throw] at h
  case div op _ _ _ => cases op <;> simp [instNames, divOpcode, eNamePairs]
  case load op _ _ _ _ => cases op <;> simp [instNames, loadOpcode, eNamePairs]
  case store op _ _ _ _ _ => cases op <;> simp [instNames, storeOpcode, eNamePairs]
  case extend op _ _ => cases op <;> simp [instNames, eNamePairs]
  all_goals simp [instNames, eNamePairs]

/-- The opcode names only unverified instructions (`Compile.instE` false) produce. -/
def unverifiedNames : List String :=
  ["Bmask", "AtomicLoad", "AtomicStore", "AtomicRmw", "AtomicCas", "Fence", "TlsValue"]

set_option maxRecDepth 20000 in
/-- Every name pair of `eNamePairs` is a format and an opcode of `eOps`, or an `unverifiedNames`
opcode (the `bmask`/atomic/fence/`tls_value` instructions lower but are outside `E2E.InSubset`, so their
opcodes stay out of `eOps` — the excluded-root refutations need that). -/
theorem eNamePairs_idx : eNamePairs.all (fun pr =>
    match variantIdx 152 pr.1, variantIdx 151 pr.2 with
    | some _, some ko => eOps.contains ko || unverifiedNames.contains pr.2
    | _, _ => false) = true := by
  decide +kernel

/-- An E instruction is not one of the atomic/`bmask`/`fence`/`tls_value` instructions. -/
theorem instE_atomic_ne {c : Clif.Inst} (hE : Compile.instE c = true) :
    (instNames c).2 ∉ unverifiedNames := by
  cases c
  all_goals first
    | (simp [Compile.instE] at hE; done)
    | (simp only [instNames]; decide)
    | (simp only [instNames]; rename_i op _ _; cases op <;> decide)
    | (simp only [instNames]; rename_i op _ _ _; cases op <;> decide)
    | (simp only [instNames]; rename_i op _ _ _ _; cases op <;> decide)
    | (simp only [instNames]; rename_i op _ _ _ _ _; cases op <;> decide)
    | (simp only [instNames]; rename_i op _ _ _ _ _ _; cases op <;> decide)

/-- **The data of an E instruction**: format `kf`, E opcode `ko`, fields `fs`. -/
theorem instData_shape {f : Clif.Function} {c : Clif.Inst} {d : V} (hE : Compile.instE c = true)
    (h : instData f c = .ok d) :
    ∃ kf ko fs, d = .data 152 kf (.data 151 ko [] :: fs) ∧ ko ∈ eOps := by
  obtain ⟨rest, hd⟩ := instData_names h
  have hm := List.all_eq_true.mp eNamePairs_idx _ (instNames_mem h)
  have hatom := instE_atomic_ne hE
  generalize instNames c = pr at hm hd hatom
  obtain ⟨n1, n2⟩ := pr
  unfold instDataV opcodeV mkVariant at hd
  cases h1 : variantIdx 152 n1 with
  | none => simp only [h1] at hm; cases hm
  | some kf =>
    cases h2 : variantIdx 151 n2 with
    | none => simp only [h1, h2] at hm; cases hm
    | some ko =>
      simp only [h1, h2, Bool.or_eq_true] at hm hd
      refine ⟨kf, ko, rest, hd, ?_⟩
      rcases hm with hm | hm
      · exact List.contains_iff_mem.mp hm
      · exact absurd (List.contains_iff_mem.mp hm) hatom

set_option maxRecDepth 20000 in
theorem variantNames_Uextend_ex : (variantNames 151)[VIdx.Opcode.Uextend]? = some "Uextend" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Sextend_ex : (variantNames 151)[VIdx.Opcode.Sextend]? = some "Sextend" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_Store_ex : (variantNames 151)[VIdx.Opcode.Store]? = some "Store" := rfl

theorem instNames_extend_ex {c : Clif.Inst} {n : String} (hn : n = "Uextend" ∨ n = "Sextend")
    (h : (instNames c).2 = n) : ∃ op ty x, c = .extend op ty x := by
  rcases hn with rfl | rfl <;>
  cases c <;> simp only [instNames] at h <;>
    first
    | exact ⟨_, _, _, rfl⟩
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at h)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at h)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at h)
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at h)
    | simp at h

theorem instNames_store_ex {c : Clif.Inst} (h : (instNames c).2 = "Store") :
    ∃ ty fl x a off, c = .store .store ty fl x a off := by
  cases c <;> simp only [instNames] at h <;>
    first
    | (rename_i op _ _ _ _ _; cases op <;> simp [storeOpcode] at h; exact ⟨_, _, _, _, _, rfl⟩)
    | (rename_i op _ _; cases op <;> simp [unaryOpcode] at h)
    | (rename_i op _ _ _; cases op <;> simp [binaryOpcode, divOpcode] at h)
    | (rename_i op _ _ _ _; cases op <;> simp [loadOpcode] at h)
    | (rename_i op _ _; cases op <;> simp at h)
    | simp at h

/-- **The fields `opShape` promises.** -/
theorem instData_fields {f : Clif.Function} {ctx : Ctx} {c : Clif.Inst} {kf ko : Nat}
    {fs : List V} (h : instData f c = .ok (.data 152 kf (.data 151 ko [] :: fs)))
    {sh : List AV} (hsh : opShape ko = some sh) : AV.HoldsAll f ctx sh fs := by
  have ho := (instData_inv_names h).2
  unfold opShape at hsh
  split at hsh
  · rename_i hk
    cases hsh
    have hn : (instNames c).2 = "Uextend" ∨ (instNames c).2 = "Sextend" := by
      simp only [Bool.or_eq_true, beq_iff_eq] at hk
      rcases hk with rfl | rfl
      · rw [variantNames_Uextend_ex] at ho; exact .inl (Option.some.inj ho).symm
      · rw [variantNames_Sextend_ex] at ho; exact .inr (Option.some.inj ho).symm
    obtain ⟨op, ty, x, rfl⟩ := instNames_extend_ex (n := (instNames c).2) hn rfl
    simp only [instData] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
      injection h3 with _ h4
      subst h4
      exact ⟨⟨x, rfl⟩, trivial⟩
    · cases h
  · split at hsh
    · rename_i _ hk
      cases hsh
      have hn : (instNames c).2 = "Store" := by
        rw [beq_iff_eq.mp hk, variantNames_Store_ex] at ho; exact (Option.some.inj ho).symm
      obtain ⟨ty, fl, x, a, off, rfl⟩ := instNames_store_ex hn
      simp only [instData] at h
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [pure, Except.pure, Except.ok.injEq] at h
          obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
          injection h3 with _ h4
          subst h4
          exact ⟨⟨[x, a], rfl, rfl⟩, trivial, trivial, trivial⟩
    · cases hsh

/-! ## Extractors on the abstract values -/

section
variable {ctx : Ctx} {term : Term} {st : LState} {fs : List V}

theorem ext_idv_inv {j : Nat} (hid : term.id = TId.inst_data_value)
    (h : externExtract ctx term (.inst j) st = .ok fs) :
    ∃ info, ctx.insts[j]? = some info ∧ fs = [.ty (info.resTys.head?.getD .invalid), info.data] := by
  have e : externExtract ctx term (.inst j) st = match ctx.insts[j]? with
      | some info => .ok [.ty (info.resTys.head?.getD .invalid), info.data]
      | none => .unmodeled s!"inst {j}" := by
    unfold externExtract; rw [hid]; rfl
  rw [e] at h
  cases hi : ctx.insts[j]? with
  | none => rw [hi] at h; cases h
  | some info => rw [hi] at h; cases h; exact ⟨info, rfl, rfl⟩

theorem ext_flagOff {j : Nat} (hf : flagOff term.id = true) :
    externExtract ctx term (.inst j) st = .fail := by
  simp only [flagOff, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with (hid | hid) | hid <;> (unfold externExtract; rw [hid]; rfl)

theorem ext_def_inst_inv {x : Nat} (hid : term.id = TId.def_inst)
    (h : externExtract ctx term (.value x) st = .ok fs) :
    ∃ i, ctx.defInst? x = some i ∧ fs = [.inst i] := by
  have e : externExtract ctx term (.value x) st = match ctx.defInst? x with
      | some i => .ok [.inst i]
      | none => .fail := by
    unfold externExtract; rw [hid]; rfl
  rw [e] at h
  cases hi : ctx.defInst? x with
  | none => rw [hi] at h; cases h
  | some i => rw [hi] at h; cases h; exact ⟨i, rfl, rfl⟩

theorem ext_value_type_inv {x : Nat} (hid : term.id = TId.value_type)
    (h : externExtract ctx term (.value x) st = .ok fs) :
    ∃ t, ctx.valueType? x = some t ∧ fs = [.ty t] := by
  have e : externExtract ctx term (.value x) st = match ctx.valueType? x with
      | some ty => .ok [.ty ty]
      | none => .unmodeled s!"value_type of unknown v{x}" := by
    unfold externExtract; rw [hid]; rfl
  rw [e] at h
  cases hi : ctx.valueType? x with
  | none => rw [hi] at h; cases h
  | some t => rw [hi] at h; cases h; exact ⟨t, rfl, rfl⟩

theorem ext_value_array_2_ex {x y : Nat} (hid : term.id = TId.value_array_2) :
    externExtract ctx term (.values [x, y]) st = .ok [.value x, .value y] := by
  unfold externExtract; rw [hid]; rfl

theorem tyExtract_sound {t : CTy} {r : ExtResult (List V)} (h : tyExtract term.id t = some r) :
    externExtract ctx term (.ty t) st = r := by
  unfold tyExtract at h
  cases hp : tyPred term.id with
  | some pr =>
    rw [hp] at h
    cases h
    unfold externExtract; rw [hp]
  | none =>
    rw [hp] at h
    simp only at h
    split at h
    · rename_i hid
      cases h
      unfold externExtract; rw [hp, beq_iff_eq.mp hid]; rfl
    · split at h
      · rename_i hid
        cases h
        unfold externExtract; rw [hp, beq_iff_eq.mp hid]; rfl
      · cases h

end

end Backend.Proof
