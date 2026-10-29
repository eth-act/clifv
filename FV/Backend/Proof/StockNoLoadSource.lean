module

public import FV.Backend.Proof.StockNoLoadSink
public import FV.Backend.Proof.StockDFG
public import FV.Backend.Proof.IselExclData
public import FV.Backend.Proof.StockHighMulFamily

@[expose] public section

namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem formats_checked : eNamePairs.all (fun pair => decide
    (pair.1 ≠ "Load" → pair.1 ≠ "LoadNoOffset" →
      variantIdx 152 pair.1 ≠ some 16 ∧ variantIdx 152 pair.1 ≠ some 17)) = true := by
  decide +kernel

/-- Existing source-format classification excludes both actual sinking formats;
this is derived from instruction data, not an additional accepted-input check. -/
theorem inst_data_no_load {ctx : Ctx} {f : Clif.Function} {inst : Clif.Inst} {data : V}
    (integer : Compile.instE inst = true) (format : CastComplete.MemoryFormat inst)
    (encoded : instData f inst = .ok data) :
    ∀ fmt fields, fmt = 16 ∨ fmt = 17 → (Backend.sem ctx).unData 152 data ≠ some (fmt,fields) := by
  rcases instData_names encoded with ⟨rest,shape⟩ | ⟨ty,imm,eq,float,rest,shape | shape⟩
  · have checked := List.all_eq_true.mp formats_checked _ (instNames_mem integer encoded)
    have safe := (of_decide_eq_true checked) format.2 format.1
    unfold instDataV mkVariant at shape
    cases index : variantIdx 152 (instNames inst).1 with
    | none =>
      simp only [index] at shape
      intro fmt fields load decoded
      simp [Backend.sem,shape] at decoded
    | some k =>
      simp only [index] at shape
      have not16 : k ≠ 16 := fun eq => safe.1 (index.trans (congrArg some eq))
      have not17 : k ≠ 17 := fun eq => safe.2 (index.trans (congrArg some eq))
      intro fmt fields load decoded
      rcases load with rfl | rfl
      · simp [Backend.sem,shape,not16] at decoded
      · simp [Backend.sem,shape,not17] at decoded
  · intro fmt fields load decoded
    rcases load with rfl | rfl <;> simp [Backend.sem,shape] at decoded
  · intro fmt fields load decoded
    rcases load with rfl | rfl <;> simp [Backend.sem,shape] at decoded

/-- Successful Stock context construction retains only original source data and
terminator placeholders, so existing per-statement facts imply the helper invariant. -/
theorem build_ctx_no_load {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (built : Stock.buildCtx f = .ok (ctx,ranges,st))
    (integer : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, Compile.instE stm.inst = true)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst) :
    NoLoadData ctx := by
  obtain ⟨original,base,run,spec,view⟩ := buildCtx_source built
  intro i info found fmt fields load decoded
  have member : info ∈ original.insts.toList := by
    rw [← view.insts]
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
  rcases spec.insts info member with rfl | ⟨b,present,stm,statement,rfl⟩
  · change none = some (fmt,fields) at decoded
    cases decoded
  · change (Backend.sem ctx).unData 152 (dataOf f stm) = some (fmt,fields) at decoded
    unfold dataOf at decoded
    cases encoded : instData f stm.inst with
    | error message =>
      simp only [encoded] at decoded
      change none = some (fmt,fields) at decoded
      cases decoded
    | ok data =>
      simp only [encoded] at decoded
      exact inst_data_no_load (integer b present stm statement)
        (formats b present stm statement) encoded fmt fields load decoded

/-- The original scope supplies instruction admission; callers only provide the
already-established source-family format classification. -/
theorem scoped_build_ctx_no_load {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {st : State}
    (built : Stock.buildCtx f = .ok (ctx,ranges,st)) (scope : LowerScope f)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst) :
    NoLoadData ctx :=
  build_ctx_no_load built (fun _ hb _ hs => Compile.instE_of_functionE scope.subsetE hb hs) formats

/-- Filling the terminator placeholder retains the invariant for any non-load
terminator data. Other context fields may change independently. -/
theorem term_ctx_no_load {ctx : Ctx} (safe : NoLoadData ctx) (ti : Nat) (data : V)
    (dataSafe : ∀ fmt fields, fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 data ≠ some (fmt,fields)) :
    NoLoadData (termCtx ctx ti data) := by
  intro i info found fmt fields load decoded
  by_cases same : i = ti
  · subst i
    by_cases inside : ti < ctx.insts.size
    · have old : ∃ installed, ctx.insts[ti]? = some installed :=
        ⟨ctx.insts[ti],Array.getElem?_eq_getElem inside⟩
      obtain ⟨installed,old⟩ := old
      rw [termCtx_insts_self old data] at found
      cases found
      exact dataSafe fmt fields load decoded
    · have outside : (termCtx ctx ti data).insts[ti]? = none := by
        apply Array.getElem?_eq_none
        simpa [termCtx] using Nat.le_of_not_gt inside
      rw [outside] at found
      cases found
  · rw [termCtx_insts_ne same data] at found
    exact safe i info found fmt fields load decoded

private theorem value_format_no_load {ctx : Ctx} {name : String} {values : List V}
    (safe : variantIdx 152 name ≠ some 16 ∧ variantIdx 152 name ≠ some 17) :
    ∀ fmt fields, fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 (instDataV name values) ≠ some (fmt,fields) := by
  unfold instDataV mkVariant
  cases index : variantIdx 152 name with
  | none => intro fmt fields load decoded; cases decoded
  | some k =>
    have not16 : k ≠ 16 := fun eq => safe.1 (index.trans (congrArg some eq))
    have not17 : k ≠ 17 := fun eq => safe.2 (index.trans (congrArg some eq))
    intro fmt fields load decoded
    rcases load with rfl | rfl
    · simp [Backend.sem,not16] at decoded
    · simp [Backend.sem,not17] at decoded

/-- Every ordinary terminator format is disjoint from the two load formats. -/
theorem term_data_no_load {ctx : Ctx} {term : Clif.Terminator} {data : V}
    (encoded : termData term = .ok data) :
    ∀ fmt fields, fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 data ≠ some (fmt,fields) := by
  cases term <;> simp only [termData,pure,Except.pure] at encoded
  all_goals try cases encoded
  all_goals
    apply value_format_no_load
    decide +kernel

/-- Exception-call data also uses non-load formats; no call-signature facts
are substituted for the actual successful data construction. -/
theorem try_call_data_no_load {ctx : Ctx} {f : Clif.Function}
    {term : Clif.Terminator} {data : V} (encoded : tryCallData f term = .ok data) :
    ∀ fmt fields, fmt = 16 ∨ fmt = 17 →
      (Backend.sem ctx).unData 152 data ≠ some (fmt,fields) := by
  cases term <;> unfold tryCallData at encoded
  all_goals
    repeat' first
      | (solve | cases encoded)
      | simp only [bind,Except.bind,pure,Except.pure] at encoded
      | split at encoded
  all_goals
    cases encoded
    apply value_format_no_load
    decide +kernel

/-- Every shipped scalar family and every division has non-load source data,
regardless of position, number of divisions, operands or result demand. -/
theorem scalar_div_formats {inst : Clif.Inst}
    (family : HighMulBody.Family inst ∨ ∃ op ty x y, inst = .div op ty x y) :
    CastComplete.MemoryFormat inst := by
  rcases family with scalar | ⟨op,ty,x,y,rfl⟩
  · exact HighMulBody.family_formats scalar
  · simp [CastComplete.MemoryFormat,instNames]

/-- All actual source slots start unsunk, independently of their effect color. -/
theorem build_ctx_sunk_false {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (built : Stock.buildCtx f = .ok (ctx,ranges,initial)) (q : Nat) :
    initial.sunk[q]! = false := by
  obtain ⟨original,base,requests,old,_,finished⟩ := buildCtx_allocation built
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) finished
  dsimp only at state
  rw [state]
  change (Array.replicate original.insts.size false)[q]! = false
  by_cases bound : q < original.insts.size <;>
    simp [getElem!_def,Array.getElem?_replicate,bound]

end Backend.Stock.Proof.SinkRules
