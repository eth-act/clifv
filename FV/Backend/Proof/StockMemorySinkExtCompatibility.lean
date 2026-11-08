import FV.Backend.MemorySinkExtNIProduction

namespace Backend.Stock.MemorySinkExt
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Programs outside the optional sinking selector use exactly the previous
pipeline, including allocator effects, identities, output bytes and stages.
This is a compatibility fact; it adds no compiler input requirement. -/
theorem previous_file_exact {m : Type → Type} [Monad m]
    (enabled : Bool) (allocate : Array VCode → m (Array (Except String AFunc)))
    (pf : Clif.ParsedFile) (prior : List (String × String)) (cleanup : Bool)
    (none : (pf.funcs.any fun p => p.func.toOption.any eligible) = false) :
    compileFileMemorySinkExtNIWhen enabled allocate pf prior cleanup =
      compileFileMemoryCapturedCopyNIWhen enabled allocate pf prior cleanup := by
  cases enabled <;> simp [compileFileMemorySinkExtNIWhen,none]

/-- A nonempty ordinary return input inhabits the
compatibility premise. The theorem holds for every allocator, not only this
witness's choice. -/
theorem previous_file_exact_witness :
    ∃ pf : Clif.ParsedFile,
      pf.funcs.length = 1 ∧ pf.funcs.all (·.func.isOk) = true ∧
      (pf.funcs.any fun p => p.func.toOption.any eligible) = false ∧
      compileFileMemorySinkExtNIWhen (m := Id) true (fun _ => pure #[]) pf [] true =
        compileFileMemoryCapturedCopyNIWhen (m := Id) true (fun _ => pure #[]) pf [] true := by
  let f : Clif.Function := {
    name := "retained"
    sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
    blocks := [{ id := 0, params := [(0,.i64)], term := .ret [0] }] }
  let pf : Clif.ParsedFile := {
    header := [], funcs := [{ name := f.name, func := .ok f, runLines := 0 }] }
  have count : pf.funcs.length = 1 := by rfl
  have parsed : pf.funcs.all (·.func.isOk) = true := by rfl
  have absent : (pf.funcs.any fun p => p.func.toOption.any eligible) = false := by rfl
  exact ⟨pf,count,parsed,absent,previous_file_exact true (fun _ => pure #[]) pf [] true absent⟩

/-- Every previously published route keeps its original index. -/
theorem previous_routes_exact : lowerRoutes.take 20 = MemoryCapturedCopy.lowerRoutes := by rfl

/-- A source outside this class retains its exact previous artifact and history. -/
theorem previous_lower_exact {f : Clif.Function} (absent : eligible f = false) :
    lowerValidated f = MemoryCapturedCopy.lowerValidated f := by
  simp [lowerValidated,absent]

/-- Per function: a source outside this class gets exactly the previous checked
artifact, whatever the other functions of its file are. -/
theorem previous_checked_exact {f : Clif.Function} (absent : eligible f = false) (verify : Bool) :
    lowerCheckedMemorySinkExtNI f verify = lowerCheckedMemoryCapturedCopyNI f verify := by
  cases lowered : MemoryCapturedCopy.lowerValidated f with
  | error message =>
    simp only [lowerCheckedMemorySinkExtNI,previous_lower_exact absent,lowered]
    rfl
  | ok vc =>
    cases verify <;> cases checked : SemanticNI.check f vc <;>
      simp [lowerCheckedMemorySinkExtNI,lowerCheckedMemoryCapturedCopyNI,previous_lower_exact absent,
        lowered,checked] <;> rfl

/-- The allocation input of a source outside this class is the previous one. -/
theorem previous_allocation_exact {f : Clif.Function} (absent : eligible f = false)
    (verify cleanup : Bool) :
    lowerForAllocationMemorySinkExtNI f verify cleanup =
      lowerForAllocationMemoryCapturedCopyNI f verify cleanup := by
  simp only [lowerForAllocationMemorySinkExtNI,lowerForAllocationMemoryCapturedCopyNI,
    previous_checked_exact absent]

end Backend.Stock.MemorySinkExt
