import FV.Backend.MemoryStoreNIProduction

namespace Backend.Stock.MemoryStore
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Programs outside the optional memory selector use exactly the previous
pipeline, including allocator effects, identities, output bytes and stages.
This is a compatibility fact; it adds no compiler input requirement. -/
theorem previous_file_exact {m : Type → Type} [Monad m]
    (enabled : Bool) (allocate : Array VCode → m (Array (Except String AFunc)))
    (pf : Clif.ParsedFile) (prior : List (String × String)) (cleanup : Bool)
    (none : (pf.funcs.any fun p => p.func.toOption.any eligible) = false) :
    compileFileMemoryStoreNIWhen enabled allocate pf prior cleanup =
      compileFileMemoryExtLoadNIWhen enabled allocate pf prior cleanup := by
  cases enabled <;> simp [compileFileMemoryStoreNIWhen,none]

/-- A nonempty ordinary return input inhabits the
compatibility premise. The theorem holds for every allocator, not only this
witness's choice. -/
theorem previous_file_exact_witness :
    ∃ pf : Clif.ParsedFile,
      pf.funcs.length = 1 ∧ pf.funcs.all (·.func.isOk) = true ∧
      (pf.funcs.any fun p => p.func.toOption.any eligible) = false ∧
      compileFileMemoryStoreNIWhen (m := Id) true (fun _ => pure #[]) pf [] true =
        compileFileMemoryExtLoadNIWhen (m := Id) true (fun _ => pure #[]) pf [] true := by
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
theorem previous_routes_exact : lowerRoutes.take 16 = MemoryExtending.lowerRoutes := by rfl

/-- A source outside this class retains its exact previous artifact and history. -/
theorem previous_lower_exact {f : Clif.Function} (absent : eligible f = false) :
    lowerValidated f = MemoryExtending.lowerValidated f := by
  simp [lowerValidated,absent]

end Backend.Stock.MemoryStore
