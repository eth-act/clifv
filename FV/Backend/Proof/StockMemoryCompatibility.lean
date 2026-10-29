import FV.Backend.MemoryNIProduction

namespace Backend.Stock.Memory
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
    compileFileMemoryNIWhen enabled allocate pf prior cleanup =
      compileFileParameterCfgNIWhen enabled allocate pf prior cleanup := by
  cases enabled <;> simp [compileFileMemoryNIWhen,none]

/-- A nonempty, successfully parsed ordinary return program inhabits the
compatibility premise. The theorem holds for every allocator, not only this
witness's choice. -/
theorem previous_file_exact_witness :
    ∃ pf : Clif.ParsedFile,
      pf.funcs.length = 1 ∧ pf.funcs.all (·.func.isOk) = true ∧
      (pf.funcs.any fun p => p.func.toOption.any eligible) = false ∧
      compileFileMemoryNIWhen (m := Id) true (fun _ => pure #[]) pf [] true =
        compileFileParameterCfgNIWhen (m := Id) true (fun _ => pure #[]) pf [] true := by
  let pf := Clif.parseFile "function %retained(i64) -> i64 system_v {\nblock0(v0: i64):\n    return v0\n}\n"
  have count : pf.funcs.length = 1 := by decide +kernel
  have parsed : pf.funcs.all (·.func.isOk) = true := by decide +kernel
  have absent : (pf.funcs.any fun p => p.func.toOption.any eligible) = false := by decide +kernel
  exact ⟨pf,count,parsed,absent,previous_file_exact true (fun _ => pure #[]) pf [] true absent⟩

end Backend.Stock.Memory
