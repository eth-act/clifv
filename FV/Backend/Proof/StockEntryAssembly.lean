import FV.Backend.Lowering.Stock
import FV.Backend.Proof.IselInterp
import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.RegallocCSem
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

abbrev EntryInput := ((Nat × Clif.Ty) × ArgLoc) × Nat

def entryGatherFrom (ctx : Ctx) (uses : Array UseState) (rows : List EntryInput)
    (initial : List (Reg × Reg) × Array MInst) :
    Except String (List (Reg × Reg) × Array MInst) := do
  let mut pairs := initial.1
  let mut loads := initial.2
  for (((v,_),loc),bytes) in rows do
    if uses[v]! == .unused then continue
    let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
    match loc with
    | .reg p => pairs := pairs ++ [(r,p)]
    | .stack off => loads := loads.push (.load (loadOpOfBytes bytes) r (.fpOffset (16+off)) trustedFlags)
  pure (pairs,loads)

def entryGather (ctx : Ctx) (uses : Array UseState) (rows : List EntryInput) :=
  entryGatherFrom ctx uses rows ([],#[])

theorem entryGatherFrom_cons (ctx : Ctx) (uses : Array UseState) (row : EntryInput)
    (rows : List EntryInput) (pairs : List (Reg × Reg)) (loads : Array MInst) :
    entryGatherFrom ctx uses (row::rows) (pairs,loads) =
      (if uses[row.1.1.1]! == .unused then entryGatherFrom ctx uses rows (pairs,loads)
      else match ctx.valueReg? row.1.1.1 with
      | none => .error s!"unknown value v{row.1.1.1}"
      | some r => match row.1.2 with
        | .reg pin => entryGatherFrom ctx uses rows (pairs++[(r,pin)],loads)
        | .stack off => entryGatherFrom ctx uses rows
            (pairs,loads.push (.load (loadOpOfBytes row.2) r (.fpOffset (16+off)) trustedFlags))) := by
  rcases row with ⟨⟨⟨value,ty⟩,loc⟩,bytes⟩
  simp only [entryGatherFrom,List.forIn_cons]
  split
  · simp
  · cases mapped : ctx.valueReg? value with
    | none => simp [mapped]
    | some r => cases loc <;> simp [mapped]

structure MappedEntryRow where
  input : EntryInput
  reg : Reg

def mappedEntryRows (ctx : Ctx) (uses : Array UseState) : List EntryInput → Except String (List MappedEntryRow)
  | [] => .ok []
  | row::rows => do
    if uses[row.1.1.1]! == .unused then mappedEntryRows ctx uses rows
    else
      let some r := ctx.valueReg? row.1.1.1 | throw s!"unknown value v{row.1.1.1}"
      let tail ← mappedEntryRows ctx uses rows
      pure (⟨row,r⟩::tail)

def mappedEntryPairs (rows : List MappedEntryRow) : List (Reg × Reg) :=
  rows.filterMap fun row => match row.input.1.2 with
    | .reg pin => some (row.reg,pin)
    | .stack _ => none

def mappedEntryLoads (rows : List MappedEntryRow) : Array MInst :=
  (rows.filterMap fun row => match row.input.1.2 with
    | .reg _ => none
    | .stack off => some (.load (loadOpOfBytes row.input.2) row.reg (.fpOffset (16+off)) trustedFlags)).toArray

/-- The actual gather loop agrees with source-preserving mapped rows, including
omission of unused arguments and the original exception order. -/
theorem entryGatherFrom_mapped (ctx : Ctx) (uses : Array UseState) (rows : List EntryInput)
    (pairs : List (Reg × Reg)) (loads : Array MInst) :
    entryGatherFrom ctx uses rows (pairs,loads) = (do
      let mapped ← mappedEntryRows ctx uses rows
      pure (pairs ++ mappedEntryPairs mapped,loads ++ mappedEntryLoads mapped)) := by
  induction rows generalizing pairs loads with
  | nil => simp [entryGatherFrom,mappedEntryRows,mappedEntryPairs,mappedEntryLoads]
  | cons row rows ih =>
    rcases row with ⟨⟨⟨value,ty⟩,loc⟩,bytes⟩
    rw [entryGatherFrom_cons]
    simp only [mappedEntryRows]
    by_cases unused : uses[value]! == .unused
    · simpa [unused] using ih pairs loads
    · simp only [unused,ite_false]
      cases mapped : ctx.valueReg? value with
      | none => simp [mapped]
      | some r =>
        cases loc with
        | reg pin =>
          cases tail : mappedEntryRows ctx uses rows <;>
            simpa [mapped,tail,mappedEntryPairs,mappedEntryLoads,List.append_assoc,Array.append_assoc]
              using ih (pairs++[(r,pin)]) loads
        | stack off =>
          let instruction := MInst.load (loadOpOfBytes bytes) r (.fpOffset (16+off)) trustedFlags
          cases tail : mappedEntryRows ctx uses rows with
          | error message => simpa [mapped,tail] using ih pairs (loads.push instruction)
          | ok remaining =>
            have appended : loads.push instruction ++ mappedEntryLoads remaining =
                loads ++ mappedEntryLoads (⟨(((value,ty),.stack off),bytes),r⟩::remaining) := by
              apply Array.toList_inj.mp
              simp [mappedEntryLoads,instruction,Array.toList_append,Array.toList_push,List.append_assoc]
            have h := ih pairs (loads.push instruction)
            simp only [tail,bind,Except.bind,pure,Except.pure] at h
            rw [appended] at h
            simpa [mapped,tail,mappedEntryPairs,instruction,List.append_assoc] using h

/-- Every emitted entry row retains its original source row and actual
register lookup; skipped rows do not invent data or change order. -/
theorem mappedEntryRows_spec {ctx : Ctx} {uses : Array UseState}
    {input : List EntryInput} {output : List MappedEntryRow}
    (run : mappedEntryRows ctx uses input = .ok output) :
    (output.map (·.input)).Sublist input ∧
      ∀ row ∈ output, uses[row.input.1.1.1]! ≠ .unused ∧
        ctx.valueReg? row.input.1.1.1 = some row.reg := by
  induction input generalizing output with
  | nil =>
    simp only [mappedEntryRows,Except.ok.injEq] at run
    subst output
    exact ⟨.slnil,by simp⟩
  | cons row rows ih =>
    simp only [mappedEntryRows] at run
    by_cases unused : uses[row.1.1.1]! == .unused
    · simp only [unused,ite_true] at run
      obtain ⟨order,facts⟩ := ih run
      exact ⟨order.cons row,facts⟩
    · simp only [unused,ite_false] at run
      cases lookup : ctx.valueReg? row.1.1.1 with
      | none => simp [lookup] at run
      | some r =>
        cases tail : mappedEntryRows ctx uses rows with
        | error message => simp [lookup,tail] at run
        | ok remaining =>
          simp only [lookup,tail,bind,Except.bind,pure,Except.pure,Bool.false_eq_true,ite_false,Except.ok.injEq] at run
          subst output
          obtain ⟨order,facts⟩ := ih tail
          refine ⟨order.cons_cons row,?_⟩
          intro current member
          rcases List.mem_cons.mp member with rfl | member
          · refine ⟨?_,lookup⟩
            intro equal
            apply unused
            simp [equal]
          · exact facts current member

def entryPrelude (pairs : List (Reg × Reg)) (loads : Array MInst) : Array MInst :=
  if !pairs.isEmpty then #[.args pairs] ++ loads else loads

/-- The actual entry constructor uses exactly the gathered register copies and
stack loads; no operational or metadata fields are dropped. -/
theorem assemble_entry_eq (ctx : Ctx) (f : Clif.Function) (b : Clif.Block)
    (label : Nat) (targets : Array Nat) (outgoing : Array (Array Reg))
    (bytes : List Nat) (uses : Array UseState) (body : Array MInst) :
    assembleOriginalBlock ctx f b 0 label targets outgoing bytes uses body = (do
      let (locs,_) ← sigArgLocs f.sig
      let (pairs,loads) ← entryGather ctx uses ((b.params.zip locs).zip bytes)
      pure ({ label := label, insts := entryPrelude pairs loads ++ body, params := #[], branchArgs := if targets.size == 1 then outgoing[0]! else #[] } : VBlock)) := by
  simp only [assembleOriginalBlock,entryGather,entryGatherFrom,entryPrelude,beq_self_eq_true,ite_true]
  simp only [bind_assoc,pure_bind]
  congr 1
  funext data
  rcases data with ⟨locs,stack⟩
  simp only [bind_assoc,pure_bind]
  congr 1
  funext data
  rcases data with ⟨pairs,loads⟩
  split <;> simp [Array.append_assoc]
/-- Actual successful assembly supplies its source/ABI rows and complete
entry code by construction, without per-row input certificates. -/
theorem assemble_entry_source_rows {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {bytes : List Nat} {uses : Array UseState} {body : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b 0 label targets outgoing bytes uses body = .ok block) :
    ∃ locs stack rows, sigArgLocs f.sig = .ok (locs,stack) ∧
      mappedEntryRows ctx uses ((b.params.zip locs).zip bytes) = .ok rows ∧
      (rows.map (·.input)).Sublist ((b.params.zip locs).zip bytes) ∧
      (∀ row ∈ rows, uses[row.input.1.1.1]! ≠ .unused ∧
        ctx.valueReg? row.input.1.1.1 = some row.reg) ∧
      block = { label := label, insts := entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows) ++ body, params := #[], branchArgs := if targets.size == 1 then outgoing[0]! else #[] } := by
  rw [assemble_entry_eq] at run
  cases signature : sigArgLocs f.sig with
  | error message => simp [signature] at run
  | ok data =>
    rcases data with ⟨locs,stack⟩
    simp only [signature,bind,Except.bind] at run
    unfold entryGather at run
    rw [entryGatherFrom_mapped] at run
    cases mapped : mappedEntryRows ctx uses ((b.params.zip locs).zip bytes) with
    | error message => simp [mapped] at run
    | ok rows =>
      simp only [mapped,bind,Except.bind,pure,Except.pure,List.nil_append,Array.empty_append] at run
      cases run
      obtain ⟨order,facts⟩ := mappedEntryRows_spec mapped
      exact ⟨locs,stack,rows,rfl,mapped,order,facts,rfl⟩

end Backend.Stock.Proof
