import FV.Backend.Proof.StockSourceEntry
import FV.Backend.Proof.StockEntryAssembly
import FV.Backend.Proof.StockEntryArgs
import FV.Backend.Proof.StockEntryLoads

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Original source entry fixes the value, ABI location and supported byte width
of each source-preserving entry row. No per-row value certificate is required. -/
theorem entered_source_abi_row_frame {f : Clif.Function} {args : List Clif.Val}
    {fr : Clif.Frame} {b : Clif.Block}
    (entered : SourceEntry f args fr)
    (ssa : (valueDefs f).Nodup) (block : f.blocks[0]? = some b)
    {locs : List ArgLoc} {stack : Nat}
    (locations : sigArgLocs f.sig = .ok (locs,stack))
    {bytes : List Nat} (sizes : sigParamBytes f.sig = .ok bytes)
    {row : EntryInput} (member : row ∈ (b.params.zip locs).zip bytes)
    {v : Clif.Val} (found : fr.regs row.1.1.1 = some v) :
    (row.1.2,v) ∈ (locsOf f.sig).zip args ∧ row.2 = v.ty.bytes ∧
      (row.2 = 1 ∨ row.2 = 2 ∨ row.2 = 4 ∨ row.2 = 8) := by
  have entryFacts := entered
  obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have sameBlock : b' = b := by
    have entryBlock : f.blocks[0]? = some b' := by
      simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
    exact Option.some.inj (entryBlock.symm.trans block)
  subst b'
  have frameRegs : fr.regs = regs := congrArg (fun frame : Clif.Frame => frame.regs) frame
  have nd := (List.nodup_append.mp (block_nodup ssa block)).1
  obtain ⟨i,atRow⟩ := List.mem_iff_getElem?.mp member
  have rowParts := atRow
  simp only [List.getElem?_zip_eq_some] at rowParts
  obtain ⟨⟨atParam,atLoc⟩,atSize⟩ := rowParts
  have atID : (b.params.map (·.1))[i]? = some row.1.1.1 := by
    simp only [List.getElem?_map,atParam,Option.map_some]
  obtain ⟨j,v',atID',atArg',lookup⟩ := setMany_mem set nd row.1.1.1
    (List.mem_of_getElem? atID)
  have sameIndex : i = j :=
    (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp atID).1 nd).mp
      (atID.trans atID'.symm)
  subst j
  have sameValue : v' = v := Option.some.inj (lookup.symm.trans (frameRegs ▸ found))
  subst v'
  have located : (row.1.2,v) ∈ locs.zip args :=
    List.mem_iff_getElem?.mpr ⟨i,by simp [List.getElem?_zip_eq_some,atLoc,atArg']⟩
  have byteValue : row.2 = v.ty.bytes := by
    have bytesMap := sigParamBytes_eq_map sizes
    rw [bytesMap,List.getElem?_map] at atSize
    have typed := congrArg (·[i]?) argTypes
    simp only [Clif.AbiParam.tys,List.getElem?_map,atArg',Option.map_some] at typed
    cases hp : f.sig.params[i]? with
    | none => rw [hp] at atSize; cases atSize
    | some p =>
      rw [hp] at typed atSize
      simp only [Option.map_some,Option.some.injEq] at typed atSize
      rw [← atSize,typed]
  exact ⟨by simpa only [locsOf,locations] using located,byteValue,
    sigParamBytes_bytes sizes _ (List.mem_of_getElem? atSize)⟩

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem entered_source_abi_row {f : Clif.Function} {args : List Clif.Val}
    {cm0 cm : Clif.Mem} {fr : Clif.Frame} {b : Clif.Block}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    (ssa : (valueDefs f).Nodup) (block : f.blocks[0]? = some b)
    {locs : List ArgLoc} {stack : Nat}
    (locations : sigArgLocs f.sig = .ok (locs,stack))
    {bytes : List Nat} (sizes : sigParamBytes f.sig = .ok bytes)
    {row : EntryInput} (member : row ∈ (b.params.zip locs).zip bytes)
    {v : Clif.Val} (found : fr.regs row.1.1.1 = some v) :
    (row.1.2,v) ∈ (locsOf f.sig).zip args ∧ row.2 = v.ty.bytes ∧
      (row.2 = 1 ∨ row.2 = 2 ∨ row.2 = 4 ∨ row.2 = 8) := by
  exact entered_source_abi_row_frame (SourceEntry.of_enterFunc entered) ssa block locations sizes member found

/-- Every original parameter row has its entered source value, including rows
whose machine copy is omitted as unused. -/
theorem entered_source_row_value_frame {f : Clif.Function} {args : List Clif.Val}
    {fr : Clif.Frame} {b : Clif.Block}
    (entered : SourceEntry f args fr)
    (ssa : (valueDefs f).Nodup) (block : f.blocks[0]? = some b)
    {locs : List ArgLoc} {bytes : List Nat} {row : EntryInput}
    (member : row ∈ (b.params.zip locs).zip bytes) :
    ∃ v, fr.regs row.1.1.1 = some v := by
  have entryFacts := entered
  obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have sameBlock : b' = b := by
    have entryBlock : f.blocks[0]? = some b' := by
      simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
    exact Option.some.inj (entryBlock.symm.trans block)
  subst b'
  have frameRegs : fr.regs = regs := congrArg (fun frame : Clif.Frame => frame.regs) frame
  have nd := (List.nodup_append.mp (block_nodup ssa block)).1
  have parameter : row.1.1 ∈ b.params := (List.of_mem_zip (List.of_mem_zip member).1).1
  obtain ⟨i,v,_,_,lookup⟩ := setMany_mem set nd row.1.1.1
    (List.mem_map.mpr ⟨row.1.1,parameter,rfl⟩)
  exact ⟨v,frameRegs ▸ lookup⟩

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem entered_source_row_value {f : Clif.Function} {args : List Clif.Val}
    {cm0 cm : Clif.Mem} {fr : Clif.Frame} {b : Clif.Block}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    (ssa : (valueDefs f).Nodup) (block : f.blocks[0]? = some b)
    {locs : List ArgLoc} {bytes : List Nat} {row : EntryInput}
    (member : row ∈ (b.params.zip locs).zip bytes) :
    ∃ v, fr.regs row.1.1.1 = some v := by
  exact entered_source_row_value_frame (SourceEntry.of_enterFunc entered) ssa block member

def entryRowKey (row : MappedEntryRow) : Nat :=
  match row.reg with
  | .vreg key _ => key
  | _ => 0

def denseEntryRow (row : MappedEntryRow) : EntryInput :=
  (((entryRowKey row,row.input.1.1.2),row.input.1.2),row.input.2)

private theorem input_ids_sublist (params : List (Nat × Clif.Ty))
    (locs : List ArgLoc) (bytes : List Nat) :
    (((params.zip locs).zip bytes).map (·.1.1.1)).Sublist (params.map (·.1)) := by
  induction params generalizing locs bytes with
  | nil => simp
  | cons param params ih =>
    cases locs with
    | nil => simp
    | cons loc locs =>
      cases bytes with
      | nil => simp
      | cons byte bytes => exact (ih locs bytes).cons_cons param.1

/-- Selected entry rows use distinct actual dense virtual registers. Omission
preserves order, and source SSA plus the real mapping excludes collisions. -/
theorem mapped_entry_dense_nodup {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) (ssa : (valueDefs f).Nodup)
    {b : Clif.Block} (block : f.blocks[0]? = some b)
    {uses : Array UseState} {locs : List ArgLoc} {bytes : List Nat}
    {rows : List MappedEntryRow}
    (mapped : mappedEntryRows ctx uses ((b.params.zip locs).zip bytes) = .ok rows) :
    ((rows.map denseEntryRow).map (·.1.1.1)).Nodup := by
  obtain ⟨ordered,facts⟩ := mappedEntryRows_spec mapped
  have ids : (rows.map (·.input.1.1.1)).Nodup := by
    have sub := ordered.map (fun row : EntryInput => row.1.1.1)
    simp only [List.map_map,Function.comp_def] at sub
    exact sub.nodup ((input_ids_sublist b.params locs bytes).nodup
      (List.nodup_append.mp (block_nodup ssa block)).1)
  simp only [List.map_map] at ⊢
  change (rows.map entryRowKey).Nodup
  rw [List.nodup_iff_pairwise_ne,List.pairwise_map] at ids ⊢
  apply List.Pairwise.imp_of_mem (p := ids)
  intro a b amem bmem different equal
  obtain ⟨ka,areg⟩ := inv.valueReg _ _ (facts a amem).2
  obtain ⟨kb,breg⟩ := inv.valueReg _ _ (facts b bmem).2
  have keys : ka = kb := by simpa [entryRowKey,areg,breg] using equal
  apply different
  apply inv.injective _ _ ka
  · simpa only [areg] using (facts a amem).2
  · simpa only [breg,keys] using (facts b bmem).2

theorem mapped_entry_reg {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {uses : Array UseState} {input : List EntryInput} {rows : List MappedEntryRow}
    (mapped : mappedEntryRows ctx uses input = .ok rows) {row : MappedEntryRow}
    (member : row ∈ rows) :
    row.reg = .vreg (entryRowKey row) .int ∧
      ctx.valueReg? row.input.1.1.1 = some (.vreg (entryRowKey row) .int) := by
  have lookup := ((mappedEntryRows_spec mapped).2 row member).2
  obtain ⟨key,reg⟩ := inv.valueReg _ _ lookup
  have actual : entryRowKey row = key := by simp [entryRowKey,reg]
  exact ⟨by simpa only [actual] using reg,by simpa only [reg,actual] using lookup⟩

/-- The dense-row representation is exactly the emitted entry code, rather
than an independently reconstructed argument convention. -/
theorem mapped_entry_code {rows : List MappedEntryRow}
    (virtual : ∀ row ∈ rows, row.reg = .vreg (entryRowKey row) .int) :
    mappedEntryPairs rows = argPairs (entryNs (rows.map denseEntryRow)) ∧
      (mappedEntryLoads rows).toList = (rows.map denseEntryRow).filterMap (entryLoadOf id) := by
  induction rows with
  | nil => simp [mappedEntryPairs,mappedEntryLoads,entryNs,argPairs]
  | cons row rows ih =>
    have head := virtual row (by simp)
    have tail := ih (fun row member => virtual row (List.mem_cons_of_mem _ member))
    cases loc : row.input.1.2 <;>
      simp_all [mappedEntryPairs,mappedEntryLoads,entryNs,argPairs,denseEntryRow,
        entryLoadOf,List.filterMap_cons]

/-- Execute the actual filtered ABI prelude from an entered source frame.
Source SSA, mapping and ABI facts discharge every copy/load side condition;
unused parameters retain their seeded values without extra input conditions. -/
theorem mapped_entry_prelude_preserves_frame {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {args : List Clif.Val} {cm : Clif.Mem}
    {fr : Clif.Frame} {b : Clif.Block}
    (entered : SourceEntry f args fr)
    (ssa : (valueDefs f).Nodup) (block : f.blocks[0]? = some b)
    {locs : List ArgLoc} {stack : Nat}
    (locations : sigArgLocs f.sig = .ok (locs,stack))
    {bytes : List Nat} (sizes : sigParamBytes f.sig = .ok bytes)
    {uses : Array UseState} {rows : List MappedEntryRow}
    (mapped : mappedEntryRows ctx uses ((b.params.zip locs).zip bytes) = .ok rows)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : ValuesHeld (fun _ => True) ctx fr ρ) (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ' w', seqRun isem (entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows)).toList
        ρ w = some (.fall ρ' w') ∧ MR fr.slots cm w' ∧
      ValuesHeld (fun _ => True) ctx fr ρ' ∧ SameWorld F w' w := by
  let entries := rows.map denseEntryRow
  have nd := mapped_entry_dense_nodup inv ssa block mapped
  have virtual := fun row member => (mapped_entry_reg inv mapped (row := row) member).1
  obtain ⟨pairsCode,loadsCode⟩ := mapped_entry_code virtual
  change mappedEntryPairs rows = argPairs (entryNs entries) at pairsCode
  change (mappedEntryLoads rows).toList = entries.filterMap (entryLoadOf id) at loadsCode
  have rowMember : ∀ row ∈ rows, row.input ∈ (b.params.zip locs).zip bytes := by
    intro row member
    exact (mappedEntryRows_spec mapped).1.subset (List.mem_map.mpr ⟨row,member,rfl⟩)
  have rowABI : ∀ row ∈ rows, ∃ v, fr.regs row.input.1.1.1 = some v ∧
      (row.input.1.2,v) ∈ (locsOf f.sig).zip args ∧ row.input.2 = v.ty.bytes ∧
      (row.input.2 = 1 ∨ row.input.2 = 2 ∨ row.input.2 = 4 ∨ row.input.2 = 8) := by
    intro row member
    obtain ⟨v,found⟩ := entered_source_row_value_frame entered ssa block (rowMember row member)
    exact ⟨v,found,entered_source_abi_row_frame entered ssa block locations sizes
      (rowMember row member) found⟩
  have copies : ∀ x v key pin, fr.regs x = some v →
      ctx.valueReg? x = some (.vreg key .int) →
      (key,pin) ∈ entryNs entries → VHolds v (regVal w pin) := by
    intro x v key pin found lookup member
    obtain ⟨q,qmem,qp⟩ := List.mem_filterMap.mp member
    obtain ⟨row,rowmem,rfl⟩ := List.mem_map.mp qmem
    cases loc : row.input.1.2 with
    | stack off => simp [denseEntryRow,loc] at qp
    | reg p =>
      have pair : entryRowKey row = key ∧ p = pin := by
        simpa [denseEntryRow,loc] using qp
      have same : row.input.1.1.1 = x := inv.injective _ _ key
        (by simpa only [pair.1] using (mapped_entry_reg inv mapped rowmem).2) lookup
      have abi := entered_source_abi_row_frame entered ssa block locations sizes
        (rowMember row rowmem) (by simpa only [same] using found)
      have arg := arguments _ _ abi.1
      simpa only [loc,pair.2] using arg
  have loadRun : ∀ ρ₁, ValuesHeld (fun _ => True) ctx fr ρ₁ →
      ∃ ρ' w', seqRun isem (entries.filterMap (entryLoadOf id)) ρ₁ w = some (.fall ρ' w') ∧
        MR fr.slots cm w' ∧ ValuesHeld (fun _ => True) ctx fr ρ' ∧ SameWorld F w' w := by
    intro ρ₁ held₁
    apply entry_loads_preserve_values memorySem stable entries nd held₁ memory
    · intro q qmem off loc
      obtain ⟨row,rowmem,rfl⟩ := List.mem_map.mp qmem
      obtain ⟨v,found,located,width,supported⟩ := rowABI row rowmem
      have sourceLoc : row.input.1.2 = .stack off := loc
      have abi := arguments _ _ located
      rw [sourceLoc] at abi
      exact ⟨supported,by simpa only [denseEntryRow,width] using abi.1⟩
    · intro x v key q off found lookup qmem equal loc
      obtain ⟨row,rowmem,rfl⟩ := List.mem_map.mp qmem
      have keyEq : entryRowKey row = key := equal
      have same : row.input.1.1.1 = x := inv.injective _ _ key
        (by simpa only [keyEq] using (mapped_entry_reg inv mapped rowmem).2) lookup
      obtain ⟨located,width,supported⟩ := entered_source_abi_row_frame entered ssa block locations sizes
        (rowMember row rowmem) (by simpa only [same] using found)
      have sourceLoc : row.input.1.2 = .stack off := loc
      have abi := arguments _ _ located
      rw [sourceLoc] at abi
      obtain ⟨opbytes,_,unsigned⟩ := loadOpOfBytes_facts supported
      have narrow : v.ty.width ≤ 64 :=
        (show ∀ t : Clif.Ty, (t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8) →
          t.width ≤ 64 by intro t; cases t <;> decide) _ (width ▸ supported)
      simp only [denseEntryRow,VHolds,ofX,loadVal,unsigned,Bool.false_eq_true,↓reduceIte]
      rw [opbytes,width,BitVec.setWidth_setWidth_of_le _ (by omega),
        BitVec.setWidth_setWidth_of_le _ narrow]
      exact abi.2
  by_cases empty : entryNs entries = []
  · obtain ⟨ρ',w',execution,mem,values,same⟩ := loadRun ρ held
    refine ⟨ρ',w',?_,mem,values,same⟩
    simpa [entryPrelude,pairsCode,empty,argPairs,loadsCode] using execution
  · obtain ⟨ρ₁,copied,held₁⟩ := entry_args_preserve_values driver (entryNs entries)
      ((entryNs_sublist entries).nodup nd) held copies
    obtain ⟨ρ',w',loaded,mem,values,same⟩ := loadRun ρ₁ held₁
    refine ⟨ρ',w',?_,mem,values,same⟩
    have nonempty : (argPairs (entryNs entries)).isEmpty = false := by
      cases ns : entryNs entries with
      | nil => exact False.elim (empty ns)
      | cons pair pairs => rfl
    simpa [entryPrelude,pairsCode,nonempty,loadsCode] using
      seqRun_append_fall' isem copied loaded

/-- Executable-entry compatibility variant; retains the original statement. -/
theorem mapped_entry_prelude_preserves {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {args : List Clif.Val} {cm0 cm : Clif.Mem}
    {fr : Clif.Frame} {b : Clif.Block}
    (entered : Clif.enterFunc f args cm0 = .ok (fr,cm))
    (ssa : (valueDefs f).Nodup) (block : f.blocks[0]? = some b)
    {locs : List ArgLoc} {stack : Nat}
    (locations : sigArgLocs f.sig = .ok (locs,stack))
    {bytes : List Nat} (sizes : sigParamBytes f.sig = .ok bytes)
    {uses : Array UseState} {rows : List MappedEntryRow}
    (mapped : mappedEntryRows ctx uses ((b.params.zip locs).zip bytes) = .ok rows)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : ValuesHeld (fun _ => True) ctx fr ρ) (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ' w', seqRun isem (entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows)).toList
        ρ w = some (.fall ρ' w') ∧ MR fr.slots cm w' ∧
      ValuesHeld (fun _ => True) ctx fr ρ' ∧ SameWorld F w' w := by
  exact mapped_entry_prelude_preserves_frame inv (SourceEntry.of_enterFunc entered) ssa block locations sizes mapped driver memorySem stable held memory arguments

/-- Final resolution of source parameters leaves the actual entry prelude
unchanged. Physical ABI source registers are deliberately not virtual uses. -/
theorem mapped_entry_prelude_fixed (rename : Reg → Reg) {rows : List MappedEntryRow}
    (fixed : ∀ row ∈ rows, rename row.reg = row.reg) :
    (entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows)).map (·.mapRegs rename) =
      entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows) := by
  have rowsFixed :
      (mappedEntryPairs rows).map (fun (v,p) => (rename v,p)) = mappedEntryPairs rows ∧
      (mappedEntryLoads rows).map (·.mapRegs rename) = mappedEntryLoads rows := by
    induction rows with
    | nil => simp [mappedEntryPairs,mappedEntryLoads]
    | cons row rows ih =>
      have head := fixed row (by simp)
      have tail := ih (fun r member => fixed r (List.mem_cons_of_mem _ member))
      cases loc : row.input.1.2 <;>
        simp_all [mappedEntryPairs,mappedEntryLoads,MInst.mapRegs,AMode.mapRegs]
  unfold entryPrelude
  split <;> simp_all [Array.map_append,MInst.mapRegs]

end Backend.Stock.Proof
