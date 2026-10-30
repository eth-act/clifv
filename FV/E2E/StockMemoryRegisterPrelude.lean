import FV.E2E.StockMemoryPairedReturnAt
import FV.Backend.Proof.StockEntryPrelude

namespace E2E.StockMemory
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem register_run_world {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    {ms : List MInst} (onlyArgs : ∀ i ∈ ms,∃ ds,i = .args ds)
    {ρ ρ' : Nat → CV} {w t : Arm.ArmState}
    (run : seqRun (csem F fc X) ms ρ w = some (.fall ρ' t)) : t = w := by
  induction ms generalizing ρ w with
  | nil => exact (SeqEnd.fall.inj (Option.some.inj run)).2.symm
  | cons i rest ih =>
    obtain ⟨ds,rfl⟩ := onlyArgs i (List.mem_cons_self ..)
    obtain ⟨ops,outs,middle,operands,first,length,tail⟩ := seqRun_cons_fall run
    have expected : csem F fc X (.args ds) (vuses ops ρ) w = some (ds.map (fun p => regVal w p.2),w,.next) := rfl
    have equal := congrArg (fun r => r.2.1) (Option.some.inj (first.symm.trans expected))
    dsimp only at equal
    rw [equal] at tail
    exact ih (fun i member => onlyArgs i (List.mem_cons_of_mem _ member)) tail

private theorem pair_register_prelude {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (pairs : List (Reg × Reg)) {ρ ρ1 ρ2 : Nat → CV} {w w' t t' : Arm.ArmState}
    (registers : ∀ p ∈ pairs,regVal w p.2 = regVal w' p.2)
    (first : seqRun (csem F fc X) (entryPrelude pairs #[]).toList ρ w = some (.fall ρ1 t))
    (second : seqRun (csem F fc X) (entryPrelude pairs #[]).toList ρ w' = some (.fall ρ2 t')) :
    ρ2 = ρ1 ∧ seqRun (pairSem (csem F fc X)) (entryPrelude pairs #[]).toList ρ (w,w') =
      some (.fall ρ1 (w,w')) := by
  have members : ∀ i ∈ (entryPrelude pairs #[]).toList,i = .args pairs := by
    unfold entryPrelude
    split <;> simp
  have onlyArgs : ∀ i ∈ (entryPrelude pairs #[]).toList,∃ ds,i = .args ds :=
    fun i member => ⟨pairs,members i member⟩
  have firstWorld := register_run_world onlyArgs first
  have secondWorld := register_run_world onlyArgs second
  subst t
  subst t'
  let R := fun a b : Arm.ArmState => ∀ p ∈ pairs,regVal a p.2 = regVal b p.2
  have step : ∀ i ∈ (entryPrelude pairs #[]).toList,∀ us a b outs a' ctl outs' b' ctl',
      R a b → csem F fc X i us a = some (outs,a',ctl) → csem F fc X i us b = some (outs',b',ctl') →
      outs = outs' ∧ ctl = ctl' ∧ R a' b' := by
    intro i member us a b outs a' ctl outs' b' ctl' related ran other
    rw [members i member] at ran other
    change some (pairs.map (fun p => regVal a p.2),a,.next) = some (outs,a',ctl) at ran
    change some (pairs.map (fun p => regVal b p.2),b,.next) = some (outs',b',ctl') at other
    obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ran)
    obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj (Option.some.inj other)
    refine ⟨?_,rfl,related⟩
    exact List.map_congr_left related
  obtain ⟨otherEnd,equal,paired,related⟩ := pair_fall (fun _ _ _ _ h => h) step registers first second
  obtain ⟨file,world⟩ := SeqEnd.fall.inj equal
  rw [← world] at paired
  exact ⟨file,paired⟩

/-- Pair the actual filtered register-only ABI prelude. Original source rows
identify the copied ABI arguments, so the original register-equality premise
supplies exact copied values. Both executions use one proof-internal virtual file. -/
theorem mapped_entry_register_prelude_paired_frame {f : Clif.Function} {ctx : Ctx}
    (inv : MappedCtxInv f ctx) {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} {b : Clif.Block}
    (entered : SourceEntry f args fr) (ssa : (valueDefs f).Nodup) (block : f.blocks[0]? = some b)
    {locs : List ArgLoc} {stack : Nat} (locations : sigArgLocs f.sig = .ok (locs,stack))
    {bytes : List Nat} (sizes : sigParamBytes f.sig = .ok bytes)
    {uses : Array UseState} {rows : List MappedEntryRow}
    (mapped : mappedEntryRows ctx uses ((b.params.zip locs).zip bytes) = .ok rows)
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    {ρ : Nat → CV} {w w' : Arm.ArmState} (held : ValuesHeld (fun _ => True) ctx fr ρ)
    (memory : MRP Γ f c D fr.slots cm (w,w'))
    (arguments : ArgsAtEntry Γ.F f.sig args w) (otherArguments : ArgsAtEntry Γ.F f.sig args w')
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w' pin = regVal w pin) :
    ∃ ρ',seqRun (pairSem (csem Γ.F fc X))
      (entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows)).toList ρ (w,w') =
        some (.fall ρ' (w,w')) ∧ ValuesHeld (fun _ => True) ctx fr ρ' := by
  have rowMember : ∀ row ∈ rows,row.input ∈ (b.params.zip locs).zip bytes := by
    intro row member
    exact (mappedEntryRows_spec mapped).1.subset (List.mem_map.mpr ⟨row,member,rfl⟩)
  have rowRegister : ∀ row ∈ rows,∃ pin,row.input.1.2 = .reg pin := by
    intro row member
    have location := (List.of_mem_zip (List.of_mem_zip (rowMember row member)).1).2
    apply registerOnly
    simpa only [locsOf,locations] using location
  have emptyLoads : mappedEntryLoads rows = #[] := by
    unfold mappedEntryLoads
    change (List.filterMap _ rows).toArray = [].toArray
    apply congrArg List.toArray
    apply List.filterMap_eq_nil_iff.mpr
    intro row member
    obtain ⟨pin,loc⟩ := rowRegister row member
    simp only [loc]
  have copied : ∀ p ∈ mappedEntryPairs rows,regVal w p.2 = regVal w' p.2 := by
    intro p member
    obtain ⟨row,present,copy⟩ := List.mem_filterMap.mp member
    obtain ⟨pin,loc⟩ := rowRegister row present
    rw [loc] at copy
    cases copy
    obtain ⟨v,read⟩ := entered_source_row_value_frame entered ssa block (rowMember row present)
    have located := (entered_source_abi_row_frame entered ssa block locations sizes (rowMember row present) read).1
    exact (registers pin v (by simpa only [loc] using located)).symm
  obtain ⟨left,right,worlds⟩ := memory
  obtain ⟨ρ1,t,first,memory1,values,same⟩ := mapped_entry_prelude_preserves_frame inv entered ssa block locations sizes mapped
    (driverSem_csem Γ.F fc X) (memRefines_csem Γ.F fc X slot symbols) (mrStable_relW Γ f c) held left arguments
  obtain ⟨ρ2,t',second,memory2,otherValues,otherSame⟩ := mapped_entry_prelude_preserves_frame inv entered ssa block locations sizes mapped
    (driverSem_csem Γ.F fc X) (memRefines_csem Γ.F fc X slot symbols) (mrStable_relW Γ f c) held right otherArguments
  rw [emptyLoads] at first second ⊢
  obtain ⟨file,paired⟩ := pair_register_prelude _ copied first second
  exact ⟨ρ1,paired,values⟩

end E2E.StockMemory
