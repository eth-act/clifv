import FV.Backend.StockVoidCallNICheck
import FV.E2E.StockVoidCallDomain
import FV.E2E.PairDriver
import FV.E2E.ABIReadOnlyRealize

namespace Backend.Stock.VoidCall.NI
set_option autoImplicit false
set_option Elab.async false

/-- Actual checked code retains a finite read boundary at every non-call instruction. -/
theorem checked_instruction {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) {b k : Nat} {vb : VBlock} {i : MInst}
    (block : vc.blocks[b]? = some vb) (inst : vb.insts[k]? = some i) :
    instruction sig b k i = true := by
  have bm : (vb,b) ∈ vc.blocks.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using block)
  have im : (i,k) ∈ vb.insts.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using inst)
  exact List.all_eq_true.mp (List.all_eq_true.mp checked (vb,b) bm) (i,k) im

/-- The internal class derives absence of try-calls from actual code checks. -/
theorem noTryCall_of_codeCheck {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) : vc.hasTryCall = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  simp only [VCode.hasTryCall,Array.any_eq_true] at present
  obtain ⟨b,hb,k,hk,flag⟩ := present
  generalize atInst : vc.blocks[b].insts[k] = i at flag
  cases i <;> try cases flag
  rename_i info ti
  have found := checked_instruction checked
    (Array.getElem?_eq_some_iff.mpr ⟨hb,rfl⟩)
    (Array.getElem?_eq_some_iff.mpr ⟨hk,atInst⟩)
  change false = true at found
  cases found

end Backend.Stock.VoidCall.NI

namespace E2E.ABIReadOnly
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Exact original argument agreement transfers a finite ABI prelude, including stack reads. -/
theorem seqRun_fall_transport {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {F Z : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w w' : Arm.ArmState}
    (worlds : SameWorld Z w w')
    (registers : ∀ r v,(.reg r,v) ∈ (locsOf sig).zip args → regVal w' r = regVal w r)
    (stack : ∀ (off : Nat) (v : Clif.Val),(.stack off,v) ∈ (locsOf sig).zip args → ∀ j < v.ty.bytes,
      w'.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j) =
      w.mem (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16+(off : Int)) + BitVec.ofNat 64 j))
    {ms : List MInst} {b start : Nat}
    (checked : ∀ j i,ms[j]? = some i → Backend.ABIReadOnly.instruction sig b (start+j) i = true)
    {ρ ρ' : Nat → CV} {final : Arm.ArmState}
    (run : seqRun (sem F ctx X) ms ρ w = some (.fall ρ' final)) :
    final = w ∧ seqRun (sem F ctx X) ms ρ w' = some (.fall ρ' w') := by
  induction ms generalizing start ρ with
  | nil =>
    obtain ⟨rfl,rfl⟩ := SeqEnd.fall.inj (Option.some.inj run)
    exact ⟨rfl,rfl⟩
  | cons i rest ih =>
    have head := checked 0 i (by simp)
    simp only [Nat.add_zero] at head
    obtain ⟨ops,outs,middle,operands,first,arity,tail⟩ := seqRun_cons_fall run
    have same := step_world head first
    subst middle
    have transferred := step_transport types head worlds registers stack first
    have remaining : ∀ j item,rest[j]? = some item →
        Backend.ABIReadOnly.instruction sig b (start+1+j) item = true := by
      intro j item found
      have next := checked (j+1) item (by simpa using found)
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using next
    obtain ⟨finalWorld,other⟩ := ih remaining tail
    refine ⟨finalWorld,?_⟩
    simp only [seqRun,operands,transferred,arity,↓reduceIte,other,Option.map_some,SeqEnd.succ]

end E2E.ABIReadOnly


namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm Isle.Aarch64.program branchArgs emitBranch collectOutgoing scanBlock

private theorem entryPrelude_noCall (pairs : List (Reg × Reg)) (rows : List MappedEntryRow) :
    ∀ i ∈ (entryPrelude pairs (mappedEntryLoads rows)).toList,∀ info,i ≠ .call info := by
  have loads : ∀ i ∈ (mappedEntryLoads rows).toList,∀ info,i ≠ .call info := by
    intro i member info
    simp only [mappedEntryLoads,List.toList_toArray,List.mem_filterMap] at member
    obtain ⟨row,_,found⟩ := member
    cases loc : row.input.1.2 with
    | reg pin => simp only [loc] at found; cases found
    | stack off =>
      simp only [loc,Option.some.injEq] at found
      subst i
      intro impossible
      cases impossible
  intro i member info
  unfold entryPrelude at member
  split at member
  · have selected : i = .args pairs ∨ i ∈ (mappedEntryLoads rows).toList := by simpa using member
    rcases selected with rfl | member
    · intro impossible; cases impossible
    · exact loads i member info
  · exact loads i member info

private theorem core_scan_suffix_void_call {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    ∃ after, core.code = core.scan.output.code ++ after := by
  unfold lowerBlockCore at run
  dsimp only at run
  split at run
  all_goals
    obtain ⟨branch,branchRun,rest⟩ := Except.bind_ok run
    obtain ⟨pair,edgeRun,rest⟩ := Except.bind_ok rest
    rcases pair with ⟨next,outgoing⟩
    obtain ⟨scan,scanRun,rest⟩ := Except.bind_ok rest
    cases rest
    exact ⟨_,rfl⟩

/-- The actual entry prelude contains ABI copies and loads, with no hidden calls. -/
theorem stock_lower_entry_prelude_refines_nocall_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ (event : BlockScanEvent) (block : VBlock) (prelude body : Array MInst)
      (ρ' : Nat → CV) (w' : Arm.ArmState),
      event ∈ result.blockScans.toList ∧ event.block = 0 ∧
      result.code.blocks[0]? = some block ∧ block.insts = prelude ++ body ∧
      seqRun isem prelude.toList (entrySeed event.ctx fr) w = some (.fall ρ' w') ∧
      MR fr.slots cm w' ∧ ValuesHeld (fun _ => True) event.ctx fr ρ' ∧ SameWorld F w' w ∧
      (∀ i ∈ prelude.toList,∀ info,i ≠ .call info) ∧
      ∃ after, body = event.output.code.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ after := by
  obtain ⟨ranges,bytes,before,data,core,raw,block,sizes,build,coreRun,assembled,events,
    atBlock,blockCode⟩ := stock_lower_entry_assembly run scope
  have inv := buildCtx_mappedInv scope build
  have entryFacts := entered
  obtain ⟨b,regs,entry,argTypes,paramTypes,set,frame⟩ := entryFacts
  have sourceBlock : f.blocks[0]? = some b := by
    simpa only [Clif.Function.entry?,List.head?_eq_getElem?] using entry
  have blockValue : f.blocks[0]! = b := by
    rw [List.getElem!_eq_getElem?_getD,sourceBlock]
    rfl
  rw [blockValue] at assembled
  obtain ⟨locs,stack,rows,locations,mapped,ordered,lookups,rawCode⟩ :=
    assemble_entry_source_rows assembled
  let prelude := entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows)
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have fixed : prelude.map (·.mapRegs resolve) = prelude := by
    apply mapped_entry_prelude_fixed resolve
    intro row member
    have original : row.input ∈ (b.params.zip locs).zip bytes :=
      ordered.subset (List.mem_map.mpr ⟨row,member,rfl⟩)
    have parameter : row.input.1.1.1 ∈ b.params.map (·.1) :=
      List.mem_map.mpr ⟨row.input.1.1,(List.of_mem_zip (List.of_mem_zip original).1).1,rfl⟩
    obtain ⟨rowReg,rowMap⟩ := mapped_entry_reg inv mapped member
    have alias := stock_lower_parameter_resolves run dominated.ssa sourceBlock parameter rowMap
    rw [rowReg]
    change Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
      (.vreg (entryRowKey row) .int) = .vreg (entryRowKey row) .int
    rw [resolve_vreg]
    change Reg.vreg (aliasNum result.final.alias (entryRowKey row)) .int = _
    rw [alias]
  have maps := (stock_lower_record_context run scope events).2.1
  have held : ValuesHeld (fun _ => True) result.ctx fr (entrySeed core.scan.ctx fr) := by
    intro x _ v found
    obtain ⟨key,mapped,value⟩ := entrySeed_entered_values_frame run scope dominated events entered x trivial v found
    exact ⟨key,by rwa [maps] at mapped,value⟩
  obtain ⟨ρ',w',execution,mem,values,same⟩ := mapped_entry_prelude_preserves_frame inv entered
    dominated.ssa sourceBlock locations sizes mapped driver memorySem stable held memory arguments
  refine ⟨core.scan,block,prelude,core.code.map (·.mapRegs resolve),ρ',w',events,
    (stock_lowerBlockCore_scanOrigin coreRun).2.2.1,atBlock,?_,execution,mem,?_,same,?_,?_⟩
  · rw [blockCode,rawCode]
    change (prelude ++ core.code).map (·.mapRegs resolve) = _
    rw [Array.map_append,fixed]
  · intro x _ v found
    obtain ⟨key,mapped,value⟩ := values x trivial v found
    exact ⟨key,by rwa [← maps] at mapped,value⟩
  · exact entryPrelude_noCall _ _
  · obtain ⟨after,pieces⟩ := core_scan_suffix_void_call coreRun
    exact ⟨after.map (·.mapRegs resolve),by rw [pieces,Array.map_append]⟩

end Backend.Stock.Proof

namespace Backend.Stock.VoidCall.NI
set_option autoImplicit false
set_option Elab.async false

/-- Checked original code and actual prelude shape derive every finite read obligation. -/
theorem prelude_read_checks {sig : Clif.Signature} {vc : VCode}
    (checked : codeCheck sig vc = true) {b : Nat} {block : VBlock}
    (placed : vc.blocks[b]? = some block) {prelude body : Array MInst}
    (pieces : block.insts = prelude ++ body)
    (noCalls : ∀ i ∈ prelude.toList,∀ info,i ≠ .call info) :
    ∀ j i,prelude.toList[j]? = some i → Backend.ABIReadOnly.instruction sig b j i = true := by
  intro j i found
  have element : prelude[j]? = some i := by simpa using found
  have bound := (Array.getElem?_eq_some_iff.mp element).1
  have atInst : block.insts[j]? = some i := by
    rw [pieces,Array.getElem?_append_left bound]
    exact element
  have admitted := checked_instruction checked placed atInst
  cases i <;> try exact admitted
  rename_i info
  exact False.elim (noCalls _ (List.mem_of_getElem? found) info rfl)

end Backend.Stock.VoidCall.NI

namespace E2E.ABIReadOnly
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
set_option autoImplicit false
set_option Elab.async false

/-- Realize the exact finite ABI prelude under the existing cleanup value semantics. -/
theorem seqRun_fall_realize {sig : Clif.Signature} {args : List Clif.Val}
    (types : args.map (·.ty) = sig.params.map (·.ty))
    {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {w t : Arm.ArmState}
    (arguments : ArgsAtEntry F sig args w) (worlds : SameWorld F t w)
    {ms : List MInst} {b start : Nat}
    (checked : ∀ j i,ms[j]? = some i → Backend.ABIReadOnly.instruction sig b (start+j) i = true)
    (entry : start = 0 → t = w)
    {ρ ρ' : Nat → CV} {final : Arm.ArmState}
    (run : seqRun (sem F ctx X) ms ρ w = some (.fall ρ' final)) :
    final = w ∧ ∃ t',seqRun (valueSem F ctx X) ms ρ t = some (.fall ρ' t') ∧ SameWorld F t' w := by
  induction ms generalizing start ρ t with
  | nil =>
    obtain ⟨rfl,rfl⟩ := SeqEnd.fall.inj (Option.some.inj run)
    exact ⟨rfl,t,rfl,worlds⟩
  | cons i rest ih =>
    have head := checked 0 i (by simp)
    simp only [Nat.add_zero] at head
    obtain ⟨ops,outs,middle,operands,first,arity,tail⟩ := seqRun_cons_fall run
    have fixed := step_world head first
    subst middle
    obtain ⟨t1,concrete,related⟩ := step_realize types head arguments worlds entry first
    have remaining : ∀ j item,rest[j]? = some item →
        Backend.ABIReadOnly.instruction sig b (start+1+j) item = true := by
      intro j item found
      have next := checked (j+1) item (by simpa using found)
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using next
    obtain ⟨finalWorld,t',restRun,restWorld⟩ := ih related remaining (by omega) tail
    refine ⟨finalWorld,t',?_,restWorld⟩
    simp only [seqRun,operands,concrete,arity,↓reduceIte,restRun,Option.map_some,SeqEnd.succ]

end E2E.ABIReadOnly

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original source and NI contracts pair the actual void call and preserve its complete memory relation. -/
theorem void_call_pair {Γ : Rel} {f : Clif.Function} {c : BitVec 64}
    {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature} {X : ExtSem}
    (calls : XCallsOk env exts (RelW Γ f c) X)
    (ni : XNI Γ.F Γ.syms exts sigs c (CallLg env exts sigs) X)
    {ext : Clif.ExtFunc} (member : ext ∈ exts) (void : ext.sig.returns = [])
    {g : List Clif.Val → Clif.Mem → Clif.Outcome} (found : env.extern ext.name = some g)
    {vals : List Clif.Val} {cm after : Clif.Mem} (returned : g vals cm = .returned [] after)
    {slots : List (Clif.SlotId × Nat)} {uses : List CV} {w w' : Arm.ArmState}
    (memory : RelW Γ f c slots cm w) (memory' : RelW Γ f c slots cm w')
    (arguments : ArgsAt ext.sig vals uses w) (arguments' : ArgsAt ext.sig vals uses w')
    {Z : BitVec 64 → Prop} (covers : ∀ a,Γ.F a → Z a) (worlds : SameWorld Z w w') :
    ∃ out out',X.voidCalls.call (some ext.name) uses w = some ([],out) ∧
      X.voidCalls.call (some ext.name) uses w' = some ([],out') ∧
      RelW Γ f c slots after out ∧ RelW Γ f c slots after out' ∧ SameWorld Z out out' := by
  obtain ⟨actual,out,run,_,_,result⟩ := calls ext member g slots cm w (some ext.name) uses uses
    vals [] after found (Or.inl ⟨rfl,rfl⟩) arguments memory returned (by rw [void]; rfl)
  obtain ⟨actual',out',run',_,_,result'⟩ := calls ext member g slots cm w' (some ext.name) uses uses
    vals [] after found (Or.inl ⟨rfl,rfl⟩) arguments' memory' returned (by rw [void]; rfl)
  have legitimate : CallLg env exts sigs ext.name ext.sig vals cm :=
    ⟨Or.inl ⟨ext,member,rfl,rfl⟩,g,[],after,found,returned⟩
  have paired := ni ext.name ext.sig vals cm uses (some ext.name) uses Z w w' actual out actual' out'
    legitimate (Or.inl ⟨rfl,rfl⟩) covers worlds memory.1.1 memory'.1.1 memory.2.1 memory'.2.1
    (Or.inl ⟨⟨ext,member,rfl,rfl⟩,arguments,arguments'⟩) run run'
  exact ⟨out,out',ExtSem.voidCalls_call run,ExtSem.voidCalls_call run',result,result',paired.2⟩

end E2E
