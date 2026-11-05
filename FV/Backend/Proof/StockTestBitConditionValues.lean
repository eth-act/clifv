import FV.Backend.Proof.StockTestBitSelection

/-! Branches on a one-bit test: source values and the actual branch (#140, CB-13).

`TestBitCondMetadata` is the context metadata of a `tbnz` condition (`TestBitMetadata`) or a
`tbz` condition (`TestBitZeroMetadata`). The source value of the condition is a bit of `x`
(`test_bit_truth`, `test_bit_zero_truth`, by `DFGCons`), and one `tbnz`/`tbz` on the resolved
register of `x` takes the branch of that bit (`test_bit_resolved`). In the actual core
(`ConditionalBodySpec.test_bit_origin`) the branch emission is exactly that instruction on the
register of `x`, the two labels are the successors of the block, `x` is demanded and no register
is allocated or defined. So the retained `tbnz`/`tbz` stops at its own index on the edge of the
source truth with the guarded post-frame and unchanged registers
(`test_bit_branch_values_last`). -/

namespace Backend.Stock.Proof.TestBitBranch
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000

/-- The source value of a one-bit test `c = band x k`, `k = iconst imm`: `x` has the type of
the `band`, and `c` is true exactly when bit `bit` of `x` is set. -/
theorem test_bit_truth {ctx : Ctx} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c x k : Nat} {ty ty' : Clif.Ty} {imm : BitVec ty'.width} {t : CTy} {bit : Nat}
    (originC : ctx.defClif? c = some (.binary .band ty x k))
    (originK : ctx.defClif? k = some (.iconst ty' imm)) (he : eTy ty' = true)
    (typeX : ctx.valueType? x = some t) (fits : t.bits ≤ 64)
    (bitEq : tcbc t (u64 (imm64OfIconst ty' imm)) = some bit)
    {value : Clif.Val} (read : fr.regs c = some value) :
    ∃ u : BitVec ty.width,fr.regs x = some ⟨ty,u⟩ ∧ bit < ty.width ∧ ty.width ≤ 64 ∧
      Clif.Sem.truthy value.bits = u.getLsbD bit := by
  obtain ⟨j1,info1,defC,foundC,clifC⟩ := cmp_defClif_inv originC
  obtain ⟨j2,info2,defK,foundK,clifK⟩ := cmp_defClif_inv originK
  obtain ⟨vals,evaluated,written⟩ := dfg.1 c j1 info1 _ value defC foundC clifC rfl read
  obtain ⟨u,v,getX,getK,rfl⟩ := evalInst_binary_inv rfl (evaluated default)
  have same := lookup_zip_single written
  subst same
  have constant := iconst_val dfg defK foundK clifK (getAs_ok getK)
  cases constant
  have readX := getAs_ok getX
  have typed := dfg.2 x t _ typeX readX
  subst typed
  obtain ⟨power,below⟩ := tcbc_spec bitEq
  rw [ofClif_bits_ctl] at below fits
  rw [u64_iconst he] at power
  refine ⟨u,readX,below,fits,?_⟩
  exact truthy_and_pow u _ bit below power

/-- The source value of a zero test of a one-bit mask `c = icmp eq y z`, `y = band x k`,
`k = iconst imm`, `z = iconst 0`: `c` is true exactly when bit `bit` of `x` is clear. -/
theorem test_bit_zero_truth {ctx : Ctx} {fr : Clif.Frame} (dfg : DFGCons ctx fr)
    {c y z x k : Nat} {tyc ty ty' ty0 : Clif.Ty} {imm : BitVec ty'.width} {imm0 : BitVec ty0.width}
    {t : CTy} {bit : Nat}
    (originC : ctx.defClif? c = some (.icmp .eq tyc y z))
    (originY : ctx.defClif? y = some (.binary .band ty x k))
    (originK : ctx.defClif? k = some (.iconst ty' imm)) (he : eTy ty' = true)
    (originZ : ctx.defClif? z = some (.iconst ty0 imm0)) (zero : imm0 = 0)
    (typeX : ctx.valueType? x = some t) (fits : t.bits ≤ 64)
    (bitEq : tcbc t (u64 (imm64OfIconst ty' imm)) = some bit)
    {value : Clif.Val} (read : fr.regs c = some value) :
    ∃ u : BitVec ty.width,fr.regs x = some ⟨ty,u⟩ ∧ bit < ty.width ∧ ty.width ≤ 64 ∧
      Clif.Sem.truthy value.bits = !u.getLsbD bit := by
  obtain ⟨j0,info0,defC,foundC,clifC⟩ := cmp_defClif_inv originC
  obtain ⟨j3,info3,defZ,foundZ,clifZ⟩ := cmp_defClif_inv originZ
  obtain ⟨vals,evaluated,written⟩ := dfg.1 c j0 info0 _ value defC foundC clifC rfl read
  obtain ⟨a,b,getY,getZ,rfl,_⟩ := evalInst_icmp_ok (evaluated default)
  have same := lookup_zip_single written
  subst same
  have constant := iconst_val dfg defZ foundZ clifZ (getAs_ok getZ)
  cases constant
  obtain ⟨u,readX,below,width,truth⟩ := test_bit_truth dfg originY originK he typeX fits bitEq (getAs_ok getY)
  refine ⟨u,readX,below,width,?_⟩
  simp only at truth
  rw [← truth]
  change Clif.Sem.truthy (Clif.Sem.bool8 (Clif.Sem.intcc .eq a b)) = !Clif.Sem.truthy a
  rw [truthy_bool8,zero]
  simp only [Clif.Sem.intcc,Clif.Sem.truthy,bne,Bool.not_not]

/-- One `tbnz`/`tbz` on a resolved register stops at its own index with the branch of the tested
bit, keeping every register. -/
theorem test_bit_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (zero : Bool) {aliases : Array (Option Nat)} {ρ : Nat → CV} {world : Arm.ArmState}
    {yes no : Label} {key bit : Nat} {w : Nat} {u : BitVec w} (below : bit < w) (width : w ≤ 64)
    (holds : (ρ (aliasNum aliases key)).setWidth w = u) :
    ∃ endWorld,seqRun isem [(MInst.testBitAndBranch (if zero then .z else .nz) yes no (.vreg key .int) bit).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] ρ world =
      some (.stop 0 (.testBitAndBranch (if zero then .z else .nz) yes no (.vreg (aliasNum aliases key) .int) bit)
        #[⟨aliasNum aliases key,.int,.use,.early,.reg⟩] ρ world [] endWorld
        (.goto (if u.getLsbD bit != zero then 0 else 1))) ∧ SameWorld F endWorld world := by
  have mapped : (MInst.testBitAndBranch (if zero then .z else .nz) yes no (.vreg key .int) bit).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .testBitAndBranch (if zero then .z else .nz) yes no (.vreg (aliasNum aliases key) .int) bit := by
    simp only [MInst.mapRegs,resolve_vreg]
    rfl
  rw [mapped]
  have spec : ispec (.testBitAndBranch (if zero then .z else .nz) yes no (.vreg (aliasNum aliases key) .int) bit)
      [ρ (aliasNum aliases key)] world =
      some ([],world,.goto (if u.getLsbD bit != zero then 0 else 1)) := by
    simp only [ispec,getLsbD_lo64 (ρ (aliasNum aliases key)) below width,holds]
    cases zero <;> cases u.getLsbD bit <;> rfl
  exact seqRun_one_stop refines (operands_tbb _ yes no _ bit) (ρ := ρ) (by simp) spec rfl

end Backend.Stock.Proof.TestBitBranch

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 Backend.Stock.Proof.TestBitBranch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Context metadata of a branch condition on one bit: a `tbnz` condition or a `tbz`
condition. -/
def TestBitCondMetadata (ctx : Ctx) (c : Nat) : Prop :=
  TestBitMetadata ctx c ∨ TestBitZeroMetadata ctx c

/-- The actual branch of a one-bit condition in the core of `spec`: one `tbnz` (`zero = false`)
or `tbz` (`zero = true`) on the register of `x` with the successor labels; it marks `x`
demanded, allocates no register, and the source value of the condition is bit `bit` of `x`. -/
theorem ConditionalBodySpec.test_bit_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (condition : TestBitCondMetadata result.ctx c) :
    ∃ (zero : Bool) (x bit n : Nat) (yesLabel noLabel : Label),
      result.order.successors[label]!.toList = [yesLabel,noLabel] ∧
      spec.core.scan.ctx.valueReg? x = some (.vreg n .int) ∧
      spec.origin.emission.code.toList =
        [.testBitAndBranch (if zero then .z else .nz) yesLabel noLabel (.vreg n .int) bit] ∧
      spec.origin.emission.state.base.nextVreg = spec.input.base.nextVreg ∧
      spec.origin.emission.state.demand = (spec.input.mark x).demand ∧
      ∀ (fr : Clif.Frame),DFGCons spec.core.scan.ctx fr → ∀ (value : Clif.Val),fr.regs c = some value →
        ∃ (ty : Clif.Ty) (u : BitVec ty.width),fr.regs x = some ⟨ty,u⟩ ∧ bit < ty.width ∧ ty.width ≤ 64 ∧
          Clif.Sem.truthy value.bits = (u.getLsbD bit != zero) := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  obtain ⟨_,slot⟩ := spec.terminator_slot block termShape
  have named : Stock.runTerm spec.core.scan.ctx "lower_branch"
      [.inst (spec.ranges[bi]!.2-1),.labels result.order.successors[label]!.toList]
      {spec.input with current := some (spec.ranges[bi]!.2-1),color := none,base.emitted := #[]} =
      .ok (some spec.origin.out,spec.origin.emission.state,spec.origin.trace) := by
    simpa only [ctxEq] using spec.origin.call
  have emitted := spec.origin.emitted
  rcases condition with ⟨ty,x,k,ty',imm,t,bit,originC,originK,typeX,bitEq⟩ |
    ⟨tyc,y,z,ty0,imm0,originC,⟨ty,x,k,ty',imm,t,bit,originY,originK,typeX,bitEq⟩,originZ,zero⟩
  · have originCHere := spec.defClif_here block originC
    have originKHere := spec.defClif_here block originK
    have typeXHere : spec.core.scan.ctx.valueType? x = some t := by rw [ctxEq]; exact typeX
    have he := iconst_accepted inv originKHere
    have fits := value_type_fits inv typeXHere
    obtain ⟨yesLabel,noLabel,r,labels,mapped,_,state⟩ :=
      test_bit_named_code inv slot originCHere originKHere typeXHere bitEq named
    obtain ⟨n,rfl⟩ := inv.valueReg x r mapped
    refine ⟨false,x,bit,n,yesLabel,noLabel,labels,mapped,?_,?_,?_,?_⟩
    · rw [emitted,state]
      rfl
    · rw [state]
      rfl
    · rw [state]
      rfl
    · intro fr dfg value read
      obtain ⟨u,readX,below,width,truth⟩ := test_bit_truth dfg originCHere originKHere he typeXHere fits bitEq read
      refine ⟨ty,u,readX,below,width,?_⟩
      simpa only [Bool.bne_false] using truth
  · have originCHere := spec.defClif_here block originC
    have originYHere := spec.defClif_here block originY
    have originKHere := spec.defClif_here block originK
    have originZHere := spec.defClif_here block originZ
    have typeXHere : spec.core.scan.ctx.valueType? x = some t := by rw [ctxEq]; exact typeX
    have he := iconst_accepted inv originKHere
    have fits := value_type_fits inv typeXHere
    obtain ⟨yesLabel,noLabel,r,labels,mapped,_,state⟩ :=
      test_bit_zero_named_code inv slot originCHere originYHere originKHere originZHere zero typeXHere bitEq named
    obtain ⟨n,rfl⟩ := inv.valueReg x r mapped
    refine ⟨true,x,bit,n,yesLabel,noLabel,labels,mapped,?_,?_,?_,?_⟩
    · rw [emitted,state]
      rfl
    · rw [state]
      rfl
    · rw [state]
      rfl
    · intro fr dfg value read
      obtain ⟨u,readX,below,width,truth⟩ :=
        test_bit_zero_truth dfg originCHere originYHere originKHere he originZHere zero typeXHere fits bitEq read
      refine ⟨ty,u,readX,below,width,?_⟩
      simpa only [Bool.bne_true] using truth

/-- The real emission of a branch on a one-bit condition defines no register. -/
theorem ConditionalBodySpec.test_bit_no_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (condition : TestBitCondMetadata result.ctx c) :
    ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
  obtain ⟨zero,x,bit,n,yesLabel,noLabel,_,_,code,_⟩ := spec.test_bit_origin run scope block termShape condition
  intro m member
  rw [code] at member
  simp only [List.mem_singleton] at member
  subst member
  rfl

/-- The real emission of a branch on a one-bit condition is exactly one instruction. -/
theorem ConditionalBodySpec.test_bit_emission_size {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (condition : TestBitCondMetadata result.ctx c) :
    spec.origin.emission.code.size = 1 := by
  obtain ⟨zero,x,bit,n,yesLabel,noLabel,_,_,code,_⟩ := spec.test_bit_origin run scope block termShape condition
  rw [← Array.length_toList,code]
  rfl

/-- **The actual `tbnz`/`tbz` of a one-bit condition stops at its own index on the edge of the
source truth, with the guarded post-frame.** The register of `x` holds `x` because the branch
demands it, and the instruction defines no register, so the registers and the guarded relation
are unchanged. -/
theorem ConditionalBodySpec.test_bit_branch_values_last {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (condition : TestBitCondMetadata result.ctx c)
    {fr : Clif.Frame} {cm : Clif.Mem} {cty : Clif.Ty} {test : BitVec cty.width}
    (getC : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs c cty = .ok test)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ world) :
    ∃ index inst ops regs prefixWorld endWorld,
      seqRun isem (spec.origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) ∧
      index+1 = spec.origin.emission.code.size ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
        (b.body.length,fr,cm) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  obtain ⟨zero,x,bit,n,yesLabel,noLabel,labels,mapped,code,_,demandEq,truth⟩ :=
    spec.test_bit_origin run scope block termShape condition
  obtain ⟨ty,u,readX,below,width,truthEq⟩ := truth _ post.2.1 _ (getAs_ok getC)
  have available := restrict_regs_isSome (by rw [readX]; rfl)
  rw [restrict_regs_of_mem available] at readX
  obtain ⟨emission,afterEdges,retained,branchCall,outgoing,scanInput,scanCtx,branchScan,combined⟩ :=
    conditional_core_calls termShape spec.coreRun
  have same : emission = spec.origin.emission := Option.some.inj (retained.symm.trans spec.origin.retained)
  rw [same] at outgoing
  obtain ⟨_,edgeExtent⟩ := outgoing_base_extent outgoing
  have scanExtent : spec.core.scan.input.demand.size = spec.origin.emission.state.demand.size := by
    rw [scanInput]; exact edgeExtent
  have demandSize : spec.origin.emission.state.demand.size = spec.input.demand.size := by
    rw [demandEq]
    exact Array.size_modify
  have termRecorded : spec.term ∈ spec.core.scan.output.records := by rw [spec.split.records]; simp
  have bound : x < spec.input.demand.size := by
    have actual := (Extent.lower_mapped_demand_bounds run scope spec.events termRecorded mapped).1
    rw [spec.split.termInput,scanExtent,demandSize] at actual
    exact actual
  have marked : Demanded spec.origin.emission.state x := by
    unfold Demanded
    rw [demandEq,(mark_demand spec.input x bound).1]
    omega
  have termDemand := (Control.stock_branch_scan_body_code spec.split spec.origin.branchScan).2
  have mono := conditional_core_emission_demand termShape spec.coreRun spec.origin x
  have demanded : Demanded spec.term.output.state x := by
    unfold Demanded at marked ⊢
    rw [termDemand,spec.split.termInput]
    omega
  obtain ⟨m,mappedM,holds⟩ := post.2.2.2 x ⟨demanded,available⟩ _ readX
  rw [mapped] at mappedM
  cases mappedM
  obtain ⟨endWorld,machine,sameWorld⟩ := test_bit_resolved refines zero (aliases := result.final.alias)
    (ρ := ρ) (world := world) (yes := yesLabel) (no := noLabel) below width holds
  have truthTest : (test != 0) = (u.getLsbD bit != zero) := truthEq
  refine ⟨0,.testBitAndBranch (if zero then .z else .nz) yesLabel noLabel
    (.vreg (aliasNum result.final.alias n) .int) bit,#[⟨aliasNum result.final.alias n,.int,.use,.early,.reg⟩],
    ρ,world,endWorld,?_,?_,?_,?_,rfl⟩
  · rw [code,truthTest]
    exact machine
  · rw [← Array.length_toList,code]
    rfl
  · exact ⟨post.1,post.2.1,stable _ _ _ _ (SameWorld.nf sameWorld) post.2.2.1,post.2.2.2⟩
  · exact labels.symm

end Backend.Stock.Proof.ConditionalValues
