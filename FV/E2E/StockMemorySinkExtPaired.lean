import FV.E2E.StockMemorySinkExtDomain
import FV.E2E.StockMemoryPairedScan
import FV.E2E.StockMemoryPairedEntryReturn
import FV.Backend.Proof.StockMemoryReadTransport

/-! Paired (noninterference) execution of the sinking load/extension body. Two worlds
that agree outside the frame and the disagreement set run the one machine extending
load to one register file: the load reads only initialized source bytes. Each world
keeps the single-world guarded relation of `stock_sink_extend_return_body`. An atomic
source runs one acquiring load instead, through the guarded `ldar` memory contract. -/
namespace E2E.StockMemory.SinkExtend
open Backend Backend.Stock Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
open Backend.Stock.Memory.SinkExtend Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The terminator record and the body code of a block scan do not depend on the split. -/
theorem split_unique {f : Clif.Function} {event : BlockScanEvent} {b b' : Clif.Block}
    {term term' : ScanRecord} {body body' : BlockScan}
    (split : SourceBodySplit f event b term body) (split' : SourceBodySplit f event b' term' body') :
    term' = term ∧ body'.code = body.code := by
  have records := split'.records.symm.trans split.records
  simp only [List.cons.injEq] at records
  obtain ⟨same,_⟩ := records
  subst same
  refine ⟨rfl,?_⟩
  have code := split'.code.symm.trans split.code
  exact (Array.append_left_inj _).mp code

/-- A successful zero-extending source load and one acquiring load of the same size give
the same output on both related worlds under the guarded memory semantics: the load reads
only initialized source bytes. -/
theorem acquire_source_result_pairR
    {F Rd : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {f : Clif.Function}
    (memorySem : MemRefinesR Rd F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {w w' : Arm.ArmState}
    (memory : MR fr.slots cm w) (other : MR fr.slots cm w') (reads : InitIn Rd cm)
    {op : Clif.LoadOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {p : Nat} {vals : List Clif.Val}
    {bits d r : Nat} {u : CV} (atom : AtomTy (.int bits)) (size : (CTy.int bits).bytes = op.size ty)
    (little : fl.endianness ≠ some .big)
    (pointer : ∀ pv,fr.regs p = some pv → lo64 u = BitVec.ofNat 64 (Clif.effAddr pv 0))
    (source : Clif.evalInst fr cm (.load op ty fl p 0) = .ok (vals,cm')) :
    ∃ out t t',isem (.loadAcquire (.int bits) (.vreg d .int) (.vreg r .int) fl) [u] w =
        some ([out],t,.next) ∧
      isem (.loadAcquire (.int bits) (.vreg d .int) (.vreg r .int) fl) [u] w' = some ([out],t',.next) ∧
      SameWorld F t w ∧ SameWorld F t' w' := by
  obtain ⟨pv,raw,hpv,_,valid,read,_,_⟩ := evalInst_load_inv little source
  have address := pointer pv hpv
  have avoid : Avoids F (CTy.int bits).bytes (lo64 u) := by
    intro k hk
    rw [address,← BitVec.ofNat_add]
    exact (memoryOk.valid _ _ _ _ _ memory valid).2 k (by omega)
  have permitted : ∀ k < (CTy.int bits).bytes,Rd (lo64 u + BitVec.ofNat 64 k) := by
    intro k hk
    rw [address,← BitVec.ofNat_add]
    exact reads _ (valid_sub valid (by omega)) ((readBits_spec read).1 k (by omega))
  obtain ⟨t,executed,same⟩ := memorySem.2.2.2.2.1 (.int bits) d r fl u w atom avoid permitted
  obtain ⟨t',otherRun,otherSame⟩ := memorySem.2.2.2.2.1 (.int bits) d r fl u w' atom avoid permitted
  have equal : Arm.read_mem_bytes (CTy.int bits).bytes (lo64 u) w =
      Arm.read_mem_bytes (CTy.int bits).bytes (lo64 u) w' := by
    have bound := (memoryOk.valid _ _ _ _ _ memory valid).1
    have bits := readBits_getLsbD_eq (s := w) read bound
      (fun k hk b hb => memoryOk.bytes _ _ _ _ b memory (valid_sub valid hk) hb)
    have otherBits := readBits_getLsbD_eq (s := w') read bound
      (fun k hk b hb => memoryOk.bytes _ _ _ _ b other (valid_sub valid hk) hb)
    rw [address,size]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    exact (bits k).symm.trans (otherBits k)
  rw [← equal] at otherRun
  exact ⟨_,t,t',executed,otherRun,same,otherSame⟩

/-- The root's one machine instruction runs to one register file on both related worlds
under the guarded memory semantics, for a plain or an atomic source load. -/
theorem source_load_pairR (src : Source) (kind : Kind) (admits : src.admits kind = true)
    {F Rd : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {f : Clif.Function}
    (memorySem : MemRefinesR Rd F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {fr : Clif.Frame} {cm cm' : Clif.Mem} {w w' : Arm.ArmState}
    (memory : MR fr.slots cm w) (other : MR fr.slots cm w') (reads : InitIn Rd cm)
    {ty : Clif.Ty} {fl : Clif.MemFlags} {p : Nat} {vals : List Clif.Val} {ρ : Nat → CV} {d r : Nat}
    (little : fl.endianness ≠ some .big)
    (pointer : ∀ pv,fr.regs p = some pv → lo64 (ρ r) = BitVec.ofNat 64 (Clif.effAddr pv 0))
    (source : Clif.evalInst fr cm (.load kind.sourceOp ty fl p 0) = .ok (vals,cm')) :
    ∃ ρ' t t',seqRun isem [src.emitted kind (.vreg d .int) r fl] ρ w = some (.fall ρ' t) ∧
      seqRun isem [src.emitted kind (.vreg d .int) r fl] ρ w' = some (.fall ρ' t') := by
  cases src with
  | plain =>
    obtain ⟨_,_,_,executed,otherRun,_,_⟩ := load_source_result_pairR memorySem memoryOk memory other
      reads (aop := kind.loadOp) (d := d) (am := .unsignedOffset (.vreg r .int) 0) (uses := [ρ r])
      (by cases kind <;> decide) (by cases kind <;> rfl) little
      (fun pv hpv => by simp [amodeAddr,pointer pv hpv]) (fun pv hpv => by simp [amodeAddr,pointer pv hpv])
      source
    obtain ⟨ops,opsEq,uses,defs,_⟩ := (load_ops kind.loadOp d (am := .unsignedOffset (.vreg r .int) 0)
      (by intro r' member; exact ⟨_,List.mem_singleton.mp member⟩) fl).ops
    have usesEq : vuses ops ρ = [ρ r] := uses ρ
    rw [← usesEq] at executed otherRun
    exact ⟨_,_,_,seqRun_isem_one opsEq executed (by rw [defs]; rfl),
      seqRun_isem_one opsEq otherRun (by rw [defs]; rfl)⟩
  | acquire =>
    have unsigned : signed kind = false := by simpa [Source.admits] using admits
    obtain ⟨_,_,_,executed,otherRun,_,_⟩ := acquire_source_result_pairR memorySem memoryOk memory other
      reads (bits := (loadTy kind).width) (d := d) (r := r) (u := ρ r)
      (by cases kind <;> simp [AtomTy,loadTy,Clif.Ty.width])
      (by cases kind <;> simp only [signed,Bool.true_eq_false] at unsigned <;> rfl) little pointer source
    exact ⟨_,_,_,seqRun_isem_one (operands_loadAcquire _ d r fl) executed rfl,
      seqRun_isem_one (operands_loadAcquire _ d r fl) otherRun rfl⟩

/-- One body run in two related worlds under the guarded memory semantics, for a plain or
an atomic source load. Both worlds
end with the same register file and keep the guarded relation; memory is unchanged. -/
theorem stock_source_extend_body_pair (src : Source) (kind : Kind) {f : Clif.Function}
    {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : SourceShape src kind f b x y z ty flags)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
      ∀ {Rd : BitVec 64 → Prop} {isemG : Backend.Proof.Sem}
        (_guardedMemory : MemRefinesR Rd F sb syms isemG)
        (_subGuarded : ∀ i us w r,isemG i us w = some r → isem i us w = some r)
        (ρ : Nat → CV) (w w' : Arm.ArmState),InitIn Rd s.2.2 →
        GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
        GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w' →
        ∃ ρ' t t',seqRun isemG (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' t) ∧
          seqRun isemG (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w' =
            some (.fall ρ' t') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' t ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' t' ∧
          s'.2.2 = s.2.2 := by
  obtain ⟨term,extend,load,scanned,step,nreg,a,split,zero,extendInst,loadInst,_,retained,
    _,recorded,emitted,_,mapped,_,stateEq,codeEq,emittedEq,_,demandedX,_⟩ :=
    stock_lower_source_extend_body_facts src kind run scope dominated shape events
  obtain ⟨term',body',split',single⟩ := stock_source_extend_return_body src kind run scope dominated shape
    stable memorySem memoryOk (env := env) (cp := cp) events
  obtain ⟨sameTerm,sameCode⟩ := split_unique split split'
  subst sameTerm
  refine ⟨term',scanned,split,?_⟩
  intro s s' steps Rd isemG guardedMemory subGuarded ρ w w' reads held otherHeld
  have inv := (stock_lower_record_context run scope events).1
  have block : f.blocks[event.block]? = some b := by rw [zero,shape.blocks]; rfl
  have start : blockStart f event.block = 0 := by rw [zero]; simp [blockStart]
  have statement0 : b.body[0]? = some ⟨[y],src.load (loadTy kind) flags x⟩ := by
    simp [shape.body]
  have current0 : load.inst = blockStart f event.block + 0 := by rw [loadInst,start]
  obtain ⟨info0,source0,clif0,results0⟩ := ArithmeticBody.body_source_info run events split statement0
    current0
  have little := source_little src kind inv source0 clif0
  have finalState : event.output.state = extend.output.state := split.state.symm.trans stateEq
  -- the single-world runs and post relations
  obtain ⟨ρ1,t1,run1,post1⟩ := single s s' steps ρ w held
  obtain ⟨ρ2,t2,run2,post2⟩ := single s s' steps ρ w' otherHeld
  rw [sameCode] at run1 run2
  -- the source steps: memory is unchanged and the body equals one extending source load
  have range : (List.range b.body.length).map (blockStart f event.block + ·) = [0,1] := by
    simp [shape.body,start,List.range_succ]
  rw [range] at steps
  obtain ⟨p,fr,cm⟩ := s
  obtain ⟨p',fr',cm'⟩ := s'
  cases steps with
  | cons head0 tail =>
    rename_i s1
    cases tail with
    | cons head1 done =>
      cases done
      obtain ⟨p1,fr1,cm1⟩ := s1
      obtain ⟨at0,_,step0⟩ := head0
      obtain ⟨_,_,step1⟩ := head1
      dsimp only at at0
      rw [start] at at0
      have pZero : p = 0 := by omega
      subst pZero
      obtain ⟨info0',inst0,vals1,regs1,rest0,found0,original0,_,outcome0,written0,frame0⟩ := step0
      cases Option.some.inj (found0.symm.trans (by rw [loadInst] at source0; exact source0))
      cases Option.some.inj (original0.symm.trans clif0)
      have plain0 : Clif.evalInst fr cm (src.load (loadTy kind) flags x) = .ok (vals1,cm1) := by
        cases src <;> simpa only [instOutcome,Source.load] using outcome0
      obtain ⟨⟨v1,rfl⟩,memEq⟩ := source_load_single src little plain0
      subst cm1
      rw [results0] at written0
      simp only [Clif.Regs.setMany_cons,Clif.Regs.setMany_nil,Option.some.injEq] at written0
      subst regs1
      change fr1 = _ at frame0
      have getY : fr1.get y = .ok v1 := by
        rw [frame0]; simp [Clif.Frame.get,Clif.Regs.set_same]
      have statement1 : b.body[1]? = some ⟨[z],.extend (extendOp kind) ty y⟩ := by simp [shape.body]
      have current1 : extend.inst = blockStart f event.block + 1 := by rw [extendInst,start]
      obtain ⟨info1,source1,clif1,_⟩ := ArithmeticBody.body_source_info run events split statement1
        current1
      obtain ⟨info1',inst1,vals2,regs2,rest1,found1,original1,_,outcome1,_,_⟩ := step1
      cases Option.some.inj (found1.symm.trans (by rw [extendInst] at source1; exact source1))
      cases Option.some.inj (original1.symm.trans clif1)
      have plain1 : Clif.evalInst fr1 cm (.extend (extendOp kind) ty y) = .ok (vals2,cm') := by
        simpa only [instOutcome] using outcome1
      obtain ⟨v2,rfl⟩ := extend_single plain1
      obtain ⟨memSame,oneLoad⟩ := source_extend_eval src kind shape.admits plain0 getY plain1
      subst cm'
      -- the guarded paired machine load
      obtain ⟨_,dfg,memory,values⟩ := held
      have otherMemory := otherHeld.2.2.1
      dsimp only at dfg memory values otherMemory
      have required : Demanded event.output.state x ∧
          x ∈ availOf f (availIn f result.ctx) event.block 0 :=
        ⟨by rw [finalState]; exact demandedX,
          stock_lower_record_args_available run scope dominated events block statement0 current0
            source0 clif0 x (by cases src <;> simp [Driver.instArgs,Source.load])⟩
      have restrictedGet : (restrict fr (availOf f (availIn f result.ctx) event.block 0)).get x =
          fr.get x := by
        simp only [Clif.Frame.get,restrict_regs_of_mem required.2]
      have restrictedEval : Clif.evalInst (restrict fr (availOf f (availIn f result.ctx) event.block 0))
          cm (.load kind.sourceOp ty flags x 0) = .ok ([v2],cm) := by
        simpa only [Clif.evalInst,restrictedGet] using oneLoad
      have operands : ValueHeld event.ctx (restrict fr (availOf f (availIn f result.ctx) event.block 0))
          (fun k => ρ (aliasNum result.final.alias k)) x := by
        intro val lookup
        rw [restrict_regs_of_mem required.2] at lookup
        exact values x required val lookup
      have pointerTy := inv.addr64 _ _ _ x source0 clif0 (by cases src <;> rfl)
      have pointer : ∀ pv,(restrict fr (availOf f (availIn f result.ctx) event.block 0)).regs x = some pv →
          lo64 (ρ (aliasNum result.final.alias nreg)) = BitVec.ofNat 64 (Clif.effAddr pv 0) := by
        intro pv hpv
        obtain ⟨m,hm,held⟩ := operands pv hpv
        have equal : m = nreg := by simpa using hm.symm.trans mapped
        subst m
        rw [lo64_of_holds held (pv_i64 dfg pointerTy hpv),effAddr_zero]
      obtain ⟨_,_,_,first,second⟩ := source_load_pairR src kind shape.admits guardedMemory memoryOk
        (fr := restrict fr (availOf f (availIn f result.ctx) event.block 0)) memory otherMemory reads
        (ρ := ρ) (d := extend.input.base.nextVreg) (r := aliasNum result.final.alias nreg)
        little pointer restrictedEval
      -- the resolved body code is that one load
      have aliasBound : result.final.alias.size ≤ extend.input.base.nextVreg := by
        have frontier : (scanState extend.input extend.inst).base.nextVreg = extend.input.base.nextVreg := by
          unfold scanState; dsimp only; split <;> rfl
        simpa only [frontier] using stock_lower_blockScanAliasBounds run event events extend retained
      have fixed : aliasNum result.final.alias extend.input.base.nextVreg =
          extend.input.base.nextVreg := by
        apply chaseF_none
        rw [Array.getElem?_eq_none aliasBound]
        rfl
      have resolved : scanned.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
          [src.emitted kind (.vreg extend.input.base.nextVreg .int)
            (aliasNum result.final.alias nreg) flags] := by
        rw [codeEq,emittedEq]
        cases src
        · change [MInst.load kind.loadOp
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
              (.vreg extend.input.base.nextVreg .int))
            (.unsignedOffset (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
              (.vreg nreg .int)) 0) flags] = _
          rw [resolve_vreg,resolve_vreg]
          change [MInst.load kind.loadOp (.vreg (aliasNum result.final.alias extend.input.base.nextVreg) .int)
            (.unsignedOffset (.vreg (aliasNum result.final.alias nreg) .int) 0) flags] = _
          rw [fixed]
          rfl
        · change [MInst.loadAcquire (.int (loadTy kind).width)
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
              (.vreg extend.input.base.nextVreg .int))
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
              (.vreg nreg .int)) flags] = _
          rw [resolve_vreg,resolve_vreg]
          change [MInst.loadAcquire (.int (loadTy kind).width)
            (.vreg (aliasNum result.final.alias extend.input.base.nextVreg) .int)
            (.vreg (aliasNum result.final.alias nreg) .int) flags] = _
          rw [fixed]
          rfl
      rw [← resolved] at first second
      -- the guarded runs are the single-world runs, so both posts hold at one register file
      have firstBase := seqRun_sub subGuarded _ _ _ _ first
      have secondBase := seqRun_sub subGuarded _ _ _ _ second
      obtain ⟨fileEq,worldEq⟩ := SeqEnd.fall.inj (Option.some.inj (run1.symm.trans firstBase))
      obtain ⟨otherFileEq,otherWorldEq⟩ := SeqEnd.fall.inj (Option.some.inj (run2.symm.trans secondBase))
      subst fileEq worldEq otherWorldEq otherFileEq
      exact ⟨_,_,_,first,second,post1,post2,rfl⟩

/-- One body run in two related worlds under the guarded memory semantics. Both worlds
end with the same register file and keep the guarded relation; memory is unchanged. -/
theorem stock_sink_extend_body_pair (kind : Kind) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : Shape kind f b x y z ty flags)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms f MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
      ∀ {Rd : BitVec 64 → Prop} {isemG : Backend.Proof.Sem}
        (_guardedMemory : MemRefinesR Rd F sb syms isemG)
        (_subGuarded : ∀ i us w r,isemG i us w = some r → isem i us w = some r)
        (ρ : Nat → CV) (w w' : Arm.ArmState),InitIn Rd s.2.2 →
        GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
        GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w' →
        ∃ ρ' t t',seqRun isemG (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' t) ∧
          seqRun isemG (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w' =
            some (.fall ρ' t') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' t ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' t' ∧
          s'.2.2 = s.2.2 :=
  stock_source_extend_body_pair .plain kind run scope dominated shape.source events stable memorySem
    memoryOk

/-- The paired body provider of the paired entry/return theorem, on the original
`RelW` relation with guarded reads of initialized bytes. -/
theorem stock_source_extend_paired_body (src : Source) (kind : Kind) {f : Clif.Function}
    {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : SourceShape src kind f b x y z ty flags)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
      ∀ ρ q,PairedScanRel f result event.ctx event.block Γ c D event.output.state s ρ q →
        ∃ ρ' q',seqRun (pairSem (csem Γ.F fc X)) (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ q =
            some (.fall ρ' q') ∧
          PairedScanRel f result event.ctx event.block Γ c D term.output.state s' ρ' q' := by
  obtain ⟨term,body,split,pair⟩ := stock_source_extend_body_pair src kind run scope dominated shape events
    (mrStable_relW Γ f c) (memRefines_csem Γ.F fc X slot symbols) (memRelOk_relW Γ f c)
    (env := env) (cp := cp)
  refine ⟨term,body,split,?_⟩
  intro s s' steps ρ q before
  obtain ⟨held,otherHeld,worlds⟩ := before
  have reads := initIn_zof (Γ := Γ) held.2.2.1 D
  obtain ⟨ρ',t,t',first,second,post,otherPost,memory⟩ := pair s s' steps
    (memRefinesR_csemG (ctx := fc) (X := X) (syms := Γ.syms) slot symbols)
    (fun _ _ _ _ h => (csemG_sub h).2.2) ρ q.1 q.2 reads held otherHeld
  let code := body.code.toList.map (·.mapRegs
    (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
  obtain ⟨t2,equal,paired,related⟩ := pair_fall
    (fun _ _ _ _ h => (csemG_sub h).2.2)
    (guardedStep0 (D := D) (syms := Γ.syms) tls fc s.2.2 code [] []) worlds first second
  have sameWorld : t' = t2 := (SeqEnd.fall.inj equal).2
  subst t2
  refine ⟨ρ',(t,t'),paired,post,otherPost,?_⟩
  simpa only [memory] using related

/-- The paired body provider of the paired entry/return theorem, on the original
`RelW` relation with guarded reads of initialized bytes. -/
theorem stock_sink_extend_paired_body (kind : Kind) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : Shape kind f b x y z ty flags)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X) {env : Clif.Env} {cp : Clif.Program} :
    ∃ (term : ScanRecord) (body : BlockScan),SourceBodySplit f event b term body ∧
      ∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
      ∀ ρ q,PairedScanRel f result event.ctx event.block Γ c D event.output.state s ρ q →
        ∃ ρ' q',seqRun (pairSem (csem Γ.F fc X)) (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ q =
            some (.fall ρ' q') ∧
          PairedScanRel f result event.ctx event.block Γ c D term.output.state s' ρ' q' :=
  stock_source_extend_paired_body .plain kind run scope dominated shape.source events slot symbols tls

/-- The original source class executes from instruction zero in paired worlds. The
original ABI, `RelW` and initialized-memory relations supply all runtime premises. -/
theorem source_extend_return_paired_function_seeded (src : Source) (kind : Kind) {f : Clif.Function}
    {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : SourceShape src kind f b x y z ty flags)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X)
    {w w' : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (w,w'))
    (arguments : ArgsAtEntry Γ.F f.sig args w) (otherArguments : ArgsAtEntry Γ.F f.sig args w')
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w' pin = regVal w pin) :
    RunOkABI f result.code (pairSem (csem Γ.F fc X)) (MRP Γ f c D) fr.slots
      ⟨0,0,entrySeed result.ctx fr,(w,w')⟩ (.returned vals mem) := by
  have family : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    rw [shape.body] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals
      constructor
      · intro fn args impossible; cases src <;> cases impossible
      · intro sig callee args impossible; cases src <;> cases impossible
  exact actual_ordinary_paired_entry_return_refines_frame run scope dominated abi shape.blocks family
    shape.ret entered returned registerOnly slot symbols tls
    (fun event events => stock_source_extend_paired_body src kind run scope dominated shape events slot symbols
      tls)
    memory arguments otherArguments registers

/-- The original source class executes from instruction zero in paired worlds. The
original ABI, `RelW` and initialized-memory relations supply all runtime premises. -/
theorem sink_extend_return_paired_function_seeded (kind : Kind) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} {x y z : Nat} {ty : Clif.Ty} {flags : Clif.MemFlags}
    (shape : Shape kind f b x y z ty flags)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    (registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X)
    {w w' : Arm.ArmState} (memory : MRP Γ f c D fr.slots cm (w,w'))
    (arguments : ArgsAtEntry Γ.F f.sig args w) (otherArguments : ArgsAtEntry Γ.F f.sig args w')
    (registers : ∀ pin v,(.reg pin,v) ∈ (locsOf f.sig).zip args → regVal w' pin = regVal w pin) :
    RunOkABI f result.code (pairSem (csem Γ.F fc X)) (MRP Γ f c D) fr.slots
      ⟨0,0,entrySeed result.ctx fr,(w,w')⟩ (.returned vals mem) :=
  source_extend_return_paired_function_seeded .plain kind run scope dominated abi shape.source entered
    returned registerOnly slot symbols tls memory arguments otherArguments registers

end E2E.StockMemory.SinkExtend
