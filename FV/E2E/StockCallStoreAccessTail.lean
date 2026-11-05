import FV.Backend.Proof.StockCallStoreFault
import FV.Backend.Proof.StockMemoryAccessPlacement

namespace Backend.Stock.CallStore
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof E2E MemoryFaults
set_option autoImplicit false
set_option Elab.async false

/-- A successful call reaches the actual placed store before its failed access executes. -/
theorem access_tail {sb : Nat} {isem : Sem} {vc : VCode} {block : VBlock}
    (placed : vc.blocks[0]? = some block) {name : String} {argument called pointer : Nat}
    (separate : pointer ≠ called) {flags : Clif.MemFlags} {prelude suffix : List MInst}
    (code : block.insts.toList = (prelude ++
      [.call ⟨.sym name,retPairs [(argument,.x 0)],callDefs [(.x 0,called)]⟩,
       .store .store64 (.vreg called .int) (.unsignedOffset (.vreg pointer .int) 8) flags,
       .rets (retPairs [(called,.x 0)])]) ++ suffix)
    {seed values : Nat → CV} {initial before after : Arm.ArmState} {output : CV}
    (preRun : seqRun isem prelude seed initial = some (.fall values before))
    (callRun : isem (.call ⟨.sym name,retPairs [(argument,.x 0)],callDefs [(.x 0,called)]⟩)
      ([(argument,Reg.x 0)].map (values ·.1)) before = some ([output],after,.next))
    {trap : Clif.TrapCode} (flag : flags.trapCode = some trap) {address : BitVec 64}
    (addressed : amodeAddr sb (.unsignedOffset (.vreg pointer .int) 8) 8 [values pointer] after = some address)
    {property : BitVec 64 → Nat → Prop} (allowed : property address 8) :
    VAccessTrapFrom sb vc isem ⟨0,0,seed,initial⟩ trap property := by
  have tail := CallStoreResult.call_then_store_access separate callRun flag addressed allowed
  have returned := tail.append (rest := [.rets (retPairs [(called,.x 0)])])
  have complete := returned.prefix preRun
  have segment : SegAt block 0 (prelude ++
      [.call ⟨.sym name,retPairs [(argument,.x 0)],callDefs [(.x 0,called)]⟩,
       .store .store64 (.vreg called .int) (.unsignedOffset (.vreg pointer .int) 8) flags,
       .rets (retPairs [(called,.x 0)])]) :=
    segAt_of_toList (L₁ := []) (by simpa only [List.nil_append] using code)
  exact accessTrapRun_at placed segment (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using complete)

end Backend.Stock.CallStore
