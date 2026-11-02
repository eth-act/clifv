import FV.Backend.Proof.StockSourceReachability
import FV.Backend.Proof.StockSretSourceStability
import FV.Backend.Proof.StockReturnFullBody

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

theorem source_reach_trans {env : Clif.Env} {cp : Clif.Program} {s t u : Clif.State}
    (first : Reach env cp s t) (second : Reach env cp t u) : Reach env cp s u := by
  induction first with
  | refl => exact second
  | step step _ ih => exact .step step (ih second)

def ReturnFromAt {W : Type} (env : Clif.Env) (cp : Clif.Program) (f : Clif.Function)
    (vc : VCode) (edges : Array (Array (Array Reg))) (sem : ISem CV W) (MR : MemRelTW W)
    (initial : Clif.State) (xs : List Nat) (vs : VState CV W) : Clif.Outcome → Prop
  | .returned vals cm => ∃ terminal : Clif.State,Reach env cp initial terminal ∧
      terminal.frame.slots = initial.frame.slots ∧ ReturnValuesAt f vc edges sem MR terminal vs xs vals cm
  | .trapped c => PerEdgePrep.VTrapFromAt vc edges sem vs c
  | .stuck _ | .outOfFuel => True

theorem ReturnFromAt.runOkABIAt {W : Type} {env : Clif.Env} {cp : Clif.Program}
    {f : Clif.Function} {vc : VCode} {edges : Array (Array (Array Reg))} {sem : ISem CV W}
    {MR : MemRelTW W} {initial : Clif.State} {xs : List Nat} {vs : VState CV W} {o : Clif.Outcome}
    (returned : ReturnFromAt env cp f vc edges sem MR initial xs vs o) :
    RunOkABIAt f vc edges sem MR initial.frame.slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨terminal,reachable,slots,full⟩ := returned
    simpa only [slots] using full.runOkABIAt
  | trapped c => exact returned
  | _ => trivial

theorem ReturnFromAt.prefix {W : Type} {env : Clif.Env} {cp : Clif.Program}
    {f : Clif.Function} {vc : VCode} {edges : Array (Array (Array Reg))} {sem : ISem CV W}
    {MR : MemRelTW W} {initial : Clif.State} {xs : List Nat} {vs vs' : VState CV W} {o : Clif.Outcome}
    (steps : Star (VStepAt vc edges sem) (.run vs) (.run vs'))
    (returned : ReturnFromAt env cp f vc edges sem MR initial xs vs' o) :
    ReturnFromAt env cp f vc edges sem MR initial xs vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨terminal,reachable,slots,full⟩ := returned
    exact ⟨terminal,reachable,slots,full.prefix steps⟩
  | trapped c =>
    obtain ⟨b,k,ρ,w,vb,i,ops,outs,w',tail,rest⟩ := returned
    exact ⟨b,k,ρ,w,vb,i,ops,outs,w',steps.trans tail,rest⟩
  | _ => trivial

theorem ReturnFromAt.source_prefix {W : Type} {env : Clif.Env} {cp : Clif.Program}
    {f : Clif.Function} {vc : VCode} {edges : Array (Array (Array Reg))} {sem : ISem CV W}
    {MR : MemRelTW W} {initial next : Clif.State} {xs : List Nat} {vs : VState CV W} {o : Clif.Outcome}
    (path : Reach env cp initial next) (slots : next.frame.slots = initial.frame.slots)
    (returned : ReturnFromAt env cp f vc edges sem MR next xs vs o) :
    ReturnFromAt env cp f vc edges sem MR initial xs vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨terminal,reachable,equal,full⟩ := returned
    exact ⟨terminal,source_reach_trans path reachable,equal.trans slots,full⟩
  | trapped c => exact returned
  | _ => trivial
end Backend.Stock.Proof
namespace Backend.Stock.Proof.OrdinaryBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
theorem actual_ordinary_return_reachable_at_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block}
    (family : ∀ stm ∈ b.body, OrdinaryInst stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (func : s.frame.func = f) (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (terminal : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx event.block 0 s.frame)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR)
    (bodyRun : ∀ s s', SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block + ·)) s s' →
        ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w')
    {label : Nat} {vb : VBlock} {pre post : Array MInst}
    (placed : result.code.blocks[label]? = some vb)
    (code : vb.insts = pre ++ event.output.code.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ post) :
    ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,s.frame,s.mem) ρ w →
      ReturnFromAt env cp f result.code result.edgeArgs isem MR s xs ⟨label,pre.size,ρ,w⟩ (.returned vals mem) := by
  intro ρ w held
  obtain ⟨endpoint,steps,slots,preserved,full⟩ := actual_ordinary_return_full_values_at_block
    run scope dominated abi family ret events split func callers remaining terminal defined returned
    refines stable bodyRun placed code ρ w held
  let target : Clif.State := ⟨endpoint.frame,s.callers,endpoint.mem⟩
  have path := ordinary_source_steps_reach run events split family
    (fun i member => by
      obtain ⟨j,inside,rfl⟩ := List.mem_map.mp member
      have bound := List.mem_range.mp inside
      exact ⟨j,b.body[j],List.getElem?_eq_getElem bound,rfl⟩) steps s.callers
  refine ⟨target,?_,slots,full⟩
  change Reach env cp ⟨s.frame,s.callers,s.mem⟩ target
  exact path
end Backend.Stock.Proof.OrdinaryBody
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

theorem ReturnFromAt.original_sret_arguments {f : Clif.Function} {result : Result}
    {env : Clif.Env} {cp : Clif.Program} {args : List Clif.Val} {fr : Clif.Frame} {cm : Clif.Mem}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {vs : VState CV Arm.ArmState}
    {vals : List Clif.Val} {outMem : Clif.Mem}
    (full : ReturnFromAt env cp f result.code result.edgeArgs isem MR ⟨fr,[],cm⟩ [] vs (.returned vals outMem))
    (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ block ∈ f.blocks,∀ stmt ∈ block.body,OrdinaryBody.OrdinaryInst stmt.inst)
    (terms : ∀ block ∈ f.blocks,(∃ dest,block.term = .jump dest) ∨ (∃ xs,block.term = .ret xs))
    (entered : SourceEntry f args fr) :
    ∃ us outs world cm0,PerEdgePrep.VRetFromAt result.code result.edgeArgs isem vs us outs world ∧
      ReturnABI f us ∧ us.length = outs.length ∧ AllHold (sretArg f args) outs ∧
      MR fr.slots cm0 world ∧ outMem = (cm0.free (fr.slots.map (·.2))).leave := by
  obtain ⟨terminal,path,slots,observed⟩ := full
  have original := ordinary_cfg_sret_argument scope dominated family terms entered path
  obtain ⟨us,outs,world,extra,execution,pins,arity,read,values,memory,freed⟩ := observed
  have same : vals ++ extra = sretArg f args := Clif.Res.ok.inj (read.symm.trans original)
  rw [same] at values
  exact ⟨us,outs,world,terminal.mem,execution,pins,arity,values,
    by simpa only [slots] using memory,by simpa only [slots] using freed⟩

end Backend.Stock.Proof
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

theorem original_argument_x8_projection {f : Clif.Function} {args : List Clif.Val}
    {us : List (Reg × Reg)} {outs : List CV}
    (pins : ReturnABI f us) (arity : us.length = outs.length) (held : AllHold (sretArg f args) outs)
    (sret : (sigRets f.sig).any (·.purpose == .sret) = true) :
    ∃ pointer source value,sretArg f args = [pointer] ∧ us = [(source,.x 8)] ∧
      outs = [value] ∧ VHolds pointer value := by
  have physical : us.map (·.2) = [.x 8] := by
    simpa only [ReturnABI,returnPins,sret,↓reduceIte,Option.some.injEq] using pins.symm
  have length : us.length = 1 := by
    have same := congrArg List.length physical
    simpa only [List.length_map,List.length_singleton] using same
  obtain ⟨⟨source,pin⟩,rfl⟩ := List.length_eq_one_iff.mp length
  have pinEq : pin = .x 8 := by simpa using physical
  subst pin
  obtain ⟨value,rfl⟩ := List.length_eq_one_iff.mp (by simpa using arity.symm : outs.length = 1)
  obtain ⟨pointer,read⟩ := List.length_eq_one_iff.mp (by simpa using held.1 : (sretArg f args).length = 1)
  refine ⟨pointer,source,value,read,rfl,rfl,?_⟩
  rw [read] at held
  exact held.2 0 pointer value (by rfl) (by rfl)

end Backend.Stock.Proof
