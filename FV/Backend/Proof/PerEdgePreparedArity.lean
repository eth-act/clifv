module

public import FV.Backend.Proof.PerEdgeRouteArity
public import FV.Backend.Proof.PrepareReachability

@[expose] public section

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def Counterpart (vc : VCode) (p : EdgeVCode) (ss0 : Array (Array Nat)) (q : Nat) : Prop :=
  ∃ b,b < vc.blocks.size ∧ Prep.mk (reachable ss0) b ∧ sigmaOf vc p.code b = some q

private def Covered (vc : VCode) (p : EdgeVCode) (ss0 ss3 : Array (Array Nat)) (q : Nat) : Prop :=
  Counterpart vc p ss0 q ∨ ∃ target args tb,
    ss3[q]? = some #[target] ∧ p.edges[q]?.bind (·[0]?) = some args ∧
    p.code.blocks[target]? = some tb ∧ args.size = tb.params.size ∧ Counterpart vc p ss0 target

private def EdgeFact (vc : VCode) (p : EdgeVCode) (ss0 ss3 : Array (Array Nat)) (q j t : Nat) : Prop :=
  ∃ args tb,p.edges[q]?.bind (·[j]?) = some args ∧ p.code.blocks[t]? = some tb ∧
    args.size = tb.params.size ∧ Covered vc p ss0 ss3 t

private theorem original_edge {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    {ss0 ps0 ss3 ps3 : Array (Array Nat)} (cfg0 : vc.cfg = .ok (ss0,ps0))
    (cfg3 : p.code.cfg = .ok (ss3,ps3)) (arity : EdgeArityAt vc edges ss0)
    {q j t : Nat} (original : Counterpart vc p ss0 q)
    {succs : Array Nat} (atSuccs : ss3[q]? = some succs) (edge : succs[j]? = some t) :
    EdgeFact vc p ss0 ss3 q j t := by
  obtain ⟨b,bBound,live,sigma⟩ := original
  obtain ⟨q',sigma',checked⟩ := live_okAt run nonempty labels cfg0 cfg3 bBound live
  rw [sigma] at sigma'
  cases sigma'
  obtain ⟨vb,vb',oldBlock,newBlock,_,_,_,_,oldSS,newSS,oldRow,newRow,_⟩ := (keptOkAt_sound checked).blocks
  rw [atSuccs] at newRow
  cases newRow
  have lengths : succs.size = oldSS.size := by
    unfold keptOkAt at checked
    rw [oldBlock,newBlock,oldRow,atSuccs] at checked
    simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
    exact checked.2.1
  have jBound : j < oldSS.size := by rw [← lengths]; exact (Array.getElem?_eq_some_iff.mp edge).1
  have oldEdge : oldSS[j]? = some oldSS[j] := Array.getElem?_eq_getElem jBound
  obtain ⟨count,ssA,psA,cfgA,dimensions⟩ := prepareAt_input_facts run
  rw [cfg0] at cfgA
  cases cfgA
  have rowBound : b < edges.size := by rw [count]; exact bBound
  have atRow : edges[b]? = some edges[b] := Array.getElem?_eq_getElem rowBound
  have rowSize := dimensions b edges[b] atRow
  have argsBound : j < edges[b].size := by
    rw [rowSize]
    simpa only [getElem!_def,oldRow] using jBound
  have atArgs : edges[b][j]? = some edges[b][j] := Array.getElem?_eq_getElem argsBound
  obtain ⟨ssB,psB,q',target',cfgB,sigmaB,targetSigma,route⟩ :=
    prepareAt_routed_edge_arity run nonempty labels cfg0 arity live oldRow oldEdge atRow atArgs
  rw [cfg3] at cfgB
  cases cfgB
  rw [sigma] at sigmaB
  cases sigmaB
  have cs0 := Prep.cfg_spec cfg0
  have targetBound := Spill.cfg_succ_lt cfg0 oldRow (Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldEdge))
  have targetLive := (Prep.reachable_spec (Prep.succsIn_of cs0) (by rw [cs0.size]; omega)).2.2.1 b live oldSS[j]
    (by simpa only [getElem!_def,oldRow] using (Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldEdge)))
  have targetOriginal : Counterpart vc p ss0 target' := ⟨oldSS[j],targetBound,targetLive,targetSigma⟩
  obtain ⟨ss,middle,tb,routeRow,routeEdge,targetBlock,directOrSplit⟩ := route
  rw [atSuccs] at routeRow
  cases routeRow
  rw [edge] at routeEdge
  cases routeEdge
  rcases directOrSplit with direct | split
  · rcases direct with ⟨rfl,args,count⟩
    exact ⟨_,tb,args,targetBlock,count,.inl targetOriginal⟩
  · obtain ⟨empty,⟨eb,label,placed,insts,params,next⟩,args,count⟩ := split
    exact ⟨#[],eb,empty,placed,by simp [params],.inr ⟨target',_,tb,next,args,targetBlock,count,targetOriginal⟩⟩

private theorem covered_edge {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    {ss0 ps0 ss3 ps3 : Array (Array Nat)} (cfg0 : vc.cfg = .ok (ss0,ps0))
    (cfg3 : p.code.cfg = .ok (ss3,ps3)) (arity : EdgeArityAt vc edges ss0)
    {q j t : Nat} (covered : Covered vc p ss0 ss3 q)
    {succs : Array Nat} (atSuccs : ss3[q]? = some succs) (edge : succs[j]? = some t) :
    EdgeFact vc p ss0 ss3 q j t := by
  rcases covered with original | ⟨target,args,tb,next,atArgs,atTarget,count,original⟩
  · exact original_edge run nonempty labels cfg0 cfg3 arity original atSuccs edge
  · rw [next] at atSuccs
    cases atSuccs
    have jZero : j = 0 := by have := (Array.getElem?_eq_some_iff.mp edge).1; simp only [Array.size_singleton] at this; omega
    subst j
    have same : target = t := by simpa using edge
    subst t
    exact ⟨args,tb,atArgs,atTarget,count,.inl original⟩

/-- Arity of every actual prepared CFG edge. Coverage is derived from the real
entry, indexed direct/split routes, and executable RPO reachability; no output
arity certificate or new input restriction is assumed. -/
theorem prepareAt_edge_arity {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    {ss0 ps0 : Array (Array Nat)} (cfg0 : vc.cfg = .ok (ss0,ps0)) (arity : EdgeArityAt vc edges ss0)
    {ss3 ps3 : Array (Array Nat)} (cfg3 : p.code.cfg = .ok (ss3,ps3)) : EdgeArityAt p.code p.edges ss3 := by
  have cs0 := Prep.cfg_spec cfg0
  have entryLive := (Prep.reachable_spec (Prep.succsIn_of cs0) (by rw [cs0.size]; omega)).2.1
  have entry : Covered vc p ss0 ss3 0 := .inl ⟨0,nonempty,entryLive,prepareAt_entry run nonempty labels⟩
  have coverage : ∀ q,Prep.Reach ss3 q → Covered vc p ss0 ss3 q := by
    intro q reached
    induction reached with
    | entry => exact entry
    | @step b t reached member ih =>
      have bBound : b < ss3.size := by
        by_cases bound : b < ss3.size
        · exact bound
        · have missing : ss3[b]? = none := Array.getElem?_eq_none (by omega)
          simp only [getElem!_def,missing] at member
          change t ∈ ([] : List Nat) at member
          cases member
      have atSuccs := Array.getElem?_eq_getElem bBound
      obtain ⟨j,jBound,jValue⟩ := List.getElem_of_mem member
      have atEdge : ss3[b]![j]? = some t := by
        rw [Array.getElem?_eq_getElem (by simpa using jBound)]
        exact congrArg some (by simpa only [Array.getElem_toList] using jValue)
      rw [getElem!_pos ss3 b bBound] at atEdge
      obtain ⟨args,tb,_,_,_,next⟩ := covered_edge run nonempty labels cfg0 cfg3 arity ih atSuccs atEdge
      exact next
  intro b j target ss row args tb atSuccs edge atRow atArgs atTarget
  have bBound : b < p.code.blocks.size := by rw [← (Prep.cfg_spec cfg3).size]; exact (Array.getElem?_eq_some_iff.mp atSuccs).1
  have covered := coverage b (prepareAt_all_reachable run nonempty labels cfg3 b bBound)
  obtain ⟨actual,tb',actualArgs,actualTarget,count,_⟩ := covered_edge run nonempty labels cfg0 cfg3 arity covered atSuccs edge
  have selected : p.edges[b]?.bind (·[j]?) = some args := by simp only [atRow,Option.bind_some,atArgs]
  rw [selected] at actualArgs
  cases actualArgs
  rw [atTarget] at actualTarget
  cases actualTarget
  exact count

end Backend.Proof.PerEdgePrep

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof

/-- Every actual prepared CFG successor has a real selected argument vector
and target block, with exact arity. This exposes the existence part of route
coverage, so edge-checker completeness cannot be conditional on a missing row. -/
theorem prepareAt_edge_arguments {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    {ss0 ps0 : Array (Array Nat)} (cfg0 : vc.cfg = .ok (ss0,ps0)) (arity : EdgeArityAt vc edges ss0)
    {ss3 ps3 : Array (Array Nat)} (cfg3 : p.code.cfg = .ok (ss3,ps3))
    {b j target : Nat} {succs : Array Nat} (atSuccs : ss3[b]? = some succs) (edge : succs[j]? = some target) :
    ∃ (args : Array Reg) (tb : VBlock),p.edges[b]?.bind (·[j]?) = some args ∧
      p.code.blocks[target]? = some tb ∧ args.size = tb.params.size := by
  have cs0 := Prep.cfg_spec cfg0
  have entryLive := (Prep.reachable_spec (Prep.succsIn_of cs0) (by rw [cs0.size]; omega)).2.1
  have entry : Covered vc p ss0 ss3 0 := .inl ⟨0,nonempty,entryLive,prepareAt_entry run nonempty labels⟩
  have coverage : ∀ q,Prep.Reach ss3 q → Covered vc p ss0 ss3 q := by
    intro q reached
    induction reached with
    | entry => exact entry
    | @step source target reached member ih =>
      have bound : source < ss3.size := by
        by_cases bound : source < ss3.size
        · exact bound
        · have missing : ss3[source]? = none := Array.getElem?_eq_none (by omega)
          simp only [getElem!_def,missing] at member
          change target ∈ ([] : List Nat) at member
          cases member
      have atRow := Array.getElem?_eq_getElem bound
      obtain ⟨j,jBound,jValue⟩ := List.getElem_of_mem member
      have selected : ss3[source]![j]? = some target := by
        rw [Array.getElem?_eq_getElem (by simpa using jBound)]
        exact congrArg some (by simpa only [Array.getElem_toList] using jValue)
      rw [getElem!_pos ss3 source bound] at selected
      obtain ⟨args,tb,_,_,_,next⟩ := covered_edge run nonempty labels cfg0 cfg3 arity ih atRow selected
      exact next
  have bBound : b < p.code.blocks.size := by rw [← (Prep.cfg_spec cfg3).size]; exact (Array.getElem?_eq_some_iff.mp atSuccs).1
  have covered := coverage b (prepareAt_all_reachable run nonempty labels cfg3 b bBound)
  obtain ⟨args,tb,atArgs,atTarget,count,_⟩ := covered_edge run nonempty labels cfg0 cfg3 arity covered atSuccs edge
  exact ⟨args,tb,atArgs,atTarget,count⟩

end Backend.Proof.PerEdgePrep
