module

public import FV.Backend.Proof.StockEdgeArity
public import FV.Backend.Proof.SpillStep4Cfg
public import FV.Backend.Proof.PerEdgePrepareComplete
public import FV.Backend.Proof.PerEdgePrepareSound

@[expose] public section

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Stock.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Arity on the actual route of one original selected edge. A split source
vector is empty into an empty-parameter synthetic block, whose singleton row
then carries the original vector into its real original target counterpart. -/
def RoutedEdgeArity (p : EdgeVCode) (succs : Array (Array Nat))
    (source index target : Nat) (args : Array Reg) : Prop :=
  ∃ (ss : Array Nat) (middle : Nat) (tb : VBlock),
    succs[source]? = some ss ∧ ss[index]? = some middle ∧ p.code.blocks[target]? = some tb ∧
    ((middle = target ∧ p.edges[source]?.bind (·[index]?) = some args ∧ args.size = tb.params.size) ∨
     (p.edges[source]?.bind (·[index]?) = some #[] ∧
      (∃ (eb : VBlock) (label : Label),p.code.blocks[middle]? = some eb ∧ eb.insts = #[.jump label] ∧
        eb.params = #[] ∧ succs[middle]? = some #[target]) ∧
      p.edges[middle]?.bind (·[0]?) = some args ∧ args.size = tb.params.size))

/-- Every live original edge's actual direct/synthetic prepared route has exact
arity on both segments, from original CFG arity and real preparation. Output
CFG, target counterparts and parameter equality are derived internally. This
route result is combined with actual output reachability for global edge coverage. -/
theorem prepareAt_routed_edge_arity {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    {ss0 ps0 : Array (Array Nat)} (cfg0 : vc.cfg = .ok (ss0,ps0))
    (arity : EdgeArityAt vc edges ss0)
    {b j target : Nat} {ss : Array Nat} {row : EdgeRow} {args : Array Reg}
    (live : Prep.mk (reachable ss0) b) (successors : ss0[b]? = some ss) (edge : ss[j]? = some target)
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args) :
    ∃ (ss3 ps3 : Array (Array Nat)) (q target' : Nat),p.code.cfg = .ok (ss3,ps3) ∧
      sigmaOf vc p.code b = some q ∧ sigmaOf vc p.code target = some target' ∧
      RoutedEdgeArity p ss3 q j target' args := by
  obtain ⟨_,ss3,ps3,cfg3⟩ := prepareAt_cfg run nonempty labels
  have cs0 := Prep.cfg_spec cfg0
  have bBound : b < vc.blocks.size := by rw [← cs0.size]; exact (Array.getElem?_eq_some_iff.mp successors).1
  have targetBound := cfg_succ_lt cfg0 successors (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge))
  have targetAt : vc.blocks[target]? = some vc.blocks[target] := Array.getElem?_eq_getElem targetBound
  have count := arity b j target ss row args vc.blocks[target] successors edge atRow atArgs targetAt
  have notZero : ss0.size ≠ 0 := by rw [cs0.size]; omega
  have member : target ∈ ss0[b]!.toList := by
    simpa only [getElem!_def,successors] using (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge))
  have targetLive := (Prep.reachable_spec (Prep.succsIn_of cs0) notZero).2.2.1 b live target member
  obtain ⟨q,sourceSigma,sourceChecked⟩ := live_okAt run nonempty labels cfg0 cfg3 bBound live
  obtain ⟨target',targetSigma,targetChecked⟩ := live_okAt run nonempty labels cfg0 cfg3 targetBound targetLive
  obtain ⟨vb,vb',sourceBlock,preparedBlock,_,_,_,_,oldSS,newSS,oldRow,newRow,routes⟩ :=
    (keptOkAt_sound sourceChecked).blocks
  obtain ⟨tb,tb',oldTarget,newTarget,params,_⟩ := (keptOkAt_sound targetChecked).blocks
  rw [targetAt] at oldTarget
  cases oldTarget
  rw [successors] at oldRow
  cases oldRow
  obtain ⟨mapped,middle,mappedSigma,selected,route⟩ := routes j target edge
  rw [targetSigma] at mappedSigma
  cases mappedSigma
  have selectedArgs : edges[b]?.bind (·[j]?) = some args := by simp only [atRow,Option.bind_some,atArgs]
  refine ⟨ss3,ps3,q,target',cfg3,sourceSigma,targetSigma,newSS,middle,tb',newRow,selected,newTarget,?_⟩
  rcases route with direct | split
  · exact Or.inl ⟨direct.1,direct.2.trans selectedArgs,by rw [params]; exact count⟩
  · exact Or.inr ⟨split.1,split.2.1,split.2.2.trans selectedArgs,by rw [params]; exact count⟩

end Backend.Proof.PerEdgePrep
