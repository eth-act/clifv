import FV.Backend.Proof.RegallocOperands
import FV.Backend.Proof.PerEdgeSpillEntry
import FV.Backend.Proof.PerEdgeSpillEdge

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Internal predecessor availability: a selected argument is either a live
terminator result in its real physical result register, or an ordinary home
unaffected by the selected result stores. Dead results must already be absent
from the real edgeForget state. This is a checker-state invariant to prove from
source inputs, not an additional source acceptance condition. -/
def IncomingArgSymbolsAt (vc : VCode) (edges : Array (Array (Array Reg)))
    (vb : VBlock) (j : Nat) (args : Array Reg) (a : AState) : Prop :=
  ∀ (i : Nat) (ar : Reg),args[i]? = some ar →
    (∃ x ∈ termEdgeDefs vb j,ar.homeNum = x.1.vreg ∧ ar.homeCls = x.1.cls ∧ Sym.vreg ar.homeNum ∈ a.get x.2) ∨
    ((∀ x ∈ termEdgeDefs vb j,spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls ≠
      spillHomeAt (spillHomesAt vc edges) ar.homeNum ar.homeCls) ∧
      Sym.vreg ar.homeNum ∈ a.get (spillHomeAt (spillHomesAt vc edges) ar.homeNum ar.homeCls))

/-- The real edge transfer occurs before unique-predecessor result stores and
copies. Its renamed parameter symbols reach their actual homes, and every
unrelated home/save location is framed through both stages. -/
theorem spill_entry_symbols_runs {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (slots : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
    {succs preds : Array (Array Nat)} (cfg : vc.cfg = .ok (succs,preds))
    {b target j : Nat} {ss : Array Nat} {vb tb : VBlock} {row : Array (Array Reg)} {args : Array Reg}
    (source : vc.blocks[b]? = some vb) (targetBlock : vc.blocks[target]? = some tb)
    (successors : succs[b]? = some ss) (edge : ss[j]? = some target) (pred : preds[target]? = some #[b])
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args)
    (static : ∀ T ops,vb.insts.back? = some T → T.operands = .ok ops → OpsOk ops T.clobbers)
    (arity : args.size = tb.params.size)
    (classes : ∀ (i : Nat) (ar p : Reg),args[i]? = some ar → tb.params[i]? = some p →
      ∃ v w cl,ar = .vreg v cl ∧ p = .vreg w cl)
    (distinct : (tb.params.toList.map Reg.homeNum).Nodup)
    {out e : AState} (transfer : EdgeTransferAt c edges b target j args tb out e)
    (incoming : IncomingArgSymbolsAt vc edges vb j args (c.edgeForget b target out))
    (saved : ∀ r ∈ calleeSaved,Sym.entry r ∈ out.get (.save r))
    (stateSize : out.size = stateSizeAt vc edges) :
    Spill.Runs c tb 0 (spillEntryStoresAt (spillHomesAt vc edges) vc succs preds target ++
      spillEntryCopiesAt (spillHomesAt vc edges) vc edges succs preds target) e fun k final =>
      k = 0 ∧ final.size = stateSizeAt vc edges ∧
      (∀ (i : Nat) (ar p : Reg),args[i]? = some ar → tb.params[i]? = some p →
        Sym.vreg p.homeNum ∈ final.get (spillHomeAt (spillHomesAt vc edges) p.homeNum p.homeCls)) ∧
      (∀ r ∈ calleeSaved,Sym.entry r ∈ final.get (.save r)) ∧
      ∀ l,(∀ cl,l ≠ .reg (spillScratch cl)) →
        (∀ i cl,l ≠ .stack ((spillHomesAt vc edges).size+i) cl) →
        (∀ p ∈ tb.params.toList,l ≠ spillHomeAt (spillHomesAt vc edges) p.homeNum p.homeCls) →
        (∀ x ∈ termEdgeDefs vb j,spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls ≠ l) →
        final.get l = e.get l := by
  obtain ⟨stores,copies⟩ := spill_entry_route cfg source targetBlock successors edge pred atRow atArgs
  obtain ⟨T,last,_⟩ := cfg_last cfg targetBlock
  have nonempty : 0 ≠ tb.insts.size := by have := (back_get last).1; omega
  have eSize := transfer.size.trans stateSize
  rw [stores,copies]
  refine Spill.Runs.append (spill_entry_stores_runs slots source static nonempty eSize)
    fun k mid ⟨same,midSize,stored,storesFrame⟩ => ?_
  subst k
  refine (spillArgMovesAt_runs slots atRow atArgs targetBlock arity classes distinct nonempty midSize).mono ?_
  intro k final ⟨same,finalSize,copied,copyFrame⟩
  refine ⟨same,finalSize,?_,?_,?_⟩
  · intro i ar p arAt pAt
    rw [copied i ar p arAt pAt]
    rcases incoming i ar arAt with ⟨x,inside,num,cls,held⟩ | ⟨unaffected,held⟩
    · rw [num,cls,stored x inside]
      exact transfer.parameter i ar p arAt pAt x.2 held
    · rw [storesFrame _ unaffected]
      exact transfer.parameter i ar p arAt pAt _ held
  · intro r hr
    rw [copyFrame (.save r) (fun _ same => by cases same) (fun _ _ same => by cases same)
      (fun p _ same => by simp only [spillHomeAt] at same; cases same),
      storesFrame (.save r) (fun x _ same => by simp only [spillHomeAt] at same; cases same)]
    exact transfer.entry _ r (saved r hr)
  · intro l scratch temps params results
    rw [copyFrame l scratch temps params,storesFrame l results]

end Backend.Proof.PerEdgeSpill
