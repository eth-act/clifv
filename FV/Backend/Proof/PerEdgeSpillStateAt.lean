module

public import FV.Backend.Proof.PerEdgeSpillInst
public import FV.Backend.Proof.SpillStep4State

@[expose] public section

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Canonical state at a spilled block's body boundary, after entry saves,
result stores and relocated copies. This is not the function entry state. -/
def bodyContentAt (vc : VCode) (edges : Array (Array (Array Reg))) (A : Nat → Bool) : Loc → List Sym
  | .stack n cl => ((List.range vc.classes.size).filter fun v =>
      A v && decide (vc.classes[v]? = some cl) &&
        decide (homeLookup (spillHomesAt vc edges) (spillHomeKeyAt v cl) = some n)).map .vreg
  | .save r => if r ∈ calleeSaved then [.entry r] else []
  | _ => []
def bodyStateAt (vc : VCode) (edges : Array (Array (Array Reg))) (A : Nat → Bool) : AState :=
  mkState (stateSizeAt vc edges) (bodyContentAt vc edges A)

/-- The canonical body state realizes the actual dense-home availability and
save invariant for every VCode/vector table, without a class/slot certificate. -/
theorem bodyStateAt_good (vc : VCode) (edges : Array (Array (Array Reg))) (A : Nat → Bool) :
    GoodAt vc edges A (bodyStateAt vc edges A) := by
  constructor
  · exact size_mkState _ _
  · intro v cl n available classes home
    have bound := (spillHomesAt_spec vc edges).valid.1 _ _ home
    have index : ∃ i,(Loc.stack n cl).index = some i ∧ i < stateSizeAt vc edges := by
      cases cl <;> exact ⟨_,rfl,by unfold stateSizeAt; omega⟩
    obtain ⟨i,atIndex,iBound⟩ := index
    rw [bodyStateAt,get_mkState atIndex iBound]
    simp only [bodyContentAt,List.mem_map,List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨v,⟨(Array.getElem?_eq_some_iff.mp classes).1,⟨⟨available,classes⟩,home⟩⟩,rfl⟩
  · intro r saved
    obtain ⟨i,atIndex,iBound⟩ := save_index saved
    rw [bodyStateAt,get_mkState atIndex (by unfold stateSizeAt; omega)]
    simp only [bodyContentAt,if_pos saved,List.mem_singleton]

/-- Every actual body state satisfying GoodAt contains the canonical body
state. This gives an explicit finite candidate for invariant/fixpoint proofs. -/
theorem bodyStateAt_le {vc : VCode} {edges : Array (Array (Array Reg))} {A : Nat → Bool} {a : AState}
    (good : GoodAt vc edges A a) : (bodyStateAt vc edges A).le a = true := by
  apply le_of_mem
  intro l s held
  obtain ⟨inside,_⟩ := mem_get_mkState held
  cases l with
  | reg r => cases inside
  | stack n cl =>
    simp only [bodyContentAt,List.mem_map,List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq] at inside
    obtain ⟨v,⟨_,⟨⟨available,classes⟩,home⟩⟩,rfl⟩ := inside
    exact good.home v cl n available classes home
  | save r =>
    simp only [bodyContentAt] at inside
    split at inside
    · rename_i saved
      simp only [List.mem_singleton] at inside
      subst s
      exact good.save r saved
    · cases inside

end Backend.Proof.PerEdgeSpill
