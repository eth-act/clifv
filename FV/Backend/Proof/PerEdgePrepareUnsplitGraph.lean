import FV.Backend.Proof.PrepareComplete

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The real splitting invariant with no synthetic blocks preserves the
entire indexed successor graph. Duplicate destinations and edge indices are
retained; this is stronger than preservation of unindexed reachability. -/
theorem unsplit_cfg_eq {V B : Array VBlock} {next : Nat}
    {ss1 ss2 : Array (Array Nat)} (labels : Prep.Lbls V)
    (inv : Prep.SInv V (Prep.next0Of V) V.size (next,B,#[]))
    (cfg1 : Prep.CfgSpec V ss1) (cfg2 : Prep.CfgSpec B ss2) : ss1 = ss2 := by
  apply Array.ext
  · rw [cfg1.size,cfg2.size,inv.size]
  · intro b hb hb'
    have bound : b < V.size := by rw [← cfg1.size]; exact hb
    obtain ⟨boundB,t,t',back,back',label,params,args,size,pop,same,count,route⟩ := Prep.blk2 inv cfg1 bound
    obtain ⟨t0,row,back0,_,atRow,rowCount,targets⟩ := cfg1.blk b V[b] (Array.getElem?_eq_getElem bound)
    obtain ⟨t2,row',back2,_,atRow',rowCount',targets'⟩ := cfg2.blk b B[b] (Array.getElem?_eq_getElem boundB)
    rw [back] at back0
    cases back0
    rw [back'] at back2
    cases back2
    have rowEq : ss1[b] = row := Option.some.inj (by rw [← Array.getElem?_eq_getElem hb]; exact atRow)
    have rowEq' : ss2[b] = row' := Option.some.inj (by rw [← Array.getElem?_eq_getElem hb']; exact atRow')
    rw [rowEq,rowEq']
    apply Array.ext
    · omega
    · intro j hj hj'
      obtain ⟨l',selected'⟩ : ∃ l',t'.targets[j]? = some l' :=
        ⟨_,List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨l,selected,direct | synthetic⟩ := route j l' selected'
      · subst l'
        obtain ⟨s,edge,find⟩ := targets j l selected
        obtain ⟨s',edge',find'⟩ := targets' j l selected'
        obtain ⟨sBound,sLabel⟩ := Prep.lab_some find
        obtain ⟨sBoundB,sLabelB⟩ := Prep.lab_some find'
        have sBoundV : s' < V.size := by rw [← inv.size]; exact sBoundB
        have sLabel' : V[s'].label = l := ((Prep.rw_fields (inv.rw s' sBoundV sBoundB)).1).symm.trans sLabelB
        have equal := Prep.lbl_inj labels sBound sBoundV (sLabel.trans sLabel'.symm)
        rw [Array.getElem?_eq_getElem hj] at edge
        rw [Array.getElem?_eq_getElem hj'] at edge'
        exact (Option.some.inj edge).trans (equal.trans (Option.some.inj edge').symm)
      · obtain ⟨_,e,impossible⟩ := synthetic
        simp at impossible

end Backend.Proof.PerEdgePrep
