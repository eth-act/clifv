import FV.Backend.Proof.PerEdgeSpillCopy
import FV.Backend.Proof.PerEdgeSpillRoutes
import FV.Backend.Proof.SpillStep4Edge

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

private theorem home_eq {h : SpillHomesAt} {v n : Nat} {cl : RegClass}
    (found : homeLookup h (spillHomeKeyAt v cl) = some n) : spillHomeAt h v cl = .stack n cl := by
  unfold homeLookup at found
  simp only [spillHomeAt,found,Option.getD_some]

private theorem defs_facts {vc : VCode} {edges : Array (Array (Array Reg))}
    {b : Nat} {vb : VBlock} (source : vc.blocks[b]? = some vb)
    (static : ∀ T ops,vb.insts.back? = some T → T.operands = .ok ops → OpsOk ops T.clobbers)
    (j : Nat) :
    (∀ y ∈ termEdgeDefs vb j,
      (∃ r,y.2 = .reg r ∧ r.allocatable = true ∧ r.realClass? = some y.1.cls) ∧
      ∃ n,homeLookup (spillHomesAt vc edges) (spillHomeKeyAt y.1.vreg y.1.cls) = some n) ∧
    ((termEdgeDefs vb j).map (·.1.vreg)).Nodup := by
  rcases termEdgeDefs_sub vb j with empty | ⟨T,ops,last,operands,sub⟩
  · rw [empty]
    exact ⟨(fun _ h => by cases h),List.nodup_nil⟩
  have valid := static T ops last operands
  refine ⟨fun y member => ?_,(keptPairs_vregs_nodup valid).sublist (sub.map _)⟩
  have pair := (mem_keptPairs (sub.subset member)).1
  have opMember : y.1 ∈ ops.toList := spillPairs_fst ops T.clobbers ▸ List.mem_map_of_mem pair
  exact ⟨spill_reg valid pair,(spillHomesAt_spec vc edges).code b vb source _
    (mem_blockVregs_op (back_get last).2 operands opMember)⟩

/-- Actual selected-edge result stores are checked before copies execute. Their
homes contain the incoming physical result symbols, and all other locations
are framed. Only the existing instruction-local static obligation is exposed. -/
theorem spill_entry_stores_runs {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (hsl : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
    {b j : Nat} {vb tb : VBlock} (source : vc.blocks[b]? = some vb)
    (static : ∀ T ops,vb.insts.back? = some T → T.operands = .ok ops → OpsOk ops T.clobbers)
    {k : Nat} (beforeTerminator : k ≠ tb.insts.size) {a0 : AState}
    (stateSize : a0.size = stateSizeAt vc edges) :
    Runs c tb k ((termEdgeDefs vb j).map (fun (x : Operand × Loc) =>
      RItem.move x.2 (spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls))) a0 fun k' a' =>
      k' = k ∧ a'.size = stateSizeAt vc edges ∧
      (∀ x ∈ termEdgeDefs vb j,a'.get (spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls) = a0.get x.2) ∧
      ∀ l,(∀ x ∈ termEdgeDefs vb j,spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls ≠ l) →
        a'.get l = a0.get l := by
  obtain ⟨facts,distinct⟩ := defs_facts (edges := edges) source static j
  let ms := (termEdgeDefs vb j).map (fun x => (x.2,spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls))
  have members : ∀ m ∈ ms,∃ y ∈ termEdgeDefs vb j,∃ r n,
      m = (.reg r,.stack n y.1.cls) ∧ y.2 = .reg r ∧ r.allocatable = true ∧
      r.realClass? = some y.1.cls ∧ homeLookup (spillHomesAt vc edges) (spillHomeKeyAt y.1.vreg y.1.cls) = some n := by
    intro m member
    obtain ⟨y,inside,rfl⟩ := List.mem_map.mp member
    obtain ⟨⟨r,hr,ha,hc⟩,n,hn⟩ := facts y inside
    exact ⟨y,inside,r,n,by rw [hr,home_eq hn],hr,ha,hc,hn⟩
  have run := Runs.moves (c := c) beforeTerminator ms a0
  have result : Runs c tb k (ms.map mv) a0 fun k' a' => k' = k ∧ a'.size = a0.size ∧
      (∀ m ∈ ms,a'.get m.2 = a0.get m.1) ∧
      ∀ l,(∀ m ∈ ms,m.2 ≠ l) → a'.get l = a0.get l := by
    apply run
    · intro m member
      obtain ⟨y,_,r,n,rfl,_,ha,hc,hn⟩ := members m member
      exact checkMove_store c _ (by rw [hsl]; have := (spillHomesAt_spec vc edges).valid.1 _ _ hn; omega) ha hc
    · intro m member m' member' equal
      obtain ⟨y,_,r,n,rfl,_⟩ := members m member
      obtain ⟨y',_,r',n',rfl,_⟩ := members m' member'
      cases equal
    · change (((termEdgeDefs vb j).map _).map _).Nodup
      rw [List.map_map]
      refine nodup_map_of_inj distinct fun x hx y hy equal => ?_
      obtain ⟨_,n,hn⟩ := facts x hx
      obtain ⟨_,n',hn'⟩ := facts y hy
      simp only [Function.comp,home_eq hn,home_eq hn'] at equal
      injection equal with same cls
      rw [← same] at hn'
      have keys := (spillHomesAt_spec vc edges).valid.2 _ _ _ hn hn'
      exact (spillHomeKeyAt_injective keys).1
    · intro m member
      obtain ⟨y,_,r,n,rfl,_,_,_,hn⟩ := members m member
      have bound := (spillHomesAt_spec vc edges).valid.1 _ _ hn
      rw [stateSize]
      cases y.1.cls <;> simp only [Loc.index,stateSizeAt] <;> exact ⟨_,rfl,by omega⟩
  have items : ms.map mv = (termEdgeDefs vb j).map (fun (x : Operand × Loc) =>
      RItem.move x.2 (spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls)) := by
    simp only [ms,List.map_map,mv,Function.comp_def]
  rw [← items]
  exact result.mono fun k' a' ⟨same,sz,values,frame⟩ =>
    ⟨same,sz.trans stateSize,fun x hx => values _ (List.mem_map_of_mem hx),
      fun l hl => frame l (fun m hm => by obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm; exact hl x hx)⟩

/-- The real unique-predecessor entry segment stores live terminator results
before copying edge arguments. Fresh results reach parameter homes; unrelated
argument homes retain their incoming content, and saved-register cells survive.
The indexed class/arity/distinctness obligations remain internal VCode facts. -/
theorem spill_entry_runs {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (hsl : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
    {succs preds : Array (Array Nat)} (cfg : vc.cfg = .ok (succs,preds))
    {b s j : Nat} {ss : Array Nat} {vb tb : VBlock} {row : Array (Array Reg)} {args : Array Reg}
    (source : vc.blocks[b]? = some vb) (target : vc.blocks[s]? = some tb)
    (successors : succs[b]? = some ss) (edge : ss[j]? = some s) (pred : preds[s]? = some #[b])
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args)
    (static : ∀ T ops,vb.insts.back? = some T → T.operands = .ok ops → OpsOk ops T.clobbers)
    (size : args.size = tb.params.size)
    (classes : ∀ (i : Nat) (a p : Reg),args[i]? = some a → tb.params[i]? = some p →
      ∃ v w cl,a = .vreg v cl ∧ p = .vreg w cl)
    (distinct : (tb.params.toList.map Reg.homeNum).Nodup)
    {a0 : AState} (stateSize : a0.size = stateSizeAt vc edges) :
    Runs c tb 0
      (spillEntryStoresAt (spillHomesAt vc edges) vc succs preds s ++
       spillEntryCopiesAt (spillHomesAt vc edges) vc edges succs preds s) a0 fun k' a' =>
      k' = 0 ∧ a'.size = stateSizeAt vc edges ∧
      (∀ x ∈ termEdgeDefs vb j,∀ (i : Nat) (ar p : Reg),args[i]? = some ar → tb.params[i]? = some p →
        ar.homeNum = x.1.vreg → ar.homeCls = x.1.cls →
        a'.get (spillHomeAt (spillHomesAt vc edges) p.homeNum p.homeCls) = a0.get x.2) ∧
      (∀ (i : Nat) (ar p : Reg),args[i]? = some ar → tb.params[i]? = some p →
        (∀ x ∈ termEdgeDefs vb j,spillHomeAt (spillHomesAt vc edges) x.1.vreg x.1.cls ≠
          spillHomeAt (spillHomesAt vc edges) ar.homeNum ar.homeCls) →
        a'.get (spillHomeAt (spillHomesAt vc edges) p.homeNum p.homeCls) =
          a0.get (spillHomeAt (spillHomesAt vc edges) ar.homeNum ar.homeCls)) ∧
      ∀ r,a'.get (.save r) = a0.get (.save r) := by
  obtain ⟨stores,copies⟩ := spill_entry_route cfg source target successors edge pred atRow atArgs
  obtain ⟨T,last,_⟩ := cfg_last cfg target
  have nonempty : 0 ≠ tb.insts.size := by have := (back_get last).1; omega
  rw [stores,copies]
  refine Runs.append (spill_entry_stores_runs hsl source static nonempty stateSize)
    fun k mid ⟨same,midSize,stored,framed⟩ => ?_
  subst k
  refine (spillArgMovesAt_runs hsl atRow atArgs target size classes distinct nonempty midSize).mono
    fun k final ⟨same,finalSize,copied,copyFrame⟩ => ⟨same,finalSize,?_,?_,?_⟩
  · intro x inside i ar p arAt pAt num cls
    rw [copied i ar p arAt pAt,num,cls,stored x inside]
  · intro i ar p arAt pAt unchanged
    rw [copied i ar p arAt pAt,framed _ unchanged]
  · intro r
    rw [copyFrame (.save r) (fun cl eq => by cases eq) (fun i cl eq => by cases eq)
      (fun p _ eq => by simp only [spillHomeAt] at eq; cases eq),
      framed (.save r) (fun x _ eq => by simp only [spillHomeAt] at eq; cases eq)]

end Backend.Proof.PerEdgeSpill
