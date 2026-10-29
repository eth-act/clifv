module

public import FV.Backend.Proof.PerEdgeSpillEntryGood
public import FV.Backend.Proof.PerEdgeSpillStateAt

@[expose] public section

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill Backend.Stock.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Canonical predecessor output on a selected edge: available homes/saves plus
that edge's live physical terminator results. -/
def termContentAt (vc : VCode) (edges : Array (Array (Array Reg))) (vb : VBlock) (j : Nat)
    (A : Nat → Bool) (l : Loc) : List Sym :=
  bodyContentAt vc edges A l ++ ((termEdgeDefs vb j).filter fun x => decide (x.2 = l)).map (fun x => .vreg x.1.vreg)
def termStateAt (vc : VCode) (edges : Array (Array (Array Reg))) (vb : VBlock) (j : Nat) (A : Nat → Bool) : AState :=
  mkState (stateSizeAt vc edges) (termContentAt vc edges vb j A)
def spillCtxAt (vc : VCode) (edges : Array (Array (Array Reg))) (succs : Array (Array Nat)) : CheckCtx :=
  ⟨vc,succs,spillAllocAt vc edges,stateSizeAt vc edges⟩
def edgeStateAt (vc : VCode) (edges : Array (Array (Array Reg))) (succs : Array (Array Nat))
    (b target j : Nat) (A : Nat → Bool) : AState :=
  let source := vc.blocks[b]!
  let tb := vc.blocks[target]!
  let args := (edges[b]?.bind (·[j]?)).getD #[]
  ((spillCtxAt vc edges succs).edgeForget b target (termStateAt vc edges source j A)).parCopy
    (tb.params.toList.map Reg.homeNum) (args.toList.map Reg.homeNum)

/-- Checker states before entry moves. A unique predecessor supplies its exact
canonical edge state; a shared target uses the canonical body state after its
predecessor's jump copy. Block zero uses the actual function entry state. -/
def preEntryStateAt (vc : VCode) (edges : Array (Array (Array Reg))) (succs preds : Array (Array Nat))
    (post body : Nat → Nat → Bool) (target : Nat) : AState :=
  if target = 0 then entryState (stateSizeAt vc edges)
  else match preds[target]? with
    | some #[b] => edgeStateAt vc edges succs b target ((succs[b]!).toList.idxOf? target |>.getD 0) (post b)
    | _ => bodyStateAt vc edges (body target)

private theorem body_le_term (vc : VCode) (edges : Array (Array (Array Reg))) (vb : VBlock) (j : Nat) (A : Nat → Bool) :
    (bodyStateAt vc edges A).le (termStateAt vc edges vb j A) = true := by
  apply le_of_mem
  intro l s held
  obtain ⟨inside,i,index,bound⟩ := mem_get_mkState held
  rw [termStateAt,get_mkState index bound]
  exact List.mem_append_left _ inside
private theorem good_of_le {vc : VCode} {edges : Array (Array (Array Reg))} {A : Nat → Bool} {a b : AState}
    (good : GoodAt vc edges A a) (le : a.le b = true) (size : b.size = stateSizeAt vc edges) : GoodAt vc edges A b :=
  ⟨size,fun v cl n available classes home => AState.mem_get_le le (good.home v cl n available classes home),
    fun r member => AState.mem_get_le le (good.save r member)⟩

/-- The canonical terminator output retains the body's exact dense-home/save
invariant while adding selected live physical results. -/
theorem termStateAt_good (vc : VCode) (edges : Array (Array (Array Reg))) (vb : VBlock) (j : Nat) (A : Nat → Bool) :
    GoodAt vc edges A (termStateAt vc edges vb j A) :=
  good_of_le (bodyStateAt_good vc edges A) (body_le_term vc edges vb j A) (size_mkState _ _)

/-- Actual instruction-static facts put every selected result in a valid
physical cell of the canonical terminator state. -/
theorem termStateAt_kept {vc : VCode} {edges : Array (Array (Array Reg))} {vb : VBlock} {j : Nat} {A : Nat → Bool}
    (static : ∀ T ops,vb.insts.back? = some T → T.operands = .ok ops → OpsOk ops T.clobbers) :
    ∀ x ∈ termEdgeDefs vb j,Sym.vreg x.1.vreg ∈ (termStateAt vc edges vb j A).get x.2 := by
  intro x member
  obtain ⟨T,ops,last,_,operands,kept,_⟩ := termEdgeDefs_spec member
  obtain ⟨r,loc,alloc,_⟩ := spill_reg (static T ops last operands) (mem_keptPairs kept).1
  obtain ⟨i,index,bound⟩ := reg_index alloc
  rw [loc,termStateAt,get_mkState index (by unfold stateSizeAt; omega)]
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨x,List.mem_filter.mpr ⟨member,by simp only [decide_eq_true_eq]; exact loc⟩,rfl⟩

/-- Canonical predecessor output is included in every actual output satisfying
the proved dense-home invariant and selected physical-result postcondition. -/
theorem termStateAt_le {vc : VCode} {edges : Array (Array (Array Reg))} {vb : VBlock} {j : Nat} {A : Nat → Bool}
    {out : AState} (good : GoodAt vc edges A out) (kept : ∀ x ∈ termEdgeDefs vb j,Sym.vreg x.1.vreg ∈ out.get x.2) :
    (termStateAt vc edges vb j A).le out = true := by
  apply le_of_mem
  intro l s held
  obtain ⟨inside,i,index,bound⟩ := mem_get_mkState held
  rcases List.mem_append.mp inside with body | result
  · apply AState.mem_get_le (bodyStateAt_le good)
    rw [bodyStateAt,get_mkState index bound]
    exact body
  · obtain ⟨x,filtered,rfl⟩ := List.mem_map.mp result
    obtain ⟨member,same⟩ := List.mem_filter.mp filtered
    have eq : x.2 = l := of_decide_eq_true same
    rw [← eq]
    exact kept x member

private theorem forgetOps_le {a b : AState} {ops : List Operand} (le : a.le b = true) :
    (forgetOps a ops).le (forgetOps b ops) = true := by
  apply le_of_mem
  intro l s held
  rw [forgetOps_eq] at held ⊢
  rw [get_map _ _ (by simp)] at held ⊢
  exact List.mem_filter.mpr ⟨AState.mem_get_le le (List.mem_filter.mp held).1,(List.mem_filter.mp held).2⟩
private theorem forget_le (c : CheckCtx) (source target : Nat) {a b : AState} (le : a.le b = true) :
    (c.edgeForget source target a).le (c.edgeForget source target b) = true := by
  unfold CheckCtx.edgeForget
  repeat' first | exact le | split | exact forgetOps_le le
private theorem parCopy_le {a b : AState} {ps xs : List Nat} (le : a.le b = true) :
    (a.parCopy ps xs).le (b.parCopy ps xs) = true := by
  apply le_of_mem
  intro l s held
  rcases AState.mem_get_parCopy held with ⟨old,outside⟩ | ⟨p,x,pair,rfl,arg⟩
  · exact mem_parCopy_keep (AState.mem_get_le le old) (fun p member eq => outside (by rw [eq]; exact List.mem_map_of_mem member))
  · exact mem_parCopy_add pair (AState.mem_get_le le arg)

private theorem unique_index {vc : VCode} {succs preds : Array (Array Nat)}
    (cfg : vc.cfg = .ok (succs,preds)) {b target j : Nat} {ss : Array Nat}
    (successors : succs[b]? = some ss) (edge : ss[j]? = some target) (pred : preds[target]? = some #[b]) :
    ss.toList.idxOf? target = some j := by
  cases found : ss.toList.idxOf? target with
  | none => exact False.elim (List.idxOf?_eq_none_iff.mp found (Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge)))
  | some i =>
    obtain ⟨bound,value,_⟩ := List.idxOf?_eq_some_iff.mp found
    have atIndex : ss[i]? = some target := by
      simpa only [Array.getElem?_toList] using (List.getElem?_eq_getElem bound).trans (congrArg some value)
    have same := (preds_single cfg successors edge pred).2 i atIndex
    subst i
    rfl

/-- The real unique predecessor's canonical pre-entry state is included in the
actual indexed edge result. Actual row/index/block lookups select the same
canonical vector; symbol forgetting and renaming preserve inclusion. -/
theorem preEntryStateAt_unique_le {vc : VCode} {edges : Array (Array (Array Reg))} {succs preds : Array (Array Nat)}
    (cfg : vc.cfg = .ok (succs,preds)) {post body : Nat → Nat → Bool}
    {b target j : Nat} {ss : Array Nat} {vb tb : VBlock} {row : Array (Array Reg)} {args : Array Reg}
    (notEntry : target ≠ 0) (source : vc.blocks[b]? = some vb) (targetBlock : vc.blocks[target]? = some tb)
    (successors : succs[b]? = some ss) (edge : ss[j]? = some target) (pred : preds[target]? = some #[b])
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args)
    {out e : AState} (good : GoodAt vc edges (post b) out)
    (kept : ∀ x ∈ termEdgeDefs vb j,Sym.vreg x.1.vreg ∈ out.get x.2)
    (transfer : EdgeTransferAt (spillCtxAt vc edges succs) edges b target j args tb out e) :
    (preEntryStateAt vc edges succs preds post body target).le e = true := by
  have index := unique_index cfg successors edge pred
  unfold preEntryStateAt
  rw [if_neg notEntry,pred]
  change (edgeStateAt vc edges succs b target ((succs[b]!).toList.idxOf? target |>.getD 0) (post b)).le e = true
  rw [show succs[b]! = ss from by rw [getElem!_def,successors],index]
  simp only [Option.getD_some]
  unfold edgeStateAt
  rw [show vc.blocks[b]! = vb from by rw [getElem!_def,source],
    show vc.blocks[target]! = tb from by rw [getElem!_def,targetBlock],atRow]
  simp only [Option.bind_some,atArgs,Option.getD_some]
  rw [transfer.formula]
  exact parCopy_le (forget_le _ _ _ (termStateAt_le good kept))

/-- Run the actual unique-predecessor entry prefix from its finite canonical
checker input. No actual predecessor output or successor content certificate
is supplied: canonical homes, saves and live results construct that input. -/
theorem preEntryStateAt_unique_runs {vc : VCode} {edges : Array (Array (Array Reg))} {succs preds : Array (Array Nat)}
    (cfg : vc.cfg = .ok (succs,preds)) {post body : Nat → Nat → Bool}
    {b target j : Nat} {ss : Array Nat} {vb tb : VBlock} {row : Array (Array Reg)} {args : Array Reg}
    (notEntry : target ≠ 0) (source : vc.blocks[b]? = some vb) (targetBlock : vc.blocks[target]? = some tb)
    (successors : succs[b]? = some ss) (edge : ss[j]? = some target) (pred : preds[target]? = some #[b])
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args)
    (arity : args.size = tb.params.size) (argShape : ArgumentShape args) (paramShape : ParameterShape tb.params)
    {T : MInst} {ops : Array Operand} (atLast : vb.insts.back? = some T) (operands : T.operands = .ok ops)
    (static : OpsOk ops T.clobbers) {A : Nat → Bool} (postAt : post b = availInst T A)
    (availability : EntryAvailAt vc vb j args tb (post b) (body target)) :
    Spill.Runs (spillCtxAt vc edges succs) tb 0
      (spillEntryStoresAt (spillHomesAt vc edges) vc succs preds target ++
       spillEntryCopiesAt (spillHomesAt vc edges) vc edges succs preds target)
      (preEntryStateAt vc edges succs preds post body target)
      (fun k final => k = 0 ∧ GoodAt vc edges (body target) final ∧
        (bodyStateAt vc edges (body target)).le final = true) := by
  have canonGood := termStateAt_good vc edges vb j (post b)
  have canonKept := termStateAt_kept (vc := vc) (edges := edges) (j := j) (A := post b) (by
    intro T' ops' last' operands'
    have same := Option.some.inj (last'.symm.trans atLast)
    subst T'
    have sameOps := Except.ok.inj (operands'.symm.trans operands)
    subst ops'
    exact static)
  have slots : (spillCtxAt vc edges succs).rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges :=
    (spillAllocAt_storage vc edges).1
  rw [postAt] at availability canonGood canonKept
  obtain ⟨e,transfer,runs⟩ := spill_entry_good_runs rfl slots cfg source targetBlock successors edge pred
    atRow atArgs arity argShape paramShape atLast operands static availability canonGood canonKept
  have input : preEntryStateAt vc edges succs preds post body target = e := by
    have index := unique_index cfg successors edge pred
    unfold preEntryStateAt
    rw [if_neg notEntry,pred]
    change edgeStateAt vc edges succs b target ((succs[b]!).toList.idxOf? target |>.getD 0) (post b) = e
    rw [show succs[b]! = ss from by rw [getElem!_def,successors],index]
    simp only [Option.getD_some]
    unfold edgeStateAt
    rw [show vc.blocks[b]! = vb from by rw [getElem!_def,source],
      show vc.blocks[target]! = tb from by rw [getElem!_def,targetBlock],atRow]
    simp only [Option.bind_some,atArgs,Option.getD_some]
    rw [postAt]
    exact transfer.formula.symm
  rw [input]
  exact runs.mono (fun k final result => ⟨result.1,result.2,bodyStateAt_le result.2⟩)

/-- Shared-target canonical pre-entry states are the body states supplied by
predecessor jump copies. They are included whenever the actual edge establishes
the target body invariant; that edge invariant is proved separately. -/
theorem preEntryStateAt_shared_le {vc : VCode} {edges : Array (Array (Array Reg))} {succs preds : Array (Array Nat)}
    {post body : Nat → Nat → Bool} {target : Nat} (notEntry : target ≠ 0)
    (shared : ∀ b,preds[target]? ≠ some #[b]) {e : AState} (good : GoodAt vc edges (body target) e) :
    (preEntryStateAt vc edges succs preds post body target).le e = true := by
  unfold preEntryStateAt
  rw [if_neg notEntry]
  rcases atPred : preds[target]? with _ | ⟨_ | ⟨b,_ | ⟨b',rest⟩⟩⟩
  · exact bodyStateAt_le good
  · exact bodyStateAt_le good
  · exact False.elim (shared b atPred)
  · exact bodyStateAt_le good

end Backend.Proof.PerEdgeSpill
