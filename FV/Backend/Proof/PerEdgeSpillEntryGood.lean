import FV.Backend.Proof.PerEdgeSpillEntrySymbols
import FV.Backend.Proof.PerEdgeSpillInst

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill Backend.Stock.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Internal dataflow/class facts at a real selected edge. Post-terminator home
availability and live physical results are distinct. These facts must be proved
for actual Stock output, not imposed as additional source acceptance checks. -/
structure EntryAvailAt (vc : VCode) (vb : VBlock) (j : Nat) (args : Array Reg) (tb : VBlock)
    (post wanted : Nat → Bool) : Prop where
  arguments : ∀ (i : Nat) (ar : Reg),args[i]? = some ar → post ar.homeNum = true ∨
    ∃ x ∈ termEdgeDefs vb j,ar.homeNum = x.1.vreg ∧ ar.homeCls = x.1.cls
  argClasses : ∀ (i : Nat) (ar : Reg),args[i]? = some ar → post ar.homeNum = true → vc.classes[ar.homeNum]? = some ar.homeCls
  paramClasses : ∀ p ∈ tb.params.toList,wanted p.homeNum = true → vc.classes[p.homeNum]? = some p.homeCls
  ordinary : ∀ v,wanted v = true → v ∉ tb.params.toList.map Reg.homeNum → post v = true

private theorem home_eq {h : SpillHomesAt} {v n : Nat} {cl : RegClass}
    (found : homeLookup h (spillHomeKeyAt v cl) = some n) : spillHomeAt h v cl = .stack n cl := by
  unfold homeLookup at found
  simp only [spillHomeAt,found,Option.getD_some]
private theorem homes_ne {vc : VCode} {edges : Array (Array (Array Reg))} {v w n m : Nat} {cl dl : RegClass}
    (left : homeLookup (spillHomesAt vc edges) (spillHomeKeyAt v cl) = some n)
    (right : homeLookup (spillHomesAt vc edges) (spillHomeKeyAt w dl) = some m) (different : v ≠ w) :
    spillHomeAt (spillHomesAt vc edges) v cl ≠ spillHomeAt (spillHomesAt vc edges) w dl := by
  rw [home_eq left,home_eq right]
  intro same
  have equal : n = m := by injection same
  rw [← equal] at right
  have key := (spillHomesAt_spec vc edges).valid.2 _ _ _ left right
  exact different (spillHomeKeyAt_injective key).1

private theorem term_not_def {T : MInst} {ops : Array Operand} {A : Nat → Bool} {v : Nat}
    (term : T.isTerminator = true) (operands : T.operands = .ok ops) (available : availInst T A v = true) :
    ∀ o ∈ ops.toList,o.kind = .def → v ≠ o.vreg := by
  have notDef : isDefOf ops v = false := by
    cases found : isDefOf ops v with
    | false => rfl
    | true =>
      rw [availInst_eq operands,found] at available
      simp only [ite_true,storedDefs_eq,term,ite_true,List.contains_nil] at available
      cases available
  intro o member defKind same
  have yes := isDefOf_of member defKind
  rw [← same,notDef] at yes
  cases yes

private theorem live_kept {vb : VBlock} {T : MInst} {ops : Array Operand} {j : Nat} {x : Operand × Loc}
    (atLast : vb.insts.back? = some T) (operands : T.operands = .ok ops) (member : x ∈ termEdgeDefs vb j) :
    x ∈ keptPairs T (ops.zip (spillLocs ops T.clobbers)).toList := by
  obtain ⟨T',ops',last',_,operands',kept,_⟩ := termEdgeDefs_spec member
  rw [atLast] at last'
  cases last'
  rw [operands] at operands'
  cases operands'
  exact kept

private theorem forget_available {vc : VCode} {c : CheckCtx} (code : c.vc = vc)
    {b target : Nat} {vb : VBlock} {T : MInst} {ops : Array Operand}
    (source : vc.blocks[b]? = some vb) (atLast : vb.insts.back? = some T) (operands : T.operands = .ok ops)
    (term : T.isTerminator = true) {A : Nat → Bool} {v : Nat} (available : availInst T A v = true)
    {out : AState} {l : Loc} (held : Sym.vreg v ∈ out.get l) : Sym.vreg v ∈ (c.edgeForget b target out).get l := by
  rcases edgeForget_cases code source atLast operands out with same | ⟨jn,n,_,_,forgot⟩
  · rw [same]; exact held
  · rw [forgot]
    exact mem_forgetOps held (fun o member defKind eq => term_not_def term operands available o
      (mem_drop_defs member).1 defKind (by injection eq))

private theorem forget_live {vc : VCode} {c : CheckCtx} (code : c.vc = vc)
    {preds : Array (Array Nat)} (cfg : vc.cfg = .ok (c.succs,preds))
    {b target j : Nat} {ss : Array Nat} {vb : VBlock} {T : MInst} {ops : Array Operand}
    (source : vc.blocks[b]? = some vb) (atLast : vb.insts.back? = some T) (operands : T.operands = .ok ops)
    (static : OpsOk ops T.clobbers) (successors : c.succs[b]? = some ss) (edge : ss[j]? = some target)
    (pred : preds[target]? = some #[b]) {x : Operand × Loc} (member : x ∈ termEdgeDefs vb j)
    {out : AState} (held : Sym.vreg x.1.vreg ∈ out.get x.2) :
    Sym.vreg x.1.vreg ∈ (c.edgeForget b target out).get x.2 := by
  rcases edgeForget_cases code source atLast operands out with same | ⟨jn,n,normal,selected,forgot⟩
  · rw [same]; exact held
  · rw [successors] at selected
    simp only [Option.bind_some] at selected
    have sameIndex := (preds_single cfg successors edge pred).2 jn selected
    subst jn
    obtain ⟨T',ops',last',_,operands',_,normalLive⟩ := termEdgeDefs_spec member
    rw [atLast] at last'
    cases last'
    rw [operands] at operands'
    cases operands'
    rw [forgot]
    exact mem_forgetOps held (fun o inside _ eq => kept_take_not_drop static (normalLive j n normal rfl) o inside (by injection eq))

/-- Actual predecessor terminator availability/kept results establish the
successor's dense-home invariant through real edge renaming, result stores and
entry copies. No state-content certificate is supplied for the successor. -/
theorem spill_entry_good_runs {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (code : c.vc = vc) (slots : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
    {preds : Array (Array Nat)} (cfg : vc.cfg = .ok (c.succs,preds))
    {b target j : Nat} {ss : Array Nat} {row : Array (Array Reg)} {args : Array Reg} {vb tb : VBlock}
    (source : vc.blocks[b]? = some vb) (targetBlock : vc.blocks[target]? = some tb)
    (successors : c.succs[b]? = some ss) (edge : ss[j]? = some target) (pred : preds[target]? = some #[b])
    (atRow : edges[b]? = some row) (atArgs : row[j]? = some args)
    (arity : args.size = tb.params.size) (argShape : ArgumentShape args) (paramShape : ParameterShape tb.params)
    {T : MInst} {ops : Array Operand} (atLast : vb.insts.back? = some T) (operands : T.operands = .ok ops)
    (static : OpsOk ops T.clobbers) {A wanted : Nat → Bool}
    (availability : EntryAvailAt vc vb j args tb (availInst T A) wanted)
    {out : AState} (good : GoodAt vc edges (availInst T A) out)
    (kept : ∀ x ∈ termEdgeDefs vb j,Sym.vreg x.1.vreg ∈ out.get x.2) :
    ∃ e,EdgeTransferAt c edges b target j args tb out e ∧
      Spill.Runs c tb 0 (spillEntryStoresAt (spillHomesAt vc edges) vc c.succs preds target ++
        spillEntryCopiesAt (spillHomesAt vc edges) vc edges c.succs preds target) e
        (fun k final => k = 0 ∧ GoodAt vc edges wanted final) := by
  obtain ⟨T',last',term⟩ := cfg_last cfg source
  rw [atLast] at last'
  cases last'
  have transfer := edgeAt_of_metadata code source targetBlock atRow atArgs arity argShape paramShape out
  have incoming : IncomingArgSymbolsAt vc edges vb j args (c.edgeForget b target out) := by
    intro i ar arAt
    rcases availability.arguments i ar arAt with available | ⟨x,member,num,cls⟩
    · obtain ⟨n,home⟩ := (spillHomesAt_spec vc edges).outgoing b j i row args ar atRow atArgs arAt
      have held : Sym.vreg ar.homeNum ∈ out.get (spillHomeAt (spillHomesAt vc edges) ar.homeNum ar.homeCls) := by
        rw [home_eq home]
        exact good.home _ _ n available (availability.argClasses i ar arAt available) home
      refine .inr ⟨?_,forget_available code source atLast operands term available held⟩
      intro x member
      have pair := live_kept atLast operands member
      have opMember : x.1 ∈ ops.toList := spillPairs_fst ops T.clobbers ▸ List.mem_map_of_mem (mem_keptPairs pair).1
      obtain ⟨m,xHome⟩ := (spillHomesAt_spec vc edges).code b vb source _
        (mem_blockVregs_op (back_get atLast).2 operands opMember)
      exact homes_ne xHome home (fun same => term_not_def term operands available x.1 opMember (mem_keptPairs pair).2 same.symm)
    · refine .inl ⟨x,member,num,cls,?_⟩
      rw [num]
      exact forget_live code cfg source atLast operands static successors edge pred member (kept x member)
  have classes : ∀ (i : Nat) (ar p : Reg),args[i]? = some ar → tb.params[i]? = some p →
      ∃ v w cl,ar = .vreg v cl ∧ p = .vreg w cl := by
    intro i ar p arAt pAt
    obtain ⟨v,rfl⟩ := argShape ar (Array.mem_toList_iff.mpr (Array.mem_of_getElem? arAt))
    obtain ⟨w,rfl⟩ := paramShape.1 p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? pAt))
    exact ⟨v,w,.int,rfl,rfl⟩
  have termStatic : ∀ i os,vb.insts.back? = some i → i.operands = .ok os → OpsOk os i.clobbers := by
    intro i os lastAt operandsAt
    rw [atLast] at lastAt
    cases lastAt
    rw [operands] at operandsAt
    cases operandsAt
    exact static
  refine ⟨_,transfer,(spill_entry_symbols_runs slots cfg source targetBlock successors edge pred atRow atArgs termStatic
    arity classes paramShape.2 transfer incoming good.save good.size).mono ?_⟩
  intro k final ⟨same,size,parameters,saves,frame⟩
  refine ⟨same,⟨size,?_,saves⟩⟩
  intro v cl n wantedV classV homeV
  by_cases parameter : v ∈ tb.params.toList.map Reg.homeNum
  · obtain ⟨p,member,num⟩ := List.mem_map.mp parameter
    obtain ⟨i,iBound,iValue⟩ := List.getElem_of_mem member
    have pAt : tb.params[i]? = some p := by simpa only [Array.getElem?_toList] using (List.getElem?_eq_getElem iBound).trans (congrArg some iValue)
    have argsBound : i < args.size := by rw [arity]; simpa using iBound
    have arAt : args[i]? = some args[i] := Array.getElem?_eq_getElem argsBound
    have pClass := availability.paramClasses p member (by rw [num]; exact wantedV)
    rw [num,classV] at pClass
    have cls : p.homeCls = cl := Option.some.inj pClass.symm
    have held := parameters i args[i] p arAt pAt
    rw [num,cls,home_eq homeV] at held
    exact held
  · have available := availability.ordinary v wantedV parameter
    have held := good.home v cl n available classV homeV
    have remembered := transfer.other (.stack n cl) v parameter
      (forget_available code source atLast operands term available held)
    rw [frame (.stack n cl) (fun _ eq => by cases eq) ?_ ?_ ?_]
    · exact remembered
    · intro i dl eq
      have bound := (spillHomesAt_spec vc edges).valid.1 _ _ homeV
      injection eq with sameN
      omega
    · intro p member eq
      obtain ⟨w,virtual⟩ := paramShape.1 p member
      have homeP := (spillHomesAt_spec vc edges).code target tb targetBlock _
        (mem_blockVregs_reg (List.mem_append_left _ member) virtual)
      obtain ⟨m,homeP⟩ := homeP
      have different : v ≠ p.homeNum := fun same => parameter (List.mem_map.mpr ⟨p,member,same.symm⟩)
      have ne := homes_ne homeV homeP (by simpa only [virtual,Reg.homeNum] using different)
      apply ne
      rw [home_eq homeV]
      simpa only [virtual,Reg.homeNum,Reg.homeCls] using eq
    · intro x member eq
      have pair := live_kept atLast operands member
      have opMember : x.1 ∈ ops.toList := spillPairs_fst ops T.clobbers ▸ List.mem_map_of_mem (mem_keptPairs pair).1
      obtain ⟨m,homeX⟩ := (spillHomesAt_spec vc edges).code b vb source _
        (mem_blockVregs_op (back_get atLast).2 operands opMember)
      apply homes_ne homeX homeV (fun same => term_not_def term operands available x.1 opMember (mem_keptPairs pair).2 same.symm)
      rw [home_eq homeV]
      exact eq

end Backend.Proof.PerEdgeSpill
