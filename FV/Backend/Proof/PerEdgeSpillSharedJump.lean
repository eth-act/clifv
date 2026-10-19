import FV.Backend.Proof.PerEdgeSpillPreState

namespace Backend.Proof.PerEdgeSpill
open Backend Backend.Proof.Spill Backend.Stock.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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
  exact different (spillHomeKeyAt_injective ((spillHomesAt_spec vc edges).valid.2 _ _ _ left right)).1

private theorem jump_runs {c : CheckCtx} {vb : VBlock} {k : Nat} {label : Label} {a : AState}
    (before : k ≠ vb.insts.size) (instruction : vb.insts[k]? = some (.jump label)) (h : SpillHomesAt) :
    Spill.Runs c vb k (spillInstAt h k (.jump label)) a (fun k' a' => k' = k+1 ∧ a' = a) := by
  have step : c.stepOp s!"block {vb.label} inst {k}" (.jump label) #[] #[] a = .ok a := by
    simp [CheckCtx.stepOp,CheckCtx.checkStatic,ensure,transferOp,atPos,defineAll,clobberAll,retCheck,
      MInst.clobbers,MInst.keptDefs,MInst.isBranch,forgetDefs]
    have filterTrue : (fun x : List Sym => x.filter (fun _ => true)) = id :=
      funext fun x => List.filter_eq_self.mpr (fun _ _ => rfl)
    rw [filterTrue,Array.map_id]
  have shape : spillInstAt h k (.jump label) = [.op k #[]] := by
    unfold spillInstAt
    rw [show (MInst.jump label).operands = .ok #[] from rfl]
    simp [spillLocs,MInst.clobbers,MInst.isTerminator,MInst.isBranch,MInst.keptDefs]
  rw [shape]
  exact Spill.Runs.op before instruction rfl step ⟨rfl,rfl⟩

/-- Shared-target argument copies, the actual operandless jump and actual edge
renaming establish the successor invariant. Copies retain argument symbols;
only the edge transfer introduces parameter symbols, including cyclic copies.
The canonical shared pre-entry state is included in that actual edge output. -/
theorem spill_shared_jump_runs {vc : VCode} {edges : Array (Array (Array Reg))} {c : CheckCtx}
    (code : c.vc = vc) (slots : c.rf.spillSlots = (spillHomesAt vc edges).size + maxArgsAt edges)
    {preds : Array (Array Nat)} {post body : Nat → Nat → Bool}
    {b target k : Nat} {vb tb : VBlock} {label : Label} {row : Array (Array Reg)} {args : Array Reg}
    (notEntry : target ≠ 0) (source : vc.blocks[b]? = some vb) (targetBlock : vc.blocks[target]? = some tb)
    (successors : c.succs[b]? = some #[target]) (shared : 1 < (preds[target]?.getD #[]).size)
    (atRow : edges[b]? = some row) (atArgs : row[0]? = some args)
    (arity : args.size = tb.params.size) (argShape : ArgumentShape args) (paramShape : ParameterShape tb.params)
    (atLast : vb.insts.back? = some (.jump label)) (instruction : vb.insts[k]? = some (.jump label))
    {A : Nat → Bool} (availability : EntryAvailAt vc vb 0 args tb A (body target))
    {a : AState} (good : GoodAt vc edges A a) :
    Spill.Runs c vb k (jumpCopies vc edges c.succs preds b ++ spillInstAt (spillHomesAt vc edges) k (.jump label)) a
      (fun k' out => k' = k+1 ∧ ∃ e,EdgeTransferAt c edges b target 0 args tb out e ∧
        GoodAt vc edges (body target) e ∧
        (preEntryStateAt vc edges c.succs preds post body target).le e = true) := by
  have before : k ≠ vb.insts.size := by have := (Array.getElem?_eq_some_iff.mp instruction).1; omega
  have noDefs : termEdgeDefs vb 0 = [] := by unfold termEdgeDefs; rw [atLast]; rfl
  have argAvailable : ∀ (i : Nat) (ar : Reg),args[i]? = some ar → A ar.homeNum = true := by
    intro i ar found
    rcases availability.arguments i ar found with yes | ⟨x,member,_⟩
    · exact yes
    · rw [noDefs] at member; cases member
  have classes : ∀ (i : Nat) (ar p : Reg),args[i]? = some ar → tb.params[i]? = some p →
      ∃ v w cl,ar = .vreg v cl ∧ p = .vreg w cl := by
    intro i ar p arAt pAt
    obtain ⟨v,rfl⟩ := argShape ar (Array.mem_toList_iff.mpr (Array.mem_of_getElem? arAt))
    obtain ⟨w,rfl⟩ := paramShape.1 p (Array.mem_toList_iff.mpr (Array.mem_of_getElem? pAt))
    exact ⟨v,w,.int,rfl,rfl⟩
  rw [spill_jump_route successors shared targetBlock atRow atArgs]
  refine Spill.Runs.append (spillArgMovesAt_runs slots atRow atArgs targetBlock arity classes paramShape.2 before good.size)
    fun next copied ⟨same,size,values,frame⟩ => ?_
  subst next
  refine (jump_runs before instruction (spillHomesAt vc edges)).mono ?_
  intro next out ⟨same,unchanged⟩
  subst out
  have transfer := edgeAt_of_metadata code source targetBlock atRow atArgs arity argShape paramShape copied
  have forget : c.edgeForget b target copied = copied := by
    unfold CheckCtx.edgeForget
    rw [code,source]
    simp only [atLast]
    rfl

  have edgeGood : GoodAt vc edges (body target)
      ((c.edgeForget b target copied).parCopy (tb.params.toList.map Reg.homeNum) (args.toList.map Reg.homeNum)) := by
    constructor
    · exact transfer.size.trans size
    · intro v cl n wantedV classV homeV
      by_cases parameter : v ∈ tb.params.toList.map Reg.homeNum
      · obtain ⟨p,member,num⟩ := List.mem_map.mp parameter
        obtain ⟨i,iBound,iValue⟩ := List.getElem_of_mem member
        have pAt : tb.params[i]? = some p := by
          simpa only [Array.getElem?_toList] using (List.getElem?_eq_getElem iBound).trans (congrArg some iValue)
        have argsBound : i < args.size := by rw [arity]; simpa using iBound
        have arAt : args[i]? = some args[i] := Array.getElem?_eq_getElem argsBound
        have available := argAvailable i args[i] arAt
        obtain ⟨m,homeAr⟩ := (spillHomesAt_spec vc edges).outgoing b 0 i row args args[i] atRow atArgs arAt
        have held := good.home _ _ m available (availability.argClasses i args[i] arAt available) homeAr
        have moved : Sym.vreg (args[i]).homeNum ∈ copied.get (spillHomeAt (spillHomesAt vc edges) p.homeNum p.homeCls) := by
          rw [values i args[i] p arAt pAt,home_eq homeAr]
          exact held
        have renamed := transfer.parameter i args[i] p arAt pAt _ (by rw [forget]; exact moved)
        have pClass := availability.paramClasses p member (by rw [num]; exact wantedV)
        rw [num,classV] at pClass
        have cls : p.homeCls = cl := Option.some.inj pClass.symm
        rw [num,cls,home_eq homeV] at renamed
        exact renamed
      · apply transfer.other (.stack n cl) v parameter
        rw [forget,frame (.stack n cl) (fun _ eq => by cases eq) ?_ ?_]
        · exact good.home v cl n (availability.ordinary v wantedV parameter) classV homeV
        · intro i dl eq
          have bound := (spillHomesAt_spec vc edges).valid.1 _ _ homeV
          injection eq with sameN
          omega
        · intro p member eq
          obtain ⟨w,virtual⟩ := paramShape.1 p member
          obtain ⟨m,homeP⟩ := (spillHomesAt_spec vc edges).code target tb targetBlock _
            (mem_blockVregs_reg (List.mem_append_left _ member) virtual)
          have different : v ≠ p.homeNum := fun same => parameter (List.mem_map.mpr ⟨p,member,same.symm⟩)
          apply homes_ne homeV homeP (by simpa only [virtual,Reg.homeNum] using different)
          rw [home_eq homeV]
          simpa only [virtual,Reg.homeNum,Reg.homeCls] using eq
    · intro r member
      apply transfer.entry (.save r) r
      rw [frame (.save r) (fun _ eq => by cases eq) (fun _ _ eq => by cases eq) ?_]
      · exact good.save r member
      · intro p member eq
        obtain ⟨v,rfl⟩ := paramShape.1 p member
        obtain ⟨n,homeP⟩ := (spillHomesAt_spec vc edges).code target tb targetBlock _
          (mem_blockVregs_reg (List.mem_append_left _ member) rfl)
        dsimp only [Reg.homeNum,Reg.homeCls,Prod.fst,Prod.snd] at eq homeP
        rw [home_eq homeP] at eq
        cases eq
  have notUnique : ∀ b,preds[target]? ≠ some #[b] := by
    intro b eq
    rw [eq] at shared
    change 1 < 1 at shared
    omega
  exact ⟨same,_,transfer,edgeGood,preEntryStateAt_shared_le notEntry notUnique edgeGood⟩

end Backend.Proof.PerEdgeSpill
