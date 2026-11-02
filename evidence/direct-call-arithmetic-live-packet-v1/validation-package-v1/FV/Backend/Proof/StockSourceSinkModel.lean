import FV.Backend.Proof.StockCoverageInvariant
import FV.Backend.Proof.LogicImmComplete
import FV.Backend.Proof.StockCoverageCtor
import FV.Backend.Proof.StockCoverageOracle
import FV.Backend.Proof.IselFlowInst
import FV.Backend.Proof.StockSourceSinkTable
import FV.Backend.Proof.StockSinkFrame

/-! Real source-instruction sink provenance instantiates the generic coverage
invariant. Terminator placeholders cannot be produced as sink targets. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Cov Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

private theorem sinkable_result {ctx : Ctx} {t : Term} (id : t.id = TId.is_sinkable_inst)
    {args : List V} {st next : State} {v : V}
    (run : Stock.externCtor ctx t args st = .ok (v,next)) :
    ∃ x i,ctx.defInst? x = some i ∧ v = .inst i ∧ next = st := by
  rcases t with ⟨tid,name,targs,ret,kind,pos⟩
  dsimp only at id
  subst tid
  cases args with
  | nil => cases run
  | cons arg rest =>
    cases rest with
    | cons a rest =>
      cases arg <;> cases a <;> cases run
    | nil =>
      cases arg <;> try (cases run)
      rename_i x
      change (match source ctx st x with
        | some (i,true) => ExtResult.ok (.inst i,st)
        | _ => ExtResult.fail) = ExtResult.ok (v,next) at run
      cases found : source ctx st x with
      | none => rw [found] at run; cases run
      | some pair =>
        obtain ⟨i,flag⟩ := pair
        cases flag with
        | false => rw [found] at run; cases run
        | true =>
          rw [found] at run
          cases run
          refine ⟨x,i,?_,rfl,rfl⟩
          unfold source at found
          cases lookup : ctx.defInst? x with
          | none => simp only [lookup,bind,Option.bind] at found; cases found
          | some j =>
            simp only [lookup,bind,Option.bind] at found
            split at found
            · have same := (Prod.mk.inj (Option.some.inj found)).1
              subst j
              rfl
            · split at found
              · have same := (Prod.mk.inj (Option.some.inj found)).1
                subst j
                rfl
              · cases found

private theorem sourceSink_value_sound {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {as : List AW} {vs : List V} {term : Term}
    {v : V} {st next : State} (held : Holds2 f (sourceIdentityCtx ctx) as vs)
    (pre : sourceSinkPre term.id as = true)
    (run : (Stock.sem ctx).ctor term vs st = .ok (v,next)) :
    γ f (sourceIdentityCtx ctx) (sourceSinkActor term.id as) v := by
  by_cases eligible : term.id = TId.is_sinkable_inst
  · rw [sourceSinkActor,if_pos (by simpa only [beq_iff_eq] using eligible)]
    obtain ⟨x,i,defined,rfl,rfl⟩ := sinkable_result eligible run
    obtain ⟨info,lookup,member⟩ := mapped.defInst x i defined
    obtain ⟨inst,clif⟩ := Option.isSome_iff_exists.mp (mapped.defClif x i info defined lookup)
    exact ⟨⟨i,info,inst,rfl,lookup,clif,mapped.data i info inst lookup clif⟩,rfl,rfl⟩
  · rw [sourceSinkActor,if_neg (by simpa only [beq_iff_eq] using eligible)]
    have accepted : apre term.id as = true := by
      have accepted := pre
      simp only [sourceSinkPre,noOpportunityPre,Bool.and_eq_true] at accepted
      exact accepted.1.2
    exact ctor_value_sound mapped logicImmComplete held accepted run

private theorem one_input {f : Clif.Function} {ctx : Ctx} {a : AW} {vs : List V}
    (held : Holds2 f ctx [a] vs) : ∃ v,vs = [v] ∧ γ f ctx a v := by
  cases vs with
  | nil => cases held
  | cons v rest =>
    cases rest with
    | nil => exact ⟨v,rfl,held.1⟩
    | cons w rest => cases held.2

/-- The typed sink target preserves any sunk bit whose installed slot has no
original CLIF instruction, including every original terminator placeholder. -/
theorem stock_ctor_terminal_unsunk {f : Clif.Function} {ctx : Ctx}
    {as : List AW} {vs : List V} {term : Term} {v : V} {st next : State} {ti : Nat}
    (slot : ctx.insts[ti]!.clif = none)
    (held : Holds2 f (sourceIdentityCtx ctx) as vs)
    (pre : sourceSinkPre term.id as = true) (unsunk : st.sunk[ti]! = false)
    (run : (Stock.sem ctx).ctor term vs st = .ok (v,next)) :
    next.sunk[ti]! = false := by
  by_cases sink : term.id = TId.sink_inst
  · have args : as = [.xv .inst] := by
      have second := pre
      simp only [sourceSinkPre,sink,Bool.and_eq_true,beq_self_eq_true,ite_true] at second
      have second := second.2
      split at second
      · rfl
      · cases second
    subst as
    obtain ⟨value,rfl,described⟩ := one_input held
    obtain ⟨i,info,inst,rfl,lookup,clif,data⟩ := described.1
    change ctx.insts[i]? = some info at lookup
    have different : ti ≠ i := by
      intro same
      subst ti
      have installed : ctx.insts[i]!.clif = some inst := by
        simpa only [getElem!_def,lookup,Option.getD_some] using clif
      rw [slot] at installed
      cases installed
    have actual : Stock.externCtor ctx T.sink_inst [.inst i] st = .ok (v,next) := by
      change Stock.externCtor ctx term [.inst i] st = .ok (v,next) at run
      unfold Stock.externCtor at run
      simp only [sink] at run
      exact run
    have state := (sink_accepted actual).2.2.2.2
    rw [state]
    dsimp only
    simpa [getElem!_def,Array.getElem?_setIfInBounds,different,Ne.symm different] using unsunk
  · rw [stock_ctor_noSink sink run]
    exact unsunk

/-- Inhabited real-state model for preservation of an original empty-CLIF slot. -/
def sourceSinkModel {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    (clean : Clean (sourceIdentityCtx ctx)) (ti : Nat) (slot : ctx.insts[ti]!.clif = none) :
    Invariant.Model sourceSinkActor sourceSinkPre program f ctx where
  Is := fun st => st.sunk[ti]! = false
  source := covModel logicImmComplete mapped.identityView clean sinkState.base
  ctor := by
    intro t term lookup as vs value st next held invariant pre run
    exact ⟨sourceSink_value_sound mapped held pre run,stock_ctor_terminal_unsunk slot held pre invariant run⟩
  oracle := oracle_sound _
end Backend.Stock.Proof.Coverage
