import FV.Backend.Proof.PerEdgeSpillCopy
import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.PerEdgeAllocDriverSound

namespace Backend.Stock.Proof.IndexedSpillFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgeSpill Backend.Proof.Spill
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def function : Clif.Function := {
  name := "stock_indexed_spill_cycle"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩],
    returns := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64),(13,.i64)],term := .jump ⟨1,[7,13]⟩},
    {id := 1,params := [(31,.i64),(47,.i64)],term := .brif 31 ⟨1,[47,31]⟩ ⟨2,[31,47]⟩},
    {id := 2,params := [(59,.i64),(61,.i64)],term := .ret [59,61]}] }
private def pipeline : Except String (Result × EdgeVCode × RFunc × AFunc) := do
  let result ← Stock.lower function
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force indexed cycle fallback")
  let af ← lowerRFunc prepared.code rf
  pure (result,prepared,rf,af)
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem dominated : Dominated function := by
  constructor
  · change ([7,13,31,47,59,61] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    have bound : bi < 3 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals
      simp [function] at found
      subst b
      constructor
      · intro j stm present; simp at present
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member
        simp [availOf,function,defsBefore,defsFrom]
        rcases member with same | rest
        · exact Or.inl same
        · first
          | exact Or.inr (Or.inl rest)
          | rcases rest with h | h | h <;> first | exact Or.inl h | exact Or.inr (Or.inl h)
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have values : x = 7 ∨ x = 13 ∨ x = 31 ∨ x = 47 ∨ x = 59 ∨ x = 61 := by
      simpa [valueDefs,function] using fixed.2.2.2.1
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    rcases values with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals change y ∈ ([] : List Nat) at member; cases member

def initial (prepared : EdgeVCode) : AState :=
  AState.put (AState.put (Array.replicate (stateSizeAt prepared.code prepared.edges) [])
    (spillHomeAt (spillHomesAt prepared.code prepared.edges) 194 .int) [.vreg 194])
    (spillHomeAt (spillHomesAt prepared.code prepared.edges) 195 .int) [.vreg 195]
private def Observed : Prop := pipeline.toOption.map (fun q => decide (
  q.2.1.code.blocks.size = 4 ∧
  q.2.1.edges[3]? = some #[#[Reg.vreg 195 .int,Reg.vreg 194 .int]] ∧
  (q.2.1.code.blocks[1]!).params = #[Reg.vreg 194 .int,Reg.vreg 195 .int] ∧
  (q.2.1.code.blocks[3]!).insts.size = 1 ∧
  q.2.2.1.blocks[3]? = some ((spillArgMovesAt (spillHomesAt q.2.1.code q.2.1.edges)
    #[Reg.vreg 195 .int,Reg.vreg 194 .int] (q.2.1.code.blocks[1]!).params ++ [RItem.op 0 #[]]).toArray) ∧
  (initial q.2.1).get (spillHomeAt (spillHomesAt q.2.1.code q.2.1.edges) 194 .int) = [.vreg 194] ∧
  (initial q.2.1).get (spillHomeAt (spillHomesAt q.2.1.code q.2.1.edges) 195 .int) = [.vreg 195])) = some true
/-- One kernel evaluation of the pipeline for all seven observations (seven separate
`decide +kernel` checks re-ran the whole pipeline each: 748 s → 66 s, same peak). -/
private theorem observed : Observed := by
  unfold Observed
  decide +kernel

/-- Complete executed fixture, separated from generic proof composition so its
kernel evaluation is reused while checker invariants are developed. -/
structure Output where
  result : Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc
  lowered : Stock.lower function = .ok result
  scope : LowerScope function
  dominated : Dominated function
  prepare : prepareAt result.code result.edgeArgs = .ok prepared
  fallback : rf = spillAllocAt prepared.code prepared.edges
  accepted : checkAllocAt prepared.code prepared.edges rf = .ok ()
  physical : lowerRFunc prepared.code rf = .ok af
  blockCount : prepared.code.blocks.size = 4
  edgeRow : prepared.edges[3]? = some #[#[Reg.vreg 195 .int,Reg.vreg 194 .int]]
  params : (prepared.code.blocks[1]!).params = #[Reg.vreg 194 .int,Reg.vreg 195 .int]
  codeSize : (prepared.code.blocks[3]!).insts.size = 1
  installedCopy : rf.blocks[3]? = some ((spillArgMovesAt (spillHomesAt prepared.code prepared.edges)
    #[Reg.vreg 195 .int,Reg.vreg 194 .int] (prepared.code.blocks[1]!).params ++ [RItem.op 0 #[]]).toArray)
  firstSymbol : (initial prepared).get (spillHomeAt (spillHomesAt prepared.code prepared.edges) 194 .int) = [.vreg 194]
  secondSymbol : (initial prepared).get (spillHomeAt (spillHomesAt prepared.code prepared.edges) 195 .int) = [.vreg 195]

/-- A complete original-scope/dominated Stock loop successfully executes
preparation, actual checked spill allocation and physical lowering; its real
synthetic edge has the nonempty two-home cycle and initialized source symbols. -/
theorem cycle_fixture : Nonempty Output := by
  have actual := observed
  unfold Observed at actual
  cases run : pipeline with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok q =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    obtain ⟨blockCount,edgeRow,params,codeSize,installedCopy,firstSymbol,secondSymbol⟩ := actual
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨prepared,prepare,h⟩ := Except.bind_ok h
    obtain ⟨rf,selected,h⟩ := Except.bind_ok h
    obtain ⟨af,physical,h⟩ := Except.bind_ok h
    cases h
    dsimp only at blockCount edgeRow params codeSize installedCopy firstSymbol secondSymbol
    have accepted := PerEdge.allocResultAt_checked selected
    have fallback : rf = spillAllocAt prepared.code prepared.edges := by
      unfold allocResultAt checkedSpillAt at selected
      simp only [bind,Except.bind] at selected
      split at selected <;> cases selected
      rfl
    exact ⟨⟨result,prepared,rf,af,lowered,scope,dominated,prepare,fallback,accepted,physical,
      blockCount,edgeRow,params,codeSize,installedCopy,firstSymbol,secondSymbol⟩⟩

end Backend.Stock.Proof.IndexedSpillFixture

