import FV.Backend.Proof.IselExtern
import FV.Backend.Proof.PerEdgeSpillCopy
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.SpillArity
import FV.Backend.Proof.StockPolicy
import FV.Backend.Proof.PerEdgeAllocDriverSound

namespace Backend.Stock.Proof.SpillEntryFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgeSpill Backend.Proof.Spill
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
private def signature : Clif.Signature := {returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
private def table : Clif.ExnTable := {
  sig := 0,normal := ⟨1,[.ret 0,.val 0]⟩,items := [.tag 7 ⟨2,[.exn 0,.exn 1,.val 0]⟩] }
private def term (indirect : Bool) : Clif.Terminator :=
  if indirect then .tryCallIndirect 1 [] table else .tryCall 0 [] table
def function (indirect : Bool) : Clif.Function := {
  name := "stock_spill_try_entry",sig := signature,sigDecls := [(0,signature)],externs := [(0,{name := "callee",sig := signature})]
  blocks := [{id := 0,body := [⟨[0],.iconst .i64 9⟩] ++
      (if indirect then [⟨[1],.iconst .i64 4096⟩] else []),term := term indirect},
    {id := 1,params := [(2,.i64),(3,.i64)],term := .ret [2]},
    {id := 2,params := [(4,.i64),(5,.i64),(6,.i64)],term := .ret [4]}] }
private def pipeline (indirect : Bool) : Except String (Result × EdgeVCode × RFunc × AFunc) := do
  let result ← Stock.lower (function indirect)
  let prepared ← prepareAt result.code result.edgeArgs
  let rf ← allocResultAt prepared.code prepared.edges (.error "force indexed try fallback")
  let af ← lowerRFunc prepared.code rf
  pure (result,prepared,rf,af)

private def original (indirect : Bool) : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx (function indirect)).toOption.getD (sinkCtx,#[],default)
private theorem original_build (indirect : Bool) : Backend.buildCtx (function indirect) = .ok (original indirect) := by
  cases indirect <;> rfl
private theorem scope (indirect : Bool) : LowerScope (function indirect) := by
  cases indirect <;> apply lowerScope_of <;> decide +kernel
private theorem arity (indirect : Bool) : ArityOk (function indirect) := by
  cases indirect <;> apply arityOk_of <;> decide +kernel
private theorem dominated (indirect : Bool) : Dominated (function indirect) := by
  cases indirect with
  | false =>
    constructor
    · change ([0,2,3,4,5,6] : List Nat).Nodup; decide +kernel
    · intro ctx ranges st build bi b found
      have bound : bi < 3 := by have h := lt_of_getElem? found; simpa [function] using h
      have choices : bi = 0 ∨ bi = 1 ∨ bi = 2 := by omega
      rcases choices with rfl | rfl | rfl
      all_goals
        simp [function] at found
        subst b
        constructor
        · intro j stm present y member
          cases j <;> simp at present <;> subst stm <;> cases member
        · intro y member
          simp [abiTerm,Driver.termArgs,sretRet,sigRets,function,term,table,signature,
            Clif.ExnTable.vals,Clif.TryDest.vals] at member
          simp_all [availOf,function,defsBefore,defsFrom] <;>
            (rcases member with h | h <;> simp_all [availOf,function,defsBefore,defsFrom])
    · intro ctx ranges st build tl x available notLocal y member
      have fixed := (inFix_fixOk (f := function false) (ctx := ctx) (gn := id)).cand tl x available
      have values : x = 0 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by
        simpa [valueDefs,function] using fixed.2.2.2.1
      have context : ctx = (original false).1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans (original_build false)))
      rw [context] at member
      rcases values with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals change y ∈ ([] : List Nat) at member; cases member
  | true =>
    constructor
    · change ([0,1,2,3,4,5,6] : List Nat).Nodup; decide +kernel
    · intro ctx ranges st build bi b found
      have bound : bi < 3 := by have h := lt_of_getElem? found; simpa [function] using h
      have choices : bi = 0 ∨ bi = 1 ∨ bi = 2 := by omega
      rcases choices with rfl | rfl | rfl
      all_goals
        simp [function] at found
        subst b
        constructor
        · intro j stm present y member
          cases j with
          | zero => simp at present <;> subst stm <;> cases member
          | succ j => cases j <;> simp at present <;> subst stm <;> cases member
        · intro y member
          simp [abiTerm,Driver.termArgs,sretRet,sigRets,function,term,table,signature,
            Clif.ExnTable.vals,Clif.TryDest.vals] at member
          simp_all [availOf,function,defsBefore,defsFrom] <;>
            (rcases member with h | h <;> simp_all [availOf,function,defsBefore,defsFrom])
    · intro ctx ranges st build tl x available notLocal y member
      have fixed := (inFix_fixOk (f := function true) (ctx := ctx) (gn := id)).cand tl x available
      have values : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by
        simpa [valueDefs,function] using fixed.2.2.2.1
      have context : ctx = (original true).1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans (original_build true)))
      rw [context] at member
      rcases values with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals change y ∈ ([] : List Nat) at member; cases member

def retV (indirect : Bool) : Nat := if indirect then 194 else 193
def ordinaryV (indirect : Bool) : Nat := retV indirect + 9
def last (indirect : Bool) : MInst := .tryCall
  {dest := .reg (.vreg (retV indirect+8) .int),uses := [],
   defs := [(.x 0,.vreg (retV indirect) .int),(.x 1,.vreg (retV indirect+2) .int)]}
  {continuation := 1,handlers := [.tag 7 2],clobberAll := false,rets := 1}
def params (indirect handler : Bool) : Array Reg :=
  if handler then #[.vreg (retV indirect+5) .int,.vreg (retV indirect+6) .int,.vreg (retV indirect+7) .int]
  else #[.vreg (retV indirect+3) .int,.vreg (retV indirect+4) .int]
def args (indirect handler : Bool) : Array Reg :=
  if handler then #[.vreg (retV indirect) .int,.vreg (retV indirect+2) .int,.vreg (ordinaryV indirect) .int]
  else #[.vreg (retV indirect) .int,.vreg (ordinaryV indirect) .int]
def target (handler : Bool) : Nat := if handler then 2 else 1
def index (handler : Bool) : Nat := if handler then 0 else 1

def initial (indirect : Bool) (p : EdgeVCode) : AState :=
  AState.put (AState.put (AState.put (Array.replicate (stateSizeAt p.code p.edges) [])
    (.reg (.x 0)) [.vreg 900]) (.reg (.x 1)) [.vreg 901])
    (spillHomeAt (spillHomesAt p.code p.edges) (ordinaryV indirect) .int) [.vreg 902]

def Metadata (indirect : Bool) (p : EdgeVCode) : Prop :=
  p.code.blocks.size = 3 ∧
  (p.code.blocks[0]!).insts.back? = some (last indirect) ∧
  (p.code.blocks[1]!).params = params indirect false ∧
  (p.code.blocks[2]!).params = params indirect true ∧
  p.edges[0]? = some #[args indirect true,args indirect false] ∧
  p.code.cfg.toOption = some (#[#[2,1],#[],#[]],#[#[],#[0],#[0]]) ∧
  (initial indirect p).get (.reg (.x 0)) = [.vreg 900] ∧
  (initial indirect p).get (.reg (.x 1)) = [.vreg 901] ∧
  (initial indirect p).get (spillHomeAt (spillHomesAt p.code p.edges) (ordinaryV indirect) .int) = [.vreg 902]
private instance (indirect : Bool) (p : EdgeVCode) : Decidable (Metadata indirect p) := by
  unfold Metadata
  infer_instance
private def Observed (indirect : Bool) : Prop :=
  (pipeline indirect).toOption.map (fun q => decide (Metadata indirect q.2.1)) = some true
private theorem observed (indirect : Bool) : Observed indirect := by
  cases indirect <;> unfold Observed pipeline <;> decide +kernel

structure Output (indirect : Bool) where
  result : Result
  prepared : EdgeVCode
  rf : RFunc
  af : AFunc
  lowered : Stock.lower (function indirect) = .ok result
  scope : LowerScope (function indirect)
  dominated : Dominated (function indirect)
  arity : ArityOk (function indirect)
  prepare : prepareAt result.code result.edgeArgs = .ok prepared
  fallback : rf = spillAllocAt prepared.code prepared.edges
  accepted : checkAllocAt prepared.code prepared.edges rf = .ok ()
  physical : lowerRFunc prepared.code rf = .ok af
  metadata : Metadata indirect prepared

/-- Both complete original-scope/dominated TryCall sources execute checked
fallback allocation and physical lowering. The real normal and exception rows
carry fresh results alongside a live ordinary argument. -/
theorem try_fixture (indirect : Bool) : Nonempty (Output indirect) := by
  have actual := observed indirect
  unfold Observed at actual
  cases run : pipeline indirect with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok q =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at actual
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨prepared,prepare,h⟩ := Except.bind_ok h
    obtain ⟨rf,selected,h⟩ := Except.bind_ok h
    obtain ⟨af,physical,h⟩ := Except.bind_ok h
    cases h
    have accepted := PerEdge.allocResultAt_checked selected
    have fallback : rf = spillAllocAt prepared.code prepared.edges := by
      unfold allocResultAt checkedSpillAt at selected
      simp only [bind,Except.bind] at selected
      split at selected <;> cases selected
      rfl
    exact ⟨⟨result,prepared,rf,af,lowered,scope indirect,dominated indirect,arity indirect,
      prepare,fallback,accepted,physical,actual⟩⟩

end Backend.Stock.Proof.SpillEntryFixture
