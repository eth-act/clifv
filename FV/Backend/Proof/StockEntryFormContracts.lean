import FV.Backend.Proof.StockCoreFormContracts
import FV.Backend.Proof.LowerCover

namespace Backend.Stock.Proof.Coverage.EntryDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def EntryAcc := List (Reg × Reg) × Array MInst
private def EntryArg := ((Nat × Clif.Ty) × ArgLoc) × Nat
private def entryStep (ctx : Ctx) (uses : Array UseState) (arg : EntryArg) (acc : EntryAcc) :
    Except String (ForInStep EntryAcc) :=
  let pairs := acc.1
  let loads := acc.2
  match arg with
  | (((v,_),loc),bytes) =>
    if uses[v]! == .unused then pure (.yield (pairs,loads)) else
    match ctx.valueReg? v with
    | some r =>
      match loc with
      | .reg p => pure (.yield (pairs ++ [(r,p)],loads))
      | .stack off => pure (.yield (pairs,loads.push (.load (loadOpOfBytes bytes) r (.fpOffset ((16 : Int)+(off : Int))) trustedFlags)))
    | none => do
      throw s!"unknown value v{v}"
      pure (.yield (pairs,loads))

private theorem entryStep_keeps {ctx : Ctx} {uses : Array UseState}
    (mapped : ∀ v r,ctx.valueReg? v = some r → ∃ n,r = .vreg n .int)
    {arg : EntryArg} {acc next : EntryAcc}
    (covered : ∀ i ∈ acc.2.toList,Covered i = true)
    (run : entryStep ctx uses arg acc = .ok (.yield next)) :
    ∀ i ∈ next.2.toList,Covered i = true := by
  rcases arg with ⟨⟨⟨v,ty⟩,loc⟩,bytes⟩
  rcases acc with ⟨pairs,loads⟩
  unfold entryStep at run
  dsimp only at run
  split at run
  · cases run; exact covered
  · cases lookup : ctx.valueReg? v with
    | none => simp only [lookup] at run; cases run
    | some r =>
      obtain ⟨n,rfl⟩ := mapped v r lookup
      simp only [lookup] at run
      cases loc with
      | reg p => cases run; exact covered
      | stack off =>
        cases run
        intro i member
        simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
        rcases member with old | rfl
        · exact covered i old
        · exact covered_load bytes n (16+off)

private theorem entryStep_no_done {ctx : Ctx} {uses : Array UseState}
    {arg : EntryArg} {acc next : EntryAcc} : entryStep ctx uses arg acc ≠ .ok (.done next) := by
  intro run
  rcases arg with ⟨⟨⟨v,ty⟩,loc⟩,bytes⟩
  rcases acc with ⟨pairs,loads⟩
  unfold entryStep at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run

private theorem entryLoop_keeps {ctx : Ctx} {uses : Array UseState}
    (mapped : ∀ v r,ctx.valueReg? v = some r → ∃ n,r = .vreg n .int)
    {args : List EntryArg} {acc next : EntryAcc}
    (covered : ∀ i ∈ acc.2.toList,Covered i = true)
    (run : forIn args acc (entryStep ctx uses) = .ok next) :
    ∀ i ∈ next.2.toList,Covered i = true := by
  exact Prep.forIn_inv _ args (fun _ acc => ∀ i ∈ acc.2.toList,Covered i = true)
    (fun k x before after member held step => entryStep_keeps mapped held step)
    (fun _ _ _ => entryStep_no_done) acc next covered run

/-- The actual entry assembler adds only covered ABI argument materialization
and stack loads to covered body code; every mapped parameter is virtual-int.
Nonentry blocks preserve their covered body instruction sequence. -/
theorem stock_assemble_form_coverage {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    (mapped : ∀ v r,ctx.valueReg? v = some r → ∃ n,r = .vreg n .int)
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {paramBytes : List Nat} {uses : Array UseState} {bodyCode : Array MInst} {block : VBlock}
    (covered : ∀ i ∈ bodyCode.toList,Covered i = true)
    (run : assembleOriginalBlock ctx f b bi label targets outgoing paramBytes uses bodyCode = .ok block) :
    ∀ i ∈ block.insts.toList,Covered i = true := by
  let finish (code : Array MInst) : Except String VBlock := do
    let params ← if bi == 0 then pure #[] else
      b.params.toArray.mapM fun (v,_) =>
        match ctx.valueReg? v with
        | some r => pure r
        | none => throw s!"unknown value v{v}"
    pure {label,insts := code,params,branchArgs := if targets.size == 1 then outgoing[0]! else #[]}
  have normal : assembleOriginalBlock ctx f b bi label targets outgoing paramBytes uses bodyCode =
      (if bi == 0 then do
        let (locs,_) ← sigArgLocs f.sig
        let acc ← forIn ((b.params.zip locs).zip paramBytes) ([],#[]) (entryStep ctx uses)
        let pairs := acc.1
        let loads := acc.2
        if !pairs.isEmpty then finish (#[.args pairs] ++ loads ++ bodyCode) else finish (loads ++ bodyCode)
      else finish bodyCode) := by
    unfold assembleOriginalBlock
    dsimp only [finish]
    congr 1
    congr 1
    funext locations
    rcases locations with ⟨locs,n⟩
    dsimp only
    congr 1
    congr 1
    funext arg acc
    rcases arg with ⟨⟨⟨v,ty⟩,loc⟩,bytes⟩
    rcases acc with ⟨pairs,loads⟩
    unfold entryStep
    dsimp only
    cases ctx.valueReg? v <;> rfl
  have finish_keeps {code : Array MInst} (forms : ∀ i ∈ code.toList,Covered i = true)
      (call : finish code = .ok block) : ∀ i ∈ block.insts.toList,Covered i = true := by
    unfold finish at call
    dsimp only at call
    repeat' first
      | (solve | cases call)
      | simp only [bind,Except.bind,pure,Except.pure] at call
      | split at call
    all_goals cases call; exact forms
  rw [normal] at run
  split at run
  · cases locations : sigArgLocs f.sig with
    | error e => simp only [locations,bind,Except.bind] at run; cases run
    | ok answer =>
      rcases answer with ⟨locs,size⟩
      simp only [locations,bind,Except.bind] at run
      cases loop : forIn ((b.params.zip locs).zip paramBytes) ([],#[]) (entryStep ctx uses) with
      | error e => simp only [loop] at run; cases run
      | ok answer =>
        rcases answer with ⟨pairs,loads⟩
        simp only [loop] at run
        have shared : (if !pairs.isEmpty then finish (#[.args pairs] ++ loads ++ bodyCode) else finish (loads ++ bodyCode)) =
            finish (if !pairs.isEmpty then #[.args pairs] ++ loads ++ bodyCode else loads ++ bodyCode) := by
          split <;> rfl
        rw [shared] at run
        apply finish_keeps ?_ run
        have loadsCovered : ∀ i ∈ loads.toList,Covered i = true :=
          entryLoop_keeps mapped (fun i member => by cases member) loop
        intro i member
        split at member
        · simp only [Array.toList_append,Array.toList_push,Array.toList_empty,List.mem_append,List.mem_singleton] at member
          rcases member with (rfl | old) | body
          · rfl
          · exact loadsCovered i old
          · exact covered i body
        · simp only [Array.toList_append,List.mem_append] at member
          rcases member with old | body
          · exact loadsCovered i old
          · exact covered i body
  · exact finish_keeps covered run

end Backend.Stock.Proof.Coverage.EntryDraft
