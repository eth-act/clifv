import FV.Backend.Proof.StockSourceResults
import FV.Backend.Proof.StockResults
import FV.Backend.Proof.IselCtlCallRules
import FV.E2E.ExtSemGuard

namespace Backend.Stock.Proof.DirectCallResult
open Backend Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A real source continuation keeps the call's memory and binds its one explicit result. -/
theorem source_result {s next : Clif.State} {rest : List Clif.Stmt} {source : Nat}
    {value : Clif.Val} {after : Clif.Mem}
    (continued : Clif.continueWith s rest [source] [value] after = .next next) :
    next.frame.regs source = some value ∧ next.mem = after ∧ next.callers = s.callers ∧
      ∀ other,other ≠ source → next.frame.regs other = s.frame.regs other := by
  simp only [Clif.continueWith,Clif.Regs.setMany] at continued
  cases continued
  exact ⟨Clif.Regs.set_same _ _ _,rfl,rfl,fun other different => by simp [Clif.Regs.set,different]⟩

/-- The existing callee postcondition carries an arbitrary memory effect and one source result. -/
theorem call_post_result {env : Clif.Env} {exts : List Clif.ExtFunc} {sigs : List Clif.Signature}
    {MR : MemRelT} {sym : String → Int → BitVec 64} {ext : Clif.ExtFunc}
    {uses : List CV} {before world : Arm.ArmState} {outs : List CV}
    (post : CallPost env exts sigs MR sym (some ext.name) uses before (outs,world))
    (member : ext ∈ exts) {g : List Clif.Val → Clif.Mem → Clif.Outcome}
    {slots : List (Clif.SlotId × Nat)} {cm after : Clif.Mem} {arguments : List Clif.Val}
    {value : Clif.Val} {result : Clif.AbiParam}
    (returns : ext.sig.returns = [result]) (found : env.extern ext.name = some g)
    (args : ArgsAt ext.sig arguments uses before) (memory : MR slots cm before)
    (called : g arguments cm = .returned [value] after) :
    ∃ output,outs = [output] ∧ VHolds value output ∧ MR slots after world := by
  have facts := post.1 ext member g slots cm uses arguments [value] after found
    (Or.inl ⟨rfl,rfl⟩) args memory called (by simp [returns])
  rw [returns] at facts
  cases outs with
  | nil => simp at facts
  | cons output tail =>
    have empty : tail = [] := by simpa using facts.1
    subst tail
    exact ⟨output,rfl,facts.2.1.2 0 value output rfl rfl,facts.2.2⟩

/-- The actual call operand binder writes the returned value to its fresh virtual destination. -/
theorem virtual_result (uses : List (Nat × Reg)) (destination : Nat) (output : CV) (values : Nat → CV) :
    vdefUpd (retOps uses ++ callDefOps [(.x 0,destination)]).toArray [output] values =
      fun key => if key = destination then output else values key := by
  rw [vdefUpd_call]
  rfl

/-- Static fixed constraints and the existing executed-operand postcondition give physical x0. -/
theorem physical_result {c : CheckCtx} {wh : String} {ops : Array Operand} {regs : Array Reg}
    {clobbers : List Reg} (checked : c.checkStatic wh ops (regs.map Loc.reg) clobbers = .ok ())
    {outs : List CV} {world : Arm.ArmState} {pair : Operand × Reg} {output : CV}
    (present : (pair,output) ∈ defRegs ops regs outs)
    (fixed : pair.1.con = .fixed (.x 0))
    (held : ∀ p ∈ defRegs ops regs outs,regVal world p.1.2 = p.2) :
    regVal world (.x 0) = output := by
  have member : pair ∈ (ops.zip regs).toList :=
    (List.mem_filter.mp (List.of_mem_zip present).1).1
  have pinned := (checkStatic_facts checked).2.1 (pair.1,Loc.reg pair.2)
    (by rw [pairs_regs]; exact List.mem_map_of_mem member)
  have same : pair.2 = .x 0 := Loc.reg.inj (pinned.2 _ fixed)
  rw [← same]
  exact held _ present

/-- A retained binder connects its original source mapping to the actual fresh destination. -/
structure Binding (ctx : Ctx) (state : Stock.State) (source : Nat) where
  root : Nat
  destination : Nat
  mapped : ctx.valueReg? source = some (.vreg root .int)
  resolved : Backend.lowerFunction.resolve state.alias (state.alias.size+1) (.vreg root .int) =
    .vreg destination .int

/-- The real alias update supplies the binding; no execution certificate enters the source input. -/
def Binding.of_fresh {ctx : Ctx} {state next : Stock.State} {source root destination : Nat}
    (mapped : ctx.valueReg? source = some (.vreg root .int))
    (bound : state.setAlias (.vreg root .int) (.vreg destination .int) = .ok next)
    (fresh : root < destination) (extent : state.alias.size ≤ destination) : Binding ctx next source :=
  ⟨root,destination,mapped,(resolve_bound_fresh bound fresh extent).1⟩

/-- The source and machine bind the same returned value and keep the actual callee memory. -/
theorem Binding.bind_result {ctx : Ctx} {state : Stock.State} {source : Nat}
    (binding : Binding ctx state source) {s next : Clif.State} {rest : List Clif.Stmt}
    {value : Clif.Val} {after : Clif.Mem} {output : CV} (held : VHolds value output)
    (continued : Clif.continueWith s rest [source] [value] after = .next next)
    (uses : List (Nat × Reg)) (values : Nat → CV) :
    next.frame.regs source = some value ∧ next.mem = after ∧
      VHolds value (vdefUpd (retOps uses ++ callDefOps [(.x 0,binding.destination)]).toArray
        [output] values binding.destination) ∧
      ctx.valueReg? source = some (.vreg binding.root .int) ∧
      Backend.lowerFunction.resolve state.alias (state.alias.size+1) (.vreg binding.root .int) =
        .vreg binding.destination .int := by
  have source := source_result continued
  exact ⟨source.1,source.2.1,by simpa only [virtual_result,ite_true] using held,
    binding.mapped,binding.resolved⟩

/-- Compose the original call postcondition with the actual source and virtual binders. -/
theorem Binding.returned {ctx : Ctx} {state : Stock.State} {source : Nat}
    (binding : Binding ctx state source) {env : Clif.Env} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {MR : MemRelT} {sym : String → Int → BitVec 64}
    {ext : Clif.ExtFunc} {uses : List CV} {before world : Arm.ArmState} {outs : List CV}
    (post : CallPost env exts sigs MR sym (some ext.name) uses before (outs,world))
    (member : ext ∈ exts) {g : List Clif.Val → Clif.Mem → Clif.Outcome}
    {slots : List (Clif.SlotId × Nat)} {cm after : Clif.Mem} {arguments : List Clif.Val}
    {value : Clif.Val} {result : Clif.AbiParam}
    (returns : ext.sig.returns = [result]) (found : env.extern ext.name = some g)
    (args : ArgsAt ext.sig arguments uses before) (memory : MR slots cm before)
    (called : g arguments cm = .returned [value] after)
    {s next : Clif.State} {rest : List Clif.Stmt}
    (continued : Clif.continueWith s rest [source] [value] after = .next next)
    (pairs : List (Nat × Reg)) (values : Nat → CV) :
    ∃ output,outs = [output] ∧ next.frame.regs source = some value ∧ next.mem = after ∧
      MR slots after world ∧ VHolds value output ∧
      VHolds value (vdefUpd (retOps pairs ++ callDefOps [(.x 0,binding.destination)]).toArray
        outs values binding.destination) := by
  obtain ⟨output,equal,held,related⟩ := call_post_result post member returns found args memory called
  have bound := binding.bind_result held continued pairs values
  exact ⟨output,equal,bound.1,bound.2.1,related,held,by simpa only [equal] using bound.2.2.1⟩

/-- The physical x0 postcondition gives the exact scalar source bits. -/
theorem physical_bits {world : Arm.ArmState} {output : CV} {word : BitVec 64}
    (physical : regVal world (.x 0) = output) (held : VHolds ⟨.i64,word⟩ output) :
    Arm.r (.GPR 0#5) world = word := by
  rw [← physical] at held
  simpa [VHolds,regVal,rnum,Clif.Ty.width] using held

/-- A bound result holds at the actual alias-resolved source location. -/
theorem resolved_source_result {ctx : Ctx} {state : Stock.State} {source root destination : Nat}
    (mapped : ctx.valueReg? source = some (.vreg root .int))
    (resolved : Backend.lowerFunction.resolve state.alias (state.alias.size+1) (.vreg root .int) =
      .vreg destination .int) (uses : List (Nat × Reg)) (output : CV) (values : Nat → CV) :
    ∃ reg,ctx.valueReg? source = some reg ∧
      Backend.lowerFunction.resolve state.alias (state.alias.size+1) reg = .vreg destination .int ∧
      vdefUpd (retOps uses ++ callDefOps [(.x 0,destination)]).toArray [output] values destination = output := by
  exact ⟨_,mapped,resolved,by rw [virtual_result]; simp⟩

end Backend.Stock.Proof.DirectCallResult
