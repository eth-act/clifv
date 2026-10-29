module

public import FV.Backend.Proof.StockLogicalNotrap
public import FV.Backend.Proof.StockLogicalRecordWitness

@[expose] public section

namespace Backend.Stock.Proof.LogicalBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
open Backend.Stock.Proof.LogicalSelected Backend.Stock.Proof.LogicalSemantics
set_option autoImplicit false
set_option Elab.async false

/-- The all-fuel nontrapping theorem is inhabited by an actual nonempty logical
function with independent argument values and a successful returned source run. -/
theorem logical_source_notrap_witness (u v : BitVec 64) :
    ∃ (f : Clif.Function) (result : Result) (s : Clif.State),
      Stock.lower f = .ok result ∧ LowerScope f ∧ s.frame.body ≠ [] ∧
      Clif.enterFunc f [⟨.i64,u⟩,⟨.i64,v⟩] Clif.Mem.empty = .ok (s.frame,s.mem) ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 s =
        .returned [⟨.i64,u ||| v⟩] Clif.Mem.empty ∧
      ∀ fuel code, Clif.runLoop Clif.Env.empty {funcs := []} fuel s ≠ .trapped code := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness .registers
  let f := formFunction .registers
  let b := f.blocks[0]!
  let fr : Clif.Frame := {
    func := f
    regs := (Clif.Regs.empty.set 7 ⟨.i64,u⟩).set 31 ⟨.i64,v⟩
    slots := []
    body := b.body
    term := b.term }
  let s : Clif.State := ⟨fr,[],Clif.Mem.empty⟩
  have family : ∀ stm ∈ s.frame.body, Family stm.inst := by
    intro stm member
    change stm ∈ [⟨[100],.binary .bor .i64 7 31⟩] at member
    have equal := List.mem_singleton.mp member
    subst stm
    exact Or.inr (Or.inr ⟨.bor,.i64,7,31,rfl⟩)
  refine ⟨f,input.result,s,input.run,formScope .registers,(by change ([⟨[100],.binary .bor .i64 7 31⟩] : List Clif.Stmt) ≠ []; simp),rfl,rfl,?_⟩
  intro fuel code
  exact logical_source_notrap fuel s rfl family (xs := [100]) rfl code

end Backend.Stock.Proof.LogicalBody
