from pathlib import Path
root=Path('/tmp/stock-div-next-staged');p=root/'FV/E2E/StockMixedDivFixtures.lean';p.parent.mkdir(parents=True,exist_ok=True)
p.write_text('''import FV.E2E.StockHighMulFixtures
import FV.E2E.StockDivFixtures
namespace E2E.StockMixedDivNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
abbrev operations := StockDivNIWitness.operations
abbrev arguments := StockDivNIWitness.arguments

def divisor (safe : Bool) : Nat := if safe then 5001 else 8

def frontBody (config : Configuration) (safe : Bool) : List Clif.Stmt :=
  (StockHighMulNIWitness.function config).blocks[0]!.body ++
    (if safe then [⟨[5001],.iconst (valueType config) 2⟩] else [])

/-- The full live scalar computation is the dividend. The divisor is the original
ninth stack argument, or an original source constant for the safe selected roots. -/
def function (config : Configuration) (op : Clif.DivOp) (safe : Bool) : Clif.Function :=
  let old := StockHighMulNIWitness.function config
  let name := "stock_mixed_div_" ++ (match op with | .sdiv => "sdiv" | .udiv => "udiv" | .srem => "srem" | .urem => "urem") ++ (if safe then "_two" else "")
  {old with name := name,blocks := old.blocks.map fun b =>
    {b with body := b.body ++ (if safe then [⟨[5001],.iconst (valueType config) 2⟩] else []) ++
      [⟨[5000],.div op (valueType config) 4008 (divisor safe)⟩],term := .ret [5000]}}

def frame (config : Configuration) (op : Clif.DivOp) (safe : Bool)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) : Clif.Frame := {
  func := function config op safe
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments config input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := (function config op safe).blocks[0]!.body
  term := .ret [5000] }
end E2E.StockMixedDivNIWitness
''')
s=Path('FV/E2E/StockDivWitness.lean').read_text().replace('import FV.E2E.StockDivFixtures','import FV.E2E.StockMixedDivFixtures\nimport FV.E2E.StockHighMulWitness\nimport FV.Backend.Proof.StockScalarMixedDivDomain').replace('namespace E2E.StockDivNIWitness','namespace E2E.StockMixedDivNIWitness').replace('end E2E.StockDivNIWitness','end E2E.StockMixedDivNIWitness')
s=s.replace('(op : Clif.DivOp) (cleanup : Bool)','(op : Clif.DivOp) (safe : Bool) (cleanup : Bool)').replace('(op : Clif.DivOp)\n    (input', '(op : Clif.DivOp) (safe : Bool)\n    (input').replace('function config op','function config op safe').replace('frame config op input','frame config op safe input').replace('checks config op cleanup','checks config op safe cleanup').replace('checks config op false && checks config op true','[false,true].all fun safe => checks config op safe false && checks config op safe true').replace('forty-eight fixed actual pipeline configurations only','ninety-six fixed actual pipeline configurations only')
s=s.replace('    simp only [Bool.and_eq_true] at both\n    cases cleanup', '    have both := List.all_eq_true.mp both safe (by cases safe <;> simp)\n    simp only [Bool.and_eq_true] at both\n    cases cleanup',1)
a=s.index('  have domain : Stock.Scalar.Domain');b=s.index('  refine ⟨domain,?_⟩',a)
s=s[:a]+'''  have family : ∀ item ∈ frontBody config safe, Stock.Proof.HighMulBody.Family item.inst := by
    intro item member
    rcases List.mem_append.mp member with old | extra
    · exact StockHighMulNIWitness.source_family config item old
    · cases safe
      · simp [frontBody] at extra
      · simp only [if_true,List.mem_singleton] at extra
        subst item
        exact Stock.Scalar.highmulBodyEligible_sound (by cases config <;> rfl)
  have domain : Stock.Scalar.Domain (function config op safe) :=
    Stock.Scalar.domain_of_mixed_div (lowerScope_of scope) (dominated_of dominated) abi
      (b := (function config op safe).blocks[0]!) (by cases config <;> cases safe <;> rfl)
      (front := frontBody config safe) (stm := ⟨[5000],.div op (valueType config) 4008 (divisor safe)⟩)
      (by cases config <;> cases safe <;> rfl) family rfl rfl
      (by cases config <;> cases safe <;> rfl) (by cases config <;> rfl)
''' +s[b:]
# The frame is genuinely entered for every original input, not only the fixed grid.
s=s.replace('  cases config <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩','  cases config <;> cases safe <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩')
(root/'FV/E2E/StockMixedDivWitness.lean').write_text(s)
(root/'witness-status.txt').write_text('Prepared96 complete pipeline witnesses and arbitrary-entry fixture. Not yet compiled/applied. Add finite actual original-source outcome checks to the same witness grid before landing; optional symbolic source_runs draft was cancelled, not proved. No current-source edits.\n')
print('Prepared next-class fixture and96 pipeline witness source; unvalidated until applying split production patch')
