import FV.Backend.Proof.IselExclData
namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def sourceOpcodePattern (p : Program) : Pattern → Option Nat
  | .term 18 209 [_, .term 152 fT (.term 151 oT [] :: _)] =>
    match termOf p fT,termOf p oT with
    | .ok f,.ok o => match f.kind,o.kind with
      | .enumVariant _,.enumVariant k => some k
      | _,_ => none
    | _,_ => none
  | _ => none
def sourceRootOpcode (p : Program) : Pattern → Option Nat
  | .bind _ _ q => sourceOpcodePattern p q
  | .and _ [q] => sourceOpcodePattern p q
  | .and _ [_, .and _ [_,q]] => sourceOpcodePattern p q
  | .and _ [_,q] => sourceOpcodePattern p q
  | q => sourceOpcodePattern p q
def sourceRuleOpcode (p : Program) (r : Rule) : Option Nat := r.args.head?.bind (sourceRootOpcode p)
def sourceOpcodeIds (opcode : Nat) : List RuleId :=
  ((program.rulesOf TId.lower).filter (fun r => closureRootIds.contains r.id && sourceRuleOpcode program r == some opcode)).map Rule.id
/-- Every original closure root has a recognized primary source opcode. This
is a checked syntactic inventory; the matching connection is proved separately. -/
theorem stock_source_opcode_inventory :
    (program.rulesOf TId.lower).all (fun r => !closureRoot r || (sourceRuleOpcode program r).isSome) = true := by
  simp only [closureRoot_eq]
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel
/-- Exact candidate ids for original unary negation in the checked closure. -/
theorem stock_neg_opcode_inventory : sourceOpcodeIds 75 = [756] := by decide +kernel
/-- Exact candidate ids for original scalar byte swaps in the checked closure. -/
theorem stock_bswap_opcode_inventory : sourceOpcodeIds 110 = [932,933,934] := by decide +kernel
/-- Exact candidates for original scalar bit reversal in the checked closure. -/
theorem stock_bitrev_opcode_inventory : sourceOpcodeIds 106 = [915,916,918] := by decide +kernel
end Backend.Stock.Proof
