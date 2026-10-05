import FV.Backend.Proof.SpillClsCheck
import FV.Backend.Proof.IselFlowRootF
import FV.Backend.Proof.IselContract

/-!
# The summary table of the class analysis and its kernel checks (V4 classes)

`clsTab`: `IselFlowTabF.flowTab` plus the rows of the internal terms only the branch lowering
calls and `output_reg` of anything (inferred by the same least-fixpoint table inference, kept as
literal data). Every table
term's rules check under `aRuleC` (an `emit` of flow level `≤ 1`), and so do the root rules of
`lower` on statements (to a result of level `≤ 1` but `nop`'s 587), on `return`/`trap`, and of `lower_branch`; kernel
decisions, chunked as in `IselFlowTabF`.
-/

namespace Backend.Proof.Flow

open Isle Isle.Aarch64 Backend.Proof

/-- The rows `flowTab` lacks: terms of the branch lowering, and `output_reg` (172) of anything
(`nop`'s `invalid_reg`; a second row, after `flowTab`'s). -/
def clsTabX : Tab :=
  [(256, [FA.c0, FA.c0], FA.c0), (661, [FA.c0], FA.c0), (662, [FA.c0, FA.c0, FA.c0], FA.c0),
   (663, [FA.c0, FA.c0, FA.c0], FA.c0), (664, [FA.c0, FA.c0, FA.c0, FA.c0], FA.c0),
   (665, [FA.c0, FA.c0, FA.c0, FA.c0], FA.c0), (666, [FA.c0, FA.c0, FA.c0, FA.c0, FA.c0], FA.c0),
   (667, [FA.c0, FA.c0, FA.c0, FA.c0], FA.c0), (668, [FA.c0, FA.c0, FA.c0, FA.c0], FA.c0),
   (669, [FA.c0], FA.c0), (670, [FA.c0, FA.c0, FA.c0, FA.c0], FA.c0), (722, [FA.c0, FA.c0, FA.c0], FA.c0),
   (172, [⟨2, true⟩], FA.top)]

/-- **The class analysis' summary table.** -/
def clsTab : Tab := flowTab ++ clsTabX

set_option maxRecDepth 100000 in
theorem clsTab_flowTab0_ok :
    flowTab0.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab1_ok :
    flowTab1.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab2_ok :
    flowTab2.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab3_ok :
    flowTab3.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab4_ok :
    flowTab4.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab5_ok :
    flowTab5.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab6_ok :
    flowTab6.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab7_ok :
    flowTab7.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab8_ok :
    flowTab8.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab9_ok :
    flowTab9.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab10_ok :
    flowTab10.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab11_ok :
    flowTab11.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_flowTab12_ok :
    flowTab12.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsTab_clsTabX_ok :
    clsTabX.all (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true := by
  decide +kernel

/-- Every rule of every term of `clsTab` checks. -/
theorem clsTab_ok : chkTabC program clsTab false = true := by
  unfold chkTabC
  show (flowTab0 ++ flowTab1 ++ flowTab2 ++ flowTab3 ++ flowTab4 ++ flowTab5 ++ flowTab6 ++ flowTab7 ++ flowTab8 ++ flowTab9 ++ flowTab10 ++ flowTab11 ++ flowTab12 ++ clsTabX).all
    (fun e => (program.rulesOf e.1).all (aRuleC program clsTab false e.2.1 e.2.2)) = true
  simp only [List.all_append, clsTab_flowTab0_ok, clsTab_flowTab1_ok, clsTab_flowTab2_ok, clsTab_flowTab3_ok, clsTab_flowTab4_ok, clsTab_flowTab5_ok, clsTab_flowTab6_ok, clsTab_flowTab7_ok, clsTab_flowTab8_ok, clsTab_flowTab9_ok, clsTab_flowTab10_ok, clsTab_flowTab11_ok, clsTab_flowTab12_ok, clsTab_clsTabX_ok, Bool.and_self]

/-- The statement root check: outside the closure, or checking from the root instruction
(level 1), and (but `nop`'s rule 587) to a result of level `≤ 1`. -/
def clsRootOk (r : Rule) : Bool :=
  !closureRootIds.contains r.id || (aRuleC program clsTab false [⟨1, true⟩] FA.top r &&
    (r.id == 587 || aRuleC program clsTab false [⟨1, true⟩] ⟨1, false⟩ r))

set_option maxRecDepth 100000 in
theorem clsRules0_ok : flowRules0.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules1_ok : flowRules1.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules2_ok : flowRules2.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules3_ok : flowRules3.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules4_ok : flowRules4.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules5_ok : flowRules5.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules6_ok : flowRules6.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules7_ok : flowRules7.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules8_ok : flowRules8.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules9_ok : flowRules9.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules10_ok : flowRules10.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules11_ok : flowRules11.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules12_ok : flowRules12.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules13_ok : flowRules13.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules14_ok : flowRules14.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules15_ok : flowRules15.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules16_ok : flowRules16.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules17_ok : flowRules17.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules18_ok : flowRules18.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules19_ok : flowRules19.all clsRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem clsRules20_ok : flowRules20.all clsRootOk = true := by
  decide +kernel

/-- Every root rule of `lower` passes `clsRootOk`. -/
theorem clsRoot_ok : (program.rulesOf TId.lower).all clsRootOk = true := by
  rw [flowRules_eq]
  simp only [List.all_append, clsRules0_ok, clsRules1_ok, clsRules2_ok, clsRules3_ok, clsRules4_ok, clsRules5_ok, clsRules6_ok, clsRules7_ok, clsRules8_ok, clsRules9_ok, clsRules10_ok, clsRules11_ok, clsRules12_ok, clsRules13_ok, clsRules14_ok, clsRules15_ok, clsRules16_ok, clsRules17_ok, clsRules18_ok, clsRules19_ok, clsRules20_ok, Bool.and_self]

set_option maxRecDepth 100000 in
/-- The terminator rules of `lower` (`return`, `trap`) check from the slot (level 1). -/
theorem clsTerm_ok : (program.rulesOf TId.lower).all (fun r =>
    !termRootRule r || aRuleC program clsTab false [⟨1, true⟩] FA.top r) = true := by
  rw [flowRules_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every rule of `lower_branch` checks from the slot (level 1) and constant targets. -/
theorem clsBranch_ok : (program.rulesOf TId.lower_branch).all
    (aRuleC program clsTab false [⟨1, true⟩, FA.c0] FA.top) = true := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  decide +kernel

end Backend.Proof.Flow
