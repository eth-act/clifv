import FV.Isle

/-!
# The exported aarch64 ISLE data

* Rule counts per input file equal the Rust side's counts of `(rule ...)` forms on the parser's
  AST (`Isle.Aarch64.astRuleCounts`, independent of the exported sema rules), and the table
  sizes equal `Isle.Aarch64.sizes`.
* Arena ids, unique rule names, and the per-term rule index (`rulesByTerm`: a partition of the
  rules in `ruleBefore` order).
* Rules are referenced by name and their structure checked by the kernel (`decide`/`rfl`).
-/

namespace Isle.Test.Data
open Isle Isle.Aarch64

/-- Exported rules per file, in first-occurrence order. -/
def ruleCounts : List (String × Nat) :=
  program.rules.foldl (init := []) fun acc r =>
    match acc.lookup r.pos.file with
    | some n => acc.map fun (f, m) => if f == r.pos.file then (f, n + 1) else (f, m)
    | none => acc ++ [(r.pos.file, 1)]

#guard ruleCounts == astRuleCounts
#guard sizes == [("types", program.types.size), ("terms", program.terms.size),
  ("rules", program.rules.size), ("specs", program.specs.size)]
#guard program.files.toList == inputHashes.map (·.1)

-- Arena ids are positions.
#guard (List.range program.rules.size).all fun i => (program.rules[i]!).id == i
#guard (List.range program.terms.size).all fun i => (program.terms[i]!).id == i
#guard (List.range program.types.size).all fun i => (program.types[i]!).id == i

-- Rule names are unique, and each is the name of its generated `def`.
#guard (program.rules.toList.map (·.name)).eraseDups.length == program.rules.size
#guard program.rules[rule_lower_93.id]! == rule_lower_93
#guard program.rules[rule_inst_3751.id]! == rule_inst_3751

-- `rulesByTerm` partitions the rules, each bucket sorted by `ruleBefore`.
#guard (program.rulesByTerm.toList.map (·.size)).sum == program.rules.size
#guard (List.range program.terms.size).all fun t =>
  let rs := program.rulesOf t
  rs.all (·.term == t) &&
    (rs.zip rs.tail).all fun (a, b) => ruleBefore a b

-- `lower`'s rules start at its highest priority.
#guard (program.termByName? "lower").any fun t =>
  let rs := program.rulesOf t.id
  rs.head?.map (·.prio) == some (rs.foldl (fun m r => max m r.prio) (rs.headD default).prio)

/-! Kernel-checked structure of individual rules, referenced by name. -/

example : rule_lower_93.isleName = some "iadd_imm12_left" := rfl
example : rule_lower_93.prio = 5 := rfl
example : rule_lower_93.pos = ⟨"src/isa/aarch64/lower.isle", 93⟩ := by decide
example : rule_lower_93.iflets = [] := by decide
example : rule_inst_3751.iflets.length = 2 := by decide
example : rule_inst_3751.vars.map (·.1) = ["ty", "k", "n", "m"] := by decide
example : rule_inst_3751.args[2]? = some (.bind 4 1 (.wildcard 4)) := by decide
example : rule_lower_93 ≠ rule_lower_90 := by decide

/-! Terms: extern Rust helpers are flagged; specs are linked by term. -/

#guard ((program.termByName? "put_in_reg").bind (·.externCtor?)) == some "put_in_reg"
#guard ((program.termByName? "inst_data_value").map (·.kind)) ==
  some (.decl ⟨false, false, false, false⟩ none (some (.external "inst_data_value" true)))
#guard ((program.termByName? "add_imm").map (·.hasInternalCtor)) == some true
#guard ((program.termByName? "Opcode.Iadd").map (·.isExtern)) == some false
#guard ((program.termByName? "imm12_from_value").map fun t =>
  (program.specsOf t.id).length) == some 1
#guard [SpecKind.spec, .specMacro, .model, .state, .form, .instantiate, .attr].all fun k =>
  program.specs.any (·.kind == k)
#guard program.specs.all fun s => s.kind != .spec || s.term.isSome

end Isle.Test.Data
