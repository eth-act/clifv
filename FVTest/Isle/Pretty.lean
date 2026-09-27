import FV.Isle

/-!
# Exported rules printed back to ISLE text

`Program.ruleText` of an exported rule is compared, after `normalizeIsle` (comments dropped,
whitespace normalised), with the rule's source text in the pinned Cranelift tree
(`third_party/wasmtime/cranelift/codegen/<file>`, the span starting at the rule's line up to the
balancing parenthesis). The printer shows the analysed form, so rules whose source uses extractor
macros or implicit converters print differently; the checked rules below use neither. The
number of rules that round-trip exactly is printed for information. (`rule_lower_86`,
`iadd_base_case`, is an example that does not: its source `(lower (iadd ty x y))` uses the
`iadd` extractor macro and implicit `put_in_reg`/`output_reg` converters.)
-/

namespace Isle.Test.Pretty
open Isle Isle.Aarch64

/-- Source text of the form starting at 1-based line `line` of `text`: from the first `(` on
that line to its balancing `)`, with `;` comments removed. -/
def formAt (text : String) (line : Nat) : Option String :=
  let lines := ((text.splitOn "\n").drop (line - 1)).map fun l => (l.splitOn ";").headD ""
  let chars := ("\n".intercalate lines).toList.dropWhile (· ≠ '(')
  let rec go : List Char → Int → List Char → Option (List Char)
    | [], _, _ => none
    | c :: cs, depth, acc =>
      let d := if c == '(' then depth + 1 else if c == ')' then depth - 1 else depth
      if d == 0 then some (c :: acc).reverse else go cs d (c :: acc)
  (go chars 0 []).map String.ofList

def sourceOf (r : Rule) : IO (Option String) := do
  if r.pos.file.startsWith "<OUT_DIR>" then return none
  let text ← IO.FS.readFile s!"third_party/wasmtime/cranelift/codegen/{r.pos.file}"
  return formAt text r.pos.line

/-- Rules whose printed form must equal their source text. -/
def checked : List String := [
  "rule_inst_3118",         -- add
  "rule_inst_3122",         -- add_imm
  "rule_inst_2767",         -- cmp
  "rule_inst_1593",         -- operand_size_64
  "rule_prelude_lower_105", -- output_reg
  "rule_prelude_lower_818", -- with_flags_consumer_reg (let)
  "rule_inst_2941",         -- named, with an if-let
  "rule_inst_3751",         -- priority 1, two if-lets
  "rule_inst_3790"          -- priority -1
  ]

def check : IO Unit := do
  let mut exact := 0
  for r in program.rules do
    if let some src ← sourceOf r then
      if normalizeIsle src == normalizeIsle (program.ruleText r) then exact := exact + 1
  IO.println s!"{exact} of {program.rules.size} rules print back to their source text exactly"
  for n in checked do
    let some r := program.ruleByName? n | throw (IO.userError s!"no rule {n}")
    let some src ← sourceOf r | throw (IO.userError s!"{n}: no source")
    let got := normalizeIsle (program.ruleText r)
    unless got == normalizeIsle src do
      throw (IO.userError s!"{n}:\n printed: {got}\n source:  {normalizeIsle src}")

#eval check

end Isle.Test.Pretty
