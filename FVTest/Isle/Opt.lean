import FV.Isle.Generated.Opt.Manifest
import FV.Isle.Generated.Opt.Closure
import FV.Clif.Parse
import FVTest.Isle.OptToy

/-!
# The exported mid-end (`opt`) ISLE unit and `simplify`

* **Data.** Rule counts per input file equal the Rust parser AST's (`Isle.Opt.astRuleCounts`);
  1605 rules in all, the number of `// Rule at` sites in Cranelift 0.136.1's generated
  `isle_opt.rs`. Arena ids, the per-term rule index, and the generated constants agree with
  the tables. The multi terms are exactly `simplify`, `simplify_skeleton`, `truthy` and the four
  extern multi-extractors; multi terms' rules all have priority 0.
* **Closure.** `Isle.Opt.Closure` is closed under internal-constructor dependencies and agrees
  with the program.
* **Helpers.** Spot checks of the Rust transcriptions (`FV/Isle/Opt/Helpers.lean`) against
  values computed by the Rust functions (`div_const.rs`'s own test vectors; `Imm64` folds).
* **`simplify` against Cranelift.** For each function of `oracle/opt.clif`, the rules
  contributing results to Cranelift's `simplify` call on the function's last instruction
  (`oracle/opt.trace`, from `isle-trace-oracle --opt`, a `trace-log` build at
  `opt_level=speed`) equal, as a multiset, the rules of `Isle.Opt.simplify`'s candidates on
  the same e-graph (built from the parsed function; every operand is a block parameter or a
  constant, whose e-classes are single nodes in Cranelift too). The order differs:
  Cranelift's follows its decision tree, ours the rule order. Selected candidates are also
  checked by value.
-/

namespace Isle.Test.Opt
open Isle Isle.Opt

/-! ## Data -/

def ruleCounts : List (String × Nat) :=
  program.rules.foldl (init := []) fun acc r =>
    match acc.lookup r.pos.file with
    | some n => acc.map fun (f, m) => if f == r.pos.file then (f, n + 1) else (f, m)
    | none => acc ++ [(r.pos.file, 1)]

#guard ruleCounts == astRuleCounts
#guard program.rules.size == 1605
#guard sizes == [("types", program.types.size), ("terms", program.terms.size),
  ("rules", program.rules.size), ("specs", program.specs.size)]
#guard program.files.toList == inputHashes.map (·.1)
#guard program.files.toList.contains "src/spec/opt.isle"

#guard (List.range program.rules.size).all fun i => (program.rules[i]!).id == i
#guard (List.range program.terms.size).all fun i => (program.terms[i]!).id == i
#guard (List.range program.types.size).all fun i => (program.types[i]!).id == i
#guard (program.rules.toList.map (·.name)).eraseDups.length == program.rules.size
#guard program.ruleLists == Program.bucketRules program.terms.size program.rules
#guard (List.range program.terms.size).all fun t =>
  let rs := program.rulesOf t
  rs.all (·.term == t) && (rs.zip rs.tail).all fun (a, b) => ruleBefore a b

#guard program.term? TId.simplify == some T.simplify && T.simplify.name == "simplify"
#guard program.rulesOf TId.simplify == R.simplify
#guard program.rules[rule_arithmetic_8.id]! == rule_arithmetic_8

-- Multi terms, and their rules have no priorities.
#guard (program.terms.toList.filter (·.flags.isMulti)).map (·.name) ==
  ["inst_data_value", "inst_data_value_tupled", "simplify", "simplify_skeleton",
   "sextend_maybe_etor", "uextend_maybe_etor", "truthy"]
#guard program.terms.all fun t => !t.flags.isMulti || (program.rulesOf t.id).all (·.prio == 0)
#guard (program.rulesOf TId.simplify).length == 1320 - (program.rulesOf TId.simplify_skeleton).length

-- `rule_arithmetic_8` is `(rule (simplify (iadd ty x (iconst_u ty 0))) (subsume x))`.
example : rule_arithmetic_8.term = TId.simplify := rfl
example : rule_arithmetic_8.pos = ⟨"src/opts/arithmetic.isle", 8⟩ := rfl

/-! ## Closure -/

#guard Closure.rules.all fun c => (program.rule? c.rule).any fun r =>
  r.name == c.name && r.term == c.term
#guard Closure.terms.all fun c => (program.term? c.term).any (·.name == c.name)
-- Closed: every internal-constructor term a closure rule mentions (other than the roots) has
-- all its rules in it.
#guard Closure.terms.all fun c =>
  c.term == TId.simplify || c.term == TId.simplify_skeleton ||
  !((program.term? c.term).any (·.hasInternalCtor)) ||
    (program.rulesOf c.term).all fun r => Closure.rules.any (·.rule == r.id)
#guard Closure.rules.all fun c => c.isRoot == (c.term == TId.simplify || c.term == TId.simplify_skeleton)
#guard Closure.summary.lookup "rules" == some Closure.rules.size
#guard Closure.rustSources.all (·.2.isSome)

/-! ## Helpers -/

/-- The test vectors of `src/opts/div_const.rs` (`mod tests`), all of them:
`(d, mul_by, do_add, shift_by)` / `(d, mul_by, shift_by)`. -/
def magicU32 : List (Nat × Nat × Bool × Int) := [(2, 2147483648, false, 0), (3, 2863311531, false, 1), (4, 1073741824, false, 0), (5, 3435973837, false, 2), (6, 2863311531, false, 2), (7, 613566757, true, 3), (9, 954437177, false, 1), (10, 3435973837, false, 3), (11, 3123612579, false, 3), (12, 2863311531, false, 3), (25, 1374389535, false, 3), (125, 274877907, false, 3), (625, 3518437209, false, 9), (1337, 2284010283, true, 11), (65535, 2147516417, false, 15), (65536, 65536, false, 0), (65537, 4294901761, false, 16), (31415927, 1146832211, false, 23), (3735928559, 2468829875, false, 31), (4294967293, 1073741825, false, 30), (4294967294, 3, true, 32), (4294967295, 2147483649, false, 31)]

def magicU64 : List (Nat × Nat × Bool × Int) := [(2, 9223372036854775808, false, 0), (3, 12297829382473034411, false, 1), (4, 4611686018427387904, false, 0), (5, 14757395258967641293, false, 2), (6, 12297829382473034411, false, 2), (7, 2635249153387078803, true, 3), (9, 16397105843297379215, false, 3), (10, 14757395258967641293, false, 3), (11, 3353953467947191203, false, 1), (12, 12297829382473034411, false, 3), (25, 5165088340638674453, true, 5), (125, 442721857769029239, true, 7), (625, 3777893186295716171, false, 7), (1337, 14128246769991459129, false, 10), (31415927, 1255683285594222469, true, 25), (3735928559, 10603543571972294987, false, 31), (4294967293, 9223372043297226757, false, 31), (4294967294, 8589934597, true, 32), (4294967295, 9223372039002259457, false, 31), (4294967296, 4294967296, false, 0), (4294967297, 18446744069414584321, false, 32), (998690804919562253, 2848783859254263201, true, 60), (18446744073709551613, 4611686018427387905, false, 62), (18446744073709551614, 3, true, 64), (18446744073709551615, 9223372036854775809, false, 63)]

def magicS32 : List (Int × Int × Int) := [(-2147483648, 2147483647, 30), (-2147483647, -1073741825, 29), (-2147483646, 2147483645, 30), (-31415927, -1146832211, 23), (-1337, -1644744395, 9), (-256, 2147483647, 7), (-5, -1717986919, 1), (-3, 1431655765, 1), (-2, 2147483647, 0), (2, -2147483647, 0), (3, 1431655766, 0), (4, -2147483647, 1), (5, 1717986919, 1), (6, 715827883, 0), (7, -1840700269, 2), (9, 954437177, 1), (10, 1717986919, 2), (11, 780903145, 1), (12, 715827883, 1), (25, 1374389535, 3), (125, 274877907, 3), (625, 1759218605, 8), (1337, 1644744395, 9), (31415927, 1146832211, 23), (2147483646, -2147483645, 30), (2147483647, 1073741825, 29)]

def magicS64 : List (Int × Int × Int) := [(-9223372036854775808, 9223372036854775807, 62), (-9223372036854775807, -4611686018427387905, 61), (-9223372036854775806, 9223372036854775805, 62), (-998690804919562253, 7798980107227644207, 59), (-4294967297, -9223372034707292161, 31), (-4294967296, 9223372036854775807, 31), (-4294967295, 9223372034707292159, 31), (-4294967294, 9223372032559808509, 31), (-4294967293, 9223372030412324859, 31), (-3735928559, 7843200501737256629, 31), (-31415927, 8595530394057664573, 24), (-1337, -7064123384995729565, 9), (-256, 9223372036854775807, 7), (-5, -7378697629483820647, 1), (-3, 6148914691236517205, 1), (-2, 9223372036854775807, 0), (2, -9223372036854775807, 0), (3, 6148914691236517206, 0), (4, -9223372036854775807, 1), (5, 7378697629483820647, 1), (6, 3074457345618258603, 0), (7, 5270498306774157605, 1), (9, 2049638230412172402, 0), (10, 7378697629483820647, 2), (11, 3353953467947191203, 1), (12, 3074457345618258603, 1), (25, -6640827866535438581, 4), (125, 2361183241434822607, 4), (625, 3777893186295716171, 7), (1337, 7064123384995729565, 9), (31415927, -8595530394057664573, 24), (3735928559, -7843200501737256629, 31), (4294967293, -9223372030412324859, 31), (4294967294, -9223372032559808509, 31), (4294967295, -9223372034707292159, 31), (4294967296, -9223372036854775807, 31), (4294967297, 9223372034707292161, 31), (998690804919562253, -7798980107227644207, 59), (9223372036854775805, 2305843009213693953, 60), (9223372036854775806, -9223372036854775805, 62), (9223372036854775807, 4611686018427387905, 61)]

#guard magicU32.all fun (d, m, a, s) => Rust.magicU 32 d == (m, a, s)
#guard magicU64.all fun (d, m, a, s) => Rust.magicU 64 d == (m, a, s)
#guard magicS32.all fun (d, m, s) => Rust.magicS 32 d == (m, s)
#guard magicS64.all fun (d, m, s) => Rust.magicS 64 d == (m, s)

#guard (Rust.imm64Sshr (.int 8) 128 3).toOption == some 240       -- i8: -128 >> 3 = -16 = 0xf0
#guard (Rust.imm64Rotl (.int 32) 0x80000001 1).toOption == some 3
#guard (Rust.imm64Add (.int 64) (2 ^ 63 - 1) 1).toOption == some (-2 ^ 63)
#guard (Rust.imm64Sdiv (.int 32) 0x80000000 0xffffffff).toOption == some none   -- i32::MIN / -1
#guard (Rust.imm64Sdiv (.int 32) 7 0xfffffffe).toOption == some (some 0xfffffffd)  -- 7 / -2 = -3
#guard (Rust.imm64Srem (.int 32) 0xfffffff9 2).toOption == some (some 0xffffffff)  -- -7 % 2 = -1
#guard (Rust.imm64Clz (.int 16) 1).toOption == some 15
#guard (Rust.imm64Ctz (.int 16) 0).toOption == some 16
#guard (Rust.imm64Icmp (.int 32) .ult 3 0xffffffff).toOption == some 1
#guard (Rust.imm64Icmp (.int 32) .slt 3 0xffffffff).toOption == some 0
#guard Rust.bswap 2 0x1234 == 0x3412
#guard (Rust.i64SextendU64 (.int 8) 0xff).toOption == some (-1)
#guard (Rust.tyMask (.int 128)).toOption == none

/-! ## `simplify` against Cranelift -/

/-- Toy e-graph of a parsed function: block parameters have no nodes; each single-result
statement with an `InstructionData` form is one node. Returns the graph and the value of the
last such statement. -/
def graphOf (f : Clif.Function) : Toy.G × Nat := Id.run do
  let mut nodes : Array (List Clif.Inst) := #[]
  let mut types : Array (Option Clif.Ty) := #[]
  let mut last := 0
  let set {α : Type} [Inhabited α] (a : Array α) (i : Nat) (x : α) : Array α :=
    (if i < a.size then a else a ++ Array.replicate (i + 1 - a.size) default).set! i x
  for b in f.blocks do
    for (v, t) in b.params do
      nodes := set nodes v []
      types := set types v (some t)
    for s in b.body do
      if let [v] := s.results then
        if (ofInst s.inst).isSome then
          nodes := set nodes v [s.inst]
          types := set types v (Toy.resultTy s.inst)
          last := v
  return (⟨nodes, types⟩, last)

/-- `file:line` of a rule, as the oracle prints it (1-based). -/
def ruleLoc (name : String) : String :=
  match program.ruleByName? name with
  | some r => s!"{r.pos.file}:{r.pos.line}"
  | none => s!"<{name}>"

/-- Oracle lines by function: `(value, rule locations)` of each `simplify` call. -/
def sections (s : String) : List (String × List String) :=
  let lines := (s.splitOn "\n").filter (· ≠ "")
  let (done, cur) := lines.foldl (init := ([], none))
    fun (done, cur) l =>
      if l.startsWith "function " then
        (match cur with | some c => done ++ [c] | none => done, some ((l.drop 9).toString, []))
      else match cur with
        | some (n, ls) => (done, some (n, ls ++ [l]))
        | none => (done, none)
  match cur with | some c => done ++ [c] | none => done

def oracleCalls (s : String) : List (String × List (Nat × List String)) :=
  (sections s).map fun (fn, ls) =>
    (fn, ls.filterMap fun l =>
      match (l.drop 9).toString.splitOn ": " with
      | [v, rest] =>
        match (v.drop 1).toString.toNat?, rest.splitOn " -> " with
        | some n, [rules, _] => some (n, (rules.splitOn " ").filter (· ≠ ""))
        | _, _ => none
      | _ => none)

def sorted (l : List String) : List String := l.mergeSort (fun a b => decide (a ≤ b))

def check : IO Unit := do
  let prog ← match Clif.parse (← IO.FS.readFile "FVTest/Isle/oracle/opt.clif") with
    | .ok p => pure p
    | .error e => throw (IO.userError e)
  let oracle := oracleCalls (← IO.FS.readFile "FVTest/Isle/oracle/opt.trace")
  unless oracle.length == prog.funcs.length do
    throw (IO.userError s!"oracle has {oracle.length} functions, expected {prog.funcs.length}")
  for f in prog.funcs do
    let some calls := oracle.lookup s!"%{f.name}"
      | throw (IO.userError s!"%{f.name}: not in oracle output")
    let (g, v) := graphOf f
    let some expected := calls.lookup v
      | throw (IO.userError s!"%{f.name}: no simplify call on v{v}")
    match Toy.run g v with
    | .error e => throw (IO.userError s!"%{f.name}: {e}")
    | .ok (_, names, _) =>
      let got := names.map ruleLoc
      unless sorted got == sorted expected do
        throw (IO.userError s!"%{f.name}: rules differ\n got: {got}\n expected: {expected}")
      IO.println s!"%{f.name} v{v}: {names}"

#eval check

/-! Candidates by value (expectations derived from the rules). -/

def g (vs : List (Clif.Ty × List Clif.Inst)) := Toy.mk vs

/-- The candidates' nodes (`none`: an existing value without a node), with `subsume`. -/
def cands (gr : Toy.G) (v : Nat) : List (Option Clif.Inst × Bool) :=
  match Toy.run gr v with
  | .ok (cs, _, gr') => cs.map fun (n, s) => ((Toy.enodes gr' n).head?, s)
  | .error _ => []

-- `iadd v0 (iconst 0)` → `v0`, subsuming (`arithmetic.isle:8`), and itself (`remat`).
#guard match Toy.run (g [(.i32, []), (.i32, [.iconst .i32 0]), (.i32, [.binary .iadd .i32 0 1])]) 2 with
  | .ok (cs, _, _) => cs == [(0, true), (2, false)]
  | .error _ => false
-- `iadd 5 -7` at i64 → `iconst -2` (subsume), `iadd -7 5`, and `remat` twice.
#guard cands (g [(.i64, [.iconst .i64 5]), (.i64, [.iconst .i64 (-7)]),
    (.i64, [.binary .iadd .i64 0 1])]) 2 ==
  [(some (.iconst .i64 (-2)), true), (some (.binary .iadd .i64 1 0), false),
   (some (.binary .iadd .i64 0 1), false), (some (.binary .iadd .i64 0 1), false)]
-- `isub x x` → `iconst 0` (subsume).
#guard cands (g [(.i16, []), (.i16, [.binary .isub .i16 0 0])]) 1 == [(some (.iconst .i16 0), true)]
-- `imul x 16` → `ishl x 4`.
#guard cands (g [(.i32, []), (.i32, [.iconst .i32 16]), (.i32, [.binary .imul .i32 0 1])]) 2 ==
  [(some (.binary .ishl .i32 0 3), false)]
-- `icmp ult 3 -1` at i32 → `1`; also `icmp ugt -1 3` (constant to the right).
#guard (cands (g [(.i32, [.iconst .i32 3]), (.i32, [.iconst .i32 (-1)]),
    (.i8, [.icmp .ult .i32 0 1])]) 2).contains (some (.iconst .i8 1), true)
-- `sshr.i8 -128, 3` → `-16`.
#guard cands (g [(.i8, [.iconst .i8 (-128)]), (.i8, [.iconst .i8 3]), (.i8, [.binary .sshr .i8 0 1])]) 2 ==
  [(some (.iconst .i8 (-16)), true)]
-- `uextend.i64 (uextend.i32 x)` → `uextend.i64 x`.
#guard cands (g [(.i8, []), (.i32, [.extend .uextend .i32 0]), (.i64, [.extend .uextend .i64 1])]) 2 ==
  [(some (.extend .uextend .i64 0), false)]
-- A float or vector result never reaches `make`; a block parameter has no candidates.
#guard cands (g [(.i32, [])]) 0 == []

end Isle.Test.Opt
