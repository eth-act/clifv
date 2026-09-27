# ISLE rules as Lean data (`FV/Isle`, `rust/crates/isle2lean`), M4 preparation

PLAN.md §3.4: instruction selection interprets Cranelift's own ISLE lowering rules, exported
to Lean as data. This contract covers the exporter, the Lean datatypes, the generated aarch64
data, the closure for the emitter subset, the rule interpreter, and the tests.

## Status

- [x] `rust/crates/isle2lean` loads the aarch64 unit the way Cranelift builds it and exports
  types, terms, rules, VeriISLE specs, a manifest and the emitter-subset closure.
- [x] `FV/Isle/Syntax.lean` (datatypes), `FV/Isle/Generated/*` (data), `FV/Isle/Pretty.lean`
  (back to ISLE text), `FV/Isle/Interp.lean` (interpreter). `FV/Isle.lean` imports all of them.
- [x] `FVTest/Isle/*` pass. On five oracle functions the interpreter fires exactly the rules a
  `trace-log` build of Cranelift fires.
- Not wired to `FV/Clif` or `FV/Arm` yet (M4 work). See "Gaps".

## Regeneration

```sh
cargo run --manifest-path rust/Cargo.toml -p isle2lean --release
# options: --codegen-dir DIR (default third_party/wasmtime/cranelift/codegen)
#          --gen-dir DIR     (default rust/target/isle2lean-gen: generated ISLE inputs)
#          --out DIR         (default FV/Isle/Generated; every *.lean in it is replaced)
lake build FV.Isle FVTest.Isle
```

What the exporter does (`src/load.rs`):

1. It calls `cranelift_codegen_meta::generate_isle(gen_dir)` from the pinned crate
   `cranelift-codegen-meta =0.136.1`. That writes `numerics.isle`, `clif_lower.isle`,
   `clif_opt.isle` and `assembler.isle`. The VeriISLE CLI calls this same function, and
   Cranelift's `build.rs` runs the same generators through `meta::generate`. Checked: the
   generated `clif_lower.isle` and `numerics.isle` are byte-identical to the copies in the
   `cranelift-codegen` build `OUT_DIR` (`rust/target/*/build/cranelift-codegen-*/out/`).
2. It takes the input list from
   `cranelift_codegen_meta::isle::get_isle_compilations(codegen_dir, gen_dir).lookup("aarch64")`,
   with the meta crate's `spec` feature on (as VeriISLE does), so the list includes the VeriISLE
   spec files. That gives 43 files: `prelude.isle`, `prelude_lower.isle`, `spec/{prelude_spec,
   inst_specs, inst_tags, fpconst, state, prelude_lower_spec}.isle`, `isa/aarch64/inst.isle`,
   `inst_neon.isle`, `isa/aarch64/spec/*.isle`, `lower.isle`, `lower_dynamic_neon.isle`, then
   `<OUT_DIR>/numerics.isle` and `<OUT_DIR>/clif_lower.isle`. The one directory input
   (`isa/aarch64/spec`) is expanded in sorted order. Upstream uses `read_dir` order, which
   depends on the filesystem. Only spec-only definitions come from that directory, so rule and
   term numbering are unaffected.
3. It lexes and parses the files with `cranelift_isle`, then runs
   `TypeEnv::from_ast`, `TermEnv::from_ast(.., expand_internal_extractors = true)`,
   `overlap::check` and `recursion::check`. These are the steps of
   `cranelift_isle::compile::compile` before codegen. The 0.136.1 parser accepts every
   VeriISLE form (`spec`, `model`, `form`, `instantiate`, `attr`, `macro`, `state`). The spec
   files add no rules or terms, so ids are the same as in Cranelift's normal build: the export
   has 1165 rules, and the generated `isle_aarch64.rs` contains 1165 `// Rule at` sites.

File names in positions are the ones Cranelift's generated code uses: codegen-crate relative
(`src/isa/aarch64/lower.isle`), or `<OUT_DIR>/...` for generated inputs.

Output is deterministic. Two runs, including one with a different `--gen-dir`, give identical
trees. The manifest hashes inputs with `;` comments stripped, because the generated inputs'
comments contain the absolute path of the meta crate's sources.

`FV/Isle/Generated/` holds 24 modules (about 42k lines). No module exceeds 5000 lines:

| Module | Contents |
| --- | --- |
| `Types00` | one `def ty_<name> : TypeDef` per type (153) |
| `Ids` | `@[match_pattern]` constants: `TyId.«T»` (type ids), `VIdx.«T».«V»` (enum variant indices), `TId.«t»` (term ids) |
| `Terms00..02` | one `def T.«name» : Term` per term (2483) |
| `Rules00..03` | one `def rule_<file>_<line> : Rule` per rule (1165) |
| `RuleLists00` | one `def R.«term» : List Rule` per term with rules, in matching order (`ruleBefore`) |
| `TypeArray`, `TermTable`, `RuleArray`, `RuleTable` | flat tables `types`, `terms`, `rules`, `ruleLists` (indexed by id) |
| `Specs00..06` | `specs_k : Array SpecDef` (1036 spec-language definitions) |
| `Program` | `files`, `consts`, `converters`, `specs`, and `program : Program`, a structure literal over the flat tables |
| `Manifest` | `inputHashes`, `astRuleCounts` (per-file `(rule ...)` count on the parser AST), `sizes` |
| `Closure` | the emitter-subset closure (below) |

The tables are flat single literals (not appends of chunks) and `program` is not computed, so
the kernel evaluates lookups: `program.term? TId.lower = some T.lower` and
`program.rulesOf TId.lower = R.lower` are `rfl` (`FVTest/Isle/Data.lean`; the isel proofs'
`Data p` facts, `docs/contracts/backend-proof.md`).

Everything is in namespace `Isle.Aarch64`, except the closure, which is in
`Isle.Aarch64.Closure`.

Elaboration: a clean `lake build FV.Isle FVTest.Isle` takes about 16 s wall time (99 s CPU,
parallel). The slowest module is `Specs03` at 14 s. Rule modules take 3–4 s each.

## Datatypes (`FV/Isle/Syntax.lean`, namespace `Isle`)

The data is the post-sema form, which is what Cranelift's code generator consumes.
Internal extractors (macros such as `iadd`, `has_type`, `imm12_from_value`) are expanded, and
implicit converters (`put_in_reg`, `output_reg`, ...) are explicit terms. Ids are
`cranelift-isle` arena indices (`TypeId`, `TermId`, `VarId`, `RuleId` are `Nat`), and
`program.X[i].id = i`.

- `Pos := ⟨file, line⟩`. The line is **1-based**. Cranelift's comments and trace print 0-based
  lines.
- `TypeDef`: `kind` is `.bool | .int IntTy | .primitive | .enum isExtern variants |
  .struct isExtern fieldsKind fields`. `Variant` has `name`, `fullName` (`Enum.Variant`) and
  typed `fields`.
- `Term`: `name`, `args`, `ret`, `pos`, and `kind`, which is one of:
  - `.enumVariant k`;
  - `.struct`;
  - `.decl ⟨isPure, isMulti, isPartial, isRec⟩ (ctor : Option Ctor) (extractor : Option Extractor)`,
    with `Ctor := .internal | .external fn` and
    `Extractor := .internal form | .external fn infallible`.

  `.external fn` names the extern Rust helper, which PLAN.md §6 lists as unverified.
  `.internal form` keeps the source `(extractor ...)` S-expression for reference only.
  Helpers: `Term.externCtor?`, `externExtractor?`, `isExtern`, `hasInternalCtor`, `flags`.
- `Pattern`: `.bind ty v sub | .var ty v | .constBool | .constInt ty (i : Int) |
  .constPrim ty name` (the name is stored without `$`), plus
  `.term ty t args | .wildcard ty | .and ty ps`.
  `Expr`: `.term ty t args | .var | .constBool | .constInt | .constPrim |
  .let ty [(v, ty, e)] body`. Every node carries its ISLE type.
- `IfLet := ⟨lhs, rhs⟩`. `(if e)` is represented as `⟨.wildcard _, e⟩`.
- `Rule` fields:
  - `id`, `name` (the Lean name, below);
  - `isleName`: the explicit name, or for a term's only rule the term name, as sema assigns it.
    This is what `(attr rule ...)` refers to;
  - `explicitName`, `term`, `args`, `iflets`, `rhs`;
  - `vars` (names and types, by `VarId`), `prio : Int`, `pos`.
- `SExpr := .atom s | .binding name e | .list es`. This is `cranelift_isle::printer::SExpr`.
- `SpecDef`: `kind` is `.spec | .specMacro | .model | .state | .form | .instantiate | .attr`.
  It also has `name`, `term?` and `rule?` links, `pos`, and `body : SExpr` (the whole form).
  Every `spec` resolves to a term.
- `Const := ⟨name, ty⟩` (`extern const`) and `Converter := ⟨inner, outer, term⟩`.
- `Program` has `name`, `files`, `types`, `terms`, `rules`, `consts`, `converters`, `specs`,
  and `ruleLists` (each term's rules in matching order; `Program.build` computes it with
  `Program.bucketRules`, the generated program stores it as literals). API: `term?`, `type?`, `rule?`,
  `termName`, `typeName`, `termByName?`, `ruleByName?`, `rulesOf t` (in matching order,
  `ruleBefore`: priority descending, then source order), `specsOf t`, `ruleNames`.

All types derive `DecidableEq`. The nested ones (`SExpr`, `Pattern`, `Expr`) have hand-written
structural instances, because `deriving` does not support nested inductives. So a rule can be
referenced by name and checked by the kernel, for example
`example : rule_lower_93.prio = 5 := rfl` or
`example : rule_inst_3751.args[2]? = some (.bind 4 1 (.wildcard 4)) := by decide`.

`FV/Isle/Pretty.lean` provides:

- `program.ruleText r`: ISLE text of the analysed rule;
- `normalizeIsle`: drops comments and collapses whitespace.

## Naming scheme

Rule `def`s are `Isle.Aarch64.rule_<file stem>_<1-based line of "(rule">`, for example
`rule_lower_93` for `src/isa/aarch64/lower.isle:93` (`iadd_imm12_left`) or
`rule_prelude_lower_105`. If two rules start on the same line, later ones get `_2`, `_3`, ...
in rule order. None do at the pin. The name is also `Rule.name`, so it survives edits to other
files, and a Cranelift upgrade renames only the rules that moved.

Type defs are `ty_<sanitised type name>`.

## Closure for the emitter subset (`FV/Isle/Generated/Closure.lean`)

This is the set of rules reachable from roots `lower` and `lower_branch` for the E opcodes of
`clif-subset-v2` at `i8`..`i64` (the root filter is `E_OPCODES` in
`rust/crates/isle2lean/src/closure.rs`).

**Selecting root rules.** This step is sound for E programs, because every value has type
`i8`/`i16`/`i32`/`i64` and every instruction has an E opcode. A root rule is dropped only if
its main pattern (arguments, not if-lets) mentions any of:

- an `Opcode.X` with X not in E;
- a `Type` constant other than `$I8 $I16 $I32 $I64`;
- one of the extern extractors in `nonScalarIntExtractors`: `ty_vec64`, `ty_vec128`,
  `multi_lane`, `ty_scalar_float`, `lane_fits_in_32`, and so on. Each of these fails on every
  scalar integer type up to 64 bits (checked against `isle_prelude.rs`).

ISLE patterns are conjunctions, so each of these conditions is necessary for a match.

**Adding dependencies.** Next, every rule of every internal-constructor term that a closure
rule mentions (in its LHS, if-lets or RHS) is added, transitively and without filtering. Types
passed to internal terms can be computed, so filtering there would be unsound. For those rules
the same syntactic test is reported as `lhsReasons`, but only as a hint.

`FVTest/Isle/Closure.lean` re-checks in Lean that:

- the closure is closed;
- its entries agree with the program;
- every E opcode is matched by some closure root rule;
- every excluded root rule's reasons really occur in its pattern.

Every rule fired in the oracle cases is in the closure.

Counts (`Closure.summary`):

| | |
| --- | --- |
| closure rules | 442, of which 129 are root rules (`lower`/`lower_branch`) |
| root rules excluded | 396 |
| terms mentioned | 536 |
| extern terms (Rust helpers) | 128: 96 extern constructors, 36 extern extractors |
| extern terms with a VeriISLE `spec` | 87 of 128 |
| rules whose expansions `--default-excludes` skips (by tags) | 47 |
| rules with `lhsReasons` | 36 (v1: 14 — `scalar_size` of I128/F16/F32/F64, `is_nonzero` of fcmp and overflow ops, `emit_icmp` of I128; v2 adds the vector/float/I128 arms of `lower_select_cond`, `csel` variants and the vector `umin`… root rules, whose types are variables) |

The v1 closure had 33 extern terms without a VeriISLE spec:

- `output_vec`, `opportunistic_def`, `put_in_regs_vec`
- `single_target`, `two_targets`, `jump_table_targets`, `jump_table_size`
- `value_list_slice`, `first_result`, `inst_data_value`, `i64_from_iconst`
- `box_external_name`, `func_ref_data`, `abi_sig`, `abi_stackslot_addr`,
  `abi_stackslot_offset_into_slot_region`
- `gen_return`, `gen_call_output`, `gen_call_args`, `gen_call_rets`, `try_call_none`
- `branch_target`, `targets_jt_space`, `ashr_from_u64`, `cond_br_not_zero`, `is_pic`
- `gen_call_info`, `gen_call_ind_info`, `test_and_compare_bit_const`
- `i32_from_i64`, `u8_from_u64`, `value_array_2`, `block_array_2`

**`clif-subset-v2` delta** (regenerated 2026-09-27; old closure 392 rules / 112 roots / 488
terms / 119 externs): **+50 rules** (17 root rules), **+48 terms**, **+9 extern terms**:

| New extern term | Kind | VeriISLE spec | Needed at i8..i64 for |
| --- | --- | --- | --- |
| `invalid_reg` | constructor | no (tag `TODO`) | `(lower (nop))` result |
| `symbol_value_data` | extractor | no | `symbol_value` (name, `RelocDistance`, offset) |
| `value_array_3` | ctor + extractor (`pack/unpack_value_array_3`) | no | `select` operands (`InstructionData.Ternary`) |
| `ty_scalar_float` | extractor | yes | fails at integer types (float arm of `lower_select_cond`) |
| `ty_vec64`, `ty_vec128` | extractor (+ `ty_vec64_ctor`) | no | fail at integer types (vector `umin`… rules) |
| `not_i64x2`, `multi_lane`, `dynamic_lane` | extractor | no | fail at integer types |

New internal terms: `lower_select`, `lower_select_cond`, `csel`, `a64_rev16/32/64`, `fpu_csel`,
`vec_csel`, `vector_size`; new MInst variants `MInst.CSel` (has a spec),
`FpuCSel16/32/64`, `VecCSel`; `BitOp.Rev16/Rev32/Rev64`.
New root rules: `lower.isle` 78 (`nop` → `invalid_reg`), 1222–1228 (`umin`/`smin`/`umax`/`smax`
at `ty_int` → `lower_select` of `emit_icmp`), 1233–1251 (vector min/max, tag `vector`),
1931/1937/1946 (`bitrev` i8/i16 → `rbit.32` + `lsr`; other widths `rbit`), 2035/2038/2041
(`bswap` i16/i32/i64 → `rev16`/`rev32`/`rev64`), 2267 (`select` → `lower_select` of
`is_nonzero_cmp`), 2491 (`symbol_value` → `load_ext_name`; with `is_pic` (our setting)
`LoadExtNameGot` (+ `add` of the offset if non-zero)).

**Default VeriISLE coverage of the v2 expansions** (tags; no solver run — cvc5/z3 are not
installed and the veri crate does not build outside the full wasmtime workspace):
- `nop` (`invalid_reg`: `TODO`) and `symbol_value` (`load_ext_name`: `TODO`): skipped — veri
  skips `TODO`-tagged expansions unless `--no-skip-todo` (`veri.rs` `skip_todo`). Neither has
  a CLIF spec either.
- `select`, `smin`/`smax`/`umin`/`umax`: the root rules carry no tag, but they chain into
  `lower_select` → `lower_select_cond` rule 1 (`inst.isle` 5364), which uses `with_flags`
  (`TODO`), so the expanded rule is skipped by default **[inference: chained terms are
  inlined into the expansion, whose tags are the union over its terms]**. `select` also has no
  CLIF spec. The survey's note that `select` is excluded by `wasm_category_stack`
  (`inst_tags.isle`) does not apply: `select` is an extractor macro, so its term never occurs
  in an expansion (the same holds in isle2lean's tag computation).
- `bswap` (`rev16`/`rev32`/`rev64`, `bit_rr`): no excluding tag; CLIF spec exists → in the
  default run.
- `bitrev`: no excluding tag, but no CLIF spec → cannot be verified by VeriISLE.

So of the nine, only `bswap` is covered by the default VeriISLE run; the others need Lean
proofs without a VeriISLE cross-check.

`Closure.terms` lists all 536 terms with their Rust function names, spec status, `chain` flag
and tags.

**Coverage by the default VeriISLE run.** This is determined from tags. Each `ClosureRule`
has:

- `tags`: the tags on the rule, its root term, and every term it mentions. An expansion
  containing the rule carries all of them (VeriISLE `Expansion::tags`).
- `defaultExcludedBy`: `tags` ∩ {vector, atomics, spectre, narrowfloat, amode_const, i128,
  wasm_category_stack, slow}.

A non-empty `defaultExcludedBy` means `veri --default-excludes` skips every expansion
containing that rule. An empty one does not prove the rule is covered: chained terms'
expansions can bring more tags, and a missing spec can fail an expansion. Root rules excluded
by tags, per E opcode (rules whose first-matched opcode is that opcode):

| Opcode | excluded / closure root rules | tag |
| --- | --- | --- |
| `imul` | 1/1 | slow |
| `umulhi`, `smulhi` | 2/2 each | slow |
| `udiv`, `urem`, `srem` | 2/2 each | slow |
| `sdiv` | 2/4 | slow |
| `iadd`, `isub` | 2/11 and 1/6 (the `madd`/`msub` fusions) | slow |
| `uextend`, `sextend` | 1/3 and 1/2 (extending loads) | slow |
| `brif` | 1/3 | wasm_category_stack |

All other E opcodes have no tag-excluded root rule. So the default run does **not** cover
integer multiply, high multiply, division or remainder: those must be proven in Lean without a
VeriISLE cross-check.

## Interpreter (`FV/Isle/Interp.lean`)

```lean
structure Isle.Sem (V σ : Type) where
  int : TypeId → Int → V
  bool : Bool → V
  prim : TypeId → String → Option V          -- `$name` constants
  eq : V → V → Bool
  mkData : TypeId → Nat → List V → V         -- enum variant k / struct (k = 0)
  unData : TypeId → V → Option (Nat × List V)
  ctor : Term → List V → σ → ExtResult (V × σ)       -- extern constructors
  extract : Term → V → σ → ExtResult (List V)        -- extern extractors
inductive Isle.ExtResult (α) | ok (a : α) | fail | unmodeled (what : String)
structure Isle.Config where checkOverlap : Bool := false; fuel : Nat := 1000000
def Isle.Interp.run (p : Program) (sem : Sem V σ) (cfg : Config) (term : String)
    (args : List V) (st : σ) : Except Err (RunResult V σ)
structure Isle.RunResult (V σ) where value : Option V; state : σ; trace : List RuleId
inductive Isle.Err | unmodeled | outOfFuel | noRule term | ambiguous term rules
  | infallibleFailed term | unsupported what | malformed msg
```

The value domain `V`, the embedding state `σ` (the lowering context), and the semantics of
constants and extern helpers are all parameters. There is no dependency on `FV/Clif` or
`FV/Arm`. The semantics follow the Rust that `cranelift-isle` generates (checked against
`trie_again.rs`, `codegen.rs` and the language reference):

- **Rule order.** A term's rules are tried in descending priority, then in source order.
  Within one priority, `cranelift-isle`'s overlap check rejects any pair of rules that may both
  match, so at most one matches. With `checkOverlap := true`, the interpreter verifies that
  the rest of the priority class does not also match (`Err.ambiguous` otherwise).
- **Match phase.**
  - Argument patterns are matched left to right, then the if-lets in order.
  - An if-let expression may call pure or partial constructors. A `none` result, or a
    pattern that fails, means the rule does not match.
  - An extern extractor returning `.fail` means no match, unless the extractor is declared
    infallible (then `Err.infallibleFailed`).
  - After a failed attempt the state is restored, because the match phase is pure.
- **Commit.** The first matching rule is committed. Its RHS is evaluated left to right,
  innermost first (the order of `sema::Expr::visit`), with the state threaded through extern
  constructors.
  - If a `partial` constructor fails in the RHS, the whole term returns `none` (the generated
    `?`). There is no backtracking into other rules.
  - A total extern constructor failing is `Err.infallibleFailed`.
- **No rule matched.** A partial term returns `none`. A total term gives `Err.noRule`, which
  corresponds to the generated `unreachable!`.
- **Trace.** A committed rule is appended to the trace only after its RHS succeeds
  (post-order). This is exactly where the generated code emits its `trace-log` line.
- **Unmodeled externs** (`.unmodeled`) abort interpretation. A missing model can therefore
  never be mistaken for "rule does not match".
- **Fuel.** Each expression node and term application costs 1.
- **Multi terms** (`decl multi`) give `Err.unsupported`. The aarch64 unit has none: no term
  has `isMulti`.

The functions are total, defined by structural recursion on fuel and on patterns. They
compute by `#eval`/`#guard`.

## Tests (`FVTest/Isle`, `lake build FVTest.Isle`)

- `Data.lean` checks:
  - per-file rule counts equal `astRuleCounts` from the Rust parser AST: prelude 1,
    prelude_lower 77, inst 503, inst_neon 1, lower 561, lower_dynamic_neon 22 (total 1165);
  - table sizes, arena ids, name uniqueness, and that `ruleLists` is a sorted partition equal to `Program.bucketRules`; the generated `TId`/`VIdx`/`T`/`R` constants agree with the tables;
  - kernel `rfl`/`decide` facts about rules referenced by name;
  - extern flags and spec links.
- `Pretty.lean` compares seven rules, printed back to ISLE text and whitespace-normalised,
  with their source text in `third_party/wasmtime/cranelift/codegen`. The seven cover a named
  rule, a `let`, if-lets, and priorities ±1. The test also prints how many rules round-trip
  exactly: currently 414 of 1165. The others use extractor macros or converters.
- `Closure.lean`: the closure checks above.
- `Interp.lean` runs the interpreter against Cranelift. It uses a toy embedding
  (`Toy.lean`: a DFG, vregs, emitted MInsts, and about 55 modelled externs, most of them `Type`
  predicates, each mirroring its Rust implementation). For each function in `oracle/cases.clif`, it lowers the instructions in
  Cranelift's driver order. The resulting trace must equal, line for line, the output of a
  `trace-log` build of cranelift-codegen 0.136.1 (`oracle/cases.trace`). Results:

  | Function | Rules | Outcome |
  | --- | --- | --- |
  | `iadd (iconst 5) v0`, i64 | 7 | `iadd_imm12_left`, prio 5 |
  | `iadd v0 (iconst 0x5000)`, i32 | 7 | `iadd_imm12_right`, shifted imm12 |
  | `iadd v0 v1`, i8 | 7 | `iadd_base_case`, prio -1, after every higher rule is tried |
  | `icmp slt`, i64 | 10 | |
  | `icmp ult v0 (iconst 7)`, i32 | 10 | |

  All cases run with `checkOverlap`. The file also checks:
  - the selected `MInst` for the first case (`AluRRImm12 Add Size64 r3 r0 #5`);
  - that traces are the same with and without `checkOverlap`;
  - out of fuel, an unmodeled instruction, a partial term with no match (`none`), and a
    total term with no match (`noRule`);
  - that every fired rule is in the closure.

**Oracle.** `rust/crates/isle2lean/oracle` is a separate Cargo workspace, so that
cranelift-codegen's `trace-log` feature does not leak into the main workspace's build. It
compiles each function with the `clif2obj` settings (`opt_level=none`, verifier, regalloc
checker, PIC) for `aarch64-unknown-linux-gnu`, and prints the `ISLE <term> <file> line <n>`
lines. Regenerate the expected traces with:

```sh
CARGO_TARGET_DIR=rust/target/isle-oracle cargo build --release \
  --manifest-path rust/crates/isle2lean/oracle/Cargo.toml
rust/target/isle-oracle/release/isle-trace-oracle FVTest/Isle/oracle/cases.clif \
  > FVTest/Isle/oracle/cases.trace
```

## Gaps

- **Toy embedding.** The interpreter is not yet instantiated with `Clif` values and Arm
  `MInst`s. M4 must provide a real `Sem`: the lowering context, meaning `put_in_reg`,
  value-use counting and sinking, and the instruction order of Cranelift's driver. The toy
  models only what the oracle cases reach. It takes the driver's instruction order and the
  skipping of dead `iconst`s from the oracle.
- **Unverified Rust helpers.** Extern helpers stay trusted Rust semantics (PLAN.md §6). Each
  must get a Lean definition in M4, checked against Cranelift. 33 of the closure's 119 extern
  terms have no VeriISLE spec to cross-check against.
- **Closure is an over-approximation** beyond the root rules. It includes vector and I128
  helper rules that internal terms dispatch to (`lhsReasons` flags some of them). A precise
  closure needs a type-aware analysis, or the M4 interpreter run over all E opcodes and widths.
- **VeriISLE coverage is approximated from tags.** The approximation covers the tags of the rule
  itself. Expansion chaining, missing specs, and the verifier's results are not modelled.
- **Match order within a pattern.** The interpreter matches left to right; the generated code
  may test conjuncts in another order. Results are equal when the externs are pure and
  modelled, but an embedding must model extern extractors on every input reached in this order.
  In the oracle cases this included vector and atomic type predicates tried on scalar types.
- **Not implemented** (none of them occur in the aarch64 unit): multi terms and internal
  extractors surviving sema.
- **Deviation from upstream.** The spec-directory input is read in sorted order instead of
  `read_dir` order. Only spec numbering can differ.
