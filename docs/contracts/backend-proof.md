# Backend proofs: isel (M4) foundation, contract and template; probe findings

Producers: probe agent (`agent/probe-isel`), then M4Foundation (`agent/m4-foundation`),
2026-09-27. Consumers: M4 fan-out, M6 (checker composition), M7 (driver). Code:
`FV/Backend/Proof/Isel*.lean`, `FVTest/Backend/Proof/Probe/`.

## M4 foundation status (M4Foundation)

| Deliverable | State |
| --- | --- |
| 1. Exporter/backend redesign | **done** (`971c344`). Details below the table. Behaviour unchanged: corpus 114/114, runtests 3085/0/0, encode-check 971/971 identical, regalloc 932/932, `FVTest.Isle` (incl. Cranelift trace equality) passes; regeneration deterministic. |
| 2. Full-closure `Data p` | **done** (`c80737a`): 129 root rules, 536 terms, 838 rules (the lists of `lower`/`lower_branch` include the 396 excluded rules), every fact `rfl`; `IselData` builds in **110 s, 6.1 GB**; `data_program` axioms: `propext` only. |
| 3. Generic interpreter lemmas | **done** (`IselGeneric.lean`): `selectRule_some` (committed rule ∈ candidates, matched from the start state, fuel ≥ start − #candidates − 2), `selectRule_none`, `applyTerm_internal_some` (value = RHS of a committed matched rule, rule appended to the trace), `applyTerm_internal_none` (partial term with no match and unchanged state, or matched rule whose RHS returned `none`); match inversion `matchRule_some_inv`, `matchArgs_cons_inv`, `matchPat_enum_inv`, `matchPat_extract_inv`, `matchPat_bind_inv`. |
| 4. Contract framework + `LowerRulesCorrect` | **done** (`IselContract.lean`), shapes agreed with M7Skeleton (see "Contract"). `lowerInstOk_of_rules` / `lowerInstOk_runTerm` proven. |
| 5. Batching template | **partial**: the template `aluRR_ruleOk` and `iadd_base_case_ok`, `isub_base_case_ok` (`LowerRuleOk`, i8..i64) are proven. **Not done**: `band`/`bor`/`bxor` (their base rules go through `alu_rs_imm_logic_commutative`, 5 rules incl. iconst/ishl look-through), and the probe gaps (b) `iadd_imm12`, (c) `icmp`→`cset`, (d) `ushr` narrow. See "Remaining". |
| 6. This document | done |

**Exporter/backend changes (1).** `isle2lean` now emits one `def T.«term»` per term, one
`def R.«term» : List Rule` per term with rules (matching order), flat tables `terms`,
`rules`, `types`, `ruleLists` (`TermTable`, `RuleArray`, `TypeArray`, `RuleTable`), and
`Ids.lean` with `@[match_pattern]` constants `TyId.«T»`, `VIdx.«T».«V»` and `TId.«t»`.
`program` is a structure literal (no `Program.build`); `Program.rulesByTerm` became
`ruleLists : Array (List Rule)` (`rulesOf p t = (p.ruleLists[t]?).getD []`), and
`FVTest/Isle/Data.lean` checks it against `Program.bucketRules`. The backend (`MInst.lean`)
decodes enum values by generated index (`MInst.ofV`, `V.enum?`, `ALUOp.ofIdx?`, …) and
`externCtor`/`externExtract`/`tyPred` dispatch on the term id (`TId.*`), so a renamed
variant or term is a compile error. By-name construction remains only for CLIF-side values
(`instData`: `InstructionData`, `Opcode`, `IntCC`), checked by `FVTest/Backend/Names.lean`.
Data facts are now `rfl` (~0.1 s each with `maxRecDepth 20000`; `Meta` indexes the list);
`termByName? "lower"` is `decide +kernel` (12 s: string comparisons).

## Contract (`IselContract.lean`), agreed with M7

* VCode level, abstract semantics `isem : Sem := ISem CV Arm.ArmState` (M6's `csem F ctx` is
  the instance). The rules need only `Refines F isem`: on every form `ispec` specifies, `isem`
  gives the same def values, falls through, and a world `SameWorld F`-equal to `ispec`'s.
  `ispec` (value level, Arm-model operations): `AluRRR` add/sub/and/orr/eor, `subS` (flags via
  `AddWithCarry`/`write_pstate`), 32-bit `lsr`, `AluRRImm12` add, `AluRRImmLogic`, `Extend`,
  `CSet`. M6Rest confirmed its `csem` characterization lemmas have this shape.
* `MRStable F MR`: the memory relation ignores allocatable registers, pc and NZCV
  (`SameWorldNF`).
* `CtxInv f ctx` (M7 proves it from `buildCtx`): `instData f inst = .ok info.data`, result
  types, value `x` ↦ vreg `x`, def sites, slot offsets.
* Per instruction (M7's shapes, verbatim): `seqRun`, `VHolds` (low bits), `ValsHeld`, `DFGCons`,
  `instOutcome`, `ResultsHeld`, `UsesOk` (inside the continuing outcome arms), `LowerInstOk`,
  `LowerTermOk` (with the branch targets).
* Per rule: `LowerRuleOk isem MR env cp p r` — if root rule `r` matches `[.inst ii]` and its RHS
  returns `out` (fuels ≥ 1000; no fuel monotonicity needed), then
  `∃ ms rss, st'.emitted = st.emitted ++ ms ∧ out = .regsVec rss ∧ LowerInstOk …`.
* **Target**: `LowerRulesCorrect p := ∀ F isem MR env cp, Refines F isem → MRStable F MR →
  ∀ r ∈ p.rulesOf TId.lower, closureRoot r = true → LowerRuleOk isem MR env cp p r`;
  `ExcludedUnmatchable p` (non-closure root rules never match an instruction of a `CtxInv`
  context); `BranchRuleOk`/`BranchRulesCorrect` for `lower_branch` (stated, not proven).
* `lowerInstOk_runTerm : LowerRulesCorrect program → ExcludedUnmatchable program →
  Refines F isem → MRStable F MR → CtxInv f ctx → ctx.insts[ii]? = some info →
  info.clif = some inst → runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr) →
  ∃ ms rss, st'.emitted = st.emitted ++ ms.toArray ∧ out = .regsVec rss ∧ LowerInstOk …`.

## Template (`IselFamily.lean`) and measured cost

All 129 closure root rules have the argument pattern
`(inst_data_value tyPat (InstructionData.K (Opcode.O …) …))`, so one lemma
(`root_match_data`) recovers format and opcode from "the rule matched";
`instData_names`/`instNames` + `instNames_binary` invert `instData` to the CLIF instruction;
the rule's forward lemmas (`isel_eval`) then fix environment and emitted code by determinism;
`seqRun_aluRRR` + `aluVal_holds` give the meaning at every width. `aluRR_ruleOk` packages it:
a two-register ALU rule costs **three forward lemmas** (match, RHS at every width, RHS failing
when an operand has no register) **and one line**.

Measured (this machine, one core per file): `IselRulesALU` (forward lemmas of 2 rules plus
`sub_run`) **4.0 s**, i.e. ~2 s per rule; `IselFamilyALU` (the two rule theorems) 0.7 s;
`IselFamily` (template, once) 1.6 s. Axioms of `iadd_base_case_ok`, `isub_base_case_ok`,
`lowerInstOk_runTerm`: `propext`, `Classical.choice`, `Quot.sound`.

## Remaining root rules: families and fan-out plan

| Family (root rules) | Needs |
| --- | --- |
| reg-reg ALU base cases: iadd 86, isub 801 | **done** |
| logic ops via `alu_rs_imm_logic_commutative` (band/bor/bxor 1412/1449/1516) | term contract over its 5 rules: iconst look-through (`DFGCons`) + `ImmLogic` value, `ishl` look-through + `AluRRRShift` spec; then template |
| imm12 / neg-imm12 / extend / shifted-operand variants of iadd/isub (90, 93, 98, 102, 108, 111, 116, 120, 805, 810, 816, 821) | look-through lemmas (iconst, uextend/sextend, ishl) + `ispec` for `AluRRImm12`, `AluRRRExtend`, `AluRRRShift`; template variant with one look-through |
| madd/msub fusions (125, 128, 132), imul, umulhi/smulhi | `AluRRRR` spec, multiply width lemmas |
| unary ALU (ineg, bnot + fusions, clz/ctz/popcnt/bitrev/bswap, ireduce, extends) | per-op width lemma; popcnt uses vector `cnt` (hand work) |
| shifts/rotates (ishl/ushr/sshr/rotl/rotr) | `do_shift`, `put_in_reg_zext32/sext32` contracts, masking lemmas |
| `icmp`, `select`, min/max | `emit_icmp` (12 rules), `with_flags` (16), `lower_select`, flag lemma `ConditionHolds (condOf cc).invert ↔ intcc cc` (10 codes × 2 widths) |
| div/rem (explicit traps) | trap outcome of `LowerInstOk`, `trapIf` spec |
| load/store (10+7), stack_addr, symbol_value | `amode` contracts, `MemRel`/slot relation (M7), memory `ispec` |
| call/return/trap, `lower_branch` (5) | ABI (`CallRel`), `LowerTermOk`/`BranchRuleOk` |
| `ExcludedUnmatchable` (396 rules) | generic: an excluded rule's pattern names a non-E opcode/type test; prove with `root_match_data` + `instNames` per opcode class |

Fan-out: one agent per row, each adding its `ispec` forms (tell M6Rest), a family template
next to `aluRR_ruleOk` and a file of forward lemmas. Regenerate `IselData` with
`lake env lean --run FVTest/Backend/Proof/Probe/GenData.lean closure`.

# Probe findings (earlier)

## Status

| Deliverable | State |
| --- | --- |
| 1. MInst semantics through the real pipeline (`MInst.lines` → `Insn` → `Insn.toArmInst` → `exec_inst`) | **done**: `MInst.sem`, `seqSem`, `alloc`, `Frame` (`IselSem.lean`); per-form lemmas for every instruction (a)–(d) emit: `sem_add32/64`, `sem_addi32/64`, `sem_cmp32/64` (`subs xzr`), `sem_cset`, `sem_uxtb32`, `sem_and7_32`, `sem_lsr32`. Uses M5's `Insn.sem`; M5's `Insn.stepi_eq_sem` lifts it to `stepi` on the encoded word. |
| 2. Rule-correctness statement (M4 shape) + width convention | **done**, see "Statement" |
| 3a. `iadd_base_case` (`lower.isle:86`), i8..i64 | **proved** interpreter level (`match_86`, `rhs_86_32`, `rhs_86_64`) and end to end for i8/i16/i32 (`iadd_base_case_correct_32`); the i64 Arm half is `add64_correct` (combination = same 3-line proof as the 32-bit one, not written) |
| 3b. imm12 variant (`iadd_imm12_right`) | Arm half proved (`sem_addi32/64`), extern lemmas proved (`ext_def_inst_*`, `ext_u64_from_imm64`, `ext_imm12_from_u64`, `emit_addi_*`); **rule-level interpreter lemma not written** (same recipe as `rhs_86_*`) |
| 3c. `icmp` → `cmp` + `cset` | Arm halves proved (`sem_cmp32/64`, `sem_cset`), extern/emit lemmas (`ctor_cond_code`, `emit_cset`, `emit_subs_*`); **term lemmas for `emit_icmp`/`with_flags`/`lower_cond_result_bool` and the flag lemma `ConditionHolds (condOf cc).invert … ↔ Clif.Sem.intcc cc` not written** |
| 3d. `ushr` at i8 (`ushr_fits_in_32`) | Arm halves proved (`sem_uxtb32`, `sem_and7_32`, `sem_lsr32`), extern lemmas (`ctor_shift_mask_i8`, `emit_uxt8_32`, `emit_andi_32`, `emit_lsr_32`); **rule/term lemmas (`put_in_reg_zext32`, `do_shift`) not written** |
| 3e. `brif` | not attempted |
| 4. Interpreter link for (a) | **partial**: the generated `Data p` carries `p.termByName? "lower" = some term_686` and the full `p.rulesOf 686` list (by `native_decide`); the selection proof (all 200+ earlier `lower` rules fail) is not done. Recommended route and cost below. |
| 5. This document | done |

Stopped at the request budget; the remaining items are mechanical applications of the recipe
that works (below), not open design questions.

## Statement (M4 shape) and width convention

`FV/Backend/Proof/IselProbe.lean`:

```lean
theorem iadd_base_case_correct_32 {p : Isle.Program} (hp : Data p) (ctx : Ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) (ty : Clif.Ty) (hty : ty.width ≤ 32)
    {i x y vx vy : Nat} {info : IInfo} (hi : ctx.insts[i]? = some info)
    (hres : info.resTys.head? = some (.int ty.width))
    (hd : info.data = .data 152 2 [.data 151 73 [], .values [x, y]])   -- Binary(Iadd, [x, y])
    (hx : ctx.valueReg? x = some (.vreg vx .int)) (hy : ctx.valueReg? y = some (.vreg vy .int))
    (st : LState) (tr : Array RuleId) (n : Nat) :
    ∃ env m dst st' tr',
      (matchRule p (sem ctx) cfg (n+2) rule_lower_86 [.inst i]).run (st, tr) = .ok (some env, (st, tr)) ∧
      (evalExpr p (sem ctx) cfg (n+40) rule_lower_86.rhs env).run (st, tr) =
        .ok (some (.regsVec [[.vreg dst .int]]), (st', tr')) ∧
      st'.emitted = st.emitted.push m ∧
      ∀ ρ, ρ vx ≤ 30 → ρ vy ≤ 30 → ρ dst ≤ 30 →
      ∀ s u v, Holds ty s (ρ vx) u → Holds ty s (ρ vy) v →
        ∃ s', MInst.sem (m.mapRegs (alloc ρ)) s = .ok s' ∧
          Holds ty s' (ρ dst) (Clif.Sem.iadd u v) ∧ Frame [ρ dst] false s s'
```

`Data program` is `data_program`, so the statement instantiates to `Isle.Aarch64.program`.
`Holds ty s k v := (X k s).setWidth ty.width = v`; `Frame ds fl s s'`: all x-registers not in
`ds` (and SP), all SIMD regs, NZCV unless `fl`, the error field and all memory unchanged.

**Width convention.** The exported rules rely on Cranelift's: a value of type `ty` is the low
`ty.width` bits of its register, upper bits unspecified. `iadd_base_case` at i8/i16 emits a
32-bit `add` whose bits `ty.width..31` are garbage, so PLAN §3.4's `CanonReg w` (upper bits
zero) is **not** an invariant of rule outputs; rules that need clean upper bits re-extend
(`put_in_reg_zext32` → `uxtb` in `ushr_fits_in_32`, `cmp_extend` in `icmp` at i8/i16, masking of
shift amounts by `shift_mask`). With "low bits" the obligation stays local to each rule
(`trunc_add32`); no cross-rule invariant is needed. Recommend PLAN §3.4 be amended.

**Axioms** (`FVTest/Backend/Proof/Probe/Axioms.lean`): `propext`, `Classical.choice`,
`Quot.sound`, plus `*._native.native_decide.ax_*` from the data facts (`typeName_14`,
`program_term_*`, `program_rulesOf_*` in `data_program`) and the two bitmask facts
`dbm_uxtb`, `dbm_and7`. No `sorry`, no hand-written axiom.

## What worked (the recipe)

1. **Data facts by targeted `native_decide`, over an abstract program.** `IselData.lean` is
   generated (`lake env lean --run FVTest/Backend/Proof/Probe/GenData.lean`): for every term
   reachable from the probe's root rules, `program.term? t = some term_t` and
   `program.rulesOf t = [rule_…]`, one `native_decide` each (193 facts + 200-rule `lower` list:
   module builds in ~37 s, 2.5 GB). Rule proofs are stated for any `p : Isle.Program` with
   `Data p` (a structure bundling the facts as `termOf p t = pure term_t`); the kernel
   therefore never sees `program`. Stating them for `program` directly failed: some `simp`
   steps (a `match` on `program.term? t` reduced by `whnf`, or an `ite` step next to a
   `rulesOf` rewrite) produced proofs whose kernel check reduced `Program.build` — "deep
   recursion" at the default depth, 3 GB OOM in 9 s with `maxRecDepth 2000`. The abstract `p`
   makes that impossible by construction.
2. **Evaluate the interpreter outermost-closed-call first** (`isel_eval`, `IselInterp.lean`):
   `rw` one interpreter equation (never rewrites under a binder), then `simp only` with monad
   laws + data facts + caller lemmas and *no* interpreter equations. Plain
   `simp [evalExpr, applyTerm, …]` unfolds every not-yet-taken continuation once per unit of
   fuel: 8 GB OOM in 18 s on the two-rule `operand_size`.
3. **Per-term contracts** (`IselTerms.lean`): `operand_size`, `alu_rrr` (generic in op/size),
   `add`, `output_reg`, each for all fuel ≥ a bound and any `LState`; rule proofs use them as
   rewrite rules. Each term/rule lemma: 2–5 s.
4. **Extern helpers by `rfl`**: the string-keyed `externCtor`/`externExtract` reduce by
   evaluation; `simp [externCtor]` instead generates equation lemmas for a 100-way string match
   and times out. `MInst.ofV`/`mkVariant` look variants up by name in `program.types` — cheap
   for the kernel, but Meta `whnf` needs `maxRecDepth 4000` locally (153-element array).
5. **Arm side**: M5's `Insn.sem`; per instruction form, `simp` over `armFields`/`exec_*`.
   `decode_bit_masks` goes through `highest_set_bit`, too deep for the kernel: the two masks
   used are `native_decide` facts. `bv_decide` does not handle `extractLsb'` (which `simp`
   produces from `setWidth`); the truncation lemma is proved arithmetically instead.

## Friction points

- **Data size / lookup shape.** `program` is computed (`Program.build`: fold + sort of all
  rules; `terms` is an append of 7 arrays): nothing about it may be kernel-reduced. Every
  term/rule lookup needs a `native_decide` fact.
- **Selection vs correctness.** Correctness does not need "rule r is selected": whatever rule
  the interpreter commits to must be correct. Showing that `iadd_base_case` is selected needs
  every higher-priority `lower` rule (≈ 200 before it, all opcodes) to fail, which depends on
  the operands' definitions (`iadd_imm12_*`, `iadd_extend_*`, `madd` fusion…). Recommended:
  prove `lower` correct as "for every rule in `p.rulesOf 686` whose match succeeds, its RHS is
  correct" (a generic lemma about `selectRule`: the committed rule's `matchRule` returned
  `some env`), and prove every closure root rule; drop selection proofs (coverage is already
  checked executably: the backend errors when no rule fires).
- **Internal terms have many rules**: RHS correctness of a root rule depends on which rule of
  e.g. `do_shift` (const vs register amount), `put_in_reg_zext32` (i32/i64 vs narrow),
  `emit_icmp` (12 rules), `with_flags` (16) fires. Per-term *contracts* (VeriISLE-style specs:
  "returns a register holding f(inputs)") proven once per term over all its rules are the unit
  of work, not root-rule expansions.
- **Extern-helper specs**: 128 externs; the string-dispatch design makes each a small `rfl`
  lemma, fine; the ones with ctx lookups need the DFG invariants of `buildCtx` as hypotheses
  (`info.data = instData f clif`, `resTys = map ofClif`, `valReg v = vreg v`) — a
  `buildCtx`-invariant lemma is still owed.
- **Flags**: `with_flags` + `cset` split producer/consumer; correctness needs a lemma per
  `IntCC` relating `ConditionHolds (condOf cc).invert` after `subs` to `Clif.Sem.intcc`
  (10 codes × 2 widths, bit-blastable) and an invariant that nothing between them writes NZCV
  (true: spill code never touches flags, `backend.md`).
- **vreg → reg relation and composition with M6/M5**: rule outputs are VCode over vregs; the
  probe states them under a renaming `alloc ρ` with the per-instruction side conditions
  (`ρ v ≤ 30`; for multi-instruction rules also "fresh temporaries ≠ still-live inputs"). M6's
  intended theorem simulates VCode "with vregs as an infinite register file" — it needs a
  *VCode-level semantics per `MInst`*. Proposal: define it as `MInst.sem` under any
  injective-on-operands renaming, and prove per form that the result is renaming-independent
  (register parametricity of the LNSym exec functions); then M4 rule theorems are stated at
  the VCode level and M6 composes. M5 composes directly via `Insn.stepi_eq_sem`.

## Recommended architecture and effort for the closure (442 rules)

1. Generate `Data p` for the whole closure (≈ 540 terms, 442 rules; ~2 min build) — same
   generator, roots = all closure root rules.
2. Generic interpreter lemmas (`selectRule` commits a matching rule; `applyTerm` of an internal
   term = RHS of a matched rule) — ~1 day.
3. Per-term contracts for the ≈ 100 internal helper terms (most are one-rule wrappers like
   `add`/`alu_rrr`: `isel_eval` closes them with no human input; ~20 multi-rule dispatchers like
   `emit_icmp`, `do_shift`, `imm`, `with_flags` need case splits) — ~1–2 weeks.
4. Root rules (129): match lemma + RHS lemma are automatic with `isel_eval` given the term
   contracts; the Arm half is `sem_*` lemmas for ~45 instruction forms plus a `bv_decide` or
   arithmetic width lemma per rule. Batchable by a tactic: ALU reg-reg/imm/shift/extend
   families (~70 rules); needs hand work: division (traps), loads/stores (memory model,
   `mem_finalize`), calls/returns (ABI), branches/`br_table` (control flow), `select`/min/max
   (flags) — ~3–4 weeks.
5. Glue: `buildCtx` invariants, VCode semantics (with M6), `lower_branch`.

## Design changes that would make proofs substantially easier (findings; the exporter/backend ones are done, see "M4 foundation status")

- **Exporter**: emit per-term rule-list constants (`def rulesOf_lower : List Rule := […]` in
  `ruleBefore` order) and per-term `Term` constants, and build `Program.rulesByTerm` from them;
  then the data facts are `rfl` instead of 700+ `native_decide` calls, and `terms` should be a
  single flat array (the 7-way append is what the kernel cannot reduce).
- **Backend `V`/`MInst.ofV`**: decode enums by generated variant *indices* (constants), not by
  name via `variantNames`/`islTy` lookups into `program`; `externCtor`/`externExtract`: dispatch
  on term id (generated table) instead of a 100-way string match.
- **Interpreter**: expose a small-step or big-step relational semantics (`Eval`/`Match`
  inductive predicates) proven equivalent to the fuel-based functions; rule proofs by
  constructor application would avoid fuel arithmetic and the evaluation-order tactic.
- **Width convention**: document "low bits, upper unspecified" as the contract (PLAN §3.4).

## Family A (binary ALU with operand look-through) — M4AluA

Closure root rules of the family's opcodes (`FV/Isle/Generated/Closure.lean`, `isRoot`, term
686), with state:

| Opcode | Rule (`lower.isle` line, name) | State |
| --- | --- | --- |
| `iadd` | 86 `iadd_base_case` | done (M4Foundation) |
| `iadd` | 90 `iadd_imm12_right`, 93 `iadd_imm12_left` | **proven** (`iadd_imm12_right_ok`, `iadd_imm12_left_ok`) |
| `iadd` | 98 `iadd_imm12_neg_right`, 102 `iadd_imm12_neg_left` | **proven** (`iadd_imm12_neg_right_ok`, `iadd_imm12_neg_left_ok`) |
| `iadd` | 116 `iadd_ishl_right`, 120 `iadd_ishl_left` | **proven** (`iadd_ishl_right_ok`, `iadd_ishl_left_ok`) |
| `iadd` | 108 `iadd_extend_right`, 111 `iadd_extend_left` | **proven** (M4AluA2: `iadd_extend_right_ok`, `iadd_extend_left_ok`) |
| `iadd` | 125 `iadd_imul_right`, 128 `iadd_imul_left` | **proven** (M4AluA2: `iadd_imul_right_ok`, `iadd_imul_left_ok`) |
| `isub` | 801 `isub_base_case` | done (M4Foundation) |
| `isub` | 805 `isub_imm12`, 810 `isub_imm12_neg`, 821 `isub_ishl` | **proven** (`isub_imm12_ok`, `isub_imm12_neg_ok`, `isub_ishl_ok`) |
| `isub` | 132 `isub_imul`, 816 `isub_extend` | **proven** (M4AluA2: `isub_imul_ok`, `isub_extend_ok`) |
| `imul` | 871 `imul_base_case` | **proven** (M4AluA2: `imul_base_case_ok`) |
| `smulhi`/`umulhi` | 1056 `smulhi_64`, 1068 `umulhi_64` | **proven** (M4AluA2: `smulhi_64_ok`, `umulhi_64_ok`) |
| `smulhi`/`umulhi` | 1059, 1071 (`fits_in_32`) | **proven** (M4AluA2: `smulhi_fits_in_32_ok`, `umulhi_fits_in_32_ok`), i8/i16/i32 |
| `band`/`bor`/`bxor` | 1412, 1449, 1516 (`*_fits_in_64`) | **proven** (`band/bor/bxor_fits_in_64_ok`) via the term contract `aluRsImmLogicComm_ok` (all 5 rules: reg-reg, logical immediate either side, `ishl` by a constant either side) |
| `band`/`bor`/`bxor` | 1429/1431, 1466/1468, 1534/1536 (`*_not_right/left`) | **proven** (M4AluA2: `band/bor/bxor_not_right/left_ok`) via the term contract `aluRsImmLogic_ok` (term 566, all 3 rules) |
| `bor` | 1501, 1507 (`extr_32_or_64`) | **proven** (M4AluA2: `extr_32_or_64_ok`, `extr_32_or_64_2_ok`), I32/I64 |
| `bnot` (family B) | 1406 (`bnot (bxor x y)`) | **proven** for M4AluB2 (M4AluA2: `bnot_bxor_ok`, via `aluRsImmLogic_ok` with `EorNot`) |

**Shared edits made** (all additive, announced): `FrameTyped` conjunct of `DFGCons` (f55011e,
integrator decision); ispec forms `smulh/umulh .size64`, `AluRRRR` madd/msub (+ `ra = xzr`),
`AluRRRShift` (lsl, `aluShiftable`) and `.extr`, `AluRRRExtend` (`extendVal`) (c74e398);
`AluRRImmLogic` guarded to the logical operations (e2b64ab; Asm rejects add/sub). Taken
verbatim from peers: M4Cmp 1a4de60 / 4de7914, M4AluB 1532afa / c696bfa, M7Driver 0770fd7.

**Files.** `IselFamALUA.lean` (generic: `root_match_inv`, `binary_root_inv`, `values2_match_inv`,
`defInst_match_inv`, `imm12_args_inv`, `iflet_term_var_inv`, `negated_value_inv`; CLIF
inversion `instData_iconst_inv`/`instData_binary_inv`, `ctxInv_clif`; `dfg_single`,
`evalInst_binary_inv`/`evalInst_shift_inv`; `seqRun_step`/`seqRun_one`, `lowerInstOk_binary`,
`lowerInstOk_one`, `OneInstOk` + `OneInstOk.lowerInstOk`; `rhs_output_inv`; width lemmas
`holds_add_imm`/`holds_sub_imm`/`holds_add_K`/`holds_sub_K`/`aluVal_holds_B`,
`negImm12_value`, `sextFrom_imm64OfIconst`, `ofNat_u64`, `land_width_sub_one`);
`IselTermsALUA.lean` (generic `ofV_*`, `operand_size_run`, `alu_rr_imm12_run`, `add_imm_run`,
`sub_imm_run`); `IselRulesALUA.lean` (forward lemmas 90/93/805/98/102/810,
`imm12_from_negated_value_some/none`); `IselTermsLogic.lean` (extern lemmas
`ctor_imm_logic_*` — proven by rewriting only: a `rfl`/`simp` that lets the kernel unfold
`ImmLogic.ofNat?` on a symbolic value ran out of 14 GB — `ctor_lshl_*`, `alu_rr_imm_logic_run`,
`alu_rrr_shift_run`, `add/sub_shift_run`, forward lemmas of the five 565 rules and of
116/120/821/1412/1449/1516); `IselFamALUARules.lean`, `IselFamALUALogic.lean` (rule theorems,
`aluRsImmLogicComm_ok`, `logicRoot_ruleOk` template).

**Cost** (one core, `lake env lean`): `IselFamALUA` 3 s, `IselTermsALUA` 4 s, `IselRulesALUA`
10 s, `IselTermsLogic` 18 s / 2.9 GB peak, `IselFamALUARules` and `IselFamALUALogic` ≈ 1 s
each: ≈ 3 s per look-through rule (forward lemmas) plus < 0.2 s per rule theorem.
**Axioms** of every theorem above: `propext`, `Classical.choice`, `Quot.sound`.

### M4AluA2 (successor): the remaining 19 family-A rules and rule 1406

All 31 closure root rules of family A are now proven (plus family B's 1406, requested by
M4AluB2), each `LowerRuleOk` for any `isem` refining `ispec` and any `MRStable` memory relation,
at every width the rule's type pattern admits. No shared file was changed (no `ispec` form or
contract edit was needed; `main` a156415 merged in).

**Term contracts.** `aluRsImmLogic_ok` (`alu_rs_imm_logic`, term 566; `NotOp op` =
`AndNot`/`OrrNot`/`EorNot`, value `notOpVal op x y`; the shape of `aluRsImmLogicComm_ok`, one
instruction, `LogicOut`), `notRoot_rhs` (a right-hand side `(output_reg (alu_rs_imm_logic …))`).
`sext64_inv`/`zext64_inv` (`put_in_reg_sext64/zext64`, terms 557/558: narrow type → `extend` to
64 bits, `I64` → the operand's register, else no match); helper runs `alu_rrrr_run`, `madd_run`,
`msub_run`, `smulh_run`, `umulh_run`, `alu_rrr_extend_run`, `alu_rr_extend_reg_run`,
`add/sub_extend_run`, `a64_extr_run_32/64`, `alu_rr_imm_shift_run_fa`, `asr/lsr_imm_run`,
`extend_run_fa`.

**Look-through and value lemmas.** `instData_bnot_inv`/`bnot_value`, `binary_value` (any
non-shift op), `shift_const_value` (shift by an `iconst`), `ext_extended_inv` +
`extend_value` (`extended_value_from_value`: `ctx.defClif?` + `valueType?`, value by `DFGCons`,
source width by `FrameTyped`); `ExtrOk`/`extrOk_nat` (the `extr` if-lets). Width lemmas:
`aluVal_holds_not`, `holds_madd`/`holds_msub`/`holds_mul0`, `smulh_holds`/`umulh_holds`,
`extendVal_holds`, `extr_bits`/`extr_holds`, `mulhi_narrow_s/u` (bits `w..2w-1` of the 64-bit
product of the extensions = the high half of the `2w`-bit product).

**Multi-instruction rules (1059/1071).** `evalExpr_let_inv`, `evalBinds_cons_inv`,
`evalArgs_var1` invert a `let` right-hand side to its sub-calls; the contracts fix each operand
part, abstracted as `PartOk` (code, fresh defs, uses only the operand, 64-bit extension in the
result vreg, vregs below the start state kept); the `I64` arm is vacuous at a narrow type by
`FrameTyped`; `seqRun_append_fall_fa` composes the runs; `mulhiN_lowerInstOk` is the back half
(`madd … xzr`, `asr`/`lsr` by the width) for both rules. `ValsBelow` keeps the second operand's
vreg untouched by the first part.

**Constant type patterns** (`I64` in 1056/1068, `ty_32_or_64`, `fits_in_32`): a `*_ne`/`*_ty`
forward lemma shows the match fails at other widths (`sem_eq_beq_fa` + `beq` on `V.ty`).
Rules whose if-lets can fail (1501/1507: `u8` range, `xs + ys = w`, positivity) have a single
`match_*_none` lemma under `¬ ExtrOk` (a case split per condition, `maxHeartbeats 2000000`
locally: the 5-deep look-through pattern exceeds the default).

**Files.** `IselTermsLogicNot`/`IselFamALUALogicNot` (566 contract, 1429–1536, 1406),
`IselTermsALUAMul`/`IselFamALUAMul` (1056, 1068, 871, 125, 128, 132),
`IselTermsALUAExt`/`IselFamALUAExt` (108, 111, 816), `IselTermsALUAExtr`/`IselFamALUAExtr`
(1501, 1507), `IselTermsALUAMulN`/`IselFamALUAMulN` (1059, 1071).

**Cost** (`lake env lean`, this machine): forward-lemma files 6–13 s each except
`IselTermsALUAExtr` ≈ 55 s (the two `extr` match/none lemmas); rule-theorem files 1–3 s.
Peak memory well under the 10 GB cap.

**Integration notes.** Names that peers' branches also define were suffixed `_fa`
(`ctor_zero_reg_fa`, `ext_fits_in_32_ty_fa`, `ctor_ty_bits_ty_fa`, `ofV_extend_fa`,
`ext_value_type_none_fa`, `extend_run_fa`, `alu_rr_imm_shift_run_fa`, `seqRun_append_fall_fa`,
`operands_extend_fa`, `sem_eq_beq_fa`, `variantNames_Unary_fa`). Pre-existing clashes from the
predecessor's files remain for the integrator: M4AluB's branch also defines `szOf`,
`getAs_isSome`, `lowerInstOk_one`, `SameWorld.trans'` in `Backend.Proof`.
**Axioms** of every theorem above: `propext`, `Classical.choice`, `Quot.sound`.
## Family C: flags, select, min/max, div/rem (M4Cmp)

**Status: infrastructure only — no root rule proven yet.** Branch `agent/m4-cmp`.

Root rules in this family (none proven yet): `icmp` 2215, `uextend(icmp)` 1281, `select` 2267,
`umin/smin/umax/smax` 1222/1224/1226/1228, vector min/max 1233/1239/1245/1251 (their RHS has to
be shown to fail on scalar types), `udiv` 1116/1119, `sdiv` 1145/1153/1163/1167, `urem`
1190/1197, `srem` 1204/1211.

Shared changes (all announced and taken byte-identically by the other branches):
`1a4de60` (`ValsBelow` hypothesis of `LowerRuleOk`; `Refines` quantifies over every control
through an implicit `{ctl}` binder); `0d56d05` (`ispec` forms added at the top of `ispec`:
subS/addS imm12, subS against xzr, subS extended register, andS imm (`andsFlags`),
udiv/sdiv, msub, csel, ccmpImm, trapIf (`condBrHolds`, as M6's `CondBrKind.holds`), udf);
`4de7914` (`V`'s derived `BEq` was an opaque constant, so no proof could use a
constInt/constPrim/var pattern; replaced by a structural `V.beq` with a `LawfulBEq`
instance. Corpus 114/114 and extrt 22/22 agree, `FVTest.Isle` passes). Taken from the
others: FrameTyped `f55011e`, AluB `1532afa` and `c696bfa`, M7Driver `0770fd7`.

New files, all building with no `sorry`:

* `IselCmpInv.lean`: generic `iff` lemmas that turn a successful match or evaluation (or an
  `applyTerm` via `ApplySpec`) into the facts it implies, with internal constructor calls
  kept as `ApplyInternal` hypotheses.
* `IselCmpBase.lean`:
  * `iff` lemmas for the extern extractors and constructors used by the family.
  * `isel_inv [facts, rules] at hm he`: `simp` with these lemmas, then split with
    `isel_destruct` and `subst_vars`, repeated until nothing changes.
  * `isel_cases` and `isel_rule_cases hL`: one goal per rule of a concrete rule list.
* `IselCmpRun.lean`: how straight-line code composes.
  * `seqRun` over an append: fall through, stop, fall then stop.
  * One instruction under `Refines` (`seqRun_one_next`/`_halt`).
  * `seqRun_frame`: a run only changes the vregs its instructions define.
  * `Frag`: fresh-def fragments, with `append` and `frame`.
  * `UsesLo`, and Hoare-style `Runs` with `nil`/`append`/`one`/`imp`.
  * `SameWorldNF` is reflexive and transitive, and holds after a flag write.
  * `SameWorld` preserves `ConditionHolds`.
* `IselSemCmp.lean`: flag lemmas.
  * `ConditionHolds` after `write_pstate` (`condOn`).
  * `condOn (condOf cc).bits (cmpFlags a b) = intcc cc a b` for all 10 codes, at 32 and 64 bits.
  * Signed and unsigned narrow-operand extension lemmas (8/16 → 32).
  * `Cond.invert` negates every condition except `al`/`nv`.
  * `a ≥ b ↔ a > b-1` (unsigned and signed), for `emit_icmp` rule 5.
  * `cmp r, #0` then eq/ne; `tst #255` then ne.
* `IselCmpTerms.lean`:
  * `internal_split_first`: first-match selection for internal terms.
  * `isel_split hp hc h t` macro.
  * Contracts `operand_size_ok` (with the "earlier rule failed" argument), `cmp_ok`,
    `cmp_imm_ok`, `cmp_extend_ok`, `cset_ok`, `csel_ok` and `extend_ok`.

Axioms: `propext`, `Classical.choice`, `Quot.sound`, plus `*._native.bv_decide.ax_*` from the
flag lemmas.

**How to continue.** The plan is backward (inverse) evaluation plus semantic term contracts;
it avoids having to show which rule is selected.

1. Contracts for `put_in_reg_zext32`/`sext32` (`sext64`/`zext64` for division). The
   statement is drafted in the git history (`zext32_ok`). Rule 3809 needs the pre-failure of
   the i32 rule (forward `isel_eval` of the failed match, as in `operand_size_ok`) and
   `FrameTyped`.
2. `CondSem c lo fr ρ b`: the meaning of a `CondResult`, i.e. Zero/NotZero of a vreg at a
   size, or Cond(`ProducesFlagsSideEffect i`, cd) whose `ispec` sets flags on which `cd` is
   `b`. Contracts for `is_nonzero` (rules 4–10 and I128 are impossible: opcode or type
   mismatch via `CtxInv.defClif`/`instData`), `cond_result_invert` and `emit_icmp` (11 E-rules;
   the iconst look-through uses `DFGCons` and `imm64OfIconst`).
3. Consumers: `with_flags` (rule 818 only; the other 15 are enum mismatches),
   `lower_cond_result_bool`, `lower_select`/`lower_select_cond` (`csel`; the float, vector and
   i128 rules fail on integer types).
4. Division: the `trapIf`/`udf` halt arms go through `seqRun_one_halt` and
   `seqRun_append_fall_stop`. Needed: `imm` from M4AluB (`IselTermsImm`),
   `trap_if_div_overflow` (`ccmpImm`) and `intmin_check` (`aluRRImmShift`).

## Family Ctl: terminators, branches, calls (M4Ctl)

Branch `agent/m4-ctl`. Files `FV/Backend/Proof/IselCtl{Base,Term,Unmatch,Branch,Call,}.lean`,
axiom audit `FVTest/Backend/Proof/Ctl/Axioms.lean`.

**Statements proven for `Isle.Aarch64.program`** (axioms `propext`, `Classical.choice`,
`Quot.sound`):

| Statement | Theorem | Notes |
| --- | --- | --- |
| `LowerTermRulesCorrect program` | `lowerTermRulesCorrect` | `trap` 964 (`udf`, `trap_ruleOk`), `return` 1037 (`lower_return` → `rets` of the value vregs pinned to x0.., `ret_ruleOk`) |
| `TermUnmatchable program` | `termUnmatchable` | root-format check: `ruleFmt` + one `decide +kernel` over the 517 `lower` rules (`lower_fmts`), generic `ruleFmt_match` |
| `BranchExcludedUnmatchable program` | `branchExcludedUnmatchable` | same, `lower_branch_fmts` (try_call rules 1034/1035/1036) |

**Per-rule status (`lower_branch`, `BranchRulesCorrect` still open):**

| Rule | State |
| --- | --- |
| 1139 `jump` | **proven** (`jump_ruleOk`, `jump_termOk`) |
| 1132 `brif` base (`br_cond_result (is_nonzero_cmp v)`) | open: needs family C's `is_nonzero_cmp`/`emit_icmp` contracts (`CondSem`/`CondCode` on `agent/m4-cmp`@6e60c71, not finished) and a `br_cond_result` contract (4 rules) |
| 1137 `tbnz`, 1138 `tbz` (look through `band x (iconst 2^k)`, `icmp eq … 0`) | open: `def_inst` look-through + `test_and_compare_bit_const` lemmas |
| 1140 `br_table` | open (now provable: `BrIdxTyped`, change #6): `emit_island`, `put_in_reg_zext32` (`ExtOut`, family C), `br_table_impl` (2 rules; needs `imm` from family B), `jt_sequence` |

**Calls (`CallRulesCorrect`, open):** rules 1031 (`bl`) and 1032 (GOT + `blr`); `call_indirect`
(`rule_lower_2529`, 1033) is not in E. The extern/ABI lemmas are proven (`IselCtlCall.lean`:
`func_ref_data`, `gen_call_output` = `outRegs`/`freshN`, `argLocs_eq` (≤ 8 arguments all in
x0..), `gen_call_args`/`gen_call_rets`/`gen_call_info`/`gen_call_ind_info`, `is_pic`); the two
rule theorems (operand view of `call`, `CallsRefine` application, `ResultsHeld` of the fresh
output vregs) are not written.

**Shared changes (integrator-approved, announced):** #5 `38600e8` (calls: `CallsRefine`,
`CallRegArgs`, `CallRuleOk`/`CallRulesCorrect`, `LowerRulesCorrect` excludes `callRootRule`,
ispec control forms `rets`/`jump`/`condBr`/`testBitAndBranch`/`emitIsland`/`jtSequence` as M6's
`csem` 350a4c7, E2E threading, `InSubset.callRegArgs`, compiler flags >8-parameter externs
unverified); #6 `e597895` (`BrIdxTyped` premise of `BranchRuleOk`/`TermCalls`, `lowerCheck`'s
`brIdxOk`). `callRootRule` corrected to rule ids 1031/1032 (first version named 1027, which is
`symbol_value`; reported by M4Mem). Merged `agent/m4-cmp`@b455355 (family C infrastructure).

**Techniques.** Inverse evaluation (`isel_inv`, `ctl_inv` = `isel_inv` + the family's extern
lemmas each round); fuel as `n' + 100` so the iff lemmas apply; callee contracts passed in
before `cases hp` (which clears `hp`); a terminator's format from the matched rule
(`ruleFmt_term`) instead of evaluating the mismatching cases (which timed out).
## Family B: unary ALU, shifts, rotates (M4AluB, branch `agent/m4-alu-b`)

**Proven `LowerRuleOk` (i8..i64 where the rule's type pattern allows), 13 rules** — rule ids
(`Rule.id`) / `lower.isle` line / theorem:

| id | line | rule | theorem (file) |
| --- | --- | --- | --- |
| 756 | 857 | `ineg_base_case` | `ineg_base_case_ok` (`IselFamAluBUnary`) |
| 915 | 1931 | `bitrev.i8` | `bitrev_i8_ok` (`IselFamAluBBitrev`) |
| 916 | 1937 | `bitrev.i16` | `bitrev_i16_ok` |
| 918 | 1946 | `bitrev` (i32/i64) | `bitrev_ok` (first-match: 1931/1937) |
| 919 | 1951 | `clz_8` | `clz_i8_ok` (`IselFamAluBClz`) |
| 920 | 1955 | `clz_16` | `clz_i16_ok` |
| 922 | 1961 | `clz_32_64` | `clz_ok` (first-match: 1951/1955) |
| 924 | 1982 | `ctz_8` | `ctz_i8_ok` |
| 925 | 1986 | `ctz_16` | `ctz_i16_ok` |
| 927 | 1995 | `ctz_32_64` | `ctz_ok` (first-match: 1982/1986) |
| 932 | 2035 | `bswap.i16` | `bswap_i16_ok` (`IselFamAluBBswap`) |
| 933 | 2038 | `bswap.i32` | `bswap_i32_ok` |
| 934 | 2041 | `bswap.i64` | `bswap_i64_ok` |

Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound` and the
`<thm>._native.bv_decide.ax_*` certificates of the width lemmas. No `sorry`.

**Shared changes made (all additive, taken byte-identically by the other families):**
`1532afa` (ispec: `aluVal` andNot/orrNot/eorNot, `shiftVal`, `rrrVal` for AluRRR shifts mod
width, `aluRRImm12 .sub`, `aluRRImmShift`, `bitRR` rbit/clz/rev16/rev32/rev64, `extend` 8→16,
AluRRR with `xzr` first operand; `CtxInv.defClif`), `c696bfa` (contract change #3:
`LowerRuleOk` assumes the rules before `r` in `lower` failed to match — the generic
`bitrev`/`clz`/`ctz` rules are *wrong* at i8/i16 and only correct because selection is first
match; `selectRule_some_first`, `applyTerm_internal_some_first`, `lower_rules_nodup`).

**Infrastructure** (`IselFamAluBBase`, `IselTermsAluB`): `PRun` (world-independent
straight-line runs, `prun_cons`/`prun_rr`/`prun_rrr`), `lowerInstOk_one`, `unary_front`,
templates `unary_ruleOk` (code a function of width) and `unary_ruleOk'` (per-evaluation
`CodeShape` + meaning; for `value_type`-dependent code), tactics `wcases`/`wfix` (width lemmas by
`bv_decide -enums`; `-enums` is needed so two modules can be imported together), `code_facts`,
`st_facts`, `earlier_of_idx` (first-match side conditions from rule indices in `lower`).
Term contracts: `bit_rr_run`, `alu_rr_imm_shift_run`, `alu_rr_imm12_run`, `alu_rr_imm_logic_run`,
`extend_run`, `put_in_reg_zext32` (`zext32_pass32/pass64/ext/none/big`, all `value_type`
cases — the code depends on the operand's `valueType?`, which `CtxInv` does not relate to the
instruction; `FrameTyped` makes the other cases vacuous at run time).

**Cost** (this machine, one module at a time, 10 GB cap): `IselFamAluBBase` 1.5 s,
`IselTermsAluB` 8 s, `IselFamAluBUnary` 4 s, `IselFamAluBBitrev` 10 s, `IselFamAluBClz` 24 s,
`IselFamAluBBswap` 7 s; i.e. ~2–4 s per rule. Rule index lemmas (`lower_idx_*`, `rfl` on the
517-entry list) ~1 s each.

**Continuation (M4AluB2, same branch).** 7 more rules proven (20 total), plus the `imm`
contract; merged `main` at `4da7bdc` (only conflict: my additive `ispec` arms).

| id | line | rule | theorem (file) |
| --- | --- | --- | --- |
| 582 | 53 | `iconst` | `iconst_ok` (`IselFamAluBIconst`) |
| 587 | 78 | `nop` | `nop_ok` (`IselFamAluBMisc`) |
| 828 | 1377 | `bnot_base_case` | `bnot_base_case_ok` (`IselFamAluBMisc`) |
| 946 | 2146 | `ireduce` | `ireduce_ok` (`IselFamAluBMisc`) |
| 808 | 1261 | `uextend` | `uextend_ok` (`IselFamAluBExtend`) |
| 819 | 1315 | `sextend` | `sextend_ok` (`IselFamAluBExtend`) |
| 834 | 1406 | `bnot (bxor x y)` | proven by **M4AluA2** on `agent/m4-alu-a` (`6b431d6`, `bnot_bxor_ok`), since it needs their `alu_rs_imm_logic` (term 566) contract |

Axioms: `propext`, `Classical.choice`, `Quot.sound`, plus `bv_decide` certificates
(`extend_sem`, `bnot_base_case_ok`, and `movK_ident` for `iconst`). No `sorry`, no axiom.

* **`imm` contract** (`IselTermsImm.imm_ok`, all five rules, `i8..i64`, `ImmExtend` Zero/Sign;
  shared with M4Cmp2): from `applyTerm … 553 [.ty (.int w), .data 122 e [], .int i] = some v`,
  `ImmOut`: fresh vreg `d`, `CodeShape`, and on every run a 64-bit value `X` in `d` with
  `X % 2^w = u64 i % 2^w`, equal to `immVal w (e == 0) (u64 i)` (= `load_constant_full`'s value)
  except for an `i32` zero-extended constant `≥ 2^32`. Proof is *inverse*: `applyTerm_internal_some`
  picks the fired rule, per-rule forward match/rhs lemmas (`match_37xx`, `rhs_37xx`), then the
  meaning per case (`imm_case_*`).
* **`load_constant_full`** (`IselLcf.lcf_run`): the `movz`/`movn` + `movk` loop leaves
  `lcfValue …` in the result vreg, for every value (16-bit slice arithmetic `slice16`/`replace16`
  with concrete slice indices by `omega`; `movk` masking a `bv_decide` identity).
* **New `ispec` forms** (additive, before `| _, _ => none`; M6Rest2 told): `movWide` (`movWideVal`),
  `movK` (`movKVal`), `aluRRImmLogic op sz rd .xzr imm, []`.
* **Shift/rotate infrastructure**: `IselFamAluBShiftBase.shift_ruleOk` (template for binary
  shift/rotate rules, per-evaluation `CodeShapeU` + meaning in every `DFGCons` frame),
  `binary_front`, `evalInst_shift_ok`; `IselTermsShift`: `do_shift` per-rule forward lemmas
  (`match_1631/1622/1623/1612` and their `_none`), `defInst_iconst_inv` + `defInst_iconst_clif`
  (the `iconst` look-through of `do_shift_imm`: amount's definition, via `CtxInv.defClif`).
* **Lesson (kernel blow-up):** evaluating a whole multi-rule term forward with `isel_eval` and
  closing an `∃ tr'` by `rfl` made the *kernel* check use >15 GB (elaboration 2 GB); the same
  facts proved per rule (match lemma + rhs lemma, then `applyTerm_internal_some`) check in
  seconds. Use the per-rule inverse route for multi-rule terms.

**Remaining (not proven), with the route:**
- shifts 1545/1549/1638/1642/1695/1699: finish `do_shift_ok` — rhs lemmas for the four rules
  (`alu_rr_imm_shift_run`, `alu_rrr_run`, `and_imm` = `alu_rr_imm_logic_run` with
  `ctor_shift_mask_i8/_i16`), then the contract by `applyTerm_internal_some` (as `imm_ok`), the
  amount lemma `((ρ y).setWidth yw).toNat % w = (ρ y).toNat % w` (`w ∣ 2^yw`), and
  `put_in_reg_sext32/zext64/sext64` (same shape as `zext32_*`); each rule then through
  `shift_ruleOk`.
- `bnot_ishl` 1401: `ishl`/`iconst` look-through (`defInst_iconst_inv` pattern) and an `ispec`
  arm for `aluRRRShift .orrNot` with `xzr` first operand (M4AluA2 has the `[a, b]` arm).
- `sbfm`/`ubfm` 1704/1707: two look-throughs, `bfm_immr/imms`, ispec `bitfieldMove`.
- rotates 1772–1808, 1840–1862: `small_rotr`/`small_rotr_imm`, `rotr_mask`,
  `rotr_opposite_amount`, iconst look-through; ispec forms exist (`extr`); `shift_ruleOk` applies.
- `popcnt` 2074–2092: vector ispec forms (`movToFpu`, `vecMisc cnt`, `vecRRR addp`,
  `vecLanes addv`, `movFromVec`) not yet specified.
- Name collisions for the integrator: `szOf`, `getAs_isSome`, `lowerInstOk_one`,
  `SameWorld.trans'` exist in both this branch and `agent/m4-alu-a`.

### Integration note (Integrate1: m4-ctl + m4-alu-b)

Shared helpers deduplicated: `szOf`, `szOf_bits`, `env4`, `env5` now live in `IselRulesALU.lean`;
`SameWorld.trans'`, `getAs_isSome` in `IselFamily.lean`. Family-B lemmas whose names clashed with
different family-A/Cmp lemmas carry the suffix `_fb`: `lowerInstOk_one_fb`, `alu_rr_imm12_run_fb`,
`alu_rr_imm_logic_run_fb`, `ctor_imm_logic_some_fb`, `ctor_imm_logic_none_fb`, `ctor_zero_reg_fb'`,
`extVal_fb`, `ofV_aluRRImm12_fb`, `ofV_aluRRImmLogic_fb`, `ofV_aluRRImmShift_fb`, `ofV_extend_fb`.
`ispec`: the M4Cmp/M4Ctl forms precede the family-A generic forms (the Cmp `mSub` case is dropped:
the generic `mulAddVal` case gives the same value).

## Memory family (loads/stores/stack_addr/symbol_value) — M4Mem

**Status: contract + infrastructure; no memory root rule proven yet** (request budget).
Branch `agent/m4-mem`.

**Contract change #7** (335353d, on main ddf0955; announced to all): memory rules cannot be
`LowerRuleOk` for an arbitrary `MR`, so, like calls (#5), they are split out.
* `IselContract`: `amodeAddr sb am bytes uses w` (effective address of the emitted amode forms,
  immediates as the ISLE rules check them, as M6's `AMode.addr`), `loadSigned`, `loadVal`,
  `MemRefines F sb syms isem` (M6 obligation for `csem`: loads/stores through `amodeAddr`
  avoiding `F`, `loadAddr (slotOffset off) = sp + off + sb`, `loadExtNameGot` of a linked symbol
  = its address — with `CallsRefine` this pins its `sym` on linked symbols), `MemRelOk F sb syms f MR`
  (bytes, allocations outside `F` and below 2⁶⁴, `symbols = syms`, slot `id` at
  `sp + sb + off(id)`, stores on both sides keep the relation), `memRootRule` (815, 824, 1027,
  1041–1044, 1052–1057, 1064–1070, 1093), `MemRuleOk`, `MemRulesCorrect`; `LowerRulesCorrect`
  gains `memRootRule r = false →`.
* Soundness gap closed: `Clif.run` accepts a load/store address of any type, but the lowering uses
  the whole 64-bit register as base, so the rules are false for `i32` addresses. `buildCtx`
  already rejects them; `CtxInv.addr64` records it (`ctxOk` decides it, `ctxOk_sound` proves it).
* `InstCalls f …` is now indexed by the function (the slot relation is per function);
  `instCalls_of_rules`/`lowerInstOk_of_rules`/`lowerInstOk_runTerm` take `MemRulesCorrect`,
  `MemRefines`, `MemRelOk`; `E2E.memRelOk_holds` proves `MemRelOk` for `Rel.holds`;
  `backend_correct(_of_rules)` take `hmemRules : MemRulesCorrect program` and
  `hmem : ∀ s, MemRefines (F s) slotOff syms (sem s)`.

**Files.** `IselMemArm` (CLIF `readBits`/`writeBits` ↔ Arm `read_mem_bytes`/`write_mem_bytes`:
`readBits_getLsbD_eq`, `read_mem_write_mem_bytes`, `writeBits_bytes`, `writeBits_setWidth`),
`IselMemBase` (extern `iff` lemmas of the memory helpers; tactics `mem_inv hp [..] at h…`,
`mem_refute`, `mem_split hp hc h t` — `isel_inv'`-style, keeps `hp`), `IselMemRun` (`RtOk`,
`amVregs`/`amUses`, `load_ops`/`store_ops` operand views, `seqRun_isem_one`, `lo64_of_holds`,
`Runs.of_prun`), `IselMemAmode` (`AddOk`, `amode_add_ok`: all three rules of `amode_add`;
`add64_inv`, `add_imm64_inv`, `imm64_inv`, `addOk_imm12`, `addOk_add`).

**Remaining (plan).** Contracts `amode_reg_scaled` (576, 3 rules), `amode_no_more_iconst`
(575, 9 rules), `amode` (574, 4 rules incl. `stack_addr` → `SlotOffset`) with the statement
`Frag ∧ ∃ am, amv.amode? = some am ∧ AmVregs am ∧ ∀ fr ρ w pv, RtOk … → fr.regs x = some pv →
pv.ty = .i64 → UsesLo … ∧ Runs … (amodeAddr sb am bytes (amUses am ρ') w' = some (ofInt 64
(pv.toNat + off)))` (DFG look-through via `binary_value`/`extend_value`/`shift_const_value`);
helper terms `aarch64_{u,s}load*` (529–535), `aarch64_store*` (541–544) + `side_effect_inst_ok`,
`compute_stack_addr` (643), `load_ext_name` (570: rules 3991/3996 fail since `is_pic`),
`load_ext_name_got` (571); root rules by `root_match_data` + `instData` inversion (load format 16,
store 22); 815/824 are vacuous (`ctor_is_sinkable_inst`). Byte lemmas for the load value / store
are in `IselMemArm`.

**Axioms**: `propext`, `Classical.choice`, `Quot.sound` (no `sorry`).
