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
