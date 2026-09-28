# Lean mid-end (`FV/Opt`), M7

<!-- The mid-end pass owns this contract; the section below is the rule-data interface it
consumes. Details: `docs/contracts/isle.md`, "Mid-end export". -->

## ISLE rule data and `simplify` (`FV/Isle/Opt`, `FV/Isle/Generated/Opt`)

Cranelift 0.136.1's mid-end ISLE unit (`opt`: 1605 rules, 1281 of them `simplify`, 39
`simplify_skeleton`) is exported by `rust/crates/isle2lean` as `Isle.Opt.program`. The
mid-end calls the rules through two entry points in `FV.Isle.Opt.Simplify`, which depends only
on `FV.Clif.Syntax`, the interpreter and the generated data:

```lean
def Isle.Opt.simplify {σ} (enodes : σ → Nat → List Clif.Inst) (typeOf : σ → Nat → Option Clif.Ty)
    (make : σ → Clif.Inst → Nat × σ) (st : σ) (v : Nat) :
    Except String (List (Nat × Bool) × List String × σ)
def Isle.Opt.simplifySkeleton {σ} (enodes …) (typeOf …) (make …)
    (trapBlock : σ → Clif.BlockId → Option Clif.TrapCode) (st : σ) (i : SkelInst) :
    Except String (List SkelSimp × List String × σ)
```

- `enodes st v`: the pure single-result nodes of e-class `v` (operands are e-class ids), in
  the order Cranelift's `InstDataEtorIter` would yield them; `typeOf st v`: its type;
  `make st inst`: insert a pure node (Cranelift `make_inst` → `insert_pure_enode`, which
  simplifies the new node recursively) and return its e-class. `trapBlock`: Cranelift's
  `just_trap_block`.
- Result of `simplify`: every candidate in rule order with whether the rule `subsume`d it
  during this call, and the producing rule's name (parallel lists). Candidates may repeat and
  may be `v` itself (the `remat` rules). Cranelift's driver (`egraph/mod.rs`
  `optimize_pure_enode`) shuffles, truncates to `MATCHES_LIMIT`, sorts and dedups, skips `v`,
  and if a candidate was subsumed keeps only it. Cranelift's generated code also stops after 8
  results (`MAX_ISLE_RETURNS`) in its own order; `simplify` returns all of them.
- `SkelInst` is `.inst Clif.Inst` (`div`, `trapz`, `trapnz`) or `.term Clif.Terminator`
  (`brif`, `br_table`, `jump`); `SkelSimp` is Cranelift's `SkeletonInstSimplification`
  (`remove`, `removeWithVal`, `replace`, `replaceWithVal`, `replaceBranchCond`,
  `replaceWithTwo`).
- Nodes and rewrites outside `Clif.Inst` (float or vector types, `i128` `iconst`, other
  opcodes) are never passed to `make`; the candidates built from them are dropped.
- `.error` means an interpreter error: an unmodeled extern helper, a Rust panic of a helper,
  or fuel. It is never "no rewrite".
- `Isle.Opt.Closure` lists the rules that can fire on E programs at `i8`..`i64` (1357 rules,
  1193 of them roots), the opcodes outside E that rewrites can build (`bmask`, `iabs`,
  `iconcat`, `trapz`, `trapnz`), and the rules that build them.
- Checked against Cranelift (`FVTest/Isle/Opt.lean`, `OptCorpus.lean`): 20 hand-written
  `simplify` calls, 12 `simplify_skeleton` calls and 930 `simplify` calls over the CLIF corpus
  fire the same rules as a `trace-log` build at `opt_level=speed` (per call, on e-classes whose
  operands are single original nodes).
  Nothing about the rules or helpers is proven yet.
