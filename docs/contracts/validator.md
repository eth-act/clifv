# Contract: per-function translation validator (`FV/Validate`, M3)

## Status

Work in progress (agent `validator`).

- [x] `FV/Validate/Basic.lean`: simulation statement (`World`, `Act`, `RetOK`, `TrapOK`,
      `StackOut`, `Matches`, `GoodF`), Arm-progress rules, fuel induction over cut points.
- [x] `FV/Validate/StepThms.lean`: `#vstep` per-instruction step theorems over an abstract
      linked program (adapted from LNSym `#genStepEqTheorems`).
- [x] `FV/Validate/ClifDef.lean`: `#clif_def` (CLIF function literal via the M0 parser).
- [x] `FV/Validate/Rules.lean`: CLIF-side rules (statement, jump, brif, br_table, return, trap).
- [ ] memory relation lemmas, call rule, generator (`lake exe validate`), scripts, results.
