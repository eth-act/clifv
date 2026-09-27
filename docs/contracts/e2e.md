# M7: the end-to-end theorem `backend_correct`

Producer: M7 (agent `M7Skeleton`, branch `agent/m7-skeleton`). Consumers: the integrator, M4
(rule proofs), M6 (register level). Code: `FV/E2E/{Statement,Compose,Main}.lean` (namespace
`E2E`), the CLIF → VCode driver simulation `FV/Backend/Proof/Lower{Seq,Rename,Contract,Frame,Shape,Lemmas,Sim}.lean`
(namespace `Backend.Proof.Driver`). Inputs: `backend-proof.md` (M4 contract `IselContract.lean`),
`regalloc-proof.md` (M6), `encoder.md` (M5), `clif.md` (`Clif.run`).

## Status (2026-09-27)

| Piece | State |
| --- | --- |
| Statement: subset, compiled code, CLIF entry, memory/slot relation, ABI entry/exit, trap relation, resource precondition, conclusion `ArmRefines` | done (`Statement.lean`) |
| Composition CLIF → VCode → prepared VCode → Arm (`backend_correct_of_layers`) | **proven** |
| CLIF → VCode driver simulation (`driver_correct`: statements, returns, traps, `jump` parallel copies, `brif`/`br_table` with and without edge blocks, entry `Args`, alias resolution, DFG consistency, whole runs) | **proven** from `LowerShape` + `Cert` + M4 contracts + `DriverSem` |
| `IselSim` from the driver (`iselSim_of_driver`) | **proven** |
| M4 `lower` calls from M4's rule theorems (`instCalls_of_rules`, via `lowerInstOk_runTerm`) | **proven** |
| `MRStable` of the CLIF ↔ VCode relation (`mrStable_holds`) | **proven** |
| `Clif.run`'s initial state is a `ClifEntry` (`clifEntry_initState`) | **proven** |
| **`backend_correct`** from the hypotheses below | **proven**, sorry-free |
| M7 obligations `LoweringObligations` (`lowerFunction` ⇒ `LowerShape`, `buildCtx` ⇒ `CtxInv`, SSA certificate) and `PrepareCorrect` | open (hypotheses of `backend_correct`; see "Remaining") |

## The theorem (`FV/E2E/Main.lean`)

```lean
theorem backend_correct {p f k vc vcp rf af fa fb}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    {sem F syms slotOff astep env}
    -- M4
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hterms : ∀ s, TermCalls sem (fun sl cm w => Rel.holds ⟨F s, syms, slotOff⟩ f sl cm w))
    -- M6 + M5
    (hM6 : RegLevelCorrect sem F astep vcp af fb)
    -- the shared VCode semantics (M6's `csem`)
    (hRef : ∀ s, Refines (F s) sem) (hds : DriverSem sem)
    -- M7, remaining
    (hlow : LoweringObligations f vc) (hprep : PrepareCorrect sem vc vcp)
    -- the run
    {base ra s args cs}
    (hent : AbiEntry fb base ra s) (hres : StackAvail af s) (hargs : ArgsIn args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff⟩ f cs.frame.slots cs.mem s)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs)
```

`ArmRefines fb base ra astep s o`:

* `o = .returned vals cm` ⇒ `∃ n, ArmRet ra s (runX astep n s) ∧ (∀ j v, vals[j]? = some v →
  XHolds v (xreg j (runX astep n s))) ∧ MemAgree cm (runX astep n s)`;
* `o = .trapped c` ⇒ `∃ n, TrapAt fb base c (runX astep n s)`;
* `stuck`, `outOfFuel`: no claim.

## Definitions (`FV/E2E/Statement.lean`)

* **Width convention**: `VHolds v x := x.setWidth v.ty.width = v.bits` (M4's; low bits, upper
  bits unspecified); `XHolds v x := VHolds v (ofX x)` for a 64-bit register (= low bits for
  widths ≤ 64, `XHolds_iff`).
* **Subset** `InSubset p f`: `p.func? f.name = some f`, `Compile.functionE f` (clif-subset-v2
  E), at most 8 parameters (all in registers), every `call` targets an extern (not a function
  of `p`).
* **Compiled code** `Compiled f k vc vcp rf af fa fb`: `lowerFunction f = ok vc`, `prepare vc =
  ok vcp`, `checkAlloc vcp rf = ok ()`, `lowerRFunc vcp rf = ok af`, `emitFunc k af = ok fa`,
  `fa.layout = ok fb` (`rf` = whatever the untrusted regalloc2 returned).
* **CLIF entry** `ClifEntry f args cs`: no callers, frame of `f` at its entry block, parameters
  bound to `args` (types checked), slot ids of `f`. Slot addresses and memory are free: CLIF
  leaves stack-slot addresses unspecified; `Clif.run`'s bump allocator picks one choice
  (`clifEntry_initState`), the Arm frame another. The theorem is about `Clif.runLoop` from the
  entry state whose slots are at the Arm frame's slot region (`SlotRel`).
* **Memory** `MemRel F syms cm s`: initialised bytes of live CLIF allocations are the Arm bytes
  at the same addresses; every live CLIF address is below 2⁶⁴ and outside the frame addresses
  `F` (the allocator-private part of the frame: spill/save slots, fp/lr); `cm.symbols = syms`
  (link-time `symbol_value` addresses).
* **Slots** `Rel.holds Γ f slots cm w := MemRel Γ.F Γ.syms cm w ∧ SlotRel f (Γ.slotReg w)
  slots`, `Γ.slotReg w = sp(w) + Γ.slotOff`, `SlotRel`: slot `id` is at `base + off(id)` with
  `off` from `slotLayout f.slots`. This is M4's `MR` (`MRStable`, `mrStable_holds`).
* **Traps** `TrapsExplicit env p cs`: every trap of the CLIF run from `cs` comes from a `trap`
  terminator or a `div` (explicit check + `udf`/`trapIf` in the code). Memory-access traps and
  traps inside externs are excluded: the Arm model has no memory faults, callees are outside the
  theorem (for DSL output traps are unreachable, PLAN.md §3.2).
* **ABI entry** `AbiEntry fb base ra s`: code words of `fb` loaded at `base`
  (`s.program = fb.program base`), pc = base, no model error, x30 = ra outside the code, sp
  16-aligned, code fits the address space. `ArgsIn args s`: argument `i` in `x i` (low bits).
* **Resource precondition** `StackAvail af s`: the frame (`af.frameSize` + fp/lr) fits below sp.
  Callee stack use is part of the callee contract (M6's `CalleeSound`).
* **Exit** `ArmRet ra s s'`: pc = ra, no error, sp, x19–x29 and the low 64 bits of v8–v15 as at
  entry. `MemAgree cm s'`: live CLIF bytes = Arm bytes. **Trap** `TrapAt fb base c s'`: no error,
  pc at a trap site `t ∈ fb.traps` with `t.code = c`.
* **VCode observables** `VReturns`/`VTraps` = `VRetFrom`/`VTrapFrom` from `VConf.init`: the
  run reaches `rets us` (values = its use values) / an instruction whose semantics halts and
  whose `trapCode?` is `c`.

## Hypotheses and owners

| Hypothesis | Owner | Status |
| --- | --- | --- |
| `LowerRulesCorrect program`, `ExcludedUnmatchable program` (every closure root rule of `lower` is correct; the others never match) | M4 (`IselContract.lean`) | stated; rules proven family by family (M4AluA/B, M4Cmp) |
| `TermCalls sem MR`: every terminator call `lowerFunction` makes (`lower` on `return`/`trap`, `lower_branch` on branches) satisfies `LowerTermOk` | M4 | open: M4 has `BranchRulesCorrect` per `lower_branch` rule but no `runTerm`-level lemma for branches, and no statement for the `return`/`trap` rules of `lower` (their `info.clif = none`, so `LowerRuleOk` does not cover them) |
| `RegLevelCorrect sem F astep vcp af fb` (VCode returns/traps ⇒ Arm returns/traps, forward) | M6 + M5 (`M6Rest`) | placeholder with the agreed content (w₀ = entry state, `csem` Args/Rets, `F` = allocator-private frame, ret via the `rets` pairs, traps at `fb.traps`) |
| `Refines (F s) sem` (the VCode semantics refines M4's `ispec`) | M6 (`csem` characterization lemmas) | open (M6) |
| `DriverSem sem` (`Args` reads the argument registers of the world, `jump` → `goto 0`, `sem (i.mapRegs g) = sem i` for class-preserving vreg renamings) | M6 (`csem`) | agreed, open (M6) |
| `LoweringObligations f vc` | M7 | open (below) |
| `PrepareCorrect sem vc vcp` | M7 | open (below) |

M6's own premises (`CalleeSound`, jump tables readable, relocation hooks `ArmStepX ext`) are
premises of its instantiation of `RegLevelCorrect`, so they become premises of the
instantiated `backend_correct`; `astep` is M6's `ArmStepX ext` (`stepi` except at calls and
relocated address computations, which run the external hooks).

## The driver lemma (`FV/Backend/Proof/LowerSim.lean`)

```lean
theorem driver_correct (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) (hB0 : f.blocks[0]? = some B0)
    (hcall hfunc hslots hbody hterm hregs) (hmr : MR slots cs.mem w₀)
    (hargs : ∀ i v, args[i]? = some v → VHolds v (regVal w₀ (.x i)))
    (htr : TrapsExplicit-condition) (fuel) :
    RunOk vc sem MR slots ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoop env p fuel cs)
```

`DriverHyp`: `LowerShape` (structure of `lowerFunction`'s VCode), `Cert` (SSA availability
certificate), `DriverSem`, `InstCalls`/`TermCalls` (M4 contracts at the `runTerm` level),
extern-only calls, no `return_call`, `VCode.cfg` succeeds.

Simulation relation `Match s vs`: the CLIF state is at statement `j` of block `bi`, the VCode
state at that statement's segment (`pos bi j`); every value tracked by the certificate
(`A bi j`) is held (low bits) by its **resolved** vreg `gn x` (alias resolution
`MInst.mapRegs (resolve …)`); the frame restricted to the tracked values is DFG-consistent;
memory related by `MR`. Key steps:

* `seqRun_rename` + `operands_mapRegs` (all `MInst`s): the renamed segment run simulates M4's
  run of the un-renamed code from `ρ ∘ gn`, because every register the code reads is either
  written by it or not clobbered by it (certificate + M4's `UsesOk`/`defs`).
* `stmt_step`: statement ↦ segment (results via the rule outputs and the alias map; tracked
  values keep their registers; DFG consistency re-established; explicit traps reach the halting
  instruction).
* `term_step`: `return` (the `rets` instruction and its values), `trap`, `jump` (branch
  arguments as `VStep`'s parallel copy), `brif`/`br_table` (edge blocks: goto, `jump` via
  `DriverSem`, parallel copy), using `succOf_eq` (successors from the last instruction's targets
  with labels = indices).
* `entry_step`: `Args` defines the parameters from x0.. (`operands_args`).
* `sim_run`: induction on fuel.

## Remaining (precise)

1. **`lowerFunction_shape`** (M7): `lowerFunction f = .ok vc → ∃ ctx st0 R gn bl,
   LowerShape f vc ctx st0 R gn bl`. Loop invariants over `lowerFunction`'s `for` loops:
   segment layout, alias map (`gn r = gn out`), `resolve` a class-preserving renaming fixing
   temporaries and parameters, edge blocks, labels = indices, `tseg ≠ []`. Includes
   **`buildCtx` ⇒ `CtxInv`** (M4's context facts incl. `instData` data, result types,
   `valueReg`, `defInst`, the new `defClif`) and `ctx.func = f`.
2. **SSA certificate** (M7): `Cert f ctx st0 gn bl A` for some `A`. Either an executable
   certificate checker over the lowering records (computing `A` by an available-values
   dataflow, checked like `checkAlloc`'s `verify`), or a proof from SSA dominance (the value
   definitions strictly dominating the point). Holds for Cranelift-verifier-valid CLIF.
3. **`PrepareCorrect`** (M7): `prepare` (unreachable blocks dropped, critical edges split by
   `jump` blocks, RPO reordering) preserves VCode returns and traps.
4. **`TermCalls`** (M4): see the table.
5. **`FrameTyped`** (M7, integrator decision 2026-09-27): once `DFGCons` gains the conjunct
   `FrameTyped ctx fr` (M4AluA), the driver must maintain it: needs a typing lemma for
   `evalInst`/`instOutcome` on E instructions (results have `resultTypes`), `CtxInv` facts
   relating `valueType?` to parameter/result types, and `enterBlock`'s type check.
6. **Scope extensions**: calls between compiled functions (induction on call depth, using
   `backend_correct` of the callee as its callee contract); stack-passed parameters
   (`InSubset.regParams`); memory-access traps (need a fault model).

## Trusted (not proven)

* Lean kernel, `bv_decide`'s LRAT checker / compiled evaluation (M5, M6 axioms); Lean's and the
  C compiler that run the compiler.
* **Arm model fidelity** (`FV/Arm`, ASL-derived, co-simulated against qemu) and **`Clif.run`
  fidelity** (checked against Cranelift's interpreter and native runs), including the choice
  that CLIF slot addresses are unspecified (`ClifEntry`).
* **Object writing, linking and loading** (`elfObject`, rust-lld, the loader): the words of `fb`
  at `base`, relocations resolved to `syms`/callee addresses (M6's hooks), GOT contents.
* **Runtime/callee contracts**: externs implement `Clif.Env.extern` under AAPCS64
  (`CalleeSound`, stack use); OS behaviour at `udf` (SIGILL reported as the trap-table code).
* Frontend (pluggable, PLAN.md §4 M7 restatement).

## `#print axioms`

```
E2E.backend_correct, E2E.iselSim_of_driver, Backend.Proof.Driver.driver_correct,
Backend.Proof.Driver.instCalls_of_rules, E2E.clifEntry_initState:
  [propext, Classical.choice, Quot.sound]
E2E.backend_correct_of_layers: [propext, Quot.sound]
```
