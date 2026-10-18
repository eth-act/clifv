# `Opt.Legalize128` and its validator (`Opt.Legal.checkW`)

Status: **proven end to end.** `E2E.backend_correct_legal_wide` (`FV/E2E/Legal.lean`) covers
every function whose legalisation the validator accepts and whose legalised form is inside the
backend theorem (`InSubset`, `lowerCheck`); `lean-backend` reports those verified.
`E2E.backend_correct_legal` is the same theorem on the domain of `Opt.Legal.check` (`checkW`
without `try_call_indirect` and `call_indirect` at an `i128` signature, "Indirect calls at
`i128` signatures" below).

## Design (validator with fallback)

`Opt.Legalize128.function128Cert f` (untrusted, `FV/Opt/Legalize128Pass.lean`) returns the
legalised function `g` and a certificate `Cert` (the `(lo, hi)` pair of every `i128` value,
the shared zero of the pad values). `Opt.Legal.check f g cert : Bool` (`FV/Opt/Legal.lean`)
re-derives, statement by statement, the segment of `g` each statement of `f` must be
rewritten to (`planOf` → `Plan`: `same`, a renamed instance of a canonical *pure pattern*,
two `i64` loads/stores, a `__*ti3` helper call, an ABI-expanded call, a condition pattern +
`trapz`/`trapnz`, a `call_indirect` without `i128` operands with the same call-site
signature in `g` (`callInd`)), and checks the terminators (including `try_call`: arguments and
returns expanded like a `call`'s, the normal-return successor's arguments by `expandTry` —
an `i128` value or `retN` as its pair —, the call's fresh result values above every value of
`f` resp. of `g`, the pairs and the pad zero), block parameters (AAPCS64 pads), signature,
value-id layout (values of `f` `< T0 = maxValueId f`; pair components and zero distinct and
`≥ T0`; temporaries/pads fresh) and unique definitions.
`lean-backend` (`Opt.Legalize128.parsedFile128`) runs `checkW` on every legalised function:
a rejected function is flagged unverified (`i128 legalized (outside backend_correct:
Opt.Legal.checkW rejects)`); an accepted one is compiled like any other function — the backend
decides `InSubset` (`unverifiedReason?`) and `lowerCheck` on the legalised form, and a function
passing both is reported verified (`E2E.backend_correct_legal_wide`). Source and target
activations use programs with empty function tables, so the theorem's external-call and
indirect-resolution program conditions hold even for self-calls. `parsedFile128` no longer
rejects extern names matching functions in the file. Under `--opt` every legalised function
is still flagged (no theorem composes legalisation with the mid-end). `lean-e2e-check`
legalises too and checks the accepted functions like any other.

Measured: the check accepts all legalised functions of the survey `g_u128` crates
(debug/release/release-oc: 41) and the i128 Cranelift runtests (163), and rejects all 1197
single-statement mutants of those outputs (`/tmp` harness, not committed).

**Verified (flip):** survey (933 functions) **31** of the 41 legalised functions (debug 11,
release 10, release-oc 10; the other 10: `sret` 5, calls of a function of the file 5 — these
also declare that function as an extern); runtests **159** of 163 (outside `E` 2, stack
parameters 1, a call of a function of the file 1); `lean-e2e-check`: the 159 are in scope and
accepted by `lowerCheck`/`prepCheck`/`formsCoveredB` (1069 accepted / 0 rejected / 0 not
covered, was 910). `cargo fv test` (debug; report entries of functions whose CLIF mentions
`i128`, previously all `i128 legalized`): fv-demo **19** verified of 27 (6 `sret`, 2
`downcast_ref` instances the validator rejects: they contain a `call_indirect`), survey
example **34** of 46 (12 `sret`), vendor **2** of 10 (8 `sret`). The compiled code is
unchanged (only the labels: an accepted function is now lowering-validated).

Gates (2026-09-30, after merging main): `lake build FV FVTest FV.E2E FV.E2E.OptProven
FV.E2E.Legal` green; `lean-backend-filetests.sh` corpus 114/114 (extrt 22/22), runtests 4672
pass / 0 fail / 0 disagree; `lean-backend-encode-check.sh` 1260 identical / 0 differ;
`lean-e2e-check` 1069 / 0 rejected / 147 out of scope, `formsCoveredB` 0 not covered.

## Legaliser changes (required for provability / correctness)

* `iconcat`, `isplit.i128`, `ireduce.i64` of `i128`, `bitcast.i128` emit copies (`bor x, x`)
  instead of aliasing a pair: distinct source values never share a target value, so the value
  relation needs no dominance argument. Constant shift amounts through `iconcat` are still
  folded (`St.concatLo`).
* Shift-amount constants are folded by their **unsigned** value (`constOfDef` used `Int.toNat`
  of the signed immediate: `ishl x, iconst.i8 -1` shifted by 0 instead of 127 — a miscompile).
* `umulhi`/`smulhi` at `i128` are no longer legalised (the expansion returned
  `(0, low64(high half))`, wrong in general, e.g. `umulhi(2^64, 2^64) = 1`); such functions stay
  unsupported.
* `Clif.Rust.env`: `__*ti3` return with the caller's memory (was `Mem.empty`), and the
  `sdiv(i128::MIN, -1)` overflow test examines the dividend (it tested the divisor twice and never
  fired). The helper names are matched before `isPanic` (same semantics — the four names are not
  panic names — but the lookup is provable without evaluating `String.splitOn`).
Differential after the changes: `clif-filetest --legalize128` over the 64 i128 runtest files:
legal pass 973 / fail 7 / agree 980 / **disagree 0** (the 7 fails are original-program failures
in `i128-load-store.clif`, agreed by the legalised form).

## The end-to-end theorem

Axioms of every theorem below: `propext`, `Classical.choice`, `Quot.sound` (since T6 no
`bv_decide`/`native_decide` certificate in the backend or `FV/Opt/Proof/Legal*` proofs).

```lean
theorem E2E.backend_correct_legal {f g : Clif.Function} {cert : Opt.Legalize128.Cert}
    (hchk : Opt.Legal.check f g cert = true)
    {p p' : Clif.Program} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p' g) (hc : Compiled g k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff K : Nat}
    (hext : ∀ fn e, f.extern? fn = some e → p.func? e.name = none)
    (hext' : ∀ fn e, g.extern? fn = some e → p'.func? e.name = none)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H
      vcp.CallSite)
    (hX : ∀ s, XCallsOk Clif.Rust.env (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff⟩ g sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Clif.Val}
    {cs cs' : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hargs : ArgsIn args' s) (hcs : ClifEntry f args cs) (hcs' : ClifEntry g args' cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff⟩ g cs'.frame.slots cs'.mem w₀)
    (htrS : TrapsExplicit Clif.Rust.env p cs) (htr : TrapsExplicit Clif.Rust.env p' cs')
    (fuel : Nat) :
    ArmRefinesLegal ((Opt.Legal.groups f.sig.returns).getD []) fb base ra (ArmStepX X H fa) s
      (Clif.runLoop Clif.Rust.env p fuel cs)
```

`ArmRefinesLegal rg … (.returned vals cm)` is `∃ vals', ExpRel rg vals vals' ∧ ArmRefines …
(.returned vals' cm)` (an Arm return, callee-saved registers restored, `vals'` in x0.., the
live CLIF memory `cm` in the Arm memory); for traps (and `stuck`/`outOfFuel`) it is
`ArmRefines`. `ExpRel gs vs vs'`: the ABI split of `vs` by the slot groups of the signature —
a plain value as itself, an `i128` value as its low/high `i64` halves, after a pad register
(any `i64`) where AAPCS64 aligns the pair. So: running the Arm code of `g` with the ABI-split
arguments `args'` refines the original `i128` function's `Clif.run` on `args` — split
results, same memory, same trap codes.

Premises, beyond `backend_correct_final`'s about `g` (`InSubset p' g`, `Compiled`,
`FormsCovered`, `CalleeOk`, `XCallsOk`, `hsym`/`hslot`, the Arm entry `AbiEntry`/`StackAvail`/
`BodyEntry`/`ArgsIn`, `ClifEntry g`, `Rel.holds`, `TrapsExplicit` of the run of `g`):
* `hchk`: the validator accepted `g` (with the certificate `cert`);
* `hext`/`hext'`: calls of `f` (in the original program `p`) and of `g` (in the legalised
  program `p'`) go to the environment: no function of the program has a declared extern's name
  (`lean-backend` checks both, `parsedFile128`);
* `hexp`, `hcs`, `hsl`, `hmem`: the source run is `f`'s on `args`, from the same slots and
  memory, `args'` its ABI split;
* `htrS`: every trap of the source run is explicit (`TrapsExplicit`, as in the backend
  theorem). It gives `NoMemTrap` (`noMemTrap_of_trapsExplicit`): the split 8-byte accesses and
  the 16-byte source access agree whenever the source access does not trap.
* `htr` stays on the run of `g` (as in `backend_correct_opt_proven`: not derived from the
  source's). An `i128` division by zero or `sdiv MIN, -1` traps in `f` at the `div` (explicit)
  but in `g` inside the `__*ti3` call — an extern trap, outside the backend theorem like every
  extern trap (natively the helper aborts), so such runs are not covered.

Discharged: the environment contracts for `Clif.Rust.env` (below), `MemBounded` of the entry
memory (`memBounded_of_holds`: `MemRel.valid` of the backend relation), `NoMemTrap`.
`backend_correct_legal_env` is the same theorem for any environment with `HelperOk`,
`ExtLegal` and `EnvKeepsAllocs`.

## Completeness: no validator premise (2026-10-02)

The pass is driven by the validator's plans: it gives every `i128` value a pair of consecutive
fresh ids (`allocPairs`, the certificate) and the pad zero the next id, then emits for every
statement the segment of its `planOf` plan (`emitPlan`: the canonical pattern with temporaries
`base + c` above the zero, the two `i64` accesses, the helper call, the expanded call), and
for terminators and block parameters exactly what `termOk`/`entryParamsOk`/`paramsOk` expect
(throwing otherwise). `Opt.Legal.check` is proven complete for its output
(`FV/Opt/Proof/LegalComplete.lean`, `LegalDirect.lean`, `FV/E2E/LegalDirect.lean`):

```lean
structure Opt.Legal.Complete.Pre (f : Function) : Prop where
  mentions : mentions128 f = true
  defs : ((defsOf f).map (·.1)).Nodup
  ids : ∀ v ∈ idsOf f, v < maxValueId f
  noSelf : ∀ b ∈ f.blocks, ∀ s ∈ b.body, ∀ x ∈ instOps s.inst, x ∉ s.results
  callInd : ∀ b ∈ f.blocks, ∀ s ∈ b.body, ∀ sig callee args,
    s.inst = .callIndirect sig callee args → ∀ d, f.sigDecls.lookup sig = some d → sig128 d = false
  noTryInd : ∀ b ∈ f.blocks, ∀ c args et, b.term ≠ .tryCallIndirect c args et

theorem Opt.Legal.Complete.check_complete (hp : Pre f)
    (h : function128Cert f = .ok (g, cert)) : check f g cert = true
theorem Opt.Legal.legalize_refines (hp : Complete.Pre f) (hl : function128Cert f = .ok (g, cert))
    … (check_refines's premises) : (returns of f ⇒ split returns of g) ∧ (traps ⇒ traps)
theorem E2E.backend_correct_legal_direct (hpre : Opt.Legal.Complete.Pre f)
    (hlg : Opt.Legalize128.function128Cert f = .ok (g, cert)) … (backend_correct_legal's other
    premises) : ArmRefinesLegal …
```

`Pre`: `mentions` (otherwise `function128Cert` returns `f` itself), the two `f`-only conjuncts of
`check` (`defs`, `ids`), a statement never reads its own result (`noSelf`: the pattern's outputs
must not overwrite its inputs), and no `call_indirect` with an `i128` signature and no
`try_call_indirect` (the domain of `check`, `indOldB`). `PreW` is `Pre` without the last two
conditions; `checkW_complete : PreW f → function128Cert f = .ok (g, cert) → checkW f g cert`
(S4, below). Axioms: `propext`, `Classical.choice`, `Quot.sound`. The compiler keeps running
`checkW` as a runtime double-check. Behaviour: on the 64 `i128` runtest files `clif-filetest
--legalize128` gives legal pass 973 / fail 7 / agree 980 / disagree 0 (unchanged), and `check`
accepts all 163 legalised functions (185 `i128` functions, 22 not legalisable).

## Layers (all proven)

**`Opt.Legal.check_refines`** (`FV/Opt/Proof/LegalSim.lean`): for `check C.f C.g C.cert = true`,
from entry states of `f` on `args` and of `g` on `args'` (`ExpRel (groups f.sig.params) args
args'`; same slots and memory), if `Clif.runLoop env p fuel` of `f` returns `vals` with memory
`m1`, then `runLoop env p' k` of `g` returns `vals'` with `ExpRel (groups f.sig.returns) vals
vals'` and the same `m1` for some `k`; if it traps with `c`, `g` traps with `c`. Premises:
`EnvOk env C p p'` (externs of `f`/`g` are not functions of `p`/`p'`; `HelperOk`, `ExtLegal`,
`EnvKeepsAllocs`), `MemBounded m` (valid ranges below `2^64`), `NoMemTrap env p` of the source
run (no reachable source step traps at a load/store — chosen over an alignment/in-slot check: a
16-byte access whose two 8-byte halves are valid in two adjacent allocations traps while the
split access does not).

**The environment contracts for `Clif.Rust.env`** (`FV/Opt/Proof/LegalRust.lean`):
* `helperOk_env`: the `__*ti3` helper of each `DivOp`, on the `i64` halves of two 128-bit
  operands, returns the halves of `Clif.Sem.div` at `i128` and traps exactly where it traps
  (`int_divz` on a zero divisor, `int_ovf` on `sdiv MIN, -1`). `core_op`: the helper's pair
  arithmetic (`lo + hi·2^64` with the signed reading for `hi ≥ 2^63`; truncated division on
  magnitudes) is `BitVec.udiv/umod` by `toNat`, `BitVec.sdiv/srem` by `toInt_sdiv`/
  `toInt_srem` (`Int.tdiv`/`Int.tmod` on the magnitudes).
* `extLegal_env` (for every extern, so `ExtLegal` is not a premise): the helpers accept both the
  `i128` form and the pair form (`div128_wide`/`div128_pair` reduce both to `core`); `mem*`
  reads only its first three (`i64`) arguments, which the expansion leaves in place, and returns
  non-`i128` values; panics trap unconditionally.
* `envKeepsAllocs_env`: `mem*` writes bytes only; the helpers return the caller's memory.

Modules: `LegalShift*` (variable shifts/rotates: 7-bit amounts; each module < 20 s, < 2 GB),
`LegalMem` (split load/store), `LegalExt` (ABI expansion `ExpRel`, contracts), `LegalPlan`
(`pure_step`), `LegalSim` (`enter_sim`, statements, terminators, `step_sim`, `sim_run`,
`check_refines`), `LegalRust` (the contracts for `Clif.Rust.env`), `FV/E2E/Legal.lean`.
Before T6, `LegalArith`/`LegalShift` called `bv_decide -enums`: the enum pass realizes
`Clif.Ty.enumToBitVec` in the calling module, as `FV.Backend.Proof.IselCmpExt` does, and two
modules realizing the same constant cannot be imported together. Their kernel-checked T6 proofs
realize no such declaration (`LegalArith.lean` header).

## `try_call` and `call_indirect` (agent/last-unverified, 2026-10-01)

Survey `g_u128` test functions (`try_call`s of `i128` functions) and `downcast_ref` instances
(a `call_indirect` next to an `i128` `TypeId` compare) were the last legalised functions the
validator rejected. The simulation (`LegalSim`): `sim_try` matches the source's two steps (the
call, results bound at `f.freshValue + i`; the jump) with the target's (`SimStep`: the
intermediate state is related only through its next step; `sim_run` is by strong induction);
`crel_bind` keeps the relation (the source's result ids are not values of `f`, `DefOk` holds
for undefined ids; the target's are fresh); `expandTry_holds` relates the successor
arguments. `sim_callInd`: same values, same signature; the callee address holds no function
of `p` (`NoIndInternal`, from the source's `TrapsExplicit.indirect`) nor of `p'`, and resolves
to the same extern (`EnvOk.ind`: same function names, `p.externNames <+: p'.externNames`;
premise `hind` of `backend_correct_legal`, decided by `parsedFile128` — the legalised file's
externs extend the original's, true for every file whose legalisation only appends `__*ti3`
helpers). New premises of `backend_correct_legal`: `hCT` (`try_call` callee contract), `hXI`
(indirect-call contract), `hind`; all vacuous for functions without such calls
(`backend_correct_legal_callFree` is the former statement).

## The decidable `Pre` (S6, #30)

`Opt.Legalize128.preB f : Bool` (`FV/Opt/Legalize128Pre.lean`) decides
`Opt.Legal.Complete.Pre f` (`preB_iff : preB f = true ↔ Pre f`,
`FV/Opt/Proof/LegalPre.lean`): `mentions128 f`, distinct definitions, every value id below
`maxValueId f`, no statement reading its own result, no `call_indirect` with an `i128`
signature, no `try_call_indirect`. `check_complete_of_preB`: the validator accepts every
legalisation of a function with `preB f = true` — on that domain the runtime `Opt.Legal.check`
is provably redundant (the compiler still runs it as a double-check). `legalOkB f` (the source
domain of one function): the pass succeeds and is either the identity (no `i128`) or `preB f`;
`legalOkB_cases` splits it. Witnesses (`Opt.Legal.Complete.Witness`): `add128` satisfies `Pre`
and its legalisation is accepted; `add64` (no `i128`), `dupDef` (`defs`), `bigId` (`ids`),
`selfRead` (`noSelf`), `indI128` (`callInd`), `tryInd` (`noTryInd`) do not.

## Whole-program refinement of the original program (S3, #27)

`E2E.LegalProgram.legalProg P` replaces every function of `P` by `legalize` (the pass's output,
the function itself where the pass fails). `legalProg_refines` (`FV/E2E/LegalProgram.lean`):

```lean
theorem E2E.LegalProgram.legalProg_refines {P : Program} {B : Env} {syms : String → Option Nat}
    (hC : ProgCtx P B syms) {h : Function} (hh : h ∈ P.funcs) {args args' : List Val}
    {fr fr' : Frame} {m1 : Mem} (hE : EntryRel h args args' fr fr')
    (hG : GoodFrom B P (SomeInd (legalProg P)) syms ⟨fr, [], m1⟩) (M : Nat) :
    (∀ rv m2, Clif.runLoop B P M ⟨fr, [], m1⟩ = .returned rv m2 →
      ∃ rv', ExpRel ((groups h.sig.returns).getD []) rv rv' ∧
        ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .returned rv' m2) ∧
    (∀ c, Clif.runLoop B P M ⟨fr, [], m1⟩ = .trapped c →
      ∃ k, Clif.runLoop B (legalProg P) k ⟨fr', [], m1⟩ = .trapped c)
```

* `ProgCtx P B syms` (the source domain): every function `legalOkB`; distinct names; no
  `return_call` in `P` nor its legalisation; declarations of `P`'s functions carry their
  signatures (in both programs); no function named like a `__*ti3` helper; where a function
  mentions `i128`, the base environment's contracts `HelperOk`, `ExtLegal`, `EnvKeepsBounded`;
  where the legalised program has indirect calls, `IndScope` and no signature known to `B`.
* `EntryRel`: `h`'s entry frame on `args`, the legalisation's on the ABI-split `args'`
  (`ExpRel`), the same slots (as `E2E.ClifEntry`, slot addresses free).
* `GoodFrom` (the source run): every whole-program state reachable from the entry has valid
  ranges below `2^64` and traps at no load/store (and, with indirect calls, the link-time
  symbols). For returns the load/store clause is automatic (`memTrapFree_of_returned`).

The proof (by induction on the source fuel, `prog_refines`) runs the per-activation refinement
with **two environments**: the source activation runs under the linked environment of `P`
(`runLoop_linkN`), restricted to callee entries whose whole-program states are good
(`guardEnv`, `guard_run`: the source run enters only such callees), the target activation under
the linked environment of `legalProg P` (`tgtEnv`, unbounded callee runs).
`Opt.Legal.check_refines2` / `legalize_refines2` (`LegalSim.lean`, `LegalDirect.lean`) are
`check_refines`/`legalize_refines` for a source environment `env` and a target environment
`env'` related by `EnvOk2` (`ExtRelAt`: each extern `f` declares, called with split arguments
in `env'`, returns the split results of its `env` call; `CallIndRel`: indirect calls resolve
alike; the source's externs keep valid ranges bounded; `HelperOk env'`); `check_refines` is the
case `env' = env` (`EnvOk.two`, statement unchanged). A function without `i128` runs the same
code (`ident_run`). The induction hypothesis relates the two environments at every callee
(`extRel_prog`, `sameAt_link`, `callIndRel_link`). The target's per-function run is a
whole-program run (`Clif.unlink_run`, `FV/E2E/LinkClifRev.lean`: the converse of
`runLoop_linkN` for every environment that unlinks the program, `Unlink`).

Witnesses (`FV/E2E/NonVacuityLegalProgram.lean`, under `Clif.Rust.env`): the closed program
`{add128, caller, plain}` (`caller` builds an `i128` and calls `add128` twice — an `i128` call
between program functions, legalised to the split call; `plain` has no `i128` and calls
`caller`): `ctx` (`ProgCtx`), `plain_refines` (`plain(5)` returns `10` in both programs),
`add_refines` (`add128` on two `i128` values, legalised on the split arguments, returns the
split sum).

## The executable compiler on the original source program (S2, #26; S3)

`compileExe` runs no optimiser: `FnInput.func` is the parsed function after `parsedFile128`, and
`pipeT` is the backend. `E2E.LinkCheck.FnInput.src` is the parsed function before the pass;
`FnInput.func_eq : fi.func = legalize fi.src` for every input (`parsedFile128` keeps a function
whose legalisation fails or is rejected by `check`, as `legalize` does), so
`LinkInput.prog_eq : I.prog = legalProg I.srcProg` (`FV/E2E/LegalSource.lean`). `SrcScopeB I`
(`FV/E2E/SrcScopeDefs.lean`, proof-free so `lake exe lean-link --verified` decides it) decides
the source domain on the parsed functions (`legalOkB`, `linkFreeB`, `declSigB`, no
`__*ti3` name); `srcCtx` turns it, with the facts `compileExe` already proves of the legalised
program (`LinkSys.Ok`), into `ProgCtx`.

```lean
theorem Link.compileExe_correct_source {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f)
      (StackBound.stackFn S.input (legalize f)) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
          (step S.input B file) r (RelocAt S.input) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap B.env S.input.srcProg cs → ∀ c,
      Clif.runLoop B.env S.input.srcProg M cs = .trapped c →
      ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
        (step S.input B file) r (RelocAt S.input) (.trapped c))
```

(`FV/Link/ExeSource.lean`; axioms `propext`, `Classical.choice`, `Quot.sound`.) A return of the
**original** program's whole-program CLIF run of `f` on `args` is the executable's return of the
results split by `f`'s return groups (`ExpRel`), with the same live memory; a trap is the same
trap. No checker premise: `SrcScopeB` is an input condition decided on the parsed CLIF.

Remaining premises beyond `compileExe_correct`'s (which are stated about the target entry `cs'`
of `legalize f`):

| Premise | Kind | Notes |
| --- | --- | --- |
| `hlegal`: `HelperOk`, `ExtLegal`, `EnvKeepsBounded` of `B.env` when a source function mentions `i128` | environment (outside code) | proven for `Clif.Rust.env` (`helperOk_env`, `extLegal_env`, `envKeepsAllocs_env`) and for `Link.SourceWitness.helperEnv` |
| `hsig`: `B.env.sigOf = none` when the program has indirect calls | environment | `IndScope` already requires it of the linked system's own resolution |
| `hcs`, `hexp`, `hsl`, `hmem`: the source entry `cs` on `args`, `args'` its ABI split, the target's slots and memory | choice of the reference runs | as `ClifRun` for the target |
| `hbnd`: every memory of the source run has valid ranges below `2^64` | run condition | `Clif.run`'s bump allocator can exceed `2^64`; proven for slotless programs under externs keeping allocations (`E2E.LegalProgram.Witness.bounded_of_noSlots`) |
| traps only: `NoMemTrap` of the source run | run condition | a 16-byte access whose halves lie in two adjacent allocations traps in the source and not after the split; proven for returning runs (`memTrapFree_of_returned`) |
| traps only: `TrapsExplicit` of the target run at every fuel | run condition | the target fuel is the legalisation's; for returns derived (`trapsExplicit_of_run`) |

Witnesses: `FV/E2E/NonVacuityLegalSource.lean` (`SrcScopeB` of an identity-mixed input
`{plain, add128}` whose compiled program differs from its source; four inputs outside it, one per
conjunct: `return_call`, a `__udivti3`-named function, an `i128` indirect call, a declaration
with another signature). `FV/Link/NonVacuityExeSource.lean`: `helperBase` (the closed base
environment with the Rust `__*ti3` helpers in CLIF) meets `BaseOk`, `HooksSim` and the `i128`
contracts for programs without TLS, indirect calls or helper calls
(`compileExe_correct_source_helper`). `crate-proofs/Crates/CompileExeSourceWitness.lean`:
`compileExe` compiles `g_u128`'s `wmul_u128(i128, i128) -> i128` and its callee
`core::num::<u128>::wrapping_mul` (an original `i128` call), the input is in `SrcScopeB`, the
original program's run of `wmul_u128` on `2^64 + 3` and `5` returns `5 * 2^64 + 15`, and the
executable machine, called with `3, 1, 5, 0` in x0–x3, returns `15, 5` in x0, x1
(`compileExe_source_witness`).

**Recursive programs and the shipped compiler (L1f, #217).** `Link.compileExe_correct_source_peak`
(`FV/Link/ExeSource.lean`): the same without `hc`, the outside caller providing `frameDrop (art
S.input (legalize f)).af + S.input.D * d` bytes where `hd : Clif.DepthLe B.env S.input.srcProg d
cs` bounds the call depth of the **source** run; the trap half takes `TrapsExplicit` under
`Clif.linkEnvD … F d` at every `F`. The legalisation keeps the call depth
(`E2E.LegalProgram.legalProg_refines_depth`, `FV/E2E/LegalDepth.lean`: the matched legalised run
has depth at most `d`; e2e.md "The shipped compiler"), so it composes with
`compileExe_correct_peak`. `Link.DeadCleanup.compileExe_correct_source` and
`…_source_peak` (`FV/Link/DeadCleanupExeSource.lean`) are the two source theorems for the compiler
`lean-link` runs by default, over `S.inputCleanup` (`prog S.inputCleanup = legalProg
S.inputCleanup.srcProg`, `Link.DeadCleanup.prog_eq_legal`). Witnesses:
`crate-proofs/Crates/CompileExeSourcePeakWitness.lean` (the self-recursive `i128`
`rec128(x, n)`; source depth 3; returns `24, 8`), `DeadCleanupExePeakWitness.lean`
(`cleanup_source_peak_witness`), `DeadCleanupExeSourceWitness.lean` (`wmul_u128` under the
cleanup compiler).

## Stack-passed `i128` arguments (S4, #28)

`expandGroups` (`FV/Opt/Legalize128.lean`) follows Cranelift's aarch64 `compute_arg_locs`
beyond the registers: integers take `x0..x7` and floats `v0..v7` (separate counters; floats no
longer consume an `x` register), then 8-byte stack slots; an `i128` that does not fit in
`x0..x7` takes a 16-byte stack slot at the next 16-aligned offset, low half first, and Cranelift
does not advance `next_xreg`. The legalised signature passes the halves as two `i64` parameters,
which the backend places in the next stack slots once `x0..x7` are used up (`argLocs`):
registers used up, the pair, after an `i64` pad when the stack offset is not 16-aligned; only
`x7` left, a pad in `x7` and the pair on the stack (a 16-aligned offset required). Cranelift
passes a later integer parameter in `x7`, which the legalised signature cannot express: such
signatures (and the `x7` case at an unaligned stack offset) still make the legalisation fail.
The groups keep their shapes (`[.lo, .hi]`, `[.pad, .lo, .hi]`), so the validator and its
soundness and completeness proofs are unchanged (`groupsOf_go`, `go_plain` follow the new
recursion). Witness: `Opt.Legal.Complete.Witness.stack128` (`(i64 × 8, i128) -> i128`: `Pre`,
legalised to ten `i64` parameters, accepted). Native check:
`FVTest/Clif/fixtures/i128-stack-args.clif` (`scripts/lean-backend-filetests.sh`: 11 runs agree
with Cranelift's code — all registers used, `x7` left, a stack pad, a fifth pair, a pair then
an `i64` on the stack, a call passing a pair on the stack; the seven functions are verified;
the `x7` case followed by an `i64` is unsupported).

## Overflow ops at `i128` (S4, #28)

`uadd_overflow`/`sadd_overflow`/`usub_overflow`/`ssub_overflow` at `i128` (`v, of = op x, y`)
have a pure plan (`Opt.Legal.Pat.overflow`, `FV/Opt/Legal.lean`; outputs `rl rh of`): the
carry/borrow chain of `iadd`/`isub` (`Pat.addPair`/`Pat.subPair`) and the flag from `i64`
compares only — unsigned: the sum below `x` resp. `x <u y`, lexicographically on the halves;
signed: the signs of `x`, `y` and the result (`Pat.signOvf`: `x`, `y` of the same sign and `r` of
the other for addition; of different signs and `r` not of `x`'s for subtraction). No 64-bit
`*_overflow` instruction is emitted (the Arm model has no `UMADDL`/`SMADDL`, which Cranelift
uses for `umul_overflow`/`smul_overflow`). `Opt.Legal.pat_overflow` (`LegalArith.lean`): the
outputs are the halves of `Sem.overflow`'s result and its flag (`BitVec.saddOverflow_eq`,
`ssubOverflow_eq` reduce the signed flags to signs; the high half by `add128_hi`/`sub128_hi`);
`pure_step` (`LegalPlan.lean`) covers the plan, `wf_overflow` (`LegalComplete.lean`) the
completeness. Witness: `Opt.Legal.Complete.Witness.saddof128` (`Pre`, legalisation accepted).
`umul_overflow`/`smul_overflow` at `i128` stay unsupported (no plan; see `umulhi`/`smulhi`).
Measured: the four aarch64 runtest functions (`uadd_overflow_128.clif`, `sadd_overflow.clif`,
`usub_overflow.clif`, `ssub_overflow.clif`).

## Indirect calls at `i128` signatures and `try_call_indirect` (S4, #28)

The validator `Opt.Legal.checkW` (`FV/Opt/Legal.lean`) accepts a `call_indirect` whose
call-site signature `d` (`sigN`) has an `i128` parameter or return (`Plan.callInd128`: the call
on the same plain callee with the arguments expanded by the groups of `d`, `expandArgs`, the
results by `retsOk`, at `sigN`, which `g` declares as `sigExp d`), and a `try_call_indirect`
(`termOk`: as `try_call`, at the call-site signature; arguments and normal-return successor
arguments expanded). A `call_indirect` whose signature is not declared is rejected (the source
is stuck there). The pass emits every statement from its plan (`emitStmt`), so the special case
outside the validator is gone; completeness `checkW_complete` holds for `PreW` (`Pre` without
the two indirect-call conditions).

Soundness (`checkW_refines`, `FV/Opt/Proof/LegalSim.lean`): `sim_callInd128` — the source calls
the extern at the callee address with `vals`, the target the same address with the split
`vals'` at the expanded signature; `CallIndRel2 env env' p p' d` (the indirect resolution with
split arguments and results) holds by `EnvOk.ind` (for every indirect call site, `IndSite`: a
`call_indirect` or a `try_call_indirect`, the programs have the same function names and the
source's externs are a prefix of the target's) and the new `EnvOk.sigs` (when an indirect call
site has an `i128` signature, no signature the environment knows has `i128`: `Env.sigOf` gives
the signature of a function of a linked program, which would match the original call site,
`Signature.abiMatch`, but not the expanded one); `sim_tryInd` the same for the terminator, with
the successor arguments as for `try_call`. `IndExt`/`NoIndInternal` cover `try_call_indirect`
(from `TrapsExplicit.tryIndirect`).

**Statements.** The pre-S4 statements keep their meaning: `Opt.Legal.check f g cert` is
`checkW f g cert && indOldB f` (`indOldB`: no `try_call_indirect`, no `call_indirect` at a
declared `i128` signature), and `Complete.Pre`, `preB`, `legalOkB` are unchanged; `check_good`,
`check_refines{,2}`, `check_callInd`, `Complete.check_complete{,_of_preB}`,
`legalize_refines{,2}` and the end-to-end theorems below are corollaries (on `indOldB` the
programs premise for `call_indirect` sites gives `EnvOk.ind`, `indOldB_ind`, and `EnvOk.sigs`
is vacuous, `indOldB_sigs`). The only difference to the former `check`: a `call_indirect` at an
undeclared signature, or at a declared `i128` signature with plain operands, is rejected (the
former accepted both; the pass never produced either). The widened theorems:

| Pre-S4 statement (domain of `check`) | Widened (`checkW`, `PreW`) | File |
| --- | --- | --- |
| `Opt.Legal.check_refines`, `check_refines2` | `checkW_refines`, `checkW_refines2` | `FV/Opt/Proof/LegalSim.lean` |
| `Opt.Legal.Complete.check_complete`, `check_complete_of_preB`, `preB_iff` | `checkW_complete`, `checkW_complete_of_preBW`, `preBW_iff` | `LegalComplete.lean`, `LegalPre.lean` |
| `E2E.backend_correct_legal_env`, `backend_correct_legal` | `backend_correct_legal_env_wide`, `backend_correct_legal_wide` | `FV/E2E/Legal.lean` |
| `E2E.backend_correct_legal_direct` | `backend_correct_legal_direct_wide` | `FV/E2E/LegalDirect.lean` |
| `E2E.backend_correct_legal_env_cleanup`, `_cleanup`, `_direct_cleanup` | `backend_correct_legal_env_wide_cleanup`, `_wide_cleanup`, `_direct_wide_cleanup` | `FV/E2E/LegalWideCleanup.lean` |
| `E2E.legal_opt_refines`, `armRefinesLegal_of`, `backend_correct_legal_opt_env{,_cleanup}`, `backend_correct_legal_opt{,_cleanup}` | `legal_opt_refines_wide`, `armRefinesLegal_of_wide`, `backend_correct_legal_opt_env_wide{,_cleanup}`, `backend_correct_legal_opt_wide{,_cleanup}` | `FV/E2E/LegalOptX.lean` |

Premises of `backend_correct_legal_env_wide` beyond `backend_correct_legal_env`'s: `hind` for
every indirect call site (`∃ sig, Opt.Legal.IndSite f sig`, `try_call_indirect` included) and
`hsigs : Opt.Legal.Ind128 f → ∀ n s, env.sigOf n = some s → sig128 s = false` (discharged for
`Clif.Rust.env`, which knows no signature: `backend_correct_legal_wide` has no new premise).
`lean-backend` runs `checkW`; its labels refer to `backend_correct_legal_wide` and
`backend_correct_legal_opt_wide`. The whole-program domain (S3, `legalOkB`) is unchanged: it
requires `Pre`, and `callIndRel_link` relates indirect calls at signatures without `i128` only
(widening it needs the link-level `CallIndRel2`; `Signature.abiMatch` does not compare return
purposes, so an `sret` return could change the group shapes). Witnesses
(`Opt.Legal.Complete.Witness`): `indI128` (a `call_indirect` at `(i128) -> i128`) and `tryInd`
(a `try_call_indirect` at that signature, the `i128` result as the successor's parameter) are not
`Pre` (`indI128_not_pre`, `tryInd_not_pre`) but `PreW`, and `checkW` accepts their legalisations
(`indI128_legal`, `tryInd_legal`); `E2E.LinkWitness.a2_legal_wide` (`FV/E2E/LegalWideWitness.lean`)
applies `backend_correct_legal_wide` to the witness program's legalised callee with every
function-level premise discharged. Axiom list: `scripts/audit/i128-wide.lean`. Native check:
`FVTest/Clif/fixtures/i128-call-indirect.clif` (a `call_indirect` at `(i128, i64) -> i128` and at
`(i64, i128) -> i128` (pad in `x1`), a `try_call_indirect` at `(i128, i64) -> i128`).

## Not covered

* Legalised functions under `--opt` (no composition of `backend_correct_legal` with the mid-end
  theorems). `compileExe` runs no optimiser, so `compileExe_correct_source{,_peak}` need none.
* The source-level theorem's run conditions (`hbnd`; for traps `NoMemTrap` and the target's
  `TrapsExplicit`) and, with `i128`, the outside environment's `HelperOk`/`ExtLegal`/
  `EnvKeepsBounded` (table above).
* Runs of `g` that trap inside a `__*ti3` helper (see `htr` above).
* `umulhi`/`smulhi`, `umul_overflow`/`smul_overflow`, `uadd_sat`/`sadd_sat`/`usub_sat`/`ssub_sat`,
  atomics at `i128`: not legalised (no plan), deliberately: cg_clif never emits them at `i128`
  (`rustc_codegen_cranelift/src`: checked `u128`/`i128` addition and subtraction are `iadd`/
  `isub` with an `icmp` (`num.rs`, `codegen_checked_int_binop`), checked multiplication calls
  `__rust_u128_mulo`/`__rust_i128_mulo` (`codegen_i128.rs`), saturating arithmetic is the
  checked operation and a `select` (`codegen_saturating_int_binop`), `umulhi`/`smulhi` are
  emitted at `i64` only, and 128-bit atomics are a fatal "128bit atomics not yet supported"
  (`intrinsics/mod.rs`)), so no function of the measured crates falls back because of them.
* Indirect calls at an `i128` signature in the whole-program domain (S3, `legalOkB`: `Pre`).
* Unwinding through an `i128` `call_indirect` or a `try_call_indirect` of a legalised function:
  the theorems with unwinding (`Opt.Legal.X.check_refinesX{,2}`, `E2E.backend_correct_legal_unwind`,
  `backend_correct_legal_opt_unwind`, `LegalProgram.legalProg_refinesX`) keep the domain of
  `check` (`indOldB`; `LegalSimS`'s `step_sim`/`step_sim_out` exclude `callInd128` and
  `try_call_indirect` by it). `lean-backend` labels such a function with landing pads verified
  for normal returns only (`backend_correct_legal_wide`).
* Stack-passed `i128` arguments followed by an integer argument Cranelift passes in `x7`
  (above): not legalised.

`func_addr` (release survey `g_u128` test functions pass function pointers to the test
harness; agent/last-unverified "release i128"): planned as `same` when the declaration's name in
`g` is `f`'s (`evalInst_same` takes that instead of excluding `func_addr`).
