# `Opt.Legalize128` and its validator (`Opt.Legal.check`)

Status: **proven end to end.** `E2E.backend_correct_legal` (`FV/E2E/Legal.lean`) covers every
function whose legalisation the validator accepts and whose legalised form is inside the
backend theorem (`InSubset`, `lowerCheck`); `lean-backend` reports those verified.

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
`lean-backend` (`Opt.Legalize128.parsedFile128`) runs the check on every legalised function:
a rejected function is flagged unverified (`i128 legalized (outside backend_correct:
Opt.Legal.check rejects)`); an accepted one is compiled like any other function — the backend
decides `InSubset` (`unverifiedReason?`) and `lowerCheck` on the legalised form, and a function
passing both is reported verified (`E2E.backend_correct_legal`). Two extra conditions of the
theorem are decided in `parsedFile128`: no extern of `f` or `g` is named like a function of the
file (`hext`/`hext'`; otherwise `…outside backend_correct_legal: an extern is named like a
function of the file`), and no `--opt` (no theorem composes the legalisation with the
mid-end; under `--opt` every legalised function is flagged). `lean-e2e-check` legalises too
and checks the accepted functions like any other.

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

Axioms of every theorem below: `propext`, `Classical.choice`, `Quot.sound` and `_native`
`bv_decide` certificates only.

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
must not overwrite its inputs), and the two constructs the pass still expands outside the
validator (`call_indirect` with an `i128` signature, `try_call_indirect`; such functions stay
"unverified"). Axioms: `propext`, `Classical.choice`, `Quot.sound`. The compiler keeps running
`check` as a runtime double-check. Behaviour: on the 64 `i128` runtest files `clif-filetest
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
`LegalArith`/`LegalShift` call `bv_decide -enums`: the enum pass realizes
`Clif.Ty.enumToBitVec` in the calling module, as `FV.Backend.Proof.IselCmpExt` does, and two
modules realizing the same constant cannot be imported together.

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

## Not covered

* Legalised functions under `--opt` (no composition of `backend_correct_legal` with the mid-end
  theorems).
* Runs of `g` that trap inside a `__*ti3` helper (see `htr` above).
* `umulhi`/`smulhi`, atomics, overflow ops at `i128`, stack-passed `i128` arguments,
  `try_call_indirect`, `call_indirect` with `i128` operands: not legalised or rejected.

`func_addr` (release survey `g_u128` test functions pass function pointers to the test
harness; agent/last-unverified "release i128"): planned as `same` when the declaration's name in
`g` is `f`'s (`evalInst_same` takes that instead of excluding `func_addr`).
