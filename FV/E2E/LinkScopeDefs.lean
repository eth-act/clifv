import FV.E2E.LinkCheck
import FV.E2E.LinkOwnCallsDefs
import FV.E2E.LinkOwnFramesDefs
import FV.E2E.EmitCondsDefs
import FV.Backend.AllocReady
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.SpillArity

/-! # `okB` split: the compiler's pipeline, the input conditions, the linker's facts (L2a)

The executable definitions of `FV/E2E/LinkScope.lean` (docs/TO-PROVE.md §3 "L2", L2a), kept free
of proofs so that a crate's proof file can decide them by `native_decide`:

* `pipeT`, `LinkInput.resultsT`: **the compiler's pipeline** — `lean-backend`'s
  (`allocateRegalloc2`): regalloc2's answer is only an oracle, lowered if `checkAlloc` accepts it
  and its code is `emitReady`, else the spill allocation (`lowerAllocReady`). The checker's `pipe`
  lowers regalloc2's answer as it is (no fallback), so its success is a property of the oracle.
* `depthOf`, `LinkInput.withDepth`: the stack of one call level by construction (the largest
  `frameDrop`, as `cargo fv link-proof` chooses it).
* `InScopeP I`: **the input conditions** — decidable on the program's CLIF functions, their
  signatures and the names the CLIF takes the address of (the domain of `I.syms`): per function
  `fnScopeB`, per program `progScopeB`.
* `linkerOkB I`: **the linker's facts** — the checks about the addresses rust-lld chose (the link
  map `I.addrs`, the CLIF image's symbol addresses `I.syms`, `I.raStar`) for the compiled code:
  what a Lean static linker (L2b, #10) must provide by construction.
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-! ## The compiler's pipeline -/

/-- regalloc2's answer for the prepared VCode `vcp`, read from `lean-regalloc`'s output (an
oracle: an error or a rejected allocation selects the spill allocation). -/
def raAnswer (vcp : VCode) (o : Lean.Json) : Except String RFunc := do
  let o ← parseRAOut o
  buildRFunc vcp o

/-- **The compiler's pipeline** on `f` (index `k` in its file, `lean-regalloc`'s output `o`)
loaded at `base`: `lowerFunction`, `prepare`, `lowerAllocReady` (regalloc2's allocation if
accepted and emittable, else the spill allocation), `emitFunc`, `layout`. The artifact's
allocation is the one lowered, `allocResult vcp (readyAnswer vcp ra)` (`lowerAllocReady_eq`). -/
def pipeT (f : Clif.Function) (k : Nat) (base : BitVec 64) (o : Lean.Json) : Except String Art := do
  let vc ← lowerFunction f
  let vcp ← prepare vc
  let ra := raAnswer vcp o
  let af ← lowerAllocReady vcp ra
  let fa ← emitFunc k af
  let fb ← fa.layout
  pure ⟨k, vc, vcp, allocResult vcp (readyAnswer vcp ra), af, fa, fb, base⟩

/-- Every function of the input, compiled by the compiler's pipeline and loaded at its link-map
address. -/
def LinkInput.resultsT (I : LinkInput) : Res :=
  I.funcs.map fun fi => let f := fi.func
    (f, pipeT f fi.k (BitVec.ofNat 64 (I.baseOf f.name)) (raJ fi.ra fi.j))

/-- The program of the input: its parsed (and `i128`-legalised) functions (`progOf_resultsT`). -/
def LinkInput.prog (I : LinkInput) : Clif.Program := { funcs := I.funcs.map (·.func) }

/-- The largest `frameDrop` of the results: the stack of one call level. -/
def depthOf (R : Res) : Nat := (R.map fun e => frameDrop (getOk e.2).af).foldl max 0

/-- The input with the stack of one call level of the results `R`. -/
def LinkInput.withDepth (I : LinkInput) (R : Res) : LinkInput := { I with D := depthOf R }

/-! ## The input conditions -/

/-- `lowerFunction` and `prepare` accept `f` (internal rejections without a fallback:
docs/TO-PROVE.md §1.2, kind 4), and the prepared VCode satisfies `emitCondsB`, the decidable
condition of V6b's emission totality (`backend_correct_final_total_emit`): the spill code's word
bound is below `2 ^ 24` (needed: a large enough function exceeds `b`'s reach) and the three
instruction-selection facts `immsOkB`, `noAlwaysB`, `branchTargetsOkB` (V6c, open: to be proven
from the ISLE rules, then dropped from here). -/
def lowersB (f : Clif.Function) : Bool :=
  match lowerFunction f with
  | .ok vc => match prepare vc with
    | .ok vcp => emitCondsB vcp
    | .error _ => false
  | .error _ => false

/-- **The per-function input conditions** of `g`: the subset (`InSubset (P.only g) g`: subset
E, no direct self-call, `sigAbiOk` signatures, indirect-call signatures), the register
parameters (distinct argument registers, at most 64 bits), no `return_call`, the conditions of
the backend's totality theorems (`dominatedB`, `lowerScopeB`, `arityOkB`) and `lowersB`. -/
def fnScopeB (g : Clif.Function) : Bool :=
  Compile.functionE g && g.externs.all (fun e => e.2.name != g.name) &&
  (sigAbiOk g.sig && g.externs.all (fun e => sigAbiOk e.2.sig)) && indSigsOk g &&
  decide (regLocs g.sig).Nodup && (regLocs g.sig).all (·.isArgReg) &&
  g.sig.params.all (fun p => decide (p.ty.width ≤ 64)) && linkFreeB g &&
  dominatedB g && lowerScopeB g && Spill.arityOkB g && lowersB g

/-- A declaration of a function of `P` has its signature. -/
def declSigB (P : Clif.Program) (g : Clif.Function) : Bool :=
  g.externs.all fun e => match P.func? e.2.name with
    | some h => decide (e.2.sig = h.sig)
    | none => true

/-- `addrSlots` on the input: no indirect call in `P`, or the functions with an address have no
stack slots (stronger than the check, which also passes when no function of `P` has an outgoing
argument area). -/
def addrSlotsInB (P : Clif.Program) (S : String → Option Nat) : Bool :=
  !P.funcs.any (!indFreeB ·) || P.funcs.all fun h => (S h.name).isNone || h.slots.isEmpty

/-- **The program-level input conditions** (`S`: the CLIF image's symbols; only which names
have one matters): distinct names, declared signatures, the scope of the indirect calls
(`indB`), the call sites' registers and results (`callScopeB`), the stack arguments of the
declared program callees (`outScopeB`), `addrSlotsInB`. -/
def progScopeB (P : Clif.Program) (S : String → Option Nat) : Bool :=
  decide (P.funcs.map (·.name)).Nodup &&
  P.funcs.all (fun g => declSigB P g && indB P S g && callScopeB P S g && outScopeB P g) &&
  addrSlotsInB P S

/-- **`InScopeP`: the input conditions of a crate** — decidable on the input program alone (its
CLIF functions, their signatures, the names its CLIF takes the address of). -/
def InScopeP (I : LinkInput) : Bool :=
  progScopeB I.prog (fun n => I.syms.lookup n) && I.prog.funcs.all fnScopeB

/-! ## The linker's facts -/

/-- **The linker's facts** about the compiled code `T` placed at the link map's addresses:
every function's words fit at its base (`fits`), the image reads back (`imgB`: no overlap, no
misalignment), the return address of every call is outside the other functions' code
(`raCallB`), `raStar` is outside all code, the program's functions have distinct nonzero
addresses no other symbol has (`symInjB`), and the CLIF image's symbols are at their link-map
addresses (`symOkB`). -/
def linkerOkR (I : LinkInput) (R : Res) : Bool :=
  let T := tabOf R
  imgB T && raStarB T (BitVec.ofNat 64 I.raStar) && symInjB I (progOf R) && symOkB I &&
  R.all fun e => let a := getOk e.2
    decide (a.base.toNat + 4 * a.fb.words.size ≤ 2 ^ 64) && raCallB T e.1 a

/-- `linkerOkR` of the compiler's results. -/
def linkerOkB (I : LinkInput) : Bool := linkerOkR I I.resultsT

end E2E.LinkCheck
