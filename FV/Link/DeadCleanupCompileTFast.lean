module

public import FV.Link.DeadCleanupImage
public import FV.E2E.LinkScopeFast
public import FV.E2E.CalleeWith
public import FV.E2E.LinkOutCleanupT

@[expose] public section

/-! # The typed scope's checks at the size of std (S11e6, #419)

`InScopePT` and `OutOkTCleanup` (the checks of `Link.DeadCleanup.compileExeT`'s typed branch) as
defined scan the program and the CLIF image's symbols at every function (`InScopePT`'s
`progScopeB`; `OutOkTCleanup`'s `calleeB`, `blrOk`, `P.func?`, `List.lookup`) and run the
pipeline sequentially (`OutOkTCleanup S.inputCleanup` compiles every function twice): hours of
`lean-link` on std's 28k functions. As `FV/E2E/LinkScopeFast.lean` (T3d) does for the integer
scope, the forms here evaluate the same conditions with hash maps, compute a function's own facts
once, compile the functions once in parallel tasks and check them in parallel, and are equal to
the definitions:

* `inScopePTPar_eq : inScopePTPar I = InScopePT I`;
* `calleeWithB_eq` (`FV/E2E/CalleeWith.lean`): the callers' declared names as a hash set
  (`calleeB`; `calleeSet` of `FV/E2E/LinkCheckFast.lean`);
* `outChksTWith_eq`: `outChksT` with the program's functions, the symbols and the callee set
  given;
* `outOkTFast_eq : outOkTFast S = OutOkTCleanup S.inputCleanup`.

No statement changes; generated code is unchanged (the checks only accept or reject).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- `InScopePT` with the per-function conditions (`fnScopeTB`) evaluated in parallel tasks, the
program-level ones with hash maps (`progScopeFastB`). -/
def inScopePTPar (I : LinkInput) : Bool :=
  let sy := assocMap I.syms
  progScopeFastB I.prog (fun n => sy[n]?) && (Link.parMap fnScopeTB I.prog.funcs).all id

theorem inScopePTPar_eq (I : LinkInput) : inScopePTPar I = InScopePT I := by
  simp only [inScopePTPar, assocMap_fun, progScopeFastB_eq, InScopePT, Link.parMap_eq,
    List.all_map, Function.comp_def, id]

/-- `siteOk` with the program's functions looked up through `F`. -/
def siteOkWith (F : String → Option Clif.Function) (P : Clif.Program) (g : Clif.Function)
    (may : Clif.Function → Bool) (vc : VCode) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym n => match F n with
    | some h => g.externs.any (fun e => e.2.name == n) &&
        decide (info.uses = retPairs (decU info.uses)) &&
        decide (info.defs = callDefs (decD info.defs)) &&
        decide ((decU info.uses).map (·.2) = regLocs h.sig) &&
        decide (((decD info.defs).map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length (decD info.defs).length)).map Reg.x)
    | none => true
  | .reg _ => blrOk P may (gotOf vc) info

theorem siteOkWith_func? (P : Clif.Program) (g : Clif.Function) (may : Clif.Function → Bool)
    (vc : VCode) : siteOkWith P.func? P g may vc = siteOk P g may vc := rfl

/-- **`outChksT` with the program's functions (`F`), the CLIF image's symbols (`S`), the declared
names (`cs`) and `anyInd` given**, and `g`'s facts for `indToB` computed once (`outChksTWith_eq`). -/
def outChksTWith (F : String → Option Clif.Function) (S : String → Option Nat)
    (cs : String → Bool) (anyInd : Bool) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) : List (String × Bool) :=
  let a := getOk r
  let fr := RAFrame.compute a.vcp a.rf
  let Ds := declSet g
  let may := indToWithB S (indFreeB g) (fun n => Ds.contains n) (indSigs g) g
  [("compiled: checkAlloc", (checkAlloc a.vcp a.rf).toBool),
   ("covered", formsCoveredB ⟨a.fa.k, a.af.slotBase⟩ a.vcp),
   ("sretRets", allInsts a.vc (retsB g)),
   ("entryRegs", entryB g a.vcp),
   ("outFits", g.externs.all (fun e => !(F e.2.name).isSome || outFitsB e.2.sig fr.intBase)),
   ("callRegs/blrRegs", allInsts a.vcp (siteB (siteOkWith F P g may a.vcp))),
   ("sret: subset E", !(g.sig.params.any (·.purpose == .sret)) || Compile.functionE g),
   ("calleeInt", !calleeWithB cs anyInd S g || g.sig.returns.all (·.ty.isInt))]

theorem outChksTWith_eq (I : LinkInput) (P : Clif.Program) (g : Clif.Function)
    (r : Except String Art) :
    outChksTWith P.func? (fun n => I.syms.lookup n) (fun n => (calleeSet P).contains n)
      (P.funcs.any (!indFreeB ·)) P g r = outChksT I P g r := by
  simp only [outChksTWith, outChksT, indToWithB_declSet, siteOkWith_func?, calleeWithB_eq,
    calleeIntChk]

/-- `outOkTR I R` with the hash maps built once and the functions checked in parallel tasks. -/
def outOkTRFast (I : LinkInput) (R : Res) : Bool :=
  let P := progOf R
  let m := funcMap P
  let sy := assocMap I.syms
  let cs := calleeSet P
  let anyInd := P.funcs.any (!indFreeB ·)
  (Link.parMap (fun e => (outChksTWith (fun n => m[n]?) (fun n => sy[n]?) (fun n => cs.contains n)
    anyInd P e.1 e.2).all (·.2)) R).all id

theorem outOkTRFast_eq (I : LinkInput) (R : Res) : outOkTRFast I R = outOkTR I R := by
  simp only [outOkTRFast, outOkTR, funcMap_fun, assocMap_fun, outChksTWith_eq, Link.parMap_eq,
    List.all_map, Function.comp_def, id]

end E2E.LinkCheck

namespace Link.DeadCleanup

open E2E E2E.LinkCheck

/-- **`OutOkTCleanup S.inputCleanup`, the pipeline run once in parallel**: the cleanup input is
`S.input0.withDepth S.input0.resultsCleanupT`, and the results do not read the depth
(`outOkTFast_eq`). -/
def outOkTFast (S : LinkSpec) : Bool :=
  let I0 := S.input0
  let Rs := parResultsCleanupT I0
  outOkTRFast (I0.withDepth Rs) Rs

theorem outOkTFast_eq (S : LinkSpec) : outOkTFast S = OutOkTCleanup S.inputCleanup := by
  simp only [outOkTFast, outOkTRFast_eq, parResultsCleanupT_eq, OutOkTCleanup]
  rfl

end Link.DeadCleanup
