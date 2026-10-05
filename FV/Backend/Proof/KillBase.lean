import FV.Backend.Proof.SpillCtlPipe
import FV.Backend.Proof.SpillAvail
import FV.Backend.Proof.IselFlowExt

/-!
# Killed vregs of the ISLE lowering (V4, `SpillKillFree`): the shared definitions

`Spill.killFreeB` (`FV/Backend/Proof/SpillAvail.lean`) asks that no instruction of the prepared
VCode reads a vreg some instruction kills (`Spill.unstored`: the scratch defs of the LL/SC loops,
`JTSequence`'s temporaries, a `try_call`'s results), and that a killed branch argument is stored
by its block's entry stores. The proof splits along the driver:

* every ISLE run of the driver (`KillRunsHyp`, the analogue of `IselCtlHyp`) emits code whose
  killed vregs are fresh vregs of the run and whose uses are vregs of CLIF values or of the run
  that the run does not kill (`RunKill`); a statement's result registers likewise (`OutKill`);
  a `try_call`'s call defines only the `try_call`'s result vregs;
* the driver assembles the runs (disjoint vreg ranges, alias resolution, edge blocks);
* `prepare` keeps the facts.

The run facts come from a uniform invariant of the ISLE interpreter: every value of a run holds
no `AtomicRMWLoop`/`AtomicCASLoop`/`JTSequence` data (`V.kIn`; those are built only inside
`atomic_rmw_loop`, `atomic_cas_loop`, `br_table_impl`), its registers outside a call's defs
(`V.regsK`) are allowed (`VOk`), and in a `try_call`'s context the vregs in a call's defs
(`V.regsD`) are the `try_call`'s result vregs (`KP`); the state invariant `IsK` and the run
relation `RsK`.
-/

namespace Isle

mutual
/-- The terms an expression applies. -/
def exprTerms : Expr → List TermId
  | .term _ t args => t :: exprTermsL args
  | .let _ bs body => bindTerms bs ++ exprTerms body
  | _ => []
/-- `exprTerms` of a list. -/
def exprTermsL : List Expr → List TermId
  | [] => []
  | e :: es => exprTerms e ++ exprTermsL es
/-- `exprTerms` of `let*` bindings. -/
def bindTerms : List (VarId × TypeId × Expr) → List TermId
  | [] => []
  | (_, _, e) :: bs => exprTerms e ++ bindTerms bs
end

mutual
/-- The terms a pattern applies (enum variants, structs, extern extractors). -/
def patTerms : Pattern → List TermId
  | .bind _ _ q => patTerms q
  | .term _ t args => t :: patTermsL args
  | .and _ ps => patTermsL ps
  | _ => []
/-- `patTerms` of a list. -/
def patTermsL : List Pattern → List TermId
  | [] => []
  | q :: qs => patTerms q ++ patTermsL qs
end

/-- The terms a rule applies: in its argument patterns, its if-lets and its right-hand side. -/
def ruleTerms (r : Rule) : List TermId :=
  patTermsL r.args ++ r.iflets.flatMap (fun il => patTerms il.lhs ++ exprTerms il.rhs) ++
    exprTerms r.rhs

end Isle

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Aarch64

/-- The vregs a list of instructions kills. -/
def killedL (ms : List MInst) : List Nat := ms.flatMap unstored

/-- The registers of an operand outside a call's defs. -/
def opRegsK : Opnd → List Reg
  | .callArgs us => pairRegs us
  | .callInfo c => (match c.dest with
      | .reg r => [r]
      | .sym _ => []) ++ pairRegs c.uses
  | _ => []

/-- The registers of a call's defs inside an operand. -/
def opRegsD : Opnd → List Reg
  | .callRets ds => pairRegs ds
  | .callInfo c => pairRegs c.defs
  | _ => []

mutual
/-- The registers inside a value, outside a call's defs. -/
def _root_.Backend.V.regsK : V → List Reg
  | .reg r => [r]
  | .regs rs => rs
  | .regsVec rss => rss.flatten
  | .op o => opRegsK o
  | .data _ _ fs => regsKL fs
  | _ => []
/-- `V.regsK` of a list. -/
def regsKL : List V → List Reg
  | [] => []
  | v :: vs => v.regsK ++ regsKL vs
end

mutual
/-- The registers of a call's defs inside a value. -/
def _root_.Backend.V.regsD : V → List Reg
  | .op o => opRegsD o
  | .data _ _ fs => regsDL fs
  | _ => []
/-- `V.regsD` of a list. -/
def regsDL : List V → List Reg
  | [] => []
  | v :: vs => v.regsD ++ regsDL vs
end

/-- The `MInst` variants with killed defs: the LL/SC loops and `JTSequence`. -/
def isKVariant (k : Nat) : Bool :=
  k == VIdx.MInst.AtomicRMWLoop || k == VIdx.MInst.AtomicCASLoop || k == VIdx.MInst.JTSequence

mutual
/-- Does the value hold `MInst` data of a variant with killed defs? -/
def _root_.Backend.V.kIn : V → Bool
  | .data ty k fs => (ty == tyMInst && isKVariant k) || kInL fs
  | _ => false
/-- `V.kIn` of a list. -/
def kInL : List V → Bool
  | [] => false
  | v :: vs => v.kIn || kInL vs
end

/-- The instructions emitted from `s0` to `s`. -/
def emittedSince (s0 s : LState) : List MInst := s.emitted.toList.drop s0.emitted.size

/-- An allowed vreg number of a run with fresh vregs from `lo` and counter `hi`: a CLIF value's
vreg (`< nV`) or a vreg of the run, not killed (`K`). -/
def VOk (nV lo hi : Nat) (K : List Nat) (n : Nat) : Prop :=
  (n < nV ∨ (lo ≤ n ∧ n < hi)) ∧ n ∉ K

/-- **The value invariant** of a run started at `s0` with fresh vregs from `lo`, in state `s`. -/
def KP (ctx : Ctx) (lo : Nat) (s0 s : LState) (v : V) : Prop :=
  v.kIn = false ∧
  (∀ n c, Reg.vreg n c ∈ v.regsK →
    VOk ctx.valDef.size lo s.nextVreg (killedL (emittedSince s0 s)) n) ∧
  (ctx.tryRegs ≠ ([], []) → ∀ n c, Reg.vreg n c ∈ v.regsD →
    Reg.vreg n c ∈ ctx.tryRegs.1 ∨ Reg.vreg n c ∈ ctx.tryRegs.2)

/-- **The state invariant** of a run started at `s0` with fresh vregs from `lo`. -/
def IsK (ctx : Ctx) (lo : Nat) (s0 s : LState) : Prop :=
  (∃ ms : List MInst, s.emitted = s0.emitted ++ ms.toArray) ∧ ctx.valDef.size ≤ lo ∧
    lo ≤ s.nextVreg ∧
    ∀ m ∈ emittedSince s0 s, (∀ c ti, m ≠ .tryCall c ti) ∧
      (∀ k ∈ unstored m, lo ≤ k ∧ k < s.nextVreg) ∧
      (∀ u ∈ useVregs m, VOk ctx.valDef.size lo s.nextVreg (killedL (emittedSince s0 s)) u) ∧
      (ctx.tryRegs ≠ ([], []) → ∀ c, m = .call c → ∀ q ∈ c.defs, ∀ n cl, q.2 = .vreg n cl →
        q.2 ∈ ctx.tryRegs.1 ∨ q.2 ∈ ctx.tryRegs.2)

/-- **The run relation**: the counter grows, the code is extended, and what it newly kills is
fresh. -/
def RsK (s s' : LState) : Prop :=
  s.nextVreg ≤ s'.nextVreg ∧ ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
    ∀ k ∈ killedL ms, s.nextVreg ≤ k ∧ k < s'.nextVreg

/-! ## The driver's interface -/

/-- **What a run of the driver from `s` to `s'` guarantees** about the code `ms` it emits (vreg
counter from `lo`, CLIF values below `nV`): no `tryCall`; the vregs it kills are vregs of the
run; every use is a CLIF value's vreg or a vreg of the run, and is not killed by the run. -/
def RunKill (nV lo : Nat) (s s' : LState) : Prop :=
  ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
    (∀ m ∈ ms, ∀ c ti, m ≠ .tryCall c ti) ∧
    (∀ k ∈ killedL ms, lo ≤ k ∧ k < s'.nextVreg) ∧
    (∀ m ∈ ms, ∀ u ∈ useVregs m, (u < nV ∨ (lo ≤ u ∧ u < s'.nextVreg)) ∧ u ∉ killedL ms)

/-- **A statement's result registers**: CLIF values' vregs or vregs of the run, not killed by
it. -/
def OutKill (nV lo : Nat) (s s' : LState) (out : Option V) : Prop :=
  ∀ rss, out = some (.regsVec rss) → ∀ rs ∈ rss, ∀ n c, Reg.vreg n c ∈ rs →
    (n < nV ∨ (lo ≤ n ∧ n < s'.nextVreg)) ∧ n ∉ killedL (emittedSince s s')

/-- **The killed-vreg facts of the ISLE runs** (the analogue of `IselCtlHyp`): on input in scope,
a statement's `lower` run, a terminator's run and a `try_call`'s `lower_branch` run meet
`RunKill` (from the counter they start at; a `try_call`'s from the state after its result vregs
are allocated), a statement's results meet `OutKill`, and a `try_call`'s calls define only its
result vregs. -/
def KillRunsHyp : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    Dominated f → LowerScope f → AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    (∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
      ctx.valDef.size ≤ s.nextVreg →
      runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) →
      RunKill ctx.valDef.size s.nextVreg s s' ∧
        (info.results ≠ [] → OutKill ctx.valDef.size s.nextVreg s s' out)) ∧
    (∀ ti t data targets s out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false →
      termData (abiTerm f t) = .ok data → ctx.valDef.size ≤ s.nextVreg →
      termCallF ctx ti data t targets s = .ok (out, s', tr) →
      RunKill ctx.valDef.size s.nextVreg s s') ∧
    (∀ ti t et data sig items lo trs st1 targets out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et → (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr) →
      RunKill ctx.valDef.size st1.nextVreg { st1 with emitted := #[] } s' ∧
        ∀ m ∈ s'.emitted.toList, ∀ c, m = .call c → ∀ q ∈ c.defs, ∀ n cl, q.2 = .vreg n cl →
          q.2 ∈ trs.1 ∨ q.2 ∈ trs.2)

end Backend.Proof.Kill
