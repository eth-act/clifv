import FV.Backend.Proof.KillAssemble
import FV.Backend.Proof.SpillDefinedPaths

/-!
# Definedness of the ISLE lowering: the run facts (`DefRunsHyp`)

The analogue of `Kill.KillRunsHyp` for definite assignment. A run of the driver (a statement's
`lower`, a terminator's run, a `try_call`'s `lower_branch`) emits code whose uses are

* vregs of CLIF values the lowered instruction reaches (`Reach`: its operands, closed under the
  operands and results of each one's defining instruction, as `Driver.Prov`), or
* fresh vregs of the run (`≥` the counter it starts from) defined by an earlier instruction of
  the run (`RunDef`);

and a statement's result registers are such CLIF values' vregs or fresh vregs the run defines
(`OutDef`). This is a flow-sensitive fact: an ISLE temporary (`temp_writable_reg`) is a value of
the run before the instruction defining it is emitted, and `writable_reg_to_reg` is the identity
on ISLE values, so the uniform value invariants of `KillGen`/`IselFlowCheck` cannot state it.
-/

namespace Backend.Proof.DefRun

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Kill

/-- The vregs instruction `i` defines (its def operands). -/
def defVregs (i : MInst) : List Nat :=
  match i.operands with
  | .error _ => []
  | .ok ops => (ops.toList.filter (·.kind == .def)).map (·.vreg)

/-- The CLIF values a lowering reaches from the values `S`: closed under the operands and the
results of each one's defining instruction. -/
inductive Reach (ctx : Ctx) (S : List Nat) : Nat → Prop
  | seed {y : Nat} : y ∈ S → Reach ctx S y
  | dep {n j y : Nat} {info : IInfo} {c : Clif.Inst} : Reach ctx S n → ctx.defInst? n = some j →
      ctx.insts[j]? = some info → info.clif = some c → (y ∈ instArgs c ∨ y ∈ info.results) →
      Reach ctx S y

/-- **What a run from `s` to `s'` emits** (reaching from `S`): every use is the vreg of a CLIF
value reached from `S`, or a fresh vreg of the run defined by an earlier instruction of the run. -/
def RunDef (ctx : Ctx) (S : List Nat) (s s' : LState) : Prop :=
  ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
    ∀ (k : Nat) (m : MInst), ms[k]? = some m → ∀ u ∈ useVregs m,
      (u < ctx.valDef.size ∧ Reach ctx S u) ∨
        (s.nextVreg ≤ u ∧ ∃ k' m', k' < k ∧ ms[k']? = some m' ∧ u ∈ defVregs m')

/-- **A statement's result registers**: vregs of CLIF values reached from `S`, or fresh vregs the
run defines. -/
def OutDef (ctx : Ctx) (S : List Nat) (s s' : LState) (out : Option V) : Prop :=
  ∀ rss, out = some (.regsVec rss) → ∀ rs ∈ rss, ∀ n c, Reg.vreg n c ∈ rs →
    (n < ctx.valDef.size ∧ Reach ctx S n) ∨
      (s.nextVreg ≤ n ∧ ∃ m ∈ emittedSince s s', n ∈ defVregs m)

/-- **The definedness facts of the ISLE runs** (open): on input in scope, a statement's `lower`
run, a terminator's run and a `try_call`'s `lower_branch` run meet `RunDef` (reaching from the
instruction's operands, resp. the terminator's arguments), and a statement's results `OutDef`. -/
def DefRunsHyp : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (st0 : LState),
    Dominated f → LowerScope f → AbiSigsOk f → buildCtx f = .ok (ctx, ranges, st0) →
    (∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
      ctx.valDef.size ≤ s.nextVreg →
      runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) →
      RunDef ctx (instArgs inst) s s' ∧
        (info.results ≠ [] → OutDef ctx (instArgs inst) s s' out)) ∧
    (∀ ti t data targets s out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → t.isTry = false →
      (∃ B ∈ f.blocks, B.term = t) →
      termData (abiTerm f t) = .ok data → ctx.valDef.size ≤ s.nextVreg →
      termCallF ctx ti data t targets s = .ok (out, s', tr) →
      RunDef ctx (termArgs (abiTerm f t)) s s') ∧
    (∀ ti t et data sig items lo trs st1 targets out s' tr, ti < ctx.insts.size →
      ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → IsTryWith t et → (∃ B ∈ f.blocks, B.term = t) →
      tryCallData f t = .ok data → exnTableOpnd f et = .ok (sig, items) →
      ctx.valDef.size ≤ lo.nextVreg → tryRegsOf sig lo = some (trs, st1) →
      tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (out, s', tr) →
      RunDef ctx (termArgs t) { st1 with emitted := #[] } s')

end Backend.Proof.DefRun
