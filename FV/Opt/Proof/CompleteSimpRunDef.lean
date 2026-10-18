import FV.Opt.Proof.CompleteSimpLoop

/-!
# Completeness of simplify: the state at the end of the run

`simpFold` is the block loop of `Opt.simplify` (its result before the output function is built),
and `RunDone` the facts that hold once every block has been processed: the run invariant
`Opt.SimpInv` at the end (the current block index `f.blocks.length` is past the last block, so
the view `V0 f logs f.blocks.length` is the processed blocks and the bad values are the source values
without a processed definition and the renamed values), every block processed, the output blocks,
and two facts the validator needs that `SimpInv` does not record: only statement results are renamed
(`keysRes`), and `call_indirect` statements are kept (`callInd`).
-/

namespace Opt

open Clif

/-- The block loop of `simplify`. -/
def simpFold (rules : SimplifyFn) (skel : SkeletonFn) (allowed skelOk : Inst → Bool)
    (rematConst : Bool) (f : Function) (info : Info) :
    SState × Subst × Array Block × Array (Option BlockLog) :=
  info.cfg.rpo.foldl (stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray)
    (initSState f info rematConst, {}, f.blocks.toArray, Array.replicate f.blocks.toArray.size none)

theorem simplify_eq (rules : SimplifyFn) (skel : SkeletonFn) (allowed skelOk : Inst → Bool)
    (rematConst : Bool) (f : Function) (info : Info) :
    simplify rules skel allowed skelOk rematConst f info =
      ((simpFold rules skel allowed skelOk rematConst f info).2.1.apply
          { f with blocks := (simpFold rules skel allowed skelOk rematConst f info).2.2.1.toList },
        (simpFold rules skel allowed skelOk rematConst f info).1.stats,
        { defs := (simpFold rules skel allowed skelOk rematConst f info).1.defs,
          types := (simpFold rules skel allowed skelOk rematConst f info).1.types,
          subst := (simpFold rules skel allowed skelOk rematConst f info).2.1,
          logs := (simpFold rules skel allowed skelOk rematConst f info).2.2.2 }) := rfl

/-- **The end of the run** (module doc): `st`, `S`, `out`, `logs` the final state, renaming,
output blocks and block records. -/
structure RunDone (f : Function) (info : Info) (allowed skelOk : Inst → Bool) (st : SState)
    (S : Subst) (out : Array Block) (logs : Array (Option BlockLog)) : Prop where
  rinv : RInv f (V0 f logs f.blocks.length) (Bad f logs f.blocks.length 0 S) (fun _ => False)
    (fun _ => False) st
  srcTy : ∀ y t, info.types.get? y = some t → st.types.get? y = some t
  leafAv : ∀ y d, (initAvail f).get? y = some d → st.avail.get? y = some d
  defsLeaf : ∀ y, (initAvail f).contains y = true → st.defs.get? y = none
  doneAv : ∀ y, Done f logs f.blocks.length 0 y → S.contains y = false →
    Placed st (Bad f logs f.blocks.length 0 S) y ∧
      ∃ d t, (defMap f).get? y = some (d, t) ∧ st.avail.get? y = some d
  substOk : ∀ y w, S.get? y = some w → Done f logs f.blocks.length 0 y ∧
    Placed st (Bad f logs f.blocks.length 0 S) w ∧
    (∃ d' t', DefAt (V0 f logs f.blocks.length) w d' t' ∧ ∃ d t, (defMap f).get? y = some (d, t) ∧
      (d' = d ∨ Anc info.cfg.idom d' d)) ∧ st.types.get? w = st.types.get? y
  outs : ∀ d b, V0 f logs f.blocks.length d = some b →
    (∃ b0, f.blocks[d]? = some b0 ∧ b.params = b0.params ∧ b.id = b0.id) ∧
    ∀ k t, b.body[k]? = some t →
      OutStmt f allowed skelOk info.cfg.idom (V0 f logs f.blocks.length)
        (Bad f logs f.blocks.length 0 S) st d k t
  done : ∀ d lg, logs[d]? = some (some lg) → ∃ b0 bo, f.blocks[d]? = some b0 ∧
    blockOf f d lg = some bo ∧
    StmtsFact info.cfg.idom (V0 f logs f.blocks.length) (Bad f logs f.blocks.length 0 S) st S d
      b0.body lg.stmts 0 ∧
    TermLogFact (Bad f logs f.blocks.length 0 S) st S b0 lg ∧
    TermOut info info.cfg.idom (V0 f logs f.blocks.length) (Bad f logs f.blocks.length 0 S) st d
      bo.body.length b0 lg.term'
  size : logs.size = f.blocks.length
  all : ∀ d, d < f.blocks.length → ∃ lg, logs[d]? = some (some lg)
  outEq : out.size = f.blocks.length ∧ ∀ d lg, logs[d]? = some (some lg) → out[d]? = blockOf f d lg
  keysRes : ∀ y, S.contains y = true → ∃ d j, (defMap f).get? y = some (d, j + 1)
  callInd : ∀ (d : Nat) (lg : BlockLog) (b0 : Block), logs[d]? = some (some lg) →
    f.blocks[d]? = some b0 → ∀ s0 ∈ b0.body,
    isCallInd s0.inst = true → ∃ t ∈ outsOf lg.stmts, t.inst = mapOperands S.step s0.inst

end Opt
