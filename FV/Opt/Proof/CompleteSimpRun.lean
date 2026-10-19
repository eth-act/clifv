import FV.Opt.Proof.CompleteSimpEnd

/-!
# Completeness of simplify: the run

One block keeps the invariant between blocks `Opt.RunBInv` (`stepBlock_inv`: entering the block
`binv_start`, its statements `stmts_fold`, its terminator `block_end`), so the whole run ends with
every block processed and the facts `Opt.RunDone` (`simplify_run_inv`, by `simpFold_runDone`).
-/

namespace Opt

open Clif

/-- The statement step of `Opt.stepBlock`. -/
abbrev stmtStep (rules : SimplifyFn) (skel : SkeletonFn) (allowed skelOk : Inst → Bool) (cfg : Cfg)
    (bi : Nat) : SState × Subst × Array StmtLog → Stmt → SState × Subst × Array StmtLog :=
  fun acc s =>
    let (st, subst, lg) := stepStmt rules skel allowed skelOk cfg bi (acc.1, acc.2.1) s
    (st, subst, acc.2.2.push lg)

variable {f : Function} {info : Info} {allowed skelOk : Inst → Bool}

/-- **One block** keeps the invariant between blocks. -/
theorem stepBlock_inv {rules : SimplifyFn} {skel : SkeletonFn} (hc : Checked f info)
    (hR : SimpRulesProv rules) (hK : SkelRulesProv skel)
    (hsym : ∀ ty gv, allowed (.symbolValue ty gv) = false) {st : SState} {S : Subst}
    {out : Array Block} {logs : Array (Option BlockLog)} {bi : Nat}
    (h : RunBInv f info allowed skelOk st S out logs) (hbi : bi < f.blocks.length)
    (hn : logs[bi]? = some none)
    (hpreds : ∀ d, d ≠ bi → Anc info.cfg.idom d bi → ∃ lg, logs[d]? = some (some lg)) :
    RunBInv f info allowed skelOk
      (stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray (st, S, out, logs) bi).1
      (stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray (st, S, out, logs) bi).2.1
      (stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray (st, S, out, logs) bi).2.2.1
      (stepBlock rules skel allowed skelOk info.cfg f.blocks.toArray (st, S, out, logs) bi).2.2.2 := by
  obtain ⟨b0, hb0⟩ : ∃ b0, f.blocks[bi]? = some b0 := ⟨_, List.getElem?_eq_getElem hbi⟩
  have hb : f.blocks.toArray[bi]! = b0 := by simp [getElem!_def, hb0]
  rw [stepBlock_eq, hb]
  have hfold := stmts_fold (rules := rules) (skel := skel) hc hR hK hsym hb0 b0.body 0 st S #[]
    List.drop_zero (binv_start hc h hbi hn hpreds)
  generalize b0.body.foldl (stmtStep rules skel allowed skelOk info.cfg bi) (st, S, #[]) = acc
    at hfold ⊢
  obtain ⟨st1, S1, lgs⟩ := acc
  exact block_end hc hR hK hsym hb0 hfold h.outSize h.outEq

/-- **The run of `simplify`** on a checked function ends with every block processed and the facts
`RunDone` (under the rule obligations, and an `allowed` that never admits `symbol_value`). -/
theorem simplify_run_inv {rules : SimplifyFn} {skel : SkeletonFn} {rematConst : Bool}
    (hc : Checked f info) (hR : SimpRulesProv rules) (hK : SkelRulesProv skel)
    (hsym : ∀ ty gv, allowed (.symbolValue ty gv) = false) :
    RunDone f info allowed skelOk (simpFold rules skel allowed skelOk rematConst f info).1
      (simpFold rules skel allowed skelOk rematConst f info).2.1
      (simpFold rules skel allowed skelOk rematConst f info).2.2.1
      (simpFold rules skel allowed skelOk rematConst f info).2.2.2 :=
  simpFold_runDone hc (fun _ _ _ _ _ h hbi hn hp => stepBlock_inv hc hR hK hsym h hbi hn hp)

end Opt
