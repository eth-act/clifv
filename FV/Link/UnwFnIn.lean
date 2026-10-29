module

public import FV.Link.UnwSavedIn
public import FV.Link.UnwTryIn
public import FV.Link.UnwFns
public import FV.E2E.LinkScopeInputCleanupT
public import FV.Link.DeadCleanupImage

@[expose] public section

/-!
# The per-function unwinding checks from the input and the remaining conditions (S10g, #404)

`unwFnsB` (what `compileExeU` decides per compiled function) has six conjuncts. Four of them
follow from the input conditions and the two frame conditions, by the completeness theorems of
`FV/Link/UnwTryIn.lean` and `FV/Link/UnwSavedIn.lean`:

* `callSites`, `padsNonzeroB`: from `fnScopeB` and `tryTablesB` (`callSites_complete_input`,
  `padsNonzero_complete_input`);
* `unwindRows`, `savedCheck`: from the frame conditions `saveFrameB` (the save slots below
  32 KiB) and `leadOkB` (no other callee-save store right after the saves), measured by
  `lake exe lean-link` (`Link.DeadCleanup.unwReport`), and the code below 4 GiB
  (`unwindRows_complete_frame`, `savedCheck_pipe`).

`unwCondsB R` collects what is left per function: the input condition `tryTablesB`, the two
checks without a completeness proof yet (`unwCheck`, `lastCallsOk`, decided on the compiled
code), the two frame conditions and the code size. **`fnUnwB_of_pipe`**: on a function of
`fnScopeB` whose cleanup pipeline succeeded, they give `fnUnwB`; **`unwFnsB_of_conds`**: on an
input in `InScopeIn`, `unwCondsB` of the compiled functions gives `unwFnsB`.
-/

namespace Link.EhCheck.Complete

set_option autoImplicit false

open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck

/-- **The per-function conditions left for `unwFnsB`** (see the module doc). -/
def unwCondB (g : Clif.Function) (a : Art) : Bool :=
  tryTablesB g && unwCheck g a.vc && lastCallsOk a.af a.fa && saveFrameB a.vcp a.rf &&
    leadOkB a.rf a.af && decide (4 * a.fb.words.size < 2 ^ 32)

/-- `unwCondB` of every compiled function of `R`. -/
def unwCondsB (R : Res) : Bool := (progOf R).funcs.all fun g => unwCondB g (artOf R g)

/-- **`fnUnwB` of a compiled function from the input and the remaining conditions**: the
cleanup pipeline succeeded on `g` (any allocator answer `o`), `g` is in `fnScopeB`, and
`unwCondB` holds. -/
theorem fnUnwB_of_pipe {g : Clif.Function} {k : Nat} {base : BitVec 64} {o : Lean.Json} {a : Art}
    (hpipe : pipeCleanupT g k base o = .ok a) (hsc : fnScopeB g = true)
    (hc : unwCondB g a = true) : fnUnwB g a = true := by
  simp only [unwCondB, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨ht, hu⟩, hlc⟩, hframe⟩, hlead⟩, hcode⟩ := hc
  obtain ⟨hl, hp, hrf, hlr, hem, hla, -, -⟩ := pipeCleanupT_spec hpipe
  obtain ⟨-, -, -, -, -, -, -, hd, hs, har, -⟩ := fnScope_parts hsc
  have hD := dominated_of hd
  have hS := lowerScope_of hs
  have hA := Spill.arityOk_of har
  obtain ⟨raw, hraw, hvcp⟩ := DeadCleanup.prune_prepare_ok_inv hp
  obtain ⟨ss, ps, hcfg⟩ := Spill.cfg_ok_of_prepare hraw (prepDomain_of_lower hS hl hS.nonempty)
  have hne0 := (Spill.edgesHyp_of hD hS hA hl hraw ss ps hcfg).entry.1
  have hcfg' : a.vcp.cfg = .ok (ss, ps) := by
    rw [hvcp, DeadCleanup.preparedCleanup_cfg]; exact hcfg
  have hne : a.vcp.blocks.size ≠ 0 := by
    rw [hvcp, DeadCleanup.preparedCleanup_blocks, Array.size_map]; exact hne0
  have hsize : a.rf.blocks.size = a.vcp.blocks.size := by rw [hrf]; exact pipeAlloc_size hne o
  have halloc : lowerRFunc a.vcp (allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp o))) =
      .ok a.af := hrf ▸ hlr
  have hframe' : saveFrameB a.vcp (allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp o))) =
      true := hrf ▸ hframe
  have hlead' : leadOkB (allocResult a.vcp (readyAnswer a.vcp (raAnswer a.vcp o))) a.af = true :=
    hrf ▸ hlead
  have hRF := savedCheckRF_pipe hcfg' halloc
  obtain ⟨l, hcs⟩ := callSites_complete_input hD hS hA ht hl hp hlr hsize hem
  obtain ⟨rows, hrows⟩ :=
    unwindRows_complete_frame hRF halloc (hrf ▸ hsize) hne hframe' hlead' hem hla hcode
  obtain ⟨vb, hvb⟩ : ∃ vb, a.vcp.blocks[0]? = some vb :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨items, hit⟩ : ∃ items, a.rf.blocks[0]? = some items :=
    ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  have hpads := padsNonzero_complete_input hD hS hA ht hl hp hlr hem hla hvb hit
  have hsaved : savedCheck a.vcp a.rf = true := by
    rw [hrf]; exact savedCheck_pipe hcfg' hne halloc hframe' hlead'
  simp [fnUnwB, hu, hcs, hrows, hpads, hlc, hsaved, Except.toBool]

/-- **`unwFnsB` from the input and the remaining conditions**: on an input in `InScopeIn`,
`unwCondsB` of the compiled functions gives the per-function unwinding checks. -/
theorem unwFnsB_of_conds {I : LinkInput} (hin : InScopeIn I = true)
    (hc : unwCondsB (Link.DeadCleanup.parResultsCleanupT I) = true) :
    unwFnsB (Link.DeadCleanup.parResultsCleanupT I) = true := by
  have hin' := hin
  simp only [InScopeIn, progScopeInB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    at hin'
  obtain ⟨⟨⟨hn, -⟩, -⟩, hfs⟩ := hin'
  have hok := resultsCleanupT_ok_input hin
  rw [Link.DeadCleanup.parResultsCleanupT_eq] at hc ⊢
  have hprog : (progOf I.resultsCleanupT).funcs = I.prog.funcs := by
    simp [progOf, LinkInput.resultsCleanupT, LinkInput.prog, Function.comp_def]
  have hnR : ((progOf I.resultsCleanupT).funcs.map (·.name)).Nodup := by rw [hprog]; exact hn
  rw [unwFnsB, parMap_eq, List.all_map, List.all_eq_true]
  intro g hg
  obtain ⟨e, he, rfl, ha⟩ := artOf_spec hnR hg
  simp only [Function.comp_apply, id]
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 he
  have hok' := List.all_eq_true.1 hok _ he
  cases hpc : pipeCleanupT fi.func fi.k (BitVec.ofNat 64 (I.baseOf fi.func.name)) (raJ fi.ra fi.j)
    with
  | error _ => simp [hpc, Except.toBool] at hok'
  | ok a =>
    have haa : artOf I.resultsCleanupT fi.func = a := by rw [ha, hpc]; rfl
    rw [haa]
    have hsc := fnScopeB_of_input (hfs fi.func (by rw [← hprog]; exact hg))
    have hcg := List.all_eq_true.1 hc fi.func hg
    rw [haa] at hcg
    exact fnUnwB_of_pipe hpc hsc hcg

end Link.EhCheck.Complete
