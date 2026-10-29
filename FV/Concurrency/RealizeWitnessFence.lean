module

public import FV.Concurrency.RealizeWitness
public import FV.Concurrency.ArmAllocFwd

@[expose] public section

/-!
# `Realizes` on a run of compiled code through its `dmb` (T2k, #311)

The compiled `fence; return` (`RealizeCompiled.Witness.RA`, `spillAlloc`'s allocation) from the
Arm state after the prologue: the precise run, reading the thread's own bytes (`OkPriv`),
through the 18 saves of the callee-saved registers (`ArmAllocThread.moves_fwd`: frame writes,
private) and the `dmb ish` (`q_head`, `step_fwd`: its barrier event). `realizes_fence`: this run
satisfies `realizes_compiled`'s premises; every execution of its realized prefix (one exists:
`wf_noReads`, the run has no reads) is `Realizes`d by a CLIF thread from the entry state `csF`.
Checks by `native_decide` (witness only).
-/

namespace Concurrency.RealizeCompiled.Witness

open Arm ArmThread Prog ClifThread ProgE2E Backend Backend.Proof VCodeThread PrepThread
  AllocThread ThreadRefine ArmAllocThread ArmInstFoot Code

/-- The saves at the entry (`spillSaves`). -/
def savesL : List (Loc × Loc) := calleeSaved.map fun r => (.reg r, .save r)

/-- The items after the saves. -/
def restF : List RItem := (rfF.blocks[0]!).toList.drop 18

/-- The kinds of the lines of a move's code are `plainW` (as a check). -/
def saveOkB (p : Loc × Loc) : Bool :=
  match RA.fr.moveInsts p.1 p.2 with
  | .ok code => match codeLinesE RA.ctx RA.af code {} with
    | .ok (ls1, _) => (kinds ls1).all (· == .plainW)
    | .error _ => true
  | .error _ => true

/-- The code of the items after the saves starts with `fence` (as a check). -/
def headFenceB : Bool :=
  match itemsCode RA.fr vcpF.blocks[0]! restF with
  | .ok (.inst .fence :: _) => true
  | _ => false

theorem checksRun : (rfF.blocks[0]!).toList = savesL.map (fun p => RItem.move p.1 p.2) ++ restF ∧
    savesL.all saveOkB = true ∧ headFenceB = true ∧ 0 < vcpF.blocks.size := by
  native_decide

theorem saves_plainW : ∀ p ∈ savesL, ∀ code ls1, RA.fr.moveInsts p.1 p.2 = .ok code →
    codeLinesE RA.ctx RA.af code {} = .ok (ls1, {}) → ∀ K ∈ kinds ls1, K = .plainW := by
  intro p hp code ls1 hc hl K hK
  have h := (List.all_eq_true.mp checksRun.2.1) p hp
  simp only [saveOkB, hc, hl, List.all_eq_true, beq_iff_eq] at h
  exact h K hK

theorem head_dmb : ∀ vb code, RA.vc.blocks[0]? = some vb → itemsCode RA.fr vb restF = .ok code →
    ∀ ps ls ps', codeLinesE RA.ctx RA.af code ps = .ok (ls, ps') →
      ls.head? = some (.ins .dmbish none) := by
  intro vb code hvb hc ps ls ps' hl
  have hvb' : vb = vcpF.blocks[0]! := by
    have e : RA.vc.blocks[0]? = some vcpF.blocks[0]! := by
      show vcpF.blocks[0]? = _
      rw [Array.getElem?_eq_getElem checksRun.2.2.2]
      simp [getElem!_def, Array.getElem?_eq_getElem checksRun.2.2.2]
    rw [e] at hvb
    exact (Option.some.inj hvb).symm
  subst hvb'
  have h := checksRun.2.2.1
  simp only [headFenceB, hc] at h
  split at h
  · rename_i rest e
    cases e
    exact codeLinesE_head_fence hl
  · cases h

/-- The Arm threads of the run's realized prefix. -/
noncomputable def PAf (n : Nat) (ls : List Lab) (k : Nat) : Traces ProgE2E.AState AKind BVal :=
  ⟨1, fun _ => conv (evTr (ls.take k)), fun _ _ => (RA.step, iterN RA.step n RA.s0, none)⟩

theorem evAt_mem {α : Type} {tr : List (List α)} {p : Nat × Nat} {x : α} (h : evAt tr p = some x) :
    ∃ l ∈ tr, x ∈ l := by
  obtain ⟨j, k⟩ := p
  simp only [evAt] at h
  cases hj : tr[j]? with
  | none => rw [hj] at h; cases h
  | some l =>
    rw [hj, Option.bind_some] at h
    exact ⟨l, List.mem_of_getElem? hj, List.mem_of_getElem? h⟩

theorem evAt_conv_mem {ls : List Lab} {p : Nat × Nat} {x : Prog.Ev AKind BVal}
    (h : evAt (conv (evTr ls)) p = some x) : ∃ l ∈ ls, ∃ e ∈ l.evs, x = ProgE2E.convEv e := by
  obtain ⟨L, hL, hx⟩ := evAt_mem h
  simp only [conv, evTr, List.map_map, List.mem_map, Function.comp_apply] at hL
  obtain ⟨l, hl, rfl⟩ := hL
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact ⟨l, hl, e, he, rfl⟩

theorem evAt_evTr_mem {ls : List Lab} {p : Nat × Nat} {x : ArmThread.Ev}
    (h : evAt (evTr ls) p = some x) : ∃ l ∈ ls, x ∈ l.evs := by
  obtain ⟨L, hL, hx⟩ := evAt_mem h
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hL
  exact ⟨l, hl, hx⟩

/-- **`Realizes` on the compiled `fence; return` through its `dmb`** (module doc). -/
theorem realizes_fence : ∃ (n : Nat) (ls : List Lab) (t' : ArmState × Mon),
    PRun Policy.arm RA.step (OkPriv RA) (iterN RA.step n RA.s0, none) ls t' ∧
    ls.getLast? = some ⟨[dmbEv], false⟩ ∧
    (∀ l ∈ ls, ∀ e ∈ l.evs, (e.k = .plainW ∧ PrivA RA e.addr.toNat) ∨ e = dmbEv) ∧
    ∀ (env : Clif.Env) (p : Clif.Program), ∃ k ≤ ls.length,
      ∃ (PC : Traces TState SKind BVal) (φ : PEv → PEv), PC.n = 1 ∧ PC.st 0 0 = .run csF ∧
        PC.Runs (CStep env p) ∧
        Realizes (PAf n ls k) [] (fun _ => none) (fun _ _ => False) (coW (PAf n ls k))
          (fun _ _ => False) PC [] (fun _ => none) φ (fun _ _ _ => True) := by
  obtain ⟨n', hq, hA⟩ := qRA
  have hq' := hq
  -- the run through the saves
  have hq0 : Q RA (iterN RA.step n' RA.s0)
      (.run ⟨0, savesL.map (fun p => RItem.move p.1 p.2) ++ restF,
        locVal RA.fr (iterN RA.step n' RA.s0), w₀F⟩) := by
    have e := checksRun.1
    simp only [MConf.init] at hq'
    rw [show RA.rf = rfF from rfl, e] at hq'
    exact hq'
  obtain ⟨ls1, t1, m1, r1, hq1, hev1⟩ := moves_fwd wfRA (· = .plainW) savesL restF _ _ none hq0
    saves_plainW
  -- the `dmb ish`
  obtain ⟨j, hj, hpc, hst⟩ := q_head hq1 (x := .dmbish) (t := none) rfl head_dmb
  obtain ⟨a, ha, -, hev, hdec⟩ := stepEvs_line (X := RA.X) (H := RA.H) wfRA.layout wfRA.lm wfRA.fit
    hj rfl hst.prog hpc hst.err
  have ⟨hia, hca⟩ := dmbish_inst ha t1.1
  obtain ⟨t2, r2, -⟩ := step_fwd wfRA hj rfl hst.prog hpc hst.err
    (fun rel rs rn h => by rw [cls_of_decode hdec, hca] at h; cases h) t1.2
  rw [hev, hia] at r2
  -- the threads
  have hr : PRun Policy.arm RA.step (OkPriv RA) (iterN RA.step n' RA.s0, none)
      (ls1 ++ [⟨[dmbEv], false⟩]) t2 := PRun.append r1 r2
  have hev : ∀ l ∈ ls1 ++ [⟨[dmbEv], false⟩], ∀ e ∈ l.evs,
      (e.k = .plainW ∧ PrivA RA e.addr.toNat) ∨ e = dmbEv := by
    intro l hl e he
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨hF, hk⟩ := hev1 l hl e he
      exact .inl ⟨hk, privA_addr.2 hF⟩
    · simp only [List.mem_singleton] at hl
      subst hl
      simp only [List.mem_singleton] at he
      exact .inr he
  have hnoR : ∀ l ∈ ls1 ++ [⟨[dmbEv], false⟩], ∀ e ∈ l.evs, e.k.dir ≠ .R := by
    intro l hl e he
    rcases hev l hl e he with ⟨hk, -⟩ | rfl
    · rw [hk]; decide
    · decide
  refine ⟨n', _, t2, hr, by simp, hev, fun env p => ?_⟩
  obtain ⟨k, hk, hR⟩ := realizes_compiled (n := 1) (env := env) (p := p) (RA := fun _ => RA)
    (cs := fun _ => csF) (sA := fun _ => iterN RA.step n' RA.s0)
    (fun _ _ => compiled_of hq hA env p)
    (mon := fun _ => none) (ls := fun _ => ls1 ++ [⟨[dmbEv], false⟩]) (t' := fun _ => t2)
    (fun _ _ => hr)
  have hPA : ∀ e x, (PAf n' (ls1 ++ [⟨[dmbEv], false⟩]) (k 0)).evAt e = some x → x.dir ≠ .R := by
    intro e x hx
    cases e with
    | init q => simp [Traces.evAt] at hx
    | thr i j k' =>
      simp only [Traces.evAt, PAf] at hx
      by_cases hi : i < 1
      · simp only [hi, ite_true] at hx
        obtain ⟨l, hl, e', he', rfl⟩ := evAt_conv_mem (p := (j, k')) hx
        exact hnoR l (List.mem_of_mem_take hl) e' he'
      · simp only [hi, ite_false] at hx
        cases hx
  obtain ⟨PC, φ, h1, h2, h3, h4⟩ := hR (PAf n' (ls1 ++ [⟨[dmbEv], false⟩]) (k 0)) [] []
    (fun _ => none) (fun _ => none) (fun _ _ => False) (coW _) (fun _ _ => False) rfl
    (fun i hi => by obtain rfl : i = 0 := by omega
                    rfl) (wf_noReads _ hPA)
    (fun i hi a b => by
      obtain rfl : i = 0 := by omega
      refine ⟨False.elim, fun ⟨⟨x, hx, hxk⟩, _⟩ => ?_⟩
      obtain ⟨l, hl, hxl⟩ := evAt_evTr_mem hx
      have := hnoR l (List.mem_of_mem_take hl) x hxl
      rw [hxk] at this
      exact this rfl)
    List.nil_prefix (fun q h => absurd h (Nat.not_lt_zero _))
    (fun q h => absurd h (Nat.not_lt_zero _)) (fun i hi j hj hne => by omega)
  exact ⟨k 0, hk 0 (by omega), PC, φ, h1, h2 0 (by omega), h3, h4⟩

end Concurrency.RealizeCompiled.Witness
