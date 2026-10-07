import FV.E2E.SpillCheckAllocFix
import FV.E2E.AllocDirect
import FV.Backend.Proof.EntryParams

/-!
# `checkAlloc` accepts the spill allocation (L2a, family "compiled: checkAlloc")

`spillCheckAlloc`: on every in-scope function, the allocation checker's own verdict on the spill
allocation of the prepared VCode is `.ok ()` — the fact `Compiled` (`FV/E2E/Statement.lean`) needs
when the backend falls back to the spill allocation, beyond `AllocChecked` (`E2E.spillAccepted`).

The proof is the completeness of `checkAlloc` (`CheckComplete.checkAlloc_complete`,
`FV/E2E/SpillCheckAllocFix.lean`) applied to the spill allocation's in-states `Spill.inState`
(`FV/Backend/Proof/SpillStep4State.lean`), which verify for any availability sets `D`
(`Spill.verify_block`). `checkAlloc`'s iteration starts from `entryState`, where no home holds its
vreg, so the in-states have to be those of availability sets that hold nothing on entry to the
function: `SpillDefinedHyp`, definite assignment of the pipeline's output (every vreg a use reads
is stored in its home on every path from the function entry). That is the one fact not proven
here. The remaining premises of the completeness theorem are proven: the CFG and local facts
(`spillLocalAll`), the class table bounding every vreg (`ClassesOk`), and the reachability of every
block of `prepare`'s output (`prepare_reach`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **Definite assignment of the pipeline's output** (the remaining hypothesis of
`spillCheckAlloc`): the prepared VCode of an in-scope function has availability sets
(`Spill.SpillAvail`: every use available where it is read, every edge delivering its target's
set) in which no vreg is available on entry to the function. False as stated
(`E2E.not_spillDefinedHyp`); `SpillDefinedHypE` adds the missing input condition. -/
def SpillDefinedHyp : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc vcp : VCode), InSubset p f → Spill.ArityOk f →
    Dominated f → LowerScope f → lowerFunction f = .ok vc → Backend.prepare vc = .ok vcp →
      ∃ D, Spill.SpillAvail vcp D ∧ ∀ v, D 0 v = false

/-- `SpillDefinedHyp` with the input condition `Spill.entryParamsB` (the entry block has as many
parameters as the signature). Without it the statement is false (`E2E.not_spillDefinedHyp`,
`FV/E2E/SpillDefinedFalse.lean`: an entry-block parameter beyond the signature's is never
defined). -/
def SpillDefinedHypE : Prop :=
  ∀ (p : Clif.Program) (f : Clif.Function) (vc vcp : VCode), InSubset p f → Spill.ArityOk f →
    Dominated f → LowerScope f → Spill.entryParamsB f = true → lowerFunction f = .ok vc →
      Backend.prepare vc = .ok vcp → ∃ D, Spill.SpillAvail vcp D ∧ ∀ v, D 0 v = false

/-- **Every block of `prepare`'s output is reachable** from the entry along its CFG. -/
theorem prepare_reach {vc vcp : VCode} (hp : prepare vc = .ok vcp) (hd : Prep.PrepDomain vc)
    {succs preds : Array (Array Nat)} (hc : vcp.cfg = .ok (succs, preds)) :
    ∀ q < vcp.blocks.size, Prep.Reach succs q := by
  obtain ⟨ss0, ps0, ss1, ps1, ss2, ps2, next, B, E, hc0, hc1, hS, hc2, rfl⟩ := Prep.prepare_facts hp
  have cs0 := Prep.cfg_spec hc0
  have cs2 := Prep.cfg_spec hc2
  have cs3 : Prep.CfgSpec ((rpo ss2).map fun i => (B ++ E)[i]!) succs := Prep.cfg_spec hc
  obtain ⟨-, -, -, -, hn2, hR, hRn, hR0, -, hRre⟩ := Prep.facts_basic hd cs0 cs2 hS
  have key : ∀ i, Prep.Reach ss2 i →
      ∃ q, ∃ hq : q < (rpo ss2).size, (rpo ss2)[q] = i ∧ Prep.Reach succs q := by
    intro i hi
    induction hi with
    | entry =>
      have h0 : 0 < (rpo ss2).size := (Array.getElem?_eq_some_iff.mp hR0).1
      exact ⟨0, h0, Option.some.inj ((Array.getElem?_eq_getElem h0).symm.trans hR0), .entry⟩
    | @step i s hri hs ih =>
      obtain ⟨q, hq, hqi, hrq⟩ := ih
      subst hqi
      obtain ⟨hi2, t, j, l, ht, hl, hlab⟩ := Prep.succ_of cs2 hs
      obtain ⟨hs2, hls⟩ := Prep.lab_some hlab
      obtain ⟨q', hq', hq's, hlab3⟩ := Prep.lab3 hR hn2 hRn (hRre s (.step hri hs))
      rw [getElem!_pos (B ++ E) s hs2, hls] at hlab3
      have hq3 : q < ((rpo ss2).map fun i => (B ++ E)[i]!).size := by simpa using hq
      obtain ⟨_, e3⟩ := Prep.v3_get hR hq
      have hV3 : ((rpo ss2).map fun i => (B ++ E)[i]!)[q] = (B ++ E)[(rpo ss2)[q]] :=
        Option.some.inj ((Array.getElem?_eq_getElem hq3).symm.trans e3)
      exact ⟨q', hq', hq's, .step hrq (Prep.succ_mem cs3 hq3 (t := t) (by rw [hV3]; exact ht) hl hlab3)⟩
  intro q hq
  have hq' : q < (rpo ss2).size := by simpa using hq
  obtain ⟨q', hq'', e, hr⟩ := key _ (Spill.rpo_reach (Array.getElem_mem_toList hq'))
  have : q' = q := Spill.nodup_idx hRn (l := (rpo ss2).toList)
    (by rw [Array.getElem?_toList, Array.getElem?_eq_getElem hq'', e])
    (by rw [Array.getElem?_toList, Array.getElem?_eq_getElem hq'])
  subst this
  exact hr

theorem entry_mem_entryState {N : Nat} {r : Reg} {i : Nat} (hr : r ∈ calleeSaved)
    (hi : (Loc.reg r).index = some i) (hlt : i < N) : Sym.entry r ∈ (entryState N).get (.reg r) := by
  unfold entryState
  suffices ∀ (rs : List Reg) (a : AState), a.size = N → (r ∈ rs ∨ Sym.entry r ∈ a.get (.reg r)) →
      Sym.entry r ∈ (rs.foldl (fun a r => a.put (.reg r) [.entry r]) a).get (.reg r) from
    this calleeSaved _ (by simp) (.inl hr)
  intro rs
  induction rs with
  | nil => intro a _ h; simpa using h
  | cons r' rs ih =>
    intro a hsz h
    simp only [List.foldl_cons]
    refine ih _ (by rw [Spill.size_put]; exact hsz) ?_
    by_cases e : r' = r
    · subst e
      right
      rw [Spill.get_put_self hi (by omega)]
      exact List.mem_singleton_self _
    · rcases h with h | h
      · exact .inl ((List.mem_cons.mp h).resolve_left (Ne.symm e))
      · right
        rw [Spill.get_put_ne (by intro h'; cases h'; exact e rfl)]
        exact h

/-- **`checkAlloc` accepts the spill allocation** of every in-scope function's prepared VCode
that has availability sets holding nothing on entry. -/
theorem spillCheckAlloc_sets {p : Clif.Program} {f : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp)
    (hDs : ∃ D, Spill.SpillAvail vcp D ∧ ∀ v, D 0 v = false) :
    checkAlloc vcp (spillAlloc vcp) = .ok () := by
  obtain ⟨D, hav, hD0⟩ := hDs
  have hloc := spillLocalAll p f vc vcp hsub har hd hs hl hp
  have hdom := prepDomain_of_lower hs hl hs.nonempty
  obtain ⟨succs, preds, hcfg⟩ := Spill.cfg_ok_of_prepare hp hdom
  have hE := hloc.2.2 succs preds hcfg
  have hN : Spill.stN vcp = 128 + 2 * (spillAlloc vcp).spillSlots := by
    unfold Spill.stN; rw [Spill.spillAlloc_slots]
  have hctx : Spill.spillCtx vcp succs = ⟨vcp, succs, spillAlloc vcp, 128 + 2 * (spillAlloc vcp).spillSlots⟩ := by
    unfold Spill.spillCtx; rw [hN]
  have hpos : 0 < vcp.blocks.size := Nat.pos_of_ne_zero hE.entry.1
  refine CheckComplete.checkAlloc_complete (W := Spill.insOf vcp succs preds D) hcfg
    (Spill.spillAlloc_size vcp) hE.entry.2.1 hE.entry.2.2
    (by rw [Spill.spillAlloc_saved]; exact fun r h => h) ?_ (prepare_reach hp hdom hcfg)
    ⟨rfl, hE.entry.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- every instruction has an operand view
    intro vb hvb i hi
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hvb
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    rw [Array.getElem?_toList] at hb hk
    obtain ⟨ops, hops, -⟩ := hloc.1 b vb k i hb hk
    exact ⟨ops, hops⟩
  · -- successors are blocks
    intro b s hs'
    obtain ⟨hb, _, _, _, -, -, hlab⟩ := Prep.succ_of (Prep.cfg_spec hcfg) hs'
    exact ⟨hb, (Prep.lab_some hlab).1⟩
  · -- operand vregs have a class
    intro b vb hvb i hi ops hops o ho
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
    rw [Array.getElem?_toList] at hk
    exact (Array.getElem?_eq_some_iff.mp (hloc.2.1.1 b vb k i ops hvb hk hops o ho)).1
  · -- parameters have a class
    intro s sb hsb r hr n hn
    obtain ⟨m, cl, rfl, hm⟩ := hloc.2.1.2 s sb hsb r (List.mem_append_left _ hr)
    have : m = n := Except.ok.inj hn
    subst this
    exact (Array.getElem?_eq_some_iff.mp hm).1
  · -- the witness in-states
    intro b hb
    exact ⟨_, Spill.insOf_get hb, by unfold Spill.inState; rw [Spill.size_mkState, hN]⟩
  · intro b hb
    have := Spill.verify_block hcfg hloc hav hb
    rwa [hctx] at this
  · -- the entry in-state holds no vreg: below `entryState`
    refine ⟨_, Spill.insOf_get hpos, Spill.le_of_mem fun l s hm => ?_⟩
    obtain ⟨hm, i, hi, hlt⟩ := Spill.mem_get_mkState hm
    cases l with
    | reg r =>
      rcases Spill.inReg_mem hm with ⟨-, hr, rfl⟩ | ⟨y, hy, -⟩
      · exact entry_mem_entryState hr hi (by rw [← hN]; exact hlt)
      · rw [Spill.entryPairs_nil hE.entry.2.1] at hy; cases hy
    | save r => exact absurd (Spill.inSave_mem hm).1 (by simp)
    | stack n cl =>
      obtain ⟨v, -, -, -, hv⟩ := Spill.inStack_mem hm
      rw [hD0 v] at hv
      cases hv

/-- **`checkAlloc` accepts the spill allocation** of every in-scope function's prepared VCode,
given definite assignment of the pipeline's output (`SpillDefinedHyp`). -/
theorem spillCheckAlloc (hD : SpillDefinedHyp) {p : Clif.Program} {f : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hl : lowerFunction f = .ok vc) (hp : Backend.prepare vc = .ok vcp) :
    checkAlloc vcp (spillAlloc vcp) = .ok () :=
  spillCheckAlloc_sets hsub har hd hs hl hp (hD p f vc vcp hsub har hd hs hl hp)

/-- `spillCheckAlloc` under `SpillDefinedHypE`, for input with `entryParamsB`. -/
theorem spillCheckAllocE (hD : SpillDefinedHypE) {p : Clif.Program} {f : Clif.Function}
    {vc vcp : VCode} (hsub : InSubset p f) (har : Spill.ArityOk f) (hd : Dominated f)
    (hs : LowerScope f) (hen : Spill.entryParamsB f = true) (hl : lowerFunction f = .ok vc)
    (hp : Backend.prepare vc = .ok vcp) : checkAlloc vcp (spillAlloc vcp) = .ok () :=
  spillCheckAlloc_sets hsub har hd hs hl hp (hD p f vc vcp hsub har hd hs hen hl hp)

end E2E
