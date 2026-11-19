import FV.Opt.Proof.MidValRel

/-!
# The relation at function entry (#1119, module (5))

`rel_entry`: the entry frames of `f` and `g` (same arguments, same slot bases, any memory) are
related at the start of block 0 with no facts. Both entry blocks have the same parameters
(`CertOk.entryParams`); a value available there is a parameter, whose term is the atom
`param 0 i` on both sides.
-/

namespace Opt.MidVal

open Clif

theorem param_index {b : Block} {p : ValueId × Ty} (h : p ∈ b.params) :
    ∃ i : Nat, b.params[i]? = some p :=
  List.mem_iff_getElem?.1 h

theorem tv_param {f : Function} {cert : Cert} {syms : String → Option Nat} {fr : Frame} {t : Nat}
    {bi i : Nat} {b : Block} {p : ValueId × Ty} (ht : cert.tms[t]? = some (.param bi i))
    (hb : f.blocks[bi]? = some b) (hp : b.params[i]? = some p) :
    TV f cert syms fr t = fr.regs p.1 := by
  rw [TV, tmVal_atom ht (fun _ h => by cases h)]
  simp [atomVal, hb, hp]

/-- The entry block's values: its parameters. -/
theorem entry_param {f : Function} {W : WfData} (hW : Wf f W) {v : ValueId} (hv : Avail W 0 0 v) :
    ∃ (b : Block) (p : ValueId × Ty) (i : Nat), f.blocks[0]? = some b ∧ b.params[i]? = some p ∧
      p.1 = v := by
  obtain ⟨b, p, hb, hp, hpv⟩ := site_param' hW (avail_entry hW hv)
  obtain ⟨i, hi⟩ := param_index hp
  exact ⟨b, p, i, hb, hi, hpv⟩

/-- `entry_param` for the facts `WfM` of `wfCheck`. -/
theorem entry_paramM {f : Function} {W : WfData} (hW : WfM f W) {v : ValueId} (hv : Avail W 0 0 v) :
    ∃ (b : Block) (p : ValueId × Ty) (i : Nat), f.blocks[0]? = some b ∧ b.params[i]? = some p ∧
      p.1 = v := by
  obtain ⟨b, p, hb, hp, hpv⟩ := hW.site_param' (hW.avail_entry hv)
  obtain ⟨i, hi⟩ := param_index hp
  exact ⟨b, p, i, hb, hi, hpv⟩

/-- **Function entry**, given that the entry block's facts hold in the entry frame (none for
`checkCert`; the hoisting mode's under `globalsResolve`, `entry_facts_hold`). -/
theorem rel_entry {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}
    (H : Hyp f g fi gi cert norm) {syms : String → Option Nat} {b b' : Block}
    (hb : f.entry? = some b) (hb' : g.entry? = some b') (hp : b'.params = b.params)
    {args : List Val} {regs : Regs} {slots : List (SlotId × Nat)} (m : Mem)
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs)
    (hsl : slots.map (·.1) = f.slots.map (·.1))
    (h0 : ∀ F ∈ (ccOf fi gi cert norm).factsAt 0,
      FactHolds f cert syms ⟨f, regs, slots, b.body, b.term⟩ m F) :
    Rel f g fi gi cert norm syms 0 0 0 ((ccOf fi gi cert norm).factsAt 0)
      ⟨f, regs, slots, b.body, b.term⟩ ⟨g, regs, slots, b'.body, b'.term⟩ m := by
  have hb0 : f.blocks[0]? = some b := by simpa [Function.entry?, List.head?_eq_getElem?] using hb
  have hb0' : g.blocks[0]? = some b' := by simpa [Function.entry?, List.head?_eq_getElem?] using hb'
  obtain ⟨-, hbo⟩ := H.ok.blocks 0 b b' hb0 hb0'
  have hB := blockOk_spec hbo
  obtain ⟨Send, hw, hend⟩ := hB.walk
  refine ⟨⟨b, b', Send, hb0, hb0', by simpa using hw, hend⟩, H.wff.inv_entry hb hty hr hsl,
    H.wfg.inv_entry hb' (by rw [hp]; exact hty) (by rw [hp]; exact hr)
      (by rw [hsl, H.ok.slots]), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨b0, p, i, h0, hpi, rfl⟩ := entry_paramM H.wff hx
    rw [hb0] at h0; cases h0
    exact tv_param (hB.paramsF i p hpi) hb0 hpi
  · intro y hy
    obtain ⟨b0, p, i, h0, hpi, rfl⟩ := entry_paramM H.wfg hy
    rw [hb0'] at h0; cases h0
    have hpi' : b.params[i]? = some p := by rw [← hp]; exact hpi
    exact tv_param (hB.paramsG i p hpi) hb0 hpi'
  · intro y hy
    obtain ⟨b0, p, i, h0, hpi, rfl⟩ := entry_paramM H.wfg hy
    rw [hb0'] at h0; cases h0
    have ht := hB.paramsG i p hpi
    have := CC.tmOk_atom (CC.tmsOk_get H.ok.tms ht) (s := (0, 0)) rfl
    rw [this]
    exact LeP.refl _ _
  · exact h0
  · intro F hF t ht
    have he := H.ok.entry F hF
    cases F with
    | defd t' =>
      simp only [Fact.terms, List.mem_singleton] at ht
      subst ht
      simp only [CC.hoistFact, Bool.and_eq_true, beq_iff_eq] at he
      rw [he.1]
      exact LeP.refl _ _
    | mem => simp [CC.hoistFact] at he
    | eqn => simp [CC.hoistFact] at he

/-- A `symbol_value`, `tls_value` or `func_addr` that resolves evaluates (to one value, keeping
memory). -/
theorem evalInst_partial_resolves {f : Function} {syms : String → Option Nat} {fr : Frame}
    {i : Inst} (hp : partialK i = true) (hr : symResolves f syms i = true) (hf : fr.func = f) :
    ∃ v, evalInst fr (symMem syms) i = .ok ([v], symMem syms) := by
  cases i <;> simp [partialK] at hp
  case symbolValue ty gv =>
    simp only [symResolves] at hr
    split at hr
    · rename_i name off x hl
      obtain ⟨base, hbase⟩ := Option.isSome_iff_exists.1 hr
      exact ⟨Val.ofInt ty (base + off), by simp [evalInst, hf, hl, symMem, hbase]⟩
    · cases hr
  case tlsValue ty gv =>
    simp only [symResolves] at hr
    split at hr
    · rename_i name off x hl
      obtain ⟨base, hbase⟩ := Option.isSome_iff_exists.1 hr
      exact ⟨Val.ofInt ty (base + off), by simp [evalInst, hf, hl, symMem, hbase]⟩
    · cases hr
  case funcAddr ty fn =>
    simp only [symResolves] at hr
    split at hr
    · rename_i e he
      obtain ⟨base, hbase⟩ := Option.isSome_iff_exists.1 hr
      exact ⟨Val.ofInt ty base, by simp [evalInst, hf, he, symMem, hbase]⟩
    · cases hr

/-- **The hoisting mode's entry facts hold** when the function's global values resolve: each is
a `symbol_value`, `tls_value` or `func_addr` of `f` (`hoistFact`), a node without operands, which
evaluates in every frame of `f`. -/
theorem entry_facts_hold {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}
    (H : Hyp f g fi gi cert norm) {syms : String → Option Nat}
    (hres : globalsResolve f syms = true) {fr : Frame} (hf : fr.func = f) (m : Mem) :
    ∀ F ∈ (ccOf fi gi cert norm).factsAt 0, FactHolds f cert syms fr m F := by
  intro F hF
  have he := H.ok.entry F hF
  cases F with
  | mem => simp [CC.hoistFact] at he
  | eqn => simp [CC.hoistFact] at he
  | defd t =>
    simp only [CC.hoistFact, Bool.and_eq_true] at he
    obtain ⟨-, he⟩ := he
    simp only [CC.tm, ccOf] at he
    split at he
    · rename_i i hi
      simp only [Bool.and_eq_true] at he
      obtain ⟨hpk, hin⟩ := he
      have hops : operands i = [] := by cases i <;> simp_all [partialK, operands]
      obtain ⟨b, hb, st, hst, hsi⟩ : ∃ b ∈ f.blocks, ∃ st ∈ b.body, st.inst = i := by
        simpa [hasInst] using hin
      have hrs : symResolves f syms i = true := by
        simp only [globalsResolve, List.all_eq_true] at hres
        rw [← hsi]; exact hres b hb st hst
      obtain ⟨v, hv⟩ := evalInst_partial_resolves (fr := tmFrame f cert.tms fr (symMem syms)) hpk hrs hf
      show (tmVal f cert.tms fr (symMem syms) t).isSome
      rw [tmVal_node hi (by simp [hops])]
      simp only [evalNode, hv, Option.isSome_some]
    · cases he

end Opt.MidVal
