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

/-- **Function entry.** -/
theorem rel_entry {f g : Function} {fi gi : Info} {cert : Cert} {norm : Norm}
    (H : Hyp f g fi gi cert norm) {syms : String → Option Nat} {b b' : Block}
    (hb : f.entry? = some b) (hb' : g.entry? = some b') (hp : b'.params = b.params)
    {args : List Val} {regs : Regs} {slots : List (SlotId × Nat)} (m : Mem)
    (hty : args.map (·.ty) = b.params.map (·.2))
    (hr : Regs.empty.setMany (b.params.map (·.1)) args = some regs)
    (hsl : slots.map (·.1) = f.slots.map (·.1)) :
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
  · intro F hF
    rw [H.ok.entry] at hF; cases hF
  · intro F hF
    rw [H.ok.entry] at hF; cases hF

end Opt.MidVal
