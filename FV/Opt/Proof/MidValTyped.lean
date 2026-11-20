import FV.Opt.Proof.MidValTerm
import FV.Opt.Proof.MidValWf

/-!
# Typed atoms of the mid-end validator (#1119, the typed normaliser seam)

The typed normaliser obligation `NormSoundT f norm` (`FV/Opt/Proof/MidValTerm.lean`) assumes
`AtomsTyped`: the atoms below the normalised node hold values of their static types (`atomTy`).
The simulation evaluates a normalised node in `f`'s frame at a program point `(bi, k)` where
the node's operands have sites no later than `(bi, k)`. Then:

* every term reachable from the operands has a site no later than `(bi, k)` (`reach_site`:
  `CC.tmOk` sites a node's operands no later than the node);
* an atom is sited at its definition (`CC.tmOk_atom`), so its value of `f` is available at
  `(bi, k)` and, by the run-time invariant (`Inv.regs`), holds a value of its `wfCheck` type;
* that type is the atom's static type (`atomTy_tm`: block parameters' declared types, statement
  results' `Inst.resultTypes`, both checked by `wfCertM`).

Main result: **`atomsTyped_of`**.
-/

namespace Opt.MidVal

open Clif

/-- The static type of an atom is the `wfCheck` type of the value it stands for. -/
theorem atomTy_tm {f : Function} {W : WfData} (hW : WfM f W) {a : Tm} {ty : Ty} {v : ValueId}
    (ha : atomTy f a = some ty) (hv : atomVal f a = some v) : W.tm v = some ty := by
  cases a with
  | param b i =>
    simp only [atomTy, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
    simp only [atomVal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
    obtain ⟨blk, hb, p, hp, rfl⟩ := ha
    obtain ⟨blk', hb', p', hp', rfl⟩ := hv
    rw [hb] at hb'
    cases hb'
    rw [hp] at hp'
    cases hp'
    exact hW.params b blk hb p (List.mem_of_getElem? hp)
  | res b k j =>
    simp only [atomTy, Option.bind_eq_some_iff] at ha
    simp only [atomVal, Option.bind_eq_some_iff] at hv
    obtain ⟨blk, hb, st, hst, ts, hts, hj⟩ := ha
    obtain ⟨blk', hb', st', hst', hr⟩ := hv
    rw [hb] at hb'
    cases hb'
    rw [hst] at hst'
    cases hst'
    obtain ⟨ts', hts', -, hty⟩ := hW.results b blk hb k st hst
    have hts2 : st.inst.resultTypes (sigOf f) (sigDeclOf f) = some ts := hts
    rw [hts2] at hts'
    cases hts'
    rw [hty j v hr, hj]
  | poison b k => simp [atomTy] at ha
  | node _ => simp [atomTy] at ha

/-- Terms reachable from the operands of `i` have sites no later than the operands' bound. -/
theorem reach_site {f : Function} {W : WfData} (hW : WfM f W) {c : CC} (hidom : c.idom = W.idom)
    (hok : c.tmsOk = true) {i : Inst} {p : Nat × Nat}
    (hops : ∀ o ∈ operands i, LeP W.idom (c.siteOf o) p) {u : Nat}
    (h : TmReach c.cert.tms i u) : LeP W.idom (c.siteOf u) p := by
  induction h with
  | op ho => exact hops _ ho
  | sub _ hw hu ih =>
    have hn := CC.tmOk_node (CC.tmsOk_get hok hw) _ hu
    have hle := CC.le_sound hn.2
    rw [hidom] at hle
    exact hle.trans hW.rank ih

/-- **The atoms below a node are typed** in a frame of `f` at `(bi, k)` whose available values
hold values of their types (`Inv.regs`), when the node's operands have sites no later than
`(bi, k)` (module doc). -/
theorem atomsTyped_of {f : Function} {W : WfData} (hW : WfM f W) {c : CC} (hidom : c.idom = W.idom)
    (hok : c.tmsOk = true) {fr : Frame} {mem : Mem} {bi k : Nat}
    (hregs : ∀ v, Avail W bi k v → ∃ a, fr.regs v = some a ∧ W.tm v = some a.ty)
    {i : Inst} (hops : ∀ o ∈ operands i, LeP W.idom (c.siteOf o) (bi, k)) :
    AtomsTyped f c.cert.tms fr mem i := by
  intro u a ty v hR ha hty hv
  have hle := reach_site hW hidom hok hops hR
  have hna : ∀ j, a ≠ .node j := by
    rintro j rfl
    simp [atomTy] at hty
  rw [tmVal_atom ha hna] at hv
  obtain ⟨w, hw, hwv⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨s, hs, hd⟩ := atomVal_defSite hw
  have hst := CC.tmOk_atom (CC.tmsOk_get hok ha) hs
  rw [hst] at hle
  obtain ⟨a', ha', hta⟩ := hregs w (avail_of_leP (hW.sites w s hd) hle)
  rw [ha'] at hwv
  have e : a' = v := Option.some.inj hwv
  subst e
  rw [atomTy_tm hW hty hw] at hta
  exact (Option.some.inj hta).symm

end Opt.MidVal
