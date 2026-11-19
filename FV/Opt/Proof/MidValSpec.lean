import FV.Opt.Proof.MidValTerm

/-!
# What `checkCert` checks, as propositions (#1119, module (5), part 1)

`checkCert_spec`: `checkCert f g cert norm = true` gives `wfCheck`'s info of both functions
and `CertOk`, the facts of `FV/Opt/MidValCert.lean` the simulation proof reads: equal headers,
equal block ids and dominator trees, a well-formed term table, no facts at the entry, the static
sites, and every block's `entryOk`/`blockOk`.
-/

namespace Opt.MidVal

open Clif

/-- The context `checkCert` builds (`checkCert`'s `let c`). -/
def ccOf (fi gi : Info) (cert : Cert) (norm : Norm) : CC :=
  { idom := fi.cfg.idom, index := fi.cfg.index.get?, fty := fi.types.get?, gty := gi.types.get?,
    cert, norm }

/-- The facts `checkCert` establishes (module doc). -/
structure CertOk (f g : Function) (fi gi : Info) (cert : Cert) (norm : Norm) : Prop where
  name : g.name = f.name
  sig : g.sig = f.sig
  slots : g.slots = f.slots
  globals : g.globals = f.globals
  externs : g.externs = f.externs
  sigDecls : g.sigDecls = f.sigDecls
  ids : g.blocks.map (·.id) = f.blocks.map (·.id)
  entryParams : g.blocks.head?.map (·.params) = f.blocks.head?.map (·.params)
  idom : gi.cfg.idom = fi.cfg.idom
  tms : (ccOf fi gi cert norm).tmsOk = true
  entry : (ccOf fi gi cert norm).factsAt 0 = []
  sitesF : ∀ v s, (v, s) ∈ defSites f →
    (ccOf fi gi cert norm).le ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).ef v)) s = true
  sitesG : ∀ v d t, (v, d, t) ∈ defSites g →
    (ccOf fi gi cert norm).anc ((ccOf fi gi cert norm).siteOf ((ccOf fi gi cert norm).eg v)).1 d = true
  blocks : ∀ bi fb gb, f.blocks[bi]? = some fb → g.blocks[bi]? = some gb →
    (ccOf fi gi cert norm).entryOk bi = true ∧ (ccOf fi gi cert norm).blockOk bi fb gb = true
  len : g.blocks.length = f.blocks.length

theorem sameHeader_spec {f g : Function} (h : sameHeader f g = true) :
    g.name = f.name ∧ g.sig = f.sig ∧ g.slots = f.slots ∧ g.globals = f.globals ∧
      g.externs = f.externs := by
  simp only [sameHeader, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem CC.blocksOk_spec (c : CC) : ∀ (fbs gbs : List Block) (n : Nat), c.blocksOk n fbs gbs = true →
    fbs.length = gbs.length ∧ ∀ i fb gb, fbs[i]? = some fb → gbs[i]? = some gb →
      c.entryOk (n + i) = true ∧ c.blockOk (n + i) fb gb = true
  | [], [], _, _ => ⟨rfl, fun _ _ _ h => by simp at h⟩
  | [], _ :: _, _, h => by simp [CC.blocksOk] at h
  | _ :: _, [], _, h => by simp [CC.blocksOk] at h
  | fb :: fbs, gb :: gbs, n, h => by
    simp only [CC.blocksOk, Bool.and_eq_true] at h
    obtain ⟨⟨he, hb⟩, hr⟩ := h
    obtain ⟨hl, ih⟩ := CC.blocksOk_spec c fbs gbs (n + 1) hr
    refine ⟨by simp [hl], fun i fb' gb' h1 h2 => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1 h2
      exact ⟨by simpa using he, by simpa using hb⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at h1 h2
      have := ih i fb' gb' h1 h2
      rw [show n + (i + 1) = n + 1 + i by omega]
      exact this

/-- **Unpacking `checkCert`.** -/
theorem checkCert_spec {f g : Function} {cert : Cert} {norm : Norm}
    (h : checkCert f g cert norm = true) :
    ∃ fi gi, wfCheck f = .ok fi ∧ wfCheck g = .ok gi ∧ CertOk f g fi gi cert norm := by
  unfold checkCert at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hh, hd⟩, hm⟩ := h
  split at hm
  · rename_i fi gi hf hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨⟨hids, hep⟩, hidom⟩, ⟨⟨⟨htms, hent⟩, hsites⟩, hblocks⟩⟩ := hm
    obtain ⟨h1, h2, h3, h4, h5⟩ := sameHeader_spec hh
    have hsites' := hsites
    simp only [CC.sitesOk, Bool.and_eq_true, List.all_eq_true] at hsites'
    obtain ⟨hl, hb⟩ := CC.blocksOk_spec _ _ _ 0 hblocks
    refine ⟨fi, gi, hf, hg, ⟨h1, h2, h3, h4, h5, by simpa using hd, hids, hep, hidom, htms,
      by simp only [List.isEmpty_iff] at hent; exact hent, fun v s hv => hsites'.1 (v, s) hv,
      fun v d t hv => hsites'.2 (v, d, t) hv, fun bi fb gb h1 h2 => ?_, hl.symm⟩⟩
    have := hb bi fb gb h1 h2
    simp only [Nat.zero_add] at this
    exact this
  · simp at hm

end Opt.MidVal
