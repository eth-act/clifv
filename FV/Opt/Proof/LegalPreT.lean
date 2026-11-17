import FV.Opt.Proof.LegalPre
import FV.Opt.Proof.LegalDirect
import FV.Opt.Proof.LegalSimSW

/-!
# The source domain with `i128`-free indirect calls, one function (#1076)

`legalOkTB f` (`FV/Opt/Legalize128PreT.lean`): the pass succeeds, and `f` does not mention
`i128` or meets `preBT` (`PreW`, the validator `checkW`'s completeness precondition, and
`indTB`: no indirect call at an `i128` call-site signature; a `try_call_indirect` is allowed).

* `legalOkTB_cases`: the identity, or `PreW`, `indTB` and a successful legalisation.
* `legalOkTB_of_legalOkB`: the old source domain is inside it.
* `indTB_indSite`: on `indTB` every indirect call site's signature is `i128`-free.
* `legalize_refines2W`: the legalisation of a `PreW` function refines it (`checkW_refines2`
  through `checkW_complete`), two environments.
-/

namespace Opt.Legal.Complete

open Clif Opt.Legalize128

/-- **The source domain with `i128`-free indirect calls, one function**: the pass is the
identity, or `PreW` and `indTB` hold and the pass succeeds (`legalize f` is its result). -/
theorem legalOkTB_cases {f : Function} (h : legalOkTB f = true) :
    (mentions128 f = false ∧ function128Cert f = .ok (f, {}) ∧ legalize f = f) ∨
    (PreW f ∧ indTB f = true ∧ ∃ cert, function128Cert f = .ok (legalize f, cert)) := by
  simp only [legalOkTB, preBT, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hok, hm | ⟨hp, hT⟩⟩ := h
  · exact .inl ⟨hm, function128Cert_of_not_mentions hm, legalize_of_not_mentions hm⟩
  · refine .inr ⟨preBW_iff.1 hp, hT, ?_⟩
    cases hc : function128Cert f with
    | error e => simp [hc, Except.toBool] at hok
    | ok gc => exact ⟨gc.2, by simp [legalize, hc]⟩

theorem preBW_of_preB {f : Function} (h : preB f = true) : preBW f = true := by
  simp only [preB, preBW, Bool.and_eq_true] at h ⊢
  exact h.1.1

theorem indTB_of_preB {f : Function} (h : preB f = true) : indTB f = true := by
  simp only [preB, indTB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  intro b hb
  refine ⟨h.1.2 b hb, ?_⟩
  have ht := h.2 b hb
  split
  · rename_i c args et he
    simp [he] at ht
  · rfl

/-- **The old source domain is inside the new one.** -/
theorem legalOkTB_of_legalOkB {f : Function} (h : legalOkB f = true) : legalOkTB f = true := by
  simp only [legalOkB, legalOkTB, preBT, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  obtain ⟨hok, hm | hp⟩ := h
  · exact ⟨hok, .inl hm⟩
  · exact ⟨hok, .inr ⟨preBW_of_preB hp, indTB_of_preB hp⟩⟩

/-- On `indTB`, no indirect call site of `f` has an `i128` signature. -/
theorem indTB_indSite {f : Function} (hT : indTB f = true) {sig : Nat} {d : Signature}
    (hs : IndSite f sig) (hd : f.sigDecls.lookup sig = some d) : sig128 d = false :=
  Bool.eq_false_iff.2 fun h => S.indTB_not_ind128 hT ⟨sig, d, hs, hd, h⟩

end Opt.Legal.Complete

namespace Opt.Legal

open Clif Opt.Legalize128

/-- **`Opt.Legalize128` is correct on `PreW`, two environments** (`checkW_refines2` with
`checkW_complete`; `legalize_refines2` on `Pre`): the source `f` runs under `env`, its
legalisation `g` under `env'`, the environments related by `EnvOk2`. -/
theorem legalize_refines2W {f g : Function} {cert : Cert} (hp : Complete.PreW f)
    (hl : function128Cert f = .ok (g, cert))
    {env env' : Env} {p p' : Program} (hE : EnvOk2 env env' ⟨f, g, cert⟩ p p') {b b' : Block}
    (hb : f.entry? = some b) (hb' : g.entry? = some b') {args args' : List Val}
    {fr0 fr0' : Frame} {m : Mem}
    (h1 : fr0.func = f) (h2 : fr0.body = b.body) (h3 : fr0.term = b.term)
    (h4 : b.params.map (·.2) = args.map (·.ty))
    (h5 : Regs.empty.setMany (b.params.map (·.1)) args = some fr0.regs)
    (h1' : fr0'.func = g) (h2' : fr0'.body = b'.body) (h3' : fr0'.term = b'.term)
    (h5' : Regs.empty.setMany (b'.params.map (·.1)) args' = some fr0'.regs)
    (hsl : fr0'.slots = fr0.slots)
    (hexp : ExpRel ((groups f.sig.params).getD []) args args')
    (hM : MemBounded m) (hT : NoMemTrap env p ⟨fr0, [], m⟩)
    (hI : NoIndInternal env p f ⟨fr0, [], m⟩) (fuel : Nat) :
    (∀ vals m1, runLoop env p fuel ⟨fr0, [], m⟩ = .returned vals m1 →
      ∃ vals', ExpRel ((groups f.sig.returns).getD []) vals vals' ∧
        ∃ k, runLoop env' p' k ⟨fr0', [], m⟩ = .returned vals' m1) ∧
    (∀ c, runLoop env p fuel ⟨fr0, [], m⟩ = .trapped c →
      ∃ k, runLoop env' p' k ⟨fr0', [], m⟩ = .trapped c) :=
  checkW_refines2 (C := ⟨f, g, cert⟩) (Complete.checkW_complete hp hl) hE hb hb' h1 h2 h3 h4 h5
    h1' h2' h3' h5' hsl hexp hM hT hI fuel

end Opt.Legal
