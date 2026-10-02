import FV.Opt.Proof.LegalSim
import FV.Opt.Proof.LegalComplete

/-!
# The legalisation refines the original

`Opt.Legal.check_refines` (soundness of the validator) composed with
`Opt.Legal.Complete.check_complete` (the validator accepts every legalisation of a function
satisfying `Complete.Pre`): the legalised function `g` of `Opt.Legalize128.function128Cert`
refines the original `f` without a validator premise.
-/

namespace Opt.Legal

open Clif Opt.Legalize128

/-- **`Opt.Legalize128` is correct** on functions satisfying `Complete.Pre`: a return of `f` is a
return of the legalisation `g` with the results split by `f`'s return groups and the same memory,
a trap of `f` is a trap of `g` with the same code (the premises are `check_refines`'s). -/
theorem legalize_refines {f g : Function} {cert : Cert} (hp : Complete.Pre f)
    (hl : function128Cert f = .ok (g, cert))
    {env : Env} {p p' : Program} (hE : EnvOk env ⟨f, g, cert⟩ p p') {b b' : Block}
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
        ∃ k, runLoop env p' k ⟨fr0', [], m⟩ = .returned vals' m1) ∧
    (∀ c, runLoop env p fuel ⟨fr0, [], m⟩ = .trapped c →
      ∃ k, runLoop env p' k ⟨fr0', [], m⟩ = .trapped c) :=
  check_refines (C := ⟨f, g, cert⟩) (Complete.check_complete hp hl) hE hb hb' h1 h2 h3 h4 h5 h1'
    h2' h3' h5' hsl hexp hM hT hI fuel

end Opt.Legal
