import FV.Opt.MidValSyms
import FV.Opt.Proof.MidValCondProg

/-!
# The hoisting mode at a symbol table is sound (#1119, `placement:symbol_value`)

`symsCopy f g cert hints = some f'` (`FV/Opt/MidValSyms.lean`) says the hoisting-mode re-check
`checkCertSyms` accepts `g` (or `condPrep g hints`) against the copy `f'` of `f`: `f` itself, or
`foldPre f bs` / `foldPreK f bs` for the fold requests `bs`. At a symbol table where `f'`'s global
values resolve, `check_soundSyms` gives `FunSimMUAt syms f' (condPrep g hints)`; composed with
`foldPre_simU`/`foldPreK_simU` (`FunSimU f f'`) and `condPrep_simU` (`FunSimU (condPrep g hints)
g`), both at every symbol table:

* **`symsCopy_sound`** (a normaliser sound under typing), **`symsCopy_soundD`** (sound where the
  operands have values): `symsCopy f g cert hints = some f' → globalsResolve f' syms = true →
  FunSimMUAt syms f g`;
* **`checkCertSymsAt_sound`**: `checkCertSymsAt syms f g cert hints = true → FunSimMUAt syms f g`;
* **`checkedSymsAt_simMUAt`**: through constant-phi removal (`ConstPhi.run_simU`), as
  `checkedC_simMU`.

`neg_symhoist` (`FVTest/Opt/MidValNegWitness.lean`) stays rejected by `checkCertC` with every
certificate and hint list: `FunSimMU` (every symbol table) is false for it.
-/

namespace Opt.MidVal

open Clif

/-- **Soundness of the copy the hoisting mode accepts against** (module doc), with a normaliser
sound where the operands have values. -/
theorem symsCopy_soundD {f g f' : Function} {cert : Cert} {hints : List (BlockId × List Wrap)}
    {norm : Norm} (h : symsCopy f g cert hints norm = some f') (hN : NormSoundD f norm)
    {syms : String → Option Nat} (hres : globalsResolve f' syms = true) :
    FunSimMUAt syms f g := by
  unfold symsCopy at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact check_soundSyms_normD hc hN hres
    · cases h
  · split at h
    · split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        exact (check_soundSyms_normD hc.2 hN hres).trans ((condPrep_simU hc.1).toMU.at syms)
      · cases h
    · split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        exact ((foldPre_simU f _).toMU.at syms).trans
          ((check_soundSyms hc.2 hres).trans ((condPrep_simU hc.1).toMU.at syms))
      · split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          exact ((foldPreK_simU f _).toMU.at syms).trans
            ((check_soundSyms hc.2 hres).trans ((condPrep_simU hc.1).toMU.at syms))
        · cases h

/-- **Soundness of the copy the hoisting mode accepts against** (module doc). -/
theorem symsCopy_sound {f g f' : Function} {cert : Cert} {hints : List (BlockId × List Wrap)}
    {norm : Norm} (h : symsCopy f g cert hints norm = some f') (hN : NormSoundT f norm)
    {syms : String → Option Nat} (hres : globalsResolve f' syms = true) :
    FunSimMUAt syms f g := by
  exact symsCopy_soundD h hN.toD hres

/-- **Soundness of the hoisting-mode re-check at a symbol table** (default normaliser). -/
theorem checkCertSymsAt_sound {syms : String → Option Nat} {f g : Function} {cert : Cert}
    {hints : List (BlockId × List Wrap)} (h : checkCertSymsAt syms f g cert hints = true) :
    FunSimMUAt syms f g := by
  unfold checkCertSymsAt at h
  split at h
  · rename_i f' hc
    exact symsCopy_soundD hc normSoundD_stdD h
  · cases h

/-- `g` stands for `f` at `syms` through constant-phi removal and the hoisting-mode re-check. -/
theorem checkedSymsAt_simMUAt {syms : String → Option Nat} {f g : Function} {cert : Cert}
    {hints : List (BlockId × List Wrap)}
    (h : checkCertSymsAt syms (ConstPhi.run f) g cert hints = true) : FunSimMUAt syms f g :=
  ((ConstPhi.run_simU f).toMU.at syms).trans (checkCertSymsAt_sound h)

end Opt.MidVal
