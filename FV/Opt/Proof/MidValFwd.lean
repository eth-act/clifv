import FV.Opt.MidValFwd
import FV.Opt.Proof.MidValSim
import FV.Opt.Proof.MidValMagic

/-!
# Store-to-load forwarding before the folds is sound (#1119, family A)

`fwdOk f` (`FV/Opt/MidValFwd.lean`) is the checker's verdict on the forwarding copy `fwdPre f`
against `f` (`checkCert f (fwdPre f) cert`, the certificate from the untrusted `emit`). The
invariant that justifies each forwarded load is the checker's: in every run of `f`, at each
block, the memory holds the facts of the certificate (accessed successfully, no writer since), so
the load succeeds with the fact's value (`evalInst_load_of_holds`, `FV/Opt/Proof/MidValFacts.lean`)
or is `stuck`; `check_sound` turns the verdict into the simulation.

* **`fwdOk_simMU`**: `fwdOk f = true → FunSimMU f (fwdPre f)`;
* **`fwdFoldPre_simMU`**, **`fwdFoldPreK_simMU`**: the same composed with the fold prep
  (`foldPre_simU`, `foldPreK_simU`): `FunSimMU f (foldPre (fwdPre f) bs)` and
  `FunSimMU f (foldPreK (fwdPre f) bs)`.

The theorems on main (`foldPre_simU`, `foldPreK_simU`, `check_sound`, …) are unchanged.
-/

namespace Opt.MidVal

open Clif

/-- **The forwarding copy simulates its input** when the checker accepts it (module doc). -/
theorem fwdOk_simMU {f : Function} (h : fwdOk f = true) : FunSimMU f (fwdPre f) := by
  unfold fwdOk at h
  split at h
  · exact check_sound h
  · cases h

/-- **The fold prep after the forwarding** (`foldPre`; module doc). -/
theorem fwdFoldPre_simMU {f : Function} (h : fwdOk f = true) (bs : List BlockId) :
    FunSimMU f (foldPre (fwdPre f) bs) :=
  (fwdOk_simMU h).trans (foldPre_simU _ bs).toMU

/-- **The fold prep after the forwarding, parameters kept** (`foldPreK`; module doc). -/
theorem fwdFoldPreK_simMU {f : Function} (h : fwdOk f = true) (bs : List BlockId) :
    FunSimMU f (foldPreK (fwdPre f) bs) :=
  (fwdOk_simMU h).trans (foldPreK_simU _ bs).toMU

end Opt.MidVal
