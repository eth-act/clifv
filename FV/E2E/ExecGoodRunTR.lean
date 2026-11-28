import FV.E2E.ExecGoodRunT
import FV.E2E.LinkArmTR

/-!
# `ExecGoodRunT` for `LinkSys.OkTR` and `okBTSR` (#753, stage R4)

The declarations of `ExecGoodRunT` on the paths from the typed Stock binary theorems to
`LinkSys.OkT`/`okBTS`, for the link contract with the register-guarded calls `LinkSys.OkTR` and
the checks `okBTSR` (suffix `R`).
-/
namespace E2E.ExecBytes
open Backend Backend.Proof E2E.LinkCheck E2E.Binary E2E.BinCheck
section Conv
variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- The calls through a register of a function of a linked system with `OkTR` are through integer
vregs (`LinkSys.OkTR.blrShape`). -/
theorem destsInt_of_okTR {L : LinkSys} (hL : L.OkTR) {g : Clif.Function} (hg : g ∈ L.P.funcs) :
    (L.A g).vcp.DestsInt := by
  intro b vb k info hb hi r hd
  obtain ⟨t, Lc, Dc, hshape⟩ := hL.blrShape g hg info ⟨b, vb, k, hb, hi⟩ (fun n => by rw [hd]; simp)
  rw [hshape] at hd
  simp only [CallDest.reg.injEq] at hd
  exact ⟨t, hd.symm⟩

end Conv
end E2E.ExecBytes
