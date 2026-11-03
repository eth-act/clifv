import FV.E2E.CompiledReturnPinReturnTraceW
import FV.E2E.LinkReturnPinGoodWProgram

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
namespace LinkSys
variable (L : LinkSys) {modes : Clif.Function → ReturnPinMode}
variable {κ : Nat → Clif.Function → Nat}
set_option autoImplicit false
set_option Elab.async false

/-- Original checked program artifacts supply every required return provider. -/
theorem worldReturnTraceProviders_of_ok (hL : L.OkReturnPins modes) :
    ∀ g ∈ L.P.funcs, ∃ returns,
      WorldReturnTraceProvider L.P.bare g (L.A g).vc (L.A g).vcp (L.A g).rf
        (L.A g).af (L.A g).fa (L.A g).fb returns := by
  intro g member
  exact ⟨(modes g).Valid g,
    worldReturnTraceProvider_artifact (hL.subset g member) (hL.compiled g member).artifact⟩

/-- The original induction step derives its providers from checked artifacts. -/
theorem thmGW_of_return_pins_internal (hL : L.OkReturnPins modes) [L.CrunOk]
    (hκ : L.Budget κ) {M : Nat}
    (ih : 0 < M → L.ThmReturnPins modes κ (M - 1))
    (ihG : 0 < M → L.ThmGW κ (M - 1)) : L.ThmGW κ M :=
  L.thmGW_of_return_pins hL (L.worldReturnTraceProviders_of_ok hL) hκ ih ihG

/-- Every depth retains the ordinary and paired W guarantees without a caller provider. -/
theorem thmGW_return_pins_internal (hL : L.OkReturnPins modes) [L.CrunOk]
    (hκ : L.Budget κ) : ∀ M, L.ThmGW κ M :=
  L.thmGW_return_pins hL (L.worldReturnTraceProviders_of_ok hL) hκ

end LinkSys
end E2E
