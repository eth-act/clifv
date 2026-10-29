module

public import FV.Backend.Proof.StockTermContract
public import FV.Backend.Proof.PrepareSound

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Preparation preserves the ABI-aware source outcome and the selected
initial virtual file. It does not require a legacy lowering certificate. -/
theorem RunOkABI.prepared {f : Clif.Function} {vc vcp : VCode} {isem : Backend.Proof.Sem}
    (driver : DriverSem isem) (checked : prepCheck vc vcp = true)
    {MR : MemRelT} {slots : List (Clif.SlotId × Nat)} {ρ : Nat → CV} {w : Arm.ArmState}
    {outcome : Clif.Outcome} (source : RunOkABI f vc isem MR slots ⟨0,0,ρ,w⟩ outcome) :
    RunOkABI f vcp isem MR slots ⟨0,0,ρ,w⟩ outcome := by
  have preserved := prep_sound driver checked ρ w
  cases outcome with
  | returned vals cm =>
    obtain ⟨us,outs,w',cm0,reached,abi,arity,values,memory,freed⟩ := source
    exact ⟨us,outs,w',cm0,preserved.1 us outs w' reached,abi,arity,values,memory,freed⟩
  | trapped code => exact preserved.2 code source
  | stuck message => trivial
  | outOfFuel => trivial

end Backend.Stock.Proof
