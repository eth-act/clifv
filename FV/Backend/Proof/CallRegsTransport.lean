import FV.Backend.Proof.CtxTWTransport
import FV.Backend.Proof.ScopeTransport

/-!
# The transports with the indirect families with registers (#753, stage R2)

`CtxTWTransport`'s and `ScopeTransport`'s commands with the indirect families with registers added
to their replacements: `ctxWR_transport src => dst` (`ctxW_transport` with
`IndRulesCorrectTPR ↦ IndRulesCorrectTPRW`, `TryIndRulesCorrectTPR ↦ TryIndRulesCorrectTPRW`),
`scopeSR_transport src => dst` (`scopeS_transport` with `IndRulesCorrectTPRW ↦
IndRulesCorrectTPRS`, `TryIndRulesCorrectTPRW ↦ TryIndRulesCorrectTPRS`) and
`scopeSR_transport_defs` (declares the `…S` families; used in `LowerContractTPR`). Like the two
modules it extends, it imports only `Lean`: the commands read no file.
-/

namespace Backend.Proof.CallRegsTransport

open Lean Meta Elab Command

/-- The indirect families with registers over `CtxT` and their `CtxTW` forms. -/
def ctxWPairsR : List (Name × Name) := [
  (`Backend.Proof.IndRulesCorrectTPR, `Backend.Proof.IndRulesCorrectTPRW),
  (`Backend.Proof.TryIndRulesCorrectTPR, `Backend.Proof.TryIndRulesCorrectTPRW)]

/-- The indirect families with registers over `CtxTW` and their scope-generic forms. -/
def scopePairsR : List (Name × Name) := [
  (`Backend.Proof.IndRulesCorrectTPRW, `Backend.Proof.IndRulesCorrectTPRS),
  (`Backend.Proof.TryIndRulesCorrectTPRW, `Backend.Proof.TryIndRulesCorrectTPRS)]

/-- `ctxW_transport` with `ctxWPairsR` added to the replacement. -/
elab "ctxWR_transport " src:ident " => " dst:ident : command => do
  let srcName ← liftCoreM <| realizeGlobalConstNoOverload src
  let dstName := (← getCurrNamespace) ++ dst.getId
  liftCoreM do
    let m := ctxWPairsR.foldl (fun m (a, b) => m.insert a b) CtxTWTransport.baseMap
    let some c' ← (CtxTWTransport.ensure srcName).run' { map := m }
      | throwError "ctxWR_transport: {srcName} does not mention `CtxT`"
    let info ← getConstInfo c'
    let val : TheoremVal :=
      ⟨⟨dstName, info.levelParams, info.type⟩, .const c' (info.levelParams.map Level.param), [dstName]⟩
    addDecl (Declaration.thmDecl val)

/-- `ScopeTransport.initState` with `scopePairsR` added to the replacement. -/
def initStateR : MetaM ScopeTransport.St := do
  let st ← ScopeTransport.initState
  return { st with map := scopePairsR.foldl (fun m (a, b) => m.insert a b) st.map }

/-- `scopeS_transport` with `scopePairsR` added to the replacement. -/
elab "scopeSR_transport " src:ident " => " dst:ident : command => do
  let srcName ← liftCoreM <| realizeGlobalConstNoOverload src
  let dstName := (← getCurrNamespace) ++ dst.getId
  liftTermElabM do
    let some c' ← (ScopeTransport.ensure srcName).run' (← initStateR)
      | throwError "scopeSR_transport: {srcName} does not mention a replaced constant"
    let info ← getConstInfo c'
    addDecl (Declaration.thmDecl
      ⟨⟨dstName, info.levelParams, info.type⟩, .const c' (info.levelParams.map Level.param), [dstName]⟩)

/-- `scopeS_transport_defs` for `scopePairsR`: the scope-generic indirect families with
registers. -/
elab "scopeSR_transport_defs" : command => do
  liftTermElabM do
    let go : ScopeTransport.M Unit := do
      for (a, _) in scopePairsR do
        discard <| ScopeTransport.ensure a
    go.run' (← initStateR)

end Backend.Proof.CallRegsTransport
