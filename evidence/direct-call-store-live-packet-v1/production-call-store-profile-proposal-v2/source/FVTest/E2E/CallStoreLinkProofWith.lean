import FVTest.E2E.ReturnPinLinkProofWith
import FV.E2E.CallStoreChecks
import FV.E2E.CallStoreGeneratedStack

set_option autoImplicit false
namespace FVTest.E2E.ReturnPinLinkProofWith

def ProofApi.callStores : ProofApi :=
  ⟨"FV.E2E.CallStoreChecks", "CallStoreChecks", "FV.E2E.CallStoreGeneratedStack",
    "CallStoreGeneratedStack", "CallStoreBinary", "okRReturnPinCallStores"⟩

end FVTest.E2E.ReturnPinLinkProofWith

namespace FVTest.E2E.CallStoreLinkProofWith
open _root_.E2E _root_.E2E.LinkCheck _root_.E2E.BinCheck Backend Lean

def leanFilesCallStoreWith (lowerName : String) (I : LinkInput) (names : List String) (entries : List String) (out module exe : String)
    (cleanup : Bool)
    (noTls : Bool) (stack : Option Nat) (stackEntries : List String) (bg : BinGen)
    (lowerImport : String := "FV.Backend.General7CallStoreProduction")
    (sliceLimit : Nat := sliceSize) :
    List (String × String) :=
  ReturnPinLinkProofWith.leanFilesReturnPinFor ReturnPinLinkProofWith.ProofApi.callStores lowerName I names entries out module exe cleanup noTls stack stackEntries bg lowerImport sliceLimit

end FVTest.E2E.CallStoreLinkProofWith
