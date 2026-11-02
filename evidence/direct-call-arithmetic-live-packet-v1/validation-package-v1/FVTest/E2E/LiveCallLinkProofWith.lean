import FVTest.E2E.ReturnPinLinkProofWith
import FV.E2E.LiveCallChecks
import FV.E2E.LiveCallGeneratedStack

set_option autoImplicit false
namespace FVTest.E2E.ReturnPinLinkProofWith

def ProofApi.liveCalls : ProofApi :=
  ⟨"FV.E2E.LiveCallChecks", "LiveCallChecks", "FV.E2E.LiveCallGeneratedStack",
    "LiveCallGeneratedStack", "LiveCallBinary", "okRReturnPinLiveCalls"⟩

end FVTest.E2E.ReturnPinLinkProofWith

namespace FVTest.E2E.LiveCallLinkProofWith
open _root_.E2E _root_.E2E.LinkCheck _root_.E2E.BinCheck Backend Lean

def leanFilesLiveCallWith (lowerName : String) (I : LinkInput) (names : List String) (entries : List String) (out module exe : String)
    (cleanup : Bool)
    (noTls : Bool) (stack : Option Nat) (stackEntries : List String) (bg : BinGen)
    (lowerImport : String := "FV.Backend.Lowering.StockLiveCallRoutes")
    (sliceLimit : Nat := sliceSize) :
    List (String × String) :=
  ReturnPinLinkProofWith.leanFilesReturnPinFor ReturnPinLinkProofWith.ProofApi.liveCalls lowerName I names entries out module exe cleanup noTls stack stackEntries bg lowerImport sliceLimit

end FVTest.E2E.LiveCallLinkProofWith
