import FVTest.E2E.ReturnPinLinkProofWith
import FV.E2E.ResultCallChecks
import FV.E2E.ResultCallGeneratedStack

set_option autoImplicit false
namespace FVTest.E2E.ResultCallLinkProofWith
open _root_.E2E _root_.E2E.LinkCheck _root_.E2E.BinCheck Backend Lean

def leanFilesResultCallWith (lowerName : String) (I : LinkInput) (names : List String) (entries : List String) (out module exe : String)
    (cleanup : Bool)
    (noTls : Bool) (stack : Option Nat) (stackEntries : List String) (bg : BinGen)
    (lowerImport : String := "FV.Backend.Lowering.StockResultCallRoutes")
    (sliceLimit : Nat := sliceSize) :
    List (String × String) :=
  ReturnPinLinkProofWith.leanFilesReturnPinFor .resultCalls lowerName I names entries out module exe cleanup noTls stack stackEntries bg lowerImport sliceLimit

end FVTest.E2E.ResultCallLinkProofWith
