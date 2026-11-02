import FV.Link.ReturnPinAttemptKernel
import FV.Link.SemanticCompileDefs
import FV.E2E.PreparedReturnPinCalls

namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
variable {lower : ProductionLowering}

def attempt (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) : Except String ByteArray :=
  ReturnPinAttemptKernel.attemptWith okRReturnPinCalls lower S file0 cleanup

end Link.ReturnPinCompilerWith

namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

/-- Keep a complete checked attempt or run the complete previous compiler on its original input. -/
def compileWithFallback (current previous : ProductionLowering) (S : LinkSpec)
    (file0 : ByteArray) (cleanup : Bool) : Except String SemanticCompilerWith.Output :=
  match attempt current (S.placedProductionWith current cleanup) file0 cleanup with
  | .ok file => .ok ⟨file,true⟩
  | .error _ => SemanticCompilerWith.compile previous S file0 cleanup

end Link.ReturnPinCompilerWith
namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false

/-- Keep the existing compiler tag with the complete selected output. -/
def compileWithChoice (current previous : ProductionLowering) (S : LinkSpec)
    (file0 : ByteArray) (cleanup : Bool) : Except String SemanticCompilerWith.FallbackOutput :=
  match attempt current (S.placedProductionWith current cleanup) file0 cleanup with
  | .ok file => .ok ⟨file,.current⟩
  | .error _ => (SemanticCompilerWith.compile previous S file0 cleanup).map fun out =>
      ⟨out.file,if out.stock then .previous else .legacy⟩

def eraseChoice (out : SemanticCompilerWith.FallbackOutput) : SemanticCompilerWith.Output :=
  ⟨out.file,match out.choice with | .legacy => false | _ => true⟩

end Link.ReturnPinCompilerWith
