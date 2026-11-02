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
