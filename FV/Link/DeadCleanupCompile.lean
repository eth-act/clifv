import FV.Link.Compile
import FV.Link.DeadCleanupImage
namespace Link.DeadCleanup
set_option autoImplicit false
def compileExe (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  if inScopePar S.input0 then leanLink S file0 else .error outOfScopeMsg


end Link.DeadCleanup
