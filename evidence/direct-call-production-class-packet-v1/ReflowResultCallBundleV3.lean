import FV.Link.ResultCallExeWith
import FV.Backend.Lowering.StockResultCallRoutes
import FV.Front.Read
import FV.Link.Ld.Plan
open Link Backend E2E E2E.LinkCheck Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def plan (S : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + S.size
  {base := 0x200000,entry := S.R,
   segs := [{kind := 1,vaddr := 0x200000,offset := 0,filesz := size,memsz := size}],
   tlsAddr := 0x200000+size,tlsOff := size,tlsFilesz := 0,tlsMemsz := 0,tlsAlign := 1,
   ehOff := 0,ehAddr := 0,ehSize := 0,size,pieces := [],secs := #[],
   syms := S.addrs.toArray.map fun (n,v) => {name := symName n,value := v,info := 18,shndx := 0xfff1}}

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := args[0]!
  let cleanup := args[1]! == "true"
  let (b,exe) ← Front.readBundle dir []
  let .ok S := Front.buildSpec {b with sizes := b.markers.map (fun (n,_) => (n,0))}
    | throw (IO.userError "actual allocator layout")
  let mode := S.funcs.all fun fi => match Stock.ResultCall.lowerValidated fi.func with
    | .error _ => false
    | .ok raw => SemanticABI.checkResultCalls fi.func raw
  let lower := if mode then Stock.ResultCall.lowerValidated else Stock.VoidCall.NI.lowerValidated
  let SP := S.placedProductionWith lower cleanup
  let .ok image := Link.Ld.assemble (plan SP)
    | throw (IO.userError "actual reserved image")
  IO.FS.writeBinFile exe image.write
  IO.FS.writeFile (dir / "actual-layout.json") (toJson SP.addrs).pretty
  IO.println s!"reserved actual layout: {SP.addrs}"
