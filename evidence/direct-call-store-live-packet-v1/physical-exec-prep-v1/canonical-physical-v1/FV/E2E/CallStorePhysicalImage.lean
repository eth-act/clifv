import FV.Link.ProductionImageWith
import FV.Link.Ld.Plan
import FV.E2E.StockCallStoreProviderWitness

namespace E2E.CallStorePhysicalExec
open Backend Backend.Proof Link E2E.LinkCheck E2E.CallStoreFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def lower := Stock.CallStore.lowerWithPrevious CallStoreProviderWitness.previous

def answer (cleanup : Bool) (f : Clif.Function) : String :=
  match lower f with
  | .error _ => "null"
  | .ok vc => match prepare (productionStage cleanup f vc) with
    | .error _ => "null"
    | .ok prepared => match leanAlloc prepared with
      | .error _ => "null"
      | .ok allocated => "{\"functions\":[" ++ raAnswerJson prepared allocated ++ "]}"

def initial (cleanup : Bool) : LinkSpec := {
  funcs := [{clif := callerText,ra := answer cleanup caller},{clif := calleeText,ra := answer cleanup callee}]
  names := [],sizes := [],outside := [],symNames := [caller.name,callee.name],R := 0x200160 }
def spec (cleanup : Bool) : LinkSpec := (initial cleanup).placedProductionWith lower cleanup

def plan (S : LinkSpec) : Link.Ld.Plan :=
  let size := 0x160 + S.size
  {base := 0x200000,entry := S.R,
   segs := [{kind := 1,vaddr := 0x200000,offset := 0,filesz := size,memsz := size}],
   tlsAddr := 0x200000+size,tlsOff := size,tlsFilesz := 0,tlsMemsz := 0,tlsAlign := 1,
   ehOff := 0,ehAddr := 0,ehSize := 0,size,pieces := [],secs := #[],
   syms := S.addrs.toArray.map fun (n,v) => {name := E2E.BinCheck.symName n,value := v,info := 18,shndx := 0xfff1}}
def file0 (cleanup : Bool) : ByteArray :=
  match Link.Ld.assemble (plan (spec cleanup)) with | .ok im => im.write | .error _ => ByteArray.empty
def linked (cleanup : Bool) := leanLinkProductionWith lower (spec cleanup) (file0 cleanup) cleanup
def file (cleanup : Bool) : ByteArray := getOk (linked cleanup)
def results (cleanup : Bool) : Res := (spec cleanup).input0.resultsProductionWith lower cleanup

def readWord (file : ByteArray) (address : BitVec 64) : BitVec 32 :=
  BitVec.ofNat 32 ((List.range 4).foldl (fun word k =>
    word + ((Elf.loadMem file (address + BitVec.ofNat 64 k)).getD 0).toNat * 2^(8*k)) 0)
def linkedWords (cleanup : Bool) : List (BitVec 64 × BitVec 32) :=
  let image := file cleanup
  (tabOf (results cleanup)).flatMap fun (_,a) => (List.range a.fb.words.size).map fun k =>
    let address := a.base + BitVec.ofNat 64 (4*k)
    (address,readWord image address)


end E2E.CallStorePhysicalExec
