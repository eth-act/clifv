import FV.E2E.CallStorePhysicalImage

namespace E2E.CallStorePhysicalExec
open Backend Backend.Proof Link E2E.LinkCheck E2E.CallStoreFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def objectBytes (words : Array (BitVec 32)) : ByteArray :=
  words.foldl (fun bytes word => (List.range 4).foldl
    (fun bytes k => bytes.push (UInt8.ofNat (word.toNat / 2^(8*k)))) bytes) ByteArray.empty

#eval do
  let root : System.FilePath := "/home/lee/clifv/.git/agent-evidence/stock-memory-20261029/direct-call-store-live-packet-v1/physical-exec-prep-v1/actual-images-v1"
  IO.FS.createDirAll root
  IO.FS.writeFile (root/"original-caller.clif") callerText
  IO.FS.writeFile (root/"original-callee.clif") calleeText
  for cleanup in [false,true] do
    let stem := if cleanup then "cleanup" else "raw"
    let image ← match linked cleanup with
      | .error message => throw (IO.userError message)
      | .ok image => pure image
    IO.FS.writeBinFile (root/(stem++".elf")) image
    IO.FS.writeFile (root/(stem++".caller.ra.json")) (answer cleanup caller)
    IO.FS.writeFile (root/(stem++".callee.ra.json")) (answer cleanup callee)
    IO.FS.writeFile (root/(stem++".linked-words.json"))
      (Lean.toJson ((linkedWords cleanup).map fun (entry : BitVec 64 × BitVec 32) => (entry.1.toNat,entry.2.toNat))).compress
    for (f,a) in tabOf (results cleanup) do
      IO.FS.writeBinFile (root/(stem++"."++f.name++".object.bin")) (objectBytes a.fb.words)
      IO.FS.writeFile (root/(stem++"."++f.name++".relocations.txt")) (reprStr a.fb.relocs)
    IO.println s!"exported {stem}: {image.size} ELF bytes; {(linkedWords cleanup).length} linked instructions"

end E2E.CallStorePhysicalExec
