import FV.Backend
import FV.Backend.RegallocPerEdgePrepare

/-! Compatibility of the shared file pipeline and preservation of route payloads.
The generic route does not establish Stock source correctness or enable it in
production. In particular its allocator must receive per-successor vectors intact.
-/
namespace Backend.Proof.LoweringPipeline

/-- Specializing the shared pipeline to checked legacy lowering preserves the
entire monadic computation, including allocator effects and artifact metadata. -/
theorem compileFileWith_legacy {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String)) (deadCleanup : Bool) :
    compileFileWithLowering lowerForAllocation VCode.rulesFired alloc pf preUnverified deadCleanup =
      compileFileWith alloc pf preUnverified deadCleanup := rfl

private def source : Clif.Function := {
  name := "payload"
  sig := { params := [⟨.i64, .none, .normal⟩], returns := [⟨.i64, .none, .normal⟩] }
  blocks := [{ id := 0, params := [(0, .i64)], term := .ret [0] }] }

private def file : Clif.ParsedFile := {
  header := [], funcs := [⟨source.name, .ok source, 0⟩] }

private def payload : EdgeVCode := {
  code := { name := source.name, blocks := #[], classes := #[], slotBytes := 0, outgoing := 0, rulesFired := #[] }
  edges := #[#[#[.vreg 193 .int], #[.vreg 194 .int, .vreg 195 .int]]] }

private def recordAllocator (inputs : Array EdgeVCode) :
    StateM (Array EdgeVCode) (Array (Except String AFunc)) := do
  set inputs
  pure (inputs.map fun _ => .error "recorded complete payload")

/-- Nonempty, unequal successor vectors survive the common pipeline unchanged
and reach the allocator. Allocation rejection does not erase the captured input. -/
theorem successor_payload_witness :
    ((compileFileWithLowering (fun _ _ _ => .ok payload)
      (fun x : EdgeVCode => x.code.rulesFired) recordAllocator file
      [(source.name, "unverified payload transport witness")] false).run #[]).2.map (·.edges) = #[payload.edges] := by
  decide +kernel

/-- Concrete non-vacuity of legacy specialization: the original checked lowering
and the common route agree on an inhabited integer parameter-return function,
for both cleanup settings and both verification settings. -/
theorem legacy_specialization_witness (verify deadCleanup : Bool) :
    let alloc := fun (_ : Array VCode) => (pure #[] : Id (Array (Except String AFunc)))
    let pf : Clif.ParsedFile := file
    compileFileWithLowering lowerForAllocation VCode.rulesFired alloc pf
        (if verify then [] else [(source.name, "witness verification disabled")]) deadCleanup =
      compileFileWith alloc pf
        (if verify then [] else [(source.name, "witness verification disabled")]) deadCleanup := rfl

end Backend.Proof.LoweringPipeline
