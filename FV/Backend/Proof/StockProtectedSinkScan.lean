import FV.Backend.Proof.StockProtectedSinkFrame
import FV.Backend.Proof.StockNoLoadScan

namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Result binding, aliases and every actual scan decision preserve the protected slot. -/
theorem scan_protected_slot {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {slot : Nat}
    (safe : NoLoadAt ctx slot) (empty : ctx.insts[slot]!.results = [])
    {block i ti : Nat} {branch : Bool} {st : State} {output : Scan}
    (run : scanInstruction ctx block i ti branch st = .ok output) :
    output.state.sunk[slot]! = st.sunk[slot]! :=
  scan_sunk_at_of_lower (fun call => protected_slot_lower mapped safe empty call) run

/-- Every retained record carries the same original protected-slot value. -/
theorem scans_protected_slot {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {slot : Nat}
    (safe : NoLoadAt ctx slot) (empty : ctx.insts[slot]!.results = [])
    {block ti : Nat} {branch : Bool} {indices : List Nat} {st : State} {output : BlockScan}
    (cert : ScansSpec (fun i => scanInstruction ctx block i ti branch) indices st output) :
    output.state.sunk[slot]! = st.sunk[slot]! ∧
      ∀ r ∈ output.records,r.input.sunk[slot]! = st.sunk[slot]! ∧
        r.output.state.sunk[slot]! = st.sunk[slot]! :=
  scans_sunk_at_of_lower (fun call => protected_slot_lower mapped safe empty call) cert

/-- Complete scans preserve the protected slot at every retained record boundary. -/
theorem scan_block_protected_slot {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) {slot : Nat}
    (safe : NoLoadAt ctx slot) (empty : ctx.insts[slot]!.results = [])
    {block ti : Nat} {branch : Bool} {indices : List Nat} {st : State} {output : BlockScan}
    (run : scanBlock ctx block ti branch indices st = .ok output) :
    output.state.sunk[slot]! = st.sunk[slot]! ∧
      ∀ r ∈ output.records,r.input.sunk[slot]! = st.sunk[slot]! ∧
        r.output.state.sunk[slot]! = st.sunk[slot]! :=
  scans_protected_slot mapped safe empty (runScans_spec run)

end Backend.Stock.Proof.SinkRules
