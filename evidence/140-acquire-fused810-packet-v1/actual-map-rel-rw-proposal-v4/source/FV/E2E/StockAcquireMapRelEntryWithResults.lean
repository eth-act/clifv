import FV.E2E.StockAcquireMapRelRWWithResults
import FV.E2E.StockAcquireKeptWorld
import FV.E2E.StockAcquireLayoutImage

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

/-- The original mapping fields derive the kept entry, source relation, and argument relation.
The original stack budget supplies the internal depth bound. -/
theorem mapRelRW_linked_entry (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {M N : Nat} {f : Clif.Function} {results : Res} {mp : ArmFault.MemMap}
    {F G : BitVec 64 → Prop} {ra c : BitVec 64} {initial world : Arm.ArmState}
    {syms : String → Option Nat} {slotOff : Nat} {slots : List (Clif.SlotId × Nat)}
    {cm : Clif.Mem} {args : List Clif.Val}
    (mapped : MapRelRWWithResults mp results f N initial args cm)
    (budget : frameDrop (L.A f).af + κ M f ≤ N)
    (allocated : lowerRFunc (L.A f).vcp (L.A f).rf = .ok (L.A f).af)
    (entry : L.MachEntry κ M f F G ra initial world)
    (related : RelW ⟨F,syms,slotOff,(RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩
      f c slots cm world)
    (arguments : ArgsAtEntry F f.sig args world) :
    ({L with F := fun a => F a ∨ (mp a).allows .W = false,
      Img := fun a => L.Img a ∨ (mp a).allows .W = false, imgMem := initial.mem} : LinkSys).MachEntry
      κ M f (fun a => F a ∨ (mp a).allows .W = false)
      (fun a => G a ∨ (mp a).allows .W = false) ra initial world ∧
    RelW ⟨(fun a => F a ∨ (mp a).allows .W = false),syms,slotOff,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f c slots cm world ∧
    ArgsAtEntry (fun a => F a ∨ (mp a).allows .W = false) f.sig args world := by
  apply linked_entry_keep_fields L allocated entry related arguments
  · intro a forbidden below
    apply mapped.nw.stack a forbidden
    exact ⟨below.1, Nat.le_trans below.2 (Nat.add_le_add_left budget _)⟩
  · exact mapped.nw.args
  · exact mapped.nw.valid

/-- Actual layout and the original mapping relation derive readable table bytes. -/
theorem mapRelRW_actual_tables_readable {results : Res} {mp : ArmFault.MemMap}
    {f : Clif.Function} {N : Nat} {initial : Arm.ArmState} {args : List Clif.Val} {cm : Clif.Mem}
    (mapped : MapRelRWWithResults mp results f N initial args cm)
    (names : ((progOf results).funcs.map (·.name)).Nodup) (member : f ∈ (progOf results).funcs)
    (layout : (artOf results f).fa.layout = .ok (artOf results f).fb) :
    ∀ j target origin, (artOf results f).fa.lines.toList[j]? = some (.word target origin) →
      ∀ i < 4, (mp ((artOf results f).base +
        BitVec.ofNat 64 (lineOffset (artOf results f).fa.lines.toList j) + BitVec.ofNat 64 i)).allows .R = true := by
  intro j target origin located i byte
  exact mapRelRW_actual_code_readable mapped names member _
    (layout_line_codeAddr layout located rfl byte)

end E2E.StockAcquirePending
