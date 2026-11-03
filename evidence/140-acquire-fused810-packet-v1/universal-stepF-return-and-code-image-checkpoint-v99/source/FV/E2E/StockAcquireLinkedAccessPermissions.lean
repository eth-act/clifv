import FV.E2E.LinkGoodBoundedW

namespace E2E.LinkSys
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Internal image facts supply the original read/write permissions for a decoded unhooked instruction.
The actual binary consumer must derive the line and decoding facts from its checked artifact. -/
theorem goodAtW_access_allowed (L : LinkSys) {M : Nat} {g : Clif.Function} {initial state : Arm.ArmState}
    {mp : ArmFault.MemMap} (good : L.GoodAtW M g initial state)
    (kept : ∀ a,(mp a).allows .W = false → L.Img a)
    (readable : ∀ a,L.Img a → (mp a).allows .R = true)
    (tableImage : ∀ j tag bytes,(L.A g).fa.lines.toList[j]? = some (.word tag bytes) →
      ∀ i < 4,L.Img ((L.A g).base+BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j)+BitVec.ofNat 64 i))
    {j : Nat} {inst : Insn} {trap : Option Clif.TrapCode}
    (located : (L.A g).fa.lines.toList[j]? = some (.ins inst trap))
    (pc : Arm.r .PC state = (L.A g).base+BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j))
    (unhooked : inst.hooked = false) {encoding : Env} {decoded : Arm.ArmInst}
    (decode : inst.toArmInst encoding = .ok decoded) :
    ArmFault.evsOk mp (Concurrency.ArmInstFoot.instEvs decoded state) = true := by
  obtain ⟨X,K,G,gv,machine,actual,image,imageMem,blr⟩ := good
  exact RL.evsOk_of_goodXW actual (fun a denied => image a (kept a denied))
    (fun j tag bytes found i inside => readable _ (tableImage j tag bytes found i inside))
    located pc unhooked decode

/-- The complete bounded W trace supplies the same permission result for every reached activation.
This is a decoded model-event result; executable byte lookup and stepF correspondence remain separate. -/
theorem runGoodLBW_access_allowed (L : LinkSys) {n M : Nat} {f : Clif.Function} {initial : Arm.ArmState}
    {mp : ArmFault.MemMap} (good : L.RunGoodLBW n M f initial)
    (kept : ∀ a,(mp a).allows .W = false → L.Img a)
    (readable : ∀ a,L.Img a → (mp a).allows .R = true)
    (tableImage : ∀ g j tag bytes,(L.A g).fa.lines.toList[j]? = some (.word tag bytes) →
      ∀ i < 4,L.Img ((L.A g).base+BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j)+BitVec.ofNat 64 i))
    {M' : Nat} {g : Clif.Function} {entry state : Arm.ArmState}
    (reached : L.ReachLB n M f initial M' g entry state)
    (errorFree : Arm.r .ERR (L.mach M' g state) = .None)
    {j : Nat} {inst : Insn} {trap : Option Clif.TrapCode}
    (located : (L.A g).fa.lines.toList[j]? = some (.ins inst trap))
    (pc : Arm.r .PC state = (L.A g).base+BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j))
    (unhooked : inst.hooked = false) {encoding : Env} {decoded : Arm.ArmInst}
    (decode : inst.toArmInst encoding = .ok decoded) :
    ArmFault.evsOk mp (Concurrency.ArmInstFoot.instEvs decoded state) = true := by
  exact L.goodAtW_access_allowed (good M' g entry state reached errorFree)
    kept readable (tableImage g) located pc unhooked decode

/-- Separate code-image facts supply the original read/write permissions for a decoded unhooked instruction.
The kept image may also contain unmapped bytes. The actual binary consumer must derive the line and decoding facts from its checked artifact. -/
theorem goodAtW_access_allowed_code_image (L : LinkSys) {M : Nat} {g : Clif.Function} {initial state : Arm.ArmState}
    {mp : ArmFault.MemMap} {codeImage : BitVec 64 → Prop} (good : L.GoodAtW M g initial state)
    (kept : ∀ a,(mp a).allows .W = false → L.Img a)
    (readable : ∀ a,codeImage a → (mp a).allows .R = true)
    (tableImage : ∀ j tag bytes,(L.A g).fa.lines.toList[j]? = some (.word tag bytes) →
      ∀ i < 4,codeImage ((L.A g).base+BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j)+BitVec.ofNat 64 i))
    {j : Nat} {inst : Insn} {trap : Option Clif.TrapCode}
    (located : (L.A g).fa.lines.toList[j]? = some (.ins inst trap))
    (pc : Arm.r .PC state = (L.A g).base+BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j))
    (unhooked : inst.hooked = false) {encoding : Env} {decoded : Arm.ArmInst}
    (decode : inst.toArmInst encoding = .ok decoded) :
    ArmFault.evsOk mp (Concurrency.ArmInstFoot.instEvs decoded state) = true := by
  obtain ⟨X,K,G,gv,machine,actual,image,imageMem,blr⟩ := good
  exact RL.evsOk_of_goodXW actual (fun a denied => image a (kept a denied))
    (fun j tag bytes found i inside => readable _ (tableImage j tag bytes found i inside))
    located pc unhooked decode

/-- The complete bounded W trace supplies the same permission result for every reached activation.
This is a decoded model-event result; executable byte lookup and stepF correspondence remain separate. -/
theorem runGoodLBW_access_allowed_code_image (L : LinkSys) {n M : Nat} {f : Clif.Function} {initial : Arm.ArmState}
    {mp : ArmFault.MemMap} {codeImage : BitVec 64 → Prop} (good : L.RunGoodLBW n M f initial)
    (kept : ∀ a,(mp a).allows .W = false → L.Img a)
    (readable : ∀ a,codeImage a → (mp a).allows .R = true)
    (tableImage : ∀ g j tag bytes,(L.A g).fa.lines.toList[j]? = some (.word tag bytes) →
      ∀ i < 4,codeImage ((L.A g).base+BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j)+BitVec.ofNat 64 i))
    {M' : Nat} {g : Clif.Function} {entry state : Arm.ArmState}
    (reached : L.ReachLB n M f initial M' g entry state)
    (errorFree : Arm.r .ERR (L.mach M' g state) = .None)
    {j : Nat} {inst : Insn} {trap : Option Clif.TrapCode}
    (located : (L.A g).fa.lines.toList[j]? = some (.ins inst trap))
    (pc : Arm.r .PC state = (L.A g).base+BitVec.ofNat 64 (lineOffset (L.A g).fa.lines.toList j))
    (unhooked : inst.hooked = false) {encoding : Env} {decoded : Arm.ArmInst}
    (decode : inst.toArmInst encoding = .ok decoded) :
    ArmFault.evsOk mp (Concurrency.ArmInstFoot.instEvs decoded state) = true := by
  exact L.goodAtW_access_allowed_code_image (good M' g entry state reached errorFree)
    kept readable (tableImage g) located pc unhooked decode

end E2E.LinkSys
