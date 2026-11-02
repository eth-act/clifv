import FV.E2E.LinkArm

namespace E2E.LinkSys

def extImgProduction (L : LinkSys) (F S : BitVec 64 → Prop) (m : Arm.Memory) : LinkSys :=
  { L with F := F, Img := fun a => L.Img a ∨ S a, imgMem := m }


theorem Budget.extImgProduction {L : LinkSys} {κ : Nat → Clif.Function → Nat} (h : L.Budget κ)
    (F S : BitVec 64 → Prop) (m : Arm.Memory) : (L.extImgProduction F S m).Budget κ := h


end E2E.LinkSys
