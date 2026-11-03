import FV.E2E.LinkGoodBoundedW

namespace E2E.StockAcquirePending
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The original outside-map avoidance fields extend the source relation's kept set.
No permission test or source-input classifier is introduced. -/
theorem relW_keep_of_avoids {Γ : Rel} {f : Clif.Function} {c : BitVec 64}
    {slots : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {world : Arm.ArmState} {S : BitVec 64 → Prop}
    (related : RelW Γ f c slots cm world)
    (validAvoids : ∀ a n,cm.valid a n = true → ∀ k < n,¬ S (BitVec.ofNat 64 (a+k)))
    (outgoingAvoids : ∀ j < Γ.out,¬ S (spv world+BitVec.ofNat 64 j)) :
    RelW {Γ with F := fun a => Γ.F a ∨ S a} f c slots cm world := by
  have memory : MemRel (fun a => Γ.F a ∨ S a) Γ.syms cm world := by
    refine ⟨related.1.1.bytes,?_,related.1.1.symbols⟩
    intro a n valid
    obtain ⟨fits,avoids⟩ := related.1.1.valid a n valid
    exact ⟨fits,fun k inside marked => marked.elim (avoids k inside) (validAvoids a n valid k inside)⟩
  have outgoing : OutRel (fun a => Γ.F a ∨ S a) Γ.out cm world := by
    refine ⟨related.1.2.2.1,?_,related.1.2.2.2.2⟩
    intro j inside marked
    exact marked.elim (related.1.2.2.2.1 j inside) (outgoingAvoids j inside)
  exact ⟨⟨memory,related.1.2.1,outgoing⟩,related.2⟩

/-- The original body-entry fields remain valid when the kept set grows. -/
theorem bodyEntryW_keep {F S : BitVec 64 → Prop} {A : Reg → Prop} {af : AFunc}
    {initial world : Arm.ArmState} (entry : BodyEntryW F A af initial world) :
    BodyEntryW (fun a => F a ∨ S a) A af initial world := by
  exact ⟨entry.sp,entry.fp,entry.args,entry.other,
    fun a outside => entry.mem a (fun marked => outside (.inl marked)),entry.program⟩

/-- Original stack avoidance constructs the extended linked entry and retains all inherited image facts. -/
theorem machEntry_keep_of_stack_avoids (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {M : Nat} {f : Clif.Function} {F G S : BitVec 64 → Prop} {ra : BitVec 64} {initial world : Arm.ArmState}
    (entry : L.MachEntry κ M f F G ra initial world)
    (stackAvoids : ∀ a,S a → ¬ StackBelow (frameDrop (L.A f).af+κ M f) (spv initial) a) :
    ({L with F := fun a => F a ∨ S a,Img := fun a => L.Img a ∨ S a,imgMem := initial.mem} : LinkSys).MachEntry
      κ M f (fun a => F a ∨ S a) (fun a => G a ∨ S a) ra initial world := by
  refine ⟨entry.abi,entry.stack,?_,?_,?_,?_,bodyEntryW_keep entry.body⟩
  · intro a marked
    exact marked.elim (entry.gfree a) (stackAvoids a)
  · change frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af (fun a => G a ∨ S a) initial = _
    rw [← entry.hF]
    funext a
    apply propext
    exact or_assoc.symm
  · intro a marked
    exact marked.elim (fun old => .inl (entry.imgG a old)) Or.inr
  · intro a marked
    rfl


/-- Actual allocation and body entry place the outgoing area inside the original available stack. -/
theorem outgoing_avoids_of_original_stack {vc : VCode} {rf : RFunc} {af : AFunc}
    (allocated : lowerRFunc vc rf = .ok af) {K : Nat} {F S : BitVec 64 → Prop} {A : Reg → Prop}
    {initial world : Arm.ArmState} (stack : StackAvail K af initial)
    (body : BodyEntryW F A af initial world)
    (avoids : ∀ a,S a → ¬ StackBelow (frameDrop af+K) (spv initial) a) :
    ∀ j < (RAFrame.compute vc rf).intBase,¬ S (spv world+BitVec.ofNat 64 j) := by
  have frame := lowerRFunc_frame allocated
  have drop : frameDrop af = af.frameSize+16 := by simp [frameDrop,frame]
  have room : frameDrop af+K ≤ (spv initial).toNat := by simpa only [drop] using stack.1
  have size := size_le_frameSize allocated
  have base := intBase_le_size vc rf
  have top := (spv initial).isLt
  have worldNat : (spv world).toNat = (spv initial).toNat-frameDrop af := by
    rw [body.sp]
    exact (off_toNat 0 (spv initial) (frameDrop af) (by omega)).2.2
  intro j inside marked
  have jBound : j < 2^64 := by omega
  have sumBound : (spv world).toNat+j < 2^64 := by omega
  have address : (spv world+BitVec.ofNat 64 j).toNat = (spv world).toNat+j := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt jBound,Nat.mod_eq_of_lt sumBound]
  apply avoids _ marked
  change (spv world+BitVec.ofNat 64 j).toNat < (spv initial).toNat ∧
    (spv initial).toNat ≤ (spv world+BitVec.ofNat 64 j).toNat+(frameDrop af+K)
  rw [address]
  omega

/-- Original stack-argument avoidance transports through the actual frame-pointer equation. -/
theorem argsAtEntry_keep_of_original_stack {vc : VCode} {rf : RFunc} {af : AFunc}
    (allocated : lowerRFunc vc rf = .ok af) {F S : BitVec 64 → Prop} {A : Reg → Prop}
    {initial world : Arm.ArmState} (body : BodyEntryW F A af initial world)
    {sig : Clif.Signature} {args : List Clif.Val} (arguments : ArgsAtEntry F sig args world)
    (avoids : ∀ off v,(ArgLoc.stack off,v) ∈ (locsOf sig).zip args →
      Avoids S v.ty.bytes (spv initial+BitVec.ofNat 64 off)) :
    ArgsAtEntry (fun a => F a ∨ S a) sig args world := by
  have frame := lowerRFunc_frame allocated
  intro loc v member
  cases loc with
  | reg pin => exact arguments (.reg pin) v member
  | stack off =>
    obtain ⟨oldAvoids,read⟩ := arguments (.stack off) v member
    have address : Arm.r (.GPR 29#5) world+BitVec.ofInt 64 (16+(off : Int)) =
        spv initial+BitVec.ofNat 64 off := by
      change xreg 29 world+BitVec.ofInt 64 (16+(off : Int)) = _
      rw [body.fp,frame]
      exact fp_off_eq (spv initial) off
    refine ⟨?_,read⟩
    intro j inside marked
    rcases marked with old | new
    · exact oldAvoids j inside old
    · apply avoids off v member j inside
      rwa [address] at new


/-- The original outside-map fields construct the complete kept linked entry and source/world premises.
The final map adapter supplies these fields from the unchanged original mapping relation. -/
theorem linked_entry_keep_fields (L : LinkSys) {κ : Nat → Clif.Function → Nat}
    {M : Nat} {f : Clif.Function} {F G S : BitVec 64 → Prop} {ra c : BitVec 64}
    {initial world : Arm.ArmState} {syms : String → Option Nat} {slotOff : Nat}
    {slots : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {args : List Clif.Val}
    (allocated : lowerRFunc (L.A f).vcp (L.A f).rf = .ok (L.A f).af)
    (entry : L.MachEntry κ M f F G ra initial world)
    (related : RelW ⟨F,syms,slotOff,(RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f c slots cm world)
    (arguments : ArgsAtEntry F f.sig args world)
    (stackAvoids : ∀ a,S a → ¬ StackBelow (frameDrop (L.A f).af+κ M f) (spv initial) a)
    (argumentAvoids : ∀ off v,(ArgLoc.stack off,v) ∈ (locsOf f.sig).zip args →
      Avoids S v.ty.bytes (spv initial+BitVec.ofNat 64 off))
    (validAvoids : ∀ a n,cm.valid a n = true → ∀ k < n,¬ S (BitVec.ofNat 64 (a+k))) :
    ({L with F := fun a => F a ∨ S a,Img := fun a => L.Img a ∨ S a,imgMem := initial.mem} : LinkSys).MachEntry
      κ M f (fun a => F a ∨ S a) (fun a => G a ∨ S a) ra initial world ∧
    RelW ⟨(fun a => F a ∨ S a),syms,slotOff,(RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩
      f c slots cm world ∧ ArgsAtEntry (fun a => F a ∨ S a) f.sig args world := by
  refine ⟨machEntry_keep_of_stack_avoids L entry stackAvoids,?_,?_⟩
  · exact relW_keep_of_avoids related validAvoids
      (outgoing_avoids_of_original_stack allocated entry.stack entry.body stackAvoids)
  · exact argsAtEntry_keep_of_original_stack allocated entry.body arguments argumentAvoids

end E2E.StockAcquirePending
