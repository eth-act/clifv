import FV.Backend.Proof.IselMemBase

/-!
# Memory family (M4Mem): runs of address code and memory instructions

The run-time context of a statement (`RtOk`: frame of the context's function, values held, DFG
consistent, stack slots at `sp + sb + off`), the use values of an addressing mode (`amUses`), the
operand views of `load`/`store`/`loadAddr`/`loadExtNameGot` over vreg addressing modes, and
one-instruction runs of the memory forms under `MemRefines`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- The run-time facts a statement's lowering is run under: the frame is of `ctx`'s function,
its values are held by their vregs, it is DFG-consistent, and its stack slots are at
`sp + sb + off` (`MemRelOk.slots` with `CtxInv.slotOff`). -/
structure RtOk (ctx : Ctx) (sb : Nat) (fr : Clif.Frame) (ρ : Nat → CV) (w : Arm.ArmState) : Prop where
  func : fr.func = ctx.func
  held : ValsHeld fr ρ
  dfg : DFGCons ctx fr
  slots : ∀ id b, fr.slots.lookup id = some b →
    ∃ off, ctx.slotOff.lookup id = some off ∧ b = (spOf w).toNat + sb + off

/-- The vreg numbers of an addressing mode's registers. -/
def amVregs (am : AMode) : List Nat :=
  am.regs.filterMap fun r => match r with
    | .vreg n _ => some n
    | _ => none

/-- The use values of an addressing mode's registers. -/
def amUses (am : AMode) (ρ : Nat → CV) : List CV := (amVregs am).map ρ

/-- Every register of the addressing mode is an int vreg. -/
def AmVregs (am : AMode) : Prop := ∀ r ∈ am.regs, ∃ n, r = .vreg n .int

theorem amUses_congr {am : AMode} {ρ ρ' : Nat → CV} (h : ∀ u ∈ amVregs am, ρ' u = ρ u) :
    amUses am ρ' = amUses am ρ := by
  unfold amUses
  exact List.map_congr_left fun u hu => h u hu

/-- The operands of a load, a store, a `loadAddr` through a vreg addressing mode. -/
theorem am_operands_cases {am : AMode} (h : AmVregs am) :
    (∃ a b, am = .regReg (.vreg a .int) (.vreg b .int)) ∨
    (∃ a b, am = .regScaled (.vreg a .int) (.vreg b .int)) ∨
    (∃ a b e, am = .regScaledExtended (.vreg a .int) (.vreg b .int) e) ∨
    (∃ a b e, am = .regExtended (.vreg a .int) (.vreg b .int) e) ∨
    (∃ a i, am = .unscaled (.vreg a .int) i) ∨
    (∃ a i, am = .unsignedOffset (.vreg a .int) i) ∨
    (∃ a i, am = .regOffset (.vreg a .int) i) ∨
    am.regs = [] := by
  cases am with
  | regReg a b =>
    obtain ⟨x, rfl⟩ := h a (by simp [AMode.regs]); obtain ⟨y, rfl⟩ := h b (by simp [AMode.regs])
    exact .inl ⟨x, y, rfl⟩
  | regScaled a b =>
    obtain ⟨x, rfl⟩ := h a (by simp [AMode.regs]); obtain ⟨y, rfl⟩ := h b (by simp [AMode.regs])
    exact .inr (.inl ⟨x, y, rfl⟩)
  | regScaledExtended a b e =>
    obtain ⟨x, rfl⟩ := h a (by simp [AMode.regs]); obtain ⟨y, rfl⟩ := h b (by simp [AMode.regs])
    exact .inr (.inr (.inl ⟨x, y, e, rfl⟩))
  | regExtended a b e =>
    obtain ⟨x, rfl⟩ := h a (by simp [AMode.regs]); obtain ⟨y, rfl⟩ := h b (by simp [AMode.regs])
    exact .inr (.inr (.inr (.inl ⟨x, y, e, rfl⟩)))
  | unscaled a i =>
    obtain ⟨x, rfl⟩ := h a (by simp [AMode.regs])
    exact .inr (.inr (.inr (.inr (.inl ⟨x, i, rfl⟩))))
  | unsignedOffset a i =>
    obtain ⟨x, rfl⟩ := h a (by simp [AMode.regs])
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨x, i, rfl⟩)))))
  | regOffset a i =>
    obtain ⟨x, rfl⟩ := h a (by simp [AMode.regs])
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨x, i, rfl⟩))))))
  | _ => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))

/-- Operand view of an instruction with one late def `d` and the addressing mode's uses. -/
structure DefAmOps (i : MInst) (d : Nat) (am : AMode) : Prop where
  ops : ∃ ops, i.operands = .ok ops ∧ (∀ ρ : Nat → CV, vuses ops ρ = amUses am ρ) ∧
    (ops.toList.filter Operand.isDef).length = 1 ∧ (∀ (ρ : Nat → CV) (x : CV), vdefUpd ops [x] ρ = upd ρ d x)
  defs : vdefs i = [d]
  uses : vuseNums i = amVregs am

/-- Operand view of a store of vreg `v` through the addressing mode. -/
structure StoreAmOps (i : MInst) (v : Nat) (am : AMode) : Prop where
  ops : ∃ ops, i.operands = .ok ops ∧ (∀ ρ : Nat → CV, vuses ops ρ = ρ v :: amUses am ρ) ∧
    (ops.toList.filter Operand.isDef).length = 0 ∧ (∀ ρ : Nat → CV, vdefUpd ops [] ρ = ρ)
  defs : vdefs i = []
  uses : vuseNums i = v :: amVregs am

theorem regs_nil_visit {am : AMode} (h : am.regs = []) {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : OpSpec → Reg → m Reg) : AMode.visit f am = pure am := by
  cases am <;> simp_all [AMode.regs, AMode.visit]

theorem load_ops (op : LoadOp) (d : Nat) {am : AMode} (h : AmVregs am) (fl : Clif.MemFlags) :
    DefAmOps (.load op (.vreg d .int) am fl) d am := by
  rcases am_operands_cases h with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, e, rfl⟩ | ⟨a, b, e, rfl⟩ |
    ⟨a, i, rfl⟩ | ⟨a, i, rfl⟩ | ⟨a, i, rfl⟩ | hnil
  all_goals first
    | exact ⟨⟨_, rfl, fun ρ => rfl, rfl, fun ρ x => rfl⟩, rfl, rfl⟩
    | (cases am <;> simp [AMode.regs] at hnil <;>
        exact ⟨⟨_, rfl, fun ρ => rfl, rfl, fun ρ x => rfl⟩, rfl, rfl⟩)

theorem store_ops (op : StoreOp) (v : Nat) {am : AMode} (h : AmVregs am) (fl : Clif.MemFlags) :
    StoreAmOps (.store op (.vreg v .int) am fl) v am := by
  rcases am_operands_cases h with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, e, rfl⟩ | ⟨a, b, e, rfl⟩ |
    ⟨a, i, rfl⟩ | ⟨a, i, rfl⟩ | ⟨a, i, rfl⟩ | hnil
  all_goals first
    | exact ⟨⟨_, rfl, fun ρ => rfl, rfl, fun ρ => rfl⟩, rfl, rfl⟩
    | (cases am <;> simp [AMode.regs] at hnil <;>
        exact ⟨⟨_, rfl, fun ρ => rfl, rfl, fun ρ => rfl⟩, rfl, rfl⟩)

/-- One instruction under an arbitrary semantics fact (not only `ispec`). -/
theorem seqRun_isem_one {isem : Sem} {i : MInst} {ops : Array Operand}
    (hops : i.operands = .ok ops) {ρ : Nat → CV} {w w' : Arm.ArmState} {outs : List CV}
    (hs : isem i (vuses ops ρ) w = some (outs, w', .next))
    (hlen : outs.length = (ops.toList.filter Operand.isDef).length) :
    seqRun isem [i] ρ w = some (.fall (vdefUpd ops outs ρ) w') := by
  simp only [seqRun, hops, hs, hlen, ↓reduceIte, Option.map_some]
  rfl

theorem SameWorld.toNF {F : BitVec 64 → Prop} {s t : Arm.ArmState} (h : SameWorld F s t) :
    SameWorldNF F s t :=
  ⟨fun f hf _ => h.1 f hf, h.2.1, h.2.2⟩

theorem spOf_of_nf {F : BitVec 64 → Prop} {s t : Arm.ArmState} (h : SameWorldNF F s t) :
    spOf s = spOf t :=
  h.1 (.GPR 31#5) (by simp [Masked]) (fun fl e => by cases e)

/-- A 64-bit CLIF value held by a vreg: its low 64 bits. -/
theorem lo64_of_holds {pv : Clif.Val} {x : CV} (h : VHolds pv x) (ht : pv.ty = .i64) :
    lo64 x = BitVec.ofNat 64 pv.toNat := by
  obtain ⟨ty, bits⟩ := pv
  simp only at ht
  subst ht
  simp only [VHolds] at h
  simp only [lo64, Clif.Val.toNat]
  rw [← h]
  apply BitVec.eq_of_toNat_eq
  simp [Clif.Ty.width]

/-- `Runs` from a `PRun` (the latter holds from every world, with `SameWorld`). -/
theorem Runs.of_prun {F : BitVec 64 → Prop} {isem : Sem} {ms : List MInst} {ρ ρ' : Nat → CV}
    (h : PRun F isem ms ρ ρ') (w : Arm.ArmState) {P : (Nat → CV) → Arm.ArmState → Prop}
    (hP : ∀ w', SameWorld F w' w → P ρ' w') : Runs F isem ms ρ w P := by
  obtain ⟨w', hr, hw⟩ := h w
  exact ⟨ρ', w', hr, hw.toNF, hP w' hw⟩

end Backend.Proof
