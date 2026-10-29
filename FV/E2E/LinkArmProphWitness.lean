module

public import FV.E2E.LinkArmProph
public import FV.E2E.NonVacuityLink

@[expose] public section

/-!
# Witnesses for the prophecy-indexed call contract (`FV/E2E/LinkArmProph.lean`)

On `LinkWitness.L` (`FV/E2E/NonVacuityLink.lean`) without a code image (`L0`), a call of `f`
at depth `1` with a callee budget of 16 bytes, from the world `w0` with `sp = 0x8000`: the
callee's stack region contains `0x7FFF` and not `0x8000` (`rgn_in`, `rgn_out`).

* (a) the world's own bytes (and a prophecy equal to them only below `sp`) give `canon`,
  `progX`, `X` (`canonP_own`, `canonP_own_below`, `progXP_own`, `XP_own`);
* (b) the prophecy `0xAB` and one that is `0xAB` only below `sp`, from `w0` and from `w0` with
  `0x11` in the region, give the same canonical state and call (`canonP_ind`, `progXP_ind`);
* (c) the canonical state reads `0xAB` at `0x7FFF` and `canon`'s byte at `0x8000`, `Cond` and
  `CondP` (false at depth `0`) do not see the region inside `F`.
-/

namespace E2E.LinkArmProphWitness

open Backend Backend.Proof LinkWitness

/-- `LinkWitness.L` without a code image. -/
def L0 : LinkSys := { L (Img P A) with Img := fun _ => False }

/-- A callee budget of 16 bytes. -/
def κ16 : Nat → Clif.Function → Nat := fun _ _ => 16

/-- A world with `sp = 0x8000`. -/
def w0 : Arm.ArmState := Arm.w (.GPR 31#5) 0x8000#64 Arm.ArmState.default

theorem spv_w0 : spv w0 = 0x8000#64 := Arm.r_of_w_same

theorem rgn_in : L0.calleeRgn κ16 1 fF w0 0x7FFF#64 := by
  unfold LinkSys.calleeRgn StackBelow
  rw [spv_w0]
  have h1 : (0x7FFF#64).toNat = 32767 := rfl
  have h2 : (0x8000#64).toNat = 32768 := rfl
  rw [h1, h2]; simp only [κ16]; omega

theorem rgn_out : ¬ L0.calleeRgn κ16 1 fF w0 0x8000#64 := by
  unfold LinkSys.calleeRgn StackBelow
  rw [spv_w0]
  exact fun h => Nat.lt_irrefl _ h.1

theorem rgn_below {a : BitVec 64} (ha : L0.calleeRgn κ16 1 fF w0 a) : a.toNat < 0x8000 := by
  have h := ha.1
  rw [spv_w0] at h
  exact h

/-- The prophecy `0xAB`. -/
def PAB : BitVec 64 → BitVec 8 := fun _ => 0xAB#8

/-- `0xAB` below `0x8000`, `0` elsewhere. -/
def P2 : BitVec 64 → BitVec 8 := fun a => if a.toNat < 0x8000 then 0xAB#8 else 0#8

/-- `w0`'s bytes below `0x8000`, `0xAB` elsewhere. -/
def Pw : BitVec 64 → BitVec 8 := fun a => if a.toNat < 0x8000 then w0.mem a else 0xAB#8

/-- `w0` with `0x11` in the callee's region. -/
noncomputable def w1 : Arm.ArmState := overlay (L0.calleeRgn κ16 1 fF w0) (fun _ => 0x11#8) w0

theorem hr1 : ∀ f, Arm.r f w0 = Arm.r f w1 := fun f => (r_overlay f w0).symm
theorem hm1 : ∀ a, ¬ L0.calleeRgn κ16 1 fF w0 a → w0.mem a = w1.mem a :=
  fun _ ha => (mem_overlay_out ha).symm
theorem hP2 : ∀ a, L0.calleeRgn κ16 1 fF w0 a → PAB a = P2 a :=
  fun a ha => by simp only [PAB, P2, rgn_below ha, ↓reduceIte]

/-! ## Helpers -/

theorem state_eq_w0 : w0 = w0 := state_eq_of (fun _ => rfl) rfl fun _ => rfl

theorem r_w_w1 (f : Arm.StateField) : Arm.r f (Arm.w .PC 4#64 w0) = Arm.r f (Arm.w .PC 4#64 w1) :=
  r_w_congr hr1 .PC 4#64 f

theorem r_setReg_w1 (f : Arm.StateField) :
    Arm.r f (setReg w0 (.x 0) 7#128) = Arm.r f (setReg w1 (.x 0) 7#128) :=
  r_setReg_congr hr1 (.x 0) 7#128 f

theorem placeArgs_w1 (f : Arm.StateField) :
    Arm.r f (placeArgs [.x 0, .x 1] [7#128, 9#128] w0) =
      Arm.r f (placeArgs [.x 0, .x 1] [7#128, 9#128] w1) :=
  placeArgs_r_congr _ _ hr1 f

/-! ## (a) The world's own bytes -/

theorem worldP_own : L0.worldP κ16 1 fF w0.mem w0 = w0 := L0.worldP_self fun _ _ => rfl

theorem canonP_own : L0.canonP κ16 1 fF [7#128] w0.mem w0 = L0.canon fF [7#128] w0 :=
  L0.canonP_self _ fun _ _ => rfl

/-- A prophecy equal to `w0`'s bytes only below `sp`. -/
theorem canonP_own_below : L0.canonP κ16 1 fF [7#128] Pw w0 = L0.canon fF [7#128] w0 :=
  L0.canonP_self _ fun a ha => by simp only [Pw, rgn_below ha, ↓reduceIte]

theorem progXP_own (F : BitVec 64 → Prop) :
    L0.progXP κ16 1 F fF [7#128] w0.mem w0 = L0.progX κ16 1 F fF [7#128] w0 :=
  L0.progXP_self F _ fun _ _ => rfl

theorem progXP_eq_w0 (F : BitVec 64 → Prop) :
    L0.progXP κ16 1 F fF [7#128] PAB w0 = L0.progX κ16 1 F fF [7#128] (L0.worldP κ16 1 fF PAB w0) :=
  L0.progXP_eq F fF _ PAB w0 1

theorem XP_own (F : BitVec 64 → Prop) (d : Option String) :
    (L0.XP κ16 1 fF F (fun _ => w0.mem) 3).call d [7#128] w0 = (L0.X κ16 1 fF F).call d [7#128] w0 :=
  L0.XP_call_self fF F _ 3 d _ fun _ _ => rfl

theorem XP_sym_w0 (F : BitVec 64 → Prop) :
    (L0.XP κ16 1 fF F (fun _ => PAB) 3).sym = (L0.X κ16 1 fF F).sym ∧
      (L0.XP κ16 1 fF F (fun _ => PAB) 3).tp = (L0.X κ16 1 fF F).tp ∧
      (L0.XP κ16 1 fF F (fun _ => PAB) 3).tlsFlags = (L0.X κ16 1 fF F).tlsFlags :=
  L0.XP_sym_tp_tls fF F _ 3

theorem XP_f (F : BitVec 64 → Prop) :
    (L0.XP κ16 1 fF F (fun n _ => BitVec.ofNat 8 n) 3).call (some fF.name) [7#128] w0 =
      L0.progXP κ16 1 F fF [7#128] (fun _ => BitVec.ofNat 8 3) w0 :=
  L0.XP_prog (E2E.func?_of_mem (L_ok (Img P A) fun _ h => h).names (mem_P.2 (.inl rfl))) F _ 3 _ w0

/-! ## (b) The prophecy and the world -/

theorem worldP_ind : L0.worldP κ16 1 fF PAB w0 = L0.worldP κ16 1 fF P2 w1 :=
  L0.worldP_congr hr1 rfl hm1 hP2

theorem canonP_ind : L0.canonP κ16 1 fF [7#128] PAB w0 = L0.canonP κ16 1 fF [7#128] P2 w1 :=
  L0.canonP_congr _ hr1 rfl hm1 hP2

theorem condP_ind (F : BitVec 64 → Prop) :
    L0.CondP κ16 1 F fF [7#128] PAB w0 ↔ L0.CondP κ16 1 F fF [7#128] P2 w1 :=
  L0.condP_congr F _ hr1 rfl hm1 hP2

theorem progXP_ind (F : BitVec 64 → Prop) :
    L0.progXP κ16 1 F fF [7#128] PAB w0 = L0.progXP κ16 1 F fF [7#128] P2 w1 :=
  L0.progXP_congr F _ hr1 rfl hm1 hP2

/-! ## (c) Region facts -/

theorem mem_in : (L0.canonP κ16 1 fF [7#128] PAB w0).mem 0x7FFF#64 = 0xAB#8 :=
  L0.mem_canonP_in _ (fun h => h) rgn_in

theorem mem_out :
    (L0.canonP κ16 1 fF [7#128] PAB w0).mem 0x8000#64 = (L0.canon fF [7#128] w0).mem 0x8000#64 :=
  L0.mem_canonP_out _ rgn_out

theorem r_canonP_w0 (f : Arm.StateField) :
    Arm.r f (L0.canonP κ16 1 fF [7#128] PAB w0) = Arm.r f (L0.canon fF [7#128] w0) :=
  L0.r_canonP fF _ PAB w0 f

theorem program_canonP_w0 :
    (L0.canonP κ16 1 fF [7#128] PAB w0).program = (L0.canon fF [7#128] w0).program :=
  L0.program_canonP fF _ PAB w0

theorem canonP_overlay :
    L0.canonP κ16 1 fF [7#128] PAB w0 =
      overlay (L0.calleeRgn κ16 1 fF w0) PAB (L0.canon fF [7#128] w0) :=
  L0.canonP_eq_overlay _ fun _ _ h => h

theorem sameWorld_w0 :
    SameWorld (L0.calleeRgn κ16 1 fF w0) (L0.canon fF [7#128] w0) (L0.canonP κ16 1 fF [7#128] PAB w0) :=
  L0.sameWorld_canonP _ (fun _ ha => ⟨ha, fun h => h⟩) PAB

/-- `Cond` does not see the region inside `F`. -/
theorem cond_w1 :
    L0.Cond κ16 1 (L0.calleeRgn κ16 1 fF w0) fF [7#128] w0 ↔
      L0.Cond κ16 1 (L0.calleeRgn κ16 1 fF w0) fF [7#128] w1 :=
  L0.cond_congr hr1 hm1

/-- `CondP` is `Cond`: false at depth `0`. -/
theorem condP_zero (F : BitVec 64 → Prop) : ¬ L0.CondP κ16 0 F fF [7#128] PAB w0 :=
  fun h => Nat.lt_irrefl 0 (L0.condP_iff_cond.1 h).1

end E2E.LinkArmProphWitness
