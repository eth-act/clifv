import FV.E2E.DeadCleanupPair
import FV.E2E.DeadCleanupGuardedFP

/-! # Non-vacuity of the guarded lockstep with the float accesses (S11e5, Stage C slice 4)

Concrete instances of the semantic bridge and of the lockstep:

* `csem_fpuLoad_err`: on a world with an error (where `csem` falls back to `mspec`), `csem` of
  `ldr d0, [sp]` is now defined (`mspec`'s float arms, `memRefinesFP_csem`).
* `csemGF_fpuLoad_lockstep_witness`: on every world `w` and the world `w'` that differs from it
  in the byte `b0 = sp + 16` (`Z = {b0}`), `csemGF` with the reads guarded by `¬ Z` runs
  `ldr d0, [sp]` on both worlds (`csemGF_fp`, `csem_fpuLoad`), `csemGF_sub` gives `csem`'s run, and
  `csemGF_lockstep2` gives the same outputs and worlds that agree outside `Z`; the same for the
  guarded value semantics (`valueSemGF_lockstep2`).
* `csemGF_fpuStore_lockstep_witness`: the same for `str d0, [sp]` (a write).
* `seqRun_ext`/`LowerInstOkP.sem_ext`, `csemG_csemGF`: the integer `csemG` run of an integer
  load lifts to `csemGF`.

The composition theorems (`lowerInstOk_pair_of`, `lowerInstOk_pairF`, `lowerTryOk_pair_of`,
`lowerTryOk_pairF`, `lowerInstOk_pairF_value`) are instantiated with the lowering's own contracts
by `instCalls_pair_viaF`, `tryCalls_pair_viaF`, `tryIndCalls_pair_viaF` and
`instCalls_pair_value_viaF` (the statements of `instCalls_pair`, `tryCalls_pair`,
`tryIndCalls_pair`, `instCalls_pair_value`).
-/

namespace E2E.GuardedFPWitness
open Backend Backend.Proof

/-- An external semantics without callees, constant TLS flags. -/
def xNone' : ExtSem := ⟨fun _ _ _ => none, fun _ _ => 0, 0, fun _ _ => Arm.PState.zero⟩

def fl0 : Clif.MemFlags := default

/-- `ldr d0, [sp]` into float vreg 0. -/
def ldD : MInst := .fpuLoad .size64 (.vreg 0 .float) (.spOffset 0) fl0

/-- `str d0, [sp]` of float vreg 0. -/
def stD : MInst := .fpuStore .size64 (.vreg 0 .float) (.spOffset 0) fl0

theorem off_ne (s : BitVec 64) {k : Nat} (hk : k < 8) :
    s + BitVec.ofInt 64 0 + BitVec.ofNat 64 k ≠ s + 16#64 := by
  intro h
  have h2 : BitVec.ofNat 64 k = 16#64 := by
    have := congrArg (· - s) h
    simpa [BitVec.add_comm s] using this
  have h3 := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat] at h3
  omega

/-- On a world with an error, `csem` of a float load is defined: `mspec`'s float arm (before
S11e5 `csem` was undefined there). -/
theorem csem_fpuLoad_err (F : BitVec 64 → Prop) (ctx : FnCtx) (w : Arm.ArmState)
    (herr : Arm.r .ERR w ≠ .None) :
    csem F ctx xNone' ldD [] w =
      some ([(Arm.read_mem_bytes 8 (spOf w + BitVec.ofInt 64 0) w).setWidth 128], w, .next) := by
  rw [csem_straight rfl, if_neg (fun h => herr h.2.1)]
  simp [mspec, ldD, amodeAddr]
  rfl

section
variable (ctx : FnCtx) (w : Arm.ArmState) (v : BitVec 8)

/-- The byte where the two worlds differ. -/
def b0 : BitVec 64 := spOf w + 16#64

/-- The second world: `w` with the byte `b0` changed. -/
def w2 : Arm.ArmState := Arm.write_mem_bytes 1 (b0 w) (v.cast (by omega)) w

theorem sameWorld_w2 : SameWorld (fun b => b = b0 w) w (w2 w v) :=
  (SameWorld.write_mem_bytes_inF (SameWorld.refl _ w) 1 (b0 w) _ fun k hk => by
    have : k = 0 := by omega
    subst this
    simp).symm

/-- The guarded semantics of the witness (no frame, reads guarded by `¬ Z`, no calls). -/
noncomputable abbrev semW : Sem :=
  csemGF (fun _ => False) ctx xNone' (fun b => ¬ b = b0 w) (fun _ => none) [] [] 0
    (fun _ _ _ _ => False)

theorem guard_ldD {x : Arm.ArmState} (hx : SameWorld (fun b => b = b0 w) w x) :
    GuardFP (fun _ => False) (fun b => ¬ b = b0 w) ctx.slotBase ldD [] x := by
  have hsp : spOf w = spOf x := hx.1 (.GPR 31#5) (by simp [Masked])
  refine ⟨.inr rfl, _, rfl, fun _ _ h => h, fun k hk => ?_⟩
  show ¬ _ = spOf w + 16#64
  rw [hsp]
  exact off_ne _ hk

theorem defined_ldD {x : Arm.ArmState} (hx : SameWorld (fun b => b = b0 w) w x) :
    ∃ x₁, semW ctx w ldD [] x =
      some ([(Arm.read_mem_bytes 8 (spOf x + BitVec.ofInt 64 0) x).setWidth 128], x₁, .next) := by
  have hg := guard_ldD ctx w hx
  obtain ⟨x₁, h, -⟩ := csem_fpuLoad (fun _ => False) ctx xNone' .size64 (.inr rfl) 0 (.spOffset 0)
    fl0 [] x _ rfl (fun _ _ h => h)
  refine ⟨x₁, ?_⟩
  unfold semW ldD
  unfold ldD at hg
  rw [csemGF_fp (.inl ⟨_, _, _, _, rfl⟩), if_pos hg]
  exact h

/-- **Non-vacuity of `csemGF_lockstep2` on a float load**: both runs are defined, they are
`csem`'s, and they give the same outputs, worlds agreeing outside `Z = {b0}`. -/
theorem csemGF_fpuLoad_lockstep_witness :
    ∃ o w₁ w₁', semW ctx w ldD [] w = some (o, w₁, .next) ∧
      semW ctx w ldD [] (w2 w v) = some (o, w₁', .next) ∧
      csem (fun _ => False) ctx xNone' ldD [] w = some (o, w₁, .next) ∧
      SameWorld (fun b => b = b0 w) w₁ w₁' := by
  have hsw := sameWorld_w2 w v
  obtain ⟨w₁, h1⟩ := defined_ldD ctx w (SameWorld.refl _ w)
  obtain ⟨w₁', h2⟩ := defined_ldD ctx w hsw
  obtain ⟨ho, -, hs⟩ := csemGF_lockstep2 (fun _ h => h.elim) hsw
    (fun _ h1 => by obtain ⟨_, _, _, _, _, hf, _⟩ := h1; exact hf.elim) (fun _ => rfl) h1 h2
  refine ⟨_, w₁, w₁', h1, ?_, csemGF_sub h1, hs⟩
  rw [h2, ← ho]

/-- **Non-vacuity of `valueSemGF_lockstep2` on a float load.** -/
theorem valueSemGF_fpuLoad_lockstep_witness :
    ∃ o w₁ w₁',
      valueSemGF (fun _ => False) ctx xNone' (fun b => ¬ b = b0 w) (fun _ => none) [] [] 0
        (fun _ _ _ _ => False) ldD [] w = some (o, w₁, .next) ∧
      valueSemGF (fun _ => False) ctx xNone' (fun b => ¬ b = b0 w) (fun _ => none) [] [] 0
        (fun _ _ _ _ => False) ldD [] (w2 w v) = some (o, w₁', .next) ∧
      SameWorld (fun b => b = b0 w) w₁ w₁' := by
  obtain ⟨o, w₁, w₁', h1, h2, -, hs⟩ := csemGF_fpuLoad_lockstep_witness ctx w v
  have e : ∀ x, valueSemGF (fun _ => False) ctx xNone' (fun b => ¬ b = b0 w) (fun _ => none) [] []
      0 (fun _ _ _ _ => False) ldD [] x = semW ctx w ldD [] x := fun x => rfl
  have h1' : valueSemGF (fun _ => False) ctx xNone' (fun b => ¬ b = b0 w) (fun _ => none) [] [] 0
      (fun _ _ _ _ => False) ldD [] w = some (o, w₁, .next) := by rw [e]; exact h1
  have h2' : valueSemGF (fun _ => False) ctx xNone' (fun b => ¬ b = b0 w) (fun _ => none) [] [] 0
      (fun _ _ _ _ => False) ldD [] (w2 w v) = some (o, w₁', .next) := by rw [e]; exact h2
  refine ⟨o, w₁, w₁', h1', h2', ?_⟩
  obtain ⟨-, -, hs'⟩ := valueSemGF_lockstep2 (fun _ h => False.elim h) (sameWorld_w2 w v)
    (fun _ h1 => by obtain ⟨_, _, _, _, _, hf, _⟩ := h1; exact False.elim hf) (fun _ => rfl) h1' h2'
  exact hs'

/-- **Non-vacuity of `csemGF_lockstep2` on a float store**: the store of `u` through
`str d0, [sp]` is defined on both worlds, and the results agree outside `Z = {b0}`. -/
theorem csemGF_fpuStore_lockstep_witness (u : CV) :
    ∃ w₁ w₁', semW ctx w stD [u] w = some ([], w₁, .next) ∧
      semW ctx w stD [u] (w2 w v) = some ([], w₁', .next) ∧
      SameWorld (fun b => b = b0 w) w₁ w₁' := by
  have hsw := sameWorld_w2 w v
  have def_st : ∀ x, SameWorld (fun b => b = b0 w) w x →
      ∃ x₁, semW ctx w stD [u] x = some ([], x₁, .next) := fun x hx => by
    have hg : GuardFP (fun _ => False) (fun b => ¬ b = b0 w) ctx.slotBase stD [u] x :=
      ⟨.inr rfl, _, rfl, fun _ _ h => h⟩
    obtain ⟨x₁, h, -⟩ := csem_fpuStore (fun _ => False) ctx xNone' .size64 (.inr rfl) 0
      (.spOffset 0) fl0 u [] x _ rfl (fun _ _ h => h)
    unfold stD at hg
    exact ⟨x₁, by unfold semW stD; rw [csemGF_fp (.inr ⟨_, _, _, _, rfl⟩), if_pos hg]; exact h⟩
  obtain ⟨w₁, h1⟩ := def_st w (SameWorld.refl _ w)
  obtain ⟨w₁', h2⟩ := def_st _ hsw
  obtain ⟨-, -, hs⟩ := csemGF_lockstep2 (fun _ h => h.elim) hsw
    (fun _ h1 => by obtain ⟨_, _, _, _, _, hf, _⟩ := h1; exact hf.elim) (fun _ => rfl) h1 h2
  exact ⟨w₁, w₁', h1, h2, hs⟩

end

/-- **Non-vacuity of the extension lemmas** (`csemG_csemGF`, `seqRun_ext`): an integer load
`ldr x0, [sp]` run by `csemG` (reads unguarded) is a `csemGF` run, with the same result, also as
a one-instruction straight-line run. -/
theorem csemG_csemGF_witness (ctx : FnCtx) (w : Arm.ArmState) :
    ∃ e, seqRun (csemG (fun _ => False) ctx xNone' (fun _ => True) (fun _ => none) [] [] 0
        (fun _ _ _ _ => False)) [.load .uload64 (.vreg 0 .int) (.spOffset 0) fl0] (fun _ => 0) w =
        some e ∧
      seqRun (csemGF (fun _ => False) ctx xNone' (fun _ => True) (fun _ => none) [] [] 0
        (fun _ _ _ _ => False)) [.load .uload64 (.vreg 0 .int) (.spOffset 0) fl0] (fun _ => 0) w =
        some e := by
  obtain ⟨w', h, -⟩ := (memRefinesR_csemG (F := fun _ => False) (ctx := ctx) (X := xNone')
    (Rd := fun _ => True) (exts := []) (sigs := []) (sp0 := 0) (Pc := fun _ _ _ _ => False)
    (syms := fun _ => none) rfl (fun _ _ h => by cases h)).1 .uload64 0 (.spOffset 0) fl0 []
    w _ (by decide) rfl (fun _ _ h => h) (fun _ _ => trivial)
  have hops : (MInst.load .uload64 (.vreg 0 .int) (.spOffset 0) fl0).operands =
      .ok #[⟨0, .int, .def, .late, .reg⟩] := rfl
  have hv : vuses #[(⟨0, .int, .def, .late, .reg⟩ : Operand)] (fun _ => (0 : CV)) = [] := rfl
  have hs : ∃ e, seqRun (csemG (fun _ => False) ctx xNone' (fun _ => True) (fun _ => none) [] [] 0
      (fun _ _ _ _ => False)) [.load .uload64 (.vreg 0 .int) (.spOffset 0) fl0] (fun _ => 0) w =
      some e := by
    simp only [seqRun, hops, hv, h]
    exact ⟨_, rfl⟩
  obtain ⟨e, he⟩ := hs
  exact ⟨e, he, seqRun_ext (fun _ _ _ _ h => csemG_csemGF h) _ _ _ _ he⟩

/-! The `…_viaF` theorems have exactly the statements of the theorems they re-derive through the
composition with the float accesses (which `vcode_ni`/`vcode_ni_value` consume). -/

example : type_of% @E2E.instCalls_pair = type_of% @E2E.instCalls_pair_viaF := rfl
example : type_of% @E2E.tryCalls_pair = type_of% @E2E.tryCalls_pair_viaF := rfl
example : type_of% @E2E.tryIndCalls_pair = type_of% @E2E.tryIndCalls_pair_viaF := rfl
example : type_of% @E2E.instCalls_pair_value = type_of% @E2E.instCalls_pair_value_viaF := rfl

end E2E.GuardedFPWitness
