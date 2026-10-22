import FV.E2E.DeadCleanupRegLevel
import FV.E2E.RegLevelAtomic
import FV.E2E.RegLevelTrapCall
import FV.E2E.MemTrapStatement
import FV.Backend.Proof.PrepareMemTrap

/-!
# The register level of a memory trap (A3, #412, slice F4)

`docs/plans/memfault.md`, "Backend layers". A memory trap of the VCode run (`VMemTrapFrom`: the
run reaches an LL/SC loop with the trap code `c`, its address use `u` and size `n` satisfying
`A`) is, on the machine, the state at the loop's first line, `ldaxr x27, [x25]`, whose trap-table
entry has the code `c` (`TrapAt`) and whose `x25` holds the address. When the address range has a
byte the memory map `mp` does not map (`Unmapped mp`), that `ldaxr` faults: **`TrapAtF mp`**.

* `haltLoop c A sem`: `sem`, except that a loop with code `c` whose address satisfies `A` halts
  (a proof device, as `xrT` for the trapping callees): a `VMemTrapFrom` run is a run of
  `haltLoop` up to a halting loop (`memTrap_halt`), and a realisation of `sem` is one of
  `haltLoop` (`realizes_haltLoop`; the machine is unchanged);
* `trapAt_ins`: a line with a trap code is a trap site; `faults_ldaxr`: the `ldaxr` of an address
  range with an unmapped byte faults;
* `rmwLoop_trapAtF`, `casLoopTrapAtF`: `Q` at a halting loop item is a `TrapAtF` state;
* **`regLevel_memtrap_core`**: the explicit traps (`TrapAt`) and the memory traps (`TrapAtF`) of
  the VCode run, for one initial store;
* `regLevel_memtrap_world_value`, `regLevel_memtrap_backend_value`: for the dead-cleanup chain's
  value semantics (with and without kept addresses).
-/

namespace Backend.Proof

open Backend E2E Backend.DeadCleanup Backend.Proof.Driver

/-! ## Unmapped address ranges -/

/-- Some byte of `[x, x + n)` is not mapped (`Perm.none`). -/
def Unmapped (mp : ArmFault.MemMap) (x : BitVec 64) (n : Nat) : Prop :=
  ∃ k < n, mp (x + BitVec.ofNat 64 k) = .none

/-- The CLIF-level unmapped range (`MapFaults`'s byte) is an `Unmapped` 64-bit range. -/
theorem unmapped_of_addrPred {mp : ArmFault.MemMap} {u : BitVec 64} {n : Nat}
    (h : addrPred (fun a n => ∃ k < n, mp (BitVec.ofNat 64 (a + k)) = .none) u n) :
    Unmapped mp u n := by
  obtain ⟨a, rfl, k, hk, hm⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [← hm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

/-! ## The halting loops -/

/-- An LL/SC loop with trap code `c` whose address use (the first use) and size satisfy `A`. -/
def HaltsAt (c : Clif.TrapCode) (A : BitVec 64 → Nat → Prop) (i : MInst) (uses : List CV) :
    Prop :=
  ∃ n u us, loopTrap? i = some (c, n) ∧ uses = u :: us ∧ A (lo64 u) n

/-- Zero values for the defs of `i`. -/
def haltOuts (i : MInst) : List CV :=
  match i.operands with
  | .ok ops => (ops.toList.filter Operand.isDef).map (fun _ => 0)
  | .error _ => []

open Classical in
/-- **The semantics with halting loops** (proof device): `sem`, except that a loop with code `c`
whose address satisfies `A` halts, the world unchanged. -/
noncomputable def haltLoop (c : Clif.TrapCode) (A : BitVec 64 → Nat → Prop) (sem : Sem) : Sem :=
  fun i uses w => if HaltsAt c A i uses then some (haltOuts i, w, .halt) else sem i uses w

theorem haltLoop_of_not {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop} {sem : Sem} {i : MInst}
    {uses : List CV} (h : ¬ HaltsAt c A i uses) : haltLoop c A sem i uses = sem i uses := by
  funext w
  simp [haltLoop, h]

theorem haltLoop_of {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop} {sem : Sem} {i : MInst}
    {uses : List CV} (h : HaltsAt c A i uses) (w : Arm.ArmState) :
    haltLoop c A sem i uses w = some (haltOuts i, w, .halt) := by
  simp [haltLoop, h]

theorem haltOuts_length {i : MInst} {ops : Array Operand} (h : i.operands = .ok ops) :
    (haltOuts i).length = (ops.toList.filter Operand.isDef).length := by
  simp [haltOuts, h]

/-- A run to a halting loop is a run of `haltLoop` to the first halting loop. -/
theorem star_haltLoop {vc : VCode} {sem : Sem} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop} :
    ∀ {x y : VConf CV Arm.ArmState}, Star (VStep vc sem) x y → ∀ {T : VState CV Arm.ArmState},
      y = .run T → (∃ vb i ops, vc.blocks[T.b]? = some vb ∧ vb.insts[T.k]? = some i ∧
        i.operands = .ok ops ∧ HaltsAt c A i (vuses ops T.ρ)) →
      ∃ Y : VState CV Arm.ArmState, Star (VStep vc (haltLoop c A sem)) x (.run Y) ∧
        ∃ vb i ops, vc.blocks[Y.b]? = some vb ∧ vb.insts[Y.k]? = some i ∧
          i.operands = .ok ops ∧ HaltsAt c A i (vuses ops Y.ρ) := by
  intro x y h
  induction h with
  | refl => intro T hT hh; subst hT; exact ⟨T, .refl _, hh⟩
  | step h1 _ ih =>
    intro T hT hh
    cases h1 with
    | @step b k ρ w vb i ops outs w' ctl c' hvb hi hops hsem hlen hn =>
      by_cases hx : HaltsAt c A i (vuses ops ρ)
      · exact ⟨⟨b, k, ρ, w⟩, .refl _, vb, i, ops, hvb, hi, hops, hx⟩
      · obtain ⟨Y, hY, hYh⟩ := ih hT hh
        have hs : haltLoop c A sem i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w =
            some (outs, w', ctl) := by
          rw [show (ops.toList.filter Operand.isUse).map (ρ ·.vreg) = vuses ops ρ from rfl,
            haltLoop_of_not hx]
          exact hsem
        exact ⟨Y, .step (VStep.step hvb hi hops hs hlen hn) hY, hYh⟩

/-- **A memory trap of the VCode run is a halt of `haltLoop`.** -/
theorem memTrap_halt {vc : VCode} {sem : Sem} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop}
    {vs : VState CV Arm.ArmState} (h : VMemTrapFrom vc sem vs c A) :
    ∃ b k ρ w vb i ops, Star (VStep vc (haltLoop c A sem)) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
      vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
      HaltsAt c A i (vuses ops ρ) ∧
      VStep vc (haltLoop c A sem) (.run ⟨b, k, ρ, w⟩) (.halt w) := by
  obtain ⟨b, k, ρ, w, vb, i, ops, u, us, n, hstar, hvb, hi, hops, hu, hlt, hA⟩ := h
  obtain ⟨⟨b', k', ρ', w'⟩, hY, vb', i', ops', hvb', hi', hops', hh⟩ :=
    star_haltLoop hstar rfl ⟨vb, i, ops, hvb, hi, hops, n, u, us, hlt, hu, hA⟩
  refine ⟨b', k', ρ', w', vb', i', ops', hY, hvb', hi', hops', hh, ?_⟩
  exact VStep.step hvb' hi' hops' (haltLoop_of hh w') (haltOuts_length hops') VNext.halt

/-- **A realisation of `sem` is one of `haltLoop c A sem`**: off the halting loops they agree;
at a halting loop the allocated code halts (the machine is unchanged). -/
theorem realizes_haltLoop {R : RL} {sem₀ : Sem} {c : Clif.TrapCode} {A : BitVec 64 → Nat → Prop}
    (hreal : Realizes R.vc R.rf sem₀ ckeep R.step (fun s c => Q R s c ∧ AInv R c) R.GoodX) :
    Realizes R.vc R.rf (haltLoop c A sem₀) ckeep R.step (fun s c => Q R s c ∧ AInv R c)
      R.GoodX := by
  intro s c0 c' hq hm
  cases hm with
  | move =>
    obtain ⟨n, c'', hm'', hq'', ht⟩ := hreal s _ _ hq .move
    exact ⟨n, c'', mstep_congr hm'' fun _ _ _ _ _ _ _ _ _ hc => by cases hc, hq'', ht⟩
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsem hlen hho hcl hn =>
    have hstep : MStep R.vc (haltLoop c A sem₀) ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    by_cases hh : HaltsAt c A i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2))
    · rw [haltLoop_of hh] at hsem
      simp only [Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, -, rfl⟩ := hsem
      cases hn with
      | halt => exact ⟨0, _, hstep, ⟨trivial, trivial⟩, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · rw [haltLoop_of_not hh] at hsem
      obtain ⟨n, c'', hm'', hq'', ht⟩ := hreal s _ _ hq (MStep.op hvb hi hops hsz hsem hlen hho hcl hn)
      refine ⟨n, c'', mstep_congr hm'' fun b' k' allocs' its' m' w'' vb' i' ops' hc hvb' hi' hops' => ?_,
        hq'', ht⟩
      cases hc
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      rw [hops] at hops'; cases hops'
      exact (haltLoop_of_not hh).symm

/-! ## The machine at a halting loop -/

/-- **A line with a trap code is a trap site** (`trapAt_line` for any instruction). -/
theorem trapAt_ins {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {x : Insn}
    {code : Clif.TrapCode} (hj : R.L[j]? = some (.ins x (some code))) (hpc : Arm.r .PC s = R.pcOf j)
    (herr : Arm.r .ERR s = .None) : TrapAt R.fb R.base code s := by
  refine ⟨herr, ⟨lineOffset R.L j, code⟩, ?_, rfl, hpc⟩
  exact ((FnAsm.layout_traps hR.layout).2 _).mpr ⟨j, _, hj, rfl⟩

/-- The machine at an instruction line decodes the line's instruction. -/
theorem decodeAt_line {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {x : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins x t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    ∃ a, x.toArmInst ⟨lineOffset R.fa.lines.toList j, (R.lm[·]?)⟩ = .ok a ∧
      Concurrency.ArmFoot.decodeAt s = some a := by
  obtain ⟨h4, w, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
  have hfetch : Arm.fetch_inst (Arm.r .PC s) s = some w := by
    rw [fetch_inst_from_program, hprog, hpc]
    have := FnBin.program_find (base := R.base)
      (by have := (FnAsm.layout_size hR.layout).1; have := hR.fit; omega) hk
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4)] at this
  obtain ⟨a, ha, hd⟩ := Insn.decode_encode hw
  refine ⟨a, ha, ?_⟩
  simp only [Concurrency.ArmFoot.decodeAt, hfetch, hd]

/-- **The `ldaxr` of a range with an unmapped byte faults.** -/
theorem faults_ldaxr {mp : ArmFault.MemMap} {s : Arm.ArmState} {bits : Nat} {env : Env}
    {a : Arm.ArmInst} (hbits : bits = 8 ∨ bits = 16 ∨ bits = 32 ∨ bits = 64)
    (ha : (Insn.ldaxr bits (.x 27) (.x 25)).toArmInst env = .ok a)
    (hd : Concurrency.ArmFoot.decodeAt s = some a) (herr : Arm.r .ERR s = .None)
    (hu : Unmapped mp (Arm.r (.GPR 25#5) s) (bits / 8)) : ArmFault.Faults mp s := by
  obtain ⟨k, hk, hm⟩ := hu
  have hev : Concurrency.ArmInstFoot.stepEvs s = Concurrency.ArmInstFoot.instEvs a s := by
    simp only [Concurrency.ArmInstFoot.stepEvs, hd, show Arm.read_err s = .None from herr, ite_true]
  rcases hbits with rfl | rfl | rfl | rfl <;>
  · simp [Insn.toArmInst, Insn.armFields, Insn.armFields.exclFields, Reg.encSP, Reg.encZR,
      Functor.map, Except.map, bind, Except.bind, pure, Except.pure] at ha
    subst ha
    refine ArmFault.faults_of_byte (e := ⟨_, Arm.read_gpr 64 25#5 s, bits / 8, _⟩) ?_ hk ?_
    all_goals exact sorry

end Backend.Proof
