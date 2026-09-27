import FV.Backend.Proof.IselSemCmp

/-!
# Straight-line runs of emitted code (flags/select/div family)

Composition lemmas for `seqRun` (append, one instruction through `Refines`), the frame
property (a run changes only the vregs its instructions define), the fresh-code invariant
`Frag` (what a term emitted between two lowering states, with fresh defs), and the world
relation `SameWorldNF` (reflexive, transitive, implied by `SameWorld` and by a flag write).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-! ## Worlds -/

theorem SameWorldNF.refl (F : BitVec 64 → Prop) (s : Arm.ArmState) : SameWorldNF F s s :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem SameWorldNF.trans {F : BitVec 64 → Prop} {a b c : Arm.ArmState} (h1 : SameWorldNF F a b)
    (h2 : SameWorldNF F b c) : SameWorldNF F a c :=
  ⟨fun f hf hfl => (h1.1 f hf hfl).trans (h2.1 f hf hfl), fun x hx => (h1.2.1 x hx).trans (h2.2.1 x hx),
    h1.2.2.trans h2.2.2⟩

theorem SameWorldNF.write_pstate (F : BitVec 64 → Prop) (ps : Arm.PState) (s : Arm.ArmState) :
    SameWorldNF F (Arm.write_pstate ps s) s := by
  refine ⟨fun f _ hfl => ?_, fun a _ => ?_, ?_⟩
  · simp only [Arm.write_pstate]
    rw [Arm.r_of_w_different (hfl _), Arm.r_of_w_different (hfl _),
      Arm.r_of_w_different (hfl _), Arm.r_of_w_different (hfl _)]
  · simp only [Arm.write_pstate, Arm.ArmState.mem_w_eq_mem]
  · simp only [Arm.write_pstate, Arm.w_program]

/-- `ConditionHolds` only reads the flags, which `SameWorld` preserves. -/
theorem SameWorld.conditionHolds {F : BitVec 64 → Prop} {s t : Arm.ArmState} (h : SameWorld F s t)
    (c : BitVec 4) : Arm.ConditionHolds c s = Arm.ConditionHolds c t := by
  have hf : ∀ fl, Arm.r (.FLAG fl) s = Arm.r (.FLAG fl) t := fun fl => h.1 _ (by simp [Masked])
  simp only [Arm.ConditionHolds, Arm.read_flag, hf]
  rfl

/-! ## `seqRun` composition -/

section
variable {V W : Type} (sem : ISem V W)

/-- `SeqEnd.succ` iterated `n` times. -/
def SeqEnd.shift (n : Nat) : SeqEnd V W → SeqEnd V W
  | .fall ρ w => .fall ρ w
  | .stop k i ops ρ w outs w' ctl => .stop (k + n) i ops ρ w outs w' ctl

theorem SeqEnd.succ_shift (n : Nat) (e : SeqEnd V W) : SeqEnd.succ (e.shift n) = e.shift (n + 1) := by
  cases e <;> simp [SeqEnd.shift, SeqEnd.succ, Nat.add_assoc]

theorem seqRun_append_fall {ms1 ms2 : List MInst} {ρ ρ1 : Nat → V} {w w1 : W}
    (h : seqRun sem ms1 ρ w = some (.fall ρ1 w1)) :
    seqRun sem (ms1 ++ ms2) ρ w = (seqRun sem ms2 ρ1 w1).map (SeqEnd.shift ms1.length) := by
  induction ms1 generalizing ρ w with
  | nil =>
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.nil_append, List.length_nil]
    cases seqRun sem ms2 ρ w with
    | none => rfl
    | some e => cases e <;> rfl
  | cons i ms ih =>
    simp only [List.cons_append, seqRun, List.length_cons] at h ⊢
    split at h
    · cases h
    · rename_i ops hops
      split at h
      · cases h
      · rename_i outs w' ctl hs
        split at h
        · rename_i hlen
          simp only [hlen, ↓reduceIte]
          split at h
          · cases hr : seqRun sem ms (vdefUpd ops outs ρ) w' with
            | none => rw [hr] at h; cases h
            | some e =>
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq] at h
              cases e with
              | fall ρ2 w2 =>
                cases h
                rw [ih hr]
                cases seqRun sem ms2 ρ1 w1 with
                | none => rfl
                | some e' => simp only [Option.map_some, SeqEnd.succ_shift]
              | stop k' i' ops' ρ' w'' outs'' w''' ctl'' => cases h
          · cases h
        · cases h

theorem seqRun_append_stop {ms1 ms2 : List MInst} {ρ : Nat → V} {w : W} {k : Nat} {i : MInst}
    {ops : Array Operand} {ρ1 : Nat → V} {w1 : W} {outs : List V} {w2 : W} {ctl : Ctl}
    (h : seqRun sem ms1 ρ w = some (.stop k i ops ρ1 w1 outs w2 ctl)) :
    seqRun sem (ms1 ++ ms2) ρ w = some (.stop k i ops ρ1 w1 outs w2 ctl) := by
  induction ms1 generalizing ρ w k with
  | nil => simp [seqRun] at h
  | cons j ms ih =>
    simp only [List.cons_append, seqRun] at h ⊢
    split at h
    · cases h
    · rename_i ops' hops
      split at h
      · cases h
      · rename_i outs' w' ctl' hs
        split at h
        · rename_i hlen
          simp only [hlen, ↓reduceIte]
          split at h
          · cases hr : seqRun sem ms (vdefUpd ops' outs' ρ) w' with
            | none => rw [hr] at h; cases h
            | some e =>
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq] at h
              cases e with
              | fall ρ' w'' => cases h
              | stop k' i' ops'' ρ' w'' outs'' w''' ctl'' =>
                simp only [SeqEnd.succ, SeqEnd.stop.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
                rw [ih hr]
                rfl
          · exact h
        · cases h

/-- Running a straight-line prefix that falls through, then the rest. -/
theorem seqRun_append_fall' {ms1 ms2 : List MInst} {ρ ρ1 ρ2 : Nat → V} {w w1 w2 : W}
    (h1 : seqRun sem ms1 ρ w = some (.fall ρ1 w1)) (h2 : seqRun sem ms2 ρ1 w1 = some (.fall ρ2 w2)) :
    seqRun sem (ms1 ++ ms2) ρ w = some (.fall ρ2 w2) := by
  rw [seqRun_append_fall sem h1, h2, Option.map_some]; rfl

/-- A prefix that falls through, then a suffix that stops. -/
theorem seqRun_append_fall_stop {ms1 ms2 : List MInst} {ρ ρ1 : Nat → V} {w w1 : W} {k : Nat}
    {i : MInst} {ops : Array Operand} {ρ2 : Nat → V} {w2 : W} {outs : List V} {w3 : W} {ctl : Ctl}
    (h1 : seqRun sem ms1 ρ w = some (.fall ρ1 w1))
    (h2 : seqRun sem ms2 ρ1 w1 = some (.stop k i ops ρ2 w2 outs w3 ctl)) :
    seqRun sem (ms1 ++ ms2) ρ w = some (.stop (k + ms1.length) i ops ρ2 w2 outs w3 ctl) := by
  rw [seqRun_append_fall sem h1, h2, Option.map_some]; rfl

end

/-! ## One instruction under `Refines` -/

theorem seqRun_one_next {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {i : MInst}
    {ops : Array Operand} (hops : i.operands = .ok ops) {ρ : Nat → CV} {w w' : Arm.ArmState}
    {outs : List CV} (hs : ispec i (vuses ops ρ) w = some (outs, w', .next))
    (hlen : outs.length = (ops.toList.filter Operand.isDef).length) :
    ∃ w'', seqRun isem [i] ρ w = some (.fall (vdefUpd ops outs ρ) w'') ∧ SameWorld F w'' w' := by
  obtain ⟨w'', hi, hw⟩ := hR _ _ _ _ _ hs
  refine ⟨w'', ?_, hw⟩
  simp only [seqRun, hops, hi, hlen, ↓reduceIte, Option.map_some]
  rfl

theorem seqRun_one_halt {F : BitVec 64 → Prop} {isem : Sem} (hR : Refines F isem) {i : MInst}
    {ops : Array Operand} (hops : i.operands = .ok ops) {ρ : Nat → CV} {w w' : Arm.ArmState}
    {outs : List CV} (hs : ispec i (vuses ops ρ) w = some (outs, w', .halt))
    (hlen : outs.length = (ops.toList.filter Operand.isDef).length) :
    ∃ w'', seqRun isem [i] ρ w = some (.stop 0 i ops ρ w outs w'' .halt) := by
  obtain ⟨w'', hi, -⟩ := hR _ _ _ _ _ hs
  refine ⟨w'', ?_⟩
  simp only [seqRun, hops, hi, hlen, ↓reduceIte]

/-! ## The frame property -/

theorem writeV_not_mem {V : Type} (ρ : Nat → V) (dv : List (Operand × V)) (z : Nat)
    (hz : ∀ p ∈ dv, p.1.vreg ≠ z) : writeV ρ dv z = ρ z := by
  induction dv generalizing ρ with
  | nil => rfl
  | cons p dv ih =>
    simp only [writeV, List.foldl_cons] at ih ⊢
    rw [ih _ (fun q hq => hz q (List.mem_cons_of_mem _ hq))]
    simp only [upd]
    rw [if_neg (Ne.symm (hz p (List.mem_cons_self ..)))]

theorem vdefUpd_not_mem {V : Type} (ops : Array Operand) (outs : List V) (ρ : Nat → V) (z : Nat)
    (hz : z ∉ (ops.toList.filter Operand.isDef).map (·.vreg)) : vdefUpd ops outs ρ z = ρ z := by
  have hz' : ∀ p ∈ (ops.toList.filter Operand.isDef).zip outs, p.1.vreg ≠ z := by
    intro p hp heq
    apply hz
    rw [List.mem_map]
    exact ⟨p.1, (List.of_mem_zip hp).1, heq⟩
  unfold vdefUpd
  rw [writeV_not_mem _ _ _ (fun p hp => hz' p (List.mem_filter.1 hp).1),
    writeV_not_mem _ _ _ (fun p hp => hz' p (List.mem_filter.1 hp).1)]

theorem seqRun_frame {V W : Type} (sem : ISem V W) :
    ∀ {ms : List MInst} {ρ ρ' : Nat → V} {w w' : W}, seqRun sem ms ρ w = some (.fall ρ' w') →
      ∀ z, (∀ m ∈ ms, z ∉ vdefs m) → ρ' z = ρ z
  | [], ρ, ρ', w, w', h, z, _ => by
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h
    rw [h.1]
  | i :: ms, ρ, ρ', w, w', h, z, hz => by
    simp only [seqRun] at h
    split at h
    · cases h
    · rename_i ops hops
      split at h
      · cases h
      · rename_i outs w1 ctl hs
        split at h
        · split at h
          · cases hr : seqRun sem ms (vdefUpd ops outs ρ) w1 with
            | none => rw [hr] at h; cases h
            | some e =>
              rw [hr] at h
              cases e with
              | fall ρ2 w2 =>
                simp only [Option.map_some, Option.some.injEq] at h
                cases h
                rw [seqRun_frame sem hr z (fun m hm => hz m (List.mem_cons_of_mem _ hm))]
                apply vdefUpd_not_mem
                have := hz i (List.mem_cons_self ..)
                simpa [vdefs, hops] using this
              | stop k' i' ops' ρ3 w3 outs3 w4 ctl3 => simp [SeqEnd.succ] at h
          · cases h
        · cases h

/-! ## Emitted code with fresh defs -/

/-- What a term appended between lowering states `st` and `st'`: `ms`, whose defs are fresh. -/
structure Frag (st st' : LState) (ms : List MInst) : Prop where
  emitted : st'.emitted = st.emitted ++ ms.toArray
  mono : st.nextVreg ≤ st'.nextVreg
  defs : ∀ m ∈ ms, ∀ d ∈ vdefs m, st.nextVreg ≤ d ∧ d < st'.nextVreg

theorem Frag.nil (st : LState) : Frag st st [] := ⟨by simp, Nat.le_refl _, by simp⟩

theorem Frag.append {st st1 st2 : LState} {ms1 ms2 : List MInst} (h1 : Frag st st1 ms1)
    (h2 : Frag st1 st2 ms2) : Frag st st2 (ms1 ++ ms2) :=
  ⟨by rw [h2.emitted, h1.emitted]; simp [Array.append_assoc], Nat.le_trans h1.mono h2.mono,
    fun m hm d hd => by
      rcases List.mem_append.1 hm with hm | hm
      · have := h1.defs m hm d hd; exact ⟨this.1, Nat.lt_of_lt_of_le this.2 h2.mono⟩
      · have := h2.defs m hm d hd; exact ⟨Nat.le_trans h1.mono this.1, this.2⟩⟩

/-- Vregs below the start state are unchanged by the run of a fragment. -/
theorem Frag.frame {V W : Type} {sem : ISem V W} {st st' : LState} {ms : List MInst}
    (hf : Frag st st' ms) {ρ ρ' : Nat → V} {w w' : W} (h : seqRun sem ms ρ w = some (.fall ρ' w'))
    {z : Nat} (hz : z < st.nextVreg) : ρ' z = ρ z :=
  seqRun_frame sem h z fun m hm hd => by have := hf.defs m hm z hd; omega

theorem UsesOk.append {st st1 : LState} {fr : Clif.Frame} {ms1 ms2 : List MInst}
    (hle : st.nextVreg ≤ st1.nextVreg) (h1 : UsesOk st fr ms1) (h2 : UsesOk st1 fr ms2) :
    UsesOk st fr (ms1 ++ ms2) := by
  intro m hm u hu
  rcases List.mem_append.1 hm with hm | hm
  · exact h1 m hm u hu
  · rcases h2 m hm u hu with h | h
    · exact .inl (Nat.le_trans hle h)
    · exact .inr h

end Backend.Proof
