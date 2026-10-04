import FV.E2E.Final

/-! # Calls through the GOT: the VCode run gives them their symbol's address

A call of a non-`colocated` extern `n` is lowered to `loadExtNameGot t n; call (reg t)` (the
`adrp`/`ldr :got:` pair, then `blr`): the call's target is the vreg `t`, which the VCode run sets
to `n`'s link-time address just before. M6's callee contract quantifies over every value of the
target register, so without this knowledge a GOT site constrains every function the target could
be. This file is the static analysis (`GotV`) and its soundness on VCode runs (`vReturns_gotV`,
`vTraps_gotV`): when every def of `t` is `loadExtNameGot t n` and every call through `t` follows
one in its block, every call through `t` of a run of `csem` has `n`'s address as its target, so
the run is one of `csemV (GotV vc)` (M6's semantics with the GOT sites pinned, `RL.sem`).
`gotB` decides `GotV` (`gotB_sound`); `gotOf` finds the GOT symbol of a target vreg.
-/

namespace E2E

open Backend Backend.Proof

/-- **The GOT analysis**: every def of the vreg `t` in `vc` is `loadExtNameGot t n`, and every
`call`/`try_call` through `t` follows a `loadExtNameGot t n` in its block. -/
def GotV (vc : VCode) (t : Nat) (n : String) : Prop :=
  (∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst) (ops : Array Operand), vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → i.operands = .ok ops →
    (∃ o ∈ ops.toList, o.isDef = true ∧ o.vreg = t) → i = .loadExtNameGot (.vreg t .int) n) ∧
  (∀ (b : Nat) (vb : VBlock) (k : Nat) (info : CallInfo), vc.blocks[b]? = some vb →
    (vb.insts[k]? = some (.call info) ∨ ∃ ti, vb.insts[k]? = some (.tryCall info ti)) →
    info.dest = .reg (.vreg t .int) →
    ∃ j < k, vb.insts[j]? = some (.loadExtNameGot (.vreg t .int) n))

/-- The invariant of a run: every vreg `t` with `GotV vc t n` set by a `loadExtNameGot t n`
earlier in the current block holds `n`'s address. -/
def GotInv (vc : VCode) (X : ExtSem) (s : VState CV Arm.ArmState) : Prop :=
  ∀ (t : Nat) (n : String) (vb : VBlock) (j : Nat), GotV vc t n → vc.blocks[s.b]? = some vb → j < s.k →
    vb.insts[j]? = some (.loadExtNameGot (.vreg t .int) n) → s.ρ t = ofX (X.sym n 0)

theorem gotInv_entry (vc : VCode) (X : ExtSem) (ρ : Nat → CV) (w : Arm.ArmState) :
    GotInv vc X ⟨0, 0, ρ, w⟩ :=
  fun _ _ _ _ _ _ hj => absurd hj (Nat.not_lt_zero _)

theorem writeV_ne {V : Type} : ∀ (dv : List (Operand × V)) (ρ : Nat → V) {t : Nat},
    (∀ p ∈ dv, p.1.vreg ≠ t) → writeV ρ dv t = ρ t
  | [], _, _, _ => rfl
  | p :: dv, ρ, t, h => by
    show writeV (upd ρ p.1.vreg p.2) dv t = ρ t
    rw [writeV_ne dv _ fun q hq => h q (List.mem_cons_of_mem _ hq)]
    simp [upd, Ne.symm (h p List.mem_cons_self)]

theorem mem_defs_zip {V : Type} {ops : List Operand} {outs : List V} {p : Operand × V}
    (h : p ∈ (ops.filter Operand.isDef).zip outs) : p.1 ∈ ops ∧ p.1.isDef = true := by
  have := (List.of_mem_zip h).1
  exact List.mem_filter.mp this

theorem lo64_ofX_got (x : BitVec 64) : lo64 (ofX x) = x := by
  simp only [lo64, ofX]
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

variable {vc : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}

/-- **One step**: from a state with the invariant, a `csem` step is a `csemV (GotV vc)` step and
keeps the invariant. -/
theorem gotInv_step {s : VState CV Arm.ArmState} {c' : VConf CV Arm.ArmState}
    (hI : GotInv vc X s) (h : VStep vc (csem F ctx X) (.run s) c') :
    VStep vc (csemV (GotV vc) F ctx X) (.run s) c' ∧ ∀ s', c' = .run s' → GotInv vc X s' := by
  cases h with
  | @step b k ρ w vb i ops outs w' ctl _ hvb hi hops hsem hlen hnext =>
  refine ⟨VStep.step hvb hi hops ?_ hlen hnext, ?_⟩
  · rw [csemV_eq]
    · exact hsem
    · intro info hinfo t n ops' hd hgv hops' hhead
      have hops'' : (MInst.call info).operands = .ok ops := by
        rcases hinfo with rfl | ⟨ti, rfl⟩
        · exact hops
        · rw [← operands_tryCall_call info ti]; exact hops
      rw [hops''] at hops'
      cases hops'
      obtain ⟨j, hjk, hj⟩ := hgv.2 b vb k info hvb
        (by rcases hinfo with rfl | ⟨ti, rfl⟩; exact .inl hi; exact .inr ⟨ti, hi⟩) hd
      have hv := hI t n vb j hgv hvb hjk hj
      cases hf : ops.toList.filter Operand.isUse with
      | nil => rw [hf] at hhead; cases hhead
      | cons o rest =>
        rw [hf] at hhead
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhead
        have hv' : ρ t = ofX (X.sym n 0) := hv
        simp [hhead, hv', lo64_ofX_got]
  · intro s' hc
    cases hnext with
    | goto _ _ _ =>
      cases hc
      intro _ _ _ _ _ _ hj
      exact absurd hj (Nat.not_lt_zero _)
    | ret _ => cases hc
    | halt => cases hc
    | next hk =>
      cases hc
      intro t n vb' j hgv hvb' hj hjinst
      rw [hvb] at hvb'
      cases hvb'
      by_cases hdef : ∃ o ∈ ops.toList, o.isDef = true ∧ o.vreg = t
      · -- the step is the `loadExtNameGot t n` itself
        have e := hgv.1 b vb k i ops hvb hi hops hdef
        subst e
        have ho : ops = #[⟨t, .int, .def, .late, .reg⟩] := by
          have : (MInst.loadExtNameGot (.vreg t .int) n).operands =
              .ok #[⟨t, .int, .def, .late, .reg⟩] := rfl
          rw [this] at hops
          cases hops
          rfl
        subst ho
        simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, -⟩ := hsem
        simp [writeV, upd, Operand.isDef, Operand.isEarly, Operand.isLate]
      · have hne : ∀ (L : List (Operand × CV)), (∀ p ∈ L, p.1 ∈ ops.toList ∧ p.1.isDef = true) →
            ∀ p ∈ L, p.1.vreg ≠ t := fun L hL p hp e => hdef ⟨p.1, (hL p hp).1, (hL p hp).2, e⟩
        simp only
        rw [writeV_ne _ _ (hne _ fun p hp => mem_defs_zip (List.mem_filter.mp hp).1),
          writeV_ne _ _ (hne _ fun p hp => mem_defs_zip (List.mem_filter.mp hp).1)]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | rfl
        · exact hI t n vb j hgv hvb hjk hjinst
        · rw [hi] at hjinst
          cases hjinst
          exact absurd ⟨⟨t, .int, .def, .late, .reg⟩, by
            have : (MInst.loadExtNameGot (.vreg t .int) n).operands =
                .ok #[⟨t, .int, .def, .late, .reg⟩] := rfl
            rw [this] at hops
            cases hops
            simp, rfl, rfl⟩ hdef

/-- **Runs**: a run of `csem` from a state with the invariant is a run of `csemV (GotV vc)`,
ending in a state with the invariant. -/
theorem gotInv_star {s s' : VState CV Arm.ArmState} (hI : GotInv vc X s)
    (h : Star (VStep vc (csem F ctx X)) (.run s) (.run s')) :
    Star (VStep vc (csemV (GotV vc) F ctx X)) (.run s) (.run s') ∧ GotInv vc X s' := by
  generalize ha : (VConf.run s : VConf CV Arm.ArmState) = a at h
  generalize hb : (VConf.run s' : VConf CV Arm.ArmState) = b at h
  induction h generalizing s with
  | refl => subst ha; cases hb; exact ⟨.refl _, hI⟩
  | @step a1 a2 a3 h1 h2 ih =>
    subst ha
    cases a2 with
    | run s2 =>
      obtain ⟨h1', hI2⟩ := gotInv_step hI h1
      obtain ⟨h2', hI'⟩ := ih (hI2 s2 rfl) rfl hb
      exact ⟨.step h1' h2', hI'⟩
    | ret vals w => subst hb; cases h2 with | step h _ => cases h
    | halt w => subst hb; cases h2 with | step h _ => cases h

/-- **A returning VCode run of `csem` is one of `csemV (GotV vc)`.** -/
theorem vReturns_gotV {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {us : List (Reg × Reg)}
    {vals : List CV} {w : Arm.ArmState} (h : VReturns vc (csem F ctx X) ρ₀ w₀ us vals w) :
    VReturns vc (csemV (GotV vc) F ctx X) ρ₀ w₀ us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  obtain ⟨hs', -⟩ := gotInv_star (gotInv_entry vc X ρ₀ w₀) hs
  exact ⟨b, k, ρ, w₁, vb, ops, outs, hs', hvb, hk, hops, hvals, by
    rw [csemV_eq fun info h => by rcases h with h | ⟨_, h⟩ <;> cases h]; exact hsem⟩

/-- **A trapping VCode run of `csem` is one of `csemV (GotV vc)`.** -/
theorem vTraps_gotV {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {c : Clif.TrapCode}
    (h : VTraps vc (csem F ctx X) ρ₀ w₀ c) : VTraps vc (csemV (GotV vc) F ctx X) ρ₀ w₀ c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc⟩ := h
  obtain ⟨hs', -⟩ := gotInv_star (gotInv_entry vc X ρ₀ w₀) hs
  refine ⟨b, k, ρ, w, vb, i, ops, outs, w', hs', hvb, hi, hops, ?_, htc⟩
  obtain ⟨-, hform⟩ := csem_halt hsem
  rw [csemV_eq fun info h => by
    rcases h with rfl | ⟨_, rfl⟩ <;> rcases hform with ⟨_, e⟩ | ⟨_, _, e, _⟩ <;> cases e]
  exact hsem

/-! ## Deciding the analysis -/

/-- A `loadExtNameGot t n` precedes instruction `k` of `vb`. -/
def gotBefore (t : Nat) (n : String) (vb : VBlock) (k : Nat) : Bool :=
  (List.range k).any fun j => decide (vb.insts[j]? = some (.loadExtNameGot (.vreg t .int) n))

/-- Instruction `k` of `vb`, if a call through `t`, follows a `loadExtNameGot t n`. -/
def gotSiteB (t : Nat) (n : String) (vb : VBlock) (k : Nat) : Bool :=
  match vb.insts[k]? with
  | some (.call info) => !decide (info.dest = .reg (.vreg t .int)) || gotBefore t n vb k
  | some (.tryCall info _) => !decide (info.dest = .reg (.vreg t .int)) || gotBefore t n vb k
  | _ => true

/-- An instruction defining `t` is `loadExtNameGot t n`. -/
def gotDefB (t : Nat) (n : String) (i : MInst) : Bool :=
  match i.operands with
  | .ok ops => !(ops.any fun o => o.isDef && o.vreg == t) ||
      decide (i = .loadExtNameGot (.vreg t .int) n)
  | .error _ => true

/-- **`GotV`, decided.** -/
def gotB (vc : VCode) (t : Nat) (n : String) : Bool :=
  vc.blocks.all fun vb =>
    vb.insts.all (gotDefB t n) && (List.range vb.insts.size).all (gotSiteB t n vb)

theorem gotB_sound {vc : VCode} {t : Nat} {n : String} (h : gotB vc t n = true) : GotV vc t n := by
  simp only [gotB] at h
  have hb : ∀ b vb, vc.blocks[b]? = some vb → vb.insts.all (gotDefB t n) = true ∧
      (List.range vb.insts.size).all (gotSiteB t n vb) = true := fun b vb hvb => by
    simpa only [Bool.and_eq_true] using (array_all_iff _ _).1 h b vb hvb
  refine ⟨fun b vb k i ops hvb hi hops hdef => ?_, fun b vb k info hvb hi hd => ?_⟩
  · have := (array_all_iff _ _).1 (hb b vb hvb).1 k i hi
    simp only [gotDefB, hops, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      Array.any_eq_false, Bool.and_eq_true, beq_iff_eq] at this
    rcases this with h1 | h1
    · obtain ⟨o, ho, hd, hv⟩ := hdef
      obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp ho)
      exact absurd ⟨hd, hv⟩ (h1 j hj)
    · exact h1
  · have hk : k < vb.insts.size := by
      rcases hi with hi | ⟨_, hi⟩ <;> exact (Array.getElem?_eq_some_iff.mp hi).1
    have := List.all_eq_true.mp (hb b vb hvb).2 k (List.mem_range.mpr hk)
    have hbef : gotBefore t n vb k = true := by
      rcases hi with hi | ⟨ti, hi⟩ <;> simpa [gotSiteB, hi, hd] using this
    simp only [gotBefore, List.any_eq_true, List.mem_range, decide_eq_true_eq] at hbef
    exact hbef

/-- The symbol of a GOT load into `t` in `vc`, if any. -/
def gotSym (vc : VCode) (t : Nat) : Option String :=
  (vc.blocks.toList.flatMap (·.insts.toList)).findSome? fun i => match i with
    | .loadExtNameGot (.vreg t' .int) n => if t' = t then some n else none
    | _ => none

/-- **The GOT symbol of the target vreg `t`** when `GotV` holds for it (`gotOf_sound`). -/
def gotOf (vc : VCode) (t : Nat) : Option String :=
  match gotSym vc t with
  | some n => if gotB vc t n then some n else none
  | none => none

theorem gotOf_sound {vc : VCode} {t : Nat} {n : String} (h : gotOf vc t = some n) : GotV vc t n := by
  unfold gotOf at h
  cases hs : gotSym vc t with
  | none => simp [hs] at h
  | some n' =>
    simp only [hs] at h
    split at h
    · rename_i hb
      cases h
      exact gotB_sound hb
    · cases h

end E2E
