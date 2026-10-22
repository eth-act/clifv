import FV.Backend.Proof.IselCovLe
import FV.Backend.Proof.IselCovFormT
import FV.Backend.Proof.IselCovSemT

/-!
# Form coverage over float-capable contexts: the order and the deep facts

The typed counterpart of `IselCovLe`: `deep_soundT`, `le_soundT` (the order is inclusion of
meanings of `γT`), `isBot_soundT`, `split_soundT`. The proofs are `IselCovLe`'s, with the `.xv`
case read over `AVT.HoldsS` (`IselCovSemT`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64

variable {S : Clif.Inst → Bool} {iOps fOps : List Nat} {f : Clif.Function} {ctx : Ctx}

/-! ## Deep facts -/

mutual
theorem deep_soundT : ∀ (a : AW) (v : V), γT S iOps fOps f ctx a v → DeepOk (AW.deep a) v
  | .bot, _, h => h.elim
  | .flat m c, v, h => h
  | .reg m, v, h => by
    obtain ⟨r, rfl, hk⟩ := h
    refine ⟨fun r' hr => ?_, fun _ => rfl⟩
    simp only [regsIn_reg, List.mem_singleton] at hr
    subst hr; exact hk
  | .ty ts, v, h => by
    obtain ⟨t, -, rfl⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩
  | .bool b, v, h => by
    have h' : v = .bool b := h
    subst h'
    exact ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩
  | .logic sz, v, h => by
    obtain ⟨i, rfl, -, -⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn, opRegs] at hr, fun _ => rfl⟩
  | .scale b, v, h => by
    obtain ⟨o, rfl, -⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn, opRegs] at hr, fun _ => rfl⟩
  | .simm9, v, h => by
    obtain ⟨i, rfl, -⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn, opRegs] at hr, fun _ => rfl⟩
  | .xv e, v, h => ⟨fun r hr => (by rw [h.2.1] at hr; cases hr), fun _ => h.2.2⟩
  | .alts as, v, h => by
    simp only [AW.deep]
    exact deepAny_soundT as v h
  | .data t k fs, v, h => by
    obtain ⟨vs, rfl, hl⟩ := h
    have hd := deepL_soundT fs vs hl
    simp only [AW.deep]
    refine ⟨fun r hr => ?_, fun hc => ?_⟩
    · rw [regsIn_data] at hr
      obtain ⟨w, hw, hrw⟩ := regsInL_mem' hr
      exact (hd w hw).1 r hrw
    · simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hc
      rw [covV_data]
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
      refine ⟨?_, covVL_iff.mpr fun w hw => (hd w hw).2 hc.1⟩
      by_cases ht : t = tyMInst
      · right
        rcases hc.2 with h1 | h1
        · exact absurd ht h1
        · split
          · rename_i i hi; exact covOk_soundT h1 hl hi
          · rfl
      · exact .inl ht
  | .num k b, v, h => by
    cases k
    case callInfo =>
      obtain ⟨c, rfl, -⟩ := h
      show DeepOk (15, true) _
      refine ⟨fun r _ => ?_, fun _ => rfl⟩
      rcases kind_cases r with h1 | h1 | h1 | h1 <;> rw [h1] <;> decide
    case int =>
      obtain ⟨i, rfl, -⟩ := h
      exact ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩
    all_goals
      obtain ⟨_, rfl, -⟩ := h
      exact ⟨fun r hr => by simp [V.regsIn, opRegs] at hr, fun _ => rfl⟩
/-- `deepL` of a list holds of every value of a pointwise-described list. -/
theorem deepL_soundT : ∀ (as : List AW) (vs : List V), γLT S iOps fOps f ctx as vs →
    ∀ w ∈ vs, DeepOk (AW.deepL as) w
  | [], [], _, _, h => by cases h
  | a :: as, v :: vs, ⟨h1, h2⟩, w, hw => by
    simp only [AW.deepL]
    rcases List.mem_cons.mp hw with rfl | hw
    · have := deep_soundT a w h1
      exact ⟨deepRegs_mono this.1 and_or_left, fun hc => this.2 (by
        simp only [Bool.and_eq_true] at hc; exact hc.1)⟩
    · have := deepL_soundT as vs h2 w hw
      exact ⟨deepRegs_mono this.1 and_or_right, fun hc => this.2 (by
        simp only [Bool.and_eq_true] at hc; exact hc.2)⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
/-- `deepL` of a list holds of a value one of its elements describes. -/
theorem deepAny_soundT : ∀ (as : List AW) (v : V), γAnyT S iOps fOps f ctx as v →
    DeepOk (AW.deepL as) v
  | [], _, h => h.elim
  | a :: as, v, h => by
    simp only [AW.deepL]
    rcases h with h | h
    · have := deep_soundT a v h
      exact ⟨deepRegs_mono this.1 and_or_left, fun hc => this.2 (by
        simp only [Bool.and_eq_true] at hc; exact hc.1)⟩
    · have := deepAny_soundT as v h
      exact ⟨deepRegs_mono this.1 and_or_right, fun hc => this.2 (by
        simp only [Bool.and_eq_true] at hc; exact hc.2)⟩
end

theorem flatOf_soundT {a : AW} {v : V} (h : γT S iOps fOps f ctx a v) :
    γT S iOps fOps f ctx (AW.flatOf a) v :=
  deep_soundT a v h

/-! ## The order -/

theorem deepLe_soundT {a : AW} {m : Nat} {c : Bool} (hle : AW.deepLe a m c = true) {v : V}
    (h : γT S iOps fOps f ctx a v) : γT S iOps fOps f ctx (.flat m c) v := by
  simp only [AW.deepLe, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hle
  have hd := deep_soundT a v h
  refine ⟨deepRegs_mono hd.1 hle.1, fun hc => hd.2 ?_⟩
  rcases hle.2 with h1 | h1
  · rw [hc] at h1; cases h1
  · exact h1

theorem leBase_soundT {a b : AW} (hle : AW.leBase a b = true) {v : V} (h : γT S iOps fOps f ctx a v) :
    γT S iOps fOps f ctx b v := by
  cases b with
  | flat m c => exact deepLe_soundT (by cases a <;> simpa [AW.leBase] using hle) h
  | reg n =>
    cases a <;> simp only [AW.leBase, beq_iff_eq, reduceCtorEq] at hle
    rename_i m
    obtain ⟨r, rfl, hk⟩ := h
    exact ⟨r, rfl, and_ne_zero_mono hk hle⟩
  | ty us =>
    cases a <;> simp only [AW.leBase, reduceCtorEq] at hle
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨t, list_all_contains hle ht, rfl⟩
  | bool b' =>
    cases a <;> simp only [AW.leBase, beq_iff_eq, reduceCtorEq] at hle
    subst hle; exact h
  | logic s' =>
    cases a <;> simp only [AW.leBase, beq_iff_eq, reduceCtorEq] at hle
    subst hle; exact h
  | scale b' =>
    cases a <;> simp only [AW.leBase, beq_iff_eq, reduceCtorEq] at hle
    subst hle; exact h
  | simm9 => cases a <;> simp only [AW.leBase, reduceCtorEq] at hle; exact h
  | xv e' =>
    cases a <;> simp only [AW.leBase, decide_eq_true_eq, reduceCtorEq] at hle
    subst hle; exact h
  | num k' b' =>
    cases a <;> simp only [AW.leBase, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      reduceCtorEq] at hle
    obtain ⟨rfl, hb⟩ := hle
    exact numOk_mono hb h
  | _ => cases a <;> simp [AW.leBase] at hle

mutual
/-- **The order is inclusion of meanings.** -/
theorem le_soundT : ∀ (a b : AW), AW.le a b = true → ∀ v, γT S iOps fOps f ctx a v →
    γT S iOps fOps f ctx b v
  | .bot, _, _, _, h => h.elim
  | .alts as, b, hle, v, h => by
    rw [AW.le] at hle
    exact leAlts_soundT as b hle v h
  | .data t k fs, .flat m c, hle, v, h => by
    rw [AW.le] at hle
    exact deepLe_soundT hle h
  | .data t k fs, .data t' k' gs, hle, v, h => by
    rw [AW.le] at hle
    simp only [Bool.and_eq_true, beq_iff_eq] at hle
    obtain ⟨⟨rfl, rfl⟩, hl⟩ := hle
    obtain ⟨vs, rfl, hfs⟩ := h
    exact ⟨vs, rfl, leL_soundT fs gs hl vs hfs⟩
  | .data t k fs, .alts bs, hle, v, h => by
    rw [AW.le] at hle
    obtain ⟨b, hb, hbv⟩ := leSome_soundT (.data t k fs) bs hle v h
    exact γAnyT_iff.mpr ⟨b, hb, hbv⟩
  | .data _ _ _, .bot, hle, _, _ => by simp [AW.le] at hle
  | .data _ _ _, .reg _, hle, _, _ => by simp [AW.le] at hle
  | .data _ _ _, .ty _, hle, _, _ => by simp [AW.le] at hle
  | .data _ _ _, .bool _, hle, _, _ => by simp [AW.le] at hle
  | .data _ _ _, .logic _, hle, _, _ => by simp [AW.le] at hle
  | .data _ _ _, .scale _, hle, _, _ => by simp [AW.le] at hle
  | .data _ _ _, .simm9, hle, _, _ => by simp [AW.le] at hle
  | .data _ _ _, .xv _, hle, _, _ => by simp [AW.le] at hle
  | .data _ _ _, .num _ _, hle, _, _ => by simp [AW.le] at hle
  | .flat m c, b, hle, v, h => leBase_soundT (by simpa [AW.le] using hle) h
  | .reg m, b, hle, v, h => leBase_soundT (by simpa [AW.le] using hle) h
  | .ty ts, b, hle, v, h => leBase_soundT (by simpa [AW.le] using hle) h
  | .bool b', b, hle, v, h => leBase_soundT (by simpa [AW.le] using hle) h
  | .logic s, b, hle, v, h => leBase_soundT (by simpa [AW.le] using hle) h
  | .scale s, b, hle, v, h => leBase_soundT (by simpa [AW.le] using hle) h
  | .simm9, b, hle, v, h => leBase_soundT (by simpa [AW.le] using hle) h
  | .xv e, b, hle, v, h => leBase_soundT (by simpa [AW.le] using hle) h
  | .num k b', b, hle, v, h => leBase_soundT (by simpa [AW.le] using hle) h
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by all_goals simp_wf <;> omega
theorem leAlts_soundT : ∀ (as : List AW) (b : AW), AW.leAlts as b = true →
    ∀ v, γAnyT S iOps fOps f ctx as v → γT S iOps fOps f ctx b v
  | [], _, _, _, h => h.elim
  | a :: as, b, hle, v, h => by
    rw [AW.leAlts] at hle
    simp only [Bool.and_eq_true] at hle
    rcases h with h | h
    · exact le_soundT a b hle.1 v h
    · exact leAlts_soundT as b hle.2 v h
  termination_by as b => sizeOf as + sizeOf b
  decreasing_by all_goals simp_wf <;> omega
theorem leSome_soundT : ∀ (a : AW) (bs : List AW), AW.leSome a bs = true →
    ∀ v, γT S iOps fOps f ctx a v → ∃ b ∈ bs, γT S iOps fOps f ctx b v
  | _, [], hle, _, _ => by simp [AW.leSome] at hle
  | a, b :: bs, hle, v, h => by
    rw [AW.leSome] at hle
    simp only [Bool.or_eq_true] at hle
    rcases hle with hle | hle
    · exact ⟨b, List.mem_cons_self, le_soundT a b hle v h⟩
    · obtain ⟨c, hc, hcv⟩ := leSome_soundT a bs hle v h
      exact ⟨c, List.mem_cons_of_mem _ hc, hcv⟩
  termination_by a bs => sizeOf a + sizeOf bs
  decreasing_by all_goals simp_wf <;> omega
theorem leL_soundT : ∀ (as bs : List AW), AW.leL as bs = true →
    ∀ vs, γLT S iOps fOps f ctx as vs → γLT S iOps fOps f ctx bs vs
  | [], [], _, [], _ => trivial
  | a :: as, b :: bs, hle, v :: vs, ⟨h1, h2⟩ => by
    rw [AW.leL] at hle
    simp only [Bool.and_eq_true] at hle
    exact ⟨le_soundT a b hle.1 v h1, leL_soundT as bs hle.2 vs h2⟩
  | [], _ :: _, hle, _, _ => by simp [AW.leL] at hle
  | _ :: _, [], hle, _, _ => by simp [AW.leL] at hle
  | [], [], _, _ :: _, h => h.elim
  | _ :: _, _ :: _, _, [], h => h.elim
  termination_by as bs => sizeOf as + sizeOf bs
  decreasing_by all_goals simp_wf <;> omega
end

/-! ## Empty values and splitting -/

theorem isBot_soundT {a : AW} (hb : a.isBot = true) {v : V} (h : γT S iOps fOps f ctx a v) : False := by
  cases a with
  | bot => exact h
  | ty ts =>
    cases ts with
    | nil => obtain ⟨t, ht, -⟩ := h; cases ht
    | cons _ _ => simp [AW.isBot] at hb
  | _ => simp [AW.isBot] at hb

theorem split_soundT {a : AW} {v : V} (h : γT S iOps fOps f ctx a v) :
    ∃ b ∈ AW.split a, γT S iOps fOps f ctx b v := by
  unfold AW.split
  split
  · rename_i t u us
    obtain ⟨t', ht', rfl⟩ := h
    exact ⟨.ty [t'], List.mem_map.mpr ⟨t', ht', rfl⟩, ⟨t', List.mem_singleton_self _, rfl⟩⟩
  · exact ⟨a, List.mem_singleton_self _, h⟩

end Backend.Proof.Cov
