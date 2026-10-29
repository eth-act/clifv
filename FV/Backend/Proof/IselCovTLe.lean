import FV.Backend.Proof.IselCovTForm

/-!
# Form coverage over float-capable contexts (typed V3): the order and the deep facts

`IselCovLe` for `AT`: `deep_sound`, `le_sound`, `isBot_sound`, `split_sound` (a value's types are
split as a type set's).
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Aarch64
open Backend.Proof.Cov (DeepRegs NumOk numOk_mono kind_cases regsIn_reg)

variable {f : Clif.Function} {ctx : Ctx}

/-! ## Masks -/

theorem and_ne_zero_mono {x m m' : Nat} (h : x &&& m ≠ 0) (hm : m &&& m' = m) : x &&& m' ≠ 0 := by
  intro h0
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 := congrArg (·.testBit i) h0
  have h2 := congrArg (·.testBit i) hm
  simp only [Nat.testBit_and, Nat.zero_testBit] at h1 h2 ⊢
  cases hx : x.testBit i <;> cases hmi : m.testBit i <;> simp_all

theorem and_or_left {m n : Nat} : m &&& (m ||| n) = m := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases m.testBit i <;> cases n.testBit i <;> rfl

theorem and_or_right {m n : Nat} : n &&& (m ||| n) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases m.testBit i <;> cases n.testBit i <;> rfl

theorem deepRegs_mono {m m' : Nat} {v : V} (h : DeepRegs m v) (hm : m &&& m' = m) : DeepRegs m' v :=
  fun r hr => and_ne_zero_mono (h r hr) hm

theorem regsIn_data (t k : Nat) (vs : List V) : (V.data t k vs).regsIn = regsInL vs := by
  simp [V.regsIn]

theorem regsInL_mem' {vs : List V} {r : Reg} (h : r ∈ regsInL vs) : ∃ v ∈ vs, r ∈ v.regsIn := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    simp only [regsInL_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨w, List.mem_cons_self, h⟩
    · obtain ⟨v, hv, h⟩ := ih h; exact ⟨v, List.mem_cons_of_mem _ hv, h⟩

theorem covV_of_mem {v : V} {vs : List V} (h : covVL vs = true) (hv : v ∈ vs) : covV v = true :=
  covVL_iff.mp h v hv

/-! ## Deep facts -/

/-- `deep` facts of a value. -/
abbrev DeepOk (d : Nat × Bool) (v : V) : Prop := DeepRegs d.1 v ∧ (d.2 = true → covV v = true)

mutual
theorem deep_sound : ∀ (a : AT) (v : V), γ f ctx a v → DeepOk (AT.deep a) v
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
  | .val ts, v, h => by
    obtain ⟨x, rfl, -⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩
  | .vals tss, v, h => by
    obtain ⟨xs, rfl, -⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩
  | .valsAll ts, v, h => by
    obtain ⟨xs, rfl, -⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩
  | .inst fs, v, h => by
    obtain ⟨j, -, rfl, -⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn] at hr, fun _ => rfl⟩
  | .movi, v, h => by
    obtain ⟨i, rfl, -⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn, opRegs] at hr, fun _ => rfl⟩
  | .extv, v, h => by
    obtain ⟨x, e, b, rfl, -⟩ := h
    exact ⟨fun r hr => by simp [V.regsIn, opRegs] at hr, fun _ => rfl⟩
  | .alts as, v, h => by
    simp only [AT.deep]
    exact deepAny_sound as v h
  | .data t k fs, v, h => by
    obtain ⟨vs, rfl, hl⟩ := h
    have hd := deepL_sound fs vs hl
    simp only [AT.deep]
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
          · rename_i i hi; exact covOk_sound h1 hl hi
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
theorem deepL_sound : ∀ (as : List AT) (vs : List V), γL f ctx as vs →
    ∀ w ∈ vs, DeepOk (AT.deepL as) w
  | [], [], _, _, h => by cases h
  | a :: as, v :: vs, ⟨h1, h2⟩, w, hw => by
    simp only [AT.deepL]
    rcases List.mem_cons.mp hw with rfl | hw
    · have := deep_sound a w h1
      exact ⟨deepRegs_mono this.1 and_or_left, fun hc => this.2 (by
        simp only [Bool.and_eq_true] at hc; exact hc.1)⟩
    · have := deepL_sound as vs h2 w hw
      exact ⟨deepRegs_mono this.1 and_or_right, fun hc => this.2 (by
        simp only [Bool.and_eq_true] at hc; exact hc.2)⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
/-- `deepL` of a list holds of a value one of its elements describes. -/
theorem deepAny_sound : ∀ (as : List AT) (v : V), γAny f ctx as v → DeepOk (AT.deepL as) v
  | [], _, h => h.elim
  | a :: as, v, h => by
    simp only [AT.deepL]
    rcases h with h | h
    · have := deep_sound a v h
      exact ⟨deepRegs_mono this.1 and_or_left, fun hc => this.2 (by
        simp only [Bool.and_eq_true] at hc; exact hc.1)⟩
    · have := deepAny_sound as v h
      exact ⟨deepRegs_mono this.1 and_or_right, fun hc => this.2 (by
        simp only [Bool.and_eq_true] at hc; exact hc.2)⟩
end

theorem flatOf_sound {a : AT} {v : V} (h : γ f ctx a v) : γ f ctx (AT.flatOf a) v :=
  deep_sound a v h

/-! ## The order -/

theorem deepLe_sound {a : AT} {m : Nat} {c : Bool} (hle : AT.deepLe a m c = true) {v : V}
    (h : γ f ctx a v) : γ f ctx (.flat m c) v := by
  simp only [AT.deepLe, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hle
  have hd := deep_sound a v h
  refine ⟨deepRegs_mono hd.1 hle.1, fun hc => hd.2 ?_⟩
  rcases hle.2 with h1 | h1
  · rw [hc] at h1; cases h1
  · exact h1

theorem list_all_contains {ts us : List CTy} (h : (ts.all fun t => us.any fun u => decide (u = t)) = true)
    {t : CTy} (ht : t ∈ ts) : t ∈ us := by
  have := List.all_eq_true.mp h t ht
  obtain ⟨u, hu, he⟩ := List.any_eq_true.mp this
  rw [← of_decide_eq_true he]; exact hu

theorem leBase_sound {a b : AT} (hle : AT.leBase a b = true) {v : V} (h : γ f ctx a v) :
    γ f ctx b v := by
  cases b with
  | flat m c => exact deepLe_sound (by cases a <;> simpa [AT.leBase] using hle) h
  | reg n =>
    cases a <;> simp only [AT.leBase, beq_iff_eq, reduceCtorEq] at hle
    rename_i m
    obtain ⟨r, rfl, hk⟩ := h
    exact ⟨r, rfl, and_ne_zero_mono hk hle⟩
  | ty us =>
    cases a <;> simp only [AT.leBase, reduceCtorEq] at hle
    obtain ⟨t, ht, rfl⟩ := h
    exact ⟨t, list_all_contains hle ht, rfl⟩
  | bool b' =>
    cases a <;> simp only [AT.leBase, beq_iff_eq, reduceCtorEq] at hle
    subst hle; exact h
  | logic s' =>
    cases a <;> simp only [AT.leBase, beq_iff_eq, reduceCtorEq] at hle
    subst hle; exact h
  | scale b' =>
    cases a <;> simp only [AT.leBase, beq_iff_eq, reduceCtorEq] at hle
    subst hle; exact h
  | simm9 => cases a <;> simp only [AT.leBase, reduceCtorEq] at hle; exact h
  | val us =>
    cases a <;> simp only [AT.leBase, reduceCtorEq] at hle
    obtain ⟨x, rfl, h1, h2⟩ := h
    refine ⟨x, rfl, fun t ht => list_all_contains hle (h1 t ht), fun hn => ?_⟩
    obtain ⟨t, ht, hc⟩ := h2 hn
    exact ⟨t, list_all_contains hle ht, hc⟩
  | vals uss =>
    cases a <;> simp only [AT.leBase, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at hle
    rename_i tss
    obtain ⟨xs, rfl, hlen, hv⟩ := h
    refine ⟨xs, rfl, hlen.trans hle.1, fun i x us' hx hus => ?_⟩
    have hi : i < tss.length := by
      have := (List.getElem?_eq_some_iff.mp hx).1; omega
    obtain ⟨ts, hts⟩ : ∃ ts, tss[i]? = some ts := ⟨_, List.getElem?_eq_getElem hi⟩
    have hz : (tss.zip uss)[i]? = some (ts, us') := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hts, hus⟩
    have hall := List.all_eq_true.mp hle.2 _ (List.mem_of_getElem? hz)
    obtain ⟨h1, h2⟩ := hv i x ts hx hts
    refine ⟨fun t ht => list_all_contains hall (h1 t ht), fun hn => ?_⟩
    obtain ⟨t, ht, hc⟩ := h2 hn
    exact ⟨t, list_all_contains hall ht, hc⟩
  | valsAll us =>
    cases a <;> simp only [AT.leBase, reduceCtorEq] at hle
    obtain ⟨xs, rfl, hv⟩ := h
    refine ⟨xs, rfl, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := hv x hx
    refine ⟨fun t ht => list_all_contains hle (h1 t ht), fun hn => ?_⟩
    obtain ⟨t, ht, hc⟩ := h2 hn
    exact ⟨t, list_all_contains hle ht, hc⟩
  | inst gs =>
    cases a <;> simp only [AT.leBase, reduceCtorEq] at hle
    obtain ⟨j, info, rfl, hi, i, hif, hF⟩ := h
    exact ⟨j, info, rfl, hi, i, by simpa using List.all_eq_true.mp hle i hif, hF⟩
  | movi => cases a <;> simp only [AT.leBase, reduceCtorEq] at hle; exact h
  | extv => cases a <;> simp only [AT.leBase, reduceCtorEq] at hle; exact h
  | num k' b' =>
    cases a <;> simp only [AT.leBase, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      reduceCtorEq] at hle
    obtain ⟨rfl, hb⟩ := hle
    exact numOk_mono hb h
  | _ => cases a <;> simp [AT.leBase] at hle

mutual
/-- **The order is inclusion of meanings.** -/
theorem le_sound : ∀ (a b : AT), AT.le a b = true → ∀ v, γ f ctx a v → γ f ctx b v
  | .bot, _, _, _, h => h.elim
  | .alts as, b, hle, v, h => by
    rw [AT.le] at hle
    exact leAlts_sound as b hle v h
  | .data t k fs, .flat m c, hle, v, h => by
    rw [AT.le] at hle
    exact deepLe_sound hle h
  | .data t k fs, .data t' k' gs, hle, v, h => by
    rw [AT.le] at hle
    simp only [Bool.and_eq_true, beq_iff_eq] at hle
    obtain ⟨⟨rfl, rfl⟩, hl⟩ := hle
    obtain ⟨vs, rfl, hfs⟩ := h
    exact ⟨vs, rfl, leL_sound fs gs hl vs hfs⟩
  | .data t k fs, .alts bs, hle, v, h => by
    rw [AT.le] at hle
    obtain ⟨b, hb, hbv⟩ := leSome_sound (.data t k fs) bs hle v h
    exact γAny_iff.mpr ⟨b, hb, hbv⟩
  | .data _ _ _, .bot, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .reg _, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .ty _, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .bool _, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .logic _, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .scale _, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .simm9, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .val _, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .vals _, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .valsAll _, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .inst _, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .movi, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .extv, hle, _, _ => by simp [AT.le] at hle
  | .data _ _ _, .num _ _, hle, _, _ => by simp [AT.le] at hle
  | .flat m c, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .reg m, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .ty ts, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .bool b', b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .logic s, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .scale s, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .simm9, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .val ts, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .vals tss, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .valsAll ts, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .inst fs, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .movi, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .extv, b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  | .num k b', b, hle, v, h => leBase_sound (by simpa [AT.le] using hle) h
  termination_by a b => sizeOf a + sizeOf b
  decreasing_by all_goals simp_wf <;> omega
theorem leAlts_sound : ∀ (as : List AT) (b : AT), AT.leAlts as b = true →
    ∀ v, γAny f ctx as v → γ f ctx b v
  | [], _, _, _, h => h.elim
  | a :: as, b, hle, v, h => by
    rw [AT.leAlts] at hle
    simp only [Bool.and_eq_true] at hle
    rcases h with h | h
    · exact le_sound a b hle.1 v h
    · exact leAlts_sound as b hle.2 v h
  termination_by as b => sizeOf as + sizeOf b
  decreasing_by all_goals simp_wf <;> omega
theorem leSome_sound : ∀ (a : AT) (bs : List AT), AT.leSome a bs = true →
    ∀ v, γ f ctx a v → ∃ b ∈ bs, γ f ctx b v
  | _, [], hle, _, _ => by simp [AT.leSome] at hle
  | a, b :: bs, hle, v, h => by
    rw [AT.leSome] at hle
    simp only [Bool.or_eq_true] at hle
    rcases hle with hle | hle
    · exact ⟨b, List.mem_cons_self, le_sound a b hle v h⟩
    · obtain ⟨c, hc, hcv⟩ := leSome_sound a bs hle v h
      exact ⟨c, List.mem_cons_of_mem _ hc, hcv⟩
  termination_by a bs => sizeOf a + sizeOf bs
  decreasing_by all_goals simp_wf <;> omega
theorem leL_sound : ∀ (as bs : List AT), AT.leL as bs = true →
    ∀ vs, γL f ctx as vs → γL f ctx bs vs
  | [], [], _, [], _ => trivial
  | a :: as, b :: bs, hle, v :: vs, ⟨h1, h2⟩ => by
    rw [AT.leL] at hle
    simp only [Bool.and_eq_true] at hle
    exact ⟨le_sound a b hle.1 v h1, leL_sound as bs hle.2 vs h2⟩
  | [], _ :: _, hle, _, _ => by simp [AT.leL] at hle
  | _ :: _, [], hle, _, _ => by simp [AT.leL] at hle
  | [], [], _, _ :: _, h => h.elim
  | _ :: _, _ :: _, _, [], h => h.elim
  termination_by as bs => sizeOf as + sizeOf bs
  decreasing_by all_goals simp_wf <;> omega
end

/-! ## Empty values and splitting -/

theorem isBot_sound {a : AT} (hb : a.isBot = true) {v : V} (h : γ f ctx a v) : False := by
  cases a with
  | bot => exact h
  | ty ts =>
    cases ts with
    | nil => obtain ⟨t, ht, -⟩ := h; cases ht
    | cons _ _ => simp [AT.isBot] at hb
  | val ts =>
    cases ts with
    | nil =>
      obtain ⟨x, -, h1, h2⟩ := h
      cases hx : ctx.valueType? x with
      | none => obtain ⟨t, ht, -⟩ := h2 hx; cases ht
      | some t => cases h1 t hx
    | cons _ _ => simp [AT.isBot] at hb
  | inst fs =>
    cases fs with
    | nil => obtain ⟨_, _, _, _, i, hi, -⟩ := h; cases hi
    | cons _ _ => simp [AT.isBot] at hb
  | _ => simp [AT.isBot] at hb

theorem split_sound {a : AT} {v : V} (h : γ f ctx a v) : ∃ b ∈ AT.split a, γ f ctx b v := by
  unfold AT.split
  split
  · rename_i t u us
    obtain ⟨t', ht', rfl⟩ := h
    exact ⟨.ty [t'], List.mem_map.mpr ⟨t', ht', rfl⟩, ⟨t', List.mem_singleton_self _, rfl⟩⟩
  · rename_i t u us
    obtain ⟨x, rfl, h1, h2⟩ := h
    cases hx : ctx.valueType? x with
    | some t' =>
      have ht' := h1 t' hx
      refine ⟨.val [t'], List.mem_map.mpr ⟨t', ht', rfl⟩, x, rfl, fun s hs => ?_, fun hn => ?_⟩
      · rw [hx] at hs; cases hs; exact List.mem_singleton_self _
      · rw [hx] at hn; cases hn
    | none =>
      obtain ⟨t', ht', hc⟩ := h2 hx
      refine ⟨.val [t'], List.mem_map.mpr ⟨t', ht', rfl⟩, x, rfl, fun s hs => ?_, fun _ => ?_⟩
      · rw [hx] at hs; cases hs
      · exact ⟨t', List.mem_singleton_self _, hc⟩
  · exact ⟨a, List.mem_singleton_self _, h⟩

end Backend.Proof.CovT
