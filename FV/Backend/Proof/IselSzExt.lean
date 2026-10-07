import FV.Backend.Proof.IselSzDefs
import FV.Backend.Proof.IselEmitCtor

/-!
# The size of the ISLE lowering's output (V6c): the extern helpers and the oracle

The facts the cost analysis assumes (`IselSzDefs`), for V3's transfer functions:

* `extW_wt`/`extW_tg` (`ExtW`): an extern constructor call grows the weight `wtA` of the
  emitted instructions by at most `actorW`, their branch targets `tgA` by at most `actorT`.
  `externCtor_sz`: what a call emits (`SzE`): nothing, `emit`'s instruction, the `movz`/`movn`
  and at most three `movk`s of `load_constant_full` (`loadConstantFull_wt`), `gen_return`'s
  `Rets` of at most 8 registers, or `gen_call_args`' stores (no targets). `ofV_sz`: an
  instruction `MInst.ofV` builds from a variant other than `Call`/`CallInd`/`JTSequence` weighs
  at most `emitK`, and has at most `varT` targets of its variant.
* `oracleW_wt`/`oracleW_tg` (`OracleW`): the `operand_size` oracle keeps the lowering state
  (`os_run`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-! ## Weights and targets of arrays -/

theorem wtA_append (a : Array MInst) (ms : List MInst) :
    wtA (a ++ ms.toArray) = wtA a + wtL ms := by
  simp [wtA, wtL, List.map_append, List.sum_append]

theorem tgA_append (a : Array MInst) (ms : List MInst) :
    tgA (a ++ ms.toArray) = tgA a + tgL ms := by
  simp [tgA, tgL, List.map_append, List.sum_append]

theorem wtA_push (a : Array MInst) (m : MInst) : wtA (a.push m) = wtA a + szInstW m := by
  simp [wtA, wtL, List.map_append, List.sum_append]

theorem tgA_push (a : Array MInst) (m : MInst) :
    tgA (a.push m) = tgA a + m.targets.length := by
  simp [tgA, tgL, List.map_append, List.sum_append]

theorem tgL_nil_targets : ∀ ms : List MInst, (∀ m ∈ ms, m.targets = []) → tgL ms = 0
  | [], _ => rfl
  | m :: ms, h => by
    have h1 := h m (List.mem_cons_self ..)
    have h2 := tgL_nil_targets ms fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
    simp only [tgL, List.map_cons, List.sum_cons] at h2 ⊢
    rw [h1, h2]; rfl

/-- Instructions emitted under `EmSince` have no branch targets. -/
theorem tgA_of_since {s0 s : LState} (h : EmSince s0 s) : tgA s.emitted = tgA s0.emitted := by
  obtain ⟨ms, h1, h2⟩ := h
  rw [h1, tgA_append, tgL_nil_targets ms fun m hm => (h2 m hm).2, Nat.add_zero]

/-! ## `MInst.ofV`: weights and targets per variant -/

/-- The weight and target bounds of an instruction built from variant `k`. -/
def SzOk (k : Nat) (m : MInst) : Prop :=
  (k ≠ VIdx.MInst.Call → k ≠ VIdx.MInst.CallInd → k ≠ VIdx.MInst.JTSequence → szInstW m ≤ emitK) ∧
    (varT k).all (fun n => decide (m.targets.length ≤ n)) = true

set_option maxHeartbeats 4000000 in
/-- **`MInst.ofV`**: an instruction of a variant other than `Call`, `CallInd`, `JTSequence`
weighs at most `emitK`; every instruction has at most `varT` targets of its variant. -/
theorem ofV_sz {k : Nat} {fs : List V} {m : MInst}
    (h : MInst.ofV (.data tyMInst k fs) = some m) : SzOk k m := by
  unfold MInst.ofV at h
  obtain ⟨⟨k', fs'⟩, he, h2⟩ := bind_some_ex h
  clear h
  obtain ⟨rfl, rfl⟩ : k = k' ∧ fs = fs' := by
    have := enumOf_eq he
    simp only [V.data.injEq] at this
    exact ⟨this.2.1, this.2.2⟩
  revert h2
  revert m
  apply ofV_split _ (fun k _ (r : Option MInst) => ∀ m, r = some m → SzOk k m)
  all_goals
    intros
    rename_i m hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := bind_some_ex hm) | split at hm)
    all_goals first
      | (cases hm; done)
      | (simp only [pure, Option.some.injEq] at hm
         subst hm
         refine ⟨?_, ?_⟩
         · intro h1 h2 h3
           first
             | exact absurd rfl h1
             | exact absurd rfl h2
             | exact absurd rfl h3
             | simp [szInstW, szWords, regCount, MInst.targets, emitK]
         · first
             | rfl
             | (cases varT _ <;> rfl))

/-! ## `emit`: the abstract instruction's weight and targets -/

variable {f : Clif.Function} {ctx : Ctx}

theorem emitW_data {t k : Nat} {vs : List V} {m : MInst}
    (h : (t == tyMInst && (k != VIdx.MInst.Call && k != VIdx.MInst.CallInd &&
      k != VIdx.MInst.JTSequence)) = true) (hm : MInst.ofV (.data t k vs) = some m) :
    szInstW m ≤ emitK := by
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨rfl, ⟨h1, h2⟩, h3⟩ := h
  exact (ofV_sz hm).1 h1 h2 h3

/-- **`emitW`**: an instruction `emit` builds from a value `a` describes weighs at most
`emitW a`. -/
theorem emitW_sound {a : AW} {c : Nat} (ha : emitW a = some c) {v : V} (hv : γ f ctx a v)
    {m : MInst} (hm : MInst.ofV v = some m) : szInstW m ≤ c := by
  cases a with
  | data t k fs =>
    simp only [emitW] at ha
    split at ha
    · cases ha
      obtain ⟨vs, rfl, -⟩ := hv
      exact emitW_data ‹_› hm
    · cases ha
  | alts as =>
    simp only [emitW] at ha
    split at ha
    · cases ha
      rename_i hall
      obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
      have hp := List.all_eq_true.mp hall b hb
      cases b with
      | data t k fs =>
        obtain ⟨vs, rfl, -⟩ := hbv
        exact emitW_data hp hm
      | _ => cases hp
    · cases ha
  | _ => cases ha

theorem varT_sound {k : Nat} {vs : List V} {m : MInst} {n : Nat} (hk : varT k = some n)
    (hm : MInst.ofV (.data tyMInst k vs) = some m) : m.targets.length ≤ n := by
  have h := (ofV_sz hm).2
  rw [hk] at h
  exact of_decide_eq_true h

theorem foldl_max_ge_start : ∀ (l : List Nat) (m : Nat), m ≤ l.foldl max m
  | [], _ => Nat.le_refl _
  | a :: l, m => Nat.le_trans (Nat.le_max_left m a) (foldl_max_ge_start l (max m a))

theorem mem_le_foldl_max : ∀ (l : List Nat) (m x : Nat), x ∈ l → x ≤ l.foldl max m
  | [], _, _, h => by cases h
  | a :: l, m, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right m x) (foldl_max_ge_start l _)
    · exact mem_le_foldl_max l _ x h

/-- **`emitT`**: an instruction `emit` builds from a value `a` describes has at most `emitT a`
branch targets. -/
theorem emitT_sound {a : AW} {n : Nat} (ha : emitT a = some n) {v : V} (hv : γ f ctx a v)
    {m : MInst} (hm : MInst.ofV v = some m) : m.targets.length ≤ n := by
  cases a with
  | data t k fs =>
    simp only [emitT] at ha
    split at ha
    · rename_i ht
      obtain rfl : t = tyMInst := eq_of_beq ht
      obtain ⟨vs, rfl, -⟩ := hv
      exact varT_sound ha hm
    · cases ha
  | alts as =>
    simp only [emitT, Option.map_eq_some_iff] at ha
    obtain ⟨ns, hns, rfl⟩ := ha
    obtain ⟨b, hb, hbv⟩ := γAny_iff.mp hv
    obtain ⟨nb, hnb, hg⟩ := mapM_some_mem hns b hb
    refine Nat.le_trans ?_ (mem_le_foldl_max ns 0 nb hnb)
    cases b with
    | data t k fs =>
      simp only at hg
      split at hg
      · rename_i ht
        obtain rfl : t = tyMInst := eq_of_beq ht
        obtain ⟨vs, rfl, -⟩ := hbv
        exact varT_sound hg hm
      · cases hg
    | _ => cases hg
  | _ => cases ha

/-! ## `load_constant_full` -/

theorem foldl_wt {α β : Type} (W : α → Nat) (F : α → β → α) (g : β → Nat)
    (hF : ∀ a b, W (F a b) ≤ W a + g b) : ∀ (l : List β) (a : α), W (l.foldl F a) ≤ W a + (l.map g).sum
  | [], _ => by simp
  | b :: l, a => by
    have := foldl_wt W F g hF l (F a b)
    have := hF a b
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    omega

/-- The weight of the `movk` of slice `sh` (none for the first slice). -/
def movKW (sh : Nat) : Nat := if sh = 0 then 0 else 101

theorem movKW_sum (s : OperandSize) : ((List.range (s.bits / 16)).map movKW).sum ≤ 303 := by
  cases s <;> decide

theorem szInstW_movWide (op : MoveWideOp) (rd : Reg) (i : MoveWideConst) (sz : OperandSize) :
    szInstW (.movWide op rd i sz) = 101 := rfl

/-- A `movk` of a later slice weighs `movKW`. -/
theorem wt_movK (s : LState) (rd rn : Reg) (i : MoveWideConst) (sz : OperandSize) {sh : Nat}
    (hsh : sh ≠ 0) : wtA (s.emit (.movK rd rn i sz)).emitted ≤ wtA s.emitted + movKW sh := by
  simp only [LState.emit, wtA_push, movKW, hsh, ↓reduceIte]
  exact Nat.le_refl _

/-- The `movz`/`movn` and the `movk`s weigh at most `loadConstW`. -/
theorem lcf_total {s s0 : LState} {m : MInst} (S : OperandSize) (hs : s.emitted = s0.emitted.push m)
    (hm : szInstW m = 101) :
    wtA s.emitted + ((List.range (S.bits / 16)).map movKW).sum ≤ wtA s0.emitted + loadConstW := by
  have := movKW_sum S
  rw [hs, wtA_push, hm]
  simp only [loadConstW, emitK]
  omega

/-- **`load_constant_full`** emits at most `loadConstW`: a `movz`/`movn` and a `movk` per later
slice (at most three). -/
theorem loadConstantFull_wt (bits : Nat) (se : Bool) (sz : OperandSize) (value : Nat)
    (st : LState) :
    wtA (loadConstantFull bits se sz value st).2.emitted ≤ wtA st.emitted + loadConstW := by
  unfold loadConstantFull
  dsimp only
  refine Nat.le_trans (foldl_wt (fun x : Reg × LState × Nat => wtA x.2.1.emitted) _ movKW ?_ _ _)
    (lcf_total _ rfl (szInstW_movWide _ _ _ _))
  intro x sh
  refine ite_inv (I := fun y : Reg × LState × Nat => wtA y.2.1.emitted ≤ wtA x.2.1.emitted + movKW sh)
    (fun _ => Nat.le_add_right _ _) fun hc => ?_
  refine ite_inv (I := fun y : Reg × LState × Nat => wtA y.2.1.emitted ≤ wtA x.2.1.emitted + movKW sh)
    (fun _ => ?_) fun _ => Nat.le_add_right _ _
  exact wt_movK _ _ _ _ _ fun h0 => hc (by subst h0; exact Nat.zero_le _)

/-! ## The extern constructors -/

/-- What an extern constructor call emits, from `st` to `st'`: nothing, `emit`'s instruction,
`load_constant_full`'s (weight at most `loadConstW`, no targets), `gen_return`'s `Rets` of at
most 8 registers, or `gen_call_args`' stores (no targets). -/
def SzE (id : TermId) (args : List V) (st st' : LState) : Prop :=
  st'.emitted = st.emitted ∨
  (id = TId.emit ∧ ∃ i m, args = [i] ∧ MInst.ofV i = some m ∧ st'.emitted = st.emitted.push m) ∨
  (id = TId.load_constant_full ∧ wtA st'.emitted ≤ wtA st.emitted + loadConstW ∧
    tgA st'.emitted = tgA st.emitted) ∨
  (id = TId.gen_return ∧ ∃ l : List (Reg × Reg), l.length ≤ 8 ∧
    st'.emitted = st.emitted.push (.rets l)) ∨
  (id = TId.gen_call_args ∧ tgA st'.emitted = tgA st.emitted)

/-- `SzE` of every successful result. -/
def SzP (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) : Prop :=
  ∀ v st', r = .ok (v, st') → SzE id args st st'

theorem retRegs_zip_len {n : Nat} {ps : List Reg} (h : retRegs n = some ps) (rs : List Reg) :
    (rs.zip ps).length ≤ 8 := by
  unfold retRegs at h
  split at h
  · cases h; simp only [List.length_zip, List.length_map, List.length_range]; omega
  · cases h

set_option maxHeartbeats 8000000 in
/-- **Every extern constructor** emits what `SzE` states. -/
theorem externCtor_sz (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    SzP st t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h; exact .inl rfl
    · cases h
  · apply externCtor_split _ (SzP st)
    all_goals
      intros
      unfold SzP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | exact .inl rfl
      | exact .inr (.inl ⟨rfl, _, _, rfl, ‹_›, rfl⟩)
      | exact .inr (.inr (.inr (.inr ⟨rfl, tgA_of_since (callArgs_em st _ _ (fun _ _ => rfl))⟩)))
      | exact .inr (.inr (.inl ⟨rfl, loadConstantFull_wt _ _ _ _ st,
          tgA_of_since (loadConstantFull_em _ _ _ _ st)⟩))
      | exact .inr (.inr (.inr (.inl ⟨rfl, _, retRegs_zip_len ‹_› _, rfl⟩)))
      | exact .inl (callOutput_fold st _ _ (fun _ _ => rfl)).1

/-! ## The facts `ExtW` and `OracleW` -/

theorem γL_single {as : List AW} {i : V} (h : γL f ctx as [i]) : ∃ a, as = [a] ∧ γ f ctx a i :=
  holds2_one h

/-- **Extern constructors** grow the weight of the emitted instructions by at most `actorW`. -/
theorem extW_wt : ExtW f ctx apre actorW (fun s => wtA s.emitted) := by
  intro as vs term v st st' c hvs _ hc h
  rcases externCtor_sz ctx term vs st v st' h with
    he | ⟨hid, i, m, rfl, hm, he⟩ | ⟨hid, hw, -⟩ | ⟨hid, l, hl, he⟩ | ⟨hid, -⟩
  · simp only [he]; omega
  · obtain ⟨a, rfl, ha⟩ := γL_single hvs
    rw [hid] at hc
    simp only [actorW, beq_self_eq_true, ↓reduceIte] at hc
    simp only [he, wtA_push]
    have := emitW_sound hc ha hm
    omega
  · rw [hid] at hc
    simp only [actorW] at hc
    cases hc
    exact hw
  · rw [hid] at hc
    simp only [actorW] at hc
    cases hc
    simp only [he, wtA_push]
    have : szInstW (.rets l) ≤ retsW := by
      simp only [szInstW, szWords, regCount, MInst.targets, retsW, List.length_nil]
      omega
    omega
  · rw [hid] at hc
    simp only [actorW] at hc
    cases hc

/-- **Extern constructors** grow the branch targets of the emitted instructions by at most
`actorT`. -/
theorem extW_tg : ExtW f ctx apre actorT (fun s => tgA s.emitted) := by
  intro as vs term v st st' c hvs _ hc h
  rcases externCtor_sz ctx term vs st v st' h with
    he | ⟨hid, i, m, rfl, hm, he⟩ | ⟨-, -, ht⟩ | ⟨-, l, -, he⟩ | ⟨-, ht⟩
  · simp only [he]; omega
  · obtain ⟨a, rfl, ha⟩ := γL_single hvs
    rw [hid] at hc
    simp only [actorT, beq_self_eq_true, ↓reduceIte] at hc
    simp only [he, tgA_push]
    have := emitT_sound hc ha hm
    omega
  · simp only [ht]; omega
  · simp only [he, tgA_push, MInst.targets, List.length_nil]; omega
  · simp only [ht]; omega

/-- The oracle's runs keep the lowering state. -/
theorem oracle_keeps {cfg : Config} (hc : cfg.checkOverlap = false) {n : Nat} {ty : TypeId}
    {t : TermId} {as : List AW} {vs : List V} {a : AW} {s : LState} {tr : Array RuleId}
    {r : Option V} {s' : LState} {tr' : Array RuleId} (ha : aOracle t as = some a)
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) : s' = s := by
  unfold aOracle at ha
  split at ha
  · rename_i ht
    obtain rfl : t = 305 := eq_of_beq ht
    exact (os_run hc h).1
  · cases ha

/-- **The oracle's runs** do not grow the weight of the emitted instructions. -/
theorem oracleW_wt : OracleW program f ctx aOracle (fun s => wtA s.emitted) := by
  intro cfg hc n ty t as vs a s tr r s' tr' ha _ h
  rw [oracle_keeps hc ha h]
  exact Nat.le_refl _

/-- **The oracle's runs** do not grow the branch targets of the emitted instructions. -/
theorem oracleW_tg : OracleW program f ctx aOracle (fun s => tgA s.emitted) := by
  intro cfg hc n ty t as vs a s tr r s' tr' ha _ h
  rw [oracle_keeps hc ha h]
  exact Nat.le_refl _

end Backend.Proof.Cov
