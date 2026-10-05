import FV.Backend.Proof.LowerSpec
import FV.Backend.Proof.IselFlowData

/-!
# The two models of the abstract interpretation

* `flowModel`: on a statement `ii`, an abstract value with flow level `0` is *clean*
  (`Clean … false`): its registers are fresh vregs of the call or vregs of values `Prov ctx ii`
  reaches, its CLIF values are `Prov`, its instructions define `Prov` values; level `1` also
  allows the root instruction `ii` itself (`Clean … true`).
* `tlsModel`: the flag `s` means *safe* (`Safe`): no `ElfTlsGetAddr` data, and only the root or
  defining instructions; the state invariant is "nothing emitted since `s0` is an
  `ElfTlsGetAddr`".
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-! ## Joins -/

theorem foldl_join_f : ∀ (as : List FA) (b : FA) (l : Nat),
    (as.foldl FA.join b).f ≤ l ↔ b.f ≤ l ∧ ∀ a ∈ as, a.f ≤ l
  | [], b, l => by simp
  | a :: as, b, l => by
    rw [List.foldl_cons, foldl_join_f as (b.join a) l]
    simp only [FA.join, Nat.max_le, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem foldl_join_s : ∀ (as : List FA) (b : FA),
    (as.foldl FA.join b).s = true ↔ b.s = true ∧ ∀ a ∈ as, a.s = true
  | [], b => by simp
  | a :: as, b => by
    rw [List.foldl_cons, foldl_join_s as (b.join a)]
    simp only [FA.join, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem joinAll_f {as : List FA} {l : Nat} (h : (joinAll as).f ≤ l) : ∀ a ∈ as, a.f ≤ l :=
  ((foldl_join_f as FA.c0 l).mp h).2

theorem joinAll_s {as : List FA} (h : (joinAll as).s = true) : ∀ a ∈ as, a.s = true :=
  ((foldl_join_s as FA.c0).mp h).2

theorem holds2_mem {σ : Type} {γ : FA → σ → V → Prop} {s : σ} :
    ∀ {as : List FA} {vs : List V}, Holds2 γ s as vs → ∀ v ∈ vs, ∃ a ∈ as, γ a s v
  | [], [], _ => fun _ h => by cases h
  | a :: as, w :: vs, ⟨h1, h2⟩ => by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨a, List.mem_cons_self, h1⟩
    · obtain ⟨b, hb, h⟩ := holds2_mem h2 v hv
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- An atom of a list of values is an atom of one of them. -/
theorem regsInL_mem {vs : List V} {r : Reg} (h : r ∈ regsInL vs) : ∃ v ∈ vs, r ∈ v.regsIn := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    simp only [regsInL_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨w, List.mem_cons_self, h⟩
    · obtain ⟨v, hv, h⟩ := ih h; exact ⟨v, List.mem_cons_of_mem _ hv, h⟩

theorem valsInL_mem {vs : List V} {n : Nat} (h : n ∈ valsInL vs) : ∃ v ∈ vs, n ∈ v.valsIn := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    simp only [valsInL_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨w, List.mem_cons_self, h⟩
    · obtain ⟨v, hv, h⟩ := ih h; exact ⟨v, List.mem_cons_of_mem _ hv, h⟩

theorem instsInL_mem {vs : List V} {n : Nat} (h : n ∈ instsInL vs) : ∃ v ∈ vs, n ∈ v.instsIn := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    simp only [instsInL_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨w, List.mem_cons_self, h⟩
    · obtain ⟨v, hv, h⟩ := ih h; exact ⟨v, List.mem_cons_of_mem _ hv, h⟩

theorem tlsInL_mem {vs : List V} (h : tlsInL vs = true) : ∃ v ∈ vs, v.tlsIn = true := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    simp only [tlsInL_cons, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨w, List.mem_cons_self, h⟩
    · obtain ⟨v, hv, h⟩ := ih h; exact ⟨v, List.mem_cons_of_mem _ hv, h⟩

/-! ## The flow model -/

section FlowM
variable (ctx : Ctx) (ii lo : Nat)

/-- A register a statement's lowering may hold: fresh (`[lo, hi)`), not virtual, or of a
`Prov` value. -/
def RegOk (hi : Nat) (r : Reg) : Prop :=
  ∀ n c, r = .vreg n c → (lo ≤ n ∧ n < hi) ∨ Prov ctx ii n

/-- An instruction a statement's lowering may hold: the root (if `b`) or the definition of a
`Prov` value. -/
def InstOk (b : Bool) (j : Nat) : Prop :=
  (b = true ∧ j = ii) ∨ ∃ n, Prov ctx ii n ∧ ctx.defInst? n = some j

/-- A clean value. -/
def Clean (hi : Nat) (b : Bool) (v : V) : Prop :=
  (∀ r ∈ v.regsIn, RegOk ctx ii lo hi r) ∧ (∀ n ∈ v.valsIn, Prov ctx ii n) ∧
    ∀ j ∈ v.instsIn, InstOk ctx ii b j

/-- The flow meaning of an abstract value. -/
def γF (a : FA) (st : LState) (v : V) : Prop :=
  (a.f = 0 → Clean ctx ii lo st.nextVreg false v) ∧ (a.f = 1 → Clean ctx ii lo st.nextVreg true v)

variable {ctx ii lo}

theorem clean_true {hi : Nat} {v : V} (h : Clean ctx ii lo hi false v) : Clean ctx ii lo hi true v :=
  ⟨h.1, h.2.1, fun j hj => by
    rcases h.2.2 j hj with ⟨h, -⟩ | h
    · cases h
    · exact .inr h⟩

theorem clean_mono {hi hi' : Nat} (hle : hi ≤ hi') {b : Bool} {v : V} (h : Clean ctx ii lo hi b v) :
    Clean ctx ii lo hi' b v :=
  ⟨fun r hr n c hrn => by
    rcases h.1 r hr n c hrn with h | h
    · exact .inl ⟨h.1, by omega⟩
    · exact .inr h, h.2.1, h.2.2⟩

/-- `γF` at a level `≤ l ≤ 1`, as `Clean`. -/
theorem γF_clean {a : FA} {st : LState} {v : V} (h : γF ctx ii lo a st v) {l : Nat} (hl : a.f ≤ l)
    (hl1 : l ≤ 1) : Clean ctx ii lo st.nextVreg (decide (l = 1)) v := by
  rcases Nat.lt_or_ge a.f 1 with h0 | h1
  · have h0 : a.f = 0 := by omega
    have := h.1 h0
    by_cases hl' : l = 1
    · simp only [hl', decide_true]; exact clean_true this
    · simp only [hl', decide_false]; exact this
  · have h1 : a.f = 1 := by omega
    have hl' : l = 1 := by omega
    simp only [hl', decide_true]
    exact h.2 h1

/-- `Clean` at the level of a decided bound gives `γF`. -/
theorem γF_of_clean {a : FA} {st : LState} {v : V}
    (h : a.f ≤ 1 → Clean ctx ii lo st.nextVreg (decide (a.f = 1)) v) : γF ctx ii lo a st v :=
  ⟨fun h0 => (by have := h (by omega); simpa [h0] using this),
   fun h1 => (by have := h (by omega); simpa [h1] using this)⟩

theorem clean_noAtoms {hi : Nat} {b : Bool} {v : V} (h : NoAtoms v) : Clean ctx ii lo hi b v :=
  ⟨fun r hr => (by rw [h.1] at hr; cases hr), fun n hn => (by rw [h.2.1] at hn; cases hn),
   fun j hj => (by rw [h.2.2.1] at hj; cases hj)⟩

end FlowM

/-! ## The embedding -/

section Sem
variable (ctx : Ctx)

theorem sem_unData_eq {ty : TypeId} {v : V} {k : Nat} {fs : List V}
    (h : (sem ctx).unData ty v = some (k, fs)) : v = .data ty k fs := by
  cases v <;> simp [sem] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem sem_prim_eq {ty : TypeId} {n : String} {c : V} (h : (sem ctx).prim ty n = some c) :
    ∃ t, c = .ty t := by
  simp only [sem] at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨t, -, rfl⟩ := h
    exact ⟨t, rfl⟩
  · cases h

end Sem

theorem noAtoms_ty (t : CTy) : NoAtoms (.ty t) := ⟨rfl, rfl, rfl, rfl⟩
theorem noAtoms_int (i : Int) : NoAtoms (.int i) := ⟨rfl, rfl, rfl, rfl⟩
theorem noAtoms_bool (b : Bool) : NoAtoms (.bool b) := ⟨rfl, rfl, rfl, rfl⟩

theorem clean_data {ctx : Ctx} {ii lo hi : Nat} {b : Bool} {ty : TypeId} {k : Nat} {vs : List V}
    (h : ∀ v ∈ vs, Clean ctx ii lo hi b v) : Clean ctx ii lo hi b (.data ty k vs) := by
  refine ⟨fun r hr => ?_, fun n hn => ?_, fun j hj => ?_⟩
  · obtain ⟨v, hv, hr⟩ := regsInL_mem (by simpa [V.regsIn] using hr)
    exact (h v hv).1 r hr
  · obtain ⟨v, hv, hn⟩ := valsInL_mem (by simpa [V.valsIn] using hn)
    exact (h v hv).2.1 n hn
  · obtain ⟨v, hv, hj⟩ := instsInL_mem (by simpa [V.instsIn] using hj)
    exact (h v hv).2.2 j hj

theorem clean_field {ctx : Ctx} {ii lo hi : Nat} {b : Bool} {ty : TypeId} {k : Nat} {vs : List V}
    (h : Clean ctx ii lo hi b (.data ty k vs)) : ∀ v ∈ vs, Clean ctx ii lo hi b v := by
  intro v hv
  refine ⟨fun r hr => h.1 r ?_, fun n hn => h.2.1 n ?_, fun j hj => h.2.2 j ?_⟩
  · simpa [V.regsIn] using regsIn_sub_of_mem hv r hr
  · simpa [V.valsIn] using valsIn_sub_of_mem hv n hn
  · simpa [V.instsIn] using instsIn_sub_of_mem hv j hj

/-- The data of an instruction a clean `.inst` names: its values are `Prov`. -/
theorem data_prov {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {b : Bool}
    {j : Nat} (hj : InstOk ctx ii b j) {info : IInfo} (hinfo : ctx.insts[j]? = some info)
    (hroot : b = true → ∀ info, ctx.insts[ii]? = some info → ∃ c, info.clif = some c) :
    info.data.regsIn = [] ∧ info.data.instsIn = [] ∧ ∀ n ∈ info.data.valsIn, Prov ctx ii n := by
  rcases hj with ⟨hb, rfl⟩ | ⟨m, hm, hd⟩
  · obtain ⟨c, hc⟩ := hroot hb info hinfo
    have hd := instData_ok (hctx.data _ _ _ hinfo hc)
    exact ⟨hd.1, hd.2.1, fun n hn => .arg hinfo hc (hd.2.2.2 n hn)⟩
  · have hcl := hctx.defClif m j info hd hinfo
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hcl
    have hdd := instData_ok (hctx.data _ _ _ hinfo hc)
    exact ⟨hdd.1, hdd.2.1, fun n hn => .dep hm hd hinfo hc (.inl (hdd.2.2.2 n hn))⟩

section FlowModel
variable {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo}
  {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
  (htr : ctx.tryRegs = ([], [])) {lo : Nat}

include hi hc in
theorem root_clif : ∀ info', ctx.insts[ii]? = some info' → ∃ c, info'.clif = some c := by
  intro info' h'
  rw [hi] at h'; cases h'
  exact ⟨inst, hc⟩

theorem γF_le (a b : FA) (st : LState) (v : V) (hab : a.le b = true) (h : γF ctx ii lo a st v) :
    γF ctx ii lo b st v := by
  simp only [FA.le, Bool.and_eq_true, decide_eq_true_eq] at hab
  refine γF_of_clean fun hb => ?_
  exact γF_clean h (Nat.le_trans hab.1 (Nat.le_refl _)) hb

include hctx hi hc in
theorem γF_ext (st : LState) (a : FA) (term : Term) (v : V) (fs : List V)
    (hv : γF ctx ii lo a st v) (h : (sem ctx).extract term v st = .ok fs) :
    ∀ w ∈ fs, γF ctx ii lo (aext term.id a) st w := by
  have hs := externExtract_ok ctx term v st fs h
  intro w hw
  unfold aext
  split
  · rename_i hcond
    have hna := hs.c0 (by simpa [Bool.or_eq_true, List.contains_iff_mem] using hcond) w hw
    exact γF_of_clean fun _ => clean_noAtoms hna
  · split
    · rename_i _ hcond
      have hval := hs.val (by simpa [List.contains_iff_mem] using hcond) w hw
      refine γF_of_clean fun hl => ?_
      split at hl
      · rename_i hle
        have hcl := γF_clean hv (Nat.le_refl _) hle
        refine ⟨fun r hr => (by rw [hval.1] at hr; cases hr), fun n hn => ?_, fun j hj => ?_⟩
        · rcases hval.2.2.1 n hn with h1 | ⟨m, hm, j, info', c, hd, hinfo, hcl', hn'⟩
          · exact hcl.2.1 n h1
          · exact .dep (hcl.2.1 m hm) hd hinfo hcl' (.inl hn')
        · obtain ⟨m, hm, hd⟩ := hval.2.2.2 j hj
          exact .inr ⟨m, hcl.2.1 m hm, hd⟩
      · simp at hl
    · split
      · rename_i _ _ hid
        obtain ⟨i, info', rfl, hinfo, rfl⟩ := hs.idv (by simpa using hid)
        refine γF_of_clean fun hl => ?_
        split at hl
        · rename_i hle
          have hcl := γF_clean hv (Nat.le_refl _) hle
          have hinst : InstOk ctx ii (decide (a.f = 1)) i := hcl.2.2 i (by simp [V.instsIn])
          obtain ⟨h1, h2, h3⟩ := data_prov hctx hinst hinfo (fun _ => root_clif hi hc)
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact clean_noAtoms (noAtoms_ty _)
          · exact ⟨fun r hr => (by rw [h1] at hr; cases hr), h3, fun j hj => (by rw [h2] at hj; cases hj)⟩
        · simp at hl
      · split
        · rename_i _ _ _ hid
          obtain ⟨i, info', r, rfl, hinfo, hr, rfl⟩ := hs.fr (by simpa using hid)
          refine γF_of_clean fun hl => ?_
          split at hl
          · rename_i h0
            have h0 : a.f = 0 := by simpa using h0
            have hcl := hv.1 h0
            rcases hcl.2.2 i (by simp [V.instsIn]) with ⟨h, -⟩ | ⟨m, hm, hd⟩
            · cases h
            · have hcl' := hctx.defClif m i info' hd hinfo
              obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.mp hcl'
              simp only [List.mem_singleton] at hw
              subst hw
              refine ⟨fun r hr => (by simp [V.regsIn] at hr), fun n hn => ?_,
                fun j hj => (by simp [V.instsIn] at hj)⟩
              simp only [V.valsIn, List.mem_singleton] at hn
              subst hn
              exact .dep hm hd hinfo hcc (.inr (List.mem_of_head? hr))
          · simp at hl
        · refine γF_of_clean fun hl => ?_
          simp [FA.top] at hl

theorem amk_f (ty : TypeId) (k : Nat) (as : List FA) : (amk ty k as).f = (joinAll as).f := by
  unfold amk; split <;> rfl

/-- Arguments described at a level `l ≤ 1` of their join are clean at that level. -/
theorem args_clean {as : List FA} {vs : List V} {st : LState} (h : Holds2 (γF ctx ii lo) st as vs)
    (hl : (joinAll as).f ≤ 1) :
    ∀ w ∈ vs, Clean ctx ii lo st.nextVreg (decide ((joinAll as).f = 1)) w := by
  intro w hw
  obtain ⟨a, ha, hw⟩ := holds2_mem h w hw
  exact γF_clean hw (joinAll_f (Nat.le_refl _) a ha) hl

include hctx htr in
theorem γF_ctor (st : LState) (as : List FA) (vs : List V) (term : Term) (v : V) (st' : LState)
    (hvs : Holds2 (γF ctx ii lo) st as vs) (hlo : lo ≤ st.nextVreg)
    (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γF ctx ii lo (actor term.id as) st' v ∧ lo ≤ st'.nextVreg := by
  have hok := externCtor_ok ctx term vs st v st' h
  refine ⟨?_, Nat.le_trans hlo hok.vreg⟩
  unfold actor
  split
  · exact γF_of_clean fun hl => by simp at hl
  · rename_i hid
    refine γF_of_clean fun hl => ?_
    have hargs := args_clean hvs hl
    refine ⟨fun r hr => ?_, fun n hn => ?_, fun j hj => ?_⟩
    · rcases hok.regs r hr with h1 | ⟨n, c, rfl, h2, h3⟩ | ⟨x, hx, h4⟩ | h5 | h6 | h7 | h7
      · obtain ⟨w, hw, hrw⟩ := regsInL_mem h1
        intro n c hrn
        rcases (hargs w hw).1 r hrw n c hrn with h | h
        · exact .inl ⟨h.1, Nat.lt_of_lt_of_le h.2 hok.vreg⟩
        · exact .inr h
      · intro n' c' he
        cases he
        exact .inl ⟨Nat.le_trans hlo h2, h3⟩
      · obtain ⟨w, hw, hxw⟩ := valsInL_mem hx
        have hp := (hargs w hw).2.1 x hxw
        have := hctx.valueReg x r h4
        subst this
        intro n c he
        cases he
        exact .inr hp
      · intro n c he; exact absurd he (h5 n c)
      · exact absurd (beq_iff_eq.mpr h6) hid
      · rw [htr] at h7; cases h7
      · rw [htr] at h7; cases h7
    · obtain ⟨w, hw, hnw⟩ := valsInL_mem (hok.vals n hn)
      exact (hargs w hw).2.1 n hnw
    · obtain ⟨w, hw, hjw⟩ := instsInL_mem (hok.insts j hj)
      exact (hargs w hw).2.2 j hjw

/-- **The flow model** of a statement `ii`'s lowering from a state whose counter is `lo`. -/
def flowModel : Model (sem ctx) false where
  γ := γF ctx ii lo
  Is := fun st => lo ≤ st.nextVreg
  Rs := fun s s' => s.nextVreg ≤ s'.nextVreg
  rs_refl := fun _ => Nat.le_refl _
  rs_trans := fun _ _ _ h1 h2 => Nat.le_trans h1 h2
  rs_ctor := fun term vs s v s' h => (externCtor_ok ctx term vs s v s' h).vreg
  top := fun _ _ => γF_of_clean fun hl => by simp [FA.top] at hl
  le := γF_le
  mono := fun _ _ _ _ h hv => ⟨fun h0 => clean_mono h (hv.1 h0), fun h1 => clean_mono h (hv.2 h1)⟩
  int := fun _ _ _ => γF_of_clean fun _ => clean_noAtoms (noAtoms_int _)
  bool := fun _ _ => γF_of_clean fun _ => clean_noAtoms (noAtoms_bool _)
  prim := fun _ _ _ _ h => by
    obtain ⟨t, rfl⟩ := sem_prim_eq ctx h
    exact γF_of_clean fun _ => clean_noAtoms (noAtoms_ty _)
  mkd := fun st ty k as vs h => by
    refine γF_of_clean fun hl => ?_
    rw [amk_f] at hl ⊢
    exact clean_data (args_clean h hl)
  un := fun st a ty v k fs hv hu => by
    have := sem_unData_eq ctx hu
    subst this
    intro w hw
    exact γF_of_clean fun hl => clean_field (γF_clean hv (Nat.le_refl _) hl) w hw
  ext := γF_ext hctx hi hc
  ctor := fun st as vs term v st' hvs hIs _ h => γF_ctor hctx htr st as vs term v st' hvs hIs h

end FlowModel

/-! ## The TLS model -/

section TlsM
variable (ctx : Ctx) (root : Nat)

/-- A safe value: no `ElfTlsGetAddr` data, only the root or defining instructions. -/
def Safe (v : V) : Prop :=
  v.tlsIn = false ∧ ∀ j ∈ v.instsIn, j = root ∨ ∃ n, ctx.defInst? n = some j

/-- The TLS meaning of an abstract value. -/
def γT (a : FA) (_st : LState) (v : V) : Prop := a.s = true → Safe ctx root v

/-- Nothing emitted since `s0` is an `ElfTlsGetAddr`. -/
def NoTlsSince (s0 st : LState) : Prop :=
  ∃ ms : List MInst, st.emitted = s0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, ¬ IsTls m

variable {ctx root}

theorem safe_noAtoms {v : V} (h : NoAtoms v) : Safe ctx root v :=
  ⟨h.2.2.2, fun j hj => by rw [h.2.2.1] at hj; cases hj⟩

theorem actor_s (id : TermId) (as : List FA) : (actor id as).s = (joinAll as).s := by
  unfold actor; split <;> rfl

theorem args_safe {as : List FA} {vs : List V} {st : LState} (h : Holds2 (γT ctx root) st as vs)
    (hs : (joinAll as).s = true) : ∀ w ∈ vs, Safe ctx root w := by
  intro w hw
  obtain ⟨a, ha, hw⟩ := holds2_mem h w hw
  exact hw (joinAll_s hs a ha)

theorem safe_tlsInL {vs : List V} (h : ∀ w ∈ vs, Safe ctx root w) : tlsInL vs = false := by
  cases ht : tlsInL vs with
  | false => rfl
  | true =>
    obtain ⟨w, hw, hwt⟩ := tlsInL_mem ht
    rw [(h w hw).1] at hwt; cases hwt

variable (hroot : ∀ j info, (j = root ∨ ∃ n, ctx.defInst? n = some j) → ctx.insts[j]? = some info →
  info.data.tlsIn = false ∧ info.data.instsIn = [])

include hroot in
theorem γT_ext (st : LState) (a : FA) (term : Term) (v : V) (fs : List V)
    (hv : γT ctx root a st v) (h : (sem ctx).extract term v st = .ok fs) :
    ∀ w ∈ fs, γT ctx root (aext term.id a) st w := by
  have hs := externExtract_ok ctx term v st fs h
  intro w hw hsw
  unfold aext at hsw
  split at hsw
  · rename_i hcond
    exact safe_noAtoms (hs.c0 (by simpa [Bool.or_eq_true, List.contains_iff_mem] using hcond) w hw)
  · split at hsw
    · rename_i _ hcond
      have hval := hs.val (by simpa [List.contains_iff_mem] using hcond) w hw
      refine ⟨hval.2.1, fun j hj => ?_⟩
      obtain ⟨m, -, hd⟩ := hval.2.2.2 j hj
      exact .inr ⟨m, hd⟩
    · split at hsw
      · rename_i _ _ hid
        obtain ⟨i, info', rfl, hinfo, rfl⟩ := hs.idv (by simpa using hid)
        have hsafe := hv hsw
        have hroot' := hroot i info' (hsafe.2 i (by simp [V.instsIn])) hinfo
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · exact safe_noAtoms (noAtoms_ty _)
        · exact ⟨hroot'.1, fun j hj => by rw [hroot'.2] at hj; cases hj⟩
      · split at hsw
        · rename_i _ _ _ hid
          obtain ⟨i, info', r, rfl, hinfo, hr, rfl⟩ := hs.fr (by simpa using hid)
          simp only [List.mem_singleton] at hw
          subst hw
          exact ⟨rfl, fun j hj => by simp [V.instsIn] at hj⟩
        · simp [FA.top] at hsw

theorem γT_ctor (s0 : LState) (st : LState) (as : List FA) (vs : List V) (term : Term) (v : V)
    (st' : LState) (hvs : Holds2 (γT ctx root) st as vs) (hIs : NoTlsSince s0 st)
    (hpre : apre true term.id as = true) (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γT ctx root (actor term.id as) st' v ∧ NoTlsSince s0 st' := by
  have hok := externCtor_ok ctx term vs st v st' h
  refine ⟨fun hs => ?_, ?_⟩
  · rw [actor_s] at hs
    have hargs := args_safe hvs hs
    refine ⟨?_, fun j hj => ?_⟩
    · cases ht : v.tlsIn with
      | false => rfl
      | true => have := hok.tls ht; rw [safe_tlsInL hargs] at this; cases this
    · obtain ⟨w, hw, hjw⟩ := instsInL_mem (hok.insts j hj)
      exact (hargs w hw).2 j hjw
  · obtain ⟨ms0, h0, h1⟩ := hIs
    obtain ⟨ms, h2, h3⟩ := hok.emit
    refine ⟨ms0 ++ ms, by rw [h2, h0]; simp, fun m hm hmt => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact h1 m hm hmt
    · obtain ⟨hid, htls⟩ := (h3 m hm).2 hmt
      simp only [apre, Bool.not_true, Bool.false_or, hid, bne_self_eq_false] at hpre
      have hall : ∀ a ∈ as, a.s = true := fun a ha => by
        simpa using List.all_eq_true.mp hpre a ha
      have : tlsInL vs = false := by
        cases ht : tlsInL vs with
        | false => rfl
        | true =>
          obtain ⟨w, hw, hwt⟩ := tlsInL_mem ht
          obtain ⟨a, ha, hwa⟩ := holds2_mem hvs w hw
          rw [(hwa (hall a ha)).1] at hwt; cases hwt
      rw [this] at htls; cases htls

/-- **The TLS model** of a run from `s0` with root instruction `root`. -/
def tlsModel (s0 : LState) : Model (sem ctx) true where
  γ := γT ctx root
  Is := NoTlsSince s0
  Rs := fun _ _ => True
  rs_refl := fun _ => trivial
  rs_trans := fun _ _ _ _ _ => trivial
  rs_ctor := fun _ _ _ _ _ _ => trivial
  top := fun _ _ h => by simp [FA.top] at h
  le := fun a b _ _ hab ha hb => by
    simp only [FA.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hab
    rcases hab.2 with h | h
    · rw [h] at hb; cases hb
    · exact ha h
  mono := fun _ _ _ _ _ h => h
  int := fun _ _ _ _ => safe_noAtoms (noAtoms_int _)
  bool := fun _ _ _ => safe_noAtoms (noAtoms_bool _)
  prim := fun _ _ _ _ h _ => by
    obtain ⟨t, rfl⟩ := sem_prim_eq ctx h
    exact safe_noAtoms (noAtoms_ty _)
  mkd := fun st ty k as vs h hs => by
    unfold amk at hs
    split at hs
    · simp at hs
    · rename_i hnt
      have hargs := args_safe h hs
      refine ⟨?_, fun j hj => ?_⟩
      · show (V.data ty k vs).tlsIn = false
        simp only [V.tlsIn, Bool.or_eq_false_iff]
        exact ⟨by simpa using hnt, safe_tlsInL hargs⟩
      · change j ∈ (V.data ty k vs).instsIn at hj
        obtain ⟨w, hw, hjw⟩ := instsInL_mem (by simpa [V.instsIn] using hj)
        exact (hargs w hw).2 j hjw
  un := fun st a ty v k fs hv hu => by
    have := sem_unData_eq ctx hu
    subst this
    intro w hw hs
    have hsafe := hv hs
    refine ⟨?_, fun j hj => hsafe.2 j (by simpa [V.instsIn] using instsIn_sub_of_mem hw j hj)⟩
    cases ht : w.tlsIn with
    | false => rfl
    | true =>
      have := hsafe.1
      simp only [V.tlsIn, Bool.or_eq_false_iff] at this
      rw [tlsIn_of_mem hw ht] at this; simp at this
  ext := γT_ext hroot
  ctor := fun st as vs term v st' hvs hIs hpre h => γT_ctor s0 st as vs term v st' hvs hIs hpre h

end TlsM

end Backend.Proof.Driver
