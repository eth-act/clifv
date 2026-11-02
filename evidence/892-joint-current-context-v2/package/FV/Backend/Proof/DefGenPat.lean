import FV.Backend.Proof.DefGenSem

/-!
# Definedness of the ISLE runs: soundness of the abstract patterns

`aPat_sound`: matching a pattern against a value an abstract value describes extends the
environment, and the abstract environment `aPat` computes describes the result. Fields of a
flag/side-effect value matched by simple patterns get relational descriptions (`relField`):
an instruction field holds once the earlier instruction fields are emitted, a result field
once all are; `relField_sound` proves them from `SeqOk` when the earlier binders are bound to
their fields. The extern extractors are a hypothesis (`ExtOK`).
-/

namespace Backend.Proof.DefGen

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Kill
  Backend.Proof.DefRun Isle Isle.Aarch64 Isle.Interp

variable {c : SC}

/-- **The extern extractors' transfer** (`aext`) is sound. -/
def ExtOK (c : SC) (ctx : Ctx) : Prop :=
  ∀ (term : Term) (a : A) (e : AEnv) (env : Isle.Interp.Env V) (D : Nat → Prop) (v : V)
    (s : LState) (fs : List V), EnvOK c D env e → γ c a D env v →
    externExtract ctx term v s = .ok fs → ∀ f ∈ fs, γ c (aext e term.id a) D env f

/-- Abstract values describe values position by position (`top` past the end). -/
def HoldsP (c : SC) (D : Nat → Prop) (env : Isle.Interp.Env V) (as : List A) (vs : List V) : Prop :=
  ∀ (i : Nat) v, vs[i]? = some v → γ c (as.getD i .top) D env v

theorem HoldsP.ext {D : Nat → Prop} {env env' : Isle.Interp.Env V} (he : Ext env env')
    {as : List A} {vs : List V} (h : HoldsP c D env as vs) : HoldsP c D env' as vs :=
  fun i v hv => γ_ext _ he (h i v hv)

theorem HoldsP.tail {D : Nat → Prop} {env : Isle.Interp.Env V} {as : List A} {v : V} {vs : List V}
    (h : HoldsP c D env as (v :: vs)) : γ c (as.headD .top) D env v ∧ HoldsP c D env as.tail vs := by
  refine ⟨?_, fun i w hw => ?_⟩
  · have := h 0 v rfl
    cases as <;> simpa using this
  · have := h (i + 1) w (by simpa using hw)
    cases as <;> simpa using this

theorem HoldsP.of_γL {D : Nat → Prop} {env : Isle.Interp.Env V} :
    ∀ {as : List A} {vs : List V}, γL c as D env vs → HoldsP c D env as vs
  | [], [], _ => fun i v hv => by simp at hv
  | a :: as, w :: vs, h => by
    intro i v hv
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv; exact h.1
    | succ i => simpa using HoldsP.of_γL h.2 i v (by simpa using hv)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem HoldsP.replicate {D : Nat → Prop} {env : Isle.Interp.Env V} {a : A} {vs : List V}
    (h : ∀ v ∈ vs, γ c a D env v) (n : Nat) : HoldsP c D env (List.replicate n a) vs := by
  intro i v hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split
  · exact h v (List.mem_of_getElem? hv)
  · trivial

theorem HoldsP.top {D : Nat → Prop} {env : Isle.Interp.Env V} (n : Nat) (vs : List V) :
    HoldsP c D env (List.replicate n .top) vs :=
  HoldsP.replicate (a := .top) (fun _ _ => trivial) n

/-! ## Relational fields -/

theorem DD_nil_iff {D : Nat → Prop} {n : Nat} : DD c D [] n → D n := by
  intro h; rcases h with h | ⟨_, m, hm, _⟩
  · exact h
  · cases hm

/-- The instructions of positions `idx` all build, with a property. -/
theorem mapM_filterMap {P : MInst → Prop} {fs : List V} :
    ∀ (idx : List Nat), (∀ i ∈ idx, ∀ w, fs[i]? = some w → ∃ m, MInst.ofV w = some m ∧ P m) →
      ∃ ms, (idx.filterMap fun i => fs[i]?).mapM MInst.ofV = some ms ∧ ∀ m ∈ ms, P m
  | [], _ => ⟨[], rfl, fun _ h => by cases h⟩
  | i :: idx, h => by
    obtain ⟨ms, hms, hP⟩ := mapM_filterMap idx fun j hj => h j (List.mem_cons_of_mem _ hj)
    rw [List.filterMap_cons]
    cases hf : fs[i]? with
    | none => exact ⟨ms, hms, hP⟩
    | some w =>
      obtain ⟨m, hm, hPm⟩ := h i List.mem_cons_self w hf
      refine ⟨m :: ms, ?_, ?_⟩
      · simp [List.mapM_cons, hm, hms]
      · intro m' hm'
        rcases List.mem_cons.mp hm' with rfl | hm'
        · exact hPm
        · exact hP m' hm'

/-- The earlier binders of position `j` are bound to their fields. -/
def BindersAt (ps : List Pattern) (fs : List V) (env : Isle.Interp.Env V) (idx : List Nat) : Prop :=
  ∀ i ∈ idx, ∀ y w, (ps[i]?.bind binder) = some y → fs[i]? = some w → env[y]? = some (some w)

theorem defsIn_all {D' : Nat → Prop} {ps : List Pattern} {fs : List V} {env : Isle.Interp.Env V}
    {idx : List Nat} (hb : BindersAt ps fs env idx)
    (hs : ((idx.map fun i => ps[i]?.bind binder).all (·.isSome)) = true)
    (hd : ∀ y ∈ (idx.map fun i => ps[i]?.bind binder).filterMap id, DefsIn c D' env y) :
    ∃ ms, (idx.filterMap fun i => fs[i]?).mapM MInst.ofV = some ms ∧
      ∀ m ∈ ms, ∀ n ∈ defVregs m, c.lo ≤ n → D' n := by
  refine mapM_filterMap idx fun i hi w hw => ?_
  have hsome := List.all_eq_true.mp hs _ (List.mem_map_of_mem hi)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
  have hyw := hb i hi y w hy hw
  have hy' : y ∈ (idx.map fun i => ps[i]?.bind binder).filterMap id :=
    List.mem_filterMap.mpr ⟨some y, List.mem_map.mpr ⟨i, hi, hy⟩, rfl⟩
  exact hd y hy' w hyw

theorem DD_le {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {ms : List MInst}
    (hms : ∀ m ∈ ms, ∀ n ∈ defVregs m, c.lo ≤ n → D' n) : ∀ n, DD c D ms n → D' n := by
  intro n h
  rcases h with h | ⟨h1, m, hm, h2⟩
  · exact hD n h
  · exact hms m hm n h2 h1

/-- **The relational field descriptions hold** when the earlier binders are bound to their
fields. -/
theorem relField_sound {z : Bool} {D : Nat → Prop} {sh : List SK} {ps : List Pattern}
    {fs : List V} (hseq : SeqOk c z D fs sh) {j : Nat} {f : V} (hf : fs[j]? = some f) {s : SK}
    (hs : sh[j]? = some s) {env : Isle.Interp.Env V}
    (hb : BindersAt ps fs env (instIdx sh j)) : γ c (relField z sh ps j s) D env f := by
  obtain ⟨ho, hi, hr⟩ := hseq j f hf
  cases s with
  | i =>
    simp only [relField, instBinders]
    by_cases hnil : ((instIdx sh j).map fun i => ps[i]?.bind binder).isEmpty = true
    · simp only [hnil, ↓reduceIte]
      have hidx : instIdx sh j = [] := by simpa using hnil
      have := hi hs [] (by simp [earlier, hidx])
      exact MIok_mono (fun _ h => DD_nil_iff h) this
    · simp only [hnil, ↓reduceIte, Bool.false_eq_true]
      by_cases hall : (((instIdx sh j).map fun i => ps[i]?.bind binder).all (·.isSome)) = true
      · simp only [hall, ↓reduceIte]
        intro D' hD' hd
        obtain ⟨ms, hms, hdef⟩ := defsIn_all hb hall hd
        exact MIok_mono (DD_le hD' hdef) (hi hs ms hms)
      · simp only [hall, ↓reduceIte, Bool.false_eq_true]; trivial
  | r =>
    simp only [relField, instBinders]
    by_cases hcond : (instIdx sh sh.length == instIdx sh j &&
        ((instIdx sh j).map fun i => ps[i]?.bind binder).all (·.isSome)) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨heq, hall⟩ := hcond
      by_cases hnil : ((instIdx sh j).map fun i => ps[i]?.bind binder).isEmpty = true
      · simp only [hnil, ↓reduceIte]
        have hidx : instIdx sh j = [] := by simpa using hnil
        have := hr hs [] (by simp [earlier, heq, hidx])
        exact Cl_mono (fun _ h => DD_nil_iff h) id id this
      · simp only [hnil, ↓reduceIte, Bool.false_eq_true]
        intro D' hD' hd
        obtain ⟨ms, hms, hdef⟩ := defsIn_all hb hall hd
        have hms' : (earlier fs sh sh.length).mapM MInst.ofV = some ms := by
          simpa [earlier, heq] using hms
        exact Cl_mono (DD_le hD' hdef) id id (hr hs ms hms')
    · simp only [hcond, ↓reduceIte, Bool.false_eq_true]; trivial
  | o =>
    simp only [relField]
    exact ho hs

/-- The relational descriptions of a clean value's fields. -/
theorem relField_cl {z : Bool} {D : Nat → Prop} {sh : List SK} {ps : List Pattern} {j : Nat}
    {s : SK} {env : Isle.Interp.Env V} {f : V} (h : Cl c false z D f) :
    γ c (relField z sh ps j s) D env f := by
  cases s with
  | i =>
    simp only [relField]
    split
    · exact Cl_MIok h
    · split
      · intro D' hD' _
        exact Cl_MIok (Cl_mono hD' id id h)
      · trivial
  | r =>
    simp only [relField]
    split
    · split
      · exact h
      · intro D' hD' _
        exact Cl_mono hD' id id h
    · trivial
  | o =>
    simp only [relField]
    exact Cl_mono (fun _ h => h) id (fun _ => rfl) h

/-! ## Fields of a matched value -/

section Aun
variable {D : Nat → Prop} {env : Isle.Interp.Env V} {e : AEnv}

theorem unData_eq' {ctx : Ctx} {ty : TypeId} {v : V} {k : Nat} {fs : List V}
    (h : (sem ctx).unData ty v = some (k, fs)) : v = .data ty k fs := by
  cases v <;> simp [sem] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem γ_getD {D : Nat → Prop} {env : Isle.Interp.Env V} {l : List A} {f : V}
    (h : ∀ x ∈ l, γ c x D env f) (i : Nat) : γ c (l.getD i .top) D env f := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : l[i]? with
  | none => trivial
  | some x => exact h x (List.mem_of_getElem? hl)

/-- **The fields `aun` gives**: positionally described, or the relational descriptions of a
flag/side-effect value's fields matched by simple patterns. -/
theorem aun_sound (he : EnvOK c D env e) {a : A} {ty k k0 : Nat} {enum : Bool} {fs : List V}
    {ps : List Pattern} (hv : γ c a D env (.data ty k0 fs)) (hk0 : enum = true → k0 = k) :
    HoldsP c D env (aun e a ty k enum ps) fs ∨
      (∃ z sh, aun e a ty k enum ps =
          (List.range sh.length).map (fun j => relField z sh ps j (sh.getD j .o)) ∧
        (∀ q ∈ ps, simplePat q = true) ∧ fs.length = sh.length ∧ SeqOk c z D fs sh) := by
  have hr := res_sound he F a hv
  unfold aun
  split
  · rename_i b z hra
    rw [hra] at hr
    exact .inl (HoldsP.replicate (a := .cl b z) (fun f hf => (Cl_data_iff.mp hr) f hf) _)
  · rename_i τ k' fs' hra
    rw [hra] at hr
    obtain ⟨vs, he', hl⟩ := hr
    simp only [V.data.injEq] at he'
    obtain ⟨-, hkk, rfl⟩ := he'
    by_cases hk : k = k'
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte]
      exact .inl (HoldsP.of_γL hl)
    · have : (k == k') = false := by simpa using hk
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact .inl (HoldsP.top _ _)
  · rename_i τ z hra
    rw [hra] at hr
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨hen, rfl⟩ := hcond
      obtain rfl := hk0 hen
      split
      · rename_i sh hsh
        have hP := (PT_flag (flagShape_mem hsh)).mp hr
        split
        · rename_i hsimple
          rcases hP with hcl | ⟨k'', fs'', sh', he'', hsh', hlen, hseq⟩
          · refine .inl fun i f hf => γ_getD (fun x hx => ?_) i
            obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
            exact relField_cl (Cl_data_iff.mp hcl f (List.mem_of_getElem? hf))
          · cases he''
            rw [hsh] at hsh'
            cases hsh'
            exact .inr ⟨z, sh, rfl, by simpa using hsimple, hlen, hseq⟩
        · exact .inl (HoldsP.top _ _)
      · split
        · rename_i cs hcs
          have hτ := crShape_eq hcs
          subst hτ
          refine .inl fun i f hf => ?_
          rw [List.getD_eq_getElem?_getD, List.getElem?_map]
          cases hci : cs[i]? with
          | none => trivial
          | some b =>
            simp only [Option.map_some, Option.getD_some]
            rcases PT_cr.mp hr with hcl | ⟨k'', fs'', cs', he'', hcs', hlen, hcr⟩
            · have hf' := Cl_data_iff.mp hcl f (List.mem_of_getElem? hf)
              split
              · exact (PT_flag (by simp [flagTys])).mpr (.inl hf')
              · exact hf'
            · cases he''
              rw [hcs] at hcs'
              cases hcs'
              obtain ⟨h1, h2⟩ := hcr i f b hf hci
              cases b
              · exact h2 rfl
              · exact (PT_flag (by simp [flagTys])).mpr (h1 rfl)
        · exact .inl (HoldsP.top _ _)
    · exact .inl (HoldsP.top _ _)
  · exact .inl (HoldsP.top _ _)

end Aun

/-! ## Simple patterns on a flag/side-effect value -/

theorem aPat_wildcard (p : Program) (a : A) (ty : TypeId) (e : AEnv) :
    aPat p a (.wildcard ty) e = some e := rfl

theorem aPat_bind (p : Program) (a : A) (ty : TypeId) (x : Nat) (sub : Pattern) (e : AEnv) :
    aPat p a (.bind ty x sub) e = match e[x]? with
      | some none => aPat p a sub (e.set x (some a))
      | _ => none := by
  rw [aPat.eq_1]; rfl

theorem aPatArgs_cons (p : Program) (as : List A) (q : Pattern) (qs : List Pattern) (e : AEnv) :
    aPatArgs p as (q :: qs) e = match aPat p (as.headD .top) q e with
      | some e' => aPatArgs p as.tail qs e'
      | none => none := by
  rw [aPatArgs.eq_1]; rfl

theorem aPatArgs_nil (p : Program) (as : List A) (e : AEnv) : aPatArgs p as [] e = some e := by
  rw [aPatArgs.eq_2]

section Rel
variable {p : Program} {ctx : Ctx} {D : Nat → Prop}

theorem instIdx_sub {sh : List SK} {j : Nat} : ∀ i ∈ instIdx sh j, i ∈ List.range j :=
  fun i hi => (List.mem_filter.mp hi).1

theorem BindersAt.mono {ps : List Pattern} {fs : List V} {env : Isle.Interp.Env V}
    {idx idx' : List Nat} (h : BindersAt ps fs env idx) (hs : ∀ i ∈ idx', i ∈ idx) :
    BindersAt ps fs env idx' := fun i hi => h i (hs i hi)

theorem BindersAt.ext {ps : List Pattern} {fs : List V} {env env' : Isle.Interp.Env V}
    {idx : List Nat} (h : BindersAt ps fs env idx) (he : Ext env env') :
    BindersAt ps fs env' idx := fun i hi y w hy hw => he y w (h i hi y w hy hw)

/-- **Simple patterns on the fields of a flag/side-effect value**, from position `pre` on, with
the binders of the earlier positions bound to their fields. -/
theorem aPatArgs_rel {z : Bool} {sh : List SK} {ps : List Pattern} {fs : List V} {s : LState}
    (hseq : SeqOk c z D fs sh) (hlen : fs.length = sh.length) :
    ∀ (qs : List Pattern) (pre : Nat) {e e' : AEnv} {env env' : Isle.Interp.Env V},
      qs = ps.drop pre → (∀ q ∈ qs, simplePat q = true) →
      aPatArgs p (((List.range sh.length).map fun j => relField z sh ps j (sh.getD j .o)).drop pre)
        qs e = some e' →
      matchArgs p (sem ctx) s qs (fs.drop pre) env = .ok (some env') →
      EnvOK c D env e → BindersAt ps fs env (List.range pre) →
      EnvOK c D env' e' ∧ Ext env env'
  | [], pre, e, e', env, env', _, _, ha, hm, he, _ => by
    rw [aPatArgs_nil, Option.some.injEq] at ha
    subst ha
    cases hd : fs.drop pre with
    | nil =>
      rw [hd, matchArgs.eq_1] at hm
      cases hm
      exact ⟨he, Ext.refl _⟩
    | cons g gs =>
      rw [hd] at hm
      rw [matchArgs.eq_3] at hm
      all_goals first | cases hm | simp_all
  | q :: qs, pre, e, e', env, env', hq, hsimp, ha, hm, he, hb => by
    have hpre : ps[pre]? = some q := by
      have h0 := congrArg (·[0]?) hq
      simp only [List.getElem?_cons_zero, List.getElem?_drop, Nat.add_zero] at h0
      exact h0.symm
    have hq' : qs = ps.drop (pre + 1) := by
      rw [← List.drop_drop, ← hq]; rfl
    cases hd : fs.drop pre with
    | nil =>
      rw [hd] at hm
      rw [matchArgs.eq_3] at hm
      all_goals first | cases hm | simp_all
    | cons g gs =>
      rw [hd, matchArgs.eq_2] at hm
      have hg : fs[pre]? = some g := by
        have := congrArg (·[0]?) hd
        simpa using this
      have hgs : gs = fs.drop (pre + 1) := by
        rw [← List.drop_drop, hd]; rfl
      have hlt : pre < sh.length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hg).1
      have hhead : (((List.range sh.length).map fun j => relField z sh ps j (sh.getD j .o)).drop
          pre).headD .top = relField z sh ps pre (sh.getD pre .o) := by
        rw [List.headD_eq_head?_getD, List.head?_drop]
        simp [List.getElem?_range hlt]
      have htail : (((List.range sh.length).map fun j => relField z sh ps j (sh.getD j .o)).drop
          pre).tail = ((List.range sh.length).map fun j => relField z sh ps j (sh.getD j .o)).drop
          (pre + 1) := by
        rw [List.tail_drop]
      rw [aPatArgs_cons, hhead, htail] at ha
      have hs : sh[pre]? = some (sh.getD pre .o) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      have hrel : γ c (relField z sh ps pre (sh.getD pre .o)) D env g :=
        relField_sound hseq hg hs (hb.mono instIdx_sub)
      have hsq := hsimp q List.mem_cons_self
      cases q with
      | wildcard ty =>
        rw [aPat_wildcard] at ha
        simp only at ha
        rw [matchPat.eq_6] at hm
        simp only [bind, Except.bind, pure, Except.pure] at hm
        refine aPatArgs_rel hseq hlen qs (pre + 1) hq' (fun q hq => hsimp q (List.mem_cons_of_mem _ hq))
          ha (hgs ▸ hm) he ?_
        intro i hi y w hy hw
        rcases Nat.lt_succ_iff_lt_or_eq.mp (List.mem_range.mp hi) with hi | rfl
        · exact hb i (List.mem_range.mpr hi) y w hy hw
        · rw [hpre] at hy; simp [binder] at hy
      | bind ty x sub =>
        cases sub with
        | wildcard ty' =>
          cases hx : e[x]? with
          | none => rw [aPat_bind, hx] at ha; simp at ha
          | some o =>
            cases o with
            | some _ => rw [aPat_bind, hx] at ha; simp at ha
            | none =>
              rw [aPat_bind, hx, aPat_wildcard] at ha
              rw [matchPat.eq_1] at hm
              split at hm
              · rw [matchPat.eq_6] at hm
                simp only [bind, Except.bind, pure, Except.pure] at hm
                obtain ⟨hxe, -, he1⟩ := he.bind hx hrel
                have hext := Ext.set hxe g
                have hB : BindersAt ps fs (env.set! x (some g)) (List.range (pre + 1)) := by
                  intro i hi y w hy hw
                  rcases Nat.lt_succ_iff_lt_or_eq.mp (List.mem_range.mp hi) with hi | rfl
                  · exact hext y w (hb i (List.mem_range.mpr hi) y w hy hw)
                  · rw [hpre] at hy
                    simp only [Option.bind_some, binder, Option.some.injEq] at hy
                    subst hy
                    rw [hg] at hw
                    cases hw
                    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
                    have : x < env.size := by
                      rcases Nat.lt_or_ge x env.size with h | h
                      · exact h
                      · rw [Array.getElem?_eq_none h] at hxe; cases hxe
                    simp [this]
                obtain ⟨he2, hext2⟩ := aPatArgs_rel hseq hlen qs (pre + 1) hq'
                  (fun q hq => hsimp q (List.mem_cons_of_mem _ hq)) ha (hgs ▸ hm) he1 hB
                exact ⟨he2, hext.trans hext2⟩
              · cases hm
        | _ => simp [simplePat] at hsq
      | _ => simp [simplePat] at hsq

end Rel

/-! ## Patterns -/

section Pat
variable {p : Program} {ctx : Ctx} {D : Nat → Prop}

theorem termOf_some {t : TermId} {term : Term} (h : termOf p t = .ok term) : p.term? t = some term := by
  unfold termOf at h
  split at h
  · cases h; assumption
  · cases h

mutual
/-- **Pattern soundness.** -/
theorem aPat_sound (hX : ExtOK c ctx) : ∀ (q : Pattern) (a : A) {e e' : AEnv} {v : V}
    {env env' : Isle.Interp.Env V} {s : LState},
    aPat p a q e = some e' → matchPat p (sem ctx) s q v env = .ok (some env') →
    EnvOK c D env e → γ c a D env v → EnvOK c D env' e' ∧ Ext env env'
  | .bind ty x sub, a, e, e', v, env, env', s, ha, hm, he, hv => by
    rw [aPat_bind] at ha
    split at ha
    · rename_i hx
      rw [matchPat.eq_1] at hm
      split at hm
      · obtain ⟨hxe, -, he1⟩ := he.bind hx hv
        have hext := Ext.set hxe v
        obtain ⟨he2, hext2⟩ := aPat_sound hX sub a ha hm he1 (γ_ext a hext hv)
        exact ⟨he2, hext.trans hext2⟩
      · cases hm
    · cases ha
  | .var ty x, a, e, e', v, env, env', s, ha, hm, he, hv => by
    have : e' = e := by rw [aPat.eq_4] at ha <;> first | (simp at ha; exact ha.symm) | simp_all
    subst this
    rw [matchPat.eq_2] at hm
    split at hm
    · simp only [pure, Except.pure, Except.ok.injEq] at hm
      split at hm
      · cases hm; exact ⟨he, Ext.refl _⟩
      · cases hm
    · cases hm
  | .constBool ty b, a, e, e', v, env, env', s, ha, hm, he, hv => by
    have : e' = e := by rw [aPat.eq_4] at ha <;> first | (simp at ha; exact ha.symm) | simp_all
    subst this
    rw [matchPat.eq_3] at hm
    simp only [pure, Except.pure, Except.ok.injEq] at hm
    split at hm
    · cases hm; exact ⟨he, Ext.refl _⟩
    · cases hm
  | .constInt ty i, a, e, e', v, env, env', s, ha, hm, he, hv => by
    have : e' = e := by rw [aPat.eq_4] at ha <;> first | (simp at ha; exact ha.symm) | simp_all
    subst this
    rw [matchPat.eq_4] at hm
    simp only [pure, Except.pure, Except.ok.injEq] at hm
    split at hm
    · cases hm; exact ⟨he, Ext.refl _⟩
    · cases hm
  | .constPrim ty nm, a, e, e', v, env, env', s, ha, hm, he, hv => by
    have : e' = e := by rw [aPat.eq_4] at ha <;> first | (simp at ha; exact ha.symm) | simp_all
    subst this
    rw [matchPat.eq_5] at hm
    split at hm
    · simp only [pure, Except.pure, Except.ok.injEq] at hm
      split at hm
      · cases hm; exact ⟨he, Ext.refl _⟩
      · cases hm
    · cases hm
  | .wildcard ty, a, e, e', v, env, env', s, ha, hm, he, hv => by
    rw [aPat_wildcard, Option.some.injEq] at ha
    subst ha
    rw [matchPat.eq_6] at hm
    cases hm
    exact ⟨he, Ext.refl _⟩
  | .and ty ps, a, e, e', v, env, env', s, ha, hm, he, hv => by
    rw [aPat.eq_2] at ha
    rw [matchPat.eq_7] at hm
    exact aPatAll_sound hX ps a ha hm he hv
  | .term ty t args, a, e, e', v, env, env', s, ha, hm, he, hv => by
    rw [matchPat.eq_8] at hm
    cases ht : termOf p t with
    | error err => rw [ht] at hm; cases hm
    | ok term =>
      rw [ht] at hm
      simp only [bind, Except.bind] at hm
      rw [aPat.eq_3, termOf_some ht] at ha
      simp only at ha
      cases hk : term.kind with
      | enumVariant k =>
        rw [hk] at hm ha
        simp only at hm ha
        split at hm
        · rename_i k' fs hu
          split at hm
          · rename_i hkk
            have hvd := unData_eq' hu
            subst hvd
            have hk' : k = k' := by simpa using hkk
            subst hk'
            rcases aun_sound he hv (enum := true) (ps := args) (k := k) (fun _ => rfl) with hP | ⟨z, sh, heq, hsimp, hlen, hseq⟩
            · exact aPatArgs_sound hX args _ ha hm he hP
            · rw [heq] at ha
              exact aPatArgs_rel (p := p) (ps := args) hseq hlen args 0 (by simp) hsimp (by simpa using ha)
                (by simpa using hm) he (fun i hi => by simp at hi)
          · cases hm
        · cases hm
      | struct =>
        rw [hk] at hm ha
        simp only at hm ha
        split at hm
        · rename_i k' fs hu
          have hvd := unData_eq' hu
          subst hvd
          rcases aun_sound he hv (enum := false) (ps := args) (k := 0) (fun h => by cases h) with hP | ⟨z, sh, heq, hsimp, hlen, hseq⟩
          · exact aPatArgs_sound hX args _ ha hm he hP
          · rw [heq] at ha
            exact aPatArgs_rel (p := p) (ps := args) hseq hlen args 0 (by simp) hsimp (by simpa using ha)
              (by simpa using hm) he (fun i hi => by simp at hi)
        · cases hm
      | decl flags ctor ex =>
        rw [hk] at hm ha
        cases ex with
        | none => cases hm
        | some ex =>
          cases ex with
          | internal form => cases hm
          | external fn inf =>
            simp only at hm ha
            split at hm
            · cases hm
            · split at hm
              · rename_i fs hx
                have hP : HoldsP c D env (List.replicate args.length (aext e term.id a)) fs :=
                  HoldsP.replicate (fun f hf => hX term a e env D v s fs he hv hx f hf) _
                exact aPatArgs_sound hX args _ ha hm he hP
              · split at hm <;> cases hm
              · cases hm
/-- `aPat_sound` for every pattern against the same value. -/
theorem aPatAll_sound (hX : ExtOK c ctx) : ∀ (qs : List Pattern) (a : A) {e e' : AEnv} {v : V}
    {env env' : Isle.Interp.Env V} {s : LState},
    aPatAll p a qs e = some e' → matchAll p (sem ctx) s qs v env = .ok (some env') →
    EnvOK c D env e → γ c a D env v → EnvOK c D env' e' ∧ Ext env env'
  | [], a, e, e', v, env, env', s, ha, hm, he, hv => by
    rw [aPatAll.eq_1, Option.some.injEq] at ha
    subst ha
    rw [matchAll.eq_1] at hm
    cases hm
    exact ⟨he, Ext.refl _⟩
  | q :: qs, a, e, e', v, env, env', s, ha, hm, he, hv => by
    rw [aPatAll.eq_2] at ha
    rw [matchAll.eq_2] at hm
    cases hq : aPat p a q e with
    | none => rw [hq] at ha; cases ha
    | some e1 =>
      rw [hq] at ha
      simp only at ha
      cases hmq : matchPat p (sem ctx) s q v env with
      | error err => rw [hmq] at hm; cases hm
      | ok o =>
        rw [hmq] at hm
        cases o with
        | none => cases hm
        | some env1 =>
          obtain ⟨he1, hext1⟩ := aPat_sound hX q a hq hmq he hv
          obtain ⟨he2, hext2⟩ := aPatAll_sound hX qs a ha hm he1 (γ_ext a hext1 hv)
          exact ⟨he2, hext1.trans hext2⟩
/-- `aPat_sound` pointwise. -/
theorem aPatArgs_sound (hX : ExtOK c ctx) : ∀ (qs : List Pattern) (as : List A) {e e' : AEnv}
    {fs : List V} {env env' : Isle.Interp.Env V} {s : LState},
    aPatArgs p as qs e = some e' → matchArgs p (sem ctx) s qs fs env = .ok (some env') →
    EnvOK c D env e → HoldsP c D env as fs → EnvOK c D env' e' ∧ Ext env env'
  | [], as, e, e', fs, env, env', s, ha, hm, he, hP => by
    rw [aPatArgs_nil, Option.some.injEq] at ha
    subst ha
    cases fs with
    | nil => rw [matchArgs.eq_1] at hm; cases hm; exact ⟨he, Ext.refl _⟩
    | cons f fs => rw [matchArgs.eq_3] at hm <;> first | cases hm | simp_all
  | q :: qs, as, e, e', fs, env, env', s, ha, hm, he, hP => by
    rw [aPatArgs_cons] at ha
    cases fs with
    | nil => rw [matchArgs.eq_3] at hm <;> first | cases hm | simp_all
    | cons f fs =>
      rw [matchArgs.eq_2] at hm
      obtain ⟨hf, hP'⟩ := HoldsP.tail hP
      cases hq : aPat p (as.headD .top) q e with
      | none => rw [hq] at ha; cases ha
      | some e1 =>
        rw [hq] at ha
        simp only at ha
        cases hmq : matchPat p (sem ctx) s q f env with
        | error err => rw [hmq] at hm; cases hm
        | ok o =>
          rw [hmq] at hm
          cases o with
          | none => cases hm
          | some env1 =>
            obtain ⟨he1, hext1⟩ := aPat_sound hX q _ hq hmq he hf
            obtain ⟨he2, hext2⟩ := aPatArgs_sound hX qs as.tail ha hm he1 (hP'.ext hext1)
            exact ⟨he2, hext1.trans hext2⟩
end

end Pat

end Backend.Proof.DefGen
