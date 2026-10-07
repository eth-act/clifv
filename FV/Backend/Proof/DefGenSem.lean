import FV.Backend.Proof.DefGenOfV

/-!
# Definedness of the ISLE runs: the meaning of the abstract values

Fixed: the run's fresh vregs start at `lo`; `R` holds of the CLIF values the run may reach,
`I` of the instructions it may reach besides the root `root`. Relative to a set `D` of defined
vregs and a rule environment `env`, `γ a D env v` is the meaning of abstract value `a` (module
doc of `DefGenDom`); `γ` is monotone in `D` and stable when the environment binds an unbound
variable. `EnvOK` relates abstract and concrete environments.
-/

namespace Backend.Proof.DefGen

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Kill Backend.Proof.DefRun Isle
  Isle.Aarch64 Isle.Interp

/-- The fixed parameters of the meaning. -/
structure SC where
  lo : Nat
  R : Nat → Prop
  I : Nat → Prop
  root : Nat

variable (c : SC)

/-- A reached instruction (the root only if `b`). -/
def IOk (b : Bool) (j : Nat) : Prop := (b = true ∧ j = c.root) ∨ c.I j

/-- A defined register: a vreg of `D`, or (if `z`) a real register the allocator does not use. -/
def RD (D : Nat → Prop) (z : Bool) : Reg → Prop
  | .vreg n _ => D n
  | r => z = true ∧ r.allocatable = false

/-- A clean value. -/
def Cl (b z : Bool) (D : Nat → Prop) (v : V) : Prop :=
  (∀ r ∈ regsU v, RD D z r) ∧ (∀ n ∈ v.valsIn, c.R n) ∧ ∀ j ∈ v.instsIn, IOk c b j

/-- A pending register value: its vregs are fresh or defined. -/
def Wv (z : Bool) (D : Nat → Prop) (v : V) : Prop :=
  ∀ r ∈ regsU v, match r with
    | .vreg n _ => c.lo ≤ n ∨ D n
    | r => z = true ∧ r.allocatable = false

/-- `D` and the fresh defs of `ms`. -/
def DD (D : Nat → Prop) (ms : List MInst) (n : Nat) : Prop :=
  D n ∨ (c.lo ≤ n ∧ ∃ m ∈ ms, n ∈ defVregs m)

/-- An `MInst` value whose instruction reads defined vregs and whose registers may occupy
operand positions. -/
def MIok (D : Nat → Prop) (w : V) : Prop :=
  ∀ m, MInst.ofV w = some m → (∀ u ∈ useVregs m, D u) ∧ ∀ r ∈ useRegsK m ++ defRegsK m, OkReg r

/-- A call info whose uses are defined and whose defs may occupy operand positions. -/
def CIok (D : Nat → Prop) (w : V) : Prop :=
  ∀ ci, w = .op (.callInfo ci) → (∀ r ∈ callUses ci, RD D true r) ∧
    ∀ r ∈ ci.defs.map (·.2), OkReg r

/-- The instruction fields before position `j`. -/
def earlier (fs : List V) (sh : List SK) (j : Nat) : List V :=
  (instIdx sh j).filterMap fun i => fs[i]?

/-- **A flag/side-effect value's fields** (shape `sh`): others clean; each instruction reads
defined vregs or fresh defs of the earlier ones; the results are clean once all are emitted. -/
def SeqOk (z : Bool) (D : Nat → Prop) (fs : List V) (sh : List SK) : Prop :=
  ∀ (j : Nat) f, fs[j]? = some f →
    (sh[j]? = some .o → Cl c false true D f) ∧
    (sh[j]? = some .i → ∀ ms, (earlier fs sh j).mapM MInst.ofV = some ms → MIok (DD c D ms) f) ∧
    (sh[j]? = some .r → ∀ ms, (earlier fs sh sh.length).mapM MInst.ofV = some ms →
      Cl c false z (DD c D ms) f)

/-- A flag/side-effect value of type `τ`. -/
def FlagP (z : Bool) (D : Nat → Prop) (τ : TypeId) (v : V) : Prop :=
  ∃ k fs sh, v = .data τ k fs ∧ flagShape τ k = some sh ∧ fs.length = sh.length ∧
    SeqOk c z D fs sh

/-- A `CondResult` value. -/
def CrP (z : Bool) (D : Nat → Prop) (τ : TypeId) (v : V) : Prop :=
  ∃ k fs cs, v = .data τ k fs ∧ crShape τ k = some cs ∧ fs.length = cs.length ∧
    ∀ (i : Nat) f b, fs[i]? = some f → cs[i]? = some b →
      (b = true → Cl c false z D f ∨ FlagP c z D TyId.«ProducesFlags» f) ∧
      (b = false → Cl c false z D f)

/-- **The type predicates** (`ty τ z`). -/
def PT (z : Bool) (D : Nat → Prop) (τ : TypeId) (v : V) : Prop :=
  if τ = tyMInst then MIok D v
  else if τ ∈ ciTys then CIok D v
  else if τ ∈ flagTys then Cl c false z D v ∨ FlagP c z D τ v
  else if τ = TyId.«CondResult» then Cl c false z D v ∨ CrP c z D τ v
  else Cl c false z D v

/-- Once the instruction of variable `y` is emitted, its fresh defs are in `D'`. -/
def DefsIn (D' : Nat → Prop) (env : Isle.Interp.Env V) (y : Nat) : Prop :=
  ∀ w, env[y]? = some (some w) → ∃ m, MInst.ofV w = some m ∧ ∀ n ∈ defVregs m, c.lo ≤ n → D' n

/-- The registers of variable `x` (a pending call output) are among the call defs `ds`. -/
def CallDefsOf (D : Nat → Prop) (env : Isle.Interp.Env V) (x : Nat) (ds : List Reg) : Prop :=
  ∃ w, env[x]? = some (some w) ∧ w.valsIn = [] ∧ w.instsIn = [] ∧
    ∀ r ∈ regsU w, r ∈ ds ∧ ∃ n cl, r = .vreg n cl ∧ (c.lo ≤ n ∨ D n)

mutual
/-- **The meaning of an abstract value.** -/
def γ : A → (Nat → Prop) → Isle.Interp.Env V → V → Prop
  | .top, _, _, _ => True
  | .cl b z, D, _, v => Cl c b z D v
  | .wr z, D, _, v => Wv c z D v
  | .ty τ z, D, _, v => PT c z D τ v
  | .sym x, _, env, v => env[x]? = some (some v)
  | .aft ys a, D, env, v => ∀ D' : Nat → Prop, (∀ n, D n → D' n) →
      (∀ y ∈ ys, DefsIn c D' env y) → γ a D' env v
  | .data τ k fs, D, env, v => ∃ vs, v = .data τ k vs ∧ γL fs D env vs
  | .regs as, D, env, v => ∃ rs, v = .regs rs ∧ γL as D env (rs.map V.reg)
  | .crl xs, D, env, v => ∃ ds, v = .op (.callRets ds) ∧ (∀ r ∈ ds.map (·.2), OkReg r) ∧
      ∀ x ∈ xs, CallDefsOf c D env x (ds.map (·.2))
  | .cinfo xs, D, env, v => ∃ ci, v = .op (.callInfo ci) ∧ (∀ r ∈ callUses ci, RD D true r) ∧
      (∀ r ∈ ci.defs.map (·.2), OkReg r) ∧ ∀ x ∈ xs, CallDefsOf c D env x (ci.defs.map (·.2))
/-- `γ` pointwise (same lengths). -/
def γL : List A → (Nat → Prop) → Isle.Interp.Env V → List V → Prop
  | [], _, _, [] => True
  | a :: as, D, env, v :: vs => γ a D env v ∧ γL as D env vs
  | _, _, _, _ => False
end

/-- **The abstract environment describes the concrete one**: same length, the same variables
unbound, and every bound variable's value described. -/
def EnvOK (D : Nat → Prop) (env : Isle.Interp.Env V) (e : AEnv) : Prop :=
  e.length = env.size ∧ ∀ x : Nat, (e[x]? = some none → env[x]? = some none) ∧
    ∀ a, e[x]? = some (some a) → ∃ w, env[x]? = some (some w) ∧ γ c a D env w

/-! ## Monotonicity -/

variable {c}

theorem RD_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {z z' : Bool} (hz : z = true → z' = true)
    {r : Reg} (h : RD D z r) : RD D' z' r := by
  cases r <;> simp only [RD] at h ⊢
  case vreg => exact hD _ h
  all_goals exact ⟨hz h.1, h.2⟩

theorem IOk_mono {b b' : Bool} (hb : b = true → b' = true) {j : Nat} (h : IOk c b j) : IOk c b' j := by
  rcases h with ⟨h1, h2⟩ | h
  · exact .inl ⟨hb h1, h2⟩
  · exact .inr h

theorem Cl_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {b b' z z' : Bool}
    (hb : b = true → b' = true) (hz : z = true → z' = true) {v : V} (h : Cl c b z D v) :
    Cl c b' z' D' v :=
  ⟨fun r hr => RD_mono hD hz (h.1 r hr), h.2.1, fun j hj => IOk_mono hb (h.2.2 j hj)⟩

theorem Wv_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {z z' : Bool} (hz : z = true → z' = true)
    {v : V} (h : Wv c z D v) : Wv c z' D' v := by
  intro r hr
  have := h r hr
  cases r <;> simp only at this ⊢
  case vreg => exact this.imp id (hD _)
  all_goals exact ⟨hz this.1, this.2⟩

theorem DD_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) (ms : List MInst) :
    ∀ n, DD c D ms n → DD c D' ms n :=
  fun _ h => h.imp (hD _) id

theorem MIok_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {w : V} (h : MIok D w) : MIok D' w :=
  fun m hm => ⟨fun u hu => hD _ ((h m hm).1 u hu), (h m hm).2⟩

theorem CIok_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {w : V} (h : CIok D w) : CIok D' w :=
  fun ci hci => ⟨fun r hr => RD_mono hD id ((h ci hci).1 r hr), (h ci hci).2⟩

theorem SeqOk_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {z z' : Bool}
    (hz : z = true → z' = true) {fs : List V} {sh : List SK} (h : SeqOk c z D fs sh) :
    SeqOk c z' D' fs sh := fun j f hf =>
  ⟨fun hs => Cl_mono hD id id ((h j f hf).1 hs),
   fun hs ms hms => MIok_mono (DD_mono hD ms) ((h j f hf).2.1 hs ms hms),
   fun hs ms hms => Cl_mono (DD_mono hD ms) id hz ((h j f hf).2.2 hs ms hms)⟩

theorem FlagP_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {z z' : Bool}
    (hz : z = true → z' = true) {τ : TypeId} {v : V} (h : FlagP c z D τ v) : FlagP c z' D' τ v := by
  obtain ⟨k, fs, sh, h1, h2, h3, h4⟩ := h
  exact ⟨k, fs, sh, h1, h2, h3, SeqOk_mono hD hz h4⟩

theorem CrP_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {z z' : Bool}
    (hz : z = true → z' = true) {τ : TypeId} {v : V} (h : CrP c z D τ v) : CrP c z' D' τ v := by
  obtain ⟨k, fs, cs, h1, h2, h3, h4⟩ := h
  refine ⟨k, fs, cs, h1, h2, h3, fun i f b hf hb => ⟨fun hb' => ?_, fun hb' => ?_⟩⟩
  · rcases (h4 i f b hf hb).1 hb' with h | h
    · exact .inl (Cl_mono hD id hz h)
    · exact .inr (FlagP_mono hD hz h)
  · exact Cl_mono hD id hz ((h4 i f b hf hb).2 hb')

theorem PT_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {z z' : Bool}
    (hz : z = true → z' = true) {τ : TypeId} {v : V} (h : PT c z D τ v) : PT c z' D' τ v := by
  unfold PT at h ⊢
  split
  · simp_all only [↓reduceIte]; exact MIok_mono hD h
  rename_i h1
  simp only [h1, ↓reduceIte] at h
  split
  · simp_all only [↓reduceIte]; exact CIok_mono hD h
  rename_i h2
  simp only [h2, ↓reduceIte] at h
  split
  · simp_all only [↓reduceIte]
    rcases h with h | h
    · exact .inl (Cl_mono hD id hz h)
    · exact .inr (FlagP_mono hD hz h)
  rename_i h3
  simp only [h3, ↓reduceIte] at h
  split
  · simp_all only [↓reduceIte]
    rcases h with h | h
    · exact .inl (Cl_mono hD id hz h)
    · exact .inr (CrP_mono hD hz h)
  rename_i h4
  simp only [h4, ↓reduceIte] at h
  exact Cl_mono hD id hz h

theorem CallDefsOf_mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {env : Isle.Interp.Env V}
    {x : Nat} {ds : List Reg} (h : CallDefsOf c D env x ds) : CallDefsOf c D' env x ds := by
  obtain ⟨w, h1, h2, h3, h4⟩ := h
  exact ⟨w, h1, h2, h3, fun r hr => ⟨(h4 r hr).1, by
    obtain ⟨n, cl, e, h⟩ := (h4 r hr).2
    exact ⟨n, cl, e, h.imp id (hD n)⟩⟩⟩

mutual
/-- **`γ` is monotone in the defined set.** -/
theorem γ_mono : ∀ (a : A) {D D' : Nat → Prop} (_ : ∀ n, D n → D' n) {env : Isle.Interp.Env V}
    {v : V}, γ c a D env v → γ c a D' env v
  | .top, _, _, _, _, _, h => h
  | .cl _ _, _, _, hD, _, _, h => Cl_mono hD id id h
  | .wr _, _, _, hD, _, _, h => Wv_mono hD id h
  | .ty _ _, _, _, hD, _, _, h => PT_mono hD id h
  | .sym _, _, _, _, _, _, h => h
  | .aft _ _, _, _, hD, _, _, h => fun D'' hD'' hys => h D'' (fun n hn => hD'' n (hD n hn)) hys
  | .data _ _ fs, _, _, hD, _, _, h => by
    obtain ⟨vs, rfl, hl⟩ := h
    exact ⟨vs, rfl, γL_mono fs hD hl⟩
  | .regs as, _, _, hD, _, _, h => by
    obtain ⟨rs, rfl, hl⟩ := h
    exact ⟨rs, rfl, γL_mono as hD hl⟩
  | .crl _, _, _, hD, _, _, h => by
    obtain ⟨ds, rfl, ho, hl⟩ := h
    exact ⟨ds, rfl, ho, fun x hx => CallDefsOf_mono hD (hl x hx)⟩
  | .cinfo _, _, _, hD, _, _, h => by
    obtain ⟨ci, rfl, hu, ho, hl⟩ := h
    exact ⟨ci, rfl, fun r hr => RD_mono hD id (hu r hr), ho, fun x hx => CallDefsOf_mono hD (hl x hx)⟩
/-- `γL` is monotone in the defined set. -/
theorem γL_mono : ∀ (as : List A) {D D' : Nat → Prop} (_ : ∀ n, D n → D' n)
    {env : Isle.Interp.Env V} {vs : List V}, γL c as D env vs → γL c as D' env vs
  | [], _, _, _, _, [], h => h
  | a :: as, _, _, hD, _, _ :: _, h => ⟨γ_mono a hD h.1, γL_mono as hD h.2⟩
  | [], _, _, _, _, _ :: _, h => h.elim
  | _ :: _, _, _, _, _, [], h => h.elim
end

/-! ## Extending the environment -/

/-- `env'` keeps the bound variables of `env`. -/
def Ext (env env' : Isle.Interp.Env V) : Prop :=
  ∀ (y : Nat) (w : V), env[y]? = some (some w) → env'[y]? = some (some w)

theorem Ext.refl (env : Isle.Interp.Env V) : Ext env env := fun _ _ h => h

theorem Ext.trans {e1 e2 e3 : Isle.Interp.Env V} (h1 : Ext e1 e2) (h2 : Ext e2 e3) : Ext e1 e3 :=
  fun y w h => h2 y w (h1 y w h)

theorem Ext.set {env : Isle.Interp.Env V} {x : Nat} (hx : env[x]? = some none) (v : V) :
    Ext env (env.set! x (some v)) := by
  intro y w hy
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hxy : x = y
  · subst hxy; rw [hx] at hy; cases hy
  · simp only [hxy, ↓reduceIte]; exact hy

theorem DefsIn_ext {env env' : Isle.Interp.Env V} (he : Ext env env') {D' : Nat → Prop} {y : Nat}
    (h : DefsIn c D' env' y) : DefsIn c D' env y := fun w hw => h w (he y w hw)

theorem CallDefsOf_ext {env env' : Isle.Interp.Env V} (he : Ext env env') {D : Nat → Prop}
    {x : Nat} {ds : List Reg} (h : CallDefsOf c D env x ds) : CallDefsOf c D env' x ds := by
  obtain ⟨w, h1, h2⟩ := h
  exact ⟨w, he x w h1, h2⟩

mutual
/-- **`γ` survives extending the environment.** -/
theorem γ_ext : ∀ (a : A) {D : Nat → Prop} {env env' : Isle.Interp.Env V} (_ : Ext env env')
    {v : V}, γ c a D env v → γ c a D env' v
  | .top, _, _, _, _, _, h => h
  | .cl _ _, _, _, _, _, _, h => h
  | .wr _, _, _, _, _, _, h => h
  | .ty _ _, _, _, _, _, _, h => h
  | .sym x, _, _, _, he, _, h => he x _ h
  | .aft _ b, _, _, _, he, _, h => fun D'' hD'' hys =>
    γ_ext b he (h D'' hD'' fun y hy => DefsIn_ext he (hys y hy))
  | .data _ _ fs, _, _, _, he, _, h => by
    obtain ⟨vs, rfl, hl⟩ := h
    exact ⟨vs, rfl, γL_ext fs he hl⟩
  | .regs as, _, _, _, he, _, h => by
    obtain ⟨rs, rfl, hl⟩ := h
    exact ⟨rs, rfl, γL_ext as he hl⟩
  | .crl _, _, _, _, he, _, h => by
    obtain ⟨ds, rfl, ho, hl⟩ := h
    exact ⟨ds, rfl, ho, fun x hx => CallDefsOf_ext he (hl x hx)⟩
  | .cinfo _, _, _, _, he, _, h => by
    obtain ⟨ci, rfl, hu, ho, hl⟩ := h
    exact ⟨ci, rfl, hu, ho, fun x hx => CallDefsOf_ext he (hl x hx)⟩
/-- `γL` survives extending the environment. -/
theorem γL_ext : ∀ (as : List A) {D : Nat → Prop} {env env' : Isle.Interp.Env V}
    (_ : Ext env env') {vs : List V}, γL c as D env vs → γL c as D env' vs
  | [], _, _, _, _, [], h => h
  | a :: as, _, _, _, he, _ :: _, h => ⟨γ_ext a he h.1, γL_ext as he h.2⟩
  | [], _, _, _, _, _ :: _, h => h.elim
  | _ :: _, _, _, _, _, [], h => h.elim
end

/-! ## Abstract environments -/

theorem EnvOK.mono {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {env : Isle.Interp.Env V} {e : AEnv}
    (h : EnvOK c D env e) : EnvOK c D' env e := by
  refine ⟨h.1, fun x => ⟨(h.2 x).1, fun a ha => ?_⟩⟩
  obtain ⟨w, hw, hg⟩ := (h.2 x).2 a ha
  exact ⟨w, hw, γ_mono a hD hg⟩

theorem EnvOK.empty (D : Nat → Prop) (n : Nat) :
    EnvOK c D (Array.replicate n none) (List.replicate n none) := by
  refine ⟨by simp, fun x => ⟨fun h => ?_, fun a ha => ?_⟩⟩
  · simp only [List.getElem?_replicate] at h
    simp only [Array.getElem?_replicate]
    split at h
    · simp_all
    · cases h
  · simp only [List.getElem?_replicate] at ha
    split at ha <;> cases ha

/-- Binding an unbound variable. -/
theorem EnvOK.bind {D : Nat → Prop} {env : Isle.Interp.Env V} {e : AEnv} (h : EnvOK c D env e)
    {x : Nat} (hx : e[x]? = some none) {a : A} {v : V} (hv : γ c a D env v) :
    env[x]? = some none ∧ x < env.size ∧
      EnvOK c D (env.set! x (some v)) (e.set x (some a)) := by
  have hxe := (h.2 x).1 hx
  have hlt : x < env.size := by
    rcases Nat.lt_or_ge x env.size with hl | hl
    · exact hl
    · rw [Array.getElem?_eq_none hl] at hxe; cases hxe
  have hext := Ext.set hxe v
  refine ⟨hxe, hlt, by simp [h.1], fun y => ⟨fun hy => ?_, fun b hb => ?_⟩⟩
  · rw [List.getElem?_set] at hy
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hxy : x = y
    · subst hxy; simp at hy
    · simp only [hxy, ↓reduceIte] at hy ⊢
      exact (h.2 y).1 hy
  · rw [List.getElem?_set] at hb
    by_cases hxy : x = y
    · subst hxy
      simp only [↓reduceIte] at hb
      split at hb
      · cases hb
        refine ⟨v, ?_, γ_ext a hext hv⟩
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp [hlt]
      · cases hb
    · simp only [hxy, ↓reduceIte] at hb
      obtain ⟨w, hw, hg⟩ := (h.2 y).2 b hb
      exact ⟨w, hext y w hw, γ_ext b hext hg⟩

/-! ## Clean values -/

theorem valsInL_mem' {vs : List V} {n : Nat} (h : n ∈ valsInL vs) : ∃ v ∈ vs, n ∈ v.valsIn := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    simp only [valsInL_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨w, List.mem_cons_self, h⟩
    · obtain ⟨v, hv, h⟩ := ih h; exact ⟨v, List.mem_cons_of_mem _ hv, h⟩

theorem instsInL_mem' {vs : List V} {n : Nat} (h : n ∈ instsInL vs) : ∃ v ∈ vs, n ∈ v.instsIn := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    simp only [instsInL_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨w, List.mem_cons_self, h⟩
    · obtain ⟨v, hv, h⟩ := ih h; exact ⟨v, List.mem_cons_of_mem _ hv, h⟩

@[simp] theorem regsU_data (τ k : Nat) (vs : List V) : regsU (.data τ k vs) = regsUL vs := rfl

theorem Cl_data_iff {b z : Bool} {D : Nat → Prop} {τ k : Nat} {vs : List V} :
    Cl c b z D (.data τ k vs) ↔ ∀ v ∈ vs, Cl c b z D v := by
  constructor
  · intro h v hv
    refine ⟨fun r hr => h.1 r (regsU_sub_mem hv hr), fun n hn => h.2.1 n ?_, fun j hj => h.2.2 j ?_⟩
    · simp only [V.valsIn]; exact valsIn_sub_of_mem hv n hn
    · simp only [V.instsIn]; exact instsIn_sub_of_mem hv j hj
  · intro h
    refine ⟨fun r hr => ?_, fun n hn => ?_, fun j hj => ?_⟩
    · obtain ⟨w, hw, hr⟩ := mem_regsUL.mp hr
      exact (h w hw).1 r hr
    · obtain ⟨w, hw, hn⟩ := valsInL_mem' hn
      exact (h w hw).2.1 n hn
    · obtain ⟨w, hw, hj⟩ := instsInL_mem' hj
      exact (h w hw).2.2 j hj

theorem Cl_reg_iff {b z : Bool} {D : Nat → Prop} {r : Reg} : Cl c b z D (.reg r) ↔ RD D z r := by
  simp [Cl, regsU, V.valsIn, V.instsIn]

theorem Cl_regs_iff {b z : Bool} {D : Nat → Prop} {rs : List Reg} :
    Cl c b z D (.regs rs) ↔ ∀ r ∈ rs, RD D z r := by
  simp [Cl, regsU, V.valsIn, V.instsIn]

/-! ## Resolution and the order -/

section Fits
variable {D : Nat → Prop} {env : Isle.Interp.Env V} {e : AEnv}

theorem getD_none_eq (e : AEnv) (x : Nat) : e.getD x none = (e[x]?).getD none := by
  rw [List.getD_eq_getElem?_getD]

/-- **Resolution is sound.** -/
theorem res_sound (he : EnvOK c D env e) :
    ∀ (n : Nat) (a : A) {w : V}, γ c a D env w → γ c (res e n a) D env w
  | 0, _, _, _ => trivial
  | n + 1, a, w, h => by
    cases a with
    | sym x =>
      simp only [res, getD_none_eq]
      cases hx : e[x]? with
      | none => trivial
      | some o =>
        cases o with
        | none => trivial
        | some a' =>
          obtain ⟨w', hw', hg⟩ := (he.2 x).2 a' hx
          have h' : env[x]? = some (some w) := h
          rw [h'] at hw'
          cases hw'
          exact res_sound he n a' hg
    | aft ys a =>
      cases ys with
      | nil => exact res_sound he n a (h D (fun _ h => h) (by simp))
      | cons y ys => exact h
    | _ => exact h

mutual
/-- **`fitsCl` is sound.** -/
theorem fitsCl_sound (he : EnvOK c D env e) :
    ∀ (n : Nat) (b z : Bool) (a : A) {w : V}, γ c a D env w → fitsCl e n b z a = true →
      Cl c b z D w
  | 0, _, _, _, _, _, hf => by simp [fitsCl] at hf
  | n + 1, b, z, a, w, h, hf => by
    have hr := res_sound he n a h
    simp only [fitsCl] at hf
    split at hf
    · rename_i b' z' hra
      rw [hra] at hr
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hf
      exact Cl_mono (fun _ h => h) (fun hb => by cases b' <;> simp_all) (fun hz => by
        cases z' <;> simp_all) hr
    · rename_i τ k fs hra
      rw [hra] at hr
      obtain ⟨vs, rfl, hl⟩ := hr
      exact Cl_data_iff.mpr (fitsClL_sound he n b z fs hl hf)
    · rename_i as hra
      rw [hra] at hr
      obtain ⟨rs, rfl, hl⟩ := hr
      have := fitsClL_sound he n b z as hl hf
      exact Cl_regs_iff.mpr fun r hr => Cl_reg_iff.mp (this _ (List.mem_map_of_mem hr))
    · cases hf
/-- `fitsCl.fitsClL` is sound. -/
theorem fitsClL_sound (he : EnvOK c D env e) :
    ∀ (n : Nat) (b z : Bool) (as : List A) {vs : List V}, γL c as D env vs →
      fitsCl.fitsClL e n b z as = true → ∀ v ∈ vs, Cl c b z D v
  | _, _, _, [], [], _, _ => fun _ h => by cases h
  | n, b, z, a :: as, v :: vs, h, hf => by
    simp only [fitsCl.fitsClL, Bool.and_eq_true] at hf
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact fitsCl_sound he n b z a h.1 hf.1
    · exact fitsClL_sound he n b z as h.2 hf.2 u hu
  | _, _, _, [], _ :: _, h, _ => h.elim
  | _, _, _, _ :: _, [], h, _ => h.elim
end

/-- `fitsWr` is sound. -/
theorem fitsWr_sound (he : EnvOK c D env e) {n : Nat} {z : Bool} {a : A} {w : V}
    (h : γ c a D env w) (hf : fitsWr e n z a = true) : Wv c z D w := by
  have hr := res_sound he n a h
  unfold fitsWr at hf
  split at hf
  · rename_i z' hra
    rw [hra] at hr
    exact Wv_mono (fun _ h => h) (fun hz => by cases z' <;> simp_all) hr
  · rename_i b z' hra
    rw [hra] at hr
    intro r hr'
    have := hr.1 r hr'
    cases r <;> simp only [RD] at this ⊢
    case vreg => exact .inr this
    all_goals exact ⟨by cases z' <;> simp_all, this.2⟩
  · cases hf

theorem RD_okReg {D : Nat → Prop} {z : Bool} {r : Reg} (h : RD D z r) : OkReg r := by
  cases r
  case vreg n cl => exact .inl ⟨n, cl, rfl⟩
  all_goals exact .inr h.2

theorem Cl_CIok {b z : Bool} {w : V} (h : Cl c b z D w) : CIok D w := by
  intro ci hci
  subst hci
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have := h.1 r (by simp only [regsU, opRegsU, List.mem_append]; exact .inl hr)
    exact RD_mono (fun _ h => h) (fun _ => rfl) this
  · exact RD_okReg (h.1 r (by simp only [regsU, opRegsU, List.mem_append]; exact .inr hr))

/-- `fitsCI` is sound. -/
theorem fitsCI_sound (he : EnvOK c D env e) {n : Nat} {a : A} {w : V}
    (h : γ c a D env w) (hf : fitsCI e n a = true) : CIok D w := by
  have hr := res_sound he n a h
  unfold fitsCI at hf
  split at hf
  · rename_i τ z hra
    rw [hra] at hr
    have hτ : τ ∈ ciTys := by simpa using hf
    have hm : τ ≠ tyMInst := by
      intro e; subst e
      simp only [ciTys, List.mem_cons, List.mem_nil_iff, or_false] at hτ
      rcases hτ with h | h <;> exact absurd h (by decide)
    have hp : PT c z D τ w := hr
    unfold PT at hp
    rw [if_neg hm, if_pos hτ] at hp
    exact hp
  · rename_i xs hra
    rw [hra] at hr
    obtain ⟨ci, rfl, hu, ho, -⟩ := hr
    intro ci' hci'
    cases hci'
    exact ⟨hu, ho⟩
  · rename_i b z hra
    rw [hra] at hr
    exact Cl_CIok hr
  · cases hf

end Fits

/-! ## `MInst` values -/

theorem ofV_data {w : V} {m : MInst} (h : MInst.ofV w = some m) :
    ∃ k vs, w = .data tyMInst k vs := by
  unfold MInst.ofV at h
  obtain ⟨⟨k, fs⟩, he, -⟩ := bind_some_ex h
  exact ⟨k, fs, enumOf_eq he⟩

theorem useAll_sub : ∀ {ks : List FK} {vs : List V} {r : Reg}, r ∈ useAll ks vs → r ∈ regsUL vs
  | _ :: _, _ :: _, _, h => by
    simp only [useAll, List.mem_append] at h
    rcases h with h | h
    · exact List.mem_append_left _ (useOf_sub _ _ _ h)
    · exact List.mem_append_right _ (useAll_sub h)
  | [], _, _, h => by simp [useAll] at h
  | _ :: _, [], _, h => by simp [useAll] at h

theorem defOf_sub (k : FK) (f : V) : ∀ r ∈ defOf k f, r ∈ regsU f := by
  intro r hr
  cases k
  · exact hr
  · cases hr
  · cases f with
    | op o =>
      cases o with
      | callInfo ci =>
        simp only [regsU, opRegsU, List.mem_append]
        exact .inr hr
      | _ => simp [defOf] at hr
    | _ => simp [defOf] at hr

theorem defAll_sub : ∀ {ks : List FK} {vs : List V} {r : Reg}, r ∈ defAll ks vs → r ∈ regsUL vs
  | _ :: _, _ :: _, _, h => by
    simp only [defAll, List.mem_append] at h
    rcases h with h | h
    · exact List.mem_append_left _ (defOf_sub _ _ _ h)
    · exact List.mem_append_right _ (defAll_sub h)
  | [], _, _, h => by simp [defAll] at h
  | _ :: _, [], _, h => by simp [defAll] at h

/-- An `MInst` value whose use fields hold defined registers and whose def fields hold
registers that may occupy operand positions. -/
theorem MIok_of_fields {D : Nat → Prop} {k : Nat} {vs : List V}
    (h : ∀ ks, miKinds k = some ks → (∀ r ∈ useAll ks vs, RD D true r) ∧
      ∀ r ∈ defAll ks vs, OkReg r) : MIok D (.data tyMInst k vs) := by
  intro m hm
  obtain ⟨ks, hk, -, hU, hDf, -, -⟩ := ofV_fields hm
  obtain ⟨h1, h2⟩ := h ks hk
  refine ⟨fun u hu => ?_, fun r hr => ?_⟩
  · obtain ⟨cl, hcl⟩ := useVregs_mem hu
    exact h1 _ (hU _ hcl)
  · rcases List.mem_append.mp hr with hr | hr
    · exact RD_okReg (h1 _ (hU _ hr))
    · exact h2 _ (hDf _ hr)

theorem Cl_MIok {D : Nat → Prop} {b z : Bool} {w : V} (h : Cl c b z D w) : MIok D w := by
  intro m hm
  obtain ⟨k, vs, rfl⟩ := ofV_data hm
  refine MIok_of_fields (fun ks _ => ⟨fun r hr => ?_, fun r hr => ?_⟩) m hm
  · exact RD_mono (fun _ h => h) (fun _ => rfl) (h.1 r (useAll_sub hr))
  · exact RD_okReg (h.1 r (defAll_sub hr))

section Fits2
variable {D : Nat → Prop} {env : Isle.Interp.Env V} {e : AEnv}

theorem fitsFields_sound (he : EnvOK c D env e) {n : Nat} :
    ∀ (fs : List A) (ks : List FK) {vs : List V}, γL c fs D env vs →
      fitsFields e n fs ks = true →
      (∀ r ∈ useAll ks vs, RD D true r) ∧ ∀ r ∈ defAll ks vs, OkReg r
  | f :: fs, k :: ks, v :: vs, h, hf => by
    simp only [fitsFields, Bool.and_eq_true] at hf
    obtain ⟨ih1, ih2⟩ := fitsFields_sound he fs ks h.2 hf.2
    have hk : (∀ r ∈ useOf k v, RD D true r) ∧ ∀ r ∈ defOf k v, OkReg r := by
      cases k
      · have hw := fitsWr_sound he h.1 hf.1
        refine ⟨fun r hr => (by simp [useOf] at hr), fun r hr => ?_⟩
        have := hw r hr
        cases r
        case vreg n cl => exact .inl ⟨n, cl, rfl⟩
        all_goals exact .inr this.2
      · have hc := fitsCl_sound he n true true f h.1 hf.1
        exact ⟨fun r hr => hc.1 r hr, fun r hr => (by simp [defOf] at hr)⟩
      · have hc := fitsCI_sound he h.1 hf.1
        cases v with
        | op o =>
          cases o with
          | callInfo ci => exact ⟨(hc ci rfl).1, (hc ci rfl).2⟩
          | _ => exact ⟨fun r hr => (by simp [useOf] at hr), fun r hr => (by simp [defOf] at hr)⟩
        | _ => exact ⟨fun r hr => (by simp [useOf] at hr), fun r hr => (by simp [defOf] at hr)⟩
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [useAll, List.mem_append] at hr
      exact hr.elim (hk.1 r) (ih1 r)
    · simp only [defAll, List.mem_append] at hr
      exact hr.elim (hk.2 r) (ih2 r)
  | [], [], [], _, _ => ⟨fun r hr => by simp [useAll] at hr, fun r hr => by simp [defAll] at hr⟩
  | [], [], _ :: _, h, _ => h.elim
  | _ :: _, _, [], h, _ => h.elim
  | [], _ :: _, _, _, hf => by simp [fitsFields] at hf
  | _ :: _, [], _ :: _, _, hf => by simp [fitsFields] at hf

/-- **`fitsMI` is sound.** -/
theorem fitsMI_sound (he : EnvOK c D env e) {n : Nat} {a : A} {w : V} (h : γ c a D env w)
    (hf : fitsMI e n a = true) : MIok D w := by
  have hr := res_sound he n a h
  unfold fitsMI at hf
  split at hf
  · rename_i τ z hra
    rw [hra] at hr
    have hτ : τ = tyMInst := by simpa using hf
    subst hτ
    have hp : PT c z D tyMInst w := hr
    simpa [PT] using hp
  · rename_i b z hra
    rw [hra] at hr
    exact Cl_MIok hr
  · rename_i τ k fs hra
    rw [hra] at hr
    obtain ⟨vs, rfl, hl⟩ := hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨rfl, hf⟩ := hf
    refine MIok_of_fields fun ks hks => ?_
    rw [hks] at hf
    exact fitsFields_sound he fs ks hl hf
  · cases hf

end Fits2

/-! ## Upgrades -/

section Upg
variable {D : Nat → Prop} {env : Isle.Interp.Env V} {e : AEnv}

theorem getD_some_iff {e : AEnv} {x : Nat} {a : A} : e.getD x none = some a ↔ e[x]? = some (some a) := by
  rw [getD_none_eq]
  cases h : e[x]? with
  | none => simp
  | some o => cases o <;> simp

/-- Overwrite a bound variable's description. -/
theorem EnvOK.update (he : EnvOK c D env e) {x : Nat} {a0 : A} (hx : e[x]? = some (some a0))
    {a : A} (ha : ∀ w, env[x]? = some (some w) → γ c a D env w) :
    EnvOK c D env (e.set x (some a)) := by
  refine ⟨by simp [he.1], fun y => ⟨fun hy => ?_, fun b hb => ?_⟩⟩
  · rw [List.getElem?_set] at hy
    by_cases hxy : x = y
    · subst hxy; split at hy <;> simp_all
    · simp only [hxy, ↓reduceIte] at hy; exact (he.2 y).1 hy
  · rw [List.getElem?_set] at hb
    by_cases hxy : x = y
    · subst hxy
      simp only [↓reduceIte] at hb
      split at hb
      · cases hb
        obtain ⟨w, hw, -⟩ := (he.2 x).2 a0 hx
        exact ⟨w, hw, ha w hw⟩
      · cases hb
    · simp only [hxy, ↓reduceIte] at hb
      exact (he.2 y).2 b hb

/-- A variable whose value's fresh vregs are defined becomes defined. -/
theorem setDef_sound (he : EnvOK c D env e) {n x : Nat}
    (hx : ∀ w, env[x]? = some (some w) → w.valsIn = [] ∧ w.instsIn = [] ∧
      ∀ r ∈ regsU w, ∀ k cl, r = .vreg k cl → c.lo ≤ k → D k) :
    EnvOK c D env (setDef e n x) := by
  unfold setDef
  split
  · rename_i z hres
    cases n with
    | zero => simp [res] at hres
    | succ n =>
      simp only [res] at hres
      split at hres
      · rename_i a0 hget
        have hx0 := getD_some_iff.mp hget
        refine he.update hx0 fun w hw => ?_
        have hr := res_sound he (n + 1) (.sym x) (w := w) hw
        simp only [res, hget] at hr
        rw [hres] at hr
        obtain ⟨h1, h2, h3⟩ := hx w hw
        refine ⟨fun r hr' => ?_, by simp [h1], by simp [h2]⟩
        have := hr r hr'
        cases r with
        | vreg k cl =>
          simp only [RD]
          rcases this with h | h
          · exact h3 _ hr' k cl rfl h
          · exact h
        | _ => exact this
      · cases hres
  · exact he

theorem setDefL_sound {n : Nat} :
    ∀ (xs : List Nat) {e : AEnv}, EnvOK c D env e →
      (∀ x ∈ xs, ∀ w, env[x]? = some (some w) → w.valsIn = [] ∧ w.instsIn = [] ∧
        ∀ r ∈ regsU w, ∀ k cl, r = .vreg k cl → c.lo ≤ k → D k) →
      EnvOK c D env (setDefL e n xs)
  | [], _, he, _ => he
  | x :: xs, _, he, h => setDefL_sound xs (setDef_sound he (h x List.mem_cons_self))
      fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem fieldsOf_cons_sub {k k' : FK} {ks : List FK} {f : V} {vs : List V} :
    ∀ g ∈ fieldsOf k ks vs, g ∈ fieldsOf k (k' :: ks) (f :: vs) :=
  fun g hg => by simp only [fieldsOf, List.mem_append]; exact .inr hg

theorem fieldsOf_head {k : FK} {ks : List FK} {f : V} {vs : List V} :
    f ∈ fieldsOf k (k :: ks) (f :: vs) := by simp [fieldsOf]

/-- The upgrades of an emitted instruction's fields. -/
theorem upgF_sound {n : Nat} :
    ∀ (fs : List A) (ks : List FK) {vs : List V} {e : AEnv}, EnvOK c D env e → γL c fs D env vs →
      (∀ v ∈ fieldsOf .d ks vs, ∃ r, v = .reg r ∧ ∀ k cl, r = .vreg k cl → c.lo ≤ k → D k) →
      (∀ v ∈ fieldsOf .c ks vs, ∃ ci, v = .op (.callInfo ci) ∧
        ∀ q ∈ ci.defs, ∀ k cl, q.2 = .vreg k cl → c.lo ≤ k → D k) →
      EnvOK c D env (upgF e n fs ks)
  | f :: fs, k :: ks, v :: vs, e, he, h, hd, hc => by
    simp only [upgF]
    refine upgF_sound fs ks (upgF_sound_step he h.1 k hd hc) (h.2)
      (fun g hg => hd g (fieldsOf_cons_sub g hg)) (fun g hg => hc g (fieldsOf_cons_sub g hg))
  | [], _, _, _, he, _, _, _ => by simpa [upgF] using he
  | _ :: _, [], _, _, he, _, _, _ => by simpa [upgF] using he
  | _ :: _, _ :: _, [], _, _, h, _, _ => h.elim
where
  upgF_sound_step {e : AEnv} (he : EnvOK c D env e) {f : A} {v : V} (hv : γ c f D env v) (k : FK)
      {ks : List FK} {vs : List V}
      (hd : ∀ v' ∈ fieldsOf .d (k :: ks) (v :: vs), ∃ r, v' = .reg r ∧
        ∀ k cl, r = .vreg k cl → c.lo ≤ k → D k)
      (hc : ∀ v' ∈ fieldsOf .c (k :: ks) (v :: vs), ∃ ci, v' = .op (.callInfo ci) ∧
        ∀ q ∈ ci.defs, ∀ k cl, q.2 = .vreg k cl → c.lo ≤ k → D k) :
      EnvOK c D env (upg1 e n f k) := by
    cases k with
    | d =>
      cases f with
      | sym x =>
        simp only [upg1]
        obtain ⟨r, rfl, hr⟩ := hd v fieldsOf_head
        refine setDef_sound he fun w hw => ?_
        have hv' : env[x]? = some (some (V.reg r)) := hv
        rw [hv'] at hw
        cases hw
        refine ⟨rfl, rfl, fun r' hr' k cl hrk hlo => ?_⟩
        simp only [regsU, List.mem_singleton] at hr'
        subst hr'
        exact hr k cl hrk hlo
      | _ => simpa [upg1] using he
    | u => simpa [upg1] using he
    | c =>
      simp only [upg1]
      split
      · rename_i xs hres
        have hr := res_sound he n f hv
        rw [hres] at hr
        obtain ⟨ci, rfl, -, -, hx⟩ := hr
        obtain ⟨ci', hci', hq⟩ := hc _ fieldsOf_head
        cases hci'
        refine setDefL_sound xs he fun x hxs w hw => ?_
        obtain ⟨w', hw', h1, h2, h3⟩ := hx x hxs
        rw [hw'] at hw
        cases hw
        refine ⟨h1, h2, fun r hr k cl hrk hlo => ?_⟩
        obtain ⟨hmem, -⟩ := h3 r hr
        obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hmem
        exact hq q hq' k cl hrk hlo
      · exact he

/-- The `aft` lists after emitting the instruction of variable `y`. -/
theorem dropAft_sound {D' : Nat → Prop} (he : EnvOK c D env e) (hD : ∀ n, D n → D' n) {y : Nat}
    (hy : DefsIn c D' env y) : EnvOK c D' env (dropAft y e) := by
  refine ⟨by simp [dropAft, he.1], fun x => ⟨fun hx => ?_, fun b hb => ?_⟩⟩
  · simp only [dropAft, List.getElem?_map] at hx
    cases h : e[x]? with
    | none => rw [h] at hx; cases hx
    | some o =>
      rw [h] at hx
      cases o with
      | none => exact (he.2 x).1 h
      | some a => simp [dropAft1] at hx; split at hx <;> cases hx
  · simp only [dropAft, List.getElem?_map] at hb
    cases h : e[x]? with
    | none => rw [h] at hb; cases hb
    | some o =>
      rw [h] at hb
      cases o with
      | none => simp [dropAft1] at hb
      | some a =>
        obtain ⟨w, hw, hg⟩ := (he.2 x).2 a h
        refine ⟨w, hw, ?_⟩
        simp only [Option.map_some, Option.some.injEq] at hb
        cases a with
        | aft ys b' =>
          simp only [dropAft1, Option.some.injEq] at hb
          subst hb
          split
          · rename_i hnil
            refine hg D' hD fun y' hy' => ?_
            by_cases hyy : y' = y
            · subst hyy; exact hy
            · have : y' ∈ ys.erase y := (List.mem_erase_of_ne hyy).mpr hy'
              have hn : ys.erase y = [] := by simpa [List.isEmpty_iff] using hnil
              rw [hn] at this; cases this
          · intro D'' hD'' hys
            refine hg D'' (fun n hn => hD'' n (hD n hn)) fun y' hy' => ?_
            by_cases hyy : y' = y
            · subst hyy
              intro w' hw'
              obtain ⟨m, hm, hdm⟩ := hy w' hw'
              exact ⟨m, hm, fun n hn hlo => hD'' n (hdm n hn hlo)⟩
            · exact hys y' ((List.mem_erase_of_ne hyy).mpr hy')
        | _ =>
          simp only [dropAft1, Option.some.injEq] at hb
          subst hb
          exact γ_mono _ hD hg

/-- **The upgrades after emitting an instruction are sound**: if the emitted value `w` (described
by `a`) builds instruction `m` whose registers may occupy operand positions, then once `m`'s
fresh defs are defined (`D'`), the upgraded environment describes the variables. -/
theorem upg_sound :
    ∀ (k : Nat) (a : A) {D D' : Nat → Prop} {e : AEnv} {w : V} {m : MInst}, (∀ n, D n → D' n) →
      EnvOK c D env e → γ c a D env w →
      MInst.ofV w = some m → (∀ r ∈ useRegsK m ++ defRegsK m, OkReg r) →
      (∀ n ∈ defVregs m, c.lo ≤ n → D' n) → EnvOK c D' env (upg e k a)
  | 0, _, _, _, _, _, _, hD, he, _, _, _, _ => by simpa [upg] using he.mono hD
  | k + 1, a, D, D', e, w, m, hD, he, h, hm, hok, hdef => by
    cases a with
    | sym y =>
      simp only [upg]
      have hyw : env[y]? = some (some w) := h
      have hDI : DefsIn c D' env y := by
        intro w' hw'
        rw [hyw] at hw'
        cases hw'
        exact ⟨m, hm, hdef⟩
      have hd := dropAft_sound he hD hDI
      split
      · rename_i a' hget
        obtain ⟨w', hw', hg⟩ := (he.2 y).2 a' (getD_some_iff.mp hget)
        rw [hyw] at hw'
        cases hw'
        exact upg_sound k a' (fun _ h => h) hd (γ_mono a' hD hg) hm hok hdef
      · exact hd
    | data τ k' fs =>
      simp only [upg]
      split
      · rename_i hτ
        have hτ' : τ = tyMInst := by simpa using hτ
        subst hτ'
        obtain ⟨vs, rfl, hl⟩ := h
        obtain ⟨ks, hks, -, -, -, hd, hc⟩ := ofV_fields hm
        obtain ⟨-, hdv⟩ := operands_okRegs hok
        rw [hks]
        refine upgF_sound fs ks (he.mono hD) (γL_mono fs hD hl) (fun v hv => ?_) (fun v hv => ?_)
        · obtain ⟨r, rfl, hr⟩ := hd v hv
          exact ⟨r, rfl, fun n cl hrn hlo => hdef n (hdv n cl (hrn ▸ hr)) hlo⟩
        · obtain ⟨ci, rfl, hq⟩ := hc v hv
          exact ⟨ci, rfl, fun q hq' n cl hqn hlo => hdef n (hdv n cl (hqn ▸ hq q hq')) hlo⟩
      · exact he.mono hD
    | _ => simpa [upg] using he.mono hD

end Upg

/-! ## Flag/side-effect values and the type predicates -/

section Ty
variable {env : Isle.Interp.Env V}

theorem DD_cons {D : Nat → Prop} {m : MInst} {ms : List MInst} :
    ∀ n, DD c (DD c D [m]) ms n → DD c D (m :: ms) n := by
  intro n h
  rcases h with (h | ⟨h1, m', hm', h2⟩) | ⟨h1, m', hm', h2⟩
  · exact .inl h
  · exact .inr ⟨h1, m', by simp_all, h2⟩
  · exact .inr ⟨h1, m', List.mem_cons_of_mem _ hm', h2⟩

theorem DD_nil {D : Nat → Prop} : ∀ n, D n → DD c D [] n := fun _ h => .inl h

theorem le_DD {D : Nat → Prop} (ms : List MInst) : ∀ n, D n → DD c D ms n := fun _ h => .inl h

theorem emitSeq_len {e : AEnv} {n : Nat} :
    ∀ (fs : List A) (sh : List SK) {e' : AEnv}, emitSeq e n fs sh = some e' → fs.length = sh.length
  | f :: fs, s :: ss, e', h => by
    cases s with
    | i =>
      simp only [emitSeq] at h
      split at h
      · exact congrArg (· + 1) (emitSeq_len fs ss h)
      · cases h
    | r => simp only [emitSeq] at h; exact congrArg (· + 1) (emitSeq_len fs ss h)
    | o => simp only [emitSeq] at h; exact congrArg (· + 1) (emitSeq_len fs ss h)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [emitSeq] at h
  | _ :: _, [], _, h => by simp [emitSeq] at h

theorem γL_len {D : Nat → Prop} : ∀ {as : List A} {vs : List V}, γL c as D env vs → as.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg (· + 1) (γL_len h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem instIdx_zero (sh : List SK) : instIdx sh 0 = [] := rfl

theorem instIdx_succ (s : SK) (sh : List SK) (j : Nat) :
    instIdx (s :: sh) (j + 1) = (if s = .i then [0] else []) ++ (instIdx sh j).map (· + 1) := by
  unfold instIdx
  rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
  have : ((fun i => (s :: sh)[i]? == some SK.i) ∘ fun x => x + 1) = fun i => sh[i]? == some SK.i := by
    funext i; simp
  rw [this]
  by_cases hs : s = .i <;> simp [hs]

theorem earlier_zero (fs : List V) (sh : List SK) : earlier fs sh 0 = [] := rfl

theorem earlier_succ (v : V) (fs : List V) (s : SK) (sh : List SK) (j : Nat) :
    earlier (v :: fs) (s :: sh) (j + 1) = (if s = .i then [v] else []) ++ earlier fs sh j := by
  unfold earlier
  rw [instIdx_succ, List.filterMap_append, List.filterMap_map]
  by_cases hs : s = .i <;> simp [hs, Function.comp_def]

/-- **Emitting the instructions of a flag/side-effect value in order.** -/
theorem emitSeq_sound {n : Nat} :
    ∀ (fs : List A) (sh : List SK) {D : Nat → Prop} {e e' : AEnv} {vs : List V},
      EnvOK c D env e → γL c fs D env vs → emitSeq e n fs sh = some e' →
      (∀ (j : Nat) w, vs[j]? = some w → sh[j]? = some .i → ∀ ms,
        (earlier vs sh j).mapM MInst.ofV = some ms → MIok (DD c D ms) w) ∧
      (∀ ms, (earlier vs sh sh.length).mapM MInst.ofV = some ms → EnvOK c (DD c D ms) env e')
  | f :: fs, s :: ss, D, e, e', v :: vs, he, h, hs => by
    cases s with
    | i =>
      simp only [emitSeq] at hs
      split at hs
      · rename_i hfit
        have hmi := fitsMI_sound he h.1 hfit
        cases hm0 : MInst.ofV v with
        | none =>
          refine ⟨fun j w hw hj ms hms => ?_, fun ms hms => ?_⟩
          · cases j with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
              subst hw
              exact MIok_mono (le_DD ms) hmi
            | succ j =>
              rw [earlier_succ] at hms
              simp only [↓reduceIte, List.singleton_append, List.mapM_cons, hm0] at hms
              cases hms
          · rw [List.length_cons, earlier_succ] at hms
            simp only [↓reduceIte, List.singleton_append, List.mapM_cons, hm0] at hms
            cases hms
        | some m0 =>
          have he1 := upg_sound n f (D' := DD c D [m0]) (le_DD _) he h.1 hm0 (hmi m0 hm0).2
            fun k hk hlo => .inr ⟨hlo, m0, List.mem_cons_self, hk⟩
          obtain ⟨ih1, ih2⟩ := emitSeq_sound fs ss he1 (γL_mono fs (le_DD _) h.2) hs
          refine ⟨fun j w hw hj ms hms => ?_, fun ms hms => ?_⟩
          · cases j with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
              subst hw
              exact MIok_mono (le_DD ms) hmi
            | succ j =>
              simp only [List.getElem?_cons_succ] at hw hj
              rw [earlier_succ] at hms
              simp only [↓reduceIte, List.singleton_append, List.mapM_cons, hm0] at hms
              cases hms' : (earlier vs ss j).mapM MInst.ofV with
              | none => rw [hms'] at hms; cases hms
              | some ms' =>
                rw [hms'] at hms
                cases hms
                exact MIok_mono DD_cons (ih1 j w hw hj ms' hms')
          · rw [List.length_cons, earlier_succ] at hms
            simp only [↓reduceIte, List.singleton_append, List.mapM_cons, hm0] at hms
            cases hms' : (earlier vs ss ss.length).mapM MInst.ofV with
            | none => rw [hms'] at hms; cases hms
            | some ms' =>
              rw [hms'] at hms
              cases hms
              exact (ih2 ms' hms').mono DD_cons
      · cases hs
    | r =>
      simp only [emitSeq] at hs
      obtain ⟨ih1, ih2⟩ := emitSeq_sound fs ss he h.2 hs
      refine ⟨fun j w hw hj ms hms => ?_, fun ms hms => ?_⟩
      · cases j with
        | zero => simp at hj
        | succ j =>
          simp only [List.getElem?_cons_succ] at hw hj
          rw [earlier_succ] at hms
          simp only [reduceCtorEq, ↓reduceIte, List.nil_append] at hms
          exact ih1 j w hw hj ms hms
      · rw [List.length_cons, earlier_succ] at hms
        simp only [reduceCtorEq, ↓reduceIte, List.nil_append] at hms
        exact ih2 ms hms
    | o =>
      simp only [emitSeq] at hs
      obtain ⟨ih1, ih2⟩ := emitSeq_sound fs ss he h.2 hs
      refine ⟨fun j w hw hj ms hms => ?_, fun ms hms => ?_⟩
      · cases j with
        | zero => simp at hj
        | succ j =>
          simp only [List.getElem?_cons_succ] at hw hj
          rw [earlier_succ] at hms
          simp only [reduceCtorEq, ↓reduceIte, List.nil_append] at hms
          exact ih1 j w hw hj ms hms
      · rw [List.length_cons, earlier_succ] at hms
        simp only [reduceCtorEq, ↓reduceIte, List.nil_append] at hms
        exact ih2 ms hms
  | [], [], _, e, e', [], he, _, hs => by
    simp only [emitSeq, Option.some.injEq] at hs
    subst hs
    refine ⟨fun j w hw => by simp at hw, fun ms hms => ?_⟩
    simp only [List.length_nil, earlier_zero, List.mapM_nil] at hms
    obtain rfl : ms = [] := (Option.some.inj hms).symm
    exact he.mono DD_nil
  | [], _ :: _, _, _, _, _, _, _, hs => by simp [emitSeq] at hs
  | _ :: _, [], _, _, _, _, _, _, hs => by simp [emitSeq] at hs
  | _ :: _, _ :: _, _, _, _, [], _, h, _ => h.elim
  | [], [], _, _, _, _ :: _, _, h, _ => h.elim

/-- The other and result fields. -/
theorem restOk_sound {D D' : Nat → Prop} (hD : ∀ n, D n → D' n) {e e' : AEnv}
    (he : EnvOK c D env e) (he' : EnvOK c D' env e') {n : Nat} {z : Bool} :
    ∀ (fs : List A) (sh : List SK) {vs : List V}, γL c fs D env vs →
      restOk e e' n z fs sh = true → ∀ (j : Nat) f, vs[j]? = some f →
        (sh[j]? = some .o → Cl c false true D f) ∧ (sh[j]? = some .r → Cl c false z D' f)
  | g :: fs, s :: ss, v :: vs, h, hr => by
    simp only [restOk, Bool.and_eq_true] at hr
    intro j f hf
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf ⊢
      subst hf
      refine ⟨fun hs => ?_, fun hs => ?_⟩
      · subst hs
        exact fitsCl_sound he n false true g h.1 hr.1
      · subst hs
        exact fitsCl_sound he' n false z g (γ_mono g hD h.1) hr.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hf ⊢
      exact restOk_sound hD he he' fs ss h.2 hr.2 j f hf
  | [], [], [], _, _ => fun j f hf => by simp at hf
  | [], _ :: _, _, _, hr => by simp [restOk] at hr
  | _ :: _, [], _, _, hr => by simp [restOk] at hr
  | _ :: _, _ :: _, [], h, _ => h.elim
  | [], [], _ :: _, h, _ => h.elim

/-- The other fields only (the result environment is not needed). -/
theorem restOk_o {D : Nat → Prop} {e e' : AEnv} (he : EnvOK c D env e) {n : Nat} {z : Bool} :
    ∀ (fs : List A) (sh : List SK) {vs : List V}, γL c fs D env vs →
      restOk e e' n z fs sh = true → ∀ (j : Nat) f, vs[j]? = some f →
        sh[j]? = some .o → Cl c false true D f
  | g :: fs, s :: ss, v :: vs, h, hr => by
    simp only [restOk, Bool.and_eq_true] at hr
    intro j f hf hs
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf hs
      subst hf hs
      exact fitsCl_sound he n false true g h.1 hr.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hf hs
      exact restOk_o he fs ss h.2 hr.2 j f hf hs
  | [], [], [], _, _ => fun j f hf => by simp at hf
  | [], _ :: _, _, _, hr => by simp [restOk] at hr
  | _ :: _, [], _, _, hr => by simp [restOk] at hr
  | _ :: _, _ :: _, [], h, _ => h.elim
  | [], [], _ :: _, h, _ => h.elim

theorem flagShape_mem {τ k : Nat} {sh : List SK} (h : flagShape τ k = some sh) : τ ∈ flagTys := by
  unfold flagShape at h
  split at h <;> first | (cases h; done) | simp [flagTys]

theorem crShape_eq {τ k : Nat} {cs : List Bool} (h : crShape τ k = some cs) :
    τ = TyId.«CondResult» := by
  unfold crShape at h
  split at h <;> first | (cases h; done) | rfl

theorem PT_flag {z : Bool} {D : Nat → Prop} {τ : TypeId} (hτ : τ ∈ flagTys) {v : V} :
    PT c z D τ v ↔ Cl c false z D v ∨ FlagP c z D τ v := by
  have h1 : τ ≠ tyMInst := by
    intro e; subst e; simp only [flagTys, List.mem_cons, List.mem_nil_iff, or_false] at hτ
    rcases hτ with h | h | h | h <;> exact absurd h (by decide)
  have h2 : τ ∉ ciTys := by
    intro h; simp only [ciTys, flagTys, List.mem_cons, List.mem_nil_iff, or_false] at h hτ
    rcases h with rfl | rfl <;> rcases hτ with h | h | h | h <;> exact absurd h (by decide)
  simp [PT, h1, h2, hτ]

theorem PT_cr {z : Bool} {D : Nat → Prop} {v : V} :
    PT c z D TyId.«CondResult» v ↔ Cl c false z D v ∨ CrP c z D TyId.«CondResult» v := by
  unfold PT
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem PT_cl {z : Bool} {D : Nat → Prop} {τ : TypeId} (h1 : τ ≠ tyMInst) (h2 : τ ∉ ciTys) {v : V}
    (h : Cl c false z D v) : PT c z D τ v := by
  unfold PT
  simp only [h1, h2, ↓reduceIte]
  split
  · exact .inl h
  · split
    · exact .inl h
    · exact h

variable {D : Nat → Prop} {e : AEnv}

/-- **`fitsTy` is sound.** -/
theorem fitsTy_sound (he : EnvOK c D env e) :
    ∀ (n : Nat) (a : A) (τ : TypeId) (z : Bool) {w : V}, γ c a D env w →
      fitsTy e n a τ z = true → PT c z D τ w
  | 0, _, _, _, _, _, hf => by simp [fitsTy] at hf
  | n + 1, a, τ, z, w, h, hf => by
    simp only [fitsTy] at hf
    by_cases h1 : τ = tyMInst
    · subst h1
      simp only [beq_self_eq_true, ↓reduceIte] at hf
      simpa [PT] using fitsMI_sound he h hf
    have h1' : (τ == tyMInst) = false := by simpa using h1
    rw [h1'] at hf
    simp only [Bool.false_eq_true, ↓reduceIte] at hf
    by_cases h2 : τ ∈ ciTys
    · have h2' : ciTys.contains τ = true := by simpa using h2
      rw [h2'] at hf
      simp only [↓reduceIte] at hf
      have := fitsCI_sound he h hf
      simp [PT, h1, h2, this]
    have h2' : ciTys.contains τ = false := by simpa using h2
    rw [h2'] at hf
    simp only [Bool.false_eq_true, ↓reduceIte] at hf
    have hr := res_sound he n a h
    split at hf
    · rename_i τ' z' hra
      rw [hra] at hr
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      obtain ⟨rfl, hz⟩ := hf
      exact PT_mono (fun _ h => h) (fun hz' => by cases z' <;> simp_all) hr
    · rename_i z' hra
      rw [hra] at hr
      exact PT_cl h1 h2 (Cl_mono (fun _ h => h) id (fun hz' => by cases z' <;> simp_all) hr)
    · rename_i τ' k fs hra
      rw [hra] at hr
      obtain ⟨vs, rfl, hl⟩ := hr
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      obtain ⟨rfl, hf⟩ := hf
      split at hf
      · rename_i sh hsh
        have hτ := flagShape_mem hsh
        unfold flagOk at hf
        split at hf
        · rename_i e' hes
          obtain ⟨hi, he'⟩ := emitSeq_sound fs sh he hl hes
          refine (PT_flag hτ).mpr (.inr ⟨k, vs, sh, rfl, hsh, ?_, fun j f hf' => ⟨?_, ?_, ?_⟩⟩)
          · rw [← γL_len hl]; exact emitSeq_len fs sh hes
          · exact restOk_o he fs sh hl hf j f hf'
          · exact hi j f hf'
          · intro hs ms hms
            exact (restOk_sound (le_DD ms) he (he' ms hms) fs sh hl hf j f hf').2 hs
        · cases hf
      · split at hf
        · rename_i cs hcs
          have hτ := crShape_eq hcs
          subst hτ
          refine PT_cr.mpr (.inr ⟨k, vs, cs, rfl, hcs, ?_, ?_⟩)
          · rw [← γL_len hl]; exact crOk_len fs cs hf
          · exact crOk_sound n (fitsTy_sound he n) fs cs hl hf
        · cases hf
    · cases hf
where
  crOk_len : ∀ (fs : List A) (cs : List Bool) {n : Nat} {z : Bool},
      fitsTy.crOk e n z fs cs = true → fs.length = cs.length
    | _ :: fs, _ :: cs, _, _, h => by
      simp only [fitsTy.crOk, Bool.and_eq_true] at h
      exact congrArg (· + 1) (crOk_len fs cs h.2)
    | [], [], _, _, _ => rfl
    | [], _ :: _, _, _, h => by simp [fitsTy.crOk] at h
    | _ :: _, [], _, _, h => by simp [fitsTy.crOk] at h
  crOk_sound (n : Nat) {z : Bool}
      (ih : ∀ (a : A) (τ : TypeId) (z : Bool) {w : V}, γ c a D env w → fitsTy e n a τ z = true →
        PT c z D τ w) :
      ∀ (fs : List A) (cs : List Bool) {vs : List V}, γL c fs D env vs →
        fitsTy.crOk e n z fs cs = true →
        ∀ (i : Nat) f b, vs[i]? = some f → cs[i]? = some b →
          (b = true → Cl c false z D f ∨ FlagP c z D TyId.«ProducesFlags» f) ∧
          (b = false → Cl c false z D f)
    | g :: fs, b' :: cs, v :: vs, h, hf => by
      simp only [fitsTy.crOk, Bool.and_eq_true] at hf
      intro i f b hv hb
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hb
        subst hv hb
        refine ⟨fun hb => ?_, fun hb => ?_⟩
        · subst hb
          simp only [↓reduceIte] at hf
          exact (PT_flag (by simp [flagTys])).mp (ih g _ z h.1 hf.1)
        · subst hb
          simp only [Bool.false_eq_true, ↓reduceIte] at hf
          exact fitsCl_sound he n false z g h.1 hf.1
      | succ i =>
        simp only [List.getElem?_cons_succ] at hv hb
        exact crOk_sound n ih fs cs h.2 hf.2 i f b hv hb
    | [], [], [], _, _ => fun i f b hv => by simp at hv
    | [], _ :: _, _, _, hf => by simp [fitsTy.crOk] at hf
    | _ :: _, [], _, _, hf => by simp [fitsTy.crOk] at hf
    | _ :: _, _ :: _, [], h, _ => h.elim
    | [], [], _ :: _, h, _ => h.elim

/-- **`fitsA` is sound** (summaries `top`, `cl`, `wr`, `ty`). -/
theorem fitsA_sound (he : EnvOK c D env e) {n : Nat} {a b : A} {w : V} (h : γ c a D env w)
    (hf : fitsA e n a b = true) : γ c b D env w := by
  cases b with
  | top => trivial
  | cl b z => exact fitsCl_sound he n b z a h hf
  | wr z => exact fitsWr_sound he h hf
  | ty τ z => exact fitsTy_sound he n a τ z h hf
  | _ => simp [fitsA] at hf

theorem fitsAL_sound (he : EnvOK c D env e) {n : Nat} :
    ∀ {as bs : List A} {vs : List V}, γL c as D env vs → fitsAL e n as bs = true → γL c bs D env vs
  | a :: as, b :: bs, v :: vs, h, hf => by
    simp only [fitsAL, Bool.and_eq_true] at hf
    exact ⟨fitsA_sound he h.1 hf.1, fitsAL_sound he h.2 hf.2⟩
  | [], [], [], _, _ => trivial
  | [], _ :: _, _, _, hf => by simp [fitsAL] at hf
  | _ :: _, [], _, _, hf => by simp [fitsAL] at hf
  | _ :: _, _ :: _, [], h, _ => h.elim
  | [], [], _ :: _, h, _ => h.elim

end Ty

end Backend.Proof.DefGen

