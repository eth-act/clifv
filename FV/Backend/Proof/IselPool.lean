import FV.Backend.Proof.IselCovTCtor
import FV.Backend.Proof.IselFlowData
import FV.Backend.Proof.LowerLoopCtx

/-!
# Constant-pool entries in ISLE values (#1002): the extern helpers and the driver's data

`V.poolIn v`: the value holds a constant-pool entry (`Opnd.vcodeConst`, the `VCodeConstant` of
`emit_u64_le_const`, #565). The literal-pool load `fpuLoad _ _ (.const _) _` is built only from
`MInst` data holding one (`ofV_pool`: `AMode.Const`'s field, `amode_const_pool`), and only
`emit_u64_le_const` makes one:

* `externCtor_pool`: the result of every other extern constructor holds an entry only if an
  argument does;
* `externExtract_pool`: an extern extractor's outputs hold none when its input and the context's
  instruction data hold none (`DataP`);
* `ctor_noPool`: an extern constructor called on arguments without entry emits no literal-pool
  load (`NoPoolSince`; the emitted forms are `Cov.EmitOk`'s, `CovT.externCtor_covT`);
* the data the driver builds holds none (`instData_poolIn`, `termData_poolIn`,
  `tryCallData_poolIn`), so the driver's contexts meet `DataP` (`dataP_of_build`,
  `dataP_termCtx`, `dataP_tryCtx`).

The uniform invariant of the ISLE runs over these facts is in `IselPoolFree`.
-/

namespace Backend.Proof.Pool

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Driver Isle Isle.Aarch64

/-! ## Pool entries inside a value -/

/-- The operand is a constant-pool entry. -/
def opPool : Opnd → Bool
  | .vcodeConst _ => true
  | _ => false

mutual
/-- Does the value hold a constant-pool entry (`Opnd.vcodeConst`)? -/
def _root_.Backend.V.poolIn : V → Bool
  | .op o => opPool o
  | .data _ _ fs => poolInL fs
  | _ => false
/-- Does a value of the list hold a constant-pool entry? -/
def poolInL : List V → Bool
  | [] => false
  | v :: vs => v.poolIn || poolInL vs
end

@[simp] theorem poolInL_nil : poolInL [] = false := rfl
@[simp] theorem poolInL_cons (v : V) (vs : List V) :
    poolInL (v :: vs) = (v.poolIn || poolInL vs) := rfl

theorem poolInL_eq_false : ∀ {vs : List V}, poolInL vs = false ↔ ∀ w ∈ vs, w.poolIn = false
  | [] => by simp
  | v :: vs => by simp [poolInL_eq_false]

theorem poolIn_data (ty : TypeId) (k : Nat) (fs : List V) :
    (V.data ty k fs).poolIn = poolInL fs := by
  simp [V.poolIn]

/-! ## The literal-pool load comes from data holding an entry -/

/-- An instruction that is a literal-pool load only if `v` holds a constant-pool entry. -/
def PoolSrc (v : V) (m : MInst) : Prop :=
  ∀ sz rd c fl, m = .fpuLoad sz rd (.const c) fl → v.poolIn = true

/-- An `AMode.Const` value holds its constant-pool entry. -/
theorem amode_const_pool {v : V} {c : Nat} (h : v.amode? = some (.const c)) : v.poolIn = true := by
  unfold V.amode? at h
  obtain ⟨⟨k, fs⟩, he, h2⟩ := bind_some_ex h
  rw [enumOf_eq he]
  dsimp only at h2
  split at h2
  all_goals (repeat' (first | (obtain ⟨_, _, h2⟩ := bind_some_ex h2) | split at h2))
  all_goals first
    | (cases h2; done)
    | (simp only [pure, Option.some.injEq, reduceCtorEq] at h2; done)
    | simp [V.poolIn, opPool]

/-- **`MInst.ofV`** builds a literal-pool load only from data holding a constant-pool entry. -/
theorem ofV_pool {v : V} {m : MInst} (h : MInst.ofV v = some m) : PoolSrc v m := by
  unfold MInst.ofV at h
  obtain ⟨⟨k, fs⟩, he, h2⟩ := bind_some_ex h
  clear h
  rw [enumOf_eq he]
  revert h2
  revert m
  apply _root_.ofV_split _ (fun k fs (r : Option MInst) => ∀ m, r = some m →
    PoolSrc (V.data tyMInst k fs) m)
  all_goals
    intros
    rename_i m hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := bind_some_ex hm) | split at hm)
    all_goals first
      | (cases hm; done)
      | (simp only [pure, Option.some.injEq] at hm
         subst hm
         intro sz rd c fl h
         first
           | (cases h; done)
           | (cases h
              have hp := amode_const_pool (by assumption)
              simp [V.poolIn, hp]))

/-! ## Extern constructors -/

/-- The result of a constructor other than `emit_u64_le_const` holds a constant-pool entry only if
an argument does. -/
def CtorPool (id : TermId) (args : List V) (r : ExtResult (V × LState)) : Prop :=
  ∀ v st', r = .ok (v, st') → id ≠ TId.emit_u64_le_const → v.poolIn = true → poolInL args = true

set_option maxHeartbeats 2000000 in
/-- **Every extern constructor but `emit_u64_le_const`** returns a constant-pool entry only from
its arguments. -/
theorem externCtor_pool (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    CtorPool t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h
      intro _ hv
      simp [V.poolIn] at hv
    · cases h
  · apply _root_.externCtor_split _ CtorPool
    all_goals
      intros
      unfold CtorPool
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | (intro hid hv
         simp_all (config := { decide := true }) [V.poolIn, opPool]
         done)
      | (rename_i heq
         simp only [Option.map_eq_some_iff, Function.comp_apply] at heq
         obtain ⟨_, _, rfl⟩ := heq
         intro hid hv
         simp [V.poolIn, opPool] at hv)
      | (intro hid hv
         simp [V.poolIn, opPool] at hv
         done)

/-! ## Extern extractors -/

/-- The instruction data of the context holds no constant-pool entry. -/
def DataP (ctx : Ctx) : Prop :=
  ∀ (i : Nat) (info : IInfo), ctx.insts[i]? = some info → info.data.poolIn = false

/-- The outputs of an extractor on an input without constant-pool entry hold none. -/
def ExtPool (v : V) (r : ExtResult (List V)) : Prop :=
  ∀ fs, r = .ok fs → v.poolIn = false → ∀ f ∈ fs, f.poolIn = false

set_option maxHeartbeats 2000000 in
/-- **Every extern extractor** gives values without constant-pool entry from one without. -/
theorem externExtract_pool {ctx : Ctx} (hd : DataP ctx) (t : Term) (v : V) (st : LState) :
    ExtPool v (externExtract ctx t v st) := by
  unfold externExtract
  split
  · intro fs h
    split at h
    · cases h
      intro _
      simp [V.poolIn]
    · cases h
  · intro fs h; cases h
  · apply _root_.externExtract_split _ (fun _ v r => ExtPool v r)
    all_goals
      intros
      unfold ExtPool
      intro fs h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | (intro hv
         simp_all (config := { decide := true }) [V.poolIn, opPool]
         done)
      | (intro hv
         simp only [List.forall_mem_cons]
         exact ⟨rfl, hd _ _ ‹_›, fun _ h => by cases h⟩)

/-! ## The instructions a constructor emits -/

/-- No literal-pool load was emitted from `s` to `s'`. -/
def NoPoolSince (s s' : LState) : Prop :=
  ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
    ∀ m ∈ ms, ∀ sz rd c fl, m ≠ .fpuLoad sz rd (.const c) fl

theorem noPool_refl (s : LState) : NoPoolSince s s := ⟨[], by simp, by simp⟩

theorem noPool_trans {a b c : LState} (h1 : NoPoolSince a b) (h2 : NoPoolSince b c) :
    NoPoolSince a c := by
  obtain ⟨ms, g1, g2⟩ := h1
  obtain ⟨ms', g3, g4⟩ := h2
  refine ⟨ms ++ ms', by simp [g3, g1], fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact g2 m hm
  · exact g4 m hm

/-- A control form or a `FormOk` form is not a literal-pool load. -/
theorem covered_ne_const {i : MInst} (h : Cov.Covered i = true) :
    ∀ sz rd c fl, i ≠ .fpuLoad sz rd (.const c) fl := by
  rintro sz rd c fl rfl
  simp only [Cov.Covered, Bool.or_eq_true] at h
  rcases h with h | h
  · cases h
  · unfold FormOk at h
    split at h <;> simp_all [memOk]
    all_goals
      obtain ⟨-, -, rfl, -⟩ := ‹_ ∧ _ ∧ AMode.const _ = _ ∧ _›
      simp at h

/-- **An extern constructor** called on arguments without constant-pool entry emits no
literal-pool load. -/
theorem ctor_noPool (ctx : Ctx) {term : Term} {vs : List V} {s : LState} {v : V} {s' : LState}
    (hvs : poolInL vs = false) (h : (sem ctx).ctor term vs s = .ok (v, s')) : NoPoolSince s s' := by
  rw [CovT.sem_ctor] at h
  rcases CovT.externCtor_covT ctx term vs s v s' h with ⟨_, _, _, _, _, _, rfl⟩ | hc
  · exact noPool_refl _
  · obtain ⟨ms, h1, h2⟩ := hc.emit
    refine ⟨ms, h1, fun m hm sz rd c fl he => ?_⟩
    rcases h2 m hm with hcov | ⟨-, i, rfl, hi⟩ | ⟨-, r, b, off, hst, -⟩
    · exact covered_ne_const hcov sz rd c fl he
    · have hp := ofV_pool hi sz rd c fl he
      simp [hp] at hvs
    · rw [he] at hst
      unfold stackArgStore at hst
      split at hst <;> cases hst

/-! ## The data the driver builds -/

theorem poolIn_mkVariant {ty : TypeId} {name : String} {fs : List V} (h : poolInL fs = false) :
    (mkVariant ty name fs).poolIn = false := by
  unfold mkVariant
  split
  · simp [V.poolIn, h]
  · simp [V.poolIn, opPool]

theorem poolInL_nil' : poolInL [] = false := rfl

theorem poolInL_cons' {v : V} {vs : List V} (h1 : v.poolIn = false) (h2 : poolInL vs = false) :
    poolInL (v :: vs) = false := by simp [h1, h2]

theorem poolIn_int {i : Int} : (V.int i).poolIn = false := by simp [V.poolIn]
theorem poolIn_value {x : Nat} : (V.value x).poolIn = false := by simp [V.poolIn]
theorem poolIn_values {xs : List Nat} : (V.values xs).poolIn = false := by simp [V.poolIn]
theorem poolIn_blockCalls {bs : List Nat} : (V.blockCalls bs).poolIn = false := by
  simp [V.poolIn]
theorem poolIn_op {o : Opnd} (h : opPool o = false) : (V.op o).poolIn = false := by
  simp [V.poolIn, h]

/-- Build `poolIn = false` of an `instDataV` term. -/
macro "pool_data" : tactic => `(tactic| (
  unfold instDataV opcodeV
  repeat' first
    | with_reducible apply poolIn_mkVariant
    | with_reducible exact poolInL_nil'
    | with_reducible apply poolInL_cons'
    | with_reducible exact poolIn_int
    | with_reducible exact poolIn_value
    | with_reducible exact poolIn_values
    | with_reducible exact poolIn_op rfl
    | with_reducible exact poolIn_blockCalls))

set_option maxRecDepth 20000 in
/-- The data of a statement holds no constant-pool entry. -/
theorem instData_poolIn {f : Clif.Function} {c : Clif.Inst} {d : V} (h : instData f c = .ok d) :
    d.poolIn = false := by
  cases c <;> simp only [instData] at h
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       pool_data)

/-- The data of a terminator holds no constant-pool entry. -/
theorem termData_poolIn {t : Clif.Terminator} {d : V} (h : termData t = .ok d) :
    d.poolIn = false := by
  cases t <;> simp only [termData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       pool_data)

set_option maxRecDepth 20000 in
/-- The data of a `try_call` holds no constant-pool entry. -/
theorem tryCallData_poolIn {f : Clif.Function} {t : Clif.Terminator} {d : V}
    (h : tryCallData f t = .ok d) : d.poolIn = false := by
  cases t <;> simp only [tryCallData] at h
  all_goals first
    | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
    | skip
  all_goals
    rename_i et
    cases he : exnTableOpnd f et with
    | error e => rw [he] at h; cases h
    | ok q =>
      rw [he] at h
      obtain ⟨sig, items⟩ := q
      simp only [bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst h
           pool_data)

/-! ## The driver's contexts -/

/-- **`buildCtx`'s context** meets `DataP`: its entries are the terminators' placeholders and
the statements' `instData`. -/
theorem dataP_of_build {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} (hb : buildCtx f = .ok (ctx, ranges, st0)) : DataP ctx := by
  have sp := ctxSpec_of hb
  intro i info hi
  rcases sp.insts info (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi)) with
    rfl | ⟨B, hB, s, hs, rfl⟩
  · simp [V.poolIn, opPool]
  · obtain ⟨d, hd⟩ := ((sp.blockC B hB).2 s hs).1
    have hdo : (infoOf f s).data = d := by
      show dataOf f s = d
      unfold dataOf
      rw [hd]
    rw [hdo]
    exact instData_poolIn hd

/-- Setting a terminator slot to data without constant-pool entry keeps `DataP`. -/
theorem dataP_termCtx {ctx : Ctx} (h : DataP ctx) {data : V} (hd : data.poolIn = false)
    (ti : Nat) : DataP (termCtx ctx ti data) := by
  intro j info hj
  by_cases hji : j = ti
  · subst hji
    by_cases hlt : j < ctx.insts.size
    · have : (termCtx ctx j data).insts[j]? = some ⟨data, [], [], none⟩ := by
        show (ctx.insts.set! j _)[j]? = _
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt]
      rw [this] at hj
      cases hj
      exact hd
    · have : (termCtx ctx j data).insts = ctx.insts := by
        show ctx.insts.set! j _ = _
        rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
        simp [hlt]
      rw [this] at hj
      exact h j info hj
  · rw [termCtx_insts_ne hji] at hj
    exact h j info hj

theorem dataP_tryCtx {ctx : Ctx} (h : DataP ctx) {data : V} (hd : data.poolIn = false)
    (ti : Nat) (trs : List Reg × List Reg) : DataP (tryCtx ctx ti data trs) :=
  dataP_termCtx h hd ti

end Backend.Proof.Pool
