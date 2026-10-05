import FV.Backend.Proof.KillBase
import FV.Backend.Proof.LowerRename

/-!
# The killed vregs and the uses of an emitted instruction (`MInst.ofV`)

`ofV_kill`: an instruction built from an ISLE value `v` reads only registers of `v` outside a
call's defs (`V.regsK`), kills nothing unless `v` holds `AtomicRMWLoop`/`AtomicCASLoop`/
`JTSequence` data (`V.kIn`), a call's defs are registers of `v`'s call defs (`V.regsD`), and it
is no `tryCall`.

The operand view (`MInst.operands`) is related to the instruction's registers by kind
(`useRegsK`, `defRegsK`) through an invariant of the operand visitor (`KInv`); `ofV` is split
into its variants (`ofV_split`).
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Aarch64

/-! ## The registers of an instruction by operand kind -/

/-- The vreg sides of the fixed-use pairs of `call`/`tryCall`/`rets`. -/
def pairUses : MInst → List Reg
  | .call c | .tryCall c _ => c.uses.map (·.1)
  | .rets us => us.map (·.1)
  | _ => []

/-- The defs `MInst.defs` leaves out: the fixed-def pairs and the LL/SC scratch registers. -/
def pairDefs : MInst → List Reg
  | .call c | .tryCall c _ => c.defs.map (·.2)
  | .args ds => ds.map (·.1)
  | .atomicRmwLoop _ _ _ _ _ _ s1 s2 => [s1, s2]
  | .atomicCasLoop _ _ _ _ _ _ sc => [sc]
  | _ => []

/-- The registers an instruction visits as uses. -/
def useRegsK (m : MInst) : List Reg := m.uses ++ pairUses m

/-- The registers an instruction visits as defs. -/
def defRegsK (m : MInst) : List Reg := m.defs ++ pairDefs m

/-- The collected operands are registers of `U` (uses) and `D` (defs). -/
def OpsIn (U D : List Reg) (s : Array Operand) : Prop :=
  ∀ o ∈ s.toList, (o.kind = .use → Reg.vreg o.vreg o.cls ∈ U) ∧
    (o.kind = .def → Reg.vreg o.vreg o.cls ∈ D)

/-- A step of the operand visitor keeps `OpsIn U D`. -/
def KInv (U D : List Reg) {α : Type} (x : OpM α) : Prop :=
  ∀ s a s', x.run s = .ok (a, s') → OpsIn U D s → OpsIn U D s'

section
variable {U D : List Reg}

theorem KInv.pure {α : Type} (a : α) : KInv U D (Pure.pure a : OpM α) := by
  intro s b s' h hs
  cases h
  exact hs

theorem KInv.bind {α β : Type} {x : OpM α} {k : α → OpM β} (hx : KInv U D x)
    (hk : ∀ a, KInv U D (k a)) : KInv U D (x >>= k) := by
  intro s b s' h hs
  rw [StateT.run_bind] at h
  cases hr : x.run s with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [hr] at h
    exact hk a s1 b s' h (hx s a s1 hr hs)

theorem KInv.collect (sp : OpSpec) (r : Reg) (hu : sp.kind = .use → r ∈ U)
    (hd : sp.kind = .def → r ∈ D) : KInv U D (collectOp sp r) := by
  intro s a s' h hs
  cases r
  case vreg n c =>
    simp only [collectOp, StateT.run, modify, modifyGet, MonadStateOf.modifyGet] at h
    cases h
    intro o ho
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact hs o ho
    · exact ⟨hu, hd⟩
  all_goals
    simp only [collectOp] at h
    split at h
    · cases h
    · cases h; exact hs

theorem KInv.map {α β : Type} (f : α → β) {x : OpM α} (hx : KInv U D x) : KInv U D (f <$> x) := by
  rw [map_eq_pure_bind]
  exact KInv.bind hx fun a => KInv.pure _

theorem KInv.mapM {α β : Type} {F : α → OpM β} :
    ∀ (l : List α), (∀ a ∈ l, KInv U D (F a)) → KInv U D (l.mapM F)
  | [], _ => KInv.pure _
  | a :: l, h => by
    rw [List.mapM_cons]
    exact KInv.bind (h a List.mem_cons_self) fun b =>
      KInv.bind (KInv.mapM l fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) fun bs => KInv.pure _

theorem KInv.amode (am : AMode) (h : ∀ r ∈ am.regs, r ∈ U) :
    KInv U D (AMode.visit collectOp am) := by
  cases am <;> simp only [AMode.visit] <;> simp only [AMode.regs, List.mem_cons, List.mem_nil_iff,
    or_false, forall_eq_or_imp, forall_eq] at h <;>
    first
    | exact KInv.pure _
    | exact KInv.bind (KInv.collect _ _ (fun _ => h) (fun h' => by cases h')) fun _ => KInv.pure _
    | exact KInv.bind (KInv.collect _ _ (fun _ => h.1) (fun h' => by cases h')) fun _ =>
        KInv.bind (KInv.collect _ _ (fun _ => h.2) (fun h' => by cases h')) fun _ => KInv.pure _

theorem KInv.condBrKind (k : CondBrKind) (h : ∀ r ∈ k.regs, r ∈ U) :
    KInv U D (CondBrKind.visit collectOp k) := by
  cases k <;> simp only [CondBrKind.visit] <;> simp only [CondBrKind.regs, List.mem_cons,
    List.mem_nil_iff, or_false, forall_eq] at h <;>
    first
    | exact KInv.pure _
    | exact KInv.bind (KInv.collect _ _ (fun _ => h) (fun h' => by cases h')) fun _ => KInv.pure _

end

/-- Apply the visitor-invariant combinators. -/
macro "kinv_steps" : tactic => `(tactic| (
  repeat'
    first
    | exact KInv.pure _
    | refine KInv.bind (KInv.collect _ _ ?_ ?_) fun _ => ?_
    | refine KInv.bind (KInv.amode _ ?_) fun _ => ?_
    | refine KInv.bind (KInv.condBrKind _ ?_) fun _ => ?_
    | refine KInv.bind (KInv.mapM _ fun a ha => ?_) fun _ => ?_
    | refine KInv.mapM _ fun a ha => ?_
    | refine KInv.map _ (KInv.collect _ _ ?_ ?_)
    | refine KInv.bind (KInv.pure _) fun _ => ?_
    | refine KInv.map _ ?_))

/-- Close the side goals of `kinv_steps`. -/
macro "kinv_side" : tactic => `(tactic| (
  first
  | (intro hk; simp only [OpSpec.use, OpSpec.def_, OpSpec.earlyDef, OpSpec.fixedUse, OpSpec.fixedDef,
      OpSpec.reuseDef, reduceCtorEq] at hk; done)
  | (simp [useRegsK, defRegsK, pairUses, pairDefs, MInst.uses, MInst.defs, OpSpec.use, OpSpec.def_,
      OpSpec.earlyDef, OpSpec.fixedUse, OpSpec.fixedDef, OpSpec.reuseDef]; done)
  | (simp [useRegsK, defRegsK, pairUses, pairDefs, MInst.uses, MInst.defs, OpSpec.use, OpSpec.def_,
      OpSpec.earlyDef, OpSpec.fixedUse, OpSpec.fixedDef, OpSpec.reuseDef]
     first | exact ⟨_, ‹_›⟩ | exact .inr ⟨_, ‹_›⟩)
  | (intro r hr; simp [useRegsK, MInst.uses, hr])))

/-- **The operand visitor** collects the uses among `useRegsK`, the defs among `defRegsK`. -/
theorem kinv_visit (m : MInst) :
    KInv (useRegsK m) (defRegsK m) (MInst.visitOperands collectOp m) := by
  cases m
  case call info =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands] <;> kinv_steps
    all_goals kinv_side
  case tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands] <;> kinv_steps
    all_goals kinv_side
  all_goals simp only [MInst.visitOperands]
  all_goals kinv_steps
  all_goals kinv_side

/-- The operands of an instruction by kind. -/
theorem operands_kinds {m : MInst} {ops : Array Operand} (h : m.operands = .ok ops) :
    OpsIn (useRegsK m) (defRegsK m) ops := by
  rw [operands_eq] at h
  cases hr : (MInst.visitOperands collectOp m).run #[] with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨m', ops'⟩ := p
    rw [hr] at h
    cases h
    exact kinv_visit m #[] m' _ hr (fun o ho => by simp at ho)

/-! ## Killed defs -/

/-- The instruction is none of the variants with killed defs, nor a `tryCall`. -/
def NotK : MInst → Prop
  | .jtSequence .. | .atomicRmwLoop .. | .atomicCasLoop .. | .tryCall .. => False
  | _ => True

/-- **An instruction other than the LL/SC loops, `JTSequence` and `tryCall` kills nothing.** -/
theorem unstored_nil {m : MInst} (hk : NotK m) : unstored m = [] := by
  unfold unstored
  cases hops : m.operands with
  | error e => rfl
  | ok ops =>
    have hops' := operands_kinds hops
    simp only
    unfold storedDefs
    by_cases ht : m.isTerminator = true
    · have hnil : ops.toList.filter (·.kind == .def) = [] := by
        rw [List.filter_eq_nil_iff]
        intro o ho hd
        have := (hops' o ho).2 (by simpa using hd)
        cases m <;> simp_all [MInst.isTerminator, MInst.isBranch, MInst.isRet, NotK, defRegsK,
          MInst.defs, pairDefs]
      simp [hnil]
    · have hkd : m.keptDefs = none := by
        cases m <;> simp_all [MInst.keptDefs, NotK, MInst.isTerminator, MInst.isBranch]
      simp only [ht, Bool.false_eq_true, ↓reduceIte, hkd]
      rw [List.filter_eq_nil_iff]
      intro v hv
      simp [hv]

/-! ## The registers of an `MInst` value -/

@[simp] theorem regsKL_nil : regsKL [] = [] := rfl
@[simp] theorem regsKL_cons (v : V) (vs : List V) : regsKL (v :: vs) = v.regsK ++ regsKL vs := rfl
@[simp] theorem regsDL_nil : regsDL [] = [] := rfl
@[simp] theorem regsDL_cons (v : V) (vs : List V) : regsDL (v :: vs) = v.regsD ++ regsDL vs := rfl
@[simp] theorem kInL_nil : kInL [] = false := rfl
@[simp] theorem kInL_cons (v : V) (vs : List V) : kInL (v :: vs) = (v.kIn || kInL vs) := rfl

theorem reg?_eq {x : V} {r : Reg} (h : x.reg? = some r) : x = .reg r := by
  cases x <;> simp [V.reg?] at h
  rw [h]

theorem callInfo?_eq {x : V} {c : CallInfo} (h : x.callInfo? = some c) : x = .op (.callInfo c) := by
  cases x <;> simp [V.callInfo?] at h
  rename_i o
  cases o <;> simp at h
  rw [h]

theorem reg?_iff {x : V} {r : Reg} : x.reg? = some r ↔ x = .reg r :=
  ⟨reg?_eq, fun h => by subst h; rfl⟩

theorem callInfo?_iff {x : V} {c : CallInfo} : x.callInfo? = some c ↔ x = .op (.callInfo c) :=
  ⟨callInfo?_eq, fun h => by subst h; rfl⟩

theorem amode?_regs {x : V} {am : AMode} (h : x.amode? = some am) : ∀ r ∈ am.regs, r ∈ x.regsK := by
  unfold V.amode? at h
  obtain ⟨⟨k, fs⟩, he, h⟩ := bind_some_ex h
  rw [enumOf_eq he]
  intro r hr
  repeat' (first | (obtain ⟨_, _, h⟩ := bind_some_ex h) | split at h)
  all_goals first
    | (cases h; done)
    | (simp only [pure, Option.some.injEq] at h
       subst h
       simp only [reg?_iff, Prod.mk.injEq] at *
       obtain ⟨rfl, rfl⟩ := ‹_ = _ ∧ _ = _›
       subst_vars
       simp only [AMode.regs, List.mem_cons, List.mem_nil_iff, or_false] at hr
       all_goals first | (rcases hr with rfl | rfl <;> simp [V.regsK]) | (subst hr; simp [V.regsK]))

theorem condBrKind?_regs {x : V} {k : CondBrKind} (h : x.condBrKind? = some k) :
    ∀ r ∈ k.regs, r ∈ x.regsK := by
  unfold V.condBrKind? at h
  obtain ⟨⟨k, fs⟩, he, h⟩ := bind_some_ex h
  rw [enumOf_eq he]
  intro r hr
  repeat' (first | (obtain ⟨_, _, h⟩ := bind_some_ex h) | split at h)
  all_goals first
    | (cases h; done)
    | (simp only [pure, Option.some.injEq] at h
       subst h
       simp only [reg?_iff, Prod.mk.injEq] at *
       obtain ⟨rfl, rfl⟩ := ‹_ = _ ∧ _ = _›
       subst_vars
       simp only [CondBrKind.regs, List.mem_cons, List.mem_nil_iff, or_false] at hr
       all_goals (subst hr; simp [V.regsK]))

theorem mem_pairRegs_fst {a b : Reg} {l : List (Reg × Reg)} (h : (a, b) ∈ l) : a ∈ pairRegs l := by
  simp only [pairRegs, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false]
  exact ⟨(a, b), h, .inl rfl⟩

/-- What `ofV` builds from `v`, by register kind. -/
def OfVK (v : V) (m : MInst) : Prop :=
  (∀ r ∈ useRegsK m, r ∈ v.regsK) ∧ (∀ c, m = .call c → ∀ q ∈ c.defs, q.2 ∈ v.regsD) ∧
    (v.kIn = false → NotK m)

set_option maxHeartbeats 4000000 in
/-- **`ofV` by register kind**: the instruction's use registers are `v`'s registers outside call
defs, a call's defs are `v`'s call defs, and it has killed defs only if `v` holds such data. -/
theorem ofV_regs {v : V} {m : MInst} (h : MInst.ofV v = some m) : OfVK v m := by
  unfold MInst.ofV at h
  obtain ⟨⟨k, fs⟩, he, h2⟩ := bind_some_ex h
  clear h
  rw [enumOf_eq he]
  revert h2
  revert m
  apply ofV_split _ (fun k fs (r : Option MInst) => ∀ m, r = some m → OfVK (V.data tyMInst k fs) m)
  all_goals
    intros
    rename_i m hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := bind_some_ex hm) | split at hm)
    all_goals try (cases hm; done)
  all_goals
    simp only [pure, Option.some.injEq] at hm
    subst hm
  all_goals
    (try have hA := amode?_regs ‹V.amode? _ = some _›)
    (try have hC := condBrKind?_regs ‹V.condBrKind? _ = some _›)
    try simp only [reg?_iff, callInfo?_iff] at *
    subst_vars
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      simp only [useRegsK, pairUses, MInst.uses, V.regsK, regsKL_cons, regsKL_nil, opRegsK,
        List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.append_nil] at hr ⊢
      all_goals grind [mem_pairRegs_fst]
    · intro c hc
      first
      | (cases hc; done)
      | (cases hc
         intro q hq
         simp only [V.regsD, regsDL_cons, regsDL_nil, opRegsD, pairRegs, List.append_nil,
           List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false]
         exact ⟨q, hq, .inr rfl⟩)
    · first
      | exact fun _ => True.intro
      | (intro h; simp [V.kIn, isKVariant] at h)

/-- **An emitted instruction's uses, kills and call defs** (`MInst.ofV v = some m`): its use
operands are registers of `v` outside call defs, it kills nothing unless `v` holds
`AtomicRMWLoop`/`AtomicCASLoop`/`JTSequence` data, a call's defs are registers of `v`'s call defs,
and it is no `tryCall`. -/
theorem ofV_kill {v : V} {m : MInst} (h : MInst.ofV v = some m) :
    (∀ ops, m.operands = .ok ops → ∀ o ∈ ops.toList, o.kind = .use →
      Reg.vreg o.vreg o.cls ∈ v.regsK) ∧
    (v.kIn = false → Spill.unstored m = []) ∧
    (∀ c, m = .call c → ∀ q ∈ c.defs, q.2 ∈ v.regsD) ∧
    (∀ c ti, m ≠ .tryCall c ti) := by
  obtain ⟨h1, h2, h3⟩ := ofV_regs h
  exact ⟨fun ops hops o ho hk => h1 _ ((operands_kinds hops o ho).1 hk),
    fun hk => unstored_nil (h3 hk), h2, (ofV_ok h).1⟩

end Backend.Proof.Kill
