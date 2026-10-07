import FV.Backend.Proof.KillOfV
import FV.Backend.Proof.KillCtor
import FV.Backend.Proof.DefRuns
import FV.Backend.Proof.DefGenDom

/-!
# Definedness of the ISLE runs: the operands of an emitted instruction (`MInst.ofV`)

* `regsU`: the registers of a value in operand positions (a call's argument and return pairs
  contribute their vreg sides only);
* `kg_visit`: the operand visitor succeeds when every visited register is a vreg or not
  allocatable, and collects every def register that is a vreg as a def operand;
* `ofV_fields`: an instruction built from an `MInst` variant reads registers of its use and
  call-info fields (`miKinds`), and defines the register of each def field and the return vregs
  of its call info.
-/

namespace Backend.Proof.DefGen

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Driver
  Backend.Proof.Kill Backend.Proof.DefRun Isle Isle.Aarch64

/-! ## Registers in operand positions -/

/-- The uses of a call info: its destination register and the vreg sides of its arguments. -/
def callUses (c : CallInfo) : List Reg :=
  (match c.dest with
   | .reg r => [r]
   | .sym _ => []) ++ c.uses.map (·.1)

/-- The registers of an operand in operand positions. -/
def opRegsU : Opnd → List Reg
  | .callArgs us => us.map (·.1)
  | .callRets ds => ds.map (·.2)
  | .callInfo c => callUses c ++ c.defs.map (·.2)
  | _ => []

mutual
/-- The registers of a value in operand positions. -/
def regsU : V → List Reg
  | .reg r => [r]
  | .regs rs => rs
  | .regsVec rss => rss.flatten
  | .op o => opRegsU o
  | .data _ _ fs => regsUL fs
  | _ => []
/-- `regsU` of a list. -/
def regsUL : List V → List Reg
  | [] => []
  | v :: vs => regsU v ++ regsUL vs
end

@[simp] theorem regsUL_nil : regsUL [] = [] := rfl
@[simp] theorem regsUL_cons (v : V) (vs : List V) : regsUL (v :: vs) = regsU v ++ regsUL vs := rfl

theorem mem_regsUL {r : Reg} : ∀ {vs : List V}, r ∈ regsUL vs ↔ ∃ w ∈ vs, r ∈ regsU w
  | [] => by simp
  | v :: vs => by simp [mem_regsUL]

theorem regsU_sub_mem {v : V} {vs : List V} (h : v ∈ vs) {r : Reg} (hr : r ∈ regsU v) :
    r ∈ regsUL vs := mem_regsUL.mpr ⟨v, h, hr⟩

theorem opRegsU_sub (o : Opnd) : ∀ r ∈ opRegsU o, r ∈ opRegs o := by
  intro r hr
  cases o with
  | callArgs us =>
    simp only [opRegsU, List.mem_map] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact List.mem_flatMap.mpr ⟨p, hp, by simp⟩
  | callRets ds =>
    simp only [opRegsU, List.mem_map] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact List.mem_flatMap.mpr ⟨p, hp, by simp⟩
  | callInfo c =>
    simp only [opRegsU, callUses, opRegs, List.mem_append, List.mem_map] at hr ⊢
    rcases hr with (h | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact .inl (.inl h)
    · exact .inl (.inr (List.mem_flatMap.mpr ⟨p, hp, by simp⟩))
    · exact .inr (List.mem_flatMap.mpr ⟨p, hp, by simp⟩)
  | _ => simp [opRegsU] at hr

/-- Operand registers are registers. -/
theorem regsU_sub : ∀ (v : V), ∀ r ∈ regsU v, r ∈ v.regsIn
  | .reg _, _, h => h
  | .regs _, _, h => h
  | .regsVec _, _, h => h
  | .op o, r, h => opRegsU_sub o r h
  | .data _ _ fs, r, h => by
    simp only [regsU, V.regsIn] at h ⊢
    obtain ⟨w, hw, hr⟩ := mem_regsUL.mp h
    exact regsIn_sub_of_mem hw r (regsU_sub w r hr)
  | .int _, _, h | .bool _, _, h | .ty _, _, h | .inst _, _, h | .value _, _, h | .label _, _, h
  | .labels _, _, h | .values _, _, h | .blockCalls _, _, h => by simp [regsU] at h

/-! ## The operand visitor succeeds and collects the defs -/

/-- A register that may occupy an operand position: a vreg, or a real register the allocator
does not use. -/
def OkReg (r : Reg) : Prop := (∃ n c, r = .vreg n c) ∨ r.allocatable = false

/-- A step of the operand visitor whose registers are in `Vs`: if they are `OkReg`, it succeeds
from every state, keeps the collected operands, and collects every vreg of `Dd` as a def. -/
def KG (Vs Dd : List Reg) {α : Type} (x : OpM α) : Prop :=
  (∀ r ∈ Vs, OkReg r) → ∀ s, ∃ a s', x.run s = .ok (a, s') ∧ (∀ o ∈ s.toList, o ∈ s'.toList) ∧
    ∀ n c, Reg.vreg n c ∈ Dd → ∃ o ∈ s'.toList, o.vreg = n ∧ o.kind = .def

section
variable {Vs : List Reg}

theorem KG.pure {α : Type} (a : α) : KG Vs [] (Pure.pure a : OpM α) := by
  intro _ s
  exact ⟨a, s, rfl, fun _ h => h, fun _ _ h => by cases h⟩

theorem KG.bind {α β : Type} {D1 D2 : List Reg} {x : OpM α} {k : α → OpM β} (hx : KG Vs D1 x)
    (hk : ∀ a, KG Vs D2 (k a)) : KG Vs (D1 ++ D2) (x >>= k) := by
  intro hv s
  obtain ⟨a, s1, h1, hs1, hd1⟩ := hx hv s
  obtain ⟨b, s2, h2, hs2, hd2⟩ := hk a hv s1
  refine ⟨b, s2, ?_, fun o ho => hs2 o (hs1 o ho), ?_⟩
  · rw [StateT.run_bind, h1]; exact h2
  · intro n c hn
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨o, ho, h⟩ := hd1 n c hn
      exact ⟨o, hs2 o ho, h⟩
    · exact hd2 n c hn

theorem KG.mono {α : Type} {D1 D2 : List Reg} {x : OpM α} (hx : KG Vs D1 x)
    (h : ∀ r ∈ D2, r ∈ D1) : KG Vs D2 x := by
  intro hv s
  obtain ⟨a, s1, h1, hs1, hd1⟩ := hx hv s
  exact ⟨a, s1, h1, hs1, fun n c hn => hd1 n c (h _ hn)⟩

theorem KG.collect (sp : OpSpec) (r : Reg) (hr : r ∈ Vs) :
    KG Vs (if sp.kind = .def then [r] else []) (collectOp sp r) := by
  intro hv s
  by_cases hvr : ∃ n c, r = .vreg n c
  · obtain ⟨n, c, rfl⟩ := hvr
    refine ⟨.vreg n c, s.push ⟨n, c, sp.kind, sp.pos, sp.con⟩, rfl, fun o ho => by simp [ho], ?_⟩
    intro n' c' hn
    split at hn
    · rename_i hk
      simp only [List.mem_singleton, Reg.vreg.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      refine ⟨⟨n', c', sp.kind, sp.pos, sp.con⟩, ?_, rfl, hk⟩
      simp
    · cases hn
  · have hok : r.allocatable = false := (hv r hr).resolve_left hvr
    have e : (collectOp sp r).run s = .ok (r, s) := by
      cases r with
      | vreg n c => exact absurd ⟨n, c, rfl⟩ hvr
      | _ => simp [collectOp, hok, StateT.run]; rfl
    refine ⟨r, s, e, fun o ho => ho, fun n c hn => ?_⟩
    split at hn
    · simp only [List.mem_singleton] at hn
      exact absurd ⟨n, c, hn.symm⟩ hvr
    · cases hn

theorem KG.map {α β : Type} {D : List Reg} (f : α → β) {x : OpM α} (hx : KG Vs D x) :
    KG Vs D (f <$> x) := by
  rw [map_eq_pure_bind]
  exact (KG.bind hx fun a => KG.pure _).mono (by simp)

theorem KG.mapM {α β : Type} {F : α → OpM β} {G : α → List Reg} :
    ∀ (l : List α), (∀ a ∈ l, KG Vs (G a) (F a)) → KG Vs (l.flatMap G) (l.mapM F)
  | [], _ => KG.pure _
  | a :: l, h => by
    rw [List.mapM_cons, List.flatMap_cons]
    exact (KG.bind (h a List.mem_cons_self) fun b =>
      KG.bind (KG.mapM l fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) fun bs =>
        KG.pure _).mono (by simp)

theorem KG.amode (am : AMode) (h : ∀ r ∈ am.regs, r ∈ Vs) :
    KG Vs [] (AMode.visit collectOp am) := by
  cases am <;> simp only [AMode.visit] <;> simp only [AMode.regs, List.mem_cons, List.mem_nil_iff,
    or_false, forall_eq_or_imp, forall_eq] at h
  all_goals first
    | exact KG.pure _
    | exact (KG.bind (KG.collect _ _ h) fun _ => KG.pure _).mono (by simp)
    | exact (KG.bind (KG.collect _ _ h.1) fun _ =>
        KG.bind (KG.collect _ _ h.2) fun _ => KG.pure _).mono (by simp)

theorem KG.condBrKind (k : CondBrKind) (h : ∀ r ∈ k.regs, r ∈ Vs) :
    KG Vs [] (CondBrKind.visit collectOp k) := by
  cases k <;> simp only [CondBrKind.visit] <;> simp only [CondBrKind.regs, List.mem_cons,
    List.mem_nil_iff, or_false, forall_eq] at h
  all_goals first
    | exact KG.pure _
    | exact (KG.bind (KG.collect _ _ h) fun _ => KG.pure _).mono (by simp)

end

/-- Apply the visitor combinators. -/
macro "kg_steps" : tactic => `(tactic| (
  repeat'
    first
    | apply KG.pure
    | apply KG.collect
    | apply KG.amode
    | apply KG.condBrKind
    | apply KG.mapM
    | apply KG.map
    | apply KG.bind
    | (intro _)))

/-- Close the side goals of `kg_steps`. -/
macro "kg_close" : tactic => `(tactic| (
  first
  | (simp [useRegsK, defRegsK, pairUses, pairDefs, MInst.uses, MInst.defs, OpSpec.use, OpSpec.def_,
      OpSpec.earlyDef, OpSpec.fixedUse, OpSpec.fixedDef, OpSpec.reuseDef]; done)
  | (simp_all [useRegsK, defRegsK, pairUses, pairDefs, MInst.uses, MInst.defs, OpSpec.use,
      OpSpec.def_, OpSpec.earlyDef, OpSpec.fixedUse, OpSpec.fixedDef, OpSpec.reuseDef]; done)
  | (simp only [useRegsK, defRegsK, pairUses, pairDefs, MInst.uses, MInst.defs, List.mem_append,
      List.mem_map, List.mem_cons, List.mem_nil_iff, or_false]
     first
     | exact .inl (.inr ⟨_, ‹_›, rfl⟩)
     | exact .inr (.inr ⟨_, ‹_›, rfl⟩)
     | exact .inr ⟨_, ‹_›, rfl⟩
     | exact .inl ⟨_, ‹_›, rfl⟩)
  | grind [useRegsK, defRegsK, pairUses, pairDefs, MInst.uses, MInst.defs, OpSpec.use, OpSpec.def_,
      OpSpec.earlyDef, OpSpec.fixedUse, OpSpec.fixedDef, OpSpec.reuseDef]))

set_option maxHeartbeats 4000000 in
/-- **The operand visitor** succeeds when the instruction's registers are `OkReg`, and collects
every vreg of `defRegsK` as a def. -/
theorem kg_visit (m : MInst) :
    KG (useRegsK m ++ defRegsK m) (defRegsK m) (MInst.visitOperands collectOp m) := by
  cases m
  case call info =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands, pure_bind] <;> apply KG.mono <;> kg_steps
    all_goals kg_close
  case tryCall info ti =>
    obtain ⟨dest, uses, defs⟩ := info
    cases dest <;> simp only [MInst.visitOperands, pure_bind] <;> apply KG.mono <;> kg_steps
    all_goals kg_close
  all_goals simp only [MInst.visitOperands]
  all_goals apply KG.mono
  all_goals kg_steps
  all_goals kg_close



/-- **The operands of an instruction whose registers may occupy operand positions**: they
exist, and every def vreg is a def operand. -/
theorem operands_okRegs {m : MInst} (h : ∀ r ∈ useRegsK m ++ defRegsK m, OkReg r) :
    (∃ ops, m.operands = .ok ops) ∧ ∀ n c, Reg.vreg n c ∈ defRegsK m → n ∈ defVregs m := by
  obtain ⟨a, ops, hr, -, hd⟩ := kg_visit m h #[]
  have hops : m.operands = .ok ops := by rw [operands_eq, hr]; rfl
  refine ⟨⟨ops, hops⟩, fun n c hn => ?_⟩
  obtain ⟨o, ho, rfl, hk⟩ := hd n c hn
  unfold defVregs
  rw [hops]
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨ho, by simp [hk]⟩)

/-! ## The fields of an `MInst` value -/

/-- The registers a field of kind `k` contributes as uses. -/
def useOf : FK → V → List Reg
  | .u, f => regsU f
  | .c, .op (.callInfo c) => callUses c
  | _, _ => []

theorem useOf_sub (k : FK) (f : V) : ∀ r ∈ useOf k f, r ∈ regsU f := by
  intro r hr
  cases k
  · cases hr
  · exact hr
  · cases f <;> simp only [useOf, List.not_mem_nil] at hr
    rename_i o
    cases o <;> simp at hr
    simp only [regsU, opRegsU, List.mem_append]
    exact .inl hr

theorem amode?_regsU {x : V} {am : AMode} (h : x.amode? = some am) : ∀ r ∈ am.regs, r ∈ regsU x := by
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
       all_goals first | (rcases hr with rfl | rfl <;> simp [regsU]) | (subst hr; simp [regsU]))

theorem condBrKind?_regsU {x : V} {k : CondBrKind} (h : x.condBrKind? = some k) :
    ∀ r ∈ k.regs, r ∈ regsU x := by
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
       all_goals (subst hr; simp [regsU]))

/-- The registers a field of kind `k` contributes as defs. -/
def defOf : FK → V → List Reg
  | .d, f => regsU f
  | .c, .op (.callInfo c) => c.defs.map (·.2)
  | _, _ => []

/-- `useOf` of the fields. -/
def useAll : List FK → List V → List Reg
  | k :: ks, f :: fs => useOf k f ++ useAll ks fs
  | _, _ => []

/-- `defOf` of the fields. -/
def defAll : List FK → List V → List Reg
  | k :: ks, f :: fs => defOf k f ++ defAll ks fs
  | _, _ => []

/-- The fields of kind `k`. -/
def fieldsOf (k : FK) : List FK → List V → List V
  | k' :: ks, f :: fs => (if k' = k then [f] else []) ++ fieldsOf k ks fs
  | _, _ => []

/-- What `ofV` builds from the fields of an `MInst` variant, by field kind (`miKinds`). -/
def OfVF (k : Nat) (vs : List V) (m : MInst) : Prop :=
  ∃ ks, miKinds k = some ks ∧ vs.length = ks.length ∧
    (∀ r ∈ useRegsK m, r ∈ useAll ks vs) ∧ (∀ r ∈ defRegsK m, r ∈ defAll ks vs) ∧
    (∀ f ∈ fieldsOf .d ks vs, ∃ r, f = V.reg r ∧ r ∈ defRegsK m) ∧
    (∀ f ∈ fieldsOf .c ks vs, ∃ c, f = V.op (.callInfo c) ∧ ∀ q ∈ c.defs, q.2 ∈ defRegsK m)

theorem miKinds_load {k : Nat} {op : LoadOp} (h : loadOpOfIdx? k = some op) :
    miKinds k = some [.d, .u, .u] := by
  unfold loadOpOfIdx? at h
  split at h <;> first | rfl | cases h

theorem miKinds_store {k : Nat} {op : StoreOp} (h0 : loadOpOfIdx? k = none)
    (h : storeOpOfIdx? k = some op) : miKinds k = some [.u, .u, .u] := by
  unfold storeOpOfIdx? at h
  split at h <;> first | rfl | cases h

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
/-- **`ofV` by field kind.** -/
theorem ofV_fields {k : Nat} {vs : List V} {m : MInst}
    (h : MInst.ofV (.data tyMInst k vs) = some m) : OfVF k vs m := by
  unfold MInst.ofV at h
  obtain ⟨⟨k', fs⟩, he, h2⟩ := bind_some_ex h
  clear h
  have e := enumOf_eq he
  simp only [V.data.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  revert h2
  revert m
  apply ofV_split _ (fun k fs (r : Option MInst) => ∀ m, r = some m → OfVF k fs m)
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
    (try have hA := amode?_regsU ‹V.amode? _ = some _›)
    (try have hC := condBrKind?_regsU ‹V.condBrKind? _ = some _›)
    try simp only [reg?_iff, callInfo?_iff] at *
    subst_vars
  all_goals
    first
    | refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    | refine ⟨_, miKinds_load ‹_›, rfl, ?_, ?_, ?_, ?_⟩
    | refine ⟨_, miKinds_store ‹_› ‹_›, rfl, ?_, ?_, ?_, ?_⟩
    all_goals
      first
      | (intro r hr
         (try simp only [useRegsK, defRegsK, MInst.uses, MInst.defs, pairUses, pairDefs,
           List.append_nil, List.nil_append, List.mem_append, List.mem_cons, List.mem_nil_iff,
           or_false] at hr)
         all_goals (try simp only [useAll, defAll, useOf, defOf, regsU, callUses,
           List.append_nil, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false])
         all_goals first
           | (simp_all; done)
           | grind)
      | (intro f hf
         (try simp only [fieldsOf, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
           List.append_nil, List.nil_append, reduceIte, reduceCtorEq] at hf)
         all_goals first
           | (simp_all [defRegsK, MInst.defs, pairDefs]; done)
           | grind [defRegsK, MInst.defs, pairDefs])

end Backend.Proof.DefGen
