import FV.Backend.Proof.IselFlowSplit
import FV.Backend.Proof.IselFlowCheck
import FV.Backend.Proof.DriverCheck

/-!
# What the extern helpers do to registers, values, instructions and the lowering state

The flow facts about ISLE runs (`IselFlow`) only need to know, of every extern constructor and
extractor, where the registers, CLIF values, instruction indices and `ElfTlsGetAddr` data of its
result come from, and how it changes the lowering state. `V.regsIn`, `V.valsIn`, `V.instsIn`,
`V.tlsIn` collect these atoms of a value (inside `data` fields and operands too).

* `externCtor_ok`: every successful extern constructor call (`CtorOk`) only grows the vreg
  counter and the outgoing area, appends instructions that are no `tryCall`, and an
  `ElfTlsGetAddr` only when its argument holds that data (`emit`); the registers of its result
  come from its arguments, from fresh vregs, from the registers of its argument values, are
  physical, are the context's `try_call` registers, or it is `invalid_reg`; its values,
  instructions and `ElfTlsGetAddr` data come from its arguments.
* `externExtract_ok`: an extern extractor's outputs (`ExtOk`) have the registers of its input,
  values of its input, operands of the definition of an input value (`maybe_uextend`, …),
  results of an input instruction (`first_result` only), the data of an input instruction
  (`inst_data_value` only), and the definitions of input values (`def_inst`).

Both are proven with the splitters of `IselFlowSplit` (one goal per alternative).
-/

namespace Backend.Proof.Flow

open Backend Isle Isle.Aarch64

/-! ## Atoms of a value -/

/-- The registers of a list of register pairs. -/
def pairRegs (ps : List (Reg × Reg)) : List Reg := ps.flatMap fun p => [p.1, p.2]

/-- The registers inside an operand. -/
def opRegs : Opnd → List Reg
  | .callArgs us => pairRegs us
  | .callRets ds => pairRegs ds
  | .callInfo c => (match c.dest with
      | .reg r => [r]
      | .sym _ => []) ++ pairRegs c.uses ++ pairRegs c.defs
  | _ => []

/-- The CLIF values inside an operand. -/
def opVals : Opnd → List Nat
  | .extended x _ => [x]
  | _ => []

mutual
/-- The registers inside a value. -/
def _root_.Backend.V.regsIn : V → List Reg
  | .reg r => [r]
  | .regs rs => rs
  | .regsVec rss => rss.flatten
  | .op o => opRegs o
  | .data _ _ fs => regsInL fs
  | _ => []
/-- The registers inside a list of values. -/
def regsInL : List V → List Reg
  | [] => []
  | v :: vs => v.regsIn ++ regsInL vs
end

mutual
/-- The CLIF values inside a value. -/
def _root_.Backend.V.valsIn : V → List Nat
  | .value n => [n]
  | .values ns => ns
  | .op o => opVals o
  | .data _ _ fs => valsInL fs
  | _ => []
/-- The CLIF values inside a list of values. -/
def valsInL : List V → List Nat
  | [] => []
  | v :: vs => v.valsIn ++ valsInL vs
end

mutual
/-- The instruction indices inside a value. -/
def _root_.Backend.V.instsIn : V → List Nat
  | .inst j => [j]
  | .data _ _ fs => instsInL fs
  | _ => []
/-- The instruction indices inside a list of values. -/
def instsInL : List V → List Nat
  | [] => []
  | v :: vs => v.instsIn ++ instsInL vs
end

mutual
/-- Does the value hold `MInst.ElfTlsGetAddr` data? -/
def _root_.Backend.V.tlsIn : V → Bool
  | .data ty k fs => (ty == tyMInst && k == VIdx.MInst.ElfTlsGetAddr) || tlsInL fs
  | _ => false
/-- Does a value of the list hold `MInst.ElfTlsGetAddr` data? -/
def tlsInL : List V → Bool
  | [] => false
  | v :: vs => v.tlsIn || tlsInL vs
end

@[simp] theorem regsInL_nil : regsInL [] = [] := rfl
@[simp] theorem regsInL_cons (v : V) (vs : List V) : regsInL (v :: vs) = v.regsIn ++ regsInL vs := rfl
@[simp] theorem valsInL_nil : valsInL [] = [] := rfl
@[simp] theorem valsInL_cons (v : V) (vs : List V) : valsInL (v :: vs) = v.valsIn ++ valsInL vs := rfl
@[simp] theorem instsInL_nil : instsInL [] = [] := rfl
@[simp] theorem instsInL_cons (v : V) (vs : List V) :
    instsInL (v :: vs) = v.instsIn ++ instsInL vs := rfl
@[simp] theorem tlsInL_nil : tlsInL [] = false := rfl
@[simp] theorem tlsInL_cons (v : V) (vs : List V) : tlsInL (v :: vs) = (v.tlsIn || tlsInL vs) := rfl

/-- A member's atoms are atoms of the list. -/
theorem regsIn_sub_of_mem {v : V} {vs : List V} (h : v ∈ vs) : ∀ r ∈ v.regsIn, r ∈ regsInL vs := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    intro r hr
    rcases List.mem_cons.mp h with rfl | h
    · simp [hr]
    · simp [ih h r hr]

theorem valsIn_sub_of_mem {v : V} {vs : List V} (h : v ∈ vs) : ∀ n ∈ v.valsIn, n ∈ valsInL vs := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    intro n hn
    rcases List.mem_cons.mp h with rfl | h
    · simp [hn]
    · simp [ih h n hn]

theorem instsIn_sub_of_mem {v : V} {vs : List V} (h : v ∈ vs) :
    ∀ n ∈ v.instsIn, n ∈ instsInL vs := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    intro n hn
    rcases List.mem_cons.mp h with rfl | h
    · simp [hn]
    · simp [ih h n hn]

theorem tlsIn_of_mem {v : V} {vs : List V} (h : v ∈ vs) (ht : v.tlsIn = true) : tlsInL vs = true := by
  induction vs with
  | nil => cases h
  | cons w ws ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [ht]
    · simp [ih h]

/-! ## The state change of an extern constructor -/

/-- An instruction the extern helpers may emit: no `tryCall` (only `lowerFunction` makes one). -/
def NoTry (m : MInst) : Prop := ∀ c ti, m ≠ .tryCall c ti

/-- An `ElfTlsGetAddr`. -/
def IsTls (m : MInst) : Prop := ∃ sym rd tmp, m = .elfTlsGetAddr sym rd tmp

/-- The atoms-and-state contract of one extern constructor call `id args` from `st` returning
`v` in `st'`. -/
structure CtorOk (ctx : Ctx) (id : TermId) (args : List V) (st : LState) (v : V) (st' : LState) :
    Prop where
  vreg : st.nextVreg ≤ st'.nextVreg
  out : st.outgoing ≤ st'.outgoing
  emit : ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧
    ∀ m ∈ ms, NoTry m ∧ (IsTls m → id = TId.emit ∧ tlsInL args = true)
  regs : ∀ r ∈ v.regsIn, r ∈ regsInL args ∨
    (∃ n c, r = .vreg n c ∧ st.nextVreg ≤ n ∧ n < st'.nextVreg) ∨
    (∃ x ∈ valsInL args, ctx.valueReg? x = some r) ∨ (∀ n c, r ≠ .vreg n c) ∨
    id = TId.invalid_reg ∨ r ∈ ctx.tryRegs.1 ∨ r ∈ ctx.tryRegs.2
  vals : ∀ n ∈ v.valsIn, n ∈ valsInL args
  insts : ∀ j ∈ v.instsIn, j ∈ instsInL args
  tls : v.tlsIn = true → tlsInL args = true

/-- `CtorOk` of every successful result of a constructor call. -/
def CtorP (ctx : Ctx) (st : LState) (id : TermId) (args : List V) (r : ExtResult (V × LState)) :
    Prop :=
  ∀ v st', r = .ok (v, st') → CtorOk ctx id args st v st'

end Backend.Proof.Flow

namespace Backend.Proof.Flow

open Backend Isle Isle.Aarch64

gen_match_split ofV_split Backend.MInst.ofV.match_3

theorem enumOf_eq {ty : TypeId} {v : V} {k : Nat} {fs : List V} (h : v.enumOf? ty = some (k, fs)) :
    v = .data ty k fs := by
  cases v <;> simp [V.enumOf?] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem bind_some_ex {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- **`MInst.ofV`** never builds a `tryCall`, and an `ElfTlsGetAddr` only from that variant. -/
theorem ofV_ok {v : V} {m : MInst} (h : MInst.ofV v = some m) :
    NoTry m ∧ (IsTls m → v.tlsIn = true) := by
  unfold MInst.ofV at h
  obtain ⟨⟨k, fs⟩, he, h2⟩ := bind_some_ex h
  clear h
  rw [enumOf_eq he]
  revert h2
  revert m
  apply ofV_split _ (fun k fs (r : Option MInst) => ∀ m, r = some m → NoTry m ∧
    (IsTls m → (V.data tyMInst k fs).tlsIn = true))
  all_goals
    intros
    rename_i m hm
    try simp only at hm
    repeat' (first | (obtain ⟨_, _, hm⟩ := bind_some_ex hm) | split at hm)
    all_goals first
      | (cases hm; done)
      | (simp only [pure, Option.some.injEq] at hm
         subst hm
         exact ⟨fun c ti h => (by cases h), fun ⟨_, _, _, h⟩ => (by first | (cases h; done) | simp [V.tlsIn])⟩)

/-! ## Helpers of the constructors -/

/-- An instruction that is neither a `tryCall` nor an `ElfTlsGetAddr`. -/
def Benign (m : MInst) : Prop := NoTry m ∧ ¬ IsTls m

theorem foldl_inv {α β : Type} (I : α → Prop) (f : α → β → α) :
    ∀ (l : List β) (a : α), I a → (∀ b ∈ l, ∀ a, I a → I (f a b)) → I (l.foldl f a)
  | [], _, ha, _ => ha
  | b :: l, a, ha, hf => by
    rw [List.foldl_cons]
    exact foldl_inv I f l (f a b) (hf b List.mem_cons_self a ha)
      (fun b' hb' => hf b' (List.mem_cons_of_mem _ hb'))

/-- The state of `loadConstantFull` (register `rd` and state `s` reached from `st0`). -/
def LCInv (st0 : LState) (rd : Reg) (s : LState) : Prop :=
  (∃ n c, rd = .vreg n c ∧ st0.nextVreg ≤ n ∧ n < s.nextVreg) ∧ st0.nextVreg ≤ s.nextVreg ∧
    s.outgoing = st0.outgoing ∧
    ∃ ms : List MInst, s.emitted = st0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, Benign m

theorem push_toArray (a : Array MInst) (ms : List MInst) (m : MInst) :
    (a ++ ms.toArray).push m = a ++ (ms ++ [m]).toArray := by
  simp

theorem lcInv_step {st0 s : LState} {m : MInst}
    (hm : Benign m) (hle : st0.nextVreg ≤ s.nextVreg) (hout : s.outgoing = st0.outgoing)
    (hem : ∃ ms : List MInst, s.emitted = st0.emitted ++ ms.toArray ∧ ∀ m ∈ ms, Benign m) :
    LCInv st0 (s.fresh .int).1 ((s.fresh .int).2.emit m) := by
  obtain ⟨ms, h5, h6⟩ := hem
  refine ⟨⟨s.nextVreg, .int, rfl, hle, by simp [LState.fresh, LState.emit]⟩,
    by simp [LState.fresh, LState.emit]; omega, by simp [LState.fresh, LState.emit, hout],
    ⟨ms ++ [m], by simp [LState.fresh, LState.emit, h5], ?_⟩⟩
  intro m' hm'
  rcases List.mem_append.mp hm' with hm' | hm'
  · exact h6 m' hm'
  · simp only [List.mem_singleton] at hm'
    subst hm'
    exact hm

theorem ite_inv {α : Type} {I : α → Prop} {c : Prop} [Decidable c] {a b : α} (ha : c → I a)
    (hb : ¬c → I b) : I (if c then a else b) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

/-- **`loadConstantFull`**: a fresh register, `movz`/`movn` and `movk`s. -/
theorem loadConstantFull_ok (bits : Nat) (se : Bool) (sz : OperandSize) (value : Nat)
    (st : LState) :
    LCInv st (loadConstantFull bits se sz value st).1 (loadConstantFull bits se sz value st).2 := by
  unfold loadConstantFull
  dsimp only
  refine foldl_inv (fun x : Reg × LState × Nat => LCInv st x.1 x.2.1) _ _ _ ?_ ?_
  · exact lcInv_step ⟨fun c ti h => (by cases h), fun ⟨_, _, _, h⟩ => (by cases h)⟩
      (Nat.le_refl _) rfl ⟨[], by simp, by simp⟩
  · intro sh _ x hx
    refine ite_inv (I := fun x : Reg × LState × Nat => LCInv st x.1 x.2.1) (fun _ => hx) fun _ => ?_
    refine ite_inv (I := fun x : Reg × LState × Nat => LCInv st x.1 x.2.1) (fun _ => ?_) fun _ => hx
    obtain ⟨⟨n, c, hrd, h1, h2⟩, h3, h4, ms, h5, h6⟩ := hx
    exact lcInv_step (s := x.2.1) ⟨fun c ti h => (by cases h), fun ⟨_, _, _, h⟩ => (by cases h)⟩
      h3 h4 ⟨ms, h5, h6⟩

/-- The return registers are physical. -/
theorem retRegs_phys {k : Nat} {ps : List Reg} (h : retRegs k = some ps) :
    ∀ p ∈ ps, ∀ n c, p ≠ .vreg n c := by
  unfold retRegs at h
  split at h
  · cases h
    intro p hp n c he
    simp only [List.mem_map] at hp
    obtain ⟨i, -, rfl⟩ := hp
    cases he
  · cases h

theorem payloadRegs_phys (cc : Option Clif.CallConv) : ∀ p ∈ payloadRegs cc, ∀ n c, p ≠ .vreg n c := by
  intro p hp n c he
  unfold payloadRegs at hp
  split at hp <;> simp at hp <;> (try rcases hp with rfl | rfl) <;> cases he

/-- The register locations of `argLocs` are physical. -/
theorem argLocs_phys (bytes : List Nat) :
    ∀ l ∈ (argLocs bytes).1, ∀ p, l = .reg p → ∀ n c, p ≠ .vreg n c := by
  unfold argLocs
  dsimp only
  have := foldl_inv (fun x : Array ArgLoc × Nat × Nat =>
      ∀ l ∈ x.1.toList, ∀ p, l = .reg p → ∀ n c, p ≠ .vreg n c)
    (fun (x : Array ArgLoc × Nat × Nat) (b : Nat) =>
      if x.2.1 < 8 then (x.1.push (.reg (.x x.2.1)), x.2.1 + 1, x.2.2)
      else (x.1.push (.stack (alignTo x.2.2 (max b 8))), x.2.1, alignTo x.2.2 (max b 8) + max b 8))
    bytes (#[], 0, 0) (by simp) (by
      intro b _ x hx
      try dsimp only
      split
      · intro l hl p hp n c he
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact hx l hl p hp n c he
        · cases hp; cases he
      · intro l hl p hp n c he
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact hx l hl p hp n c he
        · cases hp)
  exact this

theorem sretLocStep_phys :
    ∀ (ps : List Clif.AbiParam) (q : Array ArgLoc × List ArgLoc),
      (∀ l ∈ q.1.toList ++ q.2, ∀ p, l = .reg p → ∀ n c, p ≠ .vreg n c) →
      ∀ l ∈ (ps.foldl sretLocStep q).1.toList, ∀ p, l = .reg p → ∀ n c, p ≠ .vreg n c
  | [], q, hq => fun l hl => hq l (List.mem_append_left _ hl)
  | a :: ps, q, hq => by
    rw [List.foldl_cons]
    refine sretLocStep_phys ps _ ?_
    intro l hl p hp n c he
    unfold sretLocStep at hl
    split at hl
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
      rcases hl with (hl | rfl) | hl
      · exact hq l (List.mem_append_left _ hl) p hp n c he
      · cases hp; cases he
      · exact hq l (List.mem_append_right _ hl) p hp n c he
    · split at hl
      · rename_i l0 r heq
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
        rcases hl with (hl | rfl) | hl
        · exact hq l (List.mem_append_left _ hl) p hp n c he
        · exact hq l (List.mem_append_right _ (by rw [heq]; exact List.mem_cons_self)) p hp n c he
        · exact hq l (List.mem_append_right _ (by rw [heq]; exact List.mem_cons_of_mem _ hl)) p hp n c he
      · rename_i heq
        simp only [List.append_nil] at hl
        exact hq l (List.mem_append_left _ hl) p hp n c he

/-- The register locations of `sigArgLocs` are physical. -/
theorem sigArgLocs_phys {s : Clif.Signature} {locs : List ArgLoc} {k : Nat}
    (h : sigArgLocs s = .ok (locs, k)) : ∀ l ∈ locs, ∀ p, l = .reg p → ∀ n c, p ≠ .vreg n c := by
  unfold sigArgLocs at h
  cases hb : sigArgs s with
  | error e => rw [hb] at h; cases h
  | ok bytes =>
    rw [hb] at h
    simp only [bind, Except.bind] at h
    split at h
    · split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact sretLocStep_phys _ _ (by
          intro l hl
          simpa using argLocs_phys _ l hl)
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      have := argLocs_phys bytes
      rw [h] at this
      exact this

/-! ## Extern constructors -/

gen_match_split externCtor_split Backend.externCtor.match_25

theorem ctorOk_same {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {v : V}
    (hr : ∀ r ∈ v.regsIn, r ∈ regsInL args ∨ (∃ x ∈ valsInL args, ctx.valueReg? x = some r) ∨
      (∀ n c, r ≠ .vreg n c))
    (hv : ∀ n ∈ v.valsIn, n ∈ valsInL args) (hi : ∀ j ∈ v.instsIn, j ∈ instsInL args)
    (ht : v.tlsIn = true → tlsInL args = true) : CtorOk ctx id args st v st := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, ⟨[], by simp, by simp⟩, fun r h => ?_, hv, hi, ht⟩
  rcases hr r h with h | h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))

theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; intro y hy; cases hy
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y0, h0, h⟩ := bind_some_ex h
    obtain ⟨ys', h1, h⟩ := bind_some_ex h
    simp only [pure, Option.some.injEq] at h
    subst h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, h0⟩
    · obtain ⟨x', hx', h'⟩ := mapM_mem h1 y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', h'⟩

theorem single_mem {rss : List (List Reg)} {rs : List Reg}
    (h : rss.mapM (fun | [r] => some r | _ => none) = some rs) : ∀ r ∈ rs, ∃ l ∈ rss, r ∈ l := by
  intro r hr
  obtain ⟨l, hl, he⟩ := mapM_mem h r hr
  refine ⟨l, hl, ?_⟩
  split at he
  · cases he; exact List.mem_singleton_self _
  · cases he

/-- `CtorOk` from its parts (no `invalid_reg`, no `try_call` registers). -/
theorem ctorOk_mk {ctx : Ctx} {id : TermId} {args : List V} {st st' : LState} {v : V}
    (h1 : st.nextVreg ≤ st'.nextVreg) (h2 : st.outgoing ≤ st'.outgoing)
    (h3 : ∃ ms : List MInst, st'.emitted = st.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, NoTry m ∧ (IsTls m → id = TId.emit ∧ tlsInL args = true))
    (hr : ∀ r ∈ v.regsIn, r ∈ regsInL args ∨
      (∃ n c, r = .vreg n c ∧ st.nextVreg ≤ n ∧ n < st'.nextVreg) ∨
      (∃ x ∈ valsInL args, ctx.valueReg? x = some r) ∨ (∀ n c, r ≠ .vreg n c))
    (hv : ∀ n ∈ v.valsIn, n ∈ valsInL args) (hi : ∀ j ∈ v.instsIn, j ∈ instsInL args)
    (ht : v.tlsIn = true → tlsInL args = true) : CtorOk ctx id args st v st' := by
  refine ⟨h1, h2, h3, fun r h => ?_, hv, hi, ht⟩
  rcases hr r h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))

theorem ctorOk_invalid {ctx : Ctx} {st : LState} :
    CtorOk ctx TId.invalid_reg [] st (.reg Reg.invalid) st :=
  ⟨Nat.le_refl _, Nat.le_refl _, ⟨[], by simp, by simp⟩,
    fun _ _ => .inr (.inr (.inr (.inr (.inl rfl)))), by simp [V.valsIn], by simp [V.instsIn],
    by simp [V.tlsIn]⟩

theorem ctorOk_fresh {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {c : RegClass} :
    CtorOk ctx id args st (.reg (st.fresh c).1) (st.fresh c).2 := by
  refine ctorOk_mk (by simp [LState.fresh]) (by simp [LState.fresh]) ⟨[], by simp [LState.fresh], by simp⟩
    ?_ (by simp [V.valsIn]) (by simp [V.instsIn]) (by simp [V.tlsIn])
  intro r hr
  simp only [V.regsIn, List.mem_singleton] at hr
  subst hr
  exact .inr (.inl ⟨st.nextVreg, c, rfl, Nat.le_refl _, by simp [LState.fresh]⟩)

theorem ctorOk_emit {ctx : Ctx} {id : TermId} {i : V} {st : LState} {m : MInst}
    (hid : id = TId.emit) (h : MInst.ofV i = some m) : CtorOk ctx id [i] st (.op .unit) (st.emit m) := by
  obtain ⟨h1, h2⟩ := ofV_ok h
  refine ctorOk_mk (by simp [LState.emit]) (by simp [LState.emit])
    ⟨[m], by simp [LState.emit], ?_⟩ (by simp [V.regsIn, opRegs]) (by simp [V.valsIn, opVals])
    (by simp [V.instsIn]) (by simp [V.tlsIn])
  intro m' hm
  simp only [List.mem_singleton] at hm
  subst hm
  exact ⟨h1, fun ht => ⟨hid, by simpa using h2 ht⟩⟩

theorem ctorOk_emitBenign {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {m : MInst}
    (h : Benign m) : CtorOk ctx id args st (.op .unit) (st.emit m) := by
  refine ctorOk_mk (by simp [LState.emit]) (by simp [LState.emit])
    ⟨[m], by simp [LState.emit], ?_⟩ (by simp [V.regsIn, opRegs]) (by simp [V.valsIn, opVals])
    (by simp [V.instsIn]) (by simp [V.tlsIn])
  intro m' hm
  simp only [List.mem_singleton] at hm
  subst hm
  exact ⟨h.1, fun ht => absurd ht h.2⟩

theorem ctorOk_lc {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {r : Reg} {st' : LState}
    (h : LCInv st r st') : CtorOk ctx id args st (.reg r) st' := by
  obtain ⟨⟨n, c, rfl, h1, h2⟩, h3, h4, ms, h5, h6⟩ := h
  refine ctorOk_mk h3 (by omega) ⟨ms, h5, fun m hm => ⟨(h6 m hm).1, fun ht => absurd ht (h6 m hm).2⟩⟩
    ?_ (by simp [V.valsIn]) (by simp [V.instsIn]) (by simp [V.tlsIn])
  intro r hr
  simp only [V.regsIn, List.mem_singleton] at hr
  subst hr
  exact .inr (.inl ⟨n, c, rfl, h1, h2⟩)

/-- `gen_call_output`: fresh registers. -/
theorem ctorOk_callOutput {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {β : Type}
    (F : Array (List Reg) × LState → β → Array (List Reg) × LState) (l : List β)
    (hF : ∀ a b, F a b = (a.1.push [(a.2.fresh .int).1], (a.2.fresh .int).2)) :
    CtorOk ctx id args st (.regsVec (l.foldl F (#[], st)).1.toList) (l.foldl F (#[], st)).2 := by
  have := foldl_inv (fun a : Array (List Reg) × LState =>
      (∀ rs ∈ a.1.toList, ∀ r ∈ rs, ∃ n c, r = .vreg n c ∧ st.nextVreg ≤ n ∧ n < a.2.nextVreg) ∧
      st.nextVreg ≤ a.2.nextVreg ∧ a.2.outgoing = st.outgoing ∧ a.2.emitted = st.emitted)
    F l (#[], st) (by simp) (by
      intro b _ a ⟨h1, h2, h3, h4⟩
      rw [hF]
      refine ⟨?_, by simp [LState.fresh]; omega, by simp [LState.fresh, h3],
        by simp [LState.fresh, h4]⟩
      intro rs hrs r hr
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hrs
      rcases hrs with hrs | rfl
      · obtain ⟨n, c, h, h5, h6⟩ := h1 rs hrs r hr
        exact ⟨n, c, h, h5, by simp [LState.fresh]; omega⟩
      · simp only [List.mem_singleton] at hr
        subst hr
        exact ⟨a.2.nextVreg, .int, rfl, h2, by simp [LState.fresh]⟩)
  obtain ⟨h1, h2, h3, h4⟩ := this
  refine ctorOk_mk h2 (by omega) ⟨[], by simp [h4], by simp⟩ ?_ (by simp [V.valsIn])
    (by simp [V.instsIn]) (by simp [V.tlsIn])
  intro r hr
  simp only [V.regsIn, List.mem_flatten] at hr
  obtain ⟨rs, hrs, hr⟩ := hr
  exact .inr (.inl (h1 rs hrs r hr))

/-- `gen_call_args`: register uses from the arguments, stores of the stack arguments. -/
theorem ctorOk_callArgs {ctx : Ctx} {id : TermId} {args : List V} {st : LState}
    (F : Array (Reg × Reg) × LState → (ArgLoc × Reg) × Nat → Array (Reg × Reg) × LState)
    (l : List ((ArgLoc × Reg) × Nat))
    (hF : ∀ a b, F a b = match b.1.1 with
      | .reg p => (a.1.push (b.1.2, p), a.2)
      | .stack off => (a.1, a.2.emit (.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags)))
    (hl : ∀ b ∈ l, (∀ p, b.1.1 = .reg p → ∀ n c, p ≠ .vreg n c) ∧ b.1.2 ∈ regsInL args) :
    CtorOk ctx id args st (.op (.callArgs (l.foldl F (#[], st)).1.toList)) (l.foldl F (#[], st)).2 := by
  have := foldl_inv (fun a : Array (Reg × Reg) × LState =>
      (∀ q ∈ a.1.toList, q.1 ∈ regsInL args ∧ ∀ n c, q.2 ≠ .vreg n c) ∧
      a.2.nextVreg = st.nextVreg ∧ a.2.outgoing = st.outgoing ∧
      ∃ ms : List MInst, a.2.emitted = st.emitted ++ ms.toArray ∧ ∀ m ∈ ms, Benign m)
    F l (#[], st) ⟨by simp, rfl, rfl, [], by simp, by simp⟩ (by
      intro b hb a ⟨h1, h2, h3, ms, h4, h5⟩
      rw [hF]
      obtain ⟨hp, hr⟩ := hl b hb
      split
      · rename_i p hbp
        refine ⟨?_, h2, h3, ms, h4, h5⟩
        intro q hq
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact h1 q hq
        · exact ⟨hr, hp p hbp⟩
      · rename_i off _
        refine ⟨h1, by simp [LState.emit, h2], by simp [LState.emit, h3],
          ms ++ [MInst.store (storeOpOfBytes b.2) b.1.2 (.spOffset off) trustedFlags],
          by simp [LState.emit, h4], ?_⟩
        intro m hm
        rcases List.mem_append.mp hm with hm | hm
        · exact h5 m hm
        · simp only [List.mem_singleton] at hm
          subst hm
          exact ⟨fun c ti h => (by cases h), fun ⟨_, _, _, h⟩ => (by cases h)⟩)
  obtain ⟨h1, h2, h3, ms, h4, h5⟩ := this
  refine ctorOk_mk (by omega) (by omega)
    ⟨ms, h4, fun m hm => ⟨(h5 m hm).1, fun ht => absurd ht (h5 m hm).2⟩⟩ ?_ (by simp [V.valsIn, opVals])
    (by simp [V.instsIn]) (by simp [V.tlsIn])
  intro r hr
  simp only [V.regsIn, opRegs, pairRegs, List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
    or_false] at hr
  obtain ⟨q, hq, hr⟩ := hr
  obtain ⟨hq1, hq2⟩ := h1 q hq
  rcases hr with rfl | rfl
  · exact .inl hq1
  · exact .inr (.inr (.inr hq2))

/-- `gen_call_info`/`gen_call_ind_info`: the call's registers come from the arguments. -/
theorem ctorOk_callInfo {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {c : CallInfo}
    {k : Nat} (hr : ∀ r ∈ opRegs (.callInfo c), r ∈ regsInL args) :
    CtorOk ctx id args st (.op (.callInfo c))
      { st with outgoing := max st.outgoing k } :=
  ctorOk_mk (Nat.le_refl _) (Nat.le_max_left _ _) ⟨[], by simp, by simp⟩
    (fun r h => .inl (hr r h)) (by simp [V.valsIn, opVals]) (by simp [V.instsIn]) (by simp [V.tlsIn])

theorem ctorOk_putRegsVec {ctx : Ctx} {id : TermId} {st : LState} {vs : List Nat} {rs : List Reg}
    (h : vs.mapM ctx.valueReg? = some rs) :
    CtorOk ctx id [.values vs] st (.regsVec (rs.map fun r => [r])) st := by
  refine ctorOk_same ?_ (by simp [V.valsIn]) (by simp [V.instsIn]) (by simp [V.tlsIn])
  intro r hr
  have hr' : r ∈ rs := by
    simp only [V.regsIn, List.mem_flatten, List.mem_map] at hr
    obtain ⟨_, ⟨a, ha, rfl⟩, hr⟩ := hr
    simp only [List.mem_singleton] at hr
    exact hr ▸ ha
  obtain ⟨x, hx, he⟩ := mapM_mem h r hr'
  exact .inr (.inl ⟨x, by simpa [V.valsIn] using hx, he⟩)

theorem ctorOk_tryRets {ctx : Ctx} {id : TermId} {args : List V} {st : LState} {k : Nat}
    {ps : List Reg} (hps : retRegs k = some ps) (cc : Option Clif.CallConv)
    (f : Reg × Reg → Bool) :
    CtorOk ctx id args st
      (.op (.callRets (ps.zip ctx.tryRegs.1 ++ List.filter f ((payloadRegs cc).zip ctx.tryRegs.2))))
      st := by
  refine ⟨Nat.le_refl _, Nat.le_refl _, ⟨[], by simp, by simp⟩, fun r hr => ?_,
    by simp [V.valsIn, opVals], by simp [V.instsIn], by simp [V.tlsIn]⟩
  simp only [V.regsIn, opRegs, pairRegs, List.mem_flatMap, List.mem_append, List.mem_filter,
    List.mem_cons, List.mem_nil_iff, or_false] at hr
  obtain ⟨⟨a, b⟩, hq, hr⟩ := hr
  rcases hq with hq | ⟨hq, -⟩
  · have hz := List.of_mem_zip hq
    rcases hr with rfl | rfl
    · exact .inr (.inr (.inr (.inl (retRegs_phys hps _ hz.1))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl hz.2)))))
  · have hz := List.of_mem_zip hq
    rcases hr with rfl | rfl
    · exact .inr (.inr (.inr (.inl (payloadRegs_phys cc _ hz.1))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr hz.2)))))

/-- Close `CtorOk` of a constructor that keeps the state. -/
macro "ctor_same" : tactic => `(tactic| (refine ctorOk_same ?_ ?_ ?_ ?_ <;> simp_all (config := { decide := true }) [V.regsIn, opRegs, pairRegs, V.valsIn, opVals, V.instsIn, V.tlsIn] <;> done))

set_option maxHeartbeats 2000000 in
/-- **Every extern constructor** satisfies `CtorOk`. -/
theorem externCtor_ok (ctx : Ctx) (t : Term) (args : List V) (st : LState) :
    CtorP ctx st t.id args (externCtor ctx t args st) := by
  unfold externCtor
  split
  · intro v st' h
    split at h
    · cases h
      exact ctorOk_same (by simp [V.regsIn]) (by simp [V.valsIn]) (by simp [V.instsIn])
        (by simp [V.tlsIn])
    · cases h
  · apply externCtor_split _ (CtorP ctx st)
    all_goals
      intros
      unfold CtorP
      intro v st' h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals first
      | ctor_same
      | (rename_i heq; simp only [Option.map_eq_some_iff, Function.comp_apply] at heq
         obtain ⟨_, _, rfl⟩ := heq; ctor_same)
      | exact ctorOk_invalid
      | exact ctorOk_fresh
      | exact ctorOk_emit rfl ‹_›
      | exact ctorOk_emitBenign ⟨fun c ti h => (by cases h), fun ⟨_, _, _, h⟩ => (by cases h)⟩
      | exact ctorOk_lc (loadConstantFull_ok _ _ _ _ _)
      | exact ctorOk_callOutput _ _ (fun _ _ => rfl)
      | (refine ctorOk_callInfo ?_
         intro r hr
         simp only [opRegs, List.mem_append, List.mem_singleton, List.mem_nil_iff, false_or] at hr
         simp only [regsInL_cons, regsInL_nil, V.regsIn, opRegs, List.mem_append,
           List.mem_singleton, List.mem_nil_iff, List.append_nil]
         first | (rcases hr with (h | h) | h <;> simp [h]) | (rcases hr with h | h <;> simp [h]))
      | (refine ctorOk_same ?_ (by simp [V.valsIn]) (by simp [V.instsIn]) (by simp [V.tlsIn])
         intro r hr
         simp only [V.regsIn, List.mem_flatten, List.mem_map] at hr
         obtain ⟨_, ⟨r', hr', rfl⟩, hr⟩ := hr
         simp only [List.mem_singleton] at hr
         subst hr
         obtain ⟨x, hx, he⟩ := mapM_mem ‹_› r' hr'
         exact .inr (.inl ⟨x, by simpa [V.valsIn] using hx, he⟩))
      | (refine ctorOk_same ?_ (by simp [V.valsIn]) (by simp [V.instsIn]) (by simp [V.tlsIn])
         intro r hr
         simp only [V.regsIn, List.mem_singleton] at hr
         subst hr
         exact .inl (by simpa [V.regsIn] using List.mem_of_getElem? ‹_›))
      | (refine ctorOk_same ?_ (by simp [V.valsIn, opVals]) (by simp [V.instsIn]) (by simp [V.tlsIn])
         intro r hr
         simp only [V.regsIn, opRegs, pairRegs, List.mem_flatMap, List.mem_cons, List.mem_nil_iff,
           or_false] at hr
         obtain ⟨⟨a, b⟩, hq, hr⟩ := hr
         have hz := List.of_mem_zip hq
         rcases hr with rfl | rfl
         · exact .inr (.inr (retRegs_phys ‹_› _ hz.1))
         · obtain ⟨l, hl, hrl⟩ := single_mem ‹_› _ hz.2
           exact .inl (by simp [V.regsIn, opRegs]; exact ⟨l, hl, hrl⟩))
      | (refine ctorOk_callArgs _ _ (fun _ _ => rfl) ?_
         intro b hb
         have hz := List.of_mem_zip hb
         have hz1 := List.of_mem_zip hz.1
         refine ⟨fun p hp => sigArgLocs_phys ‹_› _ (hp ▸ hz1.1) p rfl, ?_⟩
         obtain ⟨l, hl, hrl⟩ := single_mem ‹_› _ hz1.2
         simp [V.regsIn, opRegs]; exact ⟨l, hl, hrl⟩)
      | exact ctorOk_putRegsVec ‹_›
      | exact ctorOk_tryRets ‹_› _ _


/-! ## Extern extractors -/

gen_match_split externExtract_split Backend.externExtract.match_27

/-- A value without registers, CLIF values, instructions or `ElfTlsGetAddr` data. -/
def NoAtoms (v : V) : Prop := v.regsIn = [] ∧ v.valsIn = [] ∧ v.instsIn = [] ∧ v.tlsIn = false

/-- `n` is an operand of the definition of a value of `v`. -/
def ArgOfDef (ctx : Ctx) (v : V) (n : Nat) : Prop :=
  ∃ m ∈ v.valsIn, ∃ j info c, ctx.defInst? m = some j ∧ ctx.insts[j]? = some info ∧
    info.clif = some c ∧ n ∈ Driver.instArgs c

theorem defClif_inv {ctx : Ctx} {n : Nat} {c : Clif.Inst} (h : ctx.defClif? n = some c) :
    ∃ j info, ctx.defInst? n = some j ∧ ctx.insts[j]? = some info ∧ info.clif = some c := by
  unfold Ctx.defClif? at h
  obtain ⟨j, hj, h⟩ := bind_some_ex h
  obtain ⟨info, hi, h⟩ := bind_some_ex h
  exact ⟨j, info, hj, hi, h⟩

theorem argOfDef_of {ctx : Ctx} {m x : Nat} {c : Clif.Inst} (h : ctx.defClif? m = some c)
    (hx : x ∈ Driver.instArgs c) : ArgOfDef ctx (.value m) x := by
  obtain ⟨j, info, h1, h2, h3⟩ := defClif_inv h
  exact ⟨m, by simp [V.valsIn], j, info, c, h1, h2, h3, hx⟩

/-- What extern extractor `x` gives on `v`, by the groups of `aext`. -/
structure ExtSpec (ctx : Ctx) (x : TermId) (v : V) (fs : List V) : Prop where
  c0 : ((tyPred x).isSome = true ∨ x ∈ clean0Ext) → ∀ f ∈ fs, NoAtoms f
  val : x ∈ valueExt → ∀ f ∈ fs, f.regsIn = [] ∧ f.tlsIn = false ∧
    (∀ n ∈ f.valsIn, n ∈ v.valsIn ∨ ArgOfDef ctx v n) ∧
    (∀ j ∈ f.instsIn, ∃ m ∈ v.valsIn, ctx.defInst? m = some j)
  idv : x = TId.inst_data_value → ∃ i info, v = .inst i ∧ ctx.insts[i]? = some info ∧
    fs = [.ty (info.resTys.head?.getD .invalid), info.data]
  fr : x = TId.first_result → ∃ i info r, v = .inst i ∧ ctx.insts[i]? = some info ∧
    info.results.head? = some r ∧ fs = [.value r]

/-- `ExtSpec` of every successful result. -/
def ExtP (ctx : Ctx) (x : TermId) (v : V) (r : ExtResult (List V)) : Prop :=
  ∀ fs, r = .ok fs → ExtSpec ctx x v fs

theorem extSpec_noAtoms {ctx : Ctx} {x : TermId} {v : V} {fs : List V} (hf : ∀ f ∈ fs, NoAtoms f)
    (hv : x ∉ valueExt) (hi : x ≠ TId.inst_data_value) (hr : x ≠ TId.first_result) :
    ExtSpec ctx x v fs :=
  ⟨fun _ => hf, fun h => absurd h hv, fun h => absurd h hi, fun h => absurd h hr⟩

set_option maxHeartbeats 2000000 in
/-- **Every extern extractor** satisfies `ExtSpec`. -/
theorem externExtract_ok (ctx : Ctx) (t : Term) (v : V) (st : LState) :
    ExtP ctx t.id v (externExtract ctx t v st) := by
  unfold externExtract
  split
  · intro fs h
    split at h
    · cases h
      rename_i hp _
      refine ⟨fun _ f hf => ?_, fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
      · simp only [List.mem_singleton] at hf; subst hf
        simp [NoAtoms, V.regsIn, V.valsIn, V.instsIn, V.tlsIn]
      · have : ∀ x ∈ valueExt, tyPred x = none := by decide
        rw [this _ hx] at hp; cases hp
      · rw [hx] at hp; cases hp
      · rw [hx] at hp; cases hp
    · cases h
  · intro fs h; cases h
  · apply externExtract_split _ (ExtP ctx)
    all_goals
      intros
      unfold ExtP
      intro fs h
      try dsimp only at h
      repeat' (split at h)
      all_goals try (cases h; done)
    all_goals cases h
    all_goals
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals intro hx
      all_goals first
        | exact absurd hx (by decide)
        | (simp_all (config := { decide := true }) [NoAtoms, V.regsIn, V.valsIn, V.instsIn, V.tlsIn,
             opRegs, opVals]; done)
        | exact ⟨_, _, rfl, ‹_›, rfl⟩
        | exact ⟨_, _, _, rfl, ‹_›, ‹_›, rfl⟩
        | (intro f hf; simp only [List.mem_singleton] at hf; subst hf
           refine ⟨rfl, rfl, by simp [V.valsIn], ?_⟩
           intro j hj; simp [V.instsIn] at hj; subst hj
           exact ⟨_, by simp [V.valsIn], ‹_›⟩)
        | (intro f hf; simp only [List.mem_singleton] at hf; subst hf
           refine ⟨rfl, rfl, ?_, by simp [V.instsIn]⟩
           intro n hn; simp [V.valsIn, opVals] at hn; subst hn
           exact .inr (argOfDef_of ‹_› (by simp [Driver.instArgs])))

end Backend.Proof.Flow
