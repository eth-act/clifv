import FV.Opt.Proof.Sem
import FV.Opt.Proof.Dom

/-!
# Facts about `Clif.evalInst` used by the pass proofs

* `evalInst_congr`: an instruction reads only its operands (and the slot bases / globals).
* `evalInst_types`: its results have `Inst.resultTypes`.
* `evalNode_mem`: a pure node reads memory only through the link-time symbols.
* `evalInst_pure`, `evalInst_removable`: pure nodes and removable instructions leave memory
  unchanged and never trap.
* `evalInst_total` — lemma (T) of `docs/contracts/midend.md`: a well-typed pure node with
  typed operands evaluates (for `symbol_value`: if the symbol is defined).
-/

namespace Opt

open Clif

theorem evalInst_congr {fr fr' : Frame} {mem : Mem} {i : Inst}
    (hg : fr'.func.globals = fr.func.globals) (hs : fr'.slots = fr.slots)
    (hr : ∀ x ∈ operands i, fr'.regs x = fr.regs x) : evalInst fr' mem i = evalInst fr mem i := by
  cases i <;> simp only [operands, List.mem_cons, or_false, forall_eq_or_imp,
    forall_eq, List.not_mem_nil, false_imp_iff, imp_true_iff] at hr <;>
    simp only [evalInst, Frame.getAs, Frame.get, hr, hs, hg]

theorem evalNode_congr {fr fr' : Frame} {mem : Mem} {i : Inst}
    (hg : fr'.func.globals = fr.func.globals) (hs : fr'.slots = fr.slots)
    (hr : ∀ x ∈ operands i, fr'.regs x = fr.regs x) : evalNode fr' mem i = evalNode fr mem i := by
  simp only [evalNode, evalInst_congr hg hs hr]

theorem getMany_congr {fr fr' : Frame} {xs : List ValueId}
    (h : ∀ x ∈ xs, fr'.regs x = fr.regs x) : fr'.getMany xs = fr.getMany xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Frame.getMany, Frame.get, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem getMany_ok {fr : Frame} {xs : List ValueId} {vs : List Val} (h : fr.getMany xs = .ok vs) :
    vs.length = xs.length ∧ ∀ (n : Nat) x, xs[n]? = some x → fr.regs x = vs[n]? := by
  induction xs generalizing vs with
  | nil => cases h; simp
  | cons x xs ih =>
    simp only [Frame.getMany, Frame.get, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨a, ha, vs', hvs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih hvs
    refine ⟨by simp [h1], fun n y hy => ?_⟩
    cases n with
    | zero => simp at hy; subst hy; simpa using ha
    | succ n => simpa using h2 n y (by simpa using hy)

theorem getMany_of {fr : Frame} {xs : List ValueId} {vs : List Val} (hl : vs.length = xs.length)
    (h : ∀ (n : Nat) x, xs[n]? = some x → fr.regs x = vs[n]?) : fr.getMany xs = .ok vs := by
  induction xs generalizing vs with
  | nil => cases vs <;> simp_all [Frame.getMany]
  | cons x xs ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      have hx := h 0 x rfl
      simp only [List.getElem?_cons_zero] at hx
      simp only [Frame.getMany, Frame.get, hx, Res.ofOption_some, Res.ok_bind]
      rw [ih (by simpa using hl) (fun n y hy => by simpa using h (n + 1) y (by simpa using hy))]
      rfl

/-- The results of `evalInst` have the instruction's result types. -/
theorem evalInst_types {fr : Frame} {mem : Mem} {i : Inst} {vals : List Val} {mem' : Mem}
    {sigOf : FnRef → Option Signature} {ts : List Ty}
    (h : evalInst fr mem i = .ok (vals, mem')) (ht : i.resultTypes sigOf = some ts) :
    vals.map (·.ty) = ts := by
  cases i <;> simp only [Inst.resultTypes, Option.some.injEq, Option.map_eq_some_iff] at ht <;>
    simp only [evalInst, Frame.getAs, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
  all_goals (repeat' split at h)
  all_goals (try simp only [Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq, Res.ofOption_eq_ok] at h)
  all_goals (try obtain ⟨_, _, _, _, rfl, _⟩ := h)
  all_goals (try obtain ⟨_, _, rfl, _⟩ := h)
  all_goals (try obtain ⟨rfl, _⟩ := h)
  all_goals (try obtain ⟨_, _, _, _, _, _, rfl, _⟩ := h)
  all_goals (try subst ht)
  all_goals (try rfl)
  all_goals (try (simp only [List.map_cons, List.map_nil]; done))
  all_goals (try grind [Val.ofInt])
  all_goals (repeat (first | (obtain ⟨_, _, h⟩ := h) | (split at h) |
    (simp only [Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq, Res.ofOption_eq_ok] at h)))
  all_goals (try obtain ⟨rfl, _⟩ := h)
  all_goals (try rfl)
  all_goals grind [Val.ofInt]

@[simp] theorem Res.ofOption_ne_trap {α : Type} (m : String) (o : Option α) (c : TrapCode) :
    Res.ofOption m o = .trap c ↔ False := by
  cases o <;> simp [Res.ofOption]

@[simp] theorem Res.check_ne_trap (b : Bool) (m : String) (c : TrapCode) :
    Res.check b m = .trap c ↔ False := by
  cases b <;> simp [Res.check]

@[simp] theorem Res.pure_ne_trap {α : Type} (a : α) (c : TrapCode) :
    (pure a : Res α) = .trap c ↔ False := by
  simp [pure]

@[simp] theorem Frame.get_ne_trap (fr : Frame) (x : ValueId) (c : TrapCode) :
    fr.get x = .trap c ↔ False := by
  simp [Frame.get]

/-- Removable instructions (in particular pure nodes) keep memory and never trap. -/
theorem evalInst_removable {fr : Frame} {mem : Mem} {i : Inst} (hr : removable i = true) :
    (∀ vals mem', evalInst fr mem i = .ok (vals, mem') → mem' = mem) ∧
      ∀ c, evalInst fr mem i ≠ .trap c := by
  refine ⟨fun vals mem' h => ?_, fun c h => ?_⟩ <;>
  cases i <;> simp only [removable, isPure, Bool.false_or, Bool.or_false] at hr <;>
    (try cases hr) <;>
    simp only [evalInst, Frame.getAs, Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq,
      Res.bind_eq_trap, Res.ofOption_ne_trap, Res.check_ne_trap, Res.pure_ne_trap,
      Frame.get_ne_trap, false_or, or_false, and_false, exists_false] at h
  all_goals (repeat' split at h)
  all_goals (repeat (first | (obtain ⟨_, _, h⟩ := h) | (split at h) |
    (simp only [Res.bind_eq_ok, Res.pure_eq_ok, Prod.mk.injEq, Res.ofOption_eq_ok,
      Res.bind_eq_trap, Res.ofOption_ne_trap, Res.check_ne_trap, Res.pure_ne_trap,
      Frame.get_ne_trap, false_or, or_false, and_false, exists_false] at h)))
  all_goals grind

/-- A pure node that evaluates has one result, which is its `evalNode`, and keeps memory. -/
theorem evalInst_pure {fr : Frame} {mem : Mem} {i : Inst} (hp : isPure i = true) {vals mem'}
    (h : evalInst fr mem i = .ok (vals, mem')) :
    mem' = mem ∧ ∃ v, vals = [v] ∧ evalNode fr mem i = some v := by
  refine ⟨(evalInst_removable (by simp [removable, hp])).1 _ _ h, ?_⟩
  have ht : ∃ t, i.resultTypes (fun _ => none) = some [t] := by
    cases i <;> simp only [isPure] at hp <;> (try cases hp) <;> simp only [Inst.resultTypes]
    all_goals try exact ⟨_, rfl⟩
    rename_i ty lo hi
    cases hd : ty.double? with
    | none => simp [evalInst, hd, Res.ofOption] at h
    | some t => exact ⟨t, by simp⟩
  obtain ⟨t, ht⟩ := ht
  have hv := evalInst_types h ht
  match vals, hv with
  | [v], _ => exact ⟨v, rfl, by simp [evalNode, h]⟩

/-- The single value of an instruction result. -/
def val1 (r : Res (List Val × Mem)) : Option Val :=
  match r with
  | .ok ([v], _) => some v
  | _ => none

theorem evalNode_eq_val1 (fr : Frame) (mem : Mem) (i : Inst) :
    evalNode fr mem i = val1 (evalInst fr mem i) := rfl

theorem val1_bind {α : Type} (r : Res α) (k : α → Res (List Val × Mem)) :
    val1 (r >>= k) = match r with
      | .ok a => val1 (k a)
      | _ => none := by
  cases r <;> rfl

theorem val1_pure (vs : List Val) (m : Mem) :
    val1 (pure (vs, m)) = match vs with
      | [v] => some v
      | _ => none := by
  simp only [pure, val1]; split <;> simp_all

theorem val1_ok (vs : List Val) (m : Mem) :
    val1 (.ok (vs, m)) = match vs with
      | [v] => some v
      | _ => none := by
  simp only [val1]; split <;> simp_all

/-- A pure node reads memory only through the link-time symbols. -/
theorem evalNode_mem {fr : Frame} {m m' : Mem} {i : Inst} (hp : isPure i = true)
    (hs : m'.symbols = m.symbols) : evalNode fr m' i = evalNode fr m i := by
  cases i <;> simp only [isPure] at hp <;> (try cases hp) <;>
    simp only [evalNode_eq_val1, evalInst, val1_bind, val1_pure, hs]
  all_goals (repeat' (first | split | simp only [val1_bind, val1_pure, val1_ok]))
  all_goals simp_all [val1_bind, val1_pure, val1_ok, Res.ofOption]

theorem getAs_of {fr : Frame} {x : ValueId} {ty : Ty} {a : Val} (h : fr.regs x = some a)
    (ht : a.ty = ty) : ∃ b, fr.getAs x ty = .ok b := by
  obtain ⟨t, bits⟩ := a
  simp only at ht; subst ht
  exact ⟨bits, by simp [Frame.getAs, Frame.get, h]⟩

theorem shift_isSome {op : BinaryOp} (h : op.isShift = true) {w v : Nat} (x : BitVec w)
    (y : BitVec v) : ∃ r, Sem.shift op x y = some r := by
  cases op <;> simp [BinaryOp.isShift] at h <;> exact ⟨_, rfl⟩

/-- **(T)**: a well-typed pure node over typed operands evaluates, to one value, without
touching memory (`symbol_value`: when its symbol is defined). -/
theorem evalInst_total {f : Function} {tm : ValueId → Option Ty} {fr : Frame} {mem : Mem}
    {i : Inst} (hp : isPure i = true) (ht : pureTyped tm f i = true)
    (hf : fr.func.globals = f.globals)
    (hops : ∀ x ∈ operands i, ∃ a, fr.regs x = some a ∧ tm x = some a.ty)
    (hsl : ∀ s, (f.slots.lookup s).isSome → (fr.slots.lookup s).isSome)
    (hsym : ∀ ty gv name off col, i = .symbolValue ty gv →
      f.globals.lookup gv = some (.symbol name off col) → (mem.symbols name).isSome) :
    ∃ v, evalInst fr mem i = .ok ([v], mem) := by
  have hg : ∀ x ty, x ∈ operands i → tm x = some ty → ∃ b, fr.getAs x ty = .ok b := by
    intro x ty hx htx
    obtain ⟨a, ha, hta⟩ := hops x hx
    exact getAs_of ha (by rw [htx] at hta; exact (Option.some.inj hta).symm)
  have hr : ∀ x, x ∈ operands i → ∃ a, fr.get x = .ok a ∧ tm x = some a.ty := by
    intro x hx
    obtain ⟨a, ha, hta⟩ := hops x hx
    exact ⟨a, by simp [Frame.get, ha], hta⟩
  cases i <;> simp only [isPure] at hp <;> (try cases hp) <;>
    simp only [pureTyped, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Option.isSome_iff_exists]
      at ht
  case iconst => exact ⟨_, rfl⟩
  case unary op ty x =>
    obtain ⟨b, hb⟩ := hg x ty (by simp [operands]) ht
    simp [evalInst, hb]
  case binary op ty x y =>
    obtain ⟨b, hb⟩ := hg x ty (by simp [operands]) ht.1
    by_cases hs : op.isShift = true
    · obtain ⟨c, hc, _⟩ := hr y (by simp [operands])
      obtain ⟨r, hsh⟩ := shift_isSome hs b c.bits
      simp [evalInst, hb, hs, hc, hsh]
    · have hy : tm y = some ty := by
        rcases ht.2 with ⟨h1, _⟩ | h2
        · exact absurd h1 hs
        · exact h2
      obtain ⟨c, hc⟩ := hg y ty (by simp [operands]) hy
      simp [evalInst, hb, hs, hc]
  case icmp cc ty x y =>
    obtain ⟨b, hb⟩ := hg x ty (by simp [operands]) ht.1
    obtain ⟨c, hc⟩ := hg y ty (by simp [operands]) ht.2
    simp [evalInst, hb, hc]
  case select ty c x y =>
    obtain ⟨a, ha, _⟩ := hr c (by simp [operands])
    obtain ⟨b, hb⟩ := hg x ty (by simp [operands]) ht.1.2
    obtain ⟨d, hd⟩ := hg y ty (by simp [operands]) ht.2
    simp [evalInst, ha, hb, hd]
  case bitselect ty c x y =>
    obtain ⟨a, ha⟩ := hg c ty (by simp [operands]) ht.1.1
    obtain ⟨b, hb⟩ := hg x ty (by simp [operands]) ht.1.2
    obtain ⟨d, hd⟩ := hg y ty (by simp [operands]) ht.2
    simp [evalInst, ha, hb, hd]
  case bmask ty x =>
    obtain ⟨a, ha, _⟩ := hr x (by simp [operands])
    simp [evalInst, ha]
  case extend op ty x =>
    obtain ⟨a, ha, hta⟩ := hr x (by simp [operands])
    rw [hta] at ht
    simp only [decide_eq_true_eq] at ht
    cases op <;> simp [evalInst, ha, ht, Res.check]
  case ireduce ty x =>
    obtain ⟨a, ha, hta⟩ := hr x (by simp [operands])
    rw [hta] at ht
    simp only [decide_eq_true_eq] at ht
    simp [evalInst, ha, ht, Res.check]
  case iconcat ty lo hi =>
    obtain ⟨⟨⟨t2, h2⟩, h3⟩, h4⟩ := ht
    obtain ⟨b, hb⟩ := hg lo ty (by simp [operands]) h3
    obtain ⟨c, hc⟩ := hg hi ty (by simp [operands]) h4
    simp [evalInst, h2, hb, hc]
  case bitcast ty fl x =>
    obtain ⟨b, hb⟩ := hg x ty (by simp [operands]) ht
    simp [evalInst, hb]
  case stackAddr ty s off =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hsl s (Option.isSome_iff_exists.2 ht))
    simp [evalInst, hb]
  case symbolValue ty gv =>
    split at ht
    · rename_i name off col hgv
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hsym ty gv name off col rfl hgv)
      simp [evalInst, hf, hgv, hb]
    · cases ht

/-! ## Renaming -/

theorem operands_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    operands (mapOperands σ i) = (operands i).map σ := by
  cases i <;> rfl

theorem isPure_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    isPure (mapOperands σ i) = isPure i := by
  cases i <;> rfl

theorem removable_mapOperands (σ : ValueId → ValueId) (i : Inst) :
    removable (mapOperands σ i) = removable i := by
  cases i <;> rfl

/-- A result with the `stuck` message erased (renaming changes messages, nothing else). -/
def _root_.Clif.Res.norm {α : Type} : Res α → Res α
  | .stuck _ => .stuck ""
  | r => r

@[simp] theorem Res.norm_bind {α β : Type} (r : Res α) (k : α → Res β) :
    (r >>= k).norm = r.norm >>= fun a => (k a).norm := by
  cases r <;> rfl

@[simp] theorem Res.norm_ofOption {α : Type} (m : String) (o : Option α) :
    (Res.ofOption m o).norm = Res.ofOption "" o := by
  cases o <;> rfl

@[simp] theorem Res.norm_check (b : Bool) (m : String) : (Res.check b m).norm = Res.check b "" := by
  cases b <;> rfl

@[simp] theorem Res.norm_pure {α : Type} (a : α) : (pure a : Res α).norm = pure a := rfl

@[simp] theorem Res.norm_ok {α : Type} (a : α) : (Res.ok a).norm = .ok a := rfl

@[simp] theorem Res.norm_trap {α : Type} (c : TrapCode) : (Res.trap c : Res α).norm = .trap c := rfl

@[simp] theorem Res.norm_stuck {α : Type} (m : String) : (Res.stuck m : Res α).norm = .stuck "" := rfl

@[simp] theorem Res.norm_ofExcept {α : Type} (e : Except TrapCode α) :
    (Res.ofExcept e).norm = Res.ofExcept e := by
  cases e <;> rfl

theorem Res.norm_ite {α : Type} (c : Prop) [Decidable c] (a b : Res α) :
    (if c then a else b).norm = if c then a.norm else b.norm := by
  split <;> rfl

theorem Res.norm_eq_ok {α : Type} {r r' : Res α} (h : r'.norm = r.norm) {a : α} (ha : r = .ok a) :
    r' = .ok a := by
  subst ha; cases r' <;> simp_all [Res.norm]

theorem Res.norm_eq_trap {α : Type} {r r' : Res α} (h : r'.norm = r.norm) {c : TrapCode}
    (ha : r = .trap c) : r' = .trap c := by
  subst ha; cases r' <;> simp_all [Res.norm]

/-- Evaluating a renamed instruction in a frame that holds, at `σ x`, the value of `x`. -/
theorem evalInst_rename {σ : ValueId → ValueId} {fr fr' : Frame} {mem : Mem} {i : Inst}
    (hg : fr'.func.globals = fr.func.globals) (hs : fr'.slots = fr.slots)
    (hr : ∀ x ∈ operands i, fr'.regs (σ x) = fr.regs x) :
    (evalInst fr' mem (mapOperands σ i)).norm = (evalInst fr mem i).norm := by
  cases i <;> simp only [operands, List.mem_cons, or_false, forall_eq_or_imp,
    forall_eq, List.not_mem_nil, false_imp_iff, imp_true_iff] at hr <;>
    simp only [evalInst, mapOperands, Frame.getAs, Frame.get, hr, hs, hg, Res.norm_bind,
      Res.norm_ofOption, Res.norm_check, Res.norm_pure, Res.norm_ofExcept, Res.norm_ite,
      Res.norm_stuck, Res.norm_trap]
  all_goals (repeat' split) <;> simp_all

theorem evalNode_rename {σ : ValueId → ValueId} {fr fr' : Frame} {mem : Mem} {i : Inst}
    (hg : fr'.func.globals = fr.func.globals) (hs : fr'.slots = fr.slots)
    (hr : ∀ x ∈ operands i, fr'.regs (σ x) = fr.regs x) :
    evalNode fr' mem (mapOperands σ i) = evalNode fr mem i := by
  have h := evalInst_rename (mem := mem) hg hs hr
  simp only [evalNode]
  cases h1 : evalInst fr mem i with
  | ok a => rw [Res.norm_eq_ok h h1]
  | trap c => rw [Res.norm_eq_trap h h1]
  | stuck m =>
    rw [h1] at h
    cases h2 : evalInst fr' mem (mapOperands σ i) <;> simp_all [Res.norm]

theorem getMany_rename {σ : ValueId → ValueId} {fr fr' : Frame} {xs : List ValueId}
    (h : ∀ x ∈ xs, fr'.regs (σ x) = fr.regs x) :
    (fr'.getMany (xs.map σ)).norm = (fr.getMany xs).norm := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, Frame.getMany, Frame.get, h x (by simp), Res.norm_bind,
      Res.norm_ofOption, ih (fun y hy => h y (by simp [hy]))]

end Opt
