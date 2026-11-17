import FV.Opt.Legal
import FV.Clif.Unwind

/-!
# The handler edges of an `i128` legalisation (S10e, #232)

`Opt.Legal.check` validates a `try_call`'s arguments, results and normal-return successor, but
not its exception table's items: the legaliser rewrites them too (`rewriteItems`, splitting
`i128` handler arguments), and the run with unwinding (`Clif.runLoopX`) continues at a handler
when the callee unwinds. `exnOk f g cert` checks them (decidable, run by `lean-backend` next to
`check`):

* for every `try_call` terminator of `f` and every `try_call` terminator of `g` that `termOk`
  relates (the frame relation of the refinement proof does not say which block of `g` the
  target runs, only that its terminator is related to the source's), the items agree one by
  one (`itemsOk`): the same tags in the same order, `default` for `default`, and handler
  destinations related by `destOk`: the same block (never the entry block), its arguments
  expanded by the block's parameters (`expandExn`: an `i128` value as its pair, an exception
  payload `exn0`/`exn1` as itself at a parameter that is not `i128`);
* `g` has no `return_call` terminator (the refinement proof follows the target in `g`'s code).
-/

namespace Opt.Legal

open Clif Opt.Legalize128

/-- The arguments of a `try_call`'s handler successor with parameters `ps` (`rewriteItems`): an
`i128` value as its pair, a plain value as itself, an exception payload `exn0`/`exn1` as itself at
a parameter that is not `i128` (Rust's payload is two `i64` words); no `retN`. -/
def expandExn (C : Ctx) : List TryArg → List (ValueId × Ty) → Option (List TryArg)
  | [], [] => some []
  | .val v :: as, (_, t) :: ps =>
    if t == .i128 then
      match C.pair v with
      | some (a, b) => ([.val a, .val b] ++ ·) <$> expandExn C as ps
      | none => none
    else if C.plain v then (.val v :: ·) <$> expandExn C as ps else none
  | .exn i :: as, (_, t) :: ps =>
    if t != .i128 && decide (i < 2) then (.exn i :: ·) <$> expandExn C as ps else none
  | _, _ => none

/-- A handler destination of `f` and its rewrite: the same block (not the entry block), the
arguments expanded by its parameters. -/
def destOk (C : Ctx) (d d' : TryDest) : Bool :=
  d'.block == d.block && C.entryId? != some d.block &&
    match C.f.block? d.block with
    | some B => expandExn C d.args B.params == some d'.args
    | none => false

/-- An exception-table item of `f` and its rewrite. -/
def itemOk (C : Ctx) : ExnItem → ExnItem → Bool
  | .tag n d, .tag n' d' => n' == n && destOk C d d'
  | .default d, .default d' => destOk C d d'
  | .context _, .context _ => true
  | _, _ => false

/-- The items of an exception table of `f` and of its rewrite, one by one. -/
def itemsOk (C : Ctx) : List ExnItem → List ExnItem → Bool
  | [], [] => true
  | i :: is, i' :: is' => itemOk C i i' && itemsOk C is is'
  | _, _ => false

/-- The handler edges of a terminator of `f` and a terminator of `g` that `termOk` relates. -/
def termExnOk (C : Ctx) : Terminator → Terminator → Bool
  | .tryCall fn args et, .tryCall fn' args' et' =>
    !termOk C (.tryCall fn args et) [] (.tryCall fn' args' et') || itemsOk C et.items et'.items
  | _, _ => true

/-- `t` is a `return_call`. -/
def isReturnCall : Terminator → Bool
  | .returnCall .. => true
  | _ => false

/-- **The handler-edge check** of a legalisation `g` of `f` (certificate `cert`). -/
def exnOk (f g : Function) (cert : Cert) : Bool :=
  let C : Ctx := ⟨f, g, cert⟩
  (f.blocks.all fun b => g.blocks.all fun b' => termExnOk C b.term b'.term) &&
    g.blocks.all fun b' => !isReturnCall b'.term

/-! ### `exnOk` as the compiler runs it (#1074)

`exnOk` relates every terminator of `f` to every terminator of `g`, and each `try_call` pair
evaluates `termOk`, which recomputes `C.T0` (`maxValueId`) and the two `freshValue`s (passes over
the whole function): `try_call`s² × size (num-bigint's `bigint_scalar::test_scalar_div_rem`'s
`check_sub`: 3,119 `try_call`s, 31,015 instructions, over an hour). `exnOkF` computes the three
once per function (`termOkF`); `exnOk_eq_F` (`@[csimp]`) proves it equal. -/

/-- `termExnOk` with `C.T0`, `C.f.freshValue` and `C.g.freshValue` given (`t0`, `ff`, `gf`). -/
def termExnOkF (C : Ctx) (t0 ff gf : Nat) : Terminator → Terminator → Bool
  | .tryCall fn args et, .tryCall fn' args' et' =>
    !termOkF C t0 ff gf (.tryCall fn args et) [] (.tryCall fn' args' et') ||
      itemsOk C et.items et'.items
  | _, _ => true

theorem termExnOk_eq_F (C : Ctx) (t t' : Terminator) :
    termExnOk C t t' = termExnOkF C C.T0 C.f.freshValue C.g.freshValue t t' := by
  cases t <;> cases t' <;> rfl

/-- `exnOk` as the compiler runs it (`exnOk_eq_F`, `@[csimp]`): `T0` and the two `freshValue`s
once per function. -/
def exnOkF (f g : Function) (cert : Cert) : Bool :=
  let C : Ctx := ⟨f, g, cert⟩
  let t0 := C.T0
  let ff := f.freshValue
  let gf := g.freshValue
  (f.blocks.all fun b => g.blocks.all fun b' => termExnOkF C t0 ff gf b.term b'.term) &&
    g.blocks.all fun b' => !isReturnCall b'.term

@[csimp] theorem exnOk_eq_F : @exnOk = @exnOkF := by
  funext f g cert
  simp only [exnOk, exnOkF, termExnOk_eq_F]

/-! ## Spec -/

theorem exnOk_items {f g : Function} {cert : Cert} (h : exnOk f g cert = true) {B B' : Block}
    (hB : B ∈ f.blocks) (hB' : B' ∈ g.blocks) {fn fn' : FnRef} {args args' : List ValueId}
    {et et' : ExnTable} (ht : B.term = .tryCall fn args et) (ht' : B'.term = .tryCall fn' args' et')
    (hok : termOk ⟨f, g, cert⟩ (.tryCall fn args et) [] (.tryCall fn' args' et') = true) :
    itemsOk ⟨f, g, cert⟩ et.items et'.items = true := by
  simp only [exnOk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 B hB B' hB'
  rw [ht, ht'] at this
  simpa [termExnOk, hok] using this

theorem exnOk_noReturnCall {f g : Function} {cert : Cert} (h : exnOk f g cert = true) {B' : Block}
    (hB' : B' ∈ g.blocks) : ∀ fn args, B'.term ≠ .returnCall fn args := by
  intro fn args he
  simp only [exnOk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 B' hB'
  rw [he] at this
  simp [isReturnCall] at this

/-- Related item lists catch an exception at related destinations. -/
theorem catch?_itemsOk {C : Ctx} {e : Exn} :
    ∀ {is is' : List ExnItem}, itemsOk C is is' = true →
      (is.findSome? fun
        | .tag n d => if e.catches n then some d else none
        | .default d => some d
        | .context _ => none) = none ∧
        (is'.findSome? fun
          | .tag n d => if e.catches n then some d else none
          | .default d => some d
          | .context _ => none) = none ∨
      ∃ d d', (is.findSome? fun
          | .tag n d => if e.catches n then some d else none
          | .default d => some d
          | .context _ => none) = some d ∧
        (is'.findSome? fun
          | .tag n d => if e.catches n then some d else none
          | .default d => some d
          | .context _ => none) = some d' ∧ destOk C d d' = true
  | [], [], _ => .inl ⟨rfl, rfl⟩
  | i :: is, i' :: is', h => by
    simp only [itemsOk, Bool.and_eq_true] at h
    obtain ⟨hi, hs⟩ := h
    have ih := catch?_itemsOk (C := C) (e := e) hs
    match i, i', hi with
    | .tag n d, .tag n' d', hi =>
      simp only [itemOk, Bool.and_eq_true, beq_iff_eq] at hi
      obtain ⟨hn, hd⟩ := hi
      subst hn
      by_cases hc : e.catches n' = true
      · exact .inr ⟨d, d', by simp [hc], by simp [hc], hd⟩
      · simpa [List.findSome?_cons, hc] using ih
    | .default d, .default d', hi =>
      simp only [itemOk] at hi
      exact .inr ⟨d, d', by simp, by simp, hi⟩
    | .context _, .context _, _ => simpa [List.findSome?_cons] using ih
    | .tag _ _, .default _, hi | .tag _ _, .context _, hi | .default _, .tag _ _, hi
    | .default _, .context _, hi | .context _, .tag _ _, hi | .context _, .default _, hi =>
      simp [itemOk] at hi
  | [], _ :: _, h => by simp [itemsOk] at h
  | _ :: _, [], h => by simp [itemsOk] at h

theorem catch?_rel {C : Ctx} {e : Exn} {et et' : ExnTable}
    (h : itemsOk C et.items et'.items = true) :
    (et.catch? e = none ∧ et'.catch? e = none) ∨
      ∃ d d', et.catch? e = some d ∧ et'.catch? e = some d' ∧ destOk C d d' = true :=
  catch?_itemsOk h

end Opt.Legal
