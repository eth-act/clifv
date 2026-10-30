import FV.Opt.Proof.SemSimX
import FV.Opt.Proof.DomInv

/-!
# Fresh-value windows: from pass simulations to `IsSimX`

A `try_call` binds its results at the function's fresh values (`Function.freshValue`, above
every value the function defines) before its normal-return successor reads them (`.ret i`
arguments, `Clif.tryNormal`). The two sides of a pass have different fresh values when the
pass removes the definition of the largest value, so the pass relations (which relate the values
the functions define) say nothing about them. The *window* of a frame is its registers from the
function's fresh value on; only `try_call`s write there (statement results and block parameters
are below it), with the same values on both sides.

`W R`: `R`, both frames at a program point of a block of their function (`InB`), and equal
windows (`Win`). `IsSimW R` is `IsSimX R` with the windows and program points available to the
`call_indirect` and `try_call` obligations; `IsSimW.toX`: `W R` is then an `IsSimX`.
`FunSimX.ofW` builds the function simulation (entry frames have empty windows).
-/

namespace Opt

open Clif

/-- `fr` is at a program point of a block of its function. -/
abbrev InB (fr : Frame) : Prop := FrameInv (fun _ => True) fr

/-- The windows of `a` and `b` (registers from each function's fresh value on) are equal. -/
def Win (a b : Frame) : Prop :=
  ∀ i, a.regs (a.func.freshValue + i) = b.regs (b.func.freshValue + i)

/-- `R` with program points and equal windows. -/
def W (R : Frame → Frame → Prop) (a b : Frame) : Prop := R a b ∧ InB a ∧ InB b ∧ Win a b

/-! ## Fresh values -/

theorem lt_foldl_of_mem {α : Type} (g : Nat → α → Nat) (hg : ∀ m a, m ≤ g m a) {x : Nat} {a : α}
    (hx : ∀ m, x < g m a) : ∀ (l : List α), a ∈ l → ∀ m, x < l.foldl g m
  | [], h, _ => by cases h
  | b :: l, h, m => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.lt_of_lt_of_le (hx m) (le_foldl g hg l _)
    · exact lt_foldl_of_mem g hg hx l h _
where
  le_foldl (g : Nat → α → Nat) (hg : ∀ m a, m ≤ g m a) : ∀ (l : List α) m, m ≤ l.foldl g m
    | [], _ => Nat.le_refl _
    | b :: l, m => Nat.le_trans (hg m b) (le_foldl g hg l _)

theorem le_foldl' {α : Type} (g : Nat → α → Nat) (hg : ∀ m a, m ≤ g m a) :
    ∀ (l : List α) m, m ≤ l.foldl g m :=
  lt_foldl_of_mem.le_foldl g hg

/-- Block parameters and statement results are below the fresh value. -/
theorem lt_freshValue {f : Function} {b : Block} (hb : b ∈ f.blocks) :
    (∀ p ∈ b.params, p.1 < f.freshValue) ∧ ∀ st ∈ b.body, ∀ r ∈ st.results, r < f.freshValue := by
  have hres : ∀ (st : Stmt) m, m ≤ st.results.foldl (fun m r => max m (r + 1)) m :=
    fun st => le_foldl' _ (fun m r => Nat.le_max_left _ _) _
  have hbody : ∀ m, m ≤ b.body.foldl (fun m st => st.results.foldl (fun m r => max m (r + 1)) m) m :=
    le_foldl' _ (fun m st => hres st m) _
  have hgb : ∀ m (b : Block), m ≤ (fun m (b : Block) =>
      let m := b.params.foldl (fun m p => max m (p.1 + 1)) m
      b.body.foldl (fun m st => st.results.foldl (fun m r => max m (r + 1)) m) m) m b := by
    intro m b
    exact Nat.le_trans (le_foldl' _ (fun m p => Nat.le_max_left _ _) _ _)
      (le_foldl' _ (fun m st => hres st m) _ _)
  refine ⟨fun p hp => ?_, fun st hst r hr => ?_⟩
  · refine lt_foldl_of_mem _ hgb (fun m => ?_) f.blocks hb 0
    refine Nat.lt_of_lt_of_le ?_ (le_foldl' _ (fun m st => hres st m) _ _)
    exact lt_foldl_of_mem (fun m (p : ValueId × Ty) => max m (p.1 + 1))
      (fun m p => Nat.le_max_left _ _)
      (fun m => Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)) _ hp m
  · refine lt_foldl_of_mem _ hgb (fun m => ?_) f.blocks hb 0
    refine lt_foldl_of_mem _ (fun m st => hres st m) (fun m => ?_) _ hst _
    exact lt_foldl_of_mem (fun m (r : ValueId) => max m (r + 1)) (fun m r => Nat.le_max_left _ _)
      (fun m => Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)) _ hr m

/-- Binding values below `W` keeps the registers from `W` on. -/
theorem setMany_above {r r' : Regs} {xs : List ValueId} {vs : List Val} {W : Nat}
    (h : r.setMany xs vs = some r') (hx : ∀ x ∈ xs, x < W) (i : Nat) : r' (W + i) = r (W + i) :=
  ((setMany_spec h).2 _).1 fun hm => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hx _ hm) (Nat.le_add_right _ _))

/-- Binding a `try_call`'s results at `W`: the window holds them, then what it held. -/
theorem setMany_tryRets {r r' : Regs} {n W : Nat} {vs : List Val}
    (h : r.setMany (tryRets n W) vs = some r') (i : Nat) :
    r' (W + i) = if i < n then vs[i]? else r (W + i) := by
  obtain ⟨hl, hy⟩ := setMany_spec h
  split
  · rename_i hi
    have hm : W + i ∈ tryRets n W := List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    obtain ⟨k, hk, he⟩ := (hy _).2 hm
    rw [List.getElem?_eq_some_iff] at hk
    obtain ⟨hkl, hkv⟩ := hk
    simp [tryRets] at hkv
    rw [show k = i by omega] at he; exact he
  · rename_i hi
    refine (hy _).1 fun hm => ?_
    obtain ⟨j, hj, he⟩ := List.mem_map.1 hm
    have hjn := List.mem_range.1 hj
    have hji : W + j = W + i := he
    omega

theorem stmt_results_lt {fr : Frame} (hI : InB fr) {st : Stmt} {rest : List Stmt}
    (hb : fr.body = st :: rest) : ∀ r ∈ st.results, r < fr.func.freshValue := by
  obtain ⟨-, b, hbm, hsuf, -⟩ := hI
  exact (lt_freshValue hbm).2 st (hsuf.subset (by rw [hb]; simp))

theorem enterBlock_win {fr fr1 : Frame} {bc : BlockCall} (h : enterBlock fr bc = .ok fr1) :
    InB fr1 ∧ fr1.func = fr.func ∧ fr1.slots = fr.slots ∧
      ∀ i, fr1.regs (fr.func.freshValue + i) = fr.regs (fr.func.freshValue + i) := by
  obtain ⟨b, args, regs, hb, -, -, hset, rfl⟩ := enterBlock_ok h
  have hbm : b ∈ fr.func.blocks := List.mem_of_find?_eq_some hb
  refine ⟨⟨trivial, b, hbm, List.suffix_refl _, rfl⟩, rfl, rfl, fun i => ?_⟩
  exact setMany_above hset (fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact (lt_freshValue hbm).1 p hp) i

/-- A local `next` step keeps the program point invariant and the window. -/
theorem lstep_next_win {fr m fr1 m1} (hI : InB fr) (h : lstep fr m = .next fr1 m1) :
    InB fr1 ∧ fr1.func = fr.func ∧
      ∀ i, fr1.regs (fr.func.freshValue + i) = fr.regs (fr.func.freshValue + i) := by
  refine ⟨lstep_next_inv hI h, (lstep_next_frame h).1, ?_⟩
  obtain ⟨func, regs, slots, body, term⟩ := fr
  cases body with
  | nil =>
    simp only [lstep] at h
    cases term <;> simp only [LRes.ofRes] at h <;> (repeat' split at h) <;> (try contradiction) <;>
      (cases h; exact (enterBlock_win ‹_›).2.2.2)
  | cons st rest =>
    simp only [lstep] at h
    split at h
    · simp only [LRes.ofRes] at h; split at h <;> contradiction
    · simp only [LRes.ofRes] at h
      split at h <;> try contradiction
      split at h <;> try contradiction
      cases h
      exact setMany_above ‹_› (stmt_results_lt hI rfl)

theorem LStar.win {fr m fr1 m1} (hI : InB fr) (h : LStar fr m fr1 m1) :
    InB fr1 ∧ fr1.func = fr.func ∧
      ∀ i, fr1.regs (fr.func.freshValue + i) = fr.regs (fr.func.freshValue + i) := by
  induction h with
  | refl => exact ⟨hI, rfl, fun _ => rfl⟩
  | step h1 _ ih =>
    obtain ⟨hI1, hf1, hw1⟩ := lstep_next_win hI h1
    obtain ⟨hI2, hf2, hw2⟩ := ih hI1
    refine ⟨hI2, hf2.trans hf1, fun i => ?_⟩
    rw [← hw1 i, ← hf1, hw2 i]

/-! ## The obligations with windows -/

/-- `CIOk` for frames at program points with equal windows. -/
def CIOkW (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop :=
  ∀ {fr fr' : Frame} {m : Mem} {st : Stmt} {rest : List Stmt} {sig : Nat} {callee : ValueId}
    {args : List ValueId} {d : Signature} {a : Nat} {vals : List Val},
    R fr fr' → InB fr → InB fr' → Win fr fr' → m.symbols = syms → fr.body = st :: rest →
    st.inst = .callIndirect sig callee args → ciArgs fr sig callee args = .ok (d, a, vals) →
    ∃ fr2 st' rest' sig' callee' args', LStar fr' m fr2 m ∧ fr2.body = st' :: rest' ∧
      st'.inst = .callIndirect sig' callee' args' ∧
      ciArgs fr2 sig' callee' args' = .ok (d, a, vals) ∧
      Cont R { fr with body := rest } st.results { fr2 with body := rest' } st'.results
        (AbiParam.tys d.returns)

/-- `TryOk` for frames at program points with equal windows. -/
structure TryOkW (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop where
  call : ∀ {fr fr' : Frame} {m : Mem} {fn : FnRef} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {ext : ExtFunc} {vals : List Val},
    R fr fr' → InB fr → InB fr' → Win fr fr' → m.symbols = syms → fr.body = [] →
    fr.term = .tryCall fn args et →
    tcArgs fr fn et = .ok (n, base, bc) → callArgs fr fn args = .ok (ext, vals) →
    ∃ fr2 fn' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCall fn' args' et' ∧ tcArgs fr2 fn' et' = .ok (n, base', bc') ∧
      callArgs fr2 fn' args' = .ok (ext, vals) ∧
      TCont R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys ext.sig.returns)
  ind : ∀ {fr fr' : Frame} {m : Mem} {callee : ValueId} {args : List ValueId} {et : ExnTable}
    {n : Nat} {base : ValueId} {bc : BlockCall} {d : Signature} {a : Nat} {vals : List Val},
    R fr fr' → InB fr → InB fr' → Win fr fr' → m.symbols = syms → fr.body = [] →
    fr.term = .tryCallIndirect callee args et →
    ticArgs fr et = .ok (n, base, bc) → ciArgs fr et.sig callee args = .ok (d, a, vals) →
    ∃ fr2 callee' args' et' base' bc', LStar fr' m fr2 m ∧ fr2.body = [] ∧
      fr2.term = .tryCallIndirect callee' args' et' ∧ ticArgs fr2 et' = .ok (n, base', bc') ∧
      ciArgs fr2 et'.sig callee' args' = .ok (d, a, vals) ∧
      TCont R fr (tryRets n base) bc fr2 (tryRets n base') bc' (AbiParam.tys d.returns)

/-- A pass simulation: `IsSim` and the window obligations. -/
structure IsSimW (syms : String → Option Nat) (R : Frame → Frame → Prop) : Prop where
  toIsSim : IsSim syms R
  ci : CIOkW syms R
  tc : TryOkW syms R

theorem tcArgs_base {fr : Frame} {fn : FnRef} {et : ExnTable} {n : Nat} {base : ValueId}
    {bc : BlockCall} (h : tcArgs fr fn et = .ok (n, base, bc)) :
    base = fr.func.freshValue ∧ tryNormal et base = .ok bc := by
  simp only [tcArgs, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.check_eq_ok, Res.pure_eq_ok,
    Prod.mk.injEq] at h
  obtain ⟨_, _, _, _, _, _, bc', hb, -, rfl, rfl⟩ := h
  exact ⟨rfl, hb⟩

theorem ticArgs_base {fr : Frame} {et : ExnTable} {n : Nat} {base : ValueId}
    {bc : BlockCall} (h : ticArgs fr et = .ok (n, base, bc)) :
    base = fr.func.freshValue ∧ tryNormal et base = .ok bc := by
  simp only [ticArgs, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok, Prod.mk.injEq] at h
  obtain ⟨_, _, bc', hb, -, rfl, rfl⟩ := h
  exact ⟨rfl, hb⟩

section
variable {syms : String → Option Nat} {R : Frame → Frame → Prop}

/-- A call's continuation, with program points and windows. -/
theorem Cont.win {fr fr2 : Frame} {st st' : Stmt} {rest rest' : List Stmt} {rtys : List Ty}
    (hI : InB fr) (hI2 : InB fr2) (hw : Win fr fr2) (hb : fr.body = st :: rest)
    (hb2 : fr2.body = st' :: rest')
    (h : Cont R { fr with body := rest } st.results { fr2 with body := rest' } st'.results rtys) :
    Cont (W R) { fr with body := rest } st.results { fr2 with body := rest' } st'.results rtys := by
  intro vs regs ht hs
  obtain ⟨regs', hs', hr⟩ := h vs regs ht hs
  refine ⟨regs', hs', hr, hI.rest hb regs, hI2.rest hb2 regs', fun i => ?_⟩
  show regs (fr.func.freshValue + i) = regs' (fr2.func.freshValue + i)
  rw [setMany_above hs (stmt_results_lt hI hb), setMany_above hs' (stmt_results_lt hI2 hb2)]
  exact hw i

/-- A `try_call`'s continuation, with program points and windows. -/
theorem TCont.win {fr fr2 : Frame} {n : Nat} {bc bc' : BlockCall} {rtys : List Ty}
    (hw : Win fr fr2)
    (h : TCont R fr (tryRets n fr.func.freshValue) bc fr2 (tryRets n fr2.func.freshValue) bc' rtys) :
    TCont (W R) fr (tryRets n fr.func.freshValue) bc fr2 (tryRets n fr2.func.freshValue) bc'
      rtys := by
  intro vs regs ht hs
  obtain ⟨regs', hs', hr⟩ := h vs regs ht hs
  refine ⟨regs', hs', fun fr1 he => ?_⟩
  obtain ⟨fr1', he', hr1⟩ := hr fr1 he
  obtain ⟨hI1, hf1, -, hw1⟩ := enterBlock_win he
  obtain ⟨hI1', hf1', -, hw1'⟩ := enterBlock_win he'
  refine ⟨fr1', he', hr1, hI1, hI1', fun i => ?_⟩
  simp only at hf1 hf1' hw1 hw1'
  rw [hf1, hf1', hw1 i, hw1' i]
  show regs (fr.func.freshValue + i) = regs' (fr2.func.freshValue + i)
  rw [setMany_tryRets hs, setMany_tryRets hs']
  split
  · rfl
  · exact hw i

/-- **A pass simulation with windows is a simulation** covering `call_indirect` and
`try_call`/`try_call_indirect`. -/
theorem IsSimW.toX (hR : IsSimW syms R) : IsSimX syms (W R) where
  toIsSim := {
    frame := fun ⟨h, _⟩ => hR.toIsSim.frame h
    next := by
      rintro fr fr' m fr1 m1 ⟨h, hI, hI', hw⟩ hm hl
      obtain ⟨fr1', hst, hr⟩ := hR.toIsSim.next h hm hl
      obtain ⟨hI1, hf1, hw1⟩ := lstep_next_win hI hl
      obtain ⟨hI1', hf1', hw1'⟩ := LStar.win hI' hst
      refine ⟨fr1', hst, hr, hI1, hI1', fun i => ?_⟩
      rw [hf1, hf1', hw1 i, hw1' i]; exact hw i
    call := by
      rintro fr fr' m ext vals rs rest ⟨h, hI, hI', hw⟩ hm hl
      obtain ⟨fr2, rs', rest', hst, hl2, hk⟩ := hR.toIsSim.call h hm hl
      obtain ⟨st, fn, args, hb, -, rfl, -⟩ := lstep_call_inv hl
      obtain ⟨st', fn', args', hb2, -, rfl, -⟩ := lstep_call_inv hl2
      obtain ⟨hI2, hf2, hw2⟩ := LStar.win hI' hst
      refine ⟨fr2, st'.results, rest', hst, hl2, Cont.win hI hI2 (fun i => ?_) hb hb2 hk⟩
      rw [hf2, hw2 i]; exact hw i
    ret := fun ⟨h, _⟩ hm hl => hR.toIsSim.ret h hm hl
    tail := fun ⟨h, _⟩ hm hl => hR.toIsSim.tail h hm hl
    trap := fun ⟨h, _⟩ hm hl => hR.toIsSim.trap h hm hl }
  ci := by
    rintro fr fr' m st rest sig callee args d a vals ⟨h, hI, hI', hw⟩ hm hb hi hca
    obtain ⟨fr2, st', rest', sig', callee', args', hst, hb2, hi2, hca2, hk⟩ :=
      hR.ci h hI hI' hw hm hb hi hca
    obtain ⟨hI2, hf2, hw2⟩ := LStar.win hI' hst
    refine ⟨fr2, st', rest', sig', callee', args', hst, hb2, hi2, hca2,
      Cont.win hI hI2 (fun i => ?_) hb hb2 hk⟩
    rw [hf2, hw2 i]; exact hw i
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr' m fn args et n base bc ext vals ⟨h, hI, hI', hw⟩ hm hb ht htc hca
      obtain ⟨fr2, fn', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk⟩ :=
        hR.tc.call h hI hI' hw hm hb ht htc hca
      obtain ⟨hI2, hf2, hw2⟩ := LStar.win hI' hst
      have hw' : Win fr fr2 := fun i => by rw [hf2, hw2 i]; exact hw i
      obtain ⟨rfl, -⟩ := tcArgs_base htc
      obtain ⟨rfl, -⟩ := tcArgs_base htc2
      exact ⟨fr2, fn', args', et', _, bc', hst, hb2, ht2, htc2, hca2, hk.win hw'⟩
    · rintro fr fr' m callee args et n base bc d a vals ⟨h, hI, hI', hw⟩ hm hb ht htc hca
      obtain ⟨fr2, callee', args', et', base', bc', hst, hb2, ht2, htc2, hca2, hk⟩ :=
        hR.tc.ind h hI hI' hw hm hb ht htc hca
      obtain ⟨hI2, hf2, hw2⟩ := LStar.win hI' hst
      have hw' : Win fr fr2 := fun i => by rw [hf2, hw2 i]; exact hw i
      obtain ⟨rfl, -⟩ := ticArgs_base htc
      obtain ⟨rfl, -⟩ := ticArgs_base htc2
      exact ⟨fr2, callee', args', et', _, bc', hst, hb2, ht2, htc2, hca2, hk.win hw'⟩

end

/-- A function simulation from a pass simulation with windows: entry frames are at the entry
block and have empty windows. -/
theorem FunSimX.ofW {f g : Function} (hn : g.name = f.name) (hs : g.sig = f.sig)
    (hsl : g.slots = f.slots) (hx : g.externs = f.externs)
    (hsim : ∀ syms, ∃ R, IsSimW syms R ∧ ∀ b, f.entry? = some b → ∃ b', g.entry? = some b' ∧
      b'.params = b.params ∧ ∀ args regs (slots : List (SlotId × Nat)),
        args.map (·.ty) = b.params.map (·.2) →
        Regs.empty.setMany (b.params.map (·.1)) args = some regs →
        slots.map (·.1) = f.slots.map (·.1) →
        R ⟨f, regs, slots, b.body, b.term⟩ ⟨g, regs, slots, b'.body, b'.term⟩) :
    FunSimX f g where
  name := hn
  sig := hs
  slots := hsl
  externs := hx
  sim syms := by
    obtain ⟨R, hR, he⟩ := hsim syms
    refine ⟨W R, hR.toX, fun b hb => ?_⟩
    obtain ⟨b', hb', hp, hr⟩ := he b hb
    refine ⟨b', hb', hp, fun args regs slots ht hset hsl' => ⟨hr args regs slots ht hset hsl',
      ⟨trivial, b, List.mem_of_mem_head? hb, List.suffix_refl _, rfl⟩,
      ⟨trivial, b', List.mem_of_mem_head? hb', List.suffix_refl _, rfl⟩, fun i => ?_⟩⟩
    have hbm : b ∈ f.blocks := List.mem_of_mem_head? hb
    have hbm' : b' ∈ g.blocks := List.mem_of_mem_head? hb'
    have h1 := setMany_above hset (fun x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; exact (lt_freshValue hbm).1 p hp) i
    have hset' := hset
    rw [← hp] at hset'
    have h2 := setMany_above hset' (fun x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; exact (lt_freshValue hbm').1 p hp) i
    show regs (f.freshValue + i) = regs (g.freshValue + i)
    rw [h1, h2]; rfl


/-! ## `try_call` successors -/

/-- Pointwise relation of two lists. -/
inductive Pw2 {α β : Type} (Q : α → β → Prop) : List α → List β → Prop
  | nil : Pw2 Q [] []
  | cons {x y xs ys} : Q x y → Pw2 Q xs ys → Pw2 Q (x :: xs) (y :: ys)

theorem Pw2.imp {α β : Type} {Q Q' : α → β → Prop} (h : ∀ x y, Q x y → Q' x y) {xs ys}
    (hp : Pw2 Q xs ys) : Pw2 Q' xs ys := by
  induction hp with
  | nil => exact .nil
  | cons hq _ ih => exact .cons (h _ _ hq) ih

/-- The arguments of a `try_call` successor, results from `b` (`Clif.tryNormal`). -/
def resolve (b : ValueId) : List TryArg → Res (List ValueId)
  | [] => .ok []
  | a :: l => do
    let x ← (match a with
      | .val v => pure v
      | .ret i => pure (b + i)
      | .exn _ => .stuck "try_call: exception payload on the normal-return edge")
    let xs ← resolve b l
    pure (x :: xs)

theorem tryNormal_eq (et : ExnTable) (b : ValueId) :
    tryNormal et b = (do let args ← resolve b et.normal.args; pure { block := et.normal.block, args }) := by
  unfold tryNormal
  congr 1
  generalize et.normal.args = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, resolve, ih]
    cases a <;> rfl

theorem resolve_pair (σ : ValueId → ValueId) (g : TryArg → TryArg)
    (hv : ∀ v, g (.val v) = .val (σ v)) (hr : ∀ i, g (.ret i) = .ret i)
    (he : ∀ i, g (.exn i) = .exn i) (b1 b2 : ValueId) :
    ∀ (l : List TryArg) (xs : List ValueId), resolve b1 l = .ok xs →
      ∃ ys, resolve b2 (l.map g) = .ok ys ∧
        Pw2 (fun x y => (∃ v, TryArg.val v ∈ l ∧ x = v ∧ y = σ v) ∨ ∃ i, x = b1 + i ∧ y = b2 + i)
          xs ys
  | [], xs, h => by
    simp only [resolve] at h
    cases h
    exact ⟨[], rfl, .nil⟩
  | a :: l, xs, h => by
    simp only [resolve, Res.bind_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    obtain ⟨ys, hys, h2⟩ := resolve_pair σ g hv hr he b1 b2 l xs' hxs
    have h2' : Pw2 (fun x y => (∃ v, TryArg.val v ∈ a :: l ∧ x = v ∧ y = σ v) ∨
        ∃ i, x = b1 + i ∧ y = b2 + i) xs' ys := h2.imp fun x y h => by
      rcases h with ⟨v, hm, h1, h2⟩ | h
      · exact Or.inl ⟨v, List.mem_cons_of_mem _ hm, h1, h2⟩
      · exact Or.inr h
    cases a with
    | val v =>
      simp only [Res.pure_eq_ok] at hx; subst hx
      refine ⟨σ v :: ys, ?_, .cons (.inl ⟨v, by simp, rfl, rfl⟩) h2'⟩
      simp only [List.map_cons, hv, resolve, hys]; rfl
    | ret i =>
      simp only [Res.pure_eq_ok] at hx; subst hx
      refine ⟨(b2 + i) :: ys, ?_, .cons (.inr ⟨i, rfl, rfl⟩) h2'⟩
      simp only [List.map_cons, hr, resolve, hys]; rfl
    | exn i => cases hx

/-- The normal-return successor of a `try_call` and of its renaming, from other fresh values:
the same block; arguments the renamed values or the results' values. -/
theorem tryNormal_pair (σ : ValueId → ValueId) {et et' : ExnTable}
    (hn : et'.normal = et.normal.mapVals σ) {b1 b2 : ValueId} {bc1 : BlockCall}
    (h : tryNormal et b1 = .ok bc1) :
    ∃ bc2, tryNormal et' b2 = .ok bc2 ∧ bc2.block = bc1.block ∧
      Pw2 (fun x y => (∃ v ∈ et.normal.vals, x = v ∧ y = σ v) ∨
        ∃ i, x = b1 + i ∧ y = b2 + i) bc1.args bc2.args := by
  rw [tryNormal_eq] at h ⊢
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨args1, hm1, rfl⟩ := h
  rw [hn]
  simp only [TryDest.mapVals]
  obtain ⟨ys, hys, h2⟩ := resolve_pair σ (fun (a : TryArg) => match a with | TryArg.val v => TryArg.val (σ v) | a => a)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) b1 b2 _ _ hm1
  refine ⟨_, by simp only [Res.bind_eq_ok]; exact ⟨ys, hys, rfl⟩, rfl, ?_⟩
  refine h2.imp fun x y hp => ?_
  rcases hp with ⟨v, hv, hx, hy⟩ | h
  · exact .inl ⟨v, List.mem_filterMap.2 ⟨_, hv, rfl⟩, hx, hy⟩
  · exact .inr h

theorem getMany_pw2 {A B : Frame} {xs ys : List ValueId}
    (h : Pw2 (fun x y => B.regs y = A.regs x) xs ys) {vs : List Val}
    (ha : A.getMany xs = .ok vs) : B.getMany ys = .ok vs := by
  induction h generalizing vs with
  | nil => exact ha
  | cons hxy _ ih =>
    simp only [Frame.getMany, Frame.get, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.pure_eq_ok] at ha ⊢
    obtain ⟨v, hv, vs', hvs, rfl⟩ := ha
    exact ⟨v, by rw [hxy]; exact hv, vs', ih hvs, rfl⟩

theorem normal_vals_sub {fn : FnRef} {args : List ValueId} {et : ExnTable} :
    ∀ v ∈ et.normal.vals, v ∈ termOperands (.tryCall fn args et) := by
  intro v hv; simp [termOperands, ExnTable.vals, hv]

theorem normal_vals_sub' {c : ValueId} {args : List ValueId} {et : ExnTable} :
    ∀ v ∈ et.normal.vals, v ∈ termOperands (.tryCallIndirect c args et) := by
  intro v hv; simp [termOperands, ExnTable.vals, hv]

theorem normal_succ {et : ExnTable} {b : ValueId} {bc : BlockCall} (h : tryNormal et b = .ok bc) :
    bc.block ∈ et.dests.map (·.block) := by
  rw [tryNormal_eq] at h
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨_, _, rfl⟩ := h
  simp [ExnTable.dests]


theorem tcArgs_ok {fr : Frame} {fn : FnRef} {et : ExnTable} {n : Nat} {base : ValueId}
    {bc : BlockCall} :
    tcArgs fr fn et = .ok (n, base, bc) ↔ ∃ ext sig, fr.func.extern? fn = some ext ∧
      fr.func.sigDecls.lookup et.sig = some sig ∧
      (AbiParam.tys sig.params == AbiParam.tys ext.sig.params &&
        AbiParam.tys sig.returns == AbiParam.tys ext.sig.returns) = true ∧
      base = fr.func.freshValue ∧ tryNormal et base = .ok bc ∧ n = ext.sig.returns.length := by
  unfold tcArgs
  constructor
  · intro h
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨ext, he, sig, hs, u, hc, bc', hb, hp⟩ := h
    simp only [Res.check_eq_ok] at hc
    simp only [Res.pure_eq_ok, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact ⟨ext, sig, he, hs, hc, rfl, hb, rfl⟩
  · rintro ⟨ext, sig, he, hs, hc, rfl, hb, rfl⟩
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok]
    exact ⟨ext, he, sig, hs, (), by simp only [Res.check_eq_ok]; exact hc, bc, hb, rfl⟩

theorem ticArgs_ok {fr : Frame} {et : ExnTable} {n : Nat} {base : ValueId} {bc : BlockCall} :
    ticArgs fr et = .ok (n, base, bc) ↔ ∃ sig, fr.func.sigDecls.lookup et.sig = some sig ∧
      base = fr.func.freshValue ∧ tryNormal et base = .ok bc ∧ n = sig.returns.length := by
  unfold ticArgs
  constructor
  · intro h
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨sig, hs, bc', hb, hp⟩ := h
    simp only [Res.pure_eq_ok, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    exact ⟨sig, hs, rfl, hb, rfl⟩
  · rintro ⟨sig, hs, rfl, hb, rfl⟩
    simp only [Res.bind_eq_ok, Res.ofOption_eq_ok]
    exact ⟨sig, hs, bc, hb, rfl⟩


theorem no_window' {a v j : Nat} (he : a + j = v) (hv : v < a) : False := by omega

end Opt
