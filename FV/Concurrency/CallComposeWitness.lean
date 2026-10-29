module

public import FV.Concurrency.CallCompose

@[expose] public section

/-!
# Non-vacuity of the linking induction (T2h, #311, layer 4b calls)

A thread of `Arm.stepi` halted in an error state without code (`sE`): every precise step has no
event and stays in `sE` (`tstep_sE`, `prun_sE`). With a caller that calls an **external** callee
at every step (its segment obligation `SegOk`: one step, then the callee entered) and the callee's
`ExtEvContract` (one step, then returned; no write), `link_compose_ext` gives the caller's
function contract, and it realizes **every** run entirely (`linked_sE`: the end `E` is `False`
and the caller never returns, so the realized prefix is the whole run, composed by
`Realized.trans`/`Refines.app` from the segments).
-/

namespace Concurrency.CallCompose.Witness

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise ClifThread ThreadRefine ArmAllocThread PrepThread
  ClifCStepTerm

/-- A halted thread: an error state without code. -/
def sE : ArmState := w .ERR (.Other "halted") ArmState.default

theorem decodeAt_sE (m : Memory) : decodeAt (setMem m sE) = none := by
  rw [decodeAt_setMem]
  simp only [decodeAt, fetch_inst_from_program, sE, w_program]
  rfl

theorem err_sE : read_err sE ≠ .None := by
  simp [sE, read_err, r, w, write_err, read_base_error, write_base_error]

theorem stepEvs_sE (m : Memory) : stepEvs (setMem m sE) = [] := by
  simp only [stepEvs, decodeAt_sE]

theorem cls_sE : cls sE = .plain := by
  have h := decodeAt_sE sE.mem
  rw [setMem_self] at h
  unfold cls; rw [h]

/-- **A precise step of the halted thread** has no event and stays put. -/
theorem tstep_sE {mon : Mon} {l : Lab} {t : ArmState × Mon}
    (hs : TStep Policy.arm stepi (sE, mon) l t) (hp : Precise sE l) : l.evs = [] ∧ t = (sE, mon) := by
  cases hs with
  | @exec _ _ evs hk hag hfp _ =>
    have he : evs = [] := by
      rcases hp with h | ⟨m, hm⟩
      · cases h
      · simpa [stepEvs_sE] using hm
    subst he
    refine ⟨rfl, ?_⟩
    simp only [applyR, setMem_self, stepi_err err_sE, cls_sE, monAfter]
  | xfail hc => rw [cls_sE] at hc; cases hc

/-- **Precise runs of the halted thread**: no event, and every prefix ends in `sE`. -/
theorem prun_sE {ok : ArmState → Lab → Prop} :
    ∀ {ls : List Lab} {mon : Mon} {t' : ArmState × Mon}, PRun Policy.arm stepi ok (sE, mon) ls t' →
      (∀ l ∈ ls, l.evs = []) ∧ ∀ k, PRun Policy.arm stepi ok (sE, mon) (ls.take k) (sE, mon)
  | [], _, _, .nil => ⟨by simp, fun _ => by simpa using PRun.nil⟩
  | _ :: _, mon, _, .cons hs hp ho hr => by
    obtain ⟨he, rfl⟩ := tstep_sE hs hp
    obtain ⟨h1, h2⟩ := prun_sE hr
    refine ⟨fun l hl => ?_, fun k => ?_⟩
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact he
      · exact h1 l hl
    · cases k with
      | zero => exact .nil
      | succ k => exact .cons hs hp ho (h2 k)

theorem evAt_noev {ls : List Lab} (h : ∀ l ∈ ls, l.evs = []) (q : Nat × Nat) :
    evAt (evTr ls) q = none := by
  simp only [evAt, evTr, List.getElem?_map]
  cases hq : ls[q.1]? with
  | none => rfl
  | some l => simp [h l (List.mem_of_getElem? hq)]

/-- **A prefix without events is realized by the empty CLIF run.** -/
theorem realized_noev {env : Clif.Env} {p : Clif.Program} {Priv : Nat → Prop} {ls : List Lab}
    (h : ∀ l ∈ ls, l.evs = []) {k : Nat} (hk : k ≤ ls.length) (c : TState) :
    Realized env p Priv ls k c c := by
  have h' : ∀ l ∈ ls.take k, l.evs = [] := fun l hl => h l (List.mem_of_mem_take hl)
  have hT : ∀ q, evAt (conv (evTr (ls.take k))) q = none := fun q => by
    rw [evAt_conv, evAt_noev h']; rfl
  refine ⟨hk, [], id, .nil, xClosed_of (fun b y hy => by rw [evAt_noev h'] at hy; cases hy), ?_⟩
  exact {
    ev := fun p x hx => by rw [evAt_nil] at hx; cases hx
    mono := fun p _ hp => by rw [evAt_nil] at hp; cases hp
    shared := fun p x hx => by rw [evAt_nil] at hx; cases hx
    priv := fun p y hy => by rw [hT] at hy; cases hy
    len := fun j hj => absurd hj (Nat.not_lt_zero _)
    pair := fun j hj => absurd hj (Nat.not_lt_zero _)
    pair_inv := fun p _ hp => by rw [evAt_nil] at hp; cases hp }

/-! ## The instance: a caller and an external callee -/

/-- `true`: the caller; `false`: the external callee. -/
abbrev Ext (b : Bool) : Prop := b = false

/-- Both are entered in the halted state, the CLIF thread returned. -/
def Ent (_ : Bool) (u : AT) (c : TState) : Prop := u.1 = sE ∧ c = .ret []

/-- The callee returns in the halted state; the caller never returns. -/
def Ret (b : Bool) (_ : AT) (_ : TState) (v : AT) (c' : TState) : Prop :=
  b = false ∧ v.1 = sE ∧ c' = .ret []

/-- The caller's invariant: halted. -/
def Inv (_ : Bool) (_ : AT) (_ : TState) (x : AT) (d : TState) : Prop := x.1 = sE ∧ d = .ret []

variable (env : Clif.Env) (p : Clif.Program) (Priv : Nat → Prop) (ok : ArmState → Lab → Prop)

/-- **The caller's segment obligation**: after one step, the external callee is entered. -/
theorem segOk_caller : SegOk env p Priv stepi ok Ent Ret (fun _ _ => False) (Inv true) true := by
  rintro u c ⟨x1, mon⟩ d ⟨hx, rfl⟩ ls t' hr
  simp only at hx; subst hx
  obtain ⟨hev, hpre⟩ := prun_sE hr
  cases ls with
  | nil => exact ⟨0, _, Realized.zero _ _, .inl rfl⟩
  | cons l ls =>
    refine ⟨1, .ret [], realized_noev hev (by simp) _, .inr (.inr (.inr ⟨Nat.one_pos, (sE, mon),
      false, hpre 1, ⟨rfl, rfl⟩, fun z d'' h => ⟨h.2.1, h.2.2⟩⟩))⟩

/-- **The external callee's event contract** (here proven): one step, then returned, no write. -/
theorem extContract : ExtEvContract env p Priv stepi ok Ext Ent Ret (fun _ _ => False)
    (fun _ _ => True) := by
  refine ⟨?_⟩
  rintro h ⟨u1, mon⟩ c rfl ⟨hu, rfl⟩ ls t' hr
  simp only at hu; subst hu
  obtain ⟨hev, hpre⟩ := prun_sE hr
  have hnw : ∀ k q y, evAt (evTr (ls.take k)) q = some y → y.k.dir = .W → ¬ True := by
    intro k q y hy
    rw [evAt_noev fun l hl => hev l (List.mem_of_mem_take hl)] at hy; cases hy
  cases ls with
  | nil => exact ⟨0, _, Realized.zero _ _, hnw 0, .inl rfl⟩
  | cons l ls =>
    exact ⟨1, .ret [], realized_noev hev (by simp) _, hnw 1,
      .inr (.inr ⟨(sE, mon), hpre 1, rfl, rfl, rfl⟩)⟩

/-- **Non-vacuity of `link_compose_ext`**: the caller's function contract, derived from its
segment obligation and the external callee's contract, realizes every run of the halted thread
entirely (the caller calls the callee at every step, the callee returns after one step). -/
theorem linked_sE (mon : Mon) {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm stepi ok (sE, mon) ls t') :
    ∃ c', Realized env p Priv ls ls.length (.ret []) c' := by
  have hF := link_compose_ext (env := env) (p := p) (Priv := Priv) (M := stepi) (ok := ok)
    (Ext := Ext) (Ent := Ent) (Ret := Ret) (E := fun _ _ => False) (Fr := fun _ _ => True)
    (Inv := Inv) (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (fun g hg => by
      obtain rfl : g = true := by simpa [Ext] using hg
      exact segOk_caller env p Priv ok)
    (extContract env p Priv ok) true (sE, mon) (.ret []) ⟨rfl, rfl⟩ ls t' hr
  obtain ⟨k, c', hR, hend⟩ := hF
  rcases hend with h | h | ⟨v, -, h, -⟩
  · exact ⟨c', h ▸ hR⟩
  · exact h.elim
  · cases h

end Concurrency.CallCompose.Witness
