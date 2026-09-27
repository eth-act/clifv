import FV.Compile.Model
import FV.Compile.Proof.Exec

/-!
# Simulation relations

* `Heap`: the abstract state of the map runtime, `handle ↦ (entry array, entries)`;
  `Mem`-level representation in `FV/Compile/Proof/Heap.lean`.
* `Enc H t x vs`: the flat CLIF values `vs` encode the DSL value `x : t.denote`.
* `hdl t vs`: the map handles in `vs` (outside vectors; well-formed vectors hold no maps).
* `EnvRel H r Γ ρ env vals st`: every variable alive in the checker state `st` has its values
  `vals[i]` in the registers `r` at `env[i]`, encoding `ρ`'s component.
* `selHdl p Γ vals`: the handles of the variables selected by `p`.
-/

set_option autoImplicit false

namespace Compile.Proof

open Compile
open Clif (Val Regs ValueId)
open DSL (Ty IntW)

abbrev Word := BitVec 64

/-- Map objects: handle ↦ (entry array base, entries as words). -/
abbrev Heap := Nat → Option (Nat × List (Word × Word))

/-- `H'` extends `H` (no object changed). -/
def Ext (H H' : Heap) : Prop := ∀ h p, H h = some p → H' h = some p

theorem Ext.refl (H : Heap) : Ext H H := fun _ _ h => h
theorem Ext.trans {H₁ H₂ H₃ : Heap} (h₁ : Ext H₁ H₂) (h₂ : Ext H₂ H₃) : Ext H₁ H₃ :=
  fun h p hp => h₂ h p (h₁ h p hp)

/-- `dom H ⊆ dom H'`. -/
def Dom (H H' : Heap) : Prop := ∀ h, H h ≠ none → H' h ≠ none

theorem Dom.refl (H : Heap) : Dom H H := fun _ h => h
theorem Dom.trans {H₁ H₂ H₃ : Heap} (h₁ : Dom H₁ H₂) (h₂ : Dom H₂ H₃) : Dom H₁ H₃ :=
  fun h hp => h₂ h (h₁ h hp)
theorem Ext.dom {H H' : Heap} (h : Ext H H') : Dom H H' := fun x hx => by
  cases hH : H x with
  | none => exact absurd hH hx
  | some p => rw [h x p hH]; simp

def encEntries (k v : Ty) (m : DSL.Map k.denote v.denote) : List (Word × Word) :=
  m.entries.map fun e => (toWord k e.1, toWord v e.2)

/-- The CLIF value of a machine integer. -/
def intV (w : IntW) (x : BitVec w.bits) : Val := Val.ofNat (intTy w) x.toNat

def Enc (H : Heap) : (t : Ty) → t.denote → List Val → Prop
  | .int w, x, vs => vs = [intV w x]
  | .bool, b, vs => vs = [Val.ofBool b]
  | .unit, _, vs => vs = []
  | .vec n t, xs, vs => ∃ parts : List (List Val), parts.length = n ∧ vs = parts.flatten ∧
      ∀ i (h : i < n), Enc H t xs[i] (parts.getD i [])
  | .prod a b, p, vs => ∃ v₁ v₂, vs = v₁ ++ v₂ ∧ Enc H a p.1 v₁ ∧ Enc H b p.2 v₂
  | .map k v, m, vs => ∃ h d, vs = [Val.ofNat .i64 h] ∧ h < 2 ^ 64 ∧ H h = some (d, encEntries k v m)

/-- Map handles of a flat value (not looking inside vectors). -/
def hdl : Ty → List Val → List Nat
  | .map _ _, v :: _ => [v.toNat]
  | .prod a b, vs => hdl a (vs.take (flat a).length) ++ hdl b (vs.drop (flat a).length)
  | _, _ => []

/-- Vector elements hold no maps (true for well-formed types). -/
def vecOk : Ty → Bool
  | .vec _ t => !t.hasMap
  | .prod a b => vecOk a && vecOk b
  | _ => true

theorem vecOk_of_wf : ∀ {t : Ty}, t.wf = true → vecOk t = true
  | .int _, _ | .bool, _ | .unit, _ | .map _ _, _ => rfl
  | .vec n t, h => by simp [DSL.Ty.wf] at h; simp [vecOk, h.1.2]
  | .prod a b, h => by
    simp [DSL.Ty.wf] at h; simp [vecOk, vecOk_of_wf h.1, vecOk_of_wf h.2]

namespace Enc

variable {H H' : Heap}

theorem length : ∀ {t : Ty} {x : t.denote} {vs : List Val}, Enc H t x vs →
    vs.length = (flat t).length
  | .int _, _, _, h | .bool, _, _, h | .unit, _, _, h => by simp_all [Enc, flat]
  | .map _ _, _, _, h => by obtain ⟨_, _, rfl, _⟩ := h; rfl
  | .prod a b, x, _, h => by
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    simp [flat, length h₁, length h₂]
  | .vec n t, xs, _, h => by
    obtain ⟨parts, hl, rfl, hp⟩ := h
    simp only [flat, List.length_flatten]
    have : ∀ (ps : List (List Val)) (k : Nat), (∀ i (hi : i < ps.length),
        (ps.getD i []).length = (flat t).length) →
        (ps.map List.length).sum = ps.length * (flat t).length := by
      intro ps k hps
      induction ps with
      | nil => simp
      | cons p ps ih =>
        have h0 := hps 0 (by simp)
        simp only [List.getD_cons_zero] at h0
        simp only [List.map_cons, List.sum_cons, h0, List.length_cons]
        rw [ih fun i hi => by simpa using hps (i + 1) (by simp; omega)]
        simp [Nat.succ_mul, Nat.add_comm]
    rw [this parts 0 (fun i hi => length (hp i (hl ▸ hi))), hl]
    simp [List.map_replicate, List.sum_replicate_nat]

theorem tys : ∀ {t : Ty} {x : t.denote} {vs : List Val}, Enc H t x vs →
    vs.map (·.ty) = flat t
  | .int w, _, _, h => by subst h; simp [intV, Val.ofNat, flat]
  | .bool, _, _, h => by subst h; simp [Val.ofBool, flat]
  | .unit, _, _, h => by subst h; simp [flat]
  | .map _ _, _, _, h => by obtain ⟨_, _, rfl, _⟩ := h; simp [Val.ofNat, flat]
  | .prod a b, x, _, h => by
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    simp [flat, tys h₁, tys h₂]
  | .vec n t, xs, _, h => by
    obtain ⟨parts, hl, rfl, hp⟩ := h
    simp only [flat, List.map_flatten]
    congr 1
    apply List.ext_getElem (by simp [hl])
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_replicate]
    have := tys (hp i (by simp at h₁; omega))
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₁)] at this
    exact this

theorem ext (hx : Ext H H') : ∀ {t : Ty} {x : t.denote} {vs : List Val}, Enc H t x vs →
    Enc H' t x vs
  | .int _, _, _, h | .bool, _, _, h | .unit, _, _, h => h
  | .map _ _, _, _, h => by
    obtain ⟨hh, d, rfl, hlt, hH⟩ := h
    exact ⟨hh, d, rfl, hlt, hx _ _ hH⟩
  | .prod a b, x, _, h => by
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    exact ⟨v₁, v₂, rfl, ext hx h₁, ext hx h₂⟩
  | .vec n t, xs, _, h => by
    obtain ⟨parts, hl, rfl, hp⟩ := h
    exact ⟨parts, hl, rfl, fun i hi => ext hx (hp i hi)⟩

/-- Values without maps do not depend on the heap. -/
theorem nomap : ∀ {t : Ty} {x : t.denote} {vs : List Val}, t.hasMap = false → Enc H t x vs →
    Enc H' t x vs
  | .int _, _, _, _, h | .bool, _, _, _, h | .unit, _, _, _, h => h
  | .map _ _, _, _, hm, _ => by simp [DSL.Ty.hasMap] at hm
  | .prod a b, x, _, hm, h => by
    simp [DSL.Ty.hasMap] at hm
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    exact ⟨v₁, v₂, rfl, nomap hm.1 h₁, nomap hm.2 h₂⟩
  | .vec n t, xs, _, hm, h => by
    simp [DSL.Ty.hasMap] at hm
    obtain ⟨parts, hl, rfl, hp⟩ := h
    exact ⟨parts, hl, rfl, fun i hi => nomap hm (hp i hi)⟩

theorem hdl_prod {a b : Ty} {v₁ v₂ : List Val} (h : v₁.length = (flat a).length) :
    hdl (.prod a b) (v₁ ++ v₂) = hdl a v₁ ++ hdl b v₂ := by
  simp [hdl, ← h]

/-- A value's encoding depends on the heap only at its handles. -/
theorem frame : ∀ {t : Ty} {x : t.denote} {vs : List Val}, vecOk t = true →
    (∀ h ∈ hdl t vs, H' h = H h) → Enc H t x vs → Enc H' t x vs
  | .int _, _, _, _, _, h | .bool, _, _, _, _, h | .unit, _, _, _, _, h => h
  | .map _ _, _, _, _, hf, h => by
    obtain ⟨hh, d, rfl, hlt, hH⟩ := h
    refine ⟨hh, d, rfl, hlt, ?_⟩
    rw [hf hh (by simp [hdl, Val.toNat, Val.ofNat, Clif.Ty.width]; omega)]; exact hH
  | .prod a b, x, _, hv, hf, h => by
    simp [vecOk] at hv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    rw [hdl_prod (length h₁)] at hf
    exact ⟨v₁, v₂, rfl, frame hv.1 (fun h hm => hf h (List.mem_append_left _ hm)) h₁,
      frame hv.2 (fun h hm => hf h (List.mem_append_right _ hm)) h₂⟩
  | .vec n t, xs, _, hv, _, h => by
    simp [vecOk] at hv
    exact nomap (t := .vec n t) (by simp [DSL.Ty.hasMap, hv]) h

/-- The handles of an encoded value are objects of the heap. -/
theorem hdl_dom : ∀ {t : Ty} {x : t.denote} {vs : List Val}, Enc H t x vs →
    ∀ h ∈ hdl t vs, H h ≠ none
  | .int _, _, _, h | .bool, _, _, h | .unit, _, _, h => by
    subst h; simp [hdl]
  | .map _ _, _, _, h => by
    obtain ⟨hh, d, rfl, hlt, hH⟩ := h
    intro h hm
    simp [hdl, Val.toNat, Val.ofNat, Clif.Ty.width] at hm
    rw [hm, Nat.mod_eq_of_lt hlt, hH]; simp
  | .prod a b, x, _, h => by
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    rw [hdl_prod (length h₁)]
    intro h hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hdl_dom h₁ h hm
    · exact hdl_dom h₂ h hm
  | .vec n t, xs, _, h => by simp [hdl]

end Enc

/-! ## Checker states -/

/-- Variable `i` is alive in checker state `st`. -/
def alive (st : DSL.CheckSt) (i : Nat) : Bool := !DSL.Check.isDead st i

/-- Variable `i` was updated (in the current `bind` scope). -/
def mutd (st : DSL.CheckSt) (i : Nat) : Bool := (st.getD i (false, false)).2

theorem alive_tail (st : DSL.CheckSt) (i : Nat) : alive st.tail i = alive st (i + 1) := by
  cases st <;> simp [alive, DSL.Check.isDead]

theorem mutd_tail (st : DSL.CheckSt) (i : Nat) : mutd st.tail i = mutd st (i + 1) := by
  cases st <;> simp [mutd]

theorem alive_cons_zero (p : Bool × Bool) (st : DSL.CheckSt) :
    alive (p :: st) 0 = !p.1 := by simp [alive, DSL.Check.isDead]

theorem alive_cons_succ (p : Bool × Bool) (st : DSL.CheckSt) (i : Nat) :
    alive (p :: st) (i + 1) = alive st i := by simp [alive, DSL.Check.isDead]

theorem mutd_cons_zero (p : Bool × Bool) (st : DSL.CheckSt) : mutd (p :: st) 0 = p.2 := by
  simp [mutd]

theorem mutd_cons_succ (p : Bool × Bool) (st : DSL.CheckSt) (i : Nat) :
    mutd (p :: st) (i + 1) = mutd st i := by simp [mutd]

/-! ## Environments -/

/-- Handles of the variables selected by `p`. -/
def selHdl (p : Nat → Bool) : List Ty → List (List Val) → List Nat
  | t :: Γ, vs :: vals => (if p 0 then hdl t vs else []) ++ selHdl (fun i => p (i + 1)) Γ vals
  | _, _ => []

/-- The environment relation. -/
def EnvRel (H : Heap) (r : Regs) :
    (Γ : List Ty) → DSL.Env Γ → List (List ValueId) → List (List Val) → DSL.CheckSt → Prop
  | [], _, _, _, _ => True
  | t :: Γ, ρ, ids :: env, vs :: vals, st =>
    (alive st 0 = true → RegsHas r ids vs ∧ Enc H t ρ.1 vs) ∧ EnvRel H r Γ ρ.2 env vals st.tail
  | _ :: _, _, _, _, _ => False

/-- Every value id of the compile-time environment is below `n`. -/
def EnvIds (env : List (List ValueId)) (n : Nat) : Prop := ∀ ids ∈ env, ∀ x ∈ ids, x < n

theorem EnvIds.mono {env : List (List ValueId)} {n m : Nat} (h : EnvIds env n) (hnm : n ≤ m) :
    EnvIds env m := fun ids hi x hx => Nat.lt_of_lt_of_le (h ids hi x hx) hnm

theorem EnvIds.getD {env : List (List ValueId)} {n : Nat} (h : EnvIds env n) (i : Nat) :
    ∀ y ∈ env.getD i [], y < n := by
  intro y hy
  simp only [List.getD_eq_getElem?_getD] at hy
  cases hge : env[i]? with
  | none => simp [hge] at hy
  | some ids => simp [hge] at hy; exact h ids (List.mem_of_getElem? hge) y hy

end Compile.Proof
