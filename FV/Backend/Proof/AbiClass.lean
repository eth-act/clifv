import FV.Backend.Isel

/-!
# Typed AAPCS64 placement: the integer case is the x-register placement

`sigArgLocs`/`abiRetRegs` (`FV/Backend/Isel.lean`, Cranelift's aarch64 `compute_arg_locs`)
place integer values in x0..x7 and `f32`/`f64` values in v0..v7, with separate counters. On
integer values that is the x-register placement the lowering used before floats:

* `argLocsC_int`: `argLocsC` of integer values is `argLocs`;
* `retRegsC_int`: `retRegsC` of `n` integer values is `retRegs n`;
* `sigArgLocs_eq`: on a signature with integer parameters only, `sigArgLocs` is the x-register
  placement through `argLocs` (the definition of `sigArgLocs` before the typed ABI);
* `abiRetRegs_int`: on a signature whose ABI returns are all integers, `abiRetRegs` is
  `retRegs` of their count; `regsClasses_int`: the classes of integer vregs.

Witnesses at the end: `(f64, i64, f32)` parameters go to `[v0, x0, v1]`, as do its returns.
-/

namespace Backend.Proof

open Backend

theorem tyClass_int {t : Clif.Ty} (h : t.isInt = true) : tyClass t = .int := by
  simp only [tyClass, h, ↓reduceIte]

/-! ## Arguments -/

/-- `argLocs`' step. -/
def xArgStep (q : Array ArgLoc × Nat × Nat) (b : Nat) : Array ArgLoc × Nat × Nat :=
  if q.2.1 < 8 then (q.1.push (.reg (.x q.2.1)), q.2.1 + 1, q.2.2)
  else (q.1.push (.stack (alignTo q.2.2 (max b 8))), q.2.1, alignTo q.2.2 (max b 8) + max b 8)

theorem argLocs_xArgStep (bytes : List Nat) :
    argLocs bytes = ((bytes.foldl xArgStep (#[], 0, 0)).1.toList,
      alignTo (bytes.foldl xArgStep (#[], 0, 0)).2.2 16) := rfl

/-- `argLocStep` on integer values is `xArgStep`, leaving the V-register counter alone. -/
theorem foldl_argLocStep_int : ∀ (bytes : List Nat) (acc : Array ArgLoc) (nx nv st : Nat),
    (bytes.map fun b => (RegClass.int, b)).foldl argLocStep (acc, nx, nv, st) =
      ((bytes.foldl xArgStep (acc, nx, st)).1, (bytes.foldl xArgStep (acc, nx, st)).2.1, nv,
        (bytes.foldl xArgStep (acc, nx, st)).2.2)
  | [], _, _, _, _ => rfl
  | b :: bytes, acc, nx, nv, st => by
    simp only [List.map_cons, List.foldl_cons]
    by_cases h : nx < 8
    · have e1 : argLocStep (acc, nx, nv, st) (.int, b) = (acc.push (.reg (.x nx)), nx + 1, nv, st) := by
        simp [argLocStep, h]
      have e2 : xArgStep (acc, nx, st) b = (acc.push (.reg (.x nx)), nx + 1, st) := by
        simp [xArgStep, h]
      rw [e1, e2]
      exact foldl_argLocStep_int bytes _ _ _ _
    · have e1 : argLocStep (acc, nx, nv, st) (.int, b) =
          (acc.push (.stack (alignTo st (max b 8))), nx, nv, alignTo st (max b 8) + max b 8) := by
        simp [argLocStep, h]
      have e2 : xArgStep (acc, nx, st) b =
          (acc.push (.stack (alignTo st (max b 8))), nx, alignTo st (max b 8) + max b 8) := by
        simp [xArgStep, h]
      rw [e1, e2]
      exact foldl_argLocStep_int bytes _ _ _ _

/-- **`argLocsC` of integer values is `argLocs`**: with no float value the V-register counter
never moves and every value takes the next of x0..x7, then the stack, as before. -/
theorem argLocsC_int (bytes : List Nat) :
    argLocsC (bytes.map fun b => (RegClass.int, b)) = argLocs bytes := by
  rw [argLocs_xArgStep]
  simp only [argLocsC, foldl_argLocStep_int]

/-- A location of the typed placement: x0..x8 (x8: the `sret` pointer), v0..v7, or a stack
slot. -/
def ArgLocOk : ArgLoc → Prop
  | .reg r => (∃ n, n ≤ 8 ∧ r = .x n) ∨ (∃ n, n < 8 ∧ r = .v n)
  | .stack _ => True

theorem argLocStep_push (q : Array ArgLoc × Nat × Nat × Nat) (p : RegClass × Nat) :
    ∃ l, ArgLocOk l ∧ (argLocStep q p).1 = q.1.push l := by
  obtain ⟨acc, nx, nv, st⟩ := q
  obtain ⟨c, b⟩ := p
  cases c
  · by_cases h : nx < 8
    · exact ⟨.reg (.x nx), .inl ⟨nx, by omega, rfl⟩, by simp [argLocStep, h]⟩
    · exact ⟨.stack (alignTo st (max b 8)), trivial, by simp [argLocStep, h]⟩
  · by_cases h : nv < 8
    · exact ⟨.reg (.v nv), .inr ⟨nv, h, rfl⟩, by simp [argLocStep, h]⟩
    · exact ⟨.stack (alignTo st (max b 8)), trivial, by simp [argLocStep, h]⟩

theorem foldl_argLocStep : ∀ (ps : List (RegClass × Nat)) (q : Array ArgLoc × Nat × Nat × Nat),
    (∀ l ∈ q.1.toList, ArgLocOk l) →
    (ps.foldl argLocStep q).1.size = q.1.size + ps.length ∧
      ∀ l ∈ (ps.foldl argLocStep q).1.toList, ArgLocOk l
  | [], q, h => ⟨by simp, by simpa using h⟩
  | p :: ps, q, h => by
    obtain ⟨l, hl, he⟩ := argLocStep_push q p
    rw [List.foldl_cons]
    have := foldl_argLocStep ps (argLocStep q p) (by
      rw [he]; intro l' hl'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl'
      rcases hl' with hl' | rfl
      · exact h l' hl'
      · exact hl)
    refine ⟨?_, this.2⟩
    rw [this.1, he]; simp; omega

/-- `argLocsC` places every value: one location per value, each `ArgLocOk`. -/
theorem argLocsC_shape (ps : List (RegClass × Nat)) :
    (argLocsC ps).1.length = ps.length ∧ ∀ l ∈ (argLocsC ps).1, ArgLocOk l := by
  have := foldl_argLocStep ps (#[], 0, 0, 0) (by simp)
  refine ⟨?_, this.2⟩
  simp only [argLocsC, Array.length_toList, this.1]; simp

/-- The classes of integer parameters are `.int`. -/
theorem map_tyClass_int : ∀ (L : List (Clif.AbiParam × Nat)), (∀ q ∈ L, q.1.ty.isInt = true) →
    L.map (fun q => (tyClass q.1.ty, q.2)) = (L.map (·.2)).map fun b => (RegClass.int, b)
  | [], _ => rfl
  | q :: L, h => by
    simp only [List.map_cons, tyClass_int (h q (by simp)),
      map_tyClass_int L (fun q' hq => h q' (List.mem_cons_of_mem _ hq))]

theorem map_snd_zip {α β : Type} : ∀ (l : List α) (m : List β), m.length ≤ l.length →
    (l.zip m).map (·.2) = m
  | _, [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: l, _ :: m, h => by
    simp only [List.zip_cons_cons, List.map_cons, map_snd_zip l m (by simpa using h)]

theorem mapM_option_length {α β : Type} (g : α → Option β) :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → r.length = l.length
  | [], r, h => by simp at h; subst h; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hg : g a with
    | none => simp [hg] at h
    | some b =>
      cases hl : l.mapM g with
      | none => simp [hg, hl] at h
      | some r' =>
        simp [hg, hl] at h
        subst h
        simp [mapM_option_length g hl]

theorem mapM_ok_length {α β ε : Type} (g : α → Except ε β) :
    ∀ {l : List α} {r : List β}, l.mapM g = .ok r → r.length = l.length
  | [], r, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : g a with
    | error e => rw [ha] at h; cases h
    | ok b =>
      rw [ha] at h
      cases hl : l.mapM g with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        simp [bind, Except.bind, pure, Except.pure] at h
        subst h
        simp [mapM_ok_length g hl]

/-- `sigArgs` sizes one byte count per parameter. -/
theorem sigArgs_length {s : Clif.Signature} {bytes : List Nat} (h : sigArgs s = .ok bytes) :
    bytes.length = s.params.length :=
  mapM_ok_length _ h

/-- `sretLocStep`'s fold keeps a property of locations that x8 has. -/
theorem sretLocStep_fold_P (P : ArgLoc → Prop) (h8 : P (.reg (.x 8))) :
    ∀ (ps : List Clif.AbiParam) (q : Array ArgLoc × List ArgLoc),
    (∀ l ∈ q.1.toList, P l) → (∀ l ∈ q.2, P l) →
    ∀ l ∈ (ps.foldl sretLocStep q).1.toList, P l
  | [], _, h1, _ => h1
  | p :: ps, ⟨acc, rest⟩, h1, h2 => by
    rw [List.foldl_cons]
    apply sretLocStep_fold_P P h8 ps
    · intro l hl
      unfold sretLocStep at hl
      split at hl
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact h1 l hl
        · exact h8
      · split at hl
        · rename_i l0 r heq
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
          rcases hl with hl | rfl
          · exact h1 l hl
          · exact h2 _ (by rw [heq]; simp)
        · exact h1 l hl
    · intro l hl
      unfold sretLocStep at hl
      split at hl
      · exact h2 l hl
      · split at hl
        · rename_i l0 r heq
          exact h2 l (by rw [heq]; exact List.mem_cons_of_mem _ hl)
        · cases hl

theorem sretLocStep_fold_ok : ∀ (ps : List Clif.AbiParam) (q : Array ArgLoc × List ArgLoc),
    (∀ l ∈ q.1.toList, ArgLocOk l) → (∀ l ∈ q.2, ArgLocOk l) →
    ∀ l ∈ (ps.foldl sretLocStep q).1.toList, ArgLocOk l :=
  sretLocStep_fold_P ArgLocOk (.inl ⟨8, Nat.le_refl _, rfl⟩)

/-- **`sigArgLocs` places every parameter**: one location per parameter, each in x0..x8,
v0..v7 or on the stack. -/
theorem sigArgLocs_shape {s : Clif.Signature} {locs : List ArgLoc} {n : Nat}
    (h : sigArgLocs s = .ok (locs, n)) :
    locs.length = s.params.length ∧ ∀ l ∈ locs, ArgLocOk l := by
  unfold sigArgLocs at h
  cases hb : sigArgs s with
  | error e => rw [hb] at h; cases h
  | ok bytes =>
    have hl := sigArgs_length hb
    simp only [hb, bind, Except.bind, paramLocs] at h
    split at h
    · split at h
      · cases h
      · rename_i hsz
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        refine ⟨by simpa using hsz, fun l hl => ?_⟩
        exact sretLocStep_fold_ok s.params (#[], (argLocsC _).1) (by simp) (argLocsC_shape _).2 l
          (by simpa using hl)
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      have hs := argLocsC_shape ((s.params.zip bytes).map fun q => (tyClass q.1.ty, q.2))
      rw [h] at hs
      exact ⟨by rw [hs.1]; simp [hl], hs.2⟩

theorem filter_zip_length {α β : Type} (p : α → Bool) :
    ∀ (l : List α) (m : List β), m.length = l.length →
      ((l.zip m).filter fun x => p x.1).length = (l.filter p).length
  | [], _, _ => by simp
  | a :: l, [], h => by simp at h
  | a :: l, b :: m, h => by
    simp only [List.zip_cons_cons, List.filter_cons]
    have := filter_zip_length p l m (by simpa using h)
    split <;> simp [this]

theorem sretFold_size : ∀ (ps : List Clif.AbiParam) (q : Array ArgLoc × List ArgLoc),
    (ps.filter fun p => !(p.purpose == .sret)).length ≤ q.2.length →
    (ps.foldl sretLocStep q).1.size = q.1.size + ps.length
  | [], _, _ => by simp
  | p :: ps, q, h => by
    rw [List.foldl_cons]
    by_cases hp : (p.purpose == .sret) = true
    · have e : sretLocStep q p = (q.1.push (.reg (.x 8)), q.2) := by simp [sretLocStep, hp]
      rw [e, sretFold_size ps _ (by simpa [List.filter_cons, hp] using h)]
      simp; omega
    · rcases q with ⟨acc, _ | ⟨l, rest⟩⟩
      · simp [hp] at h
      · have e : sretLocStep (acc, l :: rest) p = (acc.push l, rest) := by simp [sretLocStep, hp]
        rw [e, sretFold_size ps _ (by simp [hp] at h; simpa using h)]
        simp; omega

/-- `sigArgLocs` computes where `sigArgs` does. -/
theorem sigArgLocs_ok {s : Clif.Signature} {bytes : List Nat} (hb : sigArgs s = .ok bytes) :
    ∃ locs n, sigArgLocs s = .ok (locs, n) := by
  unfold sigArgLocs
  simp only [hb, bind, Except.bind, paramLocs]
  split
  · have hn := filter_zip_length (fun p : Clif.AbiParam => !(p.purpose == .sret)) s.params bytes
      (sigArgs_length hb)
    have hsz := sretFold_size s.params (#[], (argLocsC (((s.params.zip bytes).filter
      fun x => !x.1.purpose == .sret).map fun q => (tyClass q.1.ty, q.2))).1) (by
        rw [(argLocsC_shape _).1]
        simp [hn])
    simp only [hsz, Array.size_empty, Nat.zero_add, bne_self_eq_false, Bool.false_eq_true,
      ite_false]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩


/-- With at most 8 values from register counters `nx`, `nv` (and no stack used yet), every value
gets a register (of either class) and the stack stays unused. -/
theorem foldl_argLocStep_small : ∀ (ps : List (RegClass × Nat)) (acc : Array ArgLoc) (nx nv : Nat),
    nx + nv + ps.length ≤ 8 → (∀ l ∈ acc.toList, ∃ r, l = .reg r) →
    (∀ l ∈ (ps.foldl argLocStep (acc, nx, nv, 0)).1.toList, ∃ r, l = .reg r) ∧
      (ps.foldl argLocStep (acc, nx, nv, 0)).2.2.2 = 0
  | [], _, _, _, _, h => ⟨h, rfl⟩
  | (c, b) :: ps, acc, nx, nv, hn, h => by
    simp only [List.length_cons] at hn
    rw [List.foldl_cons]
    have hpush : ∀ r, ∀ l ∈ (acc.push (ArgLoc.reg r)).toList, ∃ r, l = .reg r := by
      intro r l hl
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact h l hl
      · exact ⟨r, rfl⟩
    cases c
    · have e : argLocStep (acc, nx, nv, 0) (.int, b) = (acc.push (.reg (.x nx)), nx + 1, nv, 0) := by
        simp [argLocStep, show nx < 8 by omega]
      rw [e]
      exact foldl_argLocStep_small ps _ _ _ (by omega) (hpush _)
    · have e : argLocStep (acc, nx, nv, 0) (.float, b) = (acc.push (.reg (.v nv)), nx, nv + 1, 0) := by
        simp [argLocStep, show nv < 8 by omega]
      rw [e]
      exact foldl_argLocStep_small ps _ _ _ (by omega) (hpush _)

/-- At most 8 values all go in registers, with no stack-argument area. -/
theorem argLocsC_small (ps : List (RegClass × Nat)) (h : ps.length ≤ 8) :
    (argLocsC ps).2 = 0 ∧ ∀ l ∈ (argLocsC ps).1, ∃ r, l = .reg r := by
  have := foldl_argLocStep_small ps #[] 0 0 (by omega) (by simp)
  simp only [argLocsC]
  exact ⟨by rw [this.2]; rfl, fun l hl => this.1 l (by simpa using hl)⟩

theorem length_map_filter_zip_le {α β γ : Type} (f : α × β → γ) (g : α × β → Bool) :
    ∀ (l : List α) (m : List β), (((l.zip m).filter g).map f).length ≤ m.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: m => by
    have := length_map_filter_zip_le f g l m
    simp only [List.zip_cons_cons, List.filter_cons, List.length_cons]
    split <;> simp at this ⊢ <;> omega

/-- **A signature with at most 8 parameters passes every argument in a register** (of its
class: x0..x7, v0..v7, x8 for an `sret` pointer) and has no stack-argument area. -/
theorem sigArgLocs_small {s : Clif.Signature} {bytes : List Nat} {locs : List ArgLoc} {n : Nat}
    (hb : sigArgs s = .ok bytes) (h8 : bytes.length ≤ 8) (h : sigArgLocs s = .ok (locs, n)) :
    n = 0 ∧ ∀ l ∈ locs, ∃ r, l = .reg r := by
  have hl := sigArgs_length hb
  unfold sigArgLocs at h
  simp only [hb, bind, Except.bind, paramLocs] at h
  split at h
  · split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hs := argLocsC_small _ (Nat.le_trans (length_map_filter_zip_le
        (fun q : Clif.AbiParam × Nat => (tyClass q.1.ty, q.2)) (fun x => !x.1.purpose == .sret)
        s.params bytes) h8)
      refine ⟨hs.1, fun l hl => ?_⟩
      exact sretLocStep_fold_P (fun l => ∃ r, l = .reg r) ⟨_, rfl⟩ s.params
        (#[], (argLocsC _).1) (by simp) hs.2 l
        (by simpa using hl)
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    have hs := argLocsC_small ((s.params.zip bytes).map fun q => (tyClass q.1.ty, q.2))
      (by simp; omega)
    rw [h] at hs
    exact hs

/-- **The argument locations of an integer signature are the x-register placement.**
`sigArgLocs` is `paramLocs` with the `sigArgs` sizes; on integer parameters the typed placement
(`argLocsC` of `.int` values) is `argLocs`. The right-hand side is the definition of
`sigArgLocs` before the typed ABI. -/
theorem sigArgLocs_eq {s : Clif.Signature} (hi : s.params.all (·.ty.isInt) = true) :
    sigArgLocs s = (do
    let bytes ← sigArgs s
    if s.params.any (·.purpose == .sret) then
      let normal := ((s.params.zip bytes).filter (!·.1.purpose == .sret)).map (·.2)
      let locs := (s.params.foldl sretLocStep (#[], (argLocs normal).1)).1
      if locs.size != s.params.length then throw "sigArgLocs: length"
      pure (locs.toList, (argLocs normal).2)
    else pure (argLocs bytes) : Except String (List ArgLoc × Nat)) := by
  unfold sigArgLocs
  cases hb : sigArgs s with
  | error e => rfl
  | ok bytes =>
    have hl := sigArgs_length hb
    simp only [List.all_eq_true] at hi
    have hz : ∀ L : List (Clif.AbiParam × Nat), (∀ q ∈ L, q ∈ s.params.zip bytes) →
        ∀ q ∈ L, q.1.ty.isInt = true := fun L hL q hq => hi q.1 (List.of_mem_zip (hL q hq)).1
    have e1 := map_tyClass_int (((s.params.zip bytes).filter (!·.1.purpose == .sret)))
      (hz _ fun q hq => (List.mem_filter.mp hq).1)
    have e2 := map_tyClass_int (s.params.zip bytes) (hz _ fun q hq => hq)
    rw [map_snd_zip _ _ (by omega)] at e2
    simp only [bind, Except.bind, paramLocs, e1, e2, argLocsC_int]

/-! ## Returns -/

theorem retRegsC_replicate_int : ∀ (n k nv : Nat), k ≤ 8 →
    retRegsC (List.replicate n .int) k nv =
      if k + n ≤ 8 then some ((List.range' k n).map Reg.x) else none
  | 0, k, nv, hk => by simp [retRegsC, hk]
  | n + 1, k, nv, hk => by
    simp only [List.replicate_succ, retRegsC]
    by_cases h : k < 8
    · rw [if_pos h, retRegsC_replicate_int n (k + 1) nv (by omega)]
      by_cases h' : k + 1 + n ≤ 8
      · rw [if_pos h', if_pos (by omega)]
        simp [List.range'_succ]
      · rw [if_neg h', if_neg (by omega)]; rfl
    · rw [if_neg h, if_neg (by omega)]

/-- **`retRegsC` of integer values is `retRegs`**: `n` integer returns go in x0..x(n-1), and
more than 8 fail. -/
theorem retRegsC_int (n : Nat) : retRegsC (List.replicate n .int) 0 0 = retRegs n := by
  rw [retRegsC_replicate_int n 0 0 (by omega)]
  simp [retRegs, List.range_eq_range']

/-- At most 8 values of each class fit their return registers. -/
theorem retRegsC_some : ∀ (cs : List RegClass) (nx nv : Nat), nx + cs.length ≤ 8 →
    nv + cs.length ≤ 8 → ∃ ps, retRegsC cs nx nv = some ps
  | [], _, _, _, _ => ⟨[], rfl⟩
  | .int :: cs, nx, nv, h1, h2 => by
    simp only [List.length_cons] at h1 h2
    obtain ⟨ps, hps⟩ := retRegsC_some cs (nx + 1) nv (by omega) (by omega)
    exact ⟨_, by rw [retRegsC, if_pos (by omega), hps]; rfl⟩
  | .float :: cs, nx, nv, h1, h2 => by
    simp only [List.length_cons] at h1 h2
    obtain ⟨ps, hps⟩ := retRegsC_some cs nx (nv + 1) (by omega) (by omega)
    exact ⟨_, by rw [retRegsC, if_pos (by omega), hps]; rfl⟩

theorem retClass_int {p : Clif.AbiParam} (h : p.ty.isInt = true) : retClass p = .int := by
  unfold retClass; split
  · rfl
  · exact tyClass_int h

/-- The ABI returns of a signature whose declared returns are integers are of class `.int`
(the `sret` struct pointer is `.int`, `retClass`). -/
theorem sigRets_classes_int {s : Clif.Signature} (h : s.returns.all (·.ty.isInt) = true) :
    (sigRets s).map retClass = List.replicate (sigRets s).length .int := by
  simp only [List.all_eq_true] at h
  apply List.eq_replicate_iff.mpr
  refine ⟨by simp, fun c hc => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  unfold sigRets at hp
  split at hp
  · rename_i q hq
    split at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      have := List.find?_some hq
      simp only [retClass, this, ↓reduceIte]
    · exact retClass_int (h p hp)
  · exact retClass_int (h p hp)

/-- **The typed return registers of an integer signature are the lowering's**: on a signature
whose ABI returns (`sigRets`) are all integers, `abiRetRegs` (x0..x7 for integers, v0..v7 for
floats) is `retRegs` of their count. -/
theorem abiRetRegs_int {s : Clif.Signature} (h : (sigRets s).all (·.ty.isInt) = true) :
    abiRetRegs s = retRegs (sigRets s).length := by
  unfold abiRetRegs
  have : (sigRets s).map retClass = List.replicate (sigRets s).length .int := by
    simp only [List.all_eq_true] at h
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, fun c hc => ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact retClass_int (h p hp)
  rw [this, retRegsC_int]

/-- `abiRetRegs_int` from the declared returns: integer declared returns (and an `sret`
struct pointer) return in x0..x(n-1). -/
theorem abiRetRegs_returns_int {s : Clif.Signature} (h : s.returns.all (·.ty.isInt) = true) :
    abiRetRegs s = retRegs (sigRets s).length := by
  unfold abiRetRegs
  rw [sigRets_classes_int h, retRegsC_int]

/-- The classes of returned integer vregs are `.int`, so `retRegsC` of them is `retRegs` of
their count. -/
theorem regsClasses_int {rss : List (List Reg)}
    (h : ∀ rs ∈ rss, ∃ n r, rs = .vreg n .int :: r) :
    retRegsC (regsClasses rss) 0 0 = retRegs rss.length := by
  have : regsClasses rss = List.replicate rss.length .int := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp [regsClasses], fun c hc => ?_⟩
    obtain ⟨rs, hrs, rfl⟩ := List.mem_map.mp hc
    obtain ⟨n, r, rfl⟩ := h rs hrs
    rfl
  rw [this, retRegsC_int]

/-- The classes of one-register returned values are their registers' classes. -/
theorem regsClasses_single (rs : List Reg) : regsClasses (rs.map fun r => [r]) = rs.map Reg.homeCls := by
  simp [regsClasses, Function.comp_def]

/-- Integer vregs return in x0..x(n-1) (`retRegs`). -/
theorem retRegsC_vreg_int (xs : List Nat) :
    retRegsC ((xs.map fun x => Reg.vreg x .int).map Reg.homeCls) 0 0 = retRegs xs.length := by
  rw [← retRegsC_int]; congr 1
  apply List.eq_replicate_iff.mpr
  simp [Reg.homeCls]

/-! ### The struct pointer of an `sret` function returned in x8 (`retX`, `retRegsK`) -/

theorem retX_lt {k j : Nat} (h : j < k) : retX k j = .x j := by simp [retX, h]

theorem retX_ge {k j : Nat} (h : k ≤ j) : retX k j = .x 8 := by
  simp [retX, Nat.not_lt.mpr h]

/-- With at least `n` declared returns, the first `n` ABI returns are in x0..x(n-1). -/
theorem map_retX_of_le {k n : Nat} (h : n ≤ k) :
    (List.range n).map (retX k) = (List.range n).map Reg.x :=
  List.map_congr_left fun _ hj => retX_lt (Nat.lt_of_lt_of_le (List.mem_range.mp hj) h)

/-- With `k ≤ n` return positions, `retX k` places the first `k` in x0.. and the rest in x8. -/
theorem map_retX_ge {k n : Nat} (h : k ≤ n) :
    (List.range n).map (retX k) =
      (List.range k).map Reg.x ++ List.replicate (n - k) (Reg.x 8) := by
  apply List.ext_getElem (by simp; omega)
  intro j hjn _
  simp only [List.length_map, List.length_range] at hjn
  rw [List.getElem_map, List.getElem_range]
  by_cases hj : j < k
  · simp [retX, hj, List.getElem_append, List.getElem_map, List.getElem_range]
  · have hjk : j - k < n - k := by omega
    simp [retX, hj, List.getElem_append, List.getElem_replicate, hjk]

/-- `n ≤ 8` integer values, the first `k` declared: x0.. for those, x8 after them. -/
theorem retRegsK_int (k n : Nat) (h : n ≤ 8) :
    retRegsK k (List.replicate n .int) = some ((List.range n).map (retX k)) := by
  unfold retRegsK
  rw [List.take_replicate, retRegsC_int, retRegs, if_pos (by omega)]
  simp only [Option.map_some, Option.some.injEq, List.length_replicate]
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range]
  by_cases hj : j < min k n
  · rw [List.getElem_append_left (by simpa using hj)]
    simp [retX_lt (show j < k by omega)]
  · rw [List.getElem_append_right (by simp; omega)]
    simp [retX_ge (show k ≤ j by simp at h2; omega)]

/-- With every value declared, `retRegsK` is `retRegsC`. -/
theorem retRegsK_of_le {k : Nat} {cs : List RegClass} (h : cs.length ≤ k) :
    retRegsK k cs = retRegsC cs 0 0 := by
  unfold retRegsK
  rw [List.take_of_length_le h, Nat.sub_eq_zero_of_le h]
  cases retRegsC cs 0 0 <;> simp

/-! ## Witnesses -/

/-- `(f64, i64, f32) → (f64, i64, f32)`. -/
def sigFIF : Clif.Signature :=
  { params := [⟨.f64, .none, .normal⟩, ⟨.i64, .none, .normal⟩, ⟨.f32, .none, .normal⟩]
    returns := [⟨.f64, .none, .normal⟩, ⟨.i64, .none, .normal⟩, ⟨.f32, .none, .normal⟩] }

/-- Floats and integers count separately: `(f64, i64, f32)` goes to `[v0, x0, v1]`. -/
theorem sigArgLocs_sigFIF :
    sigArgLocs sigFIF = .ok ([.reg (.v 0), .reg (.x 0), .reg (.v 1)], 0) := rfl

theorem abiRetRegs_sigFIF : abiRetRegs sigFIF = some [.v 0, .x 0, .v 1] := rfl

/-- Nine `f64`, an `i64`, an `f32`: v0..v7, the ninth `f64` on the stack, the `i64` in x0 (the
X counter is untouched by the floats), the `f32` in an 8-byte stack slot. -/
def sigSpill : Clif.Signature :=
  { params := List.replicate 9 ⟨.f64, .none, .normal⟩ ++
      [⟨.i64, .none, .normal⟩, ⟨.f32, .none, .normal⟩] }

theorem sigArgLocs_sigSpill :
    sigArgLocs sigSpill = .ok ((List.range 8).map (fun n => .reg (.v n)) ++
      [.stack 0, .reg (.x 0), .stack 8], 16) := rfl

/-- An `sret` pointer in x8 takes neither counter: `(sret i64, f64, i32)` goes to
`[x8, v0, x0]`, and the struct pointer is the only (integer) return. -/
def sigSret : Clif.Signature :=
  { params := [⟨.i64, .none, .sret⟩, ⟨.f64, .none, .normal⟩, ⟨.i32, .none, .normal⟩] }

theorem sigArgLocs_sigSret :
    sigArgLocs sigSret = .ok ([.reg (.x 8), .reg (.v 0), .reg (.x 0)], 0) := rfl

theorem abiRetRegs_sigSret : abiRetRegs sigSret = some [.x 0] := rfl

/-- The struct pointer an `sret` function returns is in x8: `gen_return` places the one ABI
return after no declared return there (`retRegsK`). -/
theorem retRegsK_sigSret : retRegsK sigSret.returns.length [.int] = some [.x 8] := rfl

/-- Nine `f32` returns do not fit v0..v7. -/
theorem abiRetRegs_nineFloats :
    abiRetRegs { returns := List.replicate 9 ⟨.f32, .none, .normal⟩ } = none := rfl

/-- An integer signature `(i64, sret i64, i8 × 8) → ()`: its hypotheses hold, and both sides of
`sigArgLocs_eq` are x0..x7 with x8 for the `sret` pointer and the ninth integer on the
stack. -/
def sigInt : Clif.Signature :=
  { params := ⟨.i64, .none, .normal⟩ :: ⟨.i64, .none, .sret⟩ :: List.replicate 8 ⟨.i8, .none, .normal⟩ }

theorem sigInt_int : sigInt.params.all (·.ty.isInt) = true := rfl

theorem sigInt_rets_int : (sigRets sigInt).all (·.ty.isInt) = true := rfl

theorem sigArgLocs_sigInt :
    sigArgLocs sigInt = .ok (.reg (.x 0) :: .reg (.x 8) ::
      ((List.range' 1 7).map (fun n => .reg (.x n)) ++ [.stack 0]), 16) := by
  rw [sigArgLocs_eq sigInt_int]; rfl

theorem abiRetRegs_sigInt : abiRetRegs sigInt = retRegs 1 := abiRetRegs_int sigInt_rets_int

theorem argLocsC_int_witness :
    argLocsC ((List.replicate 9 8).map fun b => (RegClass.int, b)) =
      ((List.range 8).map (fun n => .reg (.x n)) ++ [.stack 0], 16) := by
  rw [argLocsC_int]; rfl

theorem retRegsC_int_witness : retRegsC (List.replicate 9 .int) 0 0 = none ∧
    retRegsC (List.replicate 2 .int) 0 0 = some [.x 0, .x 1] :=
  ⟨by rw [retRegsC_int]; rfl, by rw [retRegsC_int]; rfl⟩

end Backend.Proof
