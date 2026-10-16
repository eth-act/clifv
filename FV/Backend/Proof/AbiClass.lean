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

/-- A float type is not an integer type. -/
theorem not_isFloat {t : Clif.Ty} (h : t.isInt = true) : ¬ t.isFloat = true := by
  show ¬ (!t.isInt) = true
  rw [h]; decide

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

/-- **The typed return registers of an integer signature are the lowering's**: on a signature
whose ABI returns (`sigRets`) are all integers, `abiRetRegs` (x0..x7 for integers, v0..v7 for
floats) is `retRegs` of their count. -/
theorem abiRetRegs_int {s : Clif.Signature} (h : (sigRets s).all (·.ty.isInt) = true) :
    abiRetRegs s = retRegs (sigRets s).length := by
  unfold abiRetRegs
  have : (sigRets s).map (tyClass ·.ty) = List.replicate (sigRets s).length .int := by
    simp only [List.all_eq_true] at h
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, fun c hc => ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact tyClass_int (h p hp)
  rw [this, retRegsC_int]

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
