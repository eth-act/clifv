import FV.Backend.Proof.IselCtlTerm

/-!
# Family Ctl: the `call` rules

`CallRuleOk` for `rule_lower_2508` (colocated callee: `bl name`, rule id 1031) and
`rule_lower_2518` (callee through the GOT: `loadExtNameGot t name; blr t`, rule id 1032), under
the callee contract `CallsRefine` and `CallRegArgs f` (at most 8 register arguments).
Status: extern/ABI lemmas proven (this file); the two rule theorems are not written yet.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Extern helpers -/

section
variable {ctx : Ctx}

theorem ext_func_ref_data_iff (st : LState) (fn : Nat) (fs : List V) :
    externExtract ctx T.func_ref_data (.op (.funcRef fn)) st = .ok fs ↔
      ∃ ext, ctx.func.extern? fn = some ext ∧
        fs = [.op (.sig ext.sig), .op (.extName ext.name),
          .data tyRelocDistance (if ext.colocated then 0 else 1) [], .bool false] := by
  have : externExtract ctx T.func_ref_data (.op (.funcRef fn)) st =
      match ctx.func.extern? fn with
      | some ext => .ok [.op (.sig ext.sig), .op (.extName ext.name),
          .data tyRelocDistance (if ext.colocated then 0 else 1) [], .bool false]
      | none => .unmodeled s!"fn{fn}" := rfl
  rw [this]
  cases ctx.func.extern? fn with
  | none => simp only [reduceCtorEq, false_iff, not_exists, not_and]; intro _ h; cases h
  | some ext =>
    simp only [ExtResult.ok.injEq, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨ext, rfl, rfl⟩
    · rintro ⟨e, rfl, rfl⟩; rfl

theorem ctor_abi_sig_iff (st : LState) (s : V) (v : V) (st' : LState) :
    externCtor ctx T.abi_sig [s] st = .ok (v, st') ↔ v = s ∧ st' = st := by
  have : externCtor ctx T.abi_sig [s] st = .ok (s, st) := by
    cases s <;> first | rfl | (rename_i t; cases t <;> rfl)
  rw [this]; simp [eq_comm]

end

/-! ## ABI helpers: `gen_call_output`, `argLocs`, `gen_call_args`, `gen_call_rets`, `gen_call_info` -/

/-- `n` fresh integer vregs. -/
def freshN : LState → Nat → LState
  | st, 0 => st
  | st, n + 1 => freshN (st.fresh .int).2 n

/-- The output registers `gen_call_output` allocates from `st`: one fresh vreg per return. -/
def outRegs (st : LState) (n : Nat) : List (List Reg) :=
  (List.range n).map fun j => [Reg.vreg (st.nextVreg + j) .int]

theorem freshN_nextVreg : ∀ (st : LState) (n : Nat), (freshN st n).nextVreg = st.nextVreg + n
  | st, 0 => rfl
  | st, n + 1 => by
    rw [freshN, freshN_nextVreg]; simp [LState.fresh]; omega

theorem freshN_emitted : ∀ (st : LState) (n : Nat), (freshN st n).emitted = st.emitted
  | st, 0 => rfl
  | st, n + 1 => by rw [freshN, freshN_emitted]; rfl

theorem foldl_fresh {α : Type} (L : List α) : ∀ (acc : Array (List Reg)) (st : LState),
    L.foldl (fun (p : Array (List Reg) × LState) (_ : α) =>
      (p.1.push [(p.2.fresh .int).1], (p.2.fresh .int).2)) (acc, st) =
      (acc ++ (outRegs st L.length).toArray, freshN st L.length) := by
  induction L with
  | nil => intro acc st; simp [outRegs, freshN]
  | cons a L ih =>
    intro acc st
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, freshN, Prod.mk.injEq, and_true]
    simp [outRegs, LState.fresh, List.range_succ_eq_map, Function.comp_def, Nat.add_assoc,
      Nat.add_comm 1]

/-- With at most 8 arguments, every argument is in a register, `x0 … x(n-1)`. -/
theorem argLocs_small : ∀ (bytes : List Nat) (acc : Array ArgLoc) (nx st : Nat), nx + bytes.length ≤ 8 →
    bytes.foldl (fun (p : Array ArgLoc × Nat × Nat) (b : Nat) =>
      if p.2.1 < 8 then (p.1.push (.reg (.x p.2.1)), p.2.1 + 1, p.2.2)
      else (p.1.push (.stack (alignTo p.2.2 (max b 8))), p.2.1, alignTo p.2.2 (max b 8) + max b 8))
      (acc, nx, st) =
    (acc ++ ((List.range bytes.length).map fun i => ArgLoc.reg (.x (nx + i))).toArray,
      nx + bytes.length, st)
  | [], acc, nx, st, _ => by simp
  | b :: bytes, acc, nx, st, h => by
    simp only [List.length_cons] at h
    rw [List.foldl_cons]
    simp only [show nx < 8 from by omega, ↓reduceIte]
    rw [argLocs_small bytes _ _ _ (by omega)]
    simp only [List.length_cons, Prod.mk.injEq, and_true]
    refine ⟨?_, by omega⟩
    simp [List.range_succ_eq_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

theorem argLocs_eq {bytes : List Nat} (h : bytes.length ≤ 8) :
    argLocs bytes = ((List.range bytes.length).map fun i => ArgLoc.reg (.x i), 0) := by
  have := argLocs_small bytes #[] 0 0 (by omega)
  simp only [Nat.zero_add] at this
  unfold argLocs
  rw [show (bytes.foldl (fun (x : Array ArgLoc × Nat × Nat) (b : Nat) =>
      if x.2.1 < 8 then (x.1.push (.reg (.x x.2.1)), x.2.1 + 1, x.2.2)
      else (x.1.push (.stack (alignTo x.2.2 (max b 8))), x.2.1, alignTo x.2.2 (max b 8) + max b 8))
      (#[], 0, 0)) = _ from this]
  simp [alignTo]

/-- The register of a register location. -/
def locReg : ArgLoc → Reg
  | .reg r => r
  | .stack _ => .xzr

/-- The step of `gen_call_args`' fold (as in `externCtor`). -/
def argStep (p : Array (Reg × Reg) × LState) (q : (ArgLoc × Reg) × Nat) :
    Array (Reg × Reg) × LState :=
  match q.1.1 with
  | .reg pr => (p.1.push (q.1.2, pr), p.2)
  | .stack off => (p.1, p.2.emit (.store (storeOpOfBytes q.2) q.1.2 (.spOffset off) trustedFlags))

theorem foldl_argStep : ∀ (L : List ((ArgLoc × Reg) × Nat)), (∀ q ∈ L, ∃ pr, q.1.1 = .reg pr) →
    ∀ (acc : Array (Reg × Reg)) (st : LState),
    L.foldl argStep (acc, st) = (acc ++ (L.map fun q => (q.1.2, locReg q.1.1)).toArray, st)
  | [], _, acc, st => by simp
  | q :: L, hL, acc, st => by
    obtain ⟨pr, hq⟩ := hL q (by simp)
    rw [List.foldl_cons]
    have : argStep (acc, st) q = (acc.push (q.1.2, pr), st) := by simp [argStep, hq]
    rw [this, foldl_argStep L (fun q' h => hL q' (by simp [h]))]
    simp [hq, locReg]

theorem zip_argLocs : ∀ (bytes : List Nat) (rs : List Reg) (k : Nat),
    ((((List.range' k bytes.length).map fun i => ArgLoc.reg (.x i)).zip rs).zip bytes).map
      (fun q => (q.1.2, locReg q.1.1)) = rs.zip ((List.range' k bytes.length).map Reg.x)
  | [], rs, k => by simp
  | b :: bytes, [], k => by simp [List.range'_succ]
  | b :: bytes, r :: rs, k => by
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.zip_cons_cons]
    rw [zip_argLocs bytes rs (k + 1)]
    rfl

theorem zip_argLocs_all : ∀ (bytes : List Nat) (rs : List Reg) (k : Nat),
    ∀ q ∈ (((List.range' k bytes.length).map fun i => ArgLoc.reg (.x i)).zip rs).zip bytes,
      ∃ pr, q.1.1 = .reg pr := by
  intro bytes rs k q hq
  have := List.of_mem_zip hq
  have := List.of_mem_zip this.1
  obtain ⟨i, -, h⟩ := List.mem_map.mp this.1
  exact ⟨_, h.symm⟩

section
variable {ctx : Ctx}

theorem ctor_gen_call_output_iff (st : LState) (s : Clif.Signature) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_output [.op (.sig s)] st = .ok (v, st') ↔
      v = .regsVec (outRegs st s.returns.length) ∧ st' = freshN st s.returns.length := by
  have : externCtor ctx T.gen_call_output [.op (.sig s)] st =
      (let r := s.returns.foldl (fun (p : Array (List Reg) × LState) (_ : Clif.AbiParam) =>
          (p.1.push [(p.2.fresh .int).1], (p.2.fresh .int).2)) (#[], st)
       .ok (.regsVec r.1.toList, r.2)) := rfl
  rw [this, foldl_fresh]
  simp [eq_comm]

theorem ctor_gen_call_args_iff (st : LState) (s : Clif.Signature) (rss : List (List Reg))
    {bytes : List Nat} (hb : sigParamBytes s = .ok bytes) (h8 : bytes.length ≤ 8) (v : V)
    (st' : LState) :
    externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st = .ok (v, st') ↔
      ∃ rs, rss.mapM single? = some rs ∧
        v = .op (.callArgs (rs.zip ((List.range bytes.length).map Reg.x))) ∧ st' = st := by
  have : externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st =
      match sigParamBytes s, rss.mapM single? with
      | .ok bytes, some rs =>
        let r := ((((argLocs bytes).1.zip rs).zip bytes).foldl argStep (#[], st))
        .ok (.op (.callArgs r.1.toList), r.2)
      | .error e, _ => .unmodeled s!"gen_call_args: {e}"
      | _, none => .unmodeled "gen_call_args: multi-register value" := rfl
  rw [this, hb]
  cases hrs : rss.mapM single? with
  | none => simp
  | some rs =>
    simp only [argLocs_eq h8, List.range_eq_range']
    rw [foldl_argStep _ (zip_argLocs_all bytes rs 0), zip_argLocs]
    simp [eq_comm]

theorem ctor_gen_call_rets_iff (st : LState) (s : Clif.Signature) (rss : List (List Reg)) (v : V)
    (st' : LState) :
    externCtor ctx T.gen_call_rets [.op (.sig s), .regsVec rss] st = .ok (v, st') ↔
      ∃ ps rs, retRegs rss.length = some ps ∧ rss.mapM single? = some rs ∧
        v = .op (.callRets (ps.zip rs)) ∧ st' = st := by
  have : externCtor ctx T.gen_call_rets [.op (.sig s), .regsVec rss] st =
      match retRegs rss.length, rss.mapM single? with
      | some ps, some rs => .ok (.op (.callRets (ps.zip rs)), st)
      | _, _ => .unmodeled "gen_call_rets: more than 8 return values" := rfl
  rw [this]
  cases retRegs rss.length <;> cases rss.mapM single? <;> simp [eq_comm]

theorem ctor_try_call_none_iff (st : LState) (v : V) (st' : LState) :
    externCtor ctx T.try_call_none [] st = .ok (v, st') ↔ v = .op .tryCallNone ∧ st' = st := by
  have : externCtor ctx T.try_call_none [] st = .ok (.op .tryCallNone, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_output_vec_iff (st : LState) (rss : List (List Reg)) (v : V) (st' : LState) :
    externCtor ctx T.output_vec [.regsVec rss] st = .ok (v, st') ↔ v = .regsVec rss ∧ st' = st := by
  have : externCtor ctx T.output_vec [.regsVec rss] st = .ok (.regsVec rss, st) := rfl
  rw [this]; simp [eq_comm]

theorem ctor_box_external_name_iff (st : LState) (n : V) (v : V) (st' : LState) :
    externCtor ctx T.box_external_name [n] st = .ok (v, st') ↔ v = n ∧ st' = st := by
  have : externCtor ctx T.box_external_name [n] st = .ok (n, st) := by
    cases n <;> first | rfl | (rename_i t; cases t <;> rfl)
  rw [this]; simp [eq_comm]

theorem ctor_gen_call_info_iff (st : LState) (s : Clif.Signature) (n : String)
    (us ds : List (Reg × Reg)) (a b : V) {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    (v : V) (st' : LState) :
    externCtor ctx T.gen_call_info [.op (.sig s), .op (.extName n), .op (.callArgs us),
      .op (.callRets ds), a, b] st = .ok (v, st') ↔
      v = .op (.callInfo ⟨.sym n, us, ds⟩) ∧
        st' = { st with outgoing := max st.outgoing (argLocs bytes).2 } := by
  have : externCtor ctx T.gen_call_info [.op (.sig s), .op (.extName n), .op (.callArgs us),
      .op (.callRets ds), a, b] st = match sigParamBytes s with
      | .ok bytes => .ok (.op (.callInfo ⟨.sym n, us, ds⟩),
          { st with outgoing := max st.outgoing (argLocs bytes).2 })
      | .error e => .unmodeled s!"gen_call_info: {e}" := rfl
  rw [this, hb]; simp [eq_comm]

theorem ctor_gen_call_ind_info_iff (st : LState) (s : Clif.Signature) (r : Reg)
    (us ds : List (Reg × Reg)) (a : V) {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    (v : V) (st' : LState) :
    externCtor ctx T.gen_call_ind_info [.op (.sig s), .reg r, .op (.callArgs us),
      .op (.callRets ds), a] st = .ok (v, st') ↔
      v = .op (.callInfo ⟨.reg r, us, ds⟩) ∧
        st' = { st with outgoing := max st.outgoing (argLocs bytes).2 } := by
  have : externCtor ctx T.gen_call_ind_info [.op (.sig s), .reg r, .op (.callArgs us),
      .op (.callRets ds), a] st = match sigParamBytes s with
      | .ok bytes => .ok (.op (.callInfo ⟨.reg r, us, ds⟩),
          { st with outgoing := max st.outgoing (argLocs bytes).2 })
      | .error e => .unmodeled s!"gen_call_ind_info: {e}" := rfl
  rw [this, hb]; simp [eq_comm]

theorem ctor_is_pic_iff (st : LState) (v : V) (st' : LState) :
    externCtor ctx T.is_pic [] st = .ok (v, st') ↔ v = .bool true ∧ st' = st := by
  have : externCtor ctx T.is_pic [] st = .ok (.bool true, st) := rfl
  rw [this]; simp [eq_comm]

end

end Backend.Proof
