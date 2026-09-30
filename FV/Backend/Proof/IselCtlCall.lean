import FV.Backend.Proof.IselCtlTerm

/-!
# Family Ctl: the `call` rules

`CallRuleOk` for `rule_lower_2508` (colocated callee: `bl name`, rule id 1031) and
`rule_lower_2518` (callee through the GOT: `loadExtNameGot t name; blr t`, rule id 1032), under
the callee contract `CallsRefine` and `CallRegArgs f` (at most 8 register arguments).
This file: the extern/ABI lemmas. With at most 8 parameters every argument is in a register:
`x (abiArgIdx …)` (x0.. in order, an `sret` parameter in x8, `sigArgLocs_regs`); the call
defines one register per ABI return (`sigRets`: an `sret` signature without returns returns its
struct pointer, `sigRets_cases`).
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
def argLocReg : ArgLoc → Reg
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
    L.foldl argStep (acc, st) = (acc ++ (L.map fun q => (q.1.2, argLocReg q.1.1)).toArray, st)
  | [], _, acc, st => by simp
  | q :: L, hL, acc, st => by
    obtain ⟨pr, hq⟩ := hL q (by simp)
    rw [List.foldl_cons]
    have : argStep (acc, st) q = (acc.push (q.1.2, pr), st) := by simp [argStep, hq]
    rw [this, foldl_argStep L (fun q' h => hL q' (by simp [h]))]
    simp [hq, argLocReg]

theorem mapM_except_length {α β ε : Type} (g : α → Except ε β) :
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
        simp [mapM_except_length g hl]

theorem sigParamBytes_length {s : Clif.Signature} {bytes : List Nat}
    (h : sigParamBytes s = .ok bytes) : bytes.length = s.params.length :=
  mapM_except_length _ h

/-- The non-`sret` byte sizes (`sigArgLocs`' `normal`) are as many as the non-`sret` parameters. -/
theorem normal_length : ∀ (ps : List Clif.AbiParam) (bs : List Nat), bs.length = ps.length →
    (((ps.zip bs).filter (fun q => !(q.1.purpose == .sret))).map (·.2)).length =
      (ps.filter (fun p => !(p.purpose == .sret))).length
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | p :: ps, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := normal_length ps bs h
    simp only [List.length_map] at ih
    simp only [List.zip_cons_cons, List.filter_cons, List.length_map]
    split <;> simp [ih]

/-- `sigArgLocs`' placement of an `sret` signature's parameters, from the register locations of
the non-`sret` ones: `x (abiArgIdx …)`. -/
theorem foldl_sretLocStep : ∀ (ps : List Clif.AbiParam) (acc : Array ArgLoc) (k : Nat),
    ps.foldl sretLocStep (acc, (List.range' k (ps.filter (fun p => !(p.purpose == .sret))).length).map
        fun i => ArgLoc.reg (.x i)) =
      (acc ++ ((abiArgIdx ps k).map fun n => ArgLoc.reg (.x n)).toArray, [])
  | [], acc, k => by simp [abiArgIdx]
  | p :: ps, acc, k => by
    by_cases hp : (p.purpose == .sret) = true
    · have h1 : sretLocStep (acc, (List.range' k ((p :: ps).filter
          (fun p => !(p.purpose == .sret))).length).map fun i => ArgLoc.reg (.x i)) p =
          (acc.push (.reg (.x 8)), (List.range' k (ps.filter
            (fun p => !(p.purpose == .sret))).length).map fun i => ArgLoc.reg (.x i)) := by
        simp [sretLocStep, hp]
      rw [List.foldl_cons, h1, foldl_sretLocStep ps _ k]
      simp [abiArgIdx, hp]
    · have hp' : (p.purpose == .sret) = false := by simpa using hp
      have h1 : sretLocStep (acc, (List.range' k ((p :: ps).filter
          (fun p => !(p.purpose == .sret))).length).map fun i => ArgLoc.reg (.x i)) p =
          (acc.push (.reg (.x k)), (List.range' (k + 1) (ps.filter
            (fun p => !(p.purpose == .sret))).length).map fun i => ArgLoc.reg (.x i)) := by
        simp [sretLocStep, hp', List.range'_succ]
      rw [List.foldl_cons, h1, foldl_sretLocStep ps _ (k + 1)]
      simp [abiArgIdx, hp']

/-- **Argument locations** of a signature with at most 8 parameters: all in registers, parameter
`i` in `x (abiArgIdx s.params 0)[i]` (x0.. in order, an `sret` parameter in x8), no stack. -/
theorem sigArgLocs_regs {s : Clif.Signature} {bytes : List Nat}
    (hb : sigParamBytes s = .ok bytes) (h8 : bytes.length ≤ 8) :
    sigArgLocs s = .ok ((abiArgIdx s.params 0).map fun n => ArgLoc.reg (.x n), 0) := by
  have hb' : sigArgs s = .ok bytes := hb
  have hl := sigParamBytes_length hb
  simp only [sigArgLocs, hb', bind, Except.bind]
  cases hany : s.params.any (·.purpose == .sret) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, argLocs_eq h8, abiArgIdx_of_noSret _ 0 hany, hl,
      List.range_eq_range']
    simp [pure, Except.pure]
  | true =>
    have hnl := normal_length s.params bytes hl
    have hn8 : (((s.params.zip bytes).filter (fun q => !(q.1.purpose == .sret))).map (·.2)).length ≤ 8 := by
      rw [hnl]; exact Nat.le_trans (List.length_filter_le _ _) (hl ▸ h8)
    simp only [↓reduceIte, argLocs_eq hn8, hnl, List.range_eq_range']
    rw [foldl_sretLocStep s.params #[] 0]
    simp [abiArgIdx_length, pure, Except.pure]

section
variable {ctx : Ctx}

/-- `sigRets` is the declared returns, or (an `sret` signature without returns) one value. -/
theorem sigRets_cases (s : Clif.Signature) :
    sigRets s = s.returns ∨ (s.returns = [] ∧ (sigRets s).length = 1) := by
  unfold sigRets
  cases s.params.find? (·.purpose == .sret) with
  | none => exact .inl rfl
  | some p =>
    cases hr : s.returns with
    | nil => exact .inr ⟨rfl, rfl⟩
    | cons a l => exact .inl rfl

theorem ctor_gen_call_output_iff (st : LState) (s : Clif.Signature) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_output [.op (.sig s)] st = .ok (v, st') ↔
      v = .regsVec (outRegs st (sigRets s).length) ∧ st' = freshN st (sigRets s).length := by
  have : externCtor ctx T.gen_call_output [.op (.sig s)] st =
      (let r := (sigRets s).foldl (fun (p : Array (List Reg) × LState) (_ : Clif.AbiParam) =>
          (p.1.push [(p.2.fresh .int).1], (p.2.fresh .int).2)) (#[], st)
       .ok (.regsVec r.1.toList, r.2)) := rfl
  rw [this, foldl_fresh]
  simp [eq_comm]

/-- The register pairs of `gen_call_args` for register locations `L`. -/
theorem zip_regLocs : ∀ (L : List Nat) (rs : List Reg) (bytes : List Nat), bytes.length = L.length →
    (((L.map fun n => ArgLoc.reg (.x n)).zip rs).zip bytes).map
      (fun q => (q.1.2, argLocReg q.1.1)) = rs.zip (L.map Reg.x)
  | [], rs, bytes, _ => by simp
  | _ :: _, [], bytes, _ => by simp
  | _ :: _, _ :: _, [], h => by simp at h
  | n :: L, r :: rs, b :: bytes, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.map_cons, List.zip_cons_cons]
    rw [zip_regLocs L rs bytes h]
    rfl

theorem zip_regLocs_all (L : List Nat) (rs : List Reg) (bytes : List Nat) :
    ∀ q ∈ ((L.map fun n => ArgLoc.reg (.x n)).zip rs).zip bytes, ∃ pr, q.1.1 = .reg pr := by
  intro q hq
  have := List.of_mem_zip hq
  have := List.of_mem_zip this.1
  obtain ⟨i, -, h⟩ := List.mem_map.mp this.1
  exact ⟨_, h.symm⟩

theorem ctor_gen_call_args_iff (st : LState) (s : Clif.Signature) (rss : List (List Reg))
    {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    (h8 : bytes.length ≤ 8) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st = .ok (v, st') ↔
      ∃ rs, rss.mapM single? = some rs ∧
        v = .op (.callArgs (rs.zip ((abiArgIdx s.params 0).map Reg.x))) ∧ st' = st := by
  have hloc := sigArgLocs_regs hb h8
  have : externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st =
      match sigArgLocs s, rss.mapM single? with
      | .ok (locs, _), some rs =>
        let bytes := match sigParamBytes s with | .ok b => b | _ => []
        let r := (((locs.zip rs).zip bytes).foldl argStep (#[], st))
        .ok (.op (.callArgs r.1.toList), r.2)
      | .error e, _ => .unmodeled s!"gen_call_args: {e}"
      | _, none => .unmodeled "gen_call_args: multi-register value" := rfl
  rw [this, hloc, hb]
  cases hrs : rss.mapM single? with
  | none => simp
  | some rs =>
    have hlen : bytes.length = (abiArgIdx s.params 0).length := by
      rw [abiArgIdx_length, sigParamBytes_length hb]
    simp only []
    rw [foldl_argStep _ (zip_regLocs_all _ rs bytes), zip_regLocs _ rs bytes hlen]
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
    (h8 : bytes.length ≤ 8) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_info [.op (.sig s), .op (.extName n), .op (.callArgs us),
      .op (.callRets ds), a, b] st = .ok (v, st') ↔
      v = .op (.callInfo ⟨.sym n, us, ds⟩) ∧ st' = { st with outgoing := max st.outgoing 0 } := by
  have hloc := sigArgLocs_regs hb h8
  have : externCtor ctx T.gen_call_info [.op (.sig s), .op (.extName n), .op (.callArgs us),
      .op (.callRets ds), a, b] st = match sigArgLocs s with
      | .ok (_, stack) => .ok (.op (.callInfo ⟨.sym n, us, ds⟩),
          { st with outgoing := max st.outgoing stack })
      | .error e => .unmodeled s!"gen_call_info: {e}" := rfl
  rw [this, hloc]; simp [eq_comm]

theorem ctor_gen_call_ind_info_iff (st : LState) (s : Clif.Signature) (r : Reg)
    (us ds : List (Reg × Reg)) (a : V) {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    (h8 : bytes.length ≤ 8) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_ind_info [.op (.sig s), .reg r, .op (.callArgs us),
      .op (.callRets ds), a] st = .ok (v, st') ↔
      v = .op (.callInfo ⟨.reg r, us, ds⟩) ∧ st' = { st with outgoing := max st.outgoing 0 } := by
  have hloc := sigArgLocs_regs hb h8
  have : externCtor ctx T.gen_call_ind_info [.op (.sig s), .reg r, .op (.callArgs us),
      .op (.callRets ds), a] st = match sigArgLocs s with
      | .ok (_, stack) => .ok (.op (.callInfo ⟨.reg r, us, ds⟩),
          { st with outgoing := max st.outgoing stack })
      | .error e => .unmodeled s!"gen_call_ind_info: {e}" := rfl
  rw [this, hloc]; simp [eq_comm]

theorem ctor_is_pic_iff (st : LState) (v : V) (st' : LState) :
    externCtor ctx T.is_pic [] st = .ok (v, st') ↔ v = .bool true ∧ st' = st := by
  have : externCtor ctx T.is_pic [] st = .ok (.bool true, st) := rfl
  rw [this]; simp [eq_comm]

end

end Backend.Proof
