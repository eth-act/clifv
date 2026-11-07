import FV.Backend.Proof.IselCtlTerm

/-!
# Family Ctl: the `call` rules

`CallRuleOk` for `rule_lower_2508` (colocated callee: `bl name`, rule id 1031) and
`rule_lower_2518` (callee through the GOT: `loadExtNameGot t name; blr t`, rule id 1032), under
the callee contract `CallsRefine` and `CallRegArgs f` (at most 8 register arguments).
This file: the extern/ABI lemmas. With at most 8 parameters every argument is in a register:
`x (abiArgIdx …)` (x0.. in order, an `sret` parameter in x8, `sigArgLocs_regs`); the call
defines one register per declared return (`s.returns`: an `sret` callee's struct pointer, its
extra ABI return `sigRets`, gets none, as in Cranelift's `gen_call_output`).
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

/-- Fresh vregs of the classes `cs`, in order. -/
def freshC : LState → List RegClass → LState
  | st, [] => st
  | st, c :: cs => freshC (st.fresh c).2 cs

/-- The output registers `gen_call_output` allocates from `st` for returns of the classes `cs`:
one fresh vreg per return, of its class. -/
def outRegsC (st : LState) (cs : List RegClass) : List (List Reg) :=
  cs.zipIdx.map fun q => [Reg.vreg (st.nextVreg + q.2) q.1]

theorem freshC_nextVreg : ∀ (st : LState) (cs : List RegClass),
    (freshC st cs).nextVreg = st.nextVreg + cs.length
  | st, [] => rfl
  | st, c :: cs => by
    rw [freshC, freshC_nextVreg]; simp [LState.fresh]; omega

theorem freshC_emitted : ∀ (st : LState) (cs : List RegClass), (freshC st cs).emitted = st.emitted
  | st, [] => rfl
  | st, c :: cs => by rw [freshC, freshC_emitted]; rfl

theorem outRegsC_length (st : LState) (cs : List RegClass) : (outRegsC st cs).length = cs.length := by
  simp [outRegsC]

theorem zipIdx_succ_map {β : Type} (cs : List β) (k : Nat) :
    cs.zipIdx (k + 1) = (cs.zipIdx k).map fun q => (q.1, q.2 + 1) := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih => simp [List.zipIdx_cons, ih]

/-- `outRegsC` from the state after one fresh vreg. -/
theorem outRegsC_cons (st : LState) (c : RegClass) (cs : List RegClass) :
    outRegsC st (c :: cs) = [Reg.vreg st.nextVreg c] :: outRegsC (st.fresh c).2 cs := by
  simp only [outRegsC, List.zipIdx_cons, List.map_cons, Nat.add_zero, zipIdx_succ_map,
    List.map_map, Function.comp_def, LState.fresh]
  congr 2
  funext q
  congr 2
  omega

/-- `gen_call_output`'s fold: one fresh vreg per return, of its class. -/
theorem foldl_freshC (g : Clif.AbiParam → RegClass) (L : List Clif.AbiParam) :
    ∀ (acc : Array (List Reg)) (st : LState),
    L.foldl (fun (p : Array (List Reg) × LState) (q : Clif.AbiParam) =>
      (p.1.push [(p.2.fresh (g q)).1], (p.2.fresh (g q)).2)) (acc, st) =
      (acc ++ (outRegsC st (L.map g)).toArray, freshC st (L.map g)) := by
  induction L with
  | nil => intro acc st; simp [outRegsC, freshC]
  | cons a L ih =>
    intro acc st
    rw [List.foldl_cons, ih, List.map_cons, outRegsC_cons]
    simp [freshC, LState.fresh]

/-- Integer classes: `outRegsC`/`freshC` are `outRegs`/`freshN`. -/
theorem outRegsC_replicate (st : LState) (n : Nat) :
    outRegsC st (List.replicate n .int) = outRegs st n := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, outRegsC_cons, ih]
    simp only [outRegs, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
      LState.fresh, Nat.add_zero]
    congr 2
    funext j
    congr 2
    omega

theorem freshC_replicate (st : LState) (n : Nat) :
    freshC st (List.replicate n .int) = freshN st n := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, freshC, ih, freshN]

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
  | .stack off => (p.1, p.2.emit (stackArgStore q.1.2 q.2 (.spOffset off)))

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
  sigArgs_length h

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

/-- **Argument locations** of an integer signature with at most 8 parameters: all in
registers, parameter `i` in `x (abiArgIdx s.params 0)[i]` (x0.. in order, an `sret` parameter
in x8), no stack. -/
theorem sigArgLocs_regs {s : Clif.Signature} {bytes : List Nat}
    (hi : s.params.all (·.ty.isInt) = true)
    (hb : sigParamBytes s = .ok bytes) (h8 : bytes.length ≤ 8) :
    sigArgLocs s = .ok ((abiArgIdx s.params 0).map fun n => ArgLoc.reg (.x n), 0) := by
  have hb' : sigArgs s = .ok bytes := hb
  have hl := sigParamBytes_length hb
  simp only [sigArgLocs_eq hi, hb', bind, Except.bind]
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

/-- **`gen_call_output`** (typed, S11e5a): one fresh vreg per declared return, of its class
(`retClass`). -/
theorem ctor_gen_call_output_typed (st : LState) (s : Clif.Signature) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_output [.op (.sig s)] st = .ok (v, st') ↔
      v = .regsVec (outRegsC st (s.returns.map retClass)) ∧
        st' = freshC st (s.returns.map retClass) := by
  have : externCtor ctx T.gen_call_output [.op (.sig s)] st =
      (let r := s.returns.foldl (fun (p : Array (List Reg) × LState) (q : Clif.AbiParam) =>
          (p.1.push [(p.2.fresh (retClass q)).1], (p.2.fresh (retClass q)).2)) (#[], st)
       .ok (.regsVec r.1.toList, r.2)) := rfl
  rw [this, foldl_freshC]
  simp [eq_comm]

/-- Integer ABI returns (`sigRets`) make integer declared returns. -/
theorem returnsInt_of_sigRets {s : Clif.Signature}
    (h : (sigRets s).map retClass = List.replicate (sigRets s).length .int) :
    s.returns.map retClass = List.replicate s.returns.length .int := by
  rcases sigRets_cases s with h' | ⟨h', -⟩
  · rwa [h'] at h
  · simp [h']

/-- `gen_call_output` of a signature whose ABI returns are integers: fresh integer vregs, one
per declared return. -/
theorem ctor_gen_call_output_iff (st : LState) (s : Clif.Signature)
    (hr : (sigRets s).map retClass = List.replicate (sigRets s).length .int) (v : V)
    (st' : LState) :
    externCtor ctx T.gen_call_output [.op (.sig s)] st = .ok (v, st') ↔
      v = .regsVec (outRegs st s.returns.length) ∧ st' = freshN st s.returns.length := by
  rw [ctor_gen_call_output_typed, returnsInt_of_sigRets hr, outRegsC_replicate,
    freshC_replicate]

/-- The register pairs of `gen_call_args` for register locations. -/
theorem zip_regLocs : ∀ (locs : List ArgLoc) (rs : List Reg) (bytes : List Nat),
    locs.length ≤ bytes.length →
    ((locs.zip rs).zip bytes).map (fun q => (q.1.2, argLocReg q.1.1)) =
      rs.zip (locs.map argLocReg)
  | [], rs, bytes, _ => by simp
  | _ :: _, [], bytes, _ => by simp
  | _ :: _, _ :: _, [], h => by simp at h
  | l :: L, r :: rs, b :: bytes, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    simp only [List.map_cons, List.zip_cons_cons]
    rw [zip_regLocs L rs bytes h]

theorem zip_regLocs_all {locs : List ArgLoc} (hr : ∀ l ∈ locs, ∃ r, l = .reg r)
    (rs : List Reg) (bytes : List Nat) :
    ∀ q ∈ (locs.zip rs).zip bytes, ∃ pr, q.1.1 = .reg pr := by
  intro q hq
  exact hr _ (List.of_mem_zip (List.of_mem_zip hq).1).1

/-- `gen_call_args` of a signature with at most 8 parameters: every argument in its register
(`sigArgLocs_small`), no stack store. -/
theorem ctor_gen_call_args_small (st : LState) (s : Clif.Signature) (rss : List (List Reg))
    {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    (h8 : bytes.length ≤ 8) {locs : List ArgLoc} {S : Nat} (hl : sigArgLocs s = .ok (locs, S))
    (v : V) (st' : LState) :
    externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st = .ok (v, st') ↔
      ∃ rs, rss.mapM single? = some rs ∧
        v = .op (.callArgs (rs.zip (locs.map argLocReg))) ∧ st' = st := by
  have hr := (sigArgLocs_small hb h8 hl).2
  have : externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st =
      match sigArgLocs s, rss.mapM single? with
      | .ok (locs, _), some rs =>
        let bytes := match sigParamBytes s with | .ok b => b | _ => []
        let r := (((locs.zip rs).zip bytes).foldl argStep (#[], st))
        .ok (.op (.callArgs r.1.toList), r.2)
      | .error e, _ => .unmodeled s!"gen_call_args: {e}"
      | _, none => .unmodeled "gen_call_args: multi-register value" := rfl
  rw [this, hl, hb]
  cases hrs : rss.mapM single? with
  | none => simp
  | some rs =>
    have hlen : locs.length ≤ bytes.length := by
      rw [(sigArgLocs_shape hl).1, sigParamBytes_length hb]; exact Nat.le_refl _
    simp only []
    rw [foldl_argStep _ (zip_regLocs_all hr rs bytes), zip_regLocs _ rs bytes hlen]
    simp [eq_comm]

/-- `gen_call_args` of an integer signature with at most 8 parameters: the arguments in
`x (abiArgIdx …)` (x0.. in order, an `sret` pointer in x8). -/
theorem ctor_gen_call_args_iff (st : LState) (s : Clif.Signature) (rss : List (List Reg))
    (hi : s.params.all (·.ty.isInt) = true) {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    (h8 : bytes.length ≤ 8) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_args [.op (.sig s), .regsVec rss] st = .ok (v, st') ↔
      ∃ rs, rss.mapM single? = some rs ∧
        v = .op (.callArgs (rs.zip ((abiArgIdx s.params 0).map Reg.x))) ∧ st' = st := by
  rw [ctor_gen_call_args_small st s rss hb h8 (sigArgLocs_regs hi hb h8)]
  simp [List.map_map, Function.comp_def, argLocReg]

/-- **`gen_call_rets`** (typed, S11e5a): the outputs in the return registers of their classes
(`retRegsC`), at most 8. -/
theorem ctor_gen_call_rets_iff (st : LState) (s : Clif.Signature) (rss : List (List Reg)) (v : V)
    (st' : LState) :
    externCtor ctx T.gen_call_rets [.op (.sig s), .regsVec rss] st = .ok (v, st') ↔
      ∃ ps rs, rss.length ≤ 8 ∧ retRegsC (regsClasses rss) 0 0 = some ps ∧
        rss.mapM single? = some rs ∧
        v = .op (.callRets (ps.zip rs)) ∧ st' = st := by
  have : externCtor ctx T.gen_call_rets [.op (.sig s), .regsVec rss] st =
      if rss.length ≤ 8 then
        match retRegsC (regsClasses rss) 0 0, rss.mapM single? with
        | some ps, some rs => .ok (.op (.callRets (ps.zip rs)), st)
        | _, _ => .unmodeled "gen_call_rets: multi-register values"
      else .unmodeled "gen_call_rets: more than 8 return values" := rfl
  rw [this]
  by_cases h8 : rss.length ≤ 8
  · simp only [h8, ite_true, true_and]
    cases retRegsC (regsClasses rss) 0 0 <;> cases rss.mapM single? <;> simp [eq_comm]
  · simp [h8]

/-- The classes of integer output registers are integers: their return registers are
`retRegs`. -/
theorem retRegsC_outRegs (st : LState) (n : Nat) :
    retRegsC (regsClasses (outRegs st n)) 0 0 = retRegs n := by
  have : regsClasses (outRegs st n) = List.replicate n .int := by
    apply List.eq_replicate_iff.mpr
    simp [regsClasses, outRegs, Reg.homeCls]
  rw [this, retRegsC_int]

theorem retRegs_le {n : Nat} {ps : List Reg} (h : retRegs n = some ps) : n ≤ 8 := by
  unfold retRegs at h
  split at h
  · assumption
  · cases h

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

/-- With at most 8 parameters the argument locations compute, with no stack area. -/
theorem sigArgLocs_small_ok {s : Clif.Signature} {bytes : List Nat}
    (hb : sigParamBytes s = .ok bytes) (h8 : bytes.length ≤ 8) :
    ∃ locs, sigArgLocs s = .ok (locs, 0) := by
  obtain ⟨locs, n, hl⟩ := sigArgLocs_ok (s := s) hb
  obtain ⟨rfl, -⟩ := sigArgLocs_small hb h8 hl
  exact ⟨locs, hl⟩

theorem ctor_gen_call_info_iff (st : LState) (s : Clif.Signature) (n : String)
    (us ds : List (Reg × Reg)) (a b : V) {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    (h8 : bytes.length ≤ 8) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_info [.op (.sig s), .op (.extName n), .op (.callArgs us),
      .op (.callRets ds), a, b] st = .ok (v, st') ↔
      v = .op (.callInfo ⟨.sym n, us, ds⟩) ∧ st' = { st with outgoing := max st.outgoing 0 } := by
  obtain ⟨locs, hloc⟩ := sigArgLocs_small_ok hb h8
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
  obtain ⟨locs, hloc⟩ := sigArgLocs_small_ok hb h8
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

/-! ## Stack-passed arguments (agent/stack-tls-proof)

`gen_call_args` keeps the register-passed arguments as the call's fixed uses and emits one
`spOffset` store per stack-passed argument (in parameter order, before the call). -/

/-- The register pairs of `gen_call_args`' (location, register, byte size) triples. -/
def argRegPairs (L : List ((ArgLoc × Reg) × Nat)) : List (Reg × Reg) :=
  L.filterMap fun q => match q.1.1 with
    | .reg p => some (q.1.2, p)
    | .stack _ => none

/-- The stores `gen_call_args` emits for its triples. -/
def argStores (L : List ((ArgLoc × Reg) × Nat)) : List MInst :=
  L.filterMap fun q => match q.1.1 with
    | .stack off => some (stackArgStore q.1.2 q.2 (.spOffset off))
    | .reg _ => none

theorem foldl_argStep_gen : ∀ (L : List ((ArgLoc × Reg) × Nat)) (acc : Array (Reg × Reg))
    (st : LState),
    L.foldl argStep (acc, st) =
      (acc ++ (argRegPairs L).toArray, { st with emitted := st.emitted ++ (argStores L).toArray })
  | [], acc, st => by simp [argRegPairs, argStores]
  | ((.reg p, r), b) :: L, acc, st => by
    rw [List.foldl_cons, show argStep (acc, st) ((ArgLoc.reg p, r), b) = (acc.push (r, p), st) from rfl,
      foldl_argStep_gen L]
    simp [argRegPairs, argStores]
  | ((.stack off, r), b) :: L, acc, st => by
    rw [List.foldl_cons, show argStep (acc, st) ((ArgLoc.stack off, r), b) =
      (acc, st.emit (stackArgStore r b (.spOffset off))) from rfl,
      foldl_argStep_gen L]
    cases st
    simp [argRegPairs, argStores, LState.emit]

/-- The register-passed arguments of a call's (location, argument value, byte size) triples,
with their argument registers. -/
def regPairsOf (T : List ((ArgLoc × Nat) × Nat)) : List (Nat × Reg) :=
  T.filterMap fun q => match q.1.1 with
    | .reg p => some (q.1.2, p)
    | .stack _ => none

/-- The stack-passed arguments of a call's triples: (offset, argument value, byte size). -/
def stackEnts (T : List ((ArgLoc × Nat) × Nat)) : List (Nat × Nat × Nat) :=
  T.filterMap fun q => match q.1.1 with
    | .stack off => some (off, q.1.2, q.2)
    | .reg _ => none

/-- The store `gen_call_args` emits for a stack-passed argument (offset, value, byte size). -/
def argStore (e : Nat × Nat × Nat) : MInst :=
  .store (storeOpOfBytes e.2.2) (.vreg e.2.1 .int) (.spOffset e.1) trustedFlags

theorem zip3_map (g : Nat → Reg) : ∀ (locs : List ArgLoc) (args bytes : List Nat),
    (locs.zip (args.map g)).zip bytes = ((locs.zip args).zip bytes).map fun q => ((q.1.1, g q.1.2), q.2)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | _ :: _, _ :: _, [] => by simp
  | l :: locs, a :: args, b :: bytes => by simp [zip3_map g locs args bytes]

theorem argRegPairs_map : ∀ (T : List ((ArgLoc × Nat) × Nat)),
    argRegPairs (T.map fun q => ((q.1.1, Reg.vreg q.1.2 .int), q.2)) = retPairs (regPairsOf T)
  | [] => rfl
  | ((.reg p, x), b) :: T => by
    simp only [List.map_cons, argRegPairs, regPairsOf, List.filterMap_cons] at *
    rw [show retPairs ((x, p) :: _) = (Reg.vreg x .int, p) :: retPairs _ from rfl]
    congr 1
    exact argRegPairs_map T
  | ((.stack off, x), b) :: T => by
    simp only [List.map_cons, argRegPairs, regPairsOf, List.filterMap_cons] at *
    exact argRegPairs_map T

theorem argStores_map : ∀ (T : List ((ArgLoc × Nat) × Nat)),
    argStores (T.map fun q => ((q.1.1, Reg.vreg q.1.2 .int), q.2)) = (stackEnts T).map argStore
  | [] => rfl
  | ((.reg p, x), b) :: T => by
    simp only [List.map_cons, argStores, stackEnts, List.filterMap_cons] at *
    exact argStores_map T
  | ((.stack off, x), b) :: T => by
    simp only [List.map_cons, argStores, stackEnts, List.filterMap_cons, List.map_cons] at *
    rw [show argStore (off, x, b) = stackArgStore (.vreg x .int) b (.spOffset off) from rfl]
    congr 1
    exact argStores_map T

/-- **`gen_call_args`** (any number of parameters): the register-passed arguments become the
call's uses, every stack-passed one a store. -/
theorem ctor_gen_call_args_gen (st : LState) (s : Clif.Signature) (args : List Nat)
    {bytes : List Nat} (hb : sigParamBytes s = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs s = .ok (locs, S)) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_args
      [.op (.sig s), .regsVec ((args.map fun a => Reg.vreg a .int).map fun r => [r])] st = .ok (v, st') ↔
      v = .op (.callArgs (retPairs (regPairsOf ((locs.zip args).zip bytes)))) ∧
        st' = { st with emitted := st.emitted ++
          ((stackEnts ((locs.zip args).zip bytes)).map argStore).toArray } := by
  have : externCtor ctx T.gen_call_args
      [.op (.sig s), .regsVec ((args.map fun a => Reg.vreg a .int).map fun r => [r])] st =
      match sigArgLocs s, ((args.map fun a => Reg.vreg a .int).map fun r => [r]).mapM single? with
      | .ok (locs, _), some rs =>
        let bytes := match sigParamBytes s with | .ok b => b | _ => []
        let r := (((locs.zip rs).zip bytes).foldl argStep (#[], st))
        .ok (.op (.callArgs r.1.toList), r.2)
      | .error e, _ => .unmodeled s!"gen_call_args: {e}"
      | _, none => .unmodeled "gen_call_args: multi-register value" := rfl
  rw [this, hl, hb, mapM_single_map]
  simp only []
  rw [foldl_argStep_gen, zip3_map, argRegPairs_map, argStores_map]
  simp [eq_comm]

theorem ctor_gen_call_info_gen (st : LState) (s : Clif.Signature) (n : String)
    (us ds : List (Reg × Reg)) (a b : V) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs s = .ok (locs, S)) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_info [.op (.sig s), .op (.extName n), .op (.callArgs us),
      .op (.callRets ds), a, b] st = .ok (v, st') ↔
      v = .op (.callInfo ⟨.sym n, us, ds⟩) ∧ st' = { st with outgoing := max st.outgoing S } := by
  have : externCtor ctx T.gen_call_info [.op (.sig s), .op (.extName n), .op (.callArgs us),
      .op (.callRets ds), a, b] st = match sigArgLocs s with
      | .ok (_, stack) => .ok (.op (.callInfo ⟨.sym n, us, ds⟩),
          { st with outgoing := max st.outgoing stack })
      | .error e => .unmodeled s!"gen_call_info: {e}" := rfl
  rw [this, hl]; simp [eq_comm]

theorem ctor_gen_call_ind_info_gen (st : LState) (s : Clif.Signature) (r : Reg)
    (us ds : List (Reg × Reg)) (a : V) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs s = .ok (locs, S)) (v : V) (st' : LState) :
    externCtor ctx T.gen_call_ind_info [.op (.sig s), .reg r, .op (.callArgs us),
      .op (.callRets ds), a] st = .ok (v, st') ↔
      v = .op (.callInfo ⟨.reg r, us, ds⟩) ∧ st' = { st with outgoing := max st.outgoing S } := by
  have : externCtor ctx T.gen_call_ind_info [.op (.sig s), .reg r, .op (.callArgs us),
      .op (.callRets ds), a] st = match sigArgLocs s with
      | .ok (_, stack) => .ok (.op (.callInfo ⟨.reg r, us, ds⟩),
          { st with outgoing := max st.outgoing stack })
      | .error e => .unmodeled s!"gen_call_ind_info: {e}" := rfl
  rw [this, hl]; simp [eq_comm]

/-! ### Specialisation: at most 8 parameters -/

/-- With at most 8 parameters every argument location is a register (of its class). -/
theorem locsOf_small {s : Clif.Signature} {bytes : List Nat}
    (hb : sigParamBytes s = .ok bytes) (h8 : bytes.length ≤ 8) :
    (locsOf s).length = s.params.length ∧ ∀ l ∈ locsOf s, ∃ r, l = .reg r := by
  obtain ⟨locs, hl⟩ := sigArgLocs_small_ok hb h8
  simp only [locsOf, hl]
  exact ⟨(sigArgLocs_shape hl).1, (sigArgLocs_small hb h8 hl).2⟩

theorem locsOf_of_regs {s : Clif.Signature} {bytes : List Nat}
    (hi : s.params.all (·.ty.isInt) = true)
    (hb : sigParamBytes s = .ok bytes) (h8 : bytes.length ≤ 8) :
    locsOf s = (abiArgIdx s.params 0).map fun n => ArgLoc.reg (.x n) := by
  simp [locsOf, sigArgLocs_regs hi hb h8]

theorem regArgVals_of_regs {s : Clif.Signature} {bytes : List Nat}
    (hb : sigParamBytes s = .ok bytes) (h8 : bytes.length ≤ 8) {vals : List Clif.Val}
    (hl : vals.length = s.params.length) : regArgVals s vals = vals := by
  rw [regArgVals]
  obtain ⟨hlen, hr⟩ := locsOf_small hb h8
  rw [← hl] at hlen
  clear hl
  generalize locsOf s = L at hlen hr
  induction L generalizing vals with
  | nil =>
    cases vals with
    | nil => rfl
    | cons => simp at hlen
  | cons l L ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vals =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨r, rfl⟩ := hr l (by simp)
      simp [ih hlen (fun l' hl' => hr l' (by simp [hl']))]

theorem stackArgsAt_of_regs {s : Clif.Signature} {bytes : List Nat}
    (hb : sigParamBytes s = .ok bytes) (h8 : bytes.length ≤ 8) (vals : List Clif.Val)
    (w : Arm.ArmState) : StackArgsAt s vals w := by
  intro off v hm
  obtain ⟨r, hr⟩ := (locsOf_small hb h8).2 _ (List.of_mem_zip hm).1
  cases hr

/-- **Specialisation**: with at most 8 parameters every argument of a call is in a register,
and `ArgsAt` is the former premise (`AllHold`, one value per parameter). -/
theorem argsAt_iff_of_regs {s : Clif.Signature} {bytes : List Nat}
    (hb : sigParamBytes s = .ok bytes) (h8 : bytes.length ≤ 8) {vals : List Clif.Val}
    {args : List CV} {w : Arm.ArmState} (hl : vals.length = s.params.length) :
    ArgsAt s vals args w ↔ AllHold vals args := by
  simp only [ArgsAt, regArgVals_of_regs hb h8 hl, hl, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, stackArgsAt_of_regs hb h8 vals w⟩⟩

end

end Backend.Proof
