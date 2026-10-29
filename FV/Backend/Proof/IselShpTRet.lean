import FV.Backend.Proof.IselTermFactsTy
import FV.Backend.Proof.IselShpTBase
import FV.Backend.Proof.IselShpCtor

/-!
# The `return` rule's control shape over typed contexts (#587)

Cranelift's `gen_return` returns an `sret` function's struct pointer in x8 (`machinst/abi.rs:902`,
`isa/aarch64/abi.rs:255-270` in cranelift-codegen 0.135.0), and so does ours (`retRegsK`), whatever
the class of the pointer's vreg: the `rets` meets `SpillInstOk` only because that vreg is an
integer one, which the entry block's typing gives (`EntryClassOk`, `sretRet_valClass_int`), not
the typed table's abstract values. So the typed table does not cover `gen_return` (`apreST`) and
the `return` rule (`rule_lower_2574`, id 1037) is checked by hand here:

* `ret_emitTy`: on a `return`, the rule appends one `rets` of the values' vregs at the registers
  `retRegsK` gives (`lower_return_okTy`); on a `trap` it never matches
  (`ret_rule_trap_nomatch`);
* `rets_ctlShapeT`: with an integer-classed struct pointer, that `rets` has the typed control shape
  `CtlShapeT` (declared returns in distinct x0..x7/v0..v7, `retRegsC_pairs`; the pointer in x8);
* `handOkT_ret`: the rule as a hand-checked root rule of `lower` (`HandOkT`).
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hp hc in
set_option maxHeartbeats 800000 in
/-- **`rule_lower_2574` on a `return`** appends one `rets`: the values' registers at the
registers `retRegsK` gives for their classes (`lower_return_okTy`). -/
theorem ret_emitTy {ti : Nat} {xs : List Nat} {data : V}
    (hd : termData (.ret xs) = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {m n : Nat} {st : LState} {tr : Array RuleId} {env' : Interp.Env V}
    {s1 : LState × Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2574 [.inst ti]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2574.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ∃ rs ps, xs.mapM ctx.valueReg? = some rs ∧
      retRegsK (rs.length - (sretRet ctx.func).length) (regsClasses (rs.map fun r => [r])) =
        some ps ∧
      st' = st.emit (.rets (rs.zip ps)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kR := fun n (hn : 60 ≤ n) xs s v s' h => lower_return_okTy hp (ctx := ctx) hc (n := n)
    (xs := xs) (s := s) (v := v) (s' := s') hn h
  rw [termData_ret] at hd; cases hd
  cases hp
  ctl_inv [*, rule_lower_2574] at hmatch heval
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_value_list_slice_iff] at * <;> isel_destruct <;> subst_vars)
  have h294 := ‹ApplyInternal _ _ _ _ 25 294 _ _ _ _›
  obtain ⟨rs, ps, hrs, hps, hs⟩ := kR _ (by omega) _ _ _ _ h294
  simp only at hs
  exact ⟨rs, ps, hrs, hps, hs.1⟩

include hp in
set_option maxHeartbeats 800000 in
/-- `rule_lower_2574` never matches a `trap`. -/
theorem ret_rule_trap_nomatch {ti : Nat} {c : Clif.TrapCode} {data : V}
    (hd : termData (.trap c) = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {m : Nat} {st : LState} {tr : Array RuleId} {env' : Interp.Env V}
    {s1 : LState × Array RuleId} (hm : 1000 ≤ m)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2574 [.inst ti]).run (st, tr) =
      .ok (some env', s1)) : False := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  rw [termData_trap] at hd; cases hd
  cases hp
  isel_inv [*, rule_lower_2574] at hmatch
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  simp at *

end

/-- The `return` rule's right-hand side always yields a value. -/
theorem totalE_ret : Cov.totalE program rule_lower_2574.rhs = true := by decide +kernel

private theorem mapM_valueReg_typed {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) :
    ∀ {xs : List Nat} {rs : List Reg}, xs.mapM ctx.valueReg? = some rs →
      rs = xs.map fun x => Reg.vreg x (valClassOf ctx x)
  | [], rs, h => by simp at h; simp [h]
  | x :: xs, rs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs, rfl⟩ := h
    rw [hctx.valueReg x r hr, mapM_valueReg_typed hctx hrs]
    rfl

private theorem retRegsC_len : ∀ (cs : List RegClass) (nx nv : Nat) {ps : List Reg},
    retRegsC cs nx nv = some ps → ps.length = cs.length
  | [], _, _, ps, h => by simp [retRegsC] at h; subst h; rfl
  | .int :: cs, nx, nv, ps, h => by
    simp only [retRegsC] at h
    split at h
    · obtain ⟨ps', h1, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [retRegsC_len cs _ _ h1]
    · cases h
  | .float :: cs, nx, nv, ps, h => by
    simp only [retRegsC] at h
    split at h
    · obtain ⟨ps', h1, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [retRegsC_len cs _ _ h1]
    · cases h

/-- Integer vregs paired with x8. -/
private theorem zip_x8 {ctx : Ctx} : ∀ {ys : List Nat}, (∀ y ∈ ys, valClassOf ctx y = .int) →
    (ys.map fun x => Reg.vreg x (valClassOf ctx x)).zip (List.replicate ys.length (Reg.x 8)) =
      argPairsC (ys.map fun y => (y, RegClass.int, Reg.x 8))
  | [], _ => rfl
  | y :: ys, h => by
    have hy := h y List.mem_cons_self
    have ih := zip_x8 (ys := ys) fun y' hy' => h y' (List.mem_cons_of_mem _ hy')
    simp only [List.map_cons, List.length_cons, List.replicate_succ, List.zip_cons_cons, hy]
    rw [ih]
    rfl

/-- **The `return` rule's `rets` has its typed control shape** when the appended values (an
`sret` function's struct pointer, at most one) have integer vregs: the declared returns at
distinct return registers of their classes, the pointer in x8. -/
theorem rets_ctlShapeT (N : Nat) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    {vs ys : List Nat} (hy1 : ys.length ≤ 1) (hsr : ∀ y ∈ ys, valClassOf ctx y = .int)
    {rs ps : List Reg} (hrs : (vs ++ ys).mapM ctx.valueReg? = some rs)
    (hps : retRegsK (rs.length - ys.length) (regsClasses (rs.map fun r => [r])) = some ps) :
    CtlShapeT N (.rets (rs.zip ps)) := by
  have hrs' := mapM_valueReg_typed hctx hrs
  subst hrs'
  have hcls : regsClasses (((vs ++ ys).map fun x => Reg.vreg x (valClassOf ctx x)).map
      fun r => [r]) = vs.map (valClassOf ctx) ++ ys.map (valClassOf ctx) := by
    rw [regsClasses_single, List.map_map, List.map_append]
    rfl
  rw [hcls] at hps
  simp only [List.length_map, List.length_append, Nat.add_sub_cancel] at hps
  unfold retRegsK at hps
  rw [List.take_left' (by simp)] at hps
  obtain ⟨ps1, h1, rfl⟩ := Option.map_eq_some_iff.mp hps
  have hl1 : ps1.length = vs.length := by rw [retRegsC_len _ _ _ h1]; simp
  have hv : ∀ r ∈ vs.map (fun x => Reg.vreg x (valClassOf ctx x)), ∃ n c, r = .vreg n c :=
    fun r hr => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hr
      exact ⟨x, _, rfl⟩
  have hh : (vs.map fun x => Reg.vreg x (valClassOf ctx x)).map Reg.homeCls =
      vs.map (valClassOf ctx) := by
    rw [List.map_map]; rfl
  obtain ⟨ns1, hz1, hns1, hnd1⟩ := retRegsC_pairs (vs.map fun x => Reg.vreg x (valClassOf ctx x))
    0 0 ps1 hv (by rw [hh]; exact h1)
  have hrep : (vs.map (valClassOf ctx) ++ ys.map (valClassOf ctx)).length - vs.length =
      ys.length := by simp
  rw [hrep, List.map_append, List.zip_append (by simp [hl1]), hz1, zip_x8 hsr]
  refine .inr ⟨ns1 ++ ys.map fun y => (y, RegClass.int, Reg.x 8), by simp [argPairsC], ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact retRegC_argRegC (hns1 q hq).1
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hq
      exact .inl ⟨rfl, 8, Nat.le_refl _, rfl⟩
  · have h8 : (ys.map fun y => (y, RegClass.int, Reg.x 8)).map (·.2.2) =
        List.replicate ys.length (Reg.x 8) := by
      rw [List.map_map]
      exact List.eq_replicate_iff.mpr ⟨by simp, fun b hb => by
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
        rfl⟩
    rw [List.map_append, h8, List.nodup_append]
    refine ⟨hnd1, ?_, ?_⟩
    · match ys, hy1 with
      | [], _ => exact List.nodup_nil
      | [_], _ => simp
      | _ :: _ :: _, h => simp at h
    · intro a ha b hb hab
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      rw [(List.eq_replicate_iff.mp rfl).2 b hb] at hab
      rcases (hns1 q hq).1 with ⟨-, k, hk, he⟩ | ⟨-, k, -, he⟩
      · rw [he] at hab; simp only [Reg.x.injEq] at hab; omega
      · rw [he] at hab; cases hab

/-- **The `return` rule checked by hand** (`HandOkT`): on a `return` of the values `vs` and the
struct pointer `sretRet` (`abiTerm`) with an integer vreg, its `rets` has the typed control
shape; on a `trap` it never matches. -/
theorem handOkT_ret (htot : Cov.Totality) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    {ti : Nat} {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true)
    (hd : termData t = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    (hxs : ∀ xs, t = .ret xs → ∃ vs, xs = vs ++ sretRet ctx.func)
    (hsr : ∀ y ∈ sretRet ctx.func, valClassOf ctx y = .int)
    {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower) (hid : rl.id = 1037) (N : Nat) :
    HandOkT ctx N [.inst ti] rl := by
  obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2574 hid
  intro cfg hc m n s0 s tr env s1 r s2 tr2 hm hn hs hmatch heval
  obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.1
    (htot.1 ctx cfg n _ env s1 r (s2, tr2) totalE_ret heval)
  cases t with
  | ret xs =>
    obtain ⟨vs, rfl⟩ := hxs _ rfl
    obtain ⟨rs, ps, hrs, hps, rfl⟩ := ret_emitTy data_program hc hd hi hm hn hmatch heval
    obtain ⟨⟨ms, h1, h2⟩, hN⟩ := hs
    refine ⟨⟨ms ++ [.rets (rs.zip ps)], by simp [LState.emit, h1], fun mi hmi hct => ?_⟩,
      by simpa [LState.emit] using hN⟩
    rcases List.mem_append.mp hmi with hmi | hmi
    · exact h2 mi hmi hct
    · simp only [List.mem_singleton] at hmi
      subst hmi
      exact rets_ctlShapeT N hctx (Cov.sretRet_length_le _) hsr hrs hps
  | trap c => exact (ret_rule_trap_nomatch data_program hd hi hm hmatch).elim
  | _ => simp [retOrTrap] at hrt

end Backend.Proof.CovT
