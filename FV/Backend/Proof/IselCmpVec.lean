import FV.Backend.Proof.IselCmpMinMax

/-!
# Family C: vector min/max (1233/1239/1245/1251) are vacuous in E

Their right-hand side needs `vector_size ty`, which has no rule for the scalar result types of
E (`CtxInv.resTysE`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

theorem ext_multi_lane_int (st : LState) (w : Nat) (fs : List V) :
    externExtract ctx T.multi_lane (.ty (.int w)) st = .ok fs ↔ False := by
  have e : externExtract ctx T.multi_lane (.ty (.int w)) st = .fail := rfl
  rw [e]; simp

theorem ext_dynamic_lane_ty (st : LState) (t : CTy) (fs : List V) :
    externExtract ctx T.dynamic_lane (.ty t) st = .ok fs ↔ False := by
  have e : externExtract ctx T.dynamic_lane (.ty t) st = .fail := rfl
  rw [e]; simp

set_option maxHeartbeats 4000000 in
include hp hc in
/-- `vector_size` has no rule for a scalar integer type. -/
theorem vector_size_scalar {n : Nat} (hn : 60 ≤ n) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 97 310 [.ty (.int w)] s v s') : False := by
  rcases hw with rfl | rfl | rfl | rfl <;>
  isel_split' hp hc h 310 <;>
  isel_inv' hp [ext_multi_lane_int, ext_dynamic_lane_ty] at hm

set_option maxHeartbeats 4000000 in
include hp hc in
/-- The result type of a binary instruction of E has no `vector_size`. -/
theorem vector_size_binary_absurd {f : Clif.Function} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hic : info.clif = some inst) {cop : Clif.BinaryOp} {nm : String} {ko : Nat} {w3 : V}
    (hname : (variantNames 151)[ko]? = some nm) (hcop : binaryOpcode cop = some nm)
    (hdd : V.data 152 2 [V.data 151 ko [], w3] = info.data) {n : Nat} (hn : 60 ≤ n)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 97 310 [.ty (info.resTys.head?.getD .invalid)] s v s') :
    False := by
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, -⟩ := instData_binary_inv hname hcop hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at h
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some, ofClif_int_width] at h
  exact vector_size_scalar hp hc hn (cmp_eTy_widths hety) h

end

section Root
variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
theorem vec_smin_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1233 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = info.data) := ⟨‹_›⟩
  obtain ⟨h310⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 97 310 _ _ _ _) := ⟨‹_›⟩
  exact (vector_size_binary_absurd hp hco hctx hi hic (cop := .smin) rfl rfl hdd (by omega) h310).elim


set_option maxHeartbeats 8000000 in
include hp in
theorem vec_umin_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1239 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = info.data) := ⟨‹_›⟩
  obtain ⟨h310⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 97 310 _ _ _ _) := ⟨‹_›⟩
  exact (vector_size_binary_absurd hp hco hctx hi hic (cop := .umin) rfl rfl hdd (by omega) h310).elim


set_option maxHeartbeats 8000000 in
include hp in
theorem vec_smax_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1245 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = info.data) := ⟨‹_›⟩
  obtain ⟨h310⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 97 310 _ _ _ _) := ⟨‹_›⟩
  exact (vector_size_binary_absurd hp hco hctx hi hic (cop := .smax) rfl rfl hdd (by omega) h310).elim


set_option maxHeartbeats 8000000 in
include hp in
theorem vec_umax_ruleOk (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOk isem MR env cp p rule_lower_1251 := by
  intro f ctx hctx ii info inst hi hic cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = info.data) := ⟨‹_›⟩
  obtain ⟨h310⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 97 310 _ _ _ _) := ⟨‹_›⟩
  exact (vector_size_binary_absurd hp hco hctx hi hic (cop := .umax) rfl rfl hdd (by omega) h310).elim

end Root

end Backend.Proof
