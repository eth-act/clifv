import FV.Backend.Proof.StockNarrow16CondCarry
import FV.Backend.Proof.IselCtlTbz
import FV.Backend.Proof.StockBranchRootTargets
import FV.Backend.Proof.StockExtendRequests

/-! Branches on a one-bit test: rule selection and emission (#140, CB-13).

A `brif c` whose condition is a one-bit test is not lowered by ordinary `brif` (3231). Two
`lower_branch` rules of higher priority look through the definition of `c`:

* `tbnz` (3251): `c = band x k`, `k = iconst n`, and `test_and_compare_bit_const (value_type x) n`
  gives the single set bit of `n` below the width of `x` (`tcbc`);
* `tbz` (3257): `c = icmp eq y z` with `y` such a `band` and `z = iconst 0`.

`TestBitMetadata` and `TestBitZeroMetadata` state these definitions in the built context.
`test_bit_match` and `test_bit_zero_match` evaluate the actual rule matches, so first-match
selection derives the rule (`test_bit_selected`, `test_bit_zero_selected`): the earlier rule 2542
has another format, each bit-test rule excludes the other by the definition of `c`, and ordinary
`brif` follows both. The selected right-hand sides put `x` in a register (marking it demanded)
and emit one `tbnz`/`tbz` on that register, which defines no register
(`test_bit_named_code`, `test_bit_zero_named_code`). -/

namespace Backend.Stock.Proof.TestBitBranch
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Context metadata of a one-bit test `c = band x k`: `k = iconst imm`, and `imm` has one set
bit `bit` below the width of the type of `x` (`tcbc`, the semantics of
`test_and_compare_bit_const`). -/
def TestBitMetadata (ctx : Ctx) (c : Nat) : Prop :=
  ∃ (ty : Clif.Ty) (x k : Nat) (ty' : Clif.Ty) (imm : BitVec ty'.width) (t : CTy) (bit : Nat),
    ctx.defClif? c = some (.binary .band ty x k) ∧ ctx.defClif? k = some (.iconst ty' imm) ∧
    ctx.valueType? x = some t ∧ tcbc t (u64 (imm64OfIconst ty' imm)) = some bit

/-- Context metadata of a zero test of a one-bit mask: `c = icmp eq y z`, `y` a one-bit test
(`TestBitMetadata`) and `z = iconst 0`. -/
def TestBitZeroMetadata (ctx : Ctx) (c : Nat) : Prop :=
  ∃ (tyc : Clif.Ty) (y z : Nat) (ty0 : Clif.Ty) (imm0 : BitVec ty0.width),
    ctx.defClif? c = some (.icmp .eq tyc y z) ∧ TestBitMetadata ctx y ∧
    ctx.defClif? z = some (.iconst ty0 imm0) ∧ imm0 = 0

private theorem sem_ctor (ctx : Ctx) (t : Term) (vs : List V) (st : State) :
    (Stock.sem ctx).ctor t vs st = Stock.externCtor ctx t vs st := rfl
private theorem sem_mkData (ctx : Ctx) (ty k : Nat) (vs : List V) :
    (Stock.sem ctx).mkData ty k vs = .data ty k vs := rfl
private theorem sem_unData (ctx : Ctx) (ty : Nat) (v : V) :
    (Stock.sem ctx).unData ty v = (Backend.sem ctx).unData ty v := rfl
private theorem sem_extract (ctx : Ctx) (t : Term) (v : V) (st : State) :
    (Stock.sem ctx).extract t v st = Backend.externExtract ctx t v st.base := rfl

section Data
attribute [local semireducible] Isle.Aarch64.program
private theorem band_instData {f : Clif.Function} {ty : Clif.Ty} {a b : Nat} {d : V}
    (h : instData f (.binary .band ty a b) = .ok d) :
    d = .data 152 2 [.data 151 97 [],.values [a,b]] := by
  simp only [instData,binaryOpcode] at h
  split at h
  · simp only [pure,Except.pure,Except.ok.injEq] at h
    rw [← h]
    rfl
  · cases h

private theorem iconst_instData {f : Clif.Function} {ty : Clif.Ty} {imm : BitVec ty.width} {d : V}
    (he : eTy ty = true) (h : instData f (.iconst ty imm) = .ok d) :
    d = .data 152 35 [.data 151 57 [],.int (imm64OfIconst ty imm)] := by
  simp only [instData,he,ite_true,pure,Except.pure,Except.ok.injEq] at h
  rw [← h]
  rfl

private theorem iconst_eTy {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {j : Nat} {info : IInfo}
    {ty : Clif.Ty} {imm : BitVec ty.width} (found : ctx.insts[j]? = some info)
    (clif : info.clif = some (.iconst ty imm)) : eTy ty = true := by
  have accepted := inv.instE j info _ found clif
  cases ty <;> simp_all [Compile.instE,Compile.tyE,eTy]

private theorem icmp_eq_instData {f : Clif.Function} {ty : Clif.Ty} {a b : Nat} {d : V}
    (h : instData f (.icmp .eq ty a b) = .ok d) :
    d = .data 152 14 [.data 151 72 [],.values [a,b],.data 145 0 []] := by
  simp only [instData] at h
  split at h
  · simp only [pure,Except.pure,Except.ok.injEq] at h
    rw [← h,mkVariant_intcc]
    rfl
  · cases h
end Data


private theorem tcbc_stock (ctx : Ctx) (st : State) (t : CTy) (n : Int) {bit : Nat}
    (bitEq : tcbc t n = some bit) :
    Stock.externCtor ctx T.test_and_compare_bit_const [.ty t,.int n] st = .ok (.int bit,st) := by
  rw [stock_ctor_baseOnly ctx _ _ st (by decide)]
  have legacy := (ctor_tcbc_iff (ctx := ctx) st.base t n (.int bit) st.base).mpr ⟨bit,bitEq,rfl,rfl⟩
  rw [legacy]

private theorem block_array (ctx : Ctx) (st : LState) :
    externExtract ctx T.block_array_2 (.blockCalls [0,1]) st = .ok [.blockCalls [0],.blockCalls [1]] := rfl

/-- The match environment of the `tbnz` rule (3251). -/
def tbEnv (t : CTy) (x : Nat) (n : Int) (yes no : Label) (bit : Nat) : Isle.Interp.Env V :=
  #[some (.ty t),some (.value x),some (.int n),some (.label yes),some (.label no),some (.int bit)]

/-- The data facts of a one-bit test: `c = band x k` and `k = iconst w`, in the built
context. -/
structure TestBitData (ctx : Ctx) (c x : Nat) (w : Int) where
  j1 : Nat
  j2 : Nat
  k : Nat
  info1 : IInfo
  info2 : IInfo
  defC : ctx.defInst? c = some j1
  foundC : ctx.insts[j1]? = some info1
  dataC : info1.data = .data 152 2 [.data 151 97 [],.values [x,k]]
  defK : ctx.defInst? k = some j2
  foundK : ctx.insts[j2]? = some info2
  dataK : info2.data = .data 152 35 [.data 151 57 [],.int w]

/-- Rule 3251 matches a branch on a one-bit test, with unchanged state and trace. -/
theorem test_bit_match {p : Program} (hp : Data p) {ctx : Ctx}
    {i c x : Nat} {w : Int} {t : CTy} {bit : Nat}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (data : TestBitData ctx c x w)
    (typeX : ctx.valueType? x = some t) (bitEq : tcbc t (u64 w) = some bit)
    (yes no : Label) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+40) rule_lower_3251 [.inst i,.labels [yes,no]]).run (st,tr) =
      .ok (some (tbEnv t x (u64 w) yes no bit),st,tr) := by
  obtain ⟨j1,j2,k,info1,info2,defC,foundC,dataC,defK,foundK,dataK⟩ := data
  have e0 := ext_inst_data_value ctx st.base slot
  have e1 := ext_def_inst_some ctx st.base defC
  have e2 := ext_inst_data_value ctx st.base foundC
  rw [dataC] at e2
  have e3 := ext_value_array_2 ctx st.base x k
  have e4 := ext_value_type ctx st.base typeX
  have e5 := ext_def_inst_some ctx st.base defK
  have e6 := ext_inst_data_value ctx st.base foundK
  rw [dataK] at e6
  have e7 := ext_u64_from_imm64 ctx st.base w
  have e8 := block_array ctx st.base
  have e9 : externExtract ctx T.two_targets (.labels [yes,no]) st.base = .ok [.label yes,.label no] :=
    (ext_two_targets_iff (ctx := ctx) st.base [yes,no] [.label yes,.label no]).mpr ⟨yes,no,rfl,rfl⟩
  have e10 := tcbc_stock ctx st t (u64 w) bitEq
  cases hp
  isel_eval [*,rule_lower_3251,sem_extract,sem_unData,sem_ctor,stock_matchArgs]
  all_goals rfl

/-- The `tbz` rule (3257) does not match a branch on a `band` result. -/
private theorem zero_rule_absurd {ctx : Ctx} {i c x : Nat} {w : Int} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (data : TestBitData ctx c x w)
    {fuel : Nat} {before next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel rule_lower_3257 [.inst i,.labels labels]).run before =
      .ok (some env,next)) : False := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    have hp := data_program
    isel_inv' hp [rule_lower_3257,slot] at args
    obtain ⟨defined⟩ : Nonempty (ctx.defInst? c = some _) := ⟨‹_›⟩
    obtain ⟨found⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
    obtain ⟨shape⟩ : Nonempty (V.data 152 14 _ = _) := ⟨‹_›⟩
    rw [data.defC] at defined
    cases defined
    rw [data.foundC] at found
    cases found
    rw [data.dataC] at shape
    simp at shape


private theorem branch_ruleFmt_match {ctx : Ctx} {r : Rule} {fT : Nat}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447 + 36)
    {fuel ti : Nat} {rest : List V} {st next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r (.inst ti :: rest)).run st =
      .ok (some env, next)) :
    ∃ info fs, ctx.insts[ti]? = some info ∧ info.data = .data 152 (fT - 2447) fs := by
  have bound : fT - 2447 < 36 := by omega
  obtain ⟨term, lookup, kind⟩ := fmtKinds_program (fT - 2447) bound
  rw [show 2447 + (fT - 2447) = fT by omega] at lookup
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0, args, _⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    unfold ruleFmt at format
    split at format
    · rename_i q qs shape
      rw [shape] at args
      obtain ⟨env1, head, _⟩ := matchArgs_cons_inv args
      exact rootFmt_match_k data_program format lookup kind head
    · cases format

private theorem other_format {ctx : Ctx} {i fT tag : Nat} {fields : List V}
    (slot : ctx.insts[i]? = some ⟨.data 152 tag fields,[],[],none⟩) {r : Rule}
    (format : ruleFmt r = some fT) (lo : 2447 ≤ fT) (hi : fT < 2447+36) (different : fT ≠ 2447+tag)
    {fuel : Nat} {st next : State × Array RuleId} {labels : List Label} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel r [.inst i,.labels labels]).run st =
      .ok (some env,next)) : False := by
  obtain ⟨info,fs,source,shape⟩ := branch_ruleFmt_match format lo hi matched
  rw [slot] at source
  cases source
  simp only [V.data.injEq] at shape
  omega

private theorem id_ne {r s : Rule} (different : r.id ≠ s.id) : r ≠ s := fun same => different (same ▸ rfl)

/-- In the rule list of `lower_branch`, both bit-test rules precede ordinary `brif` (3231). -/
private theorem test_bits_before_plain {pre post : List Rule}
    (order : [rule_lower_2542,rule_lower_3251,rule_lower_3257,rule_lower_2551,rule_lower_2561,
      rule_lower_3231,rule_lower_3270,rule_lower_3277] = pre ++ rule_lower_3231 :: post) :
    rule_lower_3251 ∈ pre ∧ rule_lower_3257 ∈ pre := by
  have n0 : rule_lower_2542 ≠ rule_lower_3231 := id_ne (by decide)
  have n1 : rule_lower_3251 ≠ rule_lower_3231 := id_ne (by decide)
  have n2 : rule_lower_3257 ≠ rule_lower_3231 := id_ne (by decide)
  have n3 : rule_lower_2551 ≠ rule_lower_3231 := id_ne (by decide)
  have n4 : rule_lower_2561 ≠ rule_lower_3231 := id_ne (by decide)
  have n6 : rule_lower_3270 ≠ rule_lower_3231 := id_ne (by decide)
  have n7 : rule_lower_3277 ≠ rule_lower_3231 := id_ne (by decide)
  rcases pre with _ | ⟨r0,_ | ⟨r1,_ | ⟨r2,_ | ⟨r3,_ | ⟨r4,_ | ⟨r5,rest⟩⟩⟩⟩⟩⟩
  all_goals simp only [List.cons_append,List.nil_append,List.cons.injEq] at order
  · exact absurd order.1 n0
  · exact absurd order.2.1 n1
  · exact absurd order.2.2.1 n2
  · exact absurd order.2.2.2.1 n3
  · exact absurd order.2.2.2.2.1 n4
  · obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := order
    simp
  · obtain ⟨_,_,_,_,_,_,tail⟩ := order
    rcases rest with _ | ⟨r6,_ | ⟨r7,rest⟩⟩
    all_goals simp only [List.cons_append,List.nil_append,List.cons.injEq] at tail
    · exact absurd tail.1 n6
    · exact absurd tail.2.1 n7
    · simp at tail

/-- **The actual first matching rule of a branch on a one-bit test is `tbnz` (3251).** The
preceding rule (2542) has another format; ordinary `brif` (3231) follows 3251 and is not selected
because 3251 matches (`test_bit_match`). -/
theorem test_bit_selected {ctx : Ctx}
    {i c x : Nat} {w : Int} {t : CTy} {bit : Nat} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (data : TestBitData ctx c x w)
    (typeX : ctx.valueType? x = some t) (bitEq : tcbc t (u64 w) = some bit)
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace) :
    selected.rule = rule_lower_3251 := by
  have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
  rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with root | root | root | root | root | root | root | root
  all_goals try exact root
  all_goals
    have matched := selected.matchedRun
    rw [root] at matched
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (zero_rule_absurd slot data matched)
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
  · exfalso
    obtain ⟨calls⟩ := ConditionalCalls.selected_calls selected root
    have order := selected.candidates
    rw [show T.lower_branch.id = 687 from rfl,data_program.r687,root] at order
    obtain ⟨earlier,_⟩ := test_bits_before_plain order
    obtain ⟨fuel,bound,after,failed⟩ := selected.rejected _ earlier
    have count : (program.rulesOf T.lower_branch.id).length = 8 := by
      rw [show T.lower_branch.id = 687 from rfl,data_program.r687]; rfl
    obtain ⟨n,equal⟩ : ∃ n,fuel = n+40 := ⟨fuel-40,by omega⟩
    rw [calls.labels_eq,equal,test_bit_match data_program slot data typeX bitEq] at failed
    cases failed
  · exact False.elim (other_format slot (fT := 2462) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2451) rfl (by decide) (by decide) (by decide) matched)


private theorem internal_split_first {p : Program} {cfg : Config} {σ : Type} {sem : Isle.Sem V σ}
    (hc : cfg.checkOverlap = false) {ty : TypeId} {t : TermId} {vs : List V} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : σ × Array RuleId} {v : V}
    (h : ApplyInternal p sem cfg n ty t vs s v s') :
    ∃ pre r post, p.rulesOf t = pre ++ r :: post ∧
      (∀ r' ∈ pre, ∃ m' s1, (matchRule p sem cfg (m' + 20) r' vs).run s = .ok (none, s1)) ∧
      ∃ m' n' env s1 st tr,
      (matchRule p sem cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p sem cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) ∧ n = n' + 20 := by
  obtain ⟨r, pre, post, hL, hpre, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ :=
    applyTerm_internal_some_first hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  refine ⟨pre, r, post, hL, fun r' hr' => ?_, m', n', env, s1, st, tr, hmt, he, rfl, rfl⟩
  obtain ⟨k, hk, s2, h2⟩ := hpre r' hr'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 20 := ⟨k - 20, by omega⟩
  exact ⟨k', s2, h2⟩

private theorem test_branch_builder {ctx : Ctx} {fuel : Nat} (enough : 30 ≤ fuel) {k a b r bit : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 46 666 [k,a,b,r,bit] st out next) :
    next.1 = st.1 ∧ out = .data 46 0 [.data 58 119 [k,a,b,r,bit]] := by
  have hp := data_program
  obtain ⟨_,_,_,rules,_,_,_,_,_,_,_,matched,rhs,rfl,rfl⟩ :=
    internal_split_first rfl hp.t666 term_666_kind rfl (by rw [hp.r666]; simp; omega) run
  rw [hp.r666] at rules
  isel_rule_cases rules
  cases hp
  isel_inv [*,rule_inst_5425,sem_ctor,sem_mkData,sem_unData] at matched rhs

private theorem tbnz_builder {ctx : Ctx} {fuel : Nat} (enough : 60 ≤ fuel) {a b r bit : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 46 667 [a,b,r,bit] st out next) :
    next.1 = st.1 ∧ out = .data 46 0 [.data 58 119 [.data 94 1 [],a,b,r,bit]] := by
  have hp := data_program
  obtain ⟨_,_,_,rules,_,_,_,_,_,_,_,matched,rhs,rfl,rfl⟩ :=
    internal_split_first rfl hp.t667 term_667_kind rfl (by rw [hp.r667]; simp; omega) run
  rw [hp.r667] at rules
  isel_rule_cases rules
  cases hp
  isel_inv [*,rule_inst_5431,sem_ctor,sem_mkData,sem_unData] at matched rhs
  have inner := ‹ApplyInternal _ _ _ _ 46 666 _ _ _ _›
  obtain ⟨same,rfl⟩ := test_branch_builder (by omega) inner
  exact ⟨same,rfl⟩

private theorem emit_side_effect {ctx : Ctx} {fuel : Nat} (enough : 30 ≤ fuel) {i : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 13 242 [.data 46 0 [i]] st out next) :
    ∃ m,MInst.ofV i = some m ∧ next.1 = {st.1 with base := st.1.base.emit m} ∧ out = .op .unit := by
  have emit : ∀ i st out next,Stock.externCtor ctx T.emit [i] st = .ok (out,next) ↔
      ∃ m,MInst.ofV i = some m ∧ out = .op .unit ∧ next = {st with base := st.base.emit m} := by
    intro i st out next
    rw [stock_ctor_baseOnly ctx T.emit [i] st (by decide)]
    have legacy : Backend.externCtor ctx T.emit [i] st.base = match MInst.ofV i with
      | some m => .ok (.op .unit,st.base.emit m)
      | none => .unmodeled s!"emit of {((i.variant?).map (·.2.1)).getD "?"}" := rfl
    rw [legacy]
    cases MInst.ofV i <;> simp [eq_comm]
  have hp := data_program
  obtain ⟨_,_,_,rules,_,_,_,_,_,_,_,matched,rhs,rfl,rfl⟩ :=
    internal_split_first rfl hp.t242 term_242_kind rfl (by rw [hp.r242]; simp; omega) run
  rw [hp.r242] at rules
  isel_rule_cases rules
  all_goals cases hp
  · isel_inv [*,rule_prelude_lower_522,sem_ctor,sem_mkData,sem_unData,emit] at matched rhs
    isel_destruct
    subst_vars
    obtain ⟨m,decoded,output,state⟩ := (emit _ _ _ _).mp (by assumption)
    exact ⟨m,decoded,state,output⟩
  · isel_inv [*,rule_prelude_lower_524,sem_ctor,sem_unData] at matched
  · isel_inv [*,rule_prelude_lower_527,sem_ctor,sem_unData] at matched


private theorem branch_target (ctx : Ctx) (st : State) (l : Label) (out : V) (next : State) :
    Stock.externCtor ctx T.branch_target [.label l] st = .ok (out,next) ↔ out = .label l ∧ next = st := by
  have actual : Stock.externCtor ctx T.branch_target [.label l] st = .ok (.label l,st) := rfl
  rw [actual]
  simp [eq_comm]

/-- The selected `tbnz` rule emits exactly `tbnz r, #bit` on the register of `x`, after marking
`x` demanded. -/
theorem test_bit_selected_code {ctx : Ctx}
    {i c x : Nat} {w : Int} {t : CTy} {bit : Nat} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (data : TestBitData ctx c x w)
    (typeX : ctx.valueType? x = some t) (bitEq : tcbc t (u64 w) = some bit)
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace)
    (root : selected.rule = rule_lower_3251) :
    ∃ a b r,labels = [a,b] ∧ ctx.valueReg? x = some r ∧ DemandAllowed ctx before x ∧
      next = {before.mark x with base := before.base.emit (.testBitAndBranch .nz a b r bit)} := by
  have count : (program.rulesOf T.lower_branch.id).length = 8 := by
    rw [show T.lower_branch.id = 687 from rfl,data_program.r687]; rfl
  have bound := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+40 := ⟨selected.matchFuel-40,by omega⟩
  have shape : ∃ a b,labels = [a,b] := by
    have matched := selected.matchedRun
    rw [root,fuelEq] at matched
    have hp := data_program
    cases hp
    isel_inv [*,rule_lower_3251,sem_ctor,sem_extract,sem_unData,ext_two_targets_iff] at matched
    obtain ⟨a,b,rfl,_⟩ := (ext_two_targets_iff _ _ _).mp ‹externExtract ctx T.two_targets (V.labels labels) _ = _›
    exact ⟨_,_,rfl⟩
  obtain ⟨a,b,rfl⟩ := shape
  have matched := selected.matchedRun
  rw [root,fuelEq,test_bit_match data_program slot data typeX bitEq] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [root,← envEq,← stateEq,← traceEq] at rhs
  have hp := data_program
  cases hp
  isel_inv [*,rule_lower_3251,tbEnv,sem_ctor,sem_extract,sem_unData,branch_target,stock_put_in_reg_iff] at rhs
  simp only [List.getElem?_toArray,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at *
  subst_vars
  simp only [branch_target] at *
  isel_destruct
  subst_vars
  obtain ⟨safe,r,mapped,rfl,rfl⟩ :=
    (stock_put_in_reg_iff _ _ _ _ _).mp ‹Stock.externCtor ctx T.put_in_reg [.value x] _ = _›
  have build := ‹ApplyInternal _ _ _ _ 46 667 _ _ _ _›
  obtain ⟨state1,rfl⟩ := tbnz_builder (by omega) build
  have emitted := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi,decoded,state2,_⟩ := emit_side_effect (by omega) emitted
  rw [ofV_tbb_nz] at decoded
  cases decoded
  rw [← stateEq] at safe state1
  refine ⟨a,b,⟨rfl,rfl⟩,r,mapped,safe,?_⟩
  simp only at state2 state1
  rw [state2,state1]
  rfl


/-! ## `tbz` -/

/-- The data facts of a zero test of a one-bit mask: `c = icmp eq y z`, `y = band x k`,
`k = iconst w` and `z = iconst w0` with `u64 w0 = 0`, in the built context. -/
structure TestBitZeroData (ctx : Ctx) (c x : Nat) (w : Int) where
  j0 : Nat
  j3 : Nat
  y : Nat
  z : Nat
  info0 : IInfo
  info3 : IInfo
  w0 : Int
  defC : ctx.defInst? c = some j0
  foundC : ctx.insts[j0]? = some info0
  dataC : info0.data = .data 152 14 [.data 151 72 [],.values [y,z],.data 145 0 []]
  band : TestBitData ctx y x w
  defZ : ctx.defInst? z = some j3
  foundZ : ctx.insts[j3]? = some info3
  dataZ : info3.data = .data 152 35 [.data 151 57 [],.int w0]
  zero : u64 w0 = 0

/-- Rule 3257 matches a branch on a zero test of a one-bit mask, with unchanged state and
trace. -/
theorem test_bit_zero_match {p : Program} (hp : Data p) {ctx : Ctx}
    {i c x : Nat} {w : Int} {t : CTy} {bit : Nat}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (data : TestBitZeroData ctx c x w)
    (typeX : ctx.valueType? x = some t) (fits : t.bits ≤ 64) (bitEq : tcbc t (u64 w) = some bit)
    (yes no : Label) (st : State) (tr : Array RuleId) (n : Nat) :
    (matchRule p (Stock.sem ctx) {} (n+60) rule_lower_3257 [.inst i,.labels [yes,no]]).run (st,tr) =
      .ok (some (tbEnv t x (u64 w) yes no bit),st,tr) := by
  obtain ⟨j0,j3,y,z,info0,info3,w0,defC,foundC,dataC,⟨j1,j2,k,info1,info2,defY,foundY,dataY,defK,foundK,dataK⟩,
    defZ,foundZ,dataZ,zero⟩ := data
  have e0 := ext_inst_data_value ctx st.base slot
  have e1 := ext_def_inst_some ctx st.base defC
  have e2 := ext_inst_data_value ctx st.base foundC
  rw [dataC] at e2
  have e3 := ext_value_array_2 ctx st.base y z
  have e1' := ext_def_inst_some ctx st.base defY
  have e2' := ext_inst_data_value ctx st.base foundY
  rw [dataY] at e2'
  have e3' := ext_value_array_2 ctx st.base x k
  have e4 := ext_value_type ctx st.base typeX
  have e4' : externExtract ctx T.fits_in_64 (.ty t) st.base = .ok [.ty t] := by
    rw [ext_fits_in_64']
    simp [fits]
  have e5 := ext_def_inst_some ctx st.base defK
  have e6 := ext_inst_data_value ctx st.base foundK
  rw [dataK] at e6
  have e7 := ext_u64_from_imm64 ctx st.base w
  have e5' := ext_def_inst_some ctx st.base defZ
  have e6' := ext_inst_data_value ctx st.base foundZ
  rw [dataZ] at e6'
  have e7' := ext_u64_from_imm64 ctx st.base w0
  rw [zero] at e7'
  have e8 := block_array ctx st.base
  have e9 : externExtract ctx T.two_targets (.labels [yes,no]) st.base = .ok [.label yes,.label no] :=
    (ext_two_targets_iff (ctx := ctx) st.base [yes,no] [.label yes,.label no]).mpr ⟨yes,no,rfl,rfl⟩
  have e10 := tcbc_stock ctx st t (u64 w) bitEq
  cases hp
  have zeroEq : (Backend.sem ctx).eq (V.int ((0 : Nat) : Int)) (V.int 0) = true := rfl
  isel_eval [*,rule_lower_3257,sem_extract,sem_unData,sem_ctor,stock_matchArgs]
  all_goals rfl


/-- The `tbnz` rule (3251) does not match a branch on an `icmp` result. -/
private theorem band_rule_absurd {ctx : Ctx} {i c x : Nat} {w : Int} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (data : TestBitZeroData ctx c x w)
    {fuel : Nat} {before next : State × Array RuleId} {env : Isle.Interp.Env V}
    (matched : (matchRule program (Stock.sem ctx) {} fuel rule_lower_3251 [.inst i,.labels labels]).run before =
      .ok (some env,next)) : False := by
  cases fuel with
  | zero => rw [matchRule.eq_1] at matched; cases matched
  | succ fuel =>
    obtain ⟨env0,args,_⟩ := matchRule_some_inv matched
    rw [stock_matchArgs] at args
    have hp := data_program
    isel_inv' hp [rule_lower_3251,slot] at args
    obtain ⟨defined⟩ : Nonempty (ctx.defInst? c = some _) := ⟨‹_›⟩
    obtain ⟨found⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹_›⟩
    obtain ⟨shape⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
    rw [data.defC] at defined
    cases defined
    rw [data.foundC] at found
    cases found
    rw [data.dataC] at shape
    simp at shape

/-- **The actual first matching rule of a branch on a zero test of a one-bit mask is `tbz`
(3257).** -/
theorem test_bit_zero_selected {ctx : Ctx}
    {i c x : Nat} {w : Int} {t : CTy} {bit : Nat} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (data : TestBitZeroData ctx c x w)
    (typeX : ctx.valueType? x = some t) (fits : t.bits ≤ 64) (bitEq : tcbc t (u64 w) = some bit)
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace) :
    selected.rule = rule_lower_3257 := by
  have member : selected.rule ∈ program.rulesOf T.lower_branch.id := by rw [selected.candidates]; simp
  rw [show T.lower_branch.id = 687 from rfl,data_program.r687] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with root | root | root | root | root | root | root | root
  all_goals try exact root
  all_goals
    have matched := selected.matchedRun
    rw [root] at matched
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (band_rule_absurd slot data matched)
  · exact False.elim (other_format slot (fT := 2474) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2475) rfl (by decide) (by decide) (by decide) matched)
  · exfalso
    obtain ⟨calls⟩ := ConditionalCalls.selected_calls selected root
    have order := selected.candidates
    rw [show T.lower_branch.id = 687 from rfl,data_program.r687,root] at order
    obtain ⟨_,earlier⟩ := test_bits_before_plain order
    obtain ⟨fuel,bound,after,failed⟩ := selected.rejected _ earlier
    have count : (program.rulesOf T.lower_branch.id).length = 8 := by
      rw [show T.lower_branch.id = 687 from rfl,data_program.r687]; rfl
    obtain ⟨n,equal⟩ : ∃ n,fuel = n+60 := ⟨fuel-60,by omega⟩
    rw [calls.labels_eq,equal,test_bit_zero_match data_program slot data typeX fits bitEq] at failed
    cases failed
  · exact False.elim (other_format slot (fT := 2462) rfl (by decide) (by decide) (by decide) matched)
  · exact False.elim (other_format slot (fT := 2451) rfl (by decide) (by decide) (by decide) matched)

private theorem tbz_builder {ctx : Ctx} {fuel : Nat} (enough : 60 ≤ fuel) {a b r bit : V}
    {st next : State × Array RuleId} {out : V}
    (run : ApplyInternal program (Stock.sem ctx) {} fuel 46 668 [a,b,r,bit] st out next) :
    next.1 = st.1 ∧ out = .data 46 0 [.data 58 119 [.data 94 0 [],a,b,r,bit]] := by
  have hp := data_program
  obtain ⟨_,_,_,rules,_,_,_,_,_,_,_,matched,rhs,rfl,rfl⟩ :=
    internal_split_first rfl hp.t668 term_668_kind rfl (by rw [hp.r668]; simp; omega) run
  rw [hp.r668] at rules
  isel_rule_cases rules
  cases hp
  isel_inv [*,rule_inst_5437,sem_ctor,sem_mkData,sem_unData] at matched rhs
  have inner := ‹ApplyInternal _ _ _ _ 46 666 _ _ _ _›
  obtain ⟨same,rfl⟩ := test_branch_builder (by omega) inner
  exact ⟨same,rfl⟩

/-- The selected `tbz` rule emits exactly `tbz r, #bit` on the register of `x`, after marking
`x` demanded. -/
theorem test_bit_zero_selected_code {ctx : Ctx}
    {i c x : Nat} {w : Int} {t : CTy} {bit : Nat} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (data : TestBitZeroData ctx c x w)
    (typeX : ctx.valueType? x = some t) (fits : t.bits ≤ 64) (bitEq : tcbc t (u64 w) = some bit)
    {before next : State} {out : V} {trace : List RuleId}
    (selected : BranchSelection ctx i labels before out next trace)
    (root : selected.rule = rule_lower_3257) :
    ∃ a b r,labels = [a,b] ∧ ctx.valueReg? x = some r ∧ DemandAllowed ctx before x ∧
      next = {before.mark x with base := before.base.emit (.testBitAndBranch .z a b r bit)} := by
  have count : (program.rulesOf T.lower_branch.id).length = 8 := by
    rw [show T.lower_branch.id = 687 from rfl,data_program.r687]; rfl
  have bound := selected.fuelBound
  obtain ⟨m,fuelEq⟩ : ∃ m,selected.matchFuel = m+60 := ⟨selected.matchFuel-60,by omega⟩
  have shape : ∃ a b,labels = [a,b] := by
    have matched := selected.matchedRun
    rw [root,fuelEq] at matched
    have hp := data_program
    cases hp
    isel_inv [*,rule_lower_3257,sem_ctor,sem_extract,sem_unData,ext_two_targets_iff] at matched
    obtain ⟨a,b,rfl,_⟩ := (ext_two_targets_iff _ _ _).mp ‹externExtract ctx T.two_targets (V.labels labels) _ = _›
    exact ⟨_,_,rfl⟩
  obtain ⟨a,b,rfl⟩ := shape
  have matched := selected.matchedRun
  rw [root,fuelEq,test_bit_zero_match data_program slot data typeX fits bitEq] at matched
  simp only [Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at matched
  obtain ⟨envEq,stateEq,traceEq⟩ := matched
  have rhs := selected.rhsRun
  rw [root,← envEq,← stateEq,← traceEq] at rhs
  have hp := data_program
  cases hp
  isel_inv [*,rule_lower_3257,tbEnv,sem_ctor,sem_extract,sem_unData,branch_target,stock_put_in_reg_iff] at rhs
  simp only [List.getElem?_toArray,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at *
  subst_vars
  simp only [branch_target] at *
  isel_destruct
  subst_vars
  obtain ⟨safe,r,mapped,rfl,rfl⟩ :=
    (stock_put_in_reg_iff _ _ _ _ _).mp ‹Stock.externCtor ctx T.put_in_reg [.value x] _ = _›
  have build := ‹ApplyInternal _ _ _ _ 46 668 _ _ _ _›
  obtain ⟨state1,rfl⟩ := tbz_builder (by omega) build
  have emitted := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi,decoded,state2,_⟩ := emit_side_effect (by omega) emitted
  rw [ofV_tbb_z] at decoded
  cases decoded
  rw [← stateEq] at safe state1
  refine ⟨a,b,⟨rfl,rfl⟩,r,mapped,safe,?_⟩
  simp only at state2 state1
  rw [state2,state1]
  rfl


/-! ## From the context metadata to the rule data -/

/-- The `eTy` type of an accepted `iconst`. -/
theorem iconst_accepted {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {k : Nat}
    {ty : Clif.Ty} {imm : BitVec ty.width} (origin : ctx.defClif? k = some (.iconst ty imm)) : eTy ty = true := by
  obtain ⟨j,info,_,found,clif⟩ := cmp_defClif_inv origin
  exact iconst_eTy inv found clif

/-- A typed value has a type of at most 64 bits. -/
theorem value_type_fits {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx) {x : Nat} {t : CTy}
    (typed : ctx.valueType? x = some t) : t.bits ≤ 64 := by
  have member := inv.valTyE x t typed
  simp only [eCTys,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

/-- The definitions of a one-bit test give the data facts of its rule. -/
theorem test_bit_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {c x k : Nat} {ty ty' : Clif.Ty} {imm : BitVec ty'.width}
    (originC : ctx.defClif? c = some (.binary .band ty x k))
    (originK : ctx.defClif? k = some (.iconst ty' imm)) :
    Nonempty (TestBitData ctx c x (imm64OfIconst ty' imm)) := by
  obtain ⟨j1,info1,defC,foundC,clifC⟩ := cmp_defClif_inv originC
  obtain ⟨j2,info2,defK,foundK,clifK⟩ := cmp_defClif_inv originK
  exact ⟨⟨j1,j2,k,info1,info2,defC,foundC,band_instData (inv.data j1 info1 _ foundC clifC),
    defK,foundK,iconst_instData (iconst_eTy inv foundK clifK) (inv.data j2 info2 _ foundK clifK)⟩⟩

private theorem u64_iconst_zero {ty : Clif.Ty} (he : eTy ty = true) :
    u64 (imm64OfIconst ty (0 : BitVec ty.width)) = 0 := by
  have actual := u64_iconst he (0 : BitVec ty.width)
  have small : u64 (imm64OfIconst ty (0 : BitVec ty.width)) < 2^64 := by unfold u64; omega
  rw [u64_ofNat small] at actual
  simpa using actual

/-- The definitions of a zero test of a one-bit mask give the data facts of its rule. -/
theorem test_bit_zero_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {c y z x k : Nat} {tyc ty ty' ty0 : Clif.Ty} {imm : BitVec ty'.width} {imm0 : BitVec ty0.width}
    (originC : ctx.defClif? c = some (.icmp .eq tyc y z))
    (originY : ctx.defClif? y = some (.binary .band ty x k))
    (originK : ctx.defClif? k = some (.iconst ty' imm))
    (originZ : ctx.defClif? z = some (.iconst ty0 imm0)) (zero : imm0 = 0) :
    Nonempty (TestBitZeroData ctx c x (imm64OfIconst ty' imm)) := by
  obtain ⟨j0,info0,defC,foundC,clifC⟩ := cmp_defClif_inv originC
  obtain ⟨j3,info3,defZ,foundZ,clifZ⟩ := cmp_defClif_inv originZ
  obtain ⟨band⟩ := test_bit_data inv originY originK
  subst zero
  have he := iconst_eTy inv foundZ clifZ
  exact ⟨⟨j0,j3,y,z,info0,info3,_,defC,foundC,icmp_eq_instData (inv.data j0 info0 _ foundC clifC),band,
    defZ,foundZ,iconst_instData he (inv.data j3 info3 _ foundZ clifZ),u64_iconst_zero he⟩⟩

/-! ## Named runs -/

/-- **A real named branch on a one-bit test emits `tbnz r, #bit`.** The rule is derived
(`test_bit_selected`), the labels are the two targets, `r` is the register of `x`, `x` is marked
demanded, and nothing else changes. -/
theorem test_bit_named_code {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c x k bit : Nat} {ty ty' : Clif.Ty} {imm : BitVec ty'.width} {t : CTy} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (originC : ctx.defClif? c = some (.binary .band ty x k))
    (originK : ctx.defClif? k = some (.iconst ty' imm))
    (typeX : ctx.valueType? x = some t) (bitEq : tcbc t (u64 (imm64OfIconst ty' imm)) = some bit)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace)) :
    ∃ a b r,labels = [a,b] ∧ ctx.valueReg? x = some r ∧ DemandAllowed ctx before x ∧
      next = {before.mark x with base := before.base.emit (.testBitAndBranch .nz a b r bit)} := by
  obtain ⟨data⟩ := test_bit_data inv originC originK
  obtain ⟨selected⟩ := stock_named_branch_selection run
  exact test_bit_selected_code slot data typeX bitEq selected (test_bit_selected slot data typeX bitEq selected)

/-- **A real named branch on a zero test of a one-bit mask emits `tbz r, #bit`.** -/
theorem test_bit_zero_named_code {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i c y z x k bit : Nat} {tyc ty ty' ty0 : Clif.Ty} {imm : BitVec ty'.width} {imm0 : BitVec ty0.width}
    {t : CTy} {labels : List Label}
    (slot : ctx.insts[i]? = some ⟨.data 152 5 [.data 151 1 [],.value c,.blockCalls [0,1]],[],[],none⟩)
    (originC : ctx.defClif? c = some (.icmp .eq tyc y z))
    (originY : ctx.defClif? y = some (.binary .band ty x k))
    (originK : ctx.defClif? k = some (.iconst ty' imm))
    (originZ : ctx.defClif? z = some (.iconst ty0 imm0)) (zero : imm0 = 0)
    (typeX : ctx.valueType? x = some t) (bitEq : tcbc t (u64 (imm64OfIconst ty' imm)) = some bit)
    {before next : State} {out : V} {trace : List RuleId}
    (run : Stock.runTerm ctx "lower_branch" [.inst i,.labels labels] before = .ok (some out,next,trace)) :
    ∃ a b r,labels = [a,b] ∧ ctx.valueReg? x = some r ∧ DemandAllowed ctx before x ∧
      next = {before.mark x with base := before.base.emit (.testBitAndBranch .z a b r bit)} := by
  obtain ⟨data⟩ := test_bit_zero_data inv originC originY originK originZ zero
  have fits := value_type_fits inv typeX
  obtain ⟨selected⟩ := stock_named_branch_selection run
  exact test_bit_zero_selected_code slot data typeX fits bitEq selected
    (test_bit_zero_selected slot data typeX fits bitEq selected)

end Backend.Stock.Proof.TestBitBranch
