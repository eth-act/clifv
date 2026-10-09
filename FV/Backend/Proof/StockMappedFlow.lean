import FV.Backend.Proof.StockCtorFlow
import FV.Backend.Proof.IselFlowInst
import FV.Backend.Proof.IselFlowTabF
import FV.Backend.Proof.LowerDecide

/-! Mapped source-provenance model for actual stock ISLE execution. -/
namespace Backend.Stock.Proof.MappedFlow
attribute [local irreducible] Isle.Aarch64.program
open Backend.Proof Backend.Proof.Driver Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

section FlowM
variable (ctx : Ctx) (ii lo : Nat)

/-- A register a statement's lowering may hold: fresh (`[lo, hi)`), not virtual, or of a
`Prov` value. -/
def RegOk (hi : Nat) (r : Reg) : Prop :=
  ∀ n c, r = .vreg n c → (lo ≤ n ∧ n < hi) ∨ ∃ x, Prov ctx ii x ∧ ctx.valueReg? x = some (.vreg n c)

/-- An instruction a statement's lowering may hold: the root (if `b`) or the definition of a
`Prov` value. -/
def InstOk (b : Bool) (j : Nat) : Prop :=
  (b = true ∧ j = ii) ∨ ∃ n, Prov ctx ii n ∧ ctx.defInst? n = some j

/-- A clean value. -/
def Clean (hi : Nat) (b : Bool) (v : V) : Prop :=
  (∀ r ∈ v.regsIn, RegOk ctx ii lo hi r) ∧ (∀ n ∈ v.valsIn, Prov ctx ii n) ∧
    ∀ j ∈ v.instsIn, InstOk ctx ii b j

/-- The flow meaning of an abstract value. -/
def γF (a : FA) (st : State) (v : V) : Prop :=
  (a.f = 0 → Clean ctx ii lo st.base.nextVreg false v) ∧ (a.f = 1 → Clean ctx ii lo st.base.nextVreg true v)

variable {ctx ii lo}

private theorem clean_true {hi : Nat} {v : V} (h : Clean ctx ii lo hi false v) : Clean ctx ii lo hi true v :=
  ⟨h.1, h.2.1, fun j hj => by
    rcases h.2.2 j hj with ⟨h, -⟩ | h
    · cases h
    · exact .inr h⟩

private theorem clean_mono {hi hi' : Nat} (hle : hi ≤ hi') {b : Bool} {v : V} (h : Clean ctx ii lo hi b v) :
    Clean ctx ii lo hi' b v :=
  ⟨fun r hr n c hrn => by
    rcases h.1 r hr n c hrn with h | h
    · exact .inl ⟨h.1, by omega⟩
    · exact .inr h, h.2.1, h.2.2⟩

/-- `γF` at a level `≤ l ≤ 1`, as `Clean`. -/
private theorem γF_clean {a : FA} {st : State} {v : V} (h : γF ctx ii lo a st v) {l : Nat} (hl : a.f ≤ l)
    (hl1 : l ≤ 1) : Clean ctx ii lo st.base.nextVreg (decide (l = 1)) v := by
  rcases Nat.lt_or_ge a.f 1 with h0 | h1
  · have h0 : a.f = 0 := by omega
    have := h.1 h0
    by_cases hl' : l = 1
    · simp only [hl', decide_true]; exact clean_true this
    · simp only [hl', decide_false]; exact this
  · have h1 : a.f = 1 := by omega
    have hl' : l = 1 := by omega
    simp only [hl', decide_true]
    exact h.2 h1

/-- `Clean` at the level of a decided bound gives `γF`. -/
private theorem γF_of_clean {a : FA} {st : State} {v : V}
    (h : a.f ≤ 1 → Clean ctx ii lo st.base.nextVreg (decide (a.f = 1)) v) : γF ctx ii lo a st v :=
  ⟨fun h0 => (by have := h (by omega); simpa [h0] using this),
   fun h1 => (by have := h (by omega); simpa [h1] using this)⟩

private theorem clean_noAtoms {hi : Nat} {b : Bool} {v : V} (h : NoAtoms v) : Clean ctx ii lo hi b v :=
  ⟨fun r hr => (by rw [h.1] at hr; cases hr), fun n hn => (by rw [h.2.1] at hn; cases hn),
   fun j hj => (by rw [h.2.2.1] at hj; cases hj)⟩

end FlowM

/-! ## The embedding -/

section Sem
variable (ctx : Ctx)

private theorem sem_unData_eq {ty : TypeId} {v : V} {k : Nat} {fs : List V}
    (h : (Stock.sem ctx).unData ty v = some (k, fs)) : v = .data ty k fs := by
  cases v <;> simp [Stock.sem, Backend.sem] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

private theorem sem_prim_eq {ty : TypeId} {n : String} {c : V} (h : (Stock.sem ctx).prim ty n = some c) :
    ∃ t, c = .ty t := by
  simp only [Stock.sem, Backend.sem] at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨t, -, rfl⟩ := h
    exact ⟨t, rfl⟩
  · cases h

end Sem

private theorem noAtoms_ty (t : CTy) : NoAtoms (.ty t) := ⟨rfl, rfl, rfl, rfl⟩
private theorem noAtoms_int (i : Int) : NoAtoms (.int i) := ⟨rfl, rfl, rfl, rfl⟩
private theorem noAtoms_bool (b : Bool) : NoAtoms (.bool b) := ⟨rfl, rfl, rfl, rfl⟩

private theorem clean_data {ctx : Ctx} {ii lo hi : Nat} {b : Bool} {ty : TypeId} {k : Nat} {vs : List V}
    (h : ∀ v ∈ vs, Clean ctx ii lo hi b v) : Clean ctx ii lo hi b (.data ty k vs) := by
  refine ⟨fun r hr => ?_, fun n hn => ?_, fun j hj => ?_⟩
  · obtain ⟨v, hv, hr⟩ := regsInL_mem (by simpa [V.regsIn] using hr)
    exact (h v hv).1 r hr
  · obtain ⟨v, hv, hn⟩ := valsInL_mem (by simpa [V.valsIn] using hn)
    exact (h v hv).2.1 n hn
  · obtain ⟨v, hv, hj⟩ := instsInL_mem (by simpa [V.instsIn] using hj)
    exact (h v hv).2.2 j hj

private theorem clean_field {ctx : Ctx} {ii lo hi : Nat} {b : Bool} {ty : TypeId} {k : Nat} {vs : List V}
    (h : Clean ctx ii lo hi b (.data ty k vs)) : ∀ v ∈ vs, Clean ctx ii lo hi b v := by
  intro v hv
  refine ⟨fun r hr => h.1 r ?_, fun n hn => h.2.1 n ?_, fun j hj => h.2.2 j ?_⟩
  · simpa [V.regsIn] using regsIn_sub_of_mem hv r hr
  · simpa [V.valsIn] using valsIn_sub_of_mem hv n hn
  · simpa [V.instsIn] using instsIn_sub_of_mem hv j hj

/-- The data of an instruction a clean `.inst` names: its values are `Prov`. -/
private theorem data_prov {f : Clif.Function} {ctx : Ctx} (hctx : MappedCtxInv f ctx) {ii : Nat} {b : Bool}
    {j : Nat} (hj : InstOk ctx ii b j) {info : IInfo} (hinfo : ctx.insts[j]? = some info)
    (hroot : b = true → ∀ info, ctx.insts[ii]? = some info → ∃ c, info.clif = some c) :
    info.data.regsIn = [] ∧ info.data.instsIn = [] ∧ ∀ n ∈ info.data.valsIn, Prov ctx ii n := by
  rcases hj with ⟨hb, rfl⟩ | ⟨m, hm, hd⟩
  · obtain ⟨c, hc⟩ := hroot hb info hinfo
    have hd := instData_ok (hctx.data _ _ _ hinfo hc)
    exact ⟨hd.1, hd.2.1, fun n hn => .arg hinfo hc (hd.2.2.2 n hn)⟩
  · have hcl := hctx.defClif m j info hd hinfo
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hcl
    have hdd := instData_ok (hctx.data _ _ _ hinfo hc)
    exact ⟨hdd.1, hdd.2.1, fun n hn => .dep hm hd hinfo hc (.inl (hdd.2.2.2 n hn))⟩

section FlowModel
variable {f : Clif.Function} {ctx : Ctx} (hctx : MappedCtxInv f ctx) {ii : Nat} {info : IInfo}
  {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
  (htr : ctx.tryRegs = ([], [])) {lo : Nat}

include hi hc in
private theorem root_clif : ∀ info', ctx.insts[ii]? = some info' → ∃ c, info'.clif = some c := by
  intro info' h'
  rw [hi] at h'; cases h'
  exact ⟨inst, hc⟩

private theorem γF_le (a b : FA) (st : State) (v : V) (hab : a.le b = true) (h : γF ctx ii lo a st v) :
    γF ctx ii lo b st v := by
  simp only [FA.le, Bool.and_eq_true, decide_eq_true_eq] at hab
  refine γF_of_clean fun hb => ?_
  exact γF_clean h (Nat.le_trans hab.1 (Nat.le_refl _)) hb

include hctx hi hc in
private theorem γF_ext (st : State) (a : FA) (term : Term) (v : V) (fs : List V)
    (hv : γF ctx ii lo a st v) (h : (Stock.sem ctx).extract term v st = .ok fs) :
    ∀ w ∈ fs, γF ctx ii lo (aext term.id a) st w := by
  have hs := externExtract_ok ctx term v st.base fs h
  intro w hw
  unfold aext
  split
  · rename_i hcond
    have hna := hs.c0 (by simpa [Bool.or_eq_true, List.contains_iff_mem] using hcond) w hw
    exact γF_of_clean fun _ => clean_noAtoms hna
  · split
    · rename_i _ hcond
      have hval := hs.val (by simpa [List.contains_iff_mem] using hcond) w hw
      refine γF_of_clean fun hl => ?_
      split at hl
      · rename_i hle
        have hcl := γF_clean hv (Nat.le_refl _) hle
        refine ⟨fun r hr => (by rw [hval.1] at hr; cases hr), fun n hn => ?_, fun j hj => ?_⟩
        · rcases hval.2.2.1 n hn with h1 | ⟨m, hm, j, info', c, hd, hinfo, hcl', hn'⟩
          · exact hcl.2.1 n h1
          · exact .dep (hcl.2.1 m hm) hd hinfo hcl' (.inl hn')
        · obtain ⟨m, hm, hd⟩ := hval.2.2.2 j hj
          exact .inr ⟨m, hcl.2.1 m hm, hd⟩
      · simp at hl
    · split
      · rename_i _ _ hid
        obtain ⟨i, info', rfl, hinfo, rfl⟩ := hs.idv (by simpa using hid)
        refine γF_of_clean fun hl => ?_
        split at hl
        · rename_i hle
          have hcl := γF_clean hv (Nat.le_refl _) hle
          have hinst : InstOk ctx ii (decide (a.f = 1)) i := hcl.2.2 i (by simp [V.instsIn])
          obtain ⟨h1, h2, h3⟩ := data_prov hctx hinst hinfo (fun _ => root_clif hi hc)
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact clean_noAtoms (noAtoms_ty _)
          · exact ⟨fun r hr => (by rw [h1] at hr; cases hr), h3, fun j hj => (by rw [h2] at hj; cases hj)⟩
        · simp at hl
      · split
        · rename_i _ _ _ hid
          obtain ⟨i, info', r, rfl, hinfo, hr, rfl⟩ := hs.fr (by simpa using hid)
          refine γF_of_clean fun hl => ?_
          split at hl
          · rename_i h0
            have h0 : a.f = 0 := by simpa using h0
            have hcl := hv.1 h0
            rcases hcl.2.2 i (by simp [V.instsIn]) with ⟨h, -⟩ | ⟨m, hm, hd⟩
            · cases h
            · have hcl' := hctx.defClif m i info' hd hinfo
              obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.mp hcl'
              simp only [List.mem_singleton] at hw
              subst hw
              refine ⟨fun r hr => (by simp [V.regsIn] at hr), fun n hn => ?_,
                fun j hj => (by simp [V.instsIn] at hj)⟩
              simp only [V.valsIn, List.mem_singleton] at hn
              subst hn
              exact .dep hm hd hinfo hcc (.inr (List.mem_of_head? hr))
          · simp at hl
        · refine γF_of_clean fun hl => ?_
          simp [FA.top] at hl

private theorem amk_f (ty : TypeId) (k : Nat) (as : List FA) : (amk ty k as).f = (joinAll as).f := by
  unfold amk; split <;> rfl

/-- Arguments described at a level `l ≤ 1` of their join are clean at that level. -/
private theorem args_clean {as : List FA} {vs : List V} {st : State} (h : Holds2 (γF ctx ii lo) st as vs)
    (hl : (joinAll as).f ≤ 1) :
    ∀ w ∈ vs, Clean ctx ii lo st.base.nextVreg (decide ((joinAll as).f = 1)) w := by
  intro w hw
  obtain ⟨a, ha, hw⟩ := holds2_mem h w hw
  exact γF_clean hw (joinAll_f (Nat.le_refl _) a ha) hl

include htr in
private theorem γF_ctor (st : State) (as : List FA) (vs : List V) (term : Term) (v : V) (st' : State)
    (hvs : Holds2 (γF ctx ii lo) st as vs) (hlo : lo ≤ st.base.nextVreg)
    (h : (Stock.sem ctx).ctor term vs st = .ok (v, st')) :
    γF ctx ii lo (actor term.id as) st' v ∧ lo ≤ st'.base.nextVreg := by
  have mono := (stock_ctor_allocationLe h).1
  refine ⟨?_, Nat.le_trans hlo mono⟩
  unfold actor
  split
  · exact γF_of_clean fun hl => by simp at hl
  · rename_i hid
    refine γF_of_clean fun hl => ?_
    have hargs := args_clean hvs hl
    refine ⟨fun r hr => ?_, fun n hn => ?_, fun j hj => ?_⟩
    · have origin := stock_ctor_output_origin htr h r hr
      rcases origin with old | ⟨n, c, rfl, lower, upper⟩ | ⟨x, hx, mapped⟩ | physical | invalid
      · obtain ⟨w, hw, hrw⟩ := regsInL_mem old
        intro n c eq
        rcases (hargs w hw).1 r hrw n c eq with fresh | source
        · exact .inl ⟨fresh.1, Nat.lt_of_lt_of_le fresh.2 mono⟩
        · exact .inr source
      · intro n' c' eq
        cases eq
        exact .inl ⟨Nat.le_trans hlo lower, upper⟩
      · obtain ⟨w, hw, hxw⟩ := valsInL_mem hx
        intro n c eq
        subst r
        exact .inr ⟨x, (hargs w hw).2.1 x hxw, mapped⟩
      · intro n c eq; exact absurd eq (physical n c)
      · exact absurd (beq_iff_eq.mpr invalid) hid
    · obtain ⟨w, hw, hnw⟩ := valsInL_mem (stock_ctor_output_values h n hn)
      exact (hargs w hw).2.1 n hnw
    · rcases stock_ctor_output_instructions h j hj with old | ⟨x, hx, defined⟩
      · obtain ⟨w, hw, hjw⟩ := instsInL_mem old
        exact (hargs w hw).2.2 j hjw
      · obtain ⟨w, hw, hxw⟩ := valsInL_mem hx
        exact .inr ⟨x, (hargs w hw).2.1 x hxw, defined⟩

/-- **The flow model** of a statement `ii`'s lowering from a state whose counter is `lo`. -/
def flowModel : Model (Stock.sem ctx) false where
  γ := γF ctx ii lo
  Is := fun st => lo ≤ st.base.nextVreg
  Rs := fun s s' => s.base.nextVreg ≤ s'.base.nextVreg
  rs_refl := fun _ => Nat.le_refl _
  rs_trans := fun _ _ _ h1 h2 => Nat.le_trans h1 h2
  rs_ctor := fun term vs s v s' h => (stock_ctor_allocationLe h).1
  top := fun _ _ => γF_of_clean fun hl => by simp [FA.top] at hl
  le := γF_le
  mono := fun _ _ _ _ h hv => ⟨fun h0 => clean_mono h (hv.1 h0), fun h1 => clean_mono h (hv.2 h1)⟩
  int := fun _ _ _ => γF_of_clean fun _ => clean_noAtoms (noAtoms_int _)
  bool := fun _ _ => γF_of_clean fun _ => clean_noAtoms (noAtoms_bool _)
  prim := fun _ _ _ _ h => by
    obtain ⟨t, rfl⟩ := sem_prim_eq ctx h
    exact γF_of_clean fun _ => clean_noAtoms (noAtoms_ty _)
  mkd := fun st ty k as vs h => by
    refine γF_of_clean fun hl => ?_
    rw [amk_f] at hl ⊢
    exact clean_data (args_clean h hl)
  un := fun st a ty v k fs hv hu => by
    have := sem_unData_eq ctx hu
    subst this
    intro w hw
    exact γF_of_clean fun hl => clean_field (γF_clean hv (Nat.le_refl _) hl) w hw
  ext := γF_ext hctx hi hc
  ctor := fun st as vs term v st' hvs hIs _ h => γF_ctor htr st as vs term v st' hvs hIs h

end FlowModel

/-- The existing checked abstract-flow table is sound for actual stock ISLE
helper execution with mapped source provenance and successful sinking. The
check is a property of exported rule data, not an accepted-input condition. -/
theorem stock_apply_mapped_flow {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (empty : ctx.tryRegs = ([], []))
    {root : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[root]? = some info) (original : info.clif = some inst)
    {lo fuel ty term : Nat} {as : List FA} {a : FA} {args : List V}
    {before after : State} {out : V} {trace finalTrace : Array RuleId}
    (checked : aApply program flowTab false ty term as = some a)
    (inputs : Holds2 (γF ctx root lo) before as args)
    (lower : lo ≤ before.base.nextVreg)
    (run : (applyTerm program (Stock.sem ctx) {} fuel ty term args).run (before, trace) =
      .ok (some out, (after, finalTrace))) :
    lo ≤ after.base.nextVreg ∧ γF ctx root lo a after out := by
  have result := (soundAt (flowModel mapped source original empty) (cfg := {})
    rfl flowTab_ok fuel).apply ty term as a args before trace (some out) after finalTrace
      checked inputs lower run
  exact ⟨result.1, result.2 out rfl⟩

private def modelFunction : Clif.Function := {
  name := "mapped_source_flow"
  sig := { returns := [⟨.i8, .none, .normal⟩] }
  blocks := [{ id := 0, params := [], body := [⟨[0], .iconst .i64 9⟩, ⟨[1], .ireduce .i8 0⟩], term := .ret [1] }] }
private def modelBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx modelFunction).toOption.getD (sinkCtx, #[], sinkState)

set_option maxRecDepth 4096 in
private theorem model_build : Stock.buildCtx modelFunction = .ok modelBuilt := rfl
set_option maxRecDepth 4096 in
private theorem model_scope : LowerScope modelFunction := lowerScope_of (by decide +kernel)
private theorem model_mapped : MappedCtxInv modelFunction modelBuilt.1 :=
  buildCtx_mappedInv model_scope model_build
set_option maxRecDepth 4096 in
private theorem model_info : modelBuilt.1.insts[1]? = some modelBuilt.1.insts[1]! := rfl
set_option maxRecDepth 4096 in
private theorem model_original : modelBuilt.1.insts[1]!.clif = some (.ireduce .i8 0) := rfl

set_option maxRecDepth 4096 in
/-- An actual built source context has root reduction1 reaching source value0,
whose allocated register is192. The actual stock helper marks the source used
and returns192; the checked mapped-flow theorem certifies that output. -/
theorem stock_apply_mapped_flow_witness :
    Stock.buildCtx modelFunction = .ok modelBuilt ∧
      modelBuilt.1.valueReg? 0 = some (.vreg 192 .int) ∧
      γF modelBuilt.1 1 modelBuilt.2.2.base.nextVreg FA.c0 (modelBuilt.2.2.mark 0)
        (.reg (.vreg 192 .int)) := by
  refine ⟨model_build, rfl, ?_⟩
  have sourceProv : Prov modelBuilt.1 1 0 :=
    .arg model_info model_original (by decide)
  have input : Holds2 (γF modelBuilt.1 1 modelBuilt.2.2.base.nextVreg)
      modelBuilt.2.2 [FA.c0] [.value 0] := by
    refine ⟨γF_of_clean (fun _ => ?_), trivial⟩
    refine ⟨fun r hr => (by cases hr), ?_, fun j hj => (by cases hj)⟩
    intro n hn
    simp only [V.valsIn, List.mem_singleton] at hn
    subst n
    exact sourceProv
  have checked : aApply program flowTab false T.put_in_reg.ret T.put_in_reg.id [FA.c0] =
      some FA.c0 := by
    simp only [aApply, data_program.t182, T.put_in_reg]
    rfl
  have run : (applyTerm program (Stock.sem modelBuilt.1) {} 1
      T.put_in_reg.ret T.put_in_reg.id [.value 0]).run (modelBuilt.2.2, #[]) =
      .ok (some (.reg (.vreg 192 .int)), (modelBuilt.2.2.mark 0, #[])) := by
    simp only [applyTerm.eq_2, data_program.t182, T.put_in_reg]
    rfl
  exact (stock_apply_mapped_flow model_mapped rfl model_info model_original
    checked input (Nat.le_refl _) run).2

end Backend.Stock.Proof.MappedFlow
