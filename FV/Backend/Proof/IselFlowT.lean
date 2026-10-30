import FV.Backend.Proof.IselFlow
import FV.Backend.Proof.IselExclT

/-!
# What the ISLE lowering of one instruction can produce, over float-capable contexts

`IselFlow`'s facts (`stmt_flow`, `stmt_noTls`, `termCall_noTls`, `tryCall_noTls`) over
float-capable contexts (`CtxInvT`, instructions in the typed scope `InstScopeT`, externs with
integer signatures). The abstract interpretation is the same (`flowTab`, `tlsTab`, decided once
over the exported rules); what changes is the meaning of the context:

* `flowModelT`: `flowModel` over `CtxInvT` (a value's vreg has its value's class);
* the root rules outside the closure cannot match (`lower_nonroot_nomatchT`, the typed checker),
  and `nop`'s/`tls_value`'s pinned opcodes name the instruction (`pinned_namesT`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

/-- The data of an instruction a clean `.inst` names: its values are `Prov` (`data_prov` over
`CtxInvT`). -/
theorem data_provT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat} {b : Bool}
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

section FlowModelT
variable {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat} {info : IInfo}
  {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
  (htr : ctx.tryRegs = ([], [])) {lo : Nat}

include hctx hi hc in
theorem γF_extT (st : LState) (a : FA) (term : Term) (v : V) (fs : List V)
    (hv : γF ctx ii lo a st v) (h : (sem ctx).extract term v st = .ok fs) :
    ∀ w ∈ fs, γF ctx ii lo (aext term.id a) st w := by
  have hs := externExtract_ok ctx term v st fs h
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
          obtain ⟨h1, h2, h3⟩ := data_provT hctx hinst hinfo (fun _ => root_clif hi hc)
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

include hctx htr in
theorem γF_ctorT (st : LState) (as : List FA) (vs : List V) (term : Term) (v : V) (st' : LState)
    (hvs : Holds2 (γF ctx ii lo) st as vs) (hlo : lo ≤ st.nextVreg)
    (h : (sem ctx).ctor term vs st = .ok (v, st')) :
    γF ctx ii lo (actor term.id as) st' v ∧ lo ≤ st'.nextVreg := by
  have hok := externCtor_ok ctx term vs st v st' h
  refine ⟨?_, Nat.le_trans hlo hok.vreg⟩
  unfold actor
  split
  · exact γF_of_clean fun hl => by simp at hl
  · rename_i hid
    refine γF_of_clean fun hl => ?_
    have hargs := args_clean hvs hl
    refine ⟨fun r hr => ?_, fun n hn => ?_, fun j hj => ?_⟩
    · rcases hok.regs r hr with h1 | ⟨n, c, rfl, h2, h3⟩ | ⟨x, hx, h4⟩ | h5 | h6 | h7 | h7
      · obtain ⟨w, hw, hrw⟩ := regsInL_mem h1
        intro n c hrn
        rcases (hargs w hw).1 r hrw n c hrn with h | h
        · exact .inl ⟨h.1, Nat.lt_of_lt_of_le h.2 hok.vreg⟩
        · exact .inr h
      · intro n' c' he
        cases he
        exact .inl ⟨Nat.le_trans hlo h2, h3⟩
      · obtain ⟨w, hw, hxw⟩ := valsInL_mem hx
        have hp := (hargs w hw).2.1 x hxw
        have := hctx.valueReg x r h4
        subst this
        intro n c he
        cases he
        exact .inr hp
      · intro n c he; exact absurd he (h5 n c)
      · exact absurd (beq_iff_eq.mpr h6) hid
      · rw [htr] at h7; cases h7
      · rw [htr] at h7; cases h7
    · obtain ⟨w, hw, hnw⟩ := valsInL_mem (hok.vals n hn)
      exact (hargs w hw).2.1 n hnw
    · obtain ⟨w, hw, hjw⟩ := instsInL_mem (hok.insts j hj)
      exact (hargs w hw).2.2 j hjw

/-- **The flow model** of a statement `ii`'s lowering from a state whose counter is `lo`, in a
float-capable context (`flowModel` over `CtxInvT`). -/
def flowModelT : Model (sem ctx) false where
  γ := γF ctx ii lo
  Is := fun st => lo ≤ st.nextVreg
  Rs := fun s s' => s.nextVreg ≤ s'.nextVreg
  rs_refl := fun _ => Nat.le_refl _
  rs_trans := fun _ _ _ h1 h2 => Nat.le_trans h1 h2
  rs_ctor := fun term vs s v s' h => (externCtor_ok ctx term vs s v s' h).vreg
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
  ext := γF_extT hctx hi hc
  ctor := fun st as vs term v st' hvs hIs _ h => γF_ctorT hctx htr st as vs term v st' hvs hIs h

end FlowModelT

/-! ## The statements -/

section
variable {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hsc : InstScopeT ctx)
  (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
include hctx

set_option maxRecDepth 100000 in
/-- The opcode of a statement whose rule pinned opcode `o` (not a float constant's). -/
theorem pinned_namesT {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {r : Rule} {fT oT : Nat} (hq : rootOp r = some (fT, oT)) {kf o : Nat}
    (hk : (match termOf program fT with | .ok t => t.kind == .enumVariant kf | .error _ => false) = true)
    (ho : (match termOf program oT with | .ok t => t.kind == .enumVariant o | .error _ => false) = true)
    (hof : o ≠ 59 ∧ o ≠ 60)
    {m : Nat} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    (h : (matchRule program (sem ctx) {} m r [.inst ii]).run s = .ok (some env, s1)) :
    (variantNames 151)[o]? = some (instNames inst).2 := by
  obtain ⟨tf, htf, hkf⟩ := kind_of hk
  obtain ⟨to, hto, hko⟩ := kind_of ho
  obtain ⟨info', fs, hi', hd⟩ := rootOp_match hq htf hkf hto hko h
  rw [hi] at hi'; cases hi'
  have := hctx.data ii info inst hi hc
  rw [hd] at this
  exact (instData_inv_names this (.inr hof)).2

/-- The data of the root statement and of defining instructions is safe (`stmt_root_safe` over
`CtxInvT`). -/
theorem stmt_root_safeT {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) :
    ∀ j info', (j = ii ∨ ∃ n, ctx.defInst? n = some j) → ctx.insts[j]? = some info' →
      info'.data.tlsIn = false ∧ info'.data.instsIn = [] := by
  intro j info' hj hinfo
  rcases hj with rfl | ⟨n, hd⟩
  · rw [hi] at hinfo; cases hinfo
    have := instData_ok (hctx.data _ _ _ hi hc)
    exact ⟨this.2.2.1, this.2.1⟩
  · obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.mp (hctx.defClif n j info' hd hinfo)
    have := instData_ok (hctx.data _ _ _ hinfo hcc)
    exact ⟨this.2.2.1, this.2.1⟩

/-- The data of a terminator's slot and of defining instructions is safe (`term_root_safe` over
`CtxInvT`). -/
theorem term_root_safeT {ti : Nat} (hti : ti < ctx.insts.size) {data : V}
    (hdat : data.tlsIn = false ∧ data.instsIn = [])
    (ctx' : Ctx) (hins : ctx'.insts = (termCtx ctx ti data).insts) (hdef : ctx'.valDef = ctx.valDef) :
    ∀ j info', (j = ti ∨ ∃ n, ctx'.defInst? n = some j) → ctx'.insts[j]? = some info' →
      info'.data.tlsIn = false ∧ info'.data.instsIn = [] := by
  intro j info' hj hinfo
  rw [hins] at hinfo
  by_cases hjt : j = ti
  · subst hjt
    rw [termCtx_self hti] at hinfo; cases hinfo
    exact hdat
  · rw [termCtx_insts_ne hjt] at hinfo
    rcases hj with h | ⟨n, hd⟩
    · exact absurd h hjt
    · have hd' : ctx.defInst? n = some j := by
        unfold Ctx.defInst? at hd ⊢; rw [hdef] at hd; exact hd
      obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.mp (hctx.defClif n j info' hd' hinfo)
      have := instData_ok (hctx.data _ _ _ hinfo hcc)
      exact ⟨this.2.2.1, this.2.1⟩

omit hctx in
/-- The root rules of `lower` outside the closure never match an instruction of `ctx`
(`lower_nonroot_nomatchT` on the typed scope, `lower_nonroot_nomatchTF_calls` on the float
scope). -/
def LowerNoMatch (ctx : Ctx) : Prop :=
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst → ∀ r ∈ program.rulesOf TId.lower, closureRootIds.contains r.id = false →
    ∀ cfg m s0 env s1, (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env, s1)

include hsc hx in
theorem lowerNoMatch_ofT : LowerNoMatch ctx :=
  fun _ _ _ hi hc _ hr hroot => lower_nonroot_nomatchT hctx hsc hx hi hc hr hroot

set_option maxRecDepth 100000 in
/-- **The result registers of a statement's lowering** (`stmt_flowT` over `LowerNoMatch`). -/
theorem stmt_flowG (hnm : LowerNoMatch ctx) (htr : ctx.tryRegs = ([], [])) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) {s : LState} {out : V}
    {s' : LState} {tr : List Isle.RuleId} (h : runTerm ctx "lower" [.inst ii] s = .ok (some out, s', tr)) :
    ∀ rss, out = .regsVec rss → info.results ≠ [] → ∀ rs ∈ rss, ∀ o cls, rs = [.vreg o cls] →
      (s.nextVreg ≤ o ∧ o < s'.nextVreg) ∨ Prov ctx ii o := by
  intro rss hout hres rs hrs o cls hrso
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program flowTab false [⟨1, true⟩] ⟨1, false⟩ rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp flowRoot_ok rl hrl
    have hop := List.all_eq_true.mp lower_ops rl hrl
    simp only [flowRootOk, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hf
    rcases hf with (hcr | h587) | ha
    · exact .inr (hnm ii info inst hi hc rl hrl hcr {})
    · refine .inr fun m s0 env s1 hm => hres ?_
      simp only [h587, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hop
      have hn := pinned_namesT hctx hi hc hop.1 kind_nullAry kind_nop (by decide) hm
      rw [variantNames_Nop] at hn
      have hnop := instNames_nop (Option.some.inj hn).symm
      subst hnop
      obtain ⟨tys, hty, -, hlen⟩ := hctx.resTys ii info .nop hi hc
      simp [Clif.Inst.resultTypes] at hty
      subst hty
      exact List.eq_nil_of_length_eq_zero hlen
    · exact .inl ha
  have hins : Holds2 (γF ctx ii s.nextVreg) s [⟨1, true⟩] [.inst ii] :=
    ⟨γF_of_clean fun _ => ⟨fun r hr => by simp [V.regsIn] at hr, fun n hn => by simp [V.valsIn] at hn,
      fun j hj => .inl ⟨by simp, by simpa [V.instsIn] using hj⟩⟩, trivial⟩
  obtain ⟨-, hv⟩ := (soundAt (flowModelT hctx hi hc htr (lo := s.nextVreg)) (cfg := {}) rfl
    flowTab_ok 1000000).root T.lower.ret T.lower.id T.lower _ _ [⟨1, true⟩] ⟨1, false⟩ [.inst ii] s #[]
    (some out) s' tr' data_program.t686 term_686_kind hrules hins (Nat.le_refl _) happ
  have hcl := (hv out rfl).2 rfl
  subst hout
  exact hcl.1 (.vreg o cls) (mem_regsVec hrs (by rw [hrso]; exact List.mem_singleton_self _)) o cls rfl

include hsc hx in
/-- **The result registers of a statement's lowering** (float-capable context): each is a fresh
vreg of the call or the register of a value the instruction reaches through its operands. -/
theorem stmt_flowT (htr : ctx.tryRegs = ([], [])) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst) {s : LState} {out : V}
    {s' : LState} {tr : List Isle.RuleId} (h : runTerm ctx "lower" [.inst ii] s = .ok (some out, s', tr)) :
    ∀ rss, out = .regsVec rss → info.results ≠ [] → ∀ rs ∈ rss, ∀ o cls, rs = [.vreg o cls] →
      (s.nextVreg ≤ o ∧ o < s'.nextVreg) ∨ Prov ctx ii o :=
  stmt_flowG hctx (lowerNoMatch_ofT hctx hsc hx) htr hi hc h

set_option maxRecDepth 100000 in
/-- Only the lowering of a `tls_value` emits an `ElfTlsGetAddr` (`stmt_noTlsT` over
`LowerNoMatch`). -/
theorem stmt_noTlsG (hnm : LowerNoMatch ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hnt : ∀ ty gv, inst ≠ .tlsValue ty gv) {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower] at ht
  cases ht
  have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
      aRule program tlsTab true [⟨2, true⟩] FA.top rl = true ∨
        ∀ m s0 env s1, (matchRule program (sem ctx) {} m rl [.inst ii]).run s0 ≠ .ok (some env, s1) := by
    intro rl hrl
    have hf := List.all_eq_true.mp tlsRoot_ok rl hrl
    have hop := List.all_eq_true.mp lower_ops rl hrl
    simp only [tlsRootOk, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hf
    rcases hf with ((hcr | h1) | h1) | ha
    · exact .inr (hnm ii info inst hi hc rl hrl hcr {})
    all_goals try exact .inl ha
    all_goals
      refine .inr fun m s0 env s1 hm => ?_
      simp only [h1, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hop
      have hq : rootOp rl = some (2478, 2334) := by
        rcases hop.2 with h | h
        · simp at h
        · exact h
      have hn := pinned_namesT hctx hi hc hq kind_ugv kind_tls (by decide) hm
      rw [variantNames_Tls] at hn
      obtain ⟨ty, gv, rfl⟩ := instNames_tls (Option.some.inj hn).symm
      exact hnt ty gv rfl
  have hins : Holds2 (γT ctx ii) s [⟨2, true⟩] [.inst ii] :=
    ⟨fun _ => ⟨rfl, fun j hj => .inl (by simpa [V.instsIn] using hj)⟩, trivial⟩
  obtain ⟨hIs, -⟩ := (soundAt (tlsModel (stmt_root_safeT hctx hi hc) s) (cfg := {}) rfl
    tlsTab_ok 1000000).root T.lower.ret T.lower.id T.lower _ _ [⟨2, true⟩] FA.top [.inst ii] s #[]
    out s' tr' data_program.t686 term_686_kind hrules hins ⟨[], by simp, by simp⟩ happ
  exact noTls_of hIs

include hsc hx in
/-- Only the lowering of a `tls_value` emits an `ElfTlsGetAddr` (float-capable context). -/
theorem stmt_noTlsT {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hnt : ∀ ty gv, inst ≠ .tlsValue ty gv) {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp :=
  stmt_noTlsG hctx (lowerNoMatch_ofT hctx hsc hx) hi hc hnt h

set_option maxRecDepth 100000 in
/-- `lower_branch` from a safe terminator slot: nothing emitted is an `ElfTlsGetAddr`
(`branch_noTls` over `CtxInvT`). -/
theorem branch_noTlsT {ti : Nat} (hti : ti < ctx.insts.size) {data : V}
    (hdat : data.tlsIn = false ∧ data.instsIn = [])
    (ctx' : Ctx) (hins' : ctx'.insts = (termCtx ctx ti data).insts) (hdef : ctx'.valDef = ctx.valDef)
    {targets : List Label} {s : LState} {out : Option V} {s' : LState} {tr : List Isle.RuleId}
    (h : runTerm ctx' "lower_branch" [.inst ti, .labels targets] s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
  obtain ⟨t, tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  have hins : Holds2 (γT ctx' ti) s [⟨2, true⟩, ⟨2, true⟩] [.inst ti, .labels targets] :=
    ⟨fun _ => ⟨rfl, fun j hj => .inl (by simpa [V.instsIn] using hj)⟩,
     fun _ => ⟨rfl, fun j hj => by simp [V.instsIn] at hj⟩, trivial⟩
  obtain ⟨hIs, -⟩ := (soundAt (tlsModel (term_root_safeT hctx hti hdat ctx' hins' hdef) s)
    (cfg := {}) rfl tlsTab_ok 1000000).root T.lower_branch.ret T.lower_branch.id T.lower_branch _ _
    [⟨2, true⟩, ⟨2, true⟩] FA.top _ s #[] out s' tr' data_program.t687 term_687_kind
    (fun rl hrl => .inl (List.all_eq_true.mp tlsRootBranch_ok rl hrl)) hins ⟨[], by simp, by simp⟩ happ
  exact noTls_of hIs

set_option maxRecDepth 100000 in
/-- A terminator's lowering emits no `ElfTlsGetAddr` (`termCall_noTls` over `CtxInvT`). -/
theorem termCall_noTlsT {ti : Nat} (hti : ti < ctx.insts.size) {t : Clif.Terminator} {data : V}
    (hd : termData (abiTerm f t) = .ok data) {targets : List Label} {s : LState} {out : Option V}
    {s' : LState} {tr : List Isle.RuleId} (h : termCallF ctx ti data t targets s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
  have hdok := termData_ok hd
  have hdat : data.tlsIn = false ∧ data.instsIn = [] := ⟨hdok.2.2.1, hdok.2.1⟩
  unfold termCallF at h
  have hlower : retOrTrap (abiTerm f t) = true →
      runTerm (termCtx ctx ti data) "lower" [.inst ti] s = .ok (out, s', tr) →
      ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
        ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
    intro hrt h
    obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
    rw [program_termByName_lower] at ht
    cases ht
    have hslot := termCtx_self hti data
    have hrules : ∀ rl ∈ program.rulesOf T.lower.id,
        aRule program tlsTab true [⟨2, true⟩] FA.top rl = true ∨
          ∀ m s0 env s1, (matchRule program (sem (termCtx ctx ti data)) {} m rl [.inst ti]).run s0 ≠
            .ok (some env, s1) := by
      intro rl hrl
      cases hroot : termRootRule rl with
      | false => exact .inr (lower_term_nomatch hrt hd hslot hrl hroot)
      | true =>
        have hf := List.all_eq_true.mp tlsRoot_ok rl hrl
        simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
        simp only [tlsRootOk] at hf
        rcases hroot with h1 | h1 <;> rw [h1] at hf <;>
          exact .inl (by simpa (config := { decide := true }) using hf)
    have hins : Holds2 (γT (termCtx ctx ti data) ti) s [⟨2, true⟩] [.inst ti] :=
      ⟨fun _ => ⟨rfl, fun j hj => .inl (by simpa [V.instsIn] using hj)⟩, trivial⟩
    obtain ⟨hIs, -⟩ := (soundAt (tlsModel (term_root_safeT hctx hti hdat (termCtx ctx ti data) rfl rfl) s)
      (cfg := {}) rfl tlsTab_ok 1000000).root T.lower.ret T.lower.id T.lower _ _ [⟨2, true⟩] FA.top
      [.inst ti] s #[] out s' tr' data_program.t686 term_686_kind hrules hins ⟨[], by simp, by simp⟩ happ
    exact noTls_of hIs
  cases t with
  | ret vs => exact hlower rfl h
  | trap c => exact hlower rfl h
  | jump bc => exact branch_noTlsT hctx hti hdat _ rfl rfl h
  | brif c a b => exact branch_noTlsT hctx hti hdat _ rfl rfl h
  | brTable x d tb => exact branch_noTlsT hctx hti hdat _ rfl rfl h
  | returnCall fn args => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCall fn args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd
  | tryCallIndirect callee args et => simp [abiTerm, termData, throw, throwThe, MonadExceptOf.throw] at hd

set_option maxRecDepth 100000 in
/-- A `try_call`'s lowering emits no `ElfTlsGetAddr` (`tryCall_noTls` over `CtxInvT`). -/
theorem tryCall_noTlsT {ti : Nat} (hti : ti < ctx.insts.size) {t : Clif.Terminator} {data : V}
    (hd : tryCallData f t = .ok data)
    {trs : List Reg × List Reg} {targets : List Label} {s : LState} {out : Option V} {s' : LState}
    {tr : List Isle.RuleId} (h : tryCallF ctx ti data trs targets s = .ok (out, s', tr)) :
    ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧
      ∀ m ∈ ms, ∀ sym rd tmp, m ≠ .elfTlsGetAddr sym rd tmp := by
  have hdok := tryCallData_ok hd
  exact branch_noTlsT hctx hti ⟨hdok.2.2.1, hdok.2.1⟩ (tryCtx ctx ti data trs) rfl rfl h

end

end Backend.Proof.Driver
