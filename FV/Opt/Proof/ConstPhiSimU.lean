import FV.Opt.Proof.ConstPhiSim
import FV.Opt.Proof.UnreachableU
import FV.Opt.Proof.Pipeline

/-!
# Constant-phi removal is sound with handler edges (#990): `Opt.ConstPhi.run_simU`

`cpOk_simX` (`FV/Opt/Proof/ConstPhiSim.lean`) with the handler edges of `IsSimU`: the target's
exception table is the source's renamed with the removed positions dropped
(`filterEt (keepMap m f) (et.mapVals (rename m))`), so the same tags catch the same exceptions
(`catch?_filterEt`), the handler successor is the same block, and its kept arguments are the
renamed values (read alike) or the payload bound at each side's fresh value (equal windows,
`Opt.Win`); a removed position passes a value renaming to the solution, as on every edge
(`cpOk`'s `edgesOk` covers the handler edges). The fresh values of the two sides are not
compared: like the `try_call` results, the payload is bound at each side's own fresh value
above every value the relation reads.

`run_facts`: the pass keeps the facts of the output the backend theorem uses
(`Opt.BackendFacts`), and the signature declarations.
-/

namespace Opt.ConstPhi

open Clif Opt

/-! ## Handler successors -/

theorem catch?_filterEt (k : Std.HashMap BlockId (List Bool)) (et : ExnTable) (e : Exn) :
    (filterEt k et).catch? e = (et.catch? e).map (filterTD k) := by
  unfold ExnTable.catch? filterEt
  simp only
  generalize et.items = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | tag n d =>
      simp only [List.map_cons, List.findSome?_cons]
      cases e.catches n
      · simpa using ih
      · simp
    | default d => simp
    | context v =>
      simp only [List.map_cons, List.findSome?_cons]
      exact ih

theorem resolveH_filt (b : ValueId) :
    ∀ (ks : List Bool) (l : List TryArg) {xs : List ValueId}, resolveH b l = .ok xs →
      resolveH b (filt ks l) = .ok (filt ks xs)
  | [], l, xs, h => h
  | _ :: _, [], xs, h => by simp only [resolveH] at h; cases h; rfl
  | k :: ks, a :: l, xs, h => by
    simp only [resolveH, Res.bind_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    have ih := resolveH_filt b ks l hxs
    cases k
    · simpa [filt] using ih
    · simp only [filt, ite_true, resolveH, hx, ih]; rfl

theorem resolveH_val (b : ValueId) :
    ∀ (l : List TryArg) {xs : List ValueId}, resolveH b l = .ok xs →
      ∀ (n : Nat) x, l[n]? = some (TryArg.val x) → xs[n]? = some x
  | [], xs, _, n, x, hn => by simp at hn
  | a :: l, xs, h, n, x, hn => by
    simp only [resolveH, Res.bind_eq_ok, Res.pure_eq_ok] at h
    obtain ⟨y, hy, xs', hxs, rfl⟩ := h
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      simp only [Res.pure_eq_ok] at hy
      simp [hy]
    | succ n => simpa using resolveH_val b l hxs n x (by simpa using hn)

theorem tryHandler_filter (k : Std.HashMap BlockId (List Bool)) {d : TryDest} {b : ValueId}
    {bc : BlockCall} (h : tryHandler d b = .ok bc) :
    tryHandler (filterTD k d) b = .ok { bc with args := filt (keepOf k bc.block) bc.args } := by
  rw [tryHandler_eq] at h ⊢
  simp only [Res.bind_eq_ok, Res.pure_eq_ok] at h
  obtain ⟨args, ha, rfl⟩ := h
  simp only [filterTD, resolveH_filt b _ _ ha, Res.ok_bind]
  rfl

/-! ## Handler edges -/

theorem handlers_edge {et : ExnTable} {d : TryDest} (hd : d ∈ et.handlers) :
    (d.block, d.args.map argVal) ∈ et.dests.map fun d => (d.block, d.args.map argVal) :=
  List.mem_map.2 ⟨d, List.mem_append_left _ hd, rfl⟩

section
variable {m : Std.HashMap ValueId ValueId} {f : Function} {D : WfData} (hF : CpFacts m f D)
  {syms : String → Option Nat}
include hF

/-- After a `try_call`'s callee unwinds: the tables catch alike and the frames resumed at a
handler enter related blocks, the target with the kept arguments. -/
theorem CRel.hcont {fr fr' : Frame} {bi k : Nat} (h : CRel m f D syms fr fr' bi k)
    (hs : fr.body = []) (hw : Win fr fr') {et : ExnTable}
    (hedge : ∀ d ∈ et.handlers, (d.block, d.args.map argVal) ∈ edges fr.term)
    (hsucc : ∀ d ∈ et.handlers, d.block ∈ termSuccs fr.term)
    (hvals : ∀ d ∈ et.handlers, ∀ x ∈ d.vals, x ∈ termOperands fr.term) :
    HCont (CR m f D syms) fr et fr' (filterEt (keepMap m f) (et.mapVals (rename m))) := by
  have hf := h.inv.func
  have hg := h.func
  have hT := h.termOps hF hs
  intro e
  refine ⟨fun hn => ?_, fun fr1 hc => ?_⟩
  · rw [catchIn_eq_none] at hn ⊢
    rw [catch?_filterEt, catch?_mapVals, hn]; rfl
  · obtain ⟨d, bc, regs, hd, hbc, hset, rfl⟩ := catchIn_ok hc
    have hdm := catch?_mem hd
    have hbc0 := hbc
    rw [tryHandler_eq] at hbc0
    simp only [Res.bind_eq_ok, Res.pure_eq_ok] at hbc0
    obtain ⟨bargs, hres, rfl⟩ := hbc0
    obtain ⟨bc2, hbc2, hblk, hpw⟩ := tryHandler_pair (rename m) (b2 := fr'.func.freshValue) hbc
    have hbc' := tryHandler_filter (keepMap m f) hbc2
    obtain ⟨regs', hset'⟩ := setMany_len (r := fr'.regs)
      (xs := (List.range e.payload.length).map (fr'.func.freshValue + ·)) (vs := e.payload)
      (by simp)
    have hd' : (filterEt (keepMap m f) (et.mapVals (rename m))).catch? e =
        some (filterTD (keepMap m f) (d.mapVals (rename m))) := by
      rw [catch?_filterEt, catch?_mapVals, hd]; rfl
    refine ⟨_, catchIn_of hd' hbc' hset', rfl, rfl, _, _, rfl, rfl, fun fr1 he1 => ?_⟩
    have he1' : enterBlock { fr with regs } ⟨d.block, bargs⟩ = .ok fr1 := by
      rw [← enterBlock_bt { fr with regs } [] (.jump ⟨d.block, bargs⟩)]; exact he1
    have hW := setMany_tryRets (n := e.payload.length) (W := fr.func.freshValue) hset
    have hW' := setMany_tryRets (n := e.payload.length) (W := fr'.func.freshValue) hset'
    have hlo : ∀ v < f.freshValue, regs v = fr.regs v := catch_regs_lo hset (by rw [hf])
    have hlo' : ∀ v < (cpFun m f).freshValue, regs' v = fr'.regs v := catch_regs_lo hset' (by rw [hg])
    have hinvA : Inv f D syms { fr with regs } bi k := h.inv.regs_congr hF.wf hlo
    have hagreeA : ∀ v, Avail D bi k v →
        ({ fr' with regs := regs' } : Frame).regs (rename m v) = ({ fr with regs } : Frame).regs v := by
      intro v hv
      show regs' _ = regs _
      rw [hlo' _ (rename_lt hF hv), hlo _ (avail_lt hF.wf hv)]
      exact h.agree v hv
    obtain ⟨fr1', he1'', hr1⟩ := enterAt (fr' := { fr' with regs := regs' })
      (bc' := { block := bc2.block, args := filt (keepOf (keepMap m f) bc2.block) bc2.args })
      hF hinvA hs hg h.slots hagreeA (hsucc d hdm) he1' (by simpa using hblk) (by
        intro vs1 hga
        refine ⟨?_, fun b2 hb2 i p hp hc => ?_⟩
        · have hga' : Frame.getMany { fr' with regs := regs' } bc2.args = .ok vs1 := by
            refine getMany_pw2 (A := { fr with regs }) (hpw.imp fun x y hxy => ?_) hga
            simp only
            rcases hxy with ⟨v, hv, hx, hy⟩ | ⟨i, hx, hy⟩
            · rw [hx, hy]
              obtain ⟨h1, h2, h3⟩ := hT v (hvals d hdm v hv)
              rw [hlo' _ h3, hlo _ h2, h1]
            · rw [hx, hy, hW i, hW' i]
              split
              · rfl
              · exact (hw i).symm
          rw [hblk]
          exact getMany_filt _ _ hga'
        · obtain ⟨j, hj, hid⟩ := block?_index hF.wf hb2
          have hid' : b2.id = d.block := hid
          have hidx : D.index d.block = some j := by rw [← hid']; exact hF.wf.ids j b2 hj
          obtain ⟨bb, hbi, -, hterm⟩ := inv_atEnd h.inv hs
          have hedge' := hedge d hdm
          rw [hterm] at hedge'
          obtain ⟨hlen, hpos⟩ := hF.edge bi bb hbi _ hedge' j b2 hidx hj
          have hn : i < d.args.length := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp only [List.length_map] at hlen; omega
          have hx0 : d.args[i]? = some d.args[i] := List.getElem?_eq_getElem hn
          obtain ⟨x, hx, hσ⟩ := hpos i p (argVal d.args[i]) hp (by simp [hx0]) hc
          have hval : d.args[i] = .val x := by
            cases ha : d.args[i] with
            | val v => rw [ha] at hx; simp only [argVal, Option.some.injEq] at hx; rw [hx]
            | ret _ => rw [ha] at hx; simp [argVal] at hx
            | exn _ => rw [ha] at hx; simp [argVal] at hx
          have hbargs : bargs[i]? = some x := resolveH_val _ _ hres i x (by rw [hx0, hval])
          have hxv : x ∈ d.vals := by
            simp only [TryDest.vals]
            exact List.mem_filterMap.2 ⟨.val x, by rw [← hval]; exact List.getElem_mem hn, rfl⟩
          obtain ⟨h1, h2, h3⟩ := hT x (hvals d hdm x hxv)
          show regs' (rename m p.1) = vs1[i]?
          rw [← hσ, hlo' _ h3, h1, ← hlo _ h2]
          exact (getMany_ok hga).2 i x hbargs)
    exact ⟨fr1', (enterBlock_bt { fr' with regs := regs' } [] (.jump _) _).trans he1'', hr1⟩

/-- **The frame relation is a simulation with windows and handler edges.** -/
theorem CR.isSimWU : IsSimWU syms (CR m f D syms) where
  toIsSim := (CR.isSimW hF).toIsSim
  ci := (CR.isSimW hF).ci
  tc := by
    refine ⟨?_, ?_⟩
    · rintro fr fr' mm fn args et n base bc ext vals ⟨bi, k, h⟩ - - hw hm hb ht htc hca
      have ht' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hterm' : fr'.term = .tryCall fn (args.map (rename m))
          (filterEt (keepMap m f) (et.mapVals (rename m))) := by
        rw [h.term, ht]; rfl
      have hT := h.termOps hF hb
      rw [ht] at hT
      obtain ⟨e0, s0, he0, hs0, hc0, rfl, hbc, rfl⟩ := tcArgs_ok.1 htc
      obtain ⟨bc2, hbc2, -, -⟩ := tryNormal_pair (rename m) (et := et)
        (et' := et.mapVals (rename m)) rfl (b2 := fr'.func.freshValue) hbc
      have hbc' := tryNormal_filter (keepMap m f) hbc2
      have htc' : tcArgs fr' fn (filterEt (keepMap m f) (et.mapVals (rename m))) =
          .ok (e0.sig.returns.length, fr'.func.freshValue,
            { block := bc2.block, args := filt (keepOf (keepMap m f) bc2.block) bc2.args }) := by
        refine tcArgs_ok.2 ⟨e0, s0, ?_, ?_, hc0, rfl, hbc', rfl⟩
        · rw [← he0]; simp only [Function.extern?, h.externs]
        · rw [← hs0, h.sigDecls]; rfl
      have hca' : callArgs fr' fn (args.map (rename m)) = .ok (ext, vals) :=
        Res.norm_eq_ok (callArgs_rename h.externs
          (fun x hx => (hT x (by simp [termOperands, hx])).1)) hca
      refine ⟨fr', fn, args.map (rename m), _, _, _, .refl _ _, ht', hterm', htc', hca', ?_, ?_⟩
      · exact h.tcont hF hb hw (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
          (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
          (fun x hx => by rw [ht]; exact normal_vals_sub x hx) hbc hbc'
      · exact h.hcont hF hb hw (fun d hd => by rw [ht]; exact handlers_edge hd)
          (fun d hd => by rw [ht]; exact handler_succ hd)
          (fun d hd x hx => by rw [ht]; simp [termOperands, handler_vals hd hx])
    · rintro fr fr' mm callee args et n base bc d a vals ⟨bi, k, h⟩ - - hw hm hb ht htc hca
      have ht' : fr'.body = [] := by rw [h.body, hb]; rfl
      have hterm' : fr'.term = .tryCallIndirect (rename m callee) (args.map (rename m))
          (filterEt (keepMap m f) (et.mapVals (rename m))) := by
        rw [h.term, ht]; rfl
      have hT := h.termOps hF hb
      rw [ht] at hT
      obtain ⟨s0, hs0, rfl, hbc, rfl⟩ := ticArgs_ok.1 htc
      obtain ⟨bc2, hbc2, -, -⟩ := tryNormal_pair (rename m) (et := et)
        (et' := et.mapVals (rename m)) rfl (b2 := fr'.func.freshValue) hbc
      have hbc' := tryNormal_filter (keepMap m f) hbc2
      have htc' : ticArgs fr' (filterEt (keepMap m f) (et.mapVals (rename m))) =
          .ok (s0.returns.length, fr'.func.freshValue,
            { block := bc2.block, args := filt (keepOf (keepMap m f) bc2.block) bc2.args }) :=
        ticArgs_ok.2 ⟨s0, by rw [← hs0, h.sigDecls]; rfl, rfl, hbc', rfl⟩
      have hca' : ciArgs fr' (filterEt (keepMap m f) (et.mapVals (rename m))).sig (rename m callee)
          (args.map (rename m)) = .ok (d, a, vals) :=
        ciArgs_rename h.sigDecls
          (fun x hx => (hT x (by
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp [termOperands]
            · simp [termOperands, hx])).1) hca
      refine ⟨fr', rename m callee, args.map (rename m), _, _, _, .refl _ _, ht', hterm', htc', hca',
        ?_, ?_⟩
      · exact h.tcont hF hb hw (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
          (by rw [ht]; exact List.mem_map.2 ⟨et.normal, dests_normal et, rfl⟩)
          (fun x hx => by rw [ht]; exact normal_vals_sub' x hx) hbc hbc'
      · exact h.hcont hF hb hw (fun d hd => by rw [ht]; exact handlers_edge hd)
          (fun d hd => by rw [ht]; exact handler_succ hd)
          (fun d hd x hx => by rw [ht]; simp [termOperands, handler_vals hd hx])

end

/-! ## The theorems -/

/-- **Constant-phi removal is sound with handler edges.** -/
theorem cpOk_simU {f : Function} {sol : List (ValueId × ValueId)} (h : cpOk f sol = true) :
    FunSimU f (apply f sol) := by
  obtain ⟨fi, -, hF⟩ := cpOk_facts h
  rw [apply_eq]
  refine FunSimU.ofWU rfl rfl rfl rfl fun syms => ⟨_, CR.isSimWU hF (syms := syms), fun b hb => ?_⟩
  have hb0 : f.blocks[0]? = some b := by
    simpa [Function.entry?, List.head?_eq_getElem?] using hb
  have hkeep : ∀ p ∈ b.params, (solMap sol).contains p.1 = false := by
    intro p hp
    cases hc : (solMap sol).contains p.1
    · rfl
    · obtain ⟨bp, -, -, hd, hbp, -⟩ := hF.key p.1 hc
      rw [site_param hF.wf hb0 hp] at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      exact absurd hd.1.symm hbp
  have hpar : (cpBlock (solMap sol) (keepMap (solMap sol) f) b).params = b.params := by
    simp only [cpBlock]
    exact List.filter_eq_self.2 (fun p hp => by simp [hkeep p hp])
  refine ⟨cpBlock _ _ b, by rw [cpFun_entry?, hb]; rfl, hpar,
    fun args regs slots hty hr hsl => ⟨0, 0, Inv.entry hF.wf hb hty hr hsl, rfl, rfl, rfl, rfl,
      fun v hv => ?_⟩⟩
  obtain ⟨b1, p, hb1, hp, hpv⟩ := site_param' hF.wf (avail_entry hF.wf hv)
  rw [hb0] at hb1; cases hb1
  show regs (rename (solMap sol) v) = regs v
  rw [← hpv, rename_of_not (hkeep p hp)]

theorem runCore_simU (f : Function) : FunSimU f (runCore f) := by
  unfold runCore
  by_cases hc : freshOkB f = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
    have h1 := removeUnreachable_simU f hc
    split
    · rename_i h2
      simp only [Bool.and_eq_true] at h2
      exact h1.trans (cpOk_simU h2.2)
    · exact h1
  · have hc' : freshOkB f = false := by simpa using hc
    simp only [hc', Bool.not_false, ite_true]
    exact FunSimU.refl f

/-- **The pass simulates every function with handler edges.** -/
theorem run_simU (f : Function) : FunSimU f (run f) := by
  show FunSimU f (if keepsShapeB f (runCore f) then runCore f else f)
  split
  · exact runCore_simU f
  · exact FunSimU.refl f

/-! ## What the pass keeps -/

theorem instE_mapOperands' (σ : ValueId → ValueId) (i : Inst) :
    Compile.instE (mapOperands σ i) = Compile.instE i := by
  cases i <;> rfl

theorem termE_cp (k : Std.HashMap BlockId (List Bool)) (σ : ValueId → ValueId) (t : Terminator) :
    Compile.termE (filterTerm k (mapTerm σ t)) = Compile.termE t := by
  cases t <;> rfl

theorem isTry_cp (k : Std.HashMap BlockId (List Bool)) (σ : ValueId → ValueId) (t : Terminator) :
    (filterTerm k (mapTerm σ t)).isTry = t.isTry := by
  cases t <;> rfl

theorem callees_cpFun (m : Std.HashMap ValueId ValueId) (f : Function) :
    callees (cpFun m f) = callees f := by
  simp only [callees, cpFun, List.flatMap_map]
  congr 1
  funext b
  simp only [cpBlock, List.filterMap_map]
  congr 1
  funext st
  cases hi : st.inst <;> simp [renStmt, mapOperands, hi]

/-- The rewrite keeps the facts of the output the backend theorem uses. -/
theorem cpFun_facts (m : Std.HashMap ValueId ValueId) (f : Function) :
    BackendFacts f (cpFun m f) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun hE => ?_, fun fn hfn => by rwa [callees_cpFun] at hfn,
    fun h => ⟨fun b hb st hst sig c args he => ?_, fun b hb => ?_⟩⟩
  · simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at hE ⊢
    refine ⟨hE.1, fun b' hb' => ?_⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hb'
    obtain ⟨⟨hp, hbody⟩, ht⟩ := hE.2 b hb
    refine ⟨⟨fun p hp' => hp p (List.mem_filter.1 hp').1, fun st hst => ?_⟩, ?_⟩
    · obtain ⟨st0, hst0, rfl⟩ := List.mem_map.1 hst
      simp only [renStmt, instE_mapOperands']
      exact hbody st0 hst0
    · simp only [cpBlock, termE_cp]; exact ht
  · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
    obtain ⟨st0, hst0, rfl⟩ := List.mem_map.1 hst
    refine h.1 b0 hb0 st0 hst0 sig c args ?_
    simp only [renStmt] at he
    cases hi : st0.inst <;> rw [hi] at he <;> simp [mapOperands] at he
    exact (h.1 b0 hb0 st0 hst0 _ _ _ hi).elim
  · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
    simp only [cpBlock, isTry_cp]
    exact h.2 b0 hb0

theorem backendFacts_trans {f g h : Function} (h1 : BackendFacts f g) (h2 : BackendFacts g h) :
    BackendFacts f h :=
  ⟨h2.name.trans h1.name, h2.sig.trans h1.sig, h2.slots.trans h1.slots,
    h2.globals.trans h1.globals, h2.externs.trans h1.externs, fun hE => h2.subsetE (h1.subsetE hE),
    fun fn hfn => h1.callees fn (h2.callees fn hfn), fun hc => h2.noCI (h1.noCI hc)⟩

theorem runCore_facts (f : Function) : BackendFacts f (runCore f) := by
  unfold runCore
  by_cases hc : freshOkB f = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
    split
    · exact backendFacts_trans (removeUnreachable_facts f) (cpFun_facts _ _)
    · exact removeUnreachable_facts f
  · have hc' : freshOkB f = false := by simpa using hc
    simp only [hc', Bool.not_false, ite_true]
    exact ⟨rfl, rfl, rfl, rfl, rfl, id, fun _ h => h, id⟩

theorem runCore_sigDecls (f : Function) : (runCore f).sigDecls = f.sigDecls := by
  unfold runCore
  by_cases hc : freshOkB f = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
    split
    · show (removeUnreachable f).sigDecls = _
      exact removeUnreachable_sigDecls f
    · exact removeUnreachable_sigDecls f
  · have hc' : freshOkB f = false := by simpa using hc
    simp only [hc', Bool.not_false, ite_true]

end Opt.ConstPhi
