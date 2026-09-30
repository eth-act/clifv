import FV.Backend.Proof.LowerShape

/-!
# Soundness of the lowering validator (M7)

`lowerShape_of_check`, `cert_of_check`: `lowerCheck f vc = true` gives `LowerShape` and `Cert`
for the recorded lowering (`lowBlocks`), the alias resolution `gnOf` and the dataflow `inFix`.
Construction facts (`lowStmts_spec`, `lowBlocks_spec`: the recorded states are those of the
ISLE calls) plus one lemma per decided check.
-/

namespace Backend.Proof.Driver


open Backend Backend.Proof

/-! ## Small list facts -/

theorem all_range {n : Nat} {p : Nat → Bool} (h : (List.range n).all p = true) {i : Nat}
    (hi : i < n) : p i = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem lt_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length := (List.getElem?_eq_some_iff.mp h).1

/-! ## The recorded lowering -/

theorem lowStmts_spec {call : StmtCall} :
    ∀ {ss : List Clif.Stmt} {ii : Nat} {st : LState} {sls : List SLow} {stE : LState},
      lowStmts call ii ss st = some (sls, stE) →
      sls.length = ss.length ∧ ∀ (j : Nat) (sl : SLow), sls[j]? = some sl →
        ∃ tr, call (ii + j) sl.st = .ok (some (.regsVec sl.rss), sl.st', tr) := by
  intro ss
  induction ss with
  | nil =>
    intro ii st sls stE h
    simp only [lowStmts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, fun j sl h => by simp at h⟩
  | cons s ss ih =>
    intro ii st sls stE h
    simp only [lowStmts] at h
    cases hrun : call ii { st with emitted := #[] } with
    | error e => rw [hrun] at h; cases h
    | ok q =>
      obtain ⟨out, st', tr'⟩ := q
      rw [hrun] at h
      cases hout : regsOf out with
      | none => simp only [hout] at h; cases h
      | some rss =>
        have hout' : out = some (.regsVec rss) := by
          unfold regsOf at hout; split at hout <;> simp_all
        subst hout'
        cases hrec : lowStmts call (ii + 1) ss { st' with emitted := #[] } with
        | none => simp only [hout, hrec, Option.map_none] at h; cases h
        | some q =>
          obtain ⟨sls', stE'⟩ := q
          simp only [hout, hrec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          obtain ⟨hlen, hj⟩ := ih hrec
          refine ⟨by simp [hlen], fun j sl hsl => ?_⟩
          cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hsl
            subst hsl
            exact ⟨tr', by simpa using hrun⟩
          | succ j =>
            simp only [List.getElem?_cons_succ] at hsl
            obtain ⟨tr, h⟩ := hj j sl hsl
            exact ⟨tr, by rw [show ii + (j + 1) = ii + 1 + j by omega]; exact h⟩

theorem lowTerm_spec {f : Clif.Function} {tcall : TermCallF} {ycall : TryCallF} {ti : Nat}
    {t : Clif.Terminator} {tst : LState} {nl : Nat} {data : V} {targets : List Label}
    {tl : Option TryLow} {tst' : LState} {nl' : Nat}
    (h : lowTerm f tcall ycall ti t tst nl = some (data, targets, tl, tst', nl')) :
    (t.isTry = false → tl = none ∧ termData (abiTerm f t) = .ok data ∧
      ∃ out tr, tcall ti data t targets tst = .ok (some out, tst', tr)) ∧
    (∀ fn args et, t = .tryCall fn args et → ∃ T, tl = some T ∧ tryCallData f t = .ok data ∧
      exnTableOpnd f et = .ok (T.sig, T.items) ∧ tryTargets f et.dests nl = some (targets, nl') ∧
      tryRegsOf T.sig tst = some (T.regs, T.st1) ∧ tryInfoOf T.sig T.items targets = some T.info ∧
      ∃ out tr, ycall ti data T.regs targets { T.st1 with emitted := #[] } =
        .ok (some out, tst', tr)) := by
  cases t with
  | tryCall fn0 args0 et0 =>
    refine ⟨fun h' => by simp [Clif.Terminator.isTry] at h', fun fn args et ht => ?_⟩
    cases ht
    simp only [lowTerm] at h
    split at h
    · rename_i data0 sig items targets0 nl0 hd he htt
      split at h
      · rename_i trs st1 hr
        split at h
        · rename_i info hi
          split at h
          · rename_i o tst0 tr0 hy
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
            exact ⟨⟨info, sig, items, trs, st1⟩, rfl, hd, he, htt, hr, hi, o, tr0, hy⟩
          · cases h
        · cases h
      · cases h
    · cases h
  | tryCallIndirect c args0 et0 =>
    refine ⟨fun h' => by simp [Clif.Terminator.isTry] at h', fun fn args et ht => by cases ht⟩
  | _ =>
    refine ⟨fun _ => ?_, fun fn args et ht => by cases ht⟩
    simp only [lowTerm] at h
    split at h
    · rename_i data0 targets0 nl0 hd htg
      split at h
      · rename_i o tst0 tr0 hy
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, hd, o, tr0, hy⟩
      · cases h
    · cases h

theorem lowBlocks_spec {f : Clif.Function} {call : StmtCall} {tcall : TermCallF} {ycall : TryCallF} :
    ∀ {Bs : List Clif.Block} {start : Nat} {st : LState} {nl : Nat} {bl : List BLow},
      lowBlocks f call tcall ycall start Bs st nl = some bl →
      bl.length = Bs.length ∧
      ∀ (bi : Nat) (B : Clif.Block) (L : BLow), Bs[bi]? = some B → bl[bi]? = some L →
        L.sl.length = B.body.length ∧
        (∀ (j : Nat) (sl : SLow), L.sl[j]? = some sl →
          ∃ tr, call (L.start + j) sl.st = .ok (some (.regsVec sl.rss), sl.st', tr)) ∧
        L.tst.emitted = #[] ∧
        ∃ nl0 nl', lowTerm f tcall ycall (L.start + B.body.length) B.term L.tst nl0 =
          some (L.data, L.targets, L.tl, L.tst', nl') := by
  intro Bs
  induction Bs with
  | nil =>
    intro start st nl bl h
    simp only [lowBlocks, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun bi B L h => by simp at h⟩
  | cons B Bs ih =>
    intro start st nl bl h
    simp only [lowBlocks] at h
    cases hstm : lowStmts call start B.body st with
    | none => rw [hstm] at h; cases h
    | some q =>
      obtain ⟨sls, stE⟩ := q
      rw [hstm] at h
      simp only at h
      cases hterm : lowTerm f tcall ycall (start + B.body.length) B.term { stE with emitted := #[] } nl with
      | none => rw [hterm] at h; cases h
      | some q =>
        obtain ⟨data, targets, tl, tst', nl'⟩ := q
        rw [hterm] at h
        simp only at h
        cases hrec : lowBlocks f call tcall ycall (start + B.body.length + 1) Bs
            { tst' with emitted := #[] } nl' with
        | none => rw [hrec] at h; cases h
        | some bl' =>
          rw [hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hlen, hbl⟩ := ih hrec
          obtain ⟨hsl, hsj⟩ := lowStmts_spec hstm
          refine ⟨by simp [hlen], fun bi B' L hB hL => ?_⟩
          cases bi with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hB hL
            subst hB hL
            exact ⟨hsl, hsj, rfl, nl, nl', hterm⟩
          | succ bi =>
            simp only [List.getElem?_cons_succ] at hB hL
            exact hbl bi B' L hB hL

/-! ## Alias resolution -/

theorem gnOf_temp {lo : Nat} {al : List (Nat × Nat)} {n : Nat} (h : lo ≤ n) : gnOf lo al n = n := by
  simp [gnOf, Nat.not_lt.mpr h]

theorem renOf_vrenaming (gn : Nat → Nat) : VRenaming (renOf gn) gn := by
  refine ⟨fun n c => rfl, fun r hr => ?_⟩
  cases r with
  | vreg n c => exact absurd rfl (hr n c)
  | _ => rfl

/-! ## The context -/

theorem ctxOk_sound {f : Clif.Function} {ctx : Ctx}
    (h : ctxOk f ctx = true) : CtxInv f ctx := by
  simp only [ctxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hfunc, hinsts⟩, hreg⟩, hty⟩, hdef⟩, hslot⟩, hres⟩, hvt⟩, haddr⟩ := h
  have hinst : ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
      info.clif = some inst →
      Compile.instE inst = true ∧ notFuncAddr inst = true ∧ (instData f inst = .ok info.data) ∧
      ∃ tys, inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (fun _ => none) = some tys ∧
        info.resTys = tys.map CTy.ofClif ∧ info.results.length = tys.length := by
    intro ii info inst hi hc
    have hm : info ∈ ctx.insts.toList := by
      rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi
    have := List.all_eq_true.mp hinsts info hm
    rw [hc] at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨h0, hfa⟩, h1, h2⟩ := this
    refine ⟨h0, hfa, ?_, ?_⟩
    · cases hd : instData f inst with
      | ok d => rw [hd] at h1; simpa using h1
      | error e => rw [hd] at h1; simp at h1
    · have h2' : ctxResTysOk f info inst = true := h2
      unfold ctxResTysOk at h2'
      cases hty : inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (fun _ => none) with
      | none => rw [hty] at h2'; simp at h2'
      | some tys =>
        have h2'' : (decide (info.resTys = tys.map CTy.ofClif) &&
            decide (info.results.length = tys.length)) = true := by
          rw [hty] at h2'; exact h2'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2''
        exact ⟨tys, rfl, h2''.1, h2''.2⟩
  refine ⟨hfunc, fun ii info inst hi hc => (hinst ii info inst hi hc).2.2.1,
    fun ii info inst hi hc => (hinst ii info inst hi hc).1,
    fun ii info inst hi hc => (hinst ii info inst hi hc).2.2.2, ?_, ?_, ?_, ?_, hslot, ?_, ?_, ?_,
    fun ii info inst hi hc ty fn he => by
      have := (hinst ii info inst hi hc).2.1
      rw [he] at this
      simp [notFuncAddr] at this⟩
  · intro x r hx
    have hlt : x < ctx.valReg.size := by
      simp only [Ctx.valueReg?] at hx
      cases h : ctx.valReg[x]? with
      | none => rw [h] at hx; cases hx
      | some _ => exact (Array.getElem?_eq_some_iff.mp h).1
    have := all_range hreg hlt
    rw [hx] at this
    simpa using this
  · intro x t hx
    have hlt : x < ctx.valTy.size := by
      simp only [Ctx.valueType?] at hx
      cases h : ctx.valTy[x]? with
      | none => rw [h] at hx; cases hx
      | some _ => exact (Array.getElem?_eq_some_iff.mp h).1
    have := all_range hty hlt
    rw [hx] at this
    simpa using this
  · intro x d hx
    have hlt : x < ctx.valDef.size := by
      simp only [Ctx.defInst?] at hx
      cases h : ctx.valDef[x]? with
      | none => rw [h] at hx; cases hx
      | some _ => exact (Array.getElem?_eq_some_iff.mp h).1
    have := all_range hdef hlt
    rw [hx] at this
    simp only at this
    split at this
    · rename_i info hi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨info, hi, this.1⟩
    · cases this
  · intro x d info hx hi
    have hlt : x < ctx.valDef.size := by
      simp only [Ctx.defInst?] at hx
      cases h : ctx.valDef[x]? with
      | none => rw [h] at hx; cases hx
      | some _ => exact (Array.getElem?_eq_some_iff.mp h).1
    have := all_range hdef hlt
    rw [hx] at this
    simp only [hi, Bool.and_eq_true] at this
    exact this.2
  · intro ii info hi t ht
    have hm : info ∈ ctx.insts.toList := by
      rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi
    have := List.all_eq_true.mp (List.all_eq_true.mp hres info hm) t ht
    obtain ⟨u, hu, he⟩ := List.any_eq_true.mp this
    rw [of_decide_eq_true he]; exact hu
  · intro x t hx
    have hlt : x < ctx.valTy.size := by
      simp only [Ctx.valueType?] at hx
      cases h : ctx.valTy[x]? with
      | none => rw [h] at hx; cases hx
      | some _ => exact (Array.getElem?_eq_some_iff.mp h).1
    have := all_range hvt hlt
    rw [hx] at this
    dsimp only at this
    obtain ⟨u, hu, he⟩ := List.any_eq_true.mp this
    rw [of_decide_eq_true he]; exact hu
  · intro ii info inst x hi hc hx
    have hm : info ∈ ctx.insts.toList := by
      rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi
    have := List.all_eq_true.mp haddr info hm
    rw [hc] at this
    cases inst <;> simp only [memAddr?, reduceCtorEq, Option.some.injEq] at hx <;> subst hx <;>
      simpa using this

/-! ## `LowerShape` -/

theorem stmtOk_sound {ctx : Ctx} {st0 : LState} {gn : Nat → Nat} {ii : Nat} {stm : Clif.Stmt}
    {sl : SLow} (h : stmtOk ctx st0 gn ii stm sl = true) :
    (∃ info, ctx.insts[ii]? = some info ∧ info.clif = some stm.inst ∧ info.results = stm.results) ∧
    sl.st.emitted = #[] ∧ st0.nextVreg ≤ sl.st.nextVreg ∧
    (∀ (k : Nat) r out cls, stm.results[k]? = some r → sl.rss[k]? = some [.vreg out cls] →
      gn r = gn out) := by
  simp only [stmtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hi, he⟩, hle⟩, hal⟩ := h
  refine ⟨?_, by simpa using he, hle, ?_⟩
  · split at hi
    · rename_i info hinfo
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨info, hinfo, hi.1, hi.2⟩
    · cases hi
  · intro k r out cls hr hrs
    have hz : (stm.results.zip sl.rss)[k]? = some (r, [.vreg out cls]) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hr, hrs⟩
    have := List.all_eq_true.mp hal _ (List.mem_of_getElem? hz)
    simpa using this

theorem succOk_sound {f : Clif.Function} {vc : VCode} {R : Reg → Reg} {B : Clif.Block} {L : BLow}
    (h : succOk f vc R B L = true) :
    match B.term with
    | .jump bc => ∃ tl, blockIdx? f bc.block = some tl ∧ L.targets = [tl]
    | .tryCall _ _ et => L.targets.length = et.dests.length ∧
      ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
        L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
        eb.branchArgs = (et.normal.args.map (normArgReg R T.regs.1)).toArray ∧
        ∀ a ∈ et.normal.args, match a with
          | .val _ => True
          | .ret i => i < T.sig.returns.length
          | .exn _ => False
    | _ => L.targets.length = (dests B.term).length ∧
      ∀ (k : Nat) bc tlab, (dests B.term)[k]? = some bc → L.targets[k]? = some tlab →
        ∃ tl, blockIdx? f bc.block = some tl ∧
          (bc.args = [] → tlab = tl) ∧
          (bc.args ≠ [] → ∃ eb, vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧
            eb.params = #[] ∧ eb.branchArgs = (bc.args.map fun a => R (.vreg a .int)).toArray) := by
  have gen : ∀ t : Clif.Terminator, (decide (L.targets.length = (dests t).length) &&
      ((dests t).zip L.targets).all fun (bc, tlab) => match blockIdx? f bc.block with
        | none => false
        | some tl =>
          if bc.args = [] then decide (tlab = tl) else
          match vc.blocks[tlab]? with
          | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
              decide (eb.branchArgs = (bc.args.map fun a => R (.vreg a .int)).toArray)
          | none => false) = true →
      L.targets.length = (dests t).length ∧
      ∀ (k : Nat) bc tlab, (dests t)[k]? = some bc → L.targets[k]? = some tlab →
        ∃ tl, blockIdx? f bc.block = some tl ∧
          (bc.args = [] → tlab = tl) ∧
          (bc.args ≠ [] → ∃ eb, vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧
            eb.params = #[] ∧ eb.branchArgs = (bc.args.map fun a => R (.vreg a .int)).toArray) := by
    intro t h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨h.1, fun k bc tlab hbc htl => ?_⟩
    have hz : ((dests t).zip L.targets)[k]? = some (bc, tlab) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hbc, htl⟩
    have := List.all_eq_true.mp h.2 _ (List.mem_of_getElem? hz)
    simp only at this
    split at this
    · cases this
    · rename_i tl htlb
      refine ⟨tl, htlb, fun ha => ?_, fun ha => ?_⟩
      · simpa [ha] using this
      · simp only [ha, ite_false] at this
        split at this
        · rename_i eb heb
          simp only [Bool.and_eq_true, decide_eq_true_eq] at this
          exact ⟨eb, heb, this.1.1, this.1.2, this.2⟩
        · cases this
  unfold succOk at h
  split at h
  · rename_i bc hj
    rw [hj]
    split at h
    · rename_i tl htl
      exact ⟨tl, htl, by simpa using h⟩
    · cases h
  · rename_i fn args et hj
    rw [hj]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlen, h⟩ := h
    refine ⟨hlen, ?_⟩
    split at h
    · rename_i tl tlab T htl htlab hT
      split at h
      · rename_i eb heb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        refine ⟨tl, tlab, T, eb, htl, htlab, hT, heb, h.1.1.1, h.1.1.2, h.1.2, fun a ha => ?_⟩
        have := List.all_eq_true.mp h.2 a ha
        cases a <;> simp_all
      · cases h
    · cases h
  · rename_i hnj hnt
    have := gen B.term h
    split
    · rename_i bc hj; exact absurd hj (hnj bc)
    · rename_i fn args et hj; exact absurd hj (hnt fn args et)
    · exact this

theorem lowerShape_of_ok {f : Clif.Function} {vc : VCode} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {st0 : LState} {bl : List BLow} {gn : Nat → Nat}
    (hb : buildCtx f = .ok (ctx, ranges, st0))
    (hl : lowBlocks f (stmtCall ctx) (termCallF ctx) (tryCallF ctx) 0 f.blocks st0
      f.blocks.length = some bl)
    (hgn : ∀ n, st0.nextVreg ≤ n → gn n = n) (hs : shapeOk f vc ctx st0 gn bl = true) :
    LowerShape f vc ctx st0 (renOf gn) gn bl := by
  obtain ⟨-, hlb⟩ := lowBlocks_spec hl
  simp only [shapeOk, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hctx, hvb⟩, hpar⟩, hlen⟩, hsize⟩, hlab⟩, hblk⟩, hfresh⟩ := hs
  have hblk' : ∀ bi B L, f.blocks[bi]? = some B → bl[bi]? = some L →
      blockOk f vc ctx st0 (renOf gn) gn bl bi B L = true := by
    intro bi B L hB hL
    have := all_range hblk (lt_of_getElem? hB)
    simpa [hB, hL] using this
  refine ⟨⟨ranges, hb⟩, ctxOk_sound hctx, renOf_vrenaming gn, hgn, ?_, hlen, hsize, ?_, ?_, hfresh,
    ?_, ?_⟩
  · intro B hB p hp
    have := List.all_eq_true.mp (List.all_eq_true.mp hpar B hB) p hp
    simpa using this
  · intro x r hx
    have : x < ctx.valReg.size := by
      simp only [Ctx.valueReg?] at hx
      cases h : ctx.valReg[x]? with
      | none => rw [h] at hx; cases hx
      | some _ => exact (Array.getElem?_eq_some_iff.mp h).1
    omega
  · intro l vb hvb
    have := all_range hlab (Array.getElem?_eq_some_iff.mp hvb).1
    simpa [hvb] using this
  · intro bi B L hB hL
    have h := hblk' bi B L hB hL
    unfold blockOk at h
    split at h
    · cases h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have h' := h.2
      split at h'
      · rename_i info hinfo
        simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Option.isNone_iff_eq_none] at h'
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
        rw [hinfo]
        cases info
        simp_all
      · cases h'
  · intro bi B L hB hL
    obtain ⟨hsl, hsj, htemp0, nl0, nl', hterm⟩ := hlb bi B L hB hL
    obtain ⟨hnt, hty⟩ := lowTerm_spec hterm
    have h := hblk' bi B L hB hL
    unfold blockOk at h
    split at h
    · cases h
    · rename_i vb hvb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hst⟩, htemp⟩, hle⟩, hcode⟩, htne⟩, hpars⟩, hbargs⟩, hsucc⟩, -⟩ := h
      refine ⟨vb, hvb, hsl, ?_, by simpa using htemp, hle, fun hnt' => ?_, fun fn args et ht => ?_,
        hcode, by simpa using htne, hpars, hbargs, succOk_sound hsucc⟩
      rotate_left
      · obtain ⟨h1, h2, out, tr, h3⟩ := hnt hnt'
        exact ⟨h1, h2, out, tr, h3⟩
      · obtain ⟨T, h1, h2, h3, -, h5, h6, out, tr, h7⟩ := hty fn args et ht
        exact ⟨T, h1, h2, h3, h5, h6, out, tr, h7⟩
      intro j stm sl hj hslj
      have := all_range hst (lt_of_getElem? hj)
      rw [hj, hslj] at this
      obtain ⟨h1, h2, h3, h4⟩ := stmtOk_sound this
      exact ⟨h1, h2, h3, hsj j sl hslj, h4⟩

/-! ## `Cert` -/

theorem mem_availOf {f : Clif.Function} {In : List (List Clif.ValueId)} {bi j : Nat}
    {x : Clif.ValueId} :
    x ∈ availOf f In bi j ↔ ∃ B, f.blocks[bi]? = some B ∧
      x ∈ B.params.map (·.1) ++ In.getD bi [] ++ defsBefore B j ∧ x ∉ defsFrom B j := by
  unfold availOf
  cases hB : f.blocks[bi]? with
  | none => simp
  | some B =>
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => ⟨B, rfl, h⟩, fun ⟨B', hB', h⟩ => by cases hB'; exact h⟩

theorem availOf_ge {f : Clif.Function} {In : List (List Clif.ValueId)} {bi j : Nat} {B : Clif.Block}
    (hB : f.blocks[bi]? = some B) (hj : B.body.length ≤ j) :
    availOf f In bi j = availOf f In bi B.body.length := by
  simp only [availOf, hB, defsBefore, defsFrom, List.take_of_length_le hj, List.take_length,
    List.drop_of_length_le hj, List.drop_length]

theorem availOf_sub {f : Clif.Function} {In : List (List Clif.ValueId)} {bi j : Nat}
    {B : Clif.Block} (hB : f.blocks[bi]? = some B) {x : Clif.ValueId}
    (hx : x ∈ availOf f In bi j) : x ∈ availOf f In bi B.body.length := by
  obtain ⟨B', hB', hm, -⟩ := mem_availOf.mp hx
  rw [hB] at hB'; cases hB'
  rw [mem_availOf]
  refine ⟨B, hB, ?_, by simp [defsFrom]⟩
  simp only [List.mem_append] at hm ⊢
  rcases hm with (h | h) | h
  · exact .inl (.inl h)
  · exact .inl (.inr h)
  · right
    simp only [defsBefore, List.mem_flatMap] at h ⊢
    obtain ⟨stm, hs, hx⟩ := h
    exact ⟨stm, by rw [List.take_length]; exact List.mem_of_mem_take hs, hx⟩

theorem closedOk_sound {ctx : Ctx} {A : List Clif.ValueId} (h : closedOk ctx A = true)
    {x : Clif.ValueId} (hx : x ∈ A) {d : Nat} {info : IInfo} {cl : Clif.Inst}
    (hd : ctx.defInst? x = some d) (hi : ctx.insts[d]? = some info) (hc : info.clif = some cl) :
    ∀ y ∈ instArgs cl, y ∈ A := by
  have := List.all_eq_true.mp h x hx
  simp only [hd, hi, hc, List.all_eq_true, decide_eq_true_eq] at this
  exact this

theorem edgeOk_sound {f : Clif.Function} {ctx : Ctx} {gn : Nat → Nat}
    {In : List (List Clif.ValueId)} {Aend : List Clif.ValueId} {b : Clif.BlockId}
    (h : edgeOk f ctx gn In Aend b = true) :
    ∀ tl TB, blockIdx? f b = some tl → f.blocks[tl]? = some TB →
      (TB.params.map (·.1)).Nodup ∧
      (∀ x ∈ availOf f In tl 0, x ∉ TB.params.map (·.1) → ∀ d info cl, ctx.defInst? x = some d →
        ctx.insts[d]? = some info → info.clif = some cl → ∀ y ∈ instArgs cl,
          y ∉ TB.params.map (·.1)) ∧
      ∀ x ∈ availOf f In tl 0, (x ∈ TB.params.map (·.1) ∧ ctx.defInst? x = none) ∨
        (x ∉ TB.params.map (·.1) ∧ x ∈ Aend ∧ gn x ∉ TB.params.map (·.1)) := by
  intro tl TB htl hTB
  simp only [edgeOk, htl, hTB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨hnd, hp⟩, hx⟩ := h
  refine ⟨hnd, fun x hxA hxp d info cl hd hi hc y hy => ?_, fun x hxA => ?_⟩
  · have := hp x hxA
    simp only [hxp, hd, hi, hc, List.all_eq_true, decide_eq_true_eq] at this
    exact (this.resolve_left id) y hy
  rcases hx x hxA with h | h
  · exact .inl h
  · exact .inr ⟨h.1.1, h.1.2, h.2⟩

theorem cert_of_ok {f : Clif.Function} {ctx : Ctx} {st0 : LState} {gn : Nat → Nat}
    {bl : List BLow} {In : List (List Clif.ValueId)} (hlen : bl.length = f.blocks.length)
    (h : certOk f ctx st0 gn bl In = true) : Cert f ctx st0 gn bl (availOf f In) := by
  simp only [certOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hentry, hblocks⟩, hres⟩, hpar⟩ := h
  have hL : ∀ (bi : Nat) (B : Clif.Block), f.blocks[bi]? = some B → ∃ L, bl[bi]? = some L := by
    intro bi B hB
    have := lt_of_getElem? hB
    exact ⟨bl[bi]'(by omega), List.getElem?_eq_getElem _⟩
  have hblk : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      certBlockOk f ctx st0 gn In bi B L = true := by
    intro bi B L hB hL
    have := all_range hblocks (lt_of_getElem? hB)
    simpa [hB, hL] using this
  have hparts : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B →
      bl[bi]? = some L → _ := fun bi B L hB hL => by
    have h := hblk bi B L hB hL
    unfold certBlockOk at h
    simp only [Bool.and_eq_true] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- small
    intro bi j x hx
    cases hB : f.blocks[bi]? with
    | none => simp [availOf, hB] at hx
    | some B =>
      obtain ⟨L, hL⟩ := hL bi B hB
      obtain ⟨⟨⟨⟨⟨hs, -⟩, -⟩, -⟩, -⟩, -⟩ := hparts bi B L hB hL
      have := List.all_eq_true.mp hs x (availOf_sub hB hx)
      simpa using this
  · -- entry
    intro B hB
    simp only [hB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hentry
    exact ⟨hentry.1, fun x hx => hentry.2 x hx⟩
  · -- closed
    intro bi j x d info cl hx hd hi hc _ y hy
    cases hB : f.blocks[bi]? with
    | none => simp [availOf, hB] at hx
    | some B =>
      obtain ⟨L, hL⟩ := hL bi B hB
      obtain ⟨⟨⟨⟨⟨-, hcl⟩, -⟩, -⟩, -⟩, -⟩ := hparts bi B L hB hL
      by_cases hj : j ≤ B.body.length
      · exact closedOk_sound (all_range hcl (by omega)) hx hd hi hc y hy
      · rw [availOf_ge hB (by omega)] at hx ⊢
        exact closedOk_sound (all_range hcl (by omega)) hx hd hi hc y hy
  · -- statements
    intro bi B L j stm sl hB hL hs hsl
    obtain ⟨⟨⟨⟨⟨-, -⟩, hst⟩, -⟩, -⟩, -⟩ := hparts bi B L hB hL
    have := all_range hst (lt_of_getElem? hs)
    simp only [hs, hsl, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
    refine ⟨h1, fun r hr => h2 r hr, h3, fun x hx => h4 x hx, fun x hx hc => ?_⟩
    rcases h5 x hx with h | h
    · exact h hc.1
    · exact h hc.2
  · -- no branch to the entry
    intro bi B hB bc hbc
    obtain ⟨L, hL⟩ := hL bi B hB
    obtain ⟨-, hd⟩ := hparts bi B L hB hL
    have := List.all_eq_true.mp hd bc hbc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · -- terminators and edges
    intro bi B L hB hL
    obtain ⟨⟨⟨-, ht⟩, hnc⟩, hd⟩ := hparts bi B L hB hL
    refine ⟨fun y hy => by simpa using List.all_eq_true.mp ht y hy, fun x hx hc => ?_,
      fun bc hbc => ?_⟩
    · have := List.all_eq_true.mp hnc x hx
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
      rcases this with h | h
      · exact h hc.1
      · exact h hc.2
    · have := List.all_eq_true.mp hd bc hbc
      simp only [Bool.and_eq_true] at this
      exact edgeOk_sound this.2
  · -- result types
    intro ii info hi m r t hr ht
    have := all_range hres (Array.getElem?_eq_some_iff.mp hi).1
    simp only [hi] at this
    have := all_range this (lt_of_getElem? hr)
    simpa [hr, ht] using this
  · -- parameter types
    intro B hB q hq
    have := List.all_eq_true.mp (List.all_eq_true.mp hpar B hB) q hq
    simpa using this

/-! ## The validator -/

/-- **Soundness of the lowering validator**: `lowerCheck f vc = true` gives the structure of
the VCode and an SSA availability certificate (M7's lowering obligations). -/
theorem brIdx_of_ok {f : Clif.Function} {ctx : Ctx} (h : brIdxOk f ctx = true) :
    ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := by
  intro B hB x d tbl ht
  have := List.all_eq_true.mp h B hB
  rw [ht] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨hlen, this⟩ := this
  refine ⟨?_, hlen⟩
  split at this
  · exact ⟨_, by simpa using this, ‹_›⟩
  · cases this

theorem lowering_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true) :
    ∃ ctx st0 R gn bl A, LowerShape f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
      ∀ B ∈ f.blocks, BrIdxTyped ctx B.term := by
  unfold lowerCheck at h
  split at h
  · cases h
  · rename_i ctx ranges st0 hb
    split at h
    · cases h
    · rename_i bl hl
      simp only [Bool.and_eq_true] at h
      have hS := lowerShape_of_ok (gn := gnOf st0.nextVreg (aliasOf f bl)) hb hl
        (fun n hn => gnOf_temp hn) h.1.1.1
      exact ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len h.1.1.2, brIdx_of_ok h.1.2⟩

/-- A function without `try_call` lowers to VCode without `tryCall` (`lowerCheck`'s last
conjunct). -/
theorem noTryCall_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true)
    (hf : ∀ B ∈ f.blocks, B.term.isTry = false) : vc.hasTryCall = false := by
  unfold lowerCheck at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      rcases h.2 with h2 | h2
      · obtain ⟨B, hB, hB'⟩ := List.any_eq_true.mp h2
        rw [hf B hB] at hB'; cases hB'
      · exact h2

end Backend.Proof.Driver
