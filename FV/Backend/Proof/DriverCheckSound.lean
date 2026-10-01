import FV.Backend.Proof.LowerShape
import Std.Data.HashSet.Lemmas

/-!
# Soundness of the lowering validator (M7)

`lowerShape_of_ok`, `cert_of_ok`: `lowerCheck f vc = true` gives `LowerShape` and `Cert`
for the recorded lowering (`lowBlocks`), the alias resolution `gnTable` (only its being the
identity on temporaries is used, `gnAt_temp`) and the dataflow `inFix` (not used at all: the
certificate holds for whatever entry values `certOk` accepts). Construction facts
(`lowStmts_spec`, `lowBlocks_spec`: the recorded states are those of the ISLE calls) plus one
lemma per decided check; the certificate's membership tests are decided by `Avail.mem`
(`mem_avail`: exact once `certBlockOk` has checked that the statements' results are defined by
their instructions, `DefsAt`).
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
    (∀ et, IsTryWith t et → ∃ T, tl = some T ∧ tryCallData f t = .ok data ∧
      exnTableOpnd f et = .ok (T.sig, T.items) ∧ tryTargets f et.dests nl = some (targets, nl') ∧
      tryRegsOf T.sig tst = some (T.regs, T.st1) ∧ tryInfoOf T.sig T.items targets = some T.info ∧
      ∃ out tr, ycall ti data T.regs targets { T.st1 with emitted := #[] } =
        .ok (some out, tst', tr)) := by
  cases t with
  | tryCall fn0 args0 et0 =>
    refine ⟨fun h' => by simp [Clif.Terminator.isTry] at h', fun et ht => ?_⟩
    obtain rfl : et = et0 := by
      rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'; rfl
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
    refine ⟨fun h' => by simp [Clif.Terminator.isTry] at h', fun et ht => ?_⟩
    obtain rfl : et = et0 := by
      rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'; rfl
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
  | _ =>
    refine ⟨fun _ => ?_, fun et ht => by rcases ht with ⟨_, _, h'⟩ | ⟨_, _, h'⟩ <;> cases h'⟩
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

theorem gnAt_temp {lo : Nat} {al : List (Nat × Nat)} {n : Nat} (h : lo ≤ n) :
    gnAt (gnTable lo al) n = n := by
  have : ¬ n < (gnTable lo al).size := by simp only [gnTable, Array.size_ofFn]; omega
  simp only [gnAt, this, dite_false]

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
      Compile.instE inst = true ∧ (instData f inst = .ok info.data) ∧
      ∃ tys, inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) =
          some tys ∧
        info.resTys = tys.map CTy.ofClif ∧ info.results.length = tys.length := by
    intro ii info inst hi hc
    have hm : info ∈ ctx.insts.toList := by
      rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hi
    have := List.all_eq_true.mp hinsts info hm
    rw [hc] at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨h0, h1, h2⟩ := this
    refine ⟨h0, ?_, ?_⟩
    · cases hd : instData f inst with
      | ok d => rw [hd] at h1; simpa using h1
      | error e => rw [hd] at h1; simp at h1
    · have h2' : ctxResTysOk f info inst = true := h2
      unfold ctxResTysOk at h2'
      cases hty : inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·) with
      | none => rw [hty] at h2'; simp at h2'
      | some tys =>
        have h2'' : (decide (info.resTys = tys.map CTy.ofClif) &&
            decide (info.results.length = tys.length)) = true := by
          rw [hty] at h2'; exact h2'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2''
        exact ⟨tys, rfl, h2''.1, h2''.2⟩
  refine ⟨hfunc, fun ii info inst hi hc => (hinst ii info inst hi hc).2.1,
    fun ii info inst hi hc => (hinst ii info inst hi hc).1,
    fun ii info inst hi hc => (hinst ii info inst hi hc).2.2, ?_, ?_, ?_, ?_, hslot, ?_, ?_, ?_⟩
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
    | .tryCall _ _ et | .tryCallIndirect _ _ et => L.targets.length = et.dests.length ∧
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
  have htry : ∀ et : Clif.ExnTable, (decide (L.targets.length = et.dests.length) &&
      match blockIdx? f et.normal.block, L.targets.getLast?, L.tl with
      | some tl, some tlab, some T => match vc.blocks[tlab]? with
        | some eb => decide (eb.insts = #[.jump tl]) && decide (eb.params = #[]) &&
            decide (eb.branchArgs = (et.normal.args.map (normArgReg R T.regs.1)).toArray) &&
            et.normal.args.all fun
              | .val _ => true
              | .ret i => decide (i < T.sig.returns.length)
              | .exn _ => false
        | none => false
      | _, _, _ => false) = true →
      L.targets.length = et.dests.length ∧
      ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
        L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
        eb.branchArgs = (et.normal.args.map (normArgReg R T.regs.1)).toArray ∧
        ∀ a ∈ et.normal.args, match a with
          | .val _ => True
          | .ret i => i < T.sig.returns.length
          | .exn _ => False := by
    intro et h
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
    exact htry et h
  · rename_i c args et hj
    rw [hj]
    exact htry et h
  · rename_i hnj hnt hnti
    have := gen B.term h
    split
    · rename_i bc hj; exact absurd hj (hnj bc)
    · rename_i fn args et hj; exact absurd hj (hnt fn args et)
    · rename_i c args et hj; exact absurd hj (hnti c args et)
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
      refine ⟨vb, hvb, hsl, ?_, by simpa using htemp, hle, fun hnt' => ?_, fun et ht => ?_,
        hcode, by simpa using htne, hpars, hbargs, succOk_sound hsucc⟩
      rotate_left
      · obtain ⟨h1, h2, out, tr, h3⟩ := hnt hnt'
        exact ⟨h1, h2, out, tr, h3⟩
      · obtain ⟨T, h1, h2, h3, -, h5, h6, out, tr, h7⟩ := hty et ht
        exact ⟨T, h1, h2, h3, h5, h6, out, tr, h7⟩
      intro j stm sl hj hslj
      have := all_range hst (lt_of_getElem? hj)
      rw [hj, hslj] at this
      obtain ⟨h1, h2, h3, h4⟩ := stmtOk_sound this
      exact ⟨h1, h2, h3, hsj j sl hslj, h4⟩

/-! ## `Cert` -/

theorem mem_flatMap_take {α β : Type} {l : List α} {g : α → List β} {j : Nat} {x : β} :
    x ∈ (l.take j).flatMap g ↔ ∃ k s, k < j ∧ l[k]? = some s ∧ x ∈ g s := by
  constructor
  · rintro h
    obtain ⟨s, hs, hx⟩ := List.mem_flatMap.mp h
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hs
    rw [List.getElem?_take] at hk
    split at hk
    · exact ⟨k, s, ‹_›, hk, hx⟩
    · cases hk
  · rintro ⟨k, s, hk, hs, hx⟩
    exact List.mem_flatMap.mpr ⟨s, List.mem_iff_getElem?.mpr ⟨k, by rw [List.getElem?_take, if_pos hk]; exact hs⟩, hx⟩

theorem mem_flatMap_drop {α β : Type} {l : List α} {g : α → List β} {j : Nat} {x : β} :
    x ∈ (l.drop j).flatMap g ↔ ∃ k s, j ≤ k ∧ l[k]? = some s ∧ x ∈ g s := by
  constructor
  · rintro h
    obtain ⟨s, hs, hx⟩ := List.mem_flatMap.mp h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hs
    rw [List.getElem?_drop] at hi
    exact ⟨j + i, s, by omega, hi, hx⟩
  · rintro ⟨k, s, hk, hs, hx⟩
    refine List.mem_flatMap.mpr ⟨s, List.mem_iff_getElem?.mpr ⟨k - j, ?_⟩, hx⟩
    rw [List.getElem?_drop, Nat.add_sub_cancel' hk]; exact hs

/-- Statement `k`'s results are defined by instruction `start + k` (checked by `certBlockOk`). -/
def DefsAt (ctx : Ctx) (B : Clif.Block) (start : Nat) : Prop :=
  ∀ k stm, B.body[k]? = some stm → ∀ r ∈ stm.results, ctx.defInst? r = some (start + k)

section
variable {ctx : Ctx} {B : Clif.Block} {L : BLow} {In : Array (List Clif.ValueId)} {bi : Nat}

theorem Avail.of_body : (Avail.of B L In bi).body = B.body.toArray := rfl
theorem Avail.of_start : (Avail.of B L In bi).start = L.start := rfl
theorem Avail.of_ent : (Avail.of B L In bi).ent = B.params.map (·.1) ++ In.getD bi [] := rfl

theorem dpos_iff (hD : DefsAt ctx B L.start) {x k : Nat} :
    (Avail.of B L In bi).dpos ctx x = some k ↔ ∃ stm, B.body[k]? = some stm ∧ x ∈ stm.results := by
  constructor
  · intro h
    simp only [Avail.dpos, Avail.of, List.getElem?_toArray] at h
    split at h
    · split at h
      · split at h
        · rename_i stm hs
          split at h
          · cases h; exact ⟨stm, hs, ‹_›⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · rintro ⟨stm, hs, hx⟩
    simp only [Avail.dpos, Avail.of, List.getElem?_toArray, hD k stm hs x hx, Nat.le_add_right,
      if_true, Nat.add_sub_cancel_left, hs, hx]

theorem dpos_lt (hD : DefsAt ctx B L.start) {x k : Nat}
    (h : (Avail.of B L In bi).dpos ctx x = some k) : k < B.body.length := by
  obtain ⟨_, hs, -⟩ := (dpos_iff hD).mp h
  exact lt_of_getElem? hs

theorem mem_ent {x : Nat} :
    (Avail.of B L In bi).entS.contains x = true ↔ x ∈ B.params.map (·.1) ++ In.getD bi [] := by
  simp only [Avail.of, Std.HashSet.contains_ofList, List.contains_iff_mem]

theorem mem_availOf {f : Clif.Function} {j x : Nat} :
    x ∈ availOf f In bi j ↔ ∃ B, f.blocks[bi]? = some B ∧
      x ∈ B.params.map (·.1) ++ In.getD bi [] ++ defsBefore B j ∧ x ∉ defsFrom B j := by
  unfold availOf
  cases hB : f.blocks[bi]? with
  | none => simp
  | some B =>
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => ⟨B, rfl, h⟩, fun ⟨B', hB', h⟩ => by cases hB'; exact h⟩

/-- Membership in the available values, decided by `Avail.mem`. -/
theorem mem_avail {f : Clif.Function} (hB : f.blocks[bi]? = some B) (hD : DefsAt ctx B L.start)
    {j x : Nat} : x ∈ availOf f In bi j ↔ (Avail.of B L In bi).mem ctx j x = true := by
  have e : x ∈ availOf f In bi j ↔
      x ∈ B.params.map (·.1) ++ In.getD bi [] ++ defsBefore B j ∧ x ∉ defsFrom B j := by
    rw [mem_availOf]
    exact ⟨fun ⟨B', hB', h⟩ => by rw [hB] at hB'; cases hB'; exact h, fun h => ⟨B, hB, h⟩⟩
  rw [e]
  simp only [List.mem_append, defsBefore, defsFrom, mem_flatMap_take, mem_flatMap_drop, Avail.mem]
  cases hp : (Avail.of B L In bi).dpos ctx x with
  | some k =>
    obtain ⟨stm, hs, hx⟩ := (dpos_iff hD).mp hp
    have uniq : ∀ (k' : Nat) (s' : Clif.Stmt), B.body[k']? = some s' → x ∈ s'.results → k' = k :=
      fun k' s' h1 h2 => by
        have := (dpos_iff (In := In) (bi := bi) hD).mpr ⟨s', h1, h2⟩
        rw [hp] at this; cases this; rfl
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨-, hnot⟩
      apply Classical.byContradiction
      intro hkj
      exact hnot ⟨k, stm, by omega, hs, hx⟩
    · intro hkj
      refine ⟨Or.inr ⟨k, stm, hkj, hs, hx⟩, ?_⟩
      rintro ⟨k', s', hk', hs', hx'⟩
      have := uniq k' s' hs' hx'
      omega
  | none =>
    have hn : ∀ (k' : Nat) (s' : Clif.Stmt), B.body[k']? = some s' → x ∉ s'.results :=
      fun k' s' h1 h2 => by
        have := (dpos_iff (In := In) (bi := bi) hD).mpr ⟨s', h1, h2⟩
        rw [hp] at this; cases this
    rw [mem_ent]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h | ⟨k', s', -, hs', hx'⟩, -⟩
      · exact h
      · exact absurd hx' (hn k' s' hs')
    · intro h
      exact ⟨Or.inl h, fun ⟨k', s', _, hs', hx'⟩ => hn k' s' hs' hx'⟩

theorem mem_iff_first (hD : DefsAt ctx B L.start) {j x : Nat} :
    (Avail.of B L In bi).mem ctx j x = true ↔
      (Avail.of B L In bi).mem ctx B.body.length x = true ∧ (Avail.of B L In bi).first ctx x ≤ j := by
  simp only [Avail.mem, Avail.first]
  cases hp : (Avail.of B L In bi).dpos ctx x with
  | some k =>
    have := dpos_lt hD hp
    simp only [decide_eq_true_eq]; omega
  | none => simp

/-- A value available somewhere in block `bi` is a parameter, an entry value or a result. -/
theorem mem_cand {f : Clif.Function} (hB : f.blocks[bi]? = some B) {j x : Nat}
    (hx : x ∈ availOf f In bi j) :
    x ∈ (Avail.of B L In bi).ent ++ B.body.flatMap (·.results) := by
  simp only [availOf, hB, List.mem_filter, List.mem_append, defsBefore, mem_flatMap_take] at hx
  simp only [Avail.of, List.mem_append]
  rcases hx.1 with (h | h) | ⟨k, s, -, hs, hk⟩
  · exact .inl (.inl h)
  · exact .inl (.inr h)
  · exact .inr (List.mem_flatMap.mpr ⟨s, List.mem_of_getElem? hs, hk⟩)

end

theorem chain_mono {α : Type} {l : List α} {lo hi : α → Nat}
    (h : ∀ k a, l[k]? = some a → lo a ≤ hi a ∧ ∀ b, l[k + 1]? = some b → hi a ≤ lo b) :
    ∀ (d s : Nat) (a b : α), l[s]? = some a → l[s + d]? = some b → lo a ≤ lo b ∧ hi a ≤ hi b := by
  intro d
  induction d with
  | zero =>
    intro s a b ha hb
    rw [Nat.add_zero, ha] at hb; cases hb; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | succ d ih =>
    intro s a b ha hb
    have hlt : s + d < l.length := by have := lt_of_getElem? hb; omega
    obtain ⟨c, hc⟩ : ∃ c, l[s + d]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨h1, h2⟩ := ih s a c ha hc
    obtain ⟨h3, h4⟩ := h (s + d) c hc
    have h5 := h4 b (by rw [← hb, Nat.add_assoc])
    have h6 := (h (s + (d + 1)) b hb).1
    omega

/-- What `certBlockOk` checks, as propositions. -/
theorem certBlockOk_spec {f : Clif.Function} {ctx : Ctx} {st0 : LState} {gn : Nat → Nat}
    {fb : Array Clif.Block} {bla : Array BLow} {In : Array (List Clif.ValueId)} {bi : Nat}
    {B : Clif.Block} {L : BLow} (h : certBlockOk f ctx st0 gn fb bla In bi B L = true) :
    L.sl.length = B.body.length ∧ DefsAt ctx B L.start ∧
    (∀ k stm, B.body[k]? = some stm → stm.results.Nodup ∧
      ∀ y ∈ instArgs stm.inst, (Avail.of B L In bi).mem ctx k y = true) ∧
    (∀ k sl, L.sl[k]? = some sl → sl.st.nextVreg ≤ sl.st'.nextVreg ∧
      ∀ sl', L.sl[k + 1]? = some sl' → sl.st'.nextVreg ≤ sl'.st.nextVreg) ∧
    (∀ x ∈ (Avail.of B L In bi).ent ++ B.body.flatMap (·.results), x < st0.nextVreg ∧
      (∀ y ∈ defArgs ctx x, (Avail.of B L In bi).mem ctx B.body.length y = true ∧
        (Avail.of B L In bi).first ctx y ≤ (Avail.of B L In bi).first ctx x) ∧
      (∀ sl last, L.sl[(Avail.of B L In bi).first ctx x]? = some sl →
        L.sl[B.body.length - 1]? = some last →
        gn x < sl.st.nextVreg ∨ last.st'.nextVreg ≤ gn x) ∧
      ¬ (L.tst.nextVreg ≤ gn x ∧ gn x < L.tst'.nextVreg)) ∧
    (∀ y ∈ termArgs (abiTerm f B.term), (Avail.of B L In bi).mem ctx B.body.length y = true) ∧
    (∀ b ∈ edgeIds B.term, blockIdx? f b ≠ some 0 ∧
      edgeOk f ctx gn fb bla In (Avail.of B L In bi) B.body.length b = true) := by
  simp only [certBlockOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlen, hst⟩, hcand⟩, hterm⟩, hedge⟩ := h
  have hk : ∀ k stm, B.body[k]? = some stm → ∃ sl, L.sl[k]? = some sl ∧
      (stm.results.all (fun r => decide (ctx.defInst? r = some (L.start + k))) &&
        decide stm.results.Nodup && (instArgs stm.inst).all ((Avail.of B L In bi).mem ctx k) &&
        decide (sl.st.nextVreg ≤ sl.st'.nextVreg) &&
        (match L.sl[k + 1]? with
          | some sl' => decide (sl.st'.nextVreg ≤ sl'.st.nextVreg)
          | none => true)) = true := by
    intro k stm hs
    have hkl := lt_of_getElem? hs
    obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[k]? = some sl := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have := all_range hst hkl
    simp only [Avail.of_body, List.getElem?_toArray, hs, hsl] at this
    exact ⟨sl, hsl, this⟩
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k stm hs r hr
    obtain ⟨sl, -, h⟩ := hk k stm hs
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1 r hr
  · intro k stm hs
    obtain ⟨sl, -, h⟩ := hk k stm hs
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.2, h.1.1.2⟩
  · intro k sl hsl
    have hkl := lt_of_getElem? hsl
    obtain ⟨stm, hs⟩ : ∃ stm, B.body[k]? = some stm := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨sl', hsl', h⟩ := hk k stm hs
    have : sl' = sl := by rw [hsl] at hsl'; exact (Option.some.inj hsl').symm
    subst this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨h.1.2, fun sl' h' => ?_⟩
    have := h.2
    simp only [h', decide_eq_true_eq] at this
    exact this
  · intro x hx
    have := List.all_eq_true.mp hcand x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
    refine ⟨h1, h2, fun sl last hsl hlast => ?_, fun hc => ?_⟩
    · simp only [List.getElem?_toArray, hsl, hlast, Bool.or_eq_true, decide_eq_true_eq] at h3
      exact h3
    · rcases h4 with h | h
      · exact h hc.1
      · exact h hc.2
  · intro y hy
    exact List.all_eq_true.mp hterm y hy
  · intro b hb
    have := List.all_eq_true.mp hedge b hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

theorem contains_false {l : List Nat} {x : Nat} : l.contains x = false ↔ x ∉ l := by
  rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem]

theorem defArgs_eq {ctx : Ctx} {x d : Nat} {info : IInfo} {cl : Clif.Inst}
    (hd : ctx.defInst? x = some d) (hi : ctx.insts[d]? = some info) (hc : info.clif = some cl) :
    defArgs ctx x = instArgs cl := by
  simp only [defArgs, hd, hi, hc]

theorem mem_ent_zero {f : Clif.Function} {In : Array (List Clif.ValueId)} {bi : Nat}
    {B : Clif.Block} {L : BLow} (hB : f.blocks[bi]? = some B) {x : Nat}
    (hx : x ∈ availOf f In bi 0) : x ∈ (Avail.of B L In bi).ent := by
  obtain ⟨B', hB', hm, -⟩ := mem_availOf.mp hx
  rw [hB] at hB'; cases hB'
  simpa [defsBefore, Avail.of_ent] using hm

theorem edgeOk_sound {f : Clif.Function} {ctx : Ctx} {gn : Nat → Nat} {bl : List BLow}
    {In : Array (List Clif.ValueId)} {a : Avail} {n : Nat} {b : Clif.BlockId}
    (hlen : bl.length = f.blocks.length)
    (hD : ∀ (tl : Nat) (TB : Clif.Block) (TL : BLow), f.blocks[tl]? = some TB → bl[tl]? = some TL →
      DefsAt ctx TB TL.start)
    (h : edgeOk f ctx gn f.blocks.toArray bl.toArray In a n b = true) :
    ∀ tl TB, blockIdx? f b = some tl → f.blocks[tl]? = some TB →
      (TB.params.map (·.1)).Nodup ∧
      (∀ x ∈ availOf f In tl 0, x ∉ TB.params.map (·.1) → ∀ d info cl, ctx.defInst? x = some d →
        ctx.insts[d]? = some info → info.clif = some cl → ∀ y ∈ instArgs cl,
          y ∉ TB.params.map (·.1)) ∧
      ∀ x ∈ availOf f In tl 0, (x ∈ TB.params.map (·.1) ∧ ctx.defInst? x = none) ∨
        (x ∉ TB.params.map (·.1) ∧ a.mem ctx n x = true ∧ gn x ∉ TB.params.map (·.1)) := by
  intro tl TB htl hTB
  obtain ⟨TL, hTL⟩ : ∃ TL, bl[tl]? = some TL :=
    ⟨_, List.getElem?_eq_getElem (by have := lt_of_getElem? hTB; omega)⟩
  have hDt := hD tl TB TL hTB hTL
  simp only [edgeOk, htl, List.getElem?_toArray, hTB, hTL, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Std.HashSet.contains_ofList,
    List.contains_iff_mem, contains_false] at h
  obtain ⟨hnd, hx⟩ := h
  have hA : ∀ x ∈ availOf f In tl 0, _ := fun x hxA =>
    (hx x (mem_ent_zero hTB hxA)).resolve_left (by rw [(mem_avail hTB hDt).mp hxA]; simp)
  refine ⟨hnd, fun x hxA hxp d info cl hd hi hc y hy => ?_, fun x hxA => ?_⟩
  · rcases (hA x hxA).1 with h | h
    · exact absurd h hxp
    · exact h y (by rw [defArgs_eq hd hi hc]; exact hy)
  · rcases (hA x hxA).2 with h | ⟨⟨h1, h2⟩, h3⟩
    · exact .inl h
    · exact .inr ⟨h1, h2, h3⟩

theorem cert_of_ok {f : Clif.Function} {ctx : Ctx} {st0 : LState} {gn : Nat → Nat}
    {bl : List BLow} {In : Array (List Clif.ValueId)} (hlen : bl.length = f.blocks.length)
    (h : certOk f ctx st0 gn bl In = true) : Cert f ctx st0 gn bl (availOf f In) := by
  simp only [certOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hentry, hblocks⟩, hres⟩, hpar⟩ := h
  have hL : ∀ (bi : Nat) (B : Clif.Block), f.blocks[bi]? = some B → ∃ L, bl[bi]? = some L := by
    intro bi B hB
    exact ⟨_, List.getElem?_eq_getElem (by have := lt_of_getElem? hB; omega)⟩
  have hblk : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B →
      bl[bi]? = some L → certBlockOk f ctx st0 gn f.blocks.toArray bl.toArray In bi B L = true := by
    intro bi B L hB hL
    have := all_range hblocks (by simpa using lt_of_getElem? hB)
    simpa [List.getElem?_toArray, hB, hL] using this
  have hS := fun bi B L hB hL => certBlockOk_spec (hblk bi B L hB hL)
  have hD : ∀ (tl : Nat) (TB : Clif.Block) (TL : BLow), f.blocks[tl]? = some TB →
      bl[tl]? = some TL → DefsAt ctx TB TL.start := fun tl TB TL h1 h2 => (hS tl TB TL h1 h2).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- small
    intro bi j x hx
    obtain ⟨B, hB, -⟩ := mem_availOf.mp hx
    obtain ⟨L, hL⟩ := hL bi B hB
    exact ((hS bi B L hB hL).2.2.2.2.1 x (mem_cand hB hx)).1
  · -- entry
    intro B hB
    obtain ⟨L, hL⟩ := hL 0 B hB
    simp only [List.getElem?_toArray, hB, hL, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hentry
    refine ⟨hentry.1, fun x hx => ?_⟩
    rcases hentry.2 x (mem_ent_zero hB hx) with h | h
    · rw [(mem_avail hB (hD 0 B L hB hL)).mp hx] at h; cases h
    · exact h
  · -- closed
    intro bi j x d info cl hx hd hi hc _ y hy
    obtain ⟨B, hB, -⟩ := mem_availOf.mp hx
    obtain ⟨L, hL⟩ := hL bi B hB
    have hDb := hD bi B L hB hL
    have hm := (mem_avail hB hDb).mp hx
    have := ((hS bi B L hB hL).2.2.2.2.1 x (mem_cand hB hx)).2.1 y
      (by rw [defArgs_eq hd hi hc]; exact hy)
    have h1 := (mem_iff_first hDb).mp hm
    exact (mem_avail hB hDb).mpr ((mem_iff_first hDb).mpr ⟨this.1, by omega⟩)
  · -- statements
    intro bi B L j stm sl hB hL hs hsl
    have hDb := hD bi B L hB hL
    obtain ⟨hsl_len, -, hst, hch, hcand, -, -⟩ := hS bi B L hB hL
    obtain ⟨hnd, hargs⟩ := hst j stm hs
    have hj := lt_of_getElem? hs
    refine ⟨fun y hy => (mem_avail hB hDb).mpr (hargs y hy),
      fun r hr => ⟨?_, hDb j stm hs r hr⟩, hnd, fun x hx => ?_, fun x hx hc => ?_⟩
    · intro hrA
      have := (mem_avail hB hDb).mp hrA
      simp only [Avail.mem, (dpos_iff hDb).mpr ⟨stm, hs, hr⟩, decide_eq_true_eq] at this
      omega
    · have := (mem_avail hB hDb).mp hx
      simp only [Avail.mem] at this
      cases hp : (Avail.of B L In bi).dpos ctx x with
      | some k =>
        rw [hp] at this
        simp only [decide_eq_true_eq] at this
        by_cases hk : k < j
        · left
          exact (mem_avail hB hDb).mpr (by simp only [Avail.mem, hp, decide_eq_true_eq]; exact hk)
        · right
          obtain ⟨stm', hs', hx'⟩ := (dpos_iff hDb).mp hp
          have : k = j := by omega
          subst this
          rw [hs] at hs'; cases hs'; exact hx'
      | none =>
        rw [hp] at this
        left
        exact (mem_avail hB hDb).mpr (by simp only [Avail.mem, hp]; exact this)
    · -- clobber: the statements' fresh ranges increase
      have hm := (mem_avail hB hDb).mp hx
      have hfirst := ((mem_iff_first hDb).mp hm).2
      obtain ⟨-, -, hclob, -⟩ := hcand x (mem_cand hB hx)
      obtain ⟨sls, hsls⟩ : ∃ a, L.sl[(Avail.of B L In bi).first ctx x]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨last, hlast⟩ : ∃ a, L.sl[B.body.length - 1]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hm1 := chain_mono (lo := fun a : SLow => a.st.nextVreg)
        (hi := fun a : SLow => a.st'.nextVreg) hch (j - (Avail.of B L In bi).first ctx x) _ sls sl
        hsls (by rw [Nat.add_sub_cancel' hfirst]; exact hsl)
      have hm2 := chain_mono (lo := fun a : SLow => a.st.nextVreg)
        (hi := fun a : SLow => a.st'.nextVreg) hch (B.body.length - 1 - j) j sl last hsl
        (by rw [Nat.add_sub_cancel' (by omega)]; exact hlast)
      rcases hclob sls last hsls hlast with h | h <;> omega
  · -- no branch to the entry
    intro bi B hB b hb
    obtain ⟨L, hL⟩ := hL bi B hB
    exact ((hS bi B L hB hL).2.2.2.2.2.2 b hb).1
  · -- terminators and edges
    intro bi B L hB hL
    have hDb := hD bi B L hB hL
    obtain ⟨-, -, -, -, hcand, hterm, hedge⟩ := hS bi B L hB hL
    refine ⟨fun y hy => (mem_avail hB hDb).mpr (hterm y hy), fun x hx => ?_, fun b hb => ?_⟩
    · exact (hcand x (mem_cand hB hx)).2.2.2
    · intro tl TB htl hTB
      obtain ⟨h1, h2, h3⟩ := edgeOk_sound hlen hD (hedge b hb).2 tl TB htl hTB
      refine ⟨h1, h2, fun x hx => ?_⟩
      rcases h3 x hx with h | ⟨h1, h2, h3⟩
      · exact .inl h
      · exact .inr ⟨h1, (mem_avail hB hDb).mpr h2, h3⟩
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
      have hS := lowerShape_of_ok (gn := gnAt (gnTable st0.nextVreg (aliasOf f bl))) hb hl
        (fun n hn => gnAt_temp hn) h.1.1.1.1
      exact ⟨ctx, st0, _, _, bl, _, hS, cert_of_ok hS.len h.1.1.1.2, brIdx_of_ok h.1.1.2⟩

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
      rcases h.1.2.1 with h2 | h2
      · obtain ⟨B, hB, hB'⟩ := List.any_eq_true.mp h2
        rw [hf B hB] at hB'; cases hB'
      · exact h2

/-- A function without `tls_value` lowers to VCode without `ElfTlsGetAddr` (`lowerCheck`). -/
theorem noTls_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true)
    (hf : hasTls f = false) : vc.hasTls = false := by
  unfold lowerCheck at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      rcases h.1.2.2 with h2 | h2
      · rw [hf] at h2; cases h2
      · exact h2

/-- The calls of `f` fit the VCode's outgoing area (`lowerCheck`'s last conjunct). -/
theorem callsStack_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true) :
    CallsStack f vc.outgoing := by
  unfold lowerCheck at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Bool.and_eq_true] at h
      have h2 := h.2.1
      intro B hB st hst fn args e hi he
      have := List.all_eq_true.mp (List.all_eq_true.mp h2 B hB) st hst
      rw [hi] at this
      simp only [he, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this

/-- The entry's parameter locations and byte sizes compute (`lowerCheck`'s `entryOkB`). -/
theorem entryOk_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true) :
    (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes := by
  unfold lowerCheck at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Bool.and_eq_true] at h
      have h2 := h.2.2
      simp only [entryOkB, Bool.and_eq_true, beq_iff_eq] at h2
      refine ⟨h2.1.1, ?_⟩
      have h3 := h2.2
      split at h3
      · exact ⟨_, ‹_›⟩
      · cases h3

/-- The register-passed parameters of the entry are in x0..x8 (`lowerCheck`'s `entryOkB`). -/
theorem entryRegs_of_check {f : Clif.Function} {vc : VCode} (h : lowerCheck f vc = true) :
    ∀ l ∈ locsOf f.sig, ∀ r, l = .reg r → ∃ n, r = .x n ∧ n ≤ 8 := by
  unfold lowerCheck at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Bool.and_eq_true] at h
      have h2 := h.2.2
      simp only [entryOkB, Bool.and_eq_true, beq_iff_eq] at h2
      intro l hl r hr
      have := List.all_eq_true.mp h2.1.2 l hl
      subst hr
      cases r with
      | x n => exact ⟨n, rfl, by simpa using this⟩
      | _ => cases this

end Backend.Proof.Driver
