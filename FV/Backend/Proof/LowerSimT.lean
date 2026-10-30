import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.LowerContractT

/-!
# The typed driver simulation (S11e5 Stage C, slice 7)

`LowerSim.lean`'s simulation over the typed model (`DriverCheckTy.lean`): a float-capable
context (`LowerShapeT`: `CtxInvT` + `InstScopeT`), the typed entry code (`preT`: the `Args`
pairs and stack-argument loads of each parameter's class, an `ldr s`/`ldr d` for a float one),
the typed result copies and edge arguments (`segT`, `vregOf`), and the driver's calls of one
context (`InstCallsT`, `TermCallsT` with class-aware returns, `TryCallsT`, `TryIndCallsT`).

* `MatchT`: `Match` at the typed positions (`posT`), and every tracked value typed in the
  context (`TypedA`: its class is its CLIF value's, so a return puts it in its class's
  register).
* `DriverHypT`: `DriverHyp` with `LowerShapeT`, the typed calls and `Compile.functionET`.
* `stmt_stepT`, `term_stepT`, `term_step_tryT`, `entry_stepT`, `entry_step2T`, `sim_runT`,
  `driver_correctT`: a returned value is in the ABI return register of its type's class
  (`retRegsT`, `RunOkT`); the stack-passed float parameters are loaded under `MemRefinesFP`.
  The `_abi` variants (`term_stepT_abi`, `sim_runT_abi`, `driver_correctT_abi`, `RunOkTAbi`)
  also return the frame's `sretRet f` values, in the return registers after the CLIF values.

Integer specialization: `DriverHyp.toT` (an integer driver hypothesis is a typed one).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- Every tracked value has a context type. -/
def TypedA (ctx : Ctx) (A : List Clif.ValueId) : Prop := ∀ x ∈ A, ∃ t, ctx.valueType? x = some t

/-- **The typed simulation relation** (`Match` at `posT`, with the tracked values typed). -/
def MatchT (f : Clif.Function) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
    (A : Nat → Nat → List Clif.ValueId) {W : Type} (MR : MemRelTW W)
    (slots : List (Clif.SlotId × Nat)) (s : Clif.State) (vs : VState CV W) : Prop :=
  s.callers = [] ∧ s.frame.func = f ∧ s.frame.slots = slots ∧ MR slots s.mem vs.w ∧
    ∃ B j, f.blocks[vs.b]? = some B ∧ s.frame.term = B.term ∧ j ≤ B.body.length ∧
    s.frame.body = B.body.drop j ∧ vs.k = posT f ctx R bl vs.b j ∧
    Held gn (A vs.b j) vs.ρ s.frame ∧ DFGCons ctx (restrict s.frame (A vs.b j)) ∧
    TypedA ctx (A vs.b j)

/-- The class of a CLIF type's context type is the type's class. -/
theorem valClass_ofClif (ty : Clif.Ty) : (CTy.ofClif ty).valClass = tyClass ty := by
  cases ty <;> rfl

/-- `retRegsT` of a concatenation starts with `retRegsT` of the prefix. -/
theorem retRegsT_append : ∀ (a b : List RegClass) (nx nv : Nat),
    ∃ r, retRegsT (a ++ b) nx nv = retRegsT a nx nv ++ r
  | [], b, nx, nv => ⟨_, rfl⟩
  | .int :: a, b, nx, nv => by
    obtain ⟨r, hr⟩ := retRegsT_append a b (nx + 1) nv
    exact ⟨r, by simp [retRegsT, hr]⟩
  | .float :: a, b, nx, nv => by
    obtain ⟨r, hr⟩ := retRegsT_append a b nx (nv + 1)
    exact ⟨r, by simp [retRegsT, hr]⟩

/-- **The returned values are in their ABI return registers** (`RetPins` over classes): the
registers of the `rets` pairs `us` start with the return registers of the values' type classes
(`retRegsT` of the first `vals.length`, with the extra classes `cs` of an `sret` function's
returned pointer counted beyond them); after them, in x8. -/
def RetRegsOk (vals : List Clif.Val) (us : List (Reg × Reg)) : Prop :=
  ∃ cs, us.map (·.2) =
    retRegsT ((vals.map (fun v => tyClass v.ty) ++ cs).take vals.length) 0 0 ++
      List.replicate ((vals.map (fun v => tyClass v.ty) ++ cs).length - vals.length) (Reg.x 8)

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow}

/-! ## Segments (typed model) -/

theorem seg_eqT {bi j : Nat} {B : Clif.Block} {L : BLow} {stm : Clif.Stmt} {sl : SLow}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) (hs : B.body[j]? = some stm)
    (hsl : L.sl[j]? = some sl) :
    segT f ctx R bl bi j =
      (sl.st'.emitted.toList ++ extraOfT ctx stm.results sl.rss).map (·.mapRegs R) := by
  simp [segT, hB, hL, hs, hsl]

theorem pos_succT (bi j : Nat) :
    posT f ctx R bl bi (j + 1) = posT f ctx R bl bi j + (segT f ctx R bl bi j).length := by
  simp [posT, List.range_succ, Nat.add_assoc]

theorem seg_atT {vb : VBlock} {bi : Nat} {B : Clif.Block}
    (hcode : vb.insts.toList = preT f ctx R bi ++ ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++
      tseg R bl bi) (htne : tseg R bl bi ≠ []) {j : Nat} (hj : j < B.body.length) :
    SegAt vb (posT f ctx R bl bi j) (segT f ctx R bl bi j) ∧ posT f ctx R bl bi (j + 1) < vb.insts.size := by
  have hsplit := flatten_range_split (segT f ctx R bl bi) hj
  rw [hsplit] at hcode
  have hlen : (preT f ctx R bi ++ ((List.range j).map (segT f ctx R bl bi)).flatten).length = posT f ctx R bl bi j := by
    simp [posT, List.length_flatten, List.map_map, Function.comp_def]
  constructor
  · have : vb.insts.toList = (preT f ctx R bi ++ ((List.range j).map (segT f ctx R bl bi)).flatten) ++
        segT f ctx R bl bi j ++ ((((List.range (B.body.length - (j + 1))).map
          fun i => segT f ctx R bl bi (j + 1 + i))).flatten ++ tseg R bl bi) := by
      rw [hcode]; simp [List.append_assoc]
    have h := segAt_of_toList this
    rwa [hlen] at h
  · have hsz : vb.insts.size = vb.insts.toList.length := by simp
    rw [hsz, hcode, pos_succT, ← hlen]
    have : 0 < (tseg R bl bi).length := List.length_pos_iff.mpr htne
    simp only [List.length_append]
    omega

theorem tseg_atT {vb : VBlock} {bi : Nat} {B : Clif.Block}
    (hcode : vb.insts.toList = preT f ctx R bi ++ ((List.range B.body.length).map (segT f ctx R bl bi)).flatten ++
      tseg R bl bi) :
    SegAt vb (posT f ctx R bl bi B.body.length) (tseg R bl bi) ∧
      vb.insts.size = posT f ctx R bl bi B.body.length + (tseg R bl bi).length := by
  have hlen : (preT f ctx R bi ++ ((List.range B.body.length).map (segT f ctx R bl bi)).flatten).length =
      posT f ctx R bl bi B.body.length := by
    simp [posT, List.length_flatten, List.map_map, Function.comp_def]
  constructor
  · have h := segAt_of_toList (L₂ := []) (by rw [hcode, List.append_nil])
    rwa [hlen] at h
  · have hsz : vb.insts.size = vb.insts.toList.length := by simp
    rw [hsz, hcode, List.length_append, hlen]

theorem extraOfT_nil {results : List Nat} {rss : List (List Reg)}
    (h : ∀ (k : Nat) rs, rss[k]? = some rs → ∃ out cls, rs = [.vreg out cls]) :
    extraOfT ctx results rss = [] := by
  unfold extraOfT
  rw [List.filterMap_eq_nil_iff]
  intro p hp
  obtain ⟨k, hk⟩ := List.getElem_of_mem hp
  obtain ⟨hk1, hk2⟩ := hk
  have := List.getElem?_eq_getElem (l := results.zip rss) hk1
  rw [hk2] at this
  have hr : rss[k]? = some p.2 := by
    rw [List.getElem?_zip_eq_some] at this
    exact this.2
  obtain ⟨out, cls, he⟩ := h k p.2 hr
  obtain ⟨r, rs⟩ := p
  simp only at he
  subst he
  rfl

/-- `vregNum` on virtual registers of any classes. -/
theorem mapM_vregNum {α : Type} (g : α → Reg) (n : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, ∃ c, g a = .vreg (n a) c) →
      List.mapM (vregNum ∘ g) l = .ok (l.map n)
  | [], _ => rfl
  | a :: l, hg => by
    obtain ⟨c, hc⟩ := hg a (List.mem_cons_self ..)
    simp [List.mapM_cons, hc, vregNum,
      mapM_vregNum g n l (fun b hb => hg b (List.mem_cons_of_mem _ hb))] <;> rfl

theorem mapM_vregNum' {α : Type} (g : α → Reg) (n : α → Nat) (l : List α)
    (hg : ∀ a ∈ l, ∃ c, g a = .vreg (n a) c) : List.mapM vregNum (l.map g) = .ok (l.map n) := by
  rw [List.mapM_map]; exact mapM_vregNum g n l hg

/-- The parallel copy of an edge, for virtual registers of any classes. -/
theorem edgeEnv_eqT {V : Type} {vc : VCode} {b s : Nat} {vb sb : VBlock}
    (hvb : vc.blocks[b]? = some vb) (hsb : vc.blocks[s]? = some sb) {α β : Type}
    {as : List α} {qs : List β} {gx : α → Reg} {nx : α → Nat} {gp : β → Reg} {np : β → Nat}
    (hba : vb.branchArgs = (as.map gx).toArray) (hgx : ∀ a ∈ as, ∃ c, gx a = .vreg (nx a) c)
    (hpa : sb.params = (qs.map gp).toArray) (hgp : ∀ q ∈ qs, ∃ c, gp q = .vreg (np q) c)
    (hl : qs.length = as.length)
    (ρ : Nat → V) : edgeEnv vc b s ρ = some (parCopyEnv ρ (qs.map np) (as.map nx)) := by
  unfold edgeEnv
  simp [hvb, hsb, hba, hpa, hl, Except.toOption, mapM_vregNum gx nx as hgx,
    mapM_vregNum' gx nx as hgx, mapM_vregNum' gp np qs hgp]

/-- A typed frame's values have the classes of their context types. -/
theorem getMany_classes {ctx : Ctx} {fr : Clif.Frame} (hT : FrameTyped ctx fr) :
    ∀ {xs : List Clif.ValueId} {vals : List Clif.Val}, fr.getMany xs = .ok vals →
      (∀ x ∈ xs, ∃ t, ctx.valueType? x = some t) →
      xs.map (valClassOf ctx) = vals.map (fun v => tyClass v.ty)
  | [], vals, h, _ => by simp only [Clif.Frame.getMany, Clif.Res.ok.injEq] at h; subst h; rfl
  | x :: xs, vals, h, hty => by
    simp only [Clif.Frame.getMany, Clif.Frame.get] at h
    cases hx : fr.regs x with
    | none => rw [hx] at h; simp [Clif.Res.ofOption] at h
    | some v =>
      rw [hx] at h
      simp only [Clif.Res.ofOption_some, Clif.Res.ok_bind] at h
      cases hr : fr.getMany xs with
      | ok vs0 =>
        rw [hr] at h
        simp only [Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at h
        subst h
        obtain ⟨t, ht⟩ := hty x (List.mem_cons_self ..)
        have hv := hT x t v ht hx
        simp only [List.map_cons, getMany_classes hT hr (fun y hy => hty y (List.mem_cons_of_mem _ hy))]
        congr 1
        simp only [valClassOf, ht, Option.map_some, Option.getD_some, ← hv, valClass_ofClif]
      | trap => rw [hr] at h; cases h
      | stuck => rw [hr] at h; cases h

end

/-! ## Hypotheses of the typed driver simulation -/

/-- **Everything the typed simulation assumes** (`DriverHyp` over the typed model): the typed
structure of the VCode (`LowerShapeT`), the SSA certificate, the driver-level semantics facts,
the driver's calls in this context (`InstCallsT`, `TermCallsT`, `TryCallsT`, `TryIndCallsT`),
extern-only calls, the typed movement scope and a successful `VCode.cfg`. -/
structure DriverHypT (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
    (gn : Nat → Nat) (bl : List BLow) (A : Nat → Nat → List Clif.ValueId) {W : Type}
    (sem : ISem CV W) (MR : MemRelTW W) (env : Clif.Env) (p : Clif.Program) : Prop where
  shape : LowerShapeT f vc ctx st0 R gn bl
  cert : Cert f ctx st0 gn bl A
  dsem : DriverSemG sem
  /-- `lower` on statements (`instCallsT_of_rules`) -/
  insts : InstCallsT f ctx sem MR env p
  /-- terminator calls (`termCallsT_of_rules`) -/
  terms : TermCallsT ctx sem MR
  ext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  /-- the signature of an indirect call is among `f`'s indirect-call signatures, with register
  arguments (`E2E.InSubset.indSigs`) -/
  indSig : ∀ B ∈ f.blocks, ∀ st ∈ B.body, IndSigOk f (indSigs f) st.inst
  /-- `f` is in the typed movement scope (`E2E.InSubsetT.subsetET`) -/
  subET : Compile.functionET f = true
  /-- `br_table` indices have at most 32 bits (`lowerCheck`'s `brIdxOk`) -/
  brIdx : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term
  /-- no tail calls (`return_call` is outside clif-subset-v2 E) -/
  noTail : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args
  /-- M4: `lower_branch` on `try_call`s (`tryCalls_of_rules`), for an outgoing area that holds
  every `try_call`'s stack arguments (`lowerCheck`'s `callsStackOkB`) -/
  tries : ∃ out, TryCallsT f ctx sem MR env p out ∧ TryStack f out
  /-- a `try_call` calls an extern (`E2E.InSubset.tryExterns`) -/
  tryExt : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  /-- M4: `lower_branch` on `try_call_indirect`s (`tryIndCalls_of_rules`) -/
  tryInd : TryIndCallsT f ctx sem MR env p (indSigs f)
  /-- the signature of a `try_call_indirect` is among `f`'s indirect-call signatures, with
  register arguments (`E2E.InSubset.indSigs`) -/
  tryIndSig : ∀ B ∈ f.blocks, ∀ c args et s, B.term = .tryCallIndirect c args et →
    f.sigDecls.lookup et.sig = some s → s ∈ indSigs f ∧ s.params.length ≤ 8
  cfg : ∃ ss ps, vc.cfg = .ok (ss, ps)
  /-- the signature's parameter locations and byte sizes compute, one per parameter
  (`lowerCheckT`'s `entryOkBT`) -/
  entryLocs : (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)}

/-- The integer-position operands of `f`'s terminators (`termIntPos_of_functionET`). -/
theorem DriverHypT.termIntPos (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {B : Clif.Block} (hB : B ∈ f.blocks) : TermIntPos ctx B.term :=
  termIntPos_of_functionET H.subET H.shape.hctx.choose_spec hB

theorem DriverHypT.blow (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p) {bi : Nat}
    {B : Clif.Block} (hB : f.blocks[bi]? = some B) : ∃ L, bl[bi]? = some L := by
  have hlt : bi < f.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  exact ⟨bl[bi]'(by rw [H.shape.len]; exact hlt), List.getElem?_eq_getElem _⟩

/-- **Statement step.** -/
theorem stmt_stepT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchT f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
        MatchT f ctx R gn bl A MR slots s' vs') ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vc sem ⟨b, k, ρ, w⟩ c) := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons, htyA⟩ := hm
  simp only at hk hheld hcons hB hmem htyA
  subst hk
  obtain ⟨hjlt, hstm, hrest⟩ := drop_cons_split (hbd ▸ hbody)
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, hsllen, hstmts, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨sl, hsl⟩ : ∃ sl, L.sl[j]? = some sl :=
    ⟨L.sl[j]'(by omega), List.getElem?_eq_getElem _⟩
  obtain ⟨⟨info, hinfo, hclif, hres⟩, hemp, hst0, ⟨tr, hrun⟩, halias⟩ := hstmts j stm sl hstm hsl
  obtain ⟨ranges, hctx⟩ := H.shape.hctx
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  have hstmmem : stm ∈ B.body := List.mem_of_getElem? hstm
  have hok := H.insts (L.start + j) info stm.inst sl.st sl.rss sl.st' tr
    ⟨B, hBmem, stm, hstmmem, rfl⟩ hinfo hclif (H.indSig B hBmem stm hstmmem) hemp
    (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0) hrun
  rw [hres] at hok
  obtain ⟨hargs, hresults, hnodup, hnext, hnoclob⟩ := H.cert.stmt b B L j stm sl hB hL hstm hsl
  let fr' := restrict s.frame (A b j)
  let ρ₀ : Nat → CV := fun n => ρ (gn n)
  have hvh : ValsHeld fr' ρ₀ := by
    intro x v hx
    have hxA : x ∈ A b j := restrict_regs_isSome (by rw [hx]; rfl)
    obtain ⟨v', hv', hh⟩ := hheld x hxA
    rw [restrict_regs_of_mem hxA, hv'] at hx
    cases hx
    exact hh
  have hrun' := hok.run fr' s.mem ρ₀ w (by simp [fr', restrict, hfunc, H.shape.ctxInvT.func])
    hvh hcons (by simpa [fr', restrict, hslots] using hmem)
  have hio : instOutcome env p fr' s.mem stm.inst = instOutcome env p s.frame s.mem stm.inst :=
    instOutcome_congr (fr := s.frame) (fr' := fr') rfl rfl env p s.mem stm.inst
      fun x hx => restrict_regs_of_mem (hargs x hx)
  rw [hio] at hrun'
  have hstep := step_stmt env p s stm rest hbody
    (fun fn args hi e he => H.ext B hBmem stm hstmmem fn args hi e (by rw [← hfunc]; exact he))
    hind
  let D : Nat → Prop := fun n => sl.st.nextVreg ≤ n ∧ n < sl.st'.nextVreg
  have hD : ∀ d, D d → gn d = d := fun d hd => H.shape.temps d (by simp only [D] at hd; omega)
  have hdefs : ∀ m ∈ sl.st'.emitted.toList, ∀ d ∈ vdefs m, D d := hok.defs
  have hAg : Agree gn D ρ₀ ρ := fun _ _ => rfl
  have huses_of : UsesOk sl.st fr' sl.st'.emitted.toList →
      ∀ m ∈ sl.st'.emitted.toList, ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
    intro hU m hm u hu
    rcases hU m hm u hu with h | h
    · by_cases h' : u < sl.st'.nextVreg
      · exact .inl ⟨h, h'⟩
      · right
        rw [H.shape.temps u (by omega)]
        intro hd; exact h' hd.2
    · right; exact hnoclob u (restrict_regs_isSome h)
  have hren := seqRun_rename (sem := sem) (ρ₀ := ρ₀) (ρ := ρ) (w := w) H.shape.ren
    (H.dsem.rename R gn H.shape.ren) hD hdefs
  have hcodeseg := seg_atT hcode htne hjlt
  constructor
  · intro s' hs
    rw [hstep] at hs
    cases hO : instOutcome env p s.frame s.mem stm.inst with
    | trap c => rw [hO] at hs; cases hs
    | stuck m => rw [hO] at hs; cases hs
    | ok r =>
      obtain ⟨vals, cm'⟩ := r
      rw [hO] at hs hrun'
      simp only [Clif.StepResult.ofRes, Clif.continueWith] at hs
      split at hs
      · rename_i regs' hset
        cases hs
        obtain ⟨hU, ρ₀', w', hsr, hrh, hmr⟩ := hrun'
        obtain ⟨ρ', hsr', hAg'⟩ := (hren (huses_of hU) hAg).1 hsr
        have hextra : extraOfT ctx stm.results sl.rss = [] := by
          rcases hrh with h0 | ⟨hl, hh⟩
          · rw [h0]; rfl
          · apply extraOfT_nil
            intro k rs hk
            have : k < vals.length := by
              have := (List.getElem?_eq_some_iff.mp hk).1; omega
            obtain ⟨out, cls, he, -, -⟩ := hh k rs vals[k] hk (List.getElem?_eq_getElem this)
            exact ⟨out, cls, he⟩
        have hseg : segT f ctx R bl b j = sl.st'.emitted.toList.map (·.mapRegs R) := by
          rw [seg_eqT hB hL hstm hsl, hextra, List.append_nil]
        obtain ⟨hsegat, hlt⟩ := hcodeseg
        rw [hseg] at hsegat
        rw [pos_succT, hseg] at hlt
        have hstar := seqRun_fall_star hvb hsegat (by simpa using hlt) hsr'
        rw [List.length_map] at hstar
        refine ⟨_, hstar, hcall, hfunc, hslots, by simpa [fr', restrict, hslots] using hmr,
          B, j + 1, hB, hterm, hjlt, hrest, ?_, ?_, ?_, ?_⟩
        · simp [pos_succT, hseg]
        · -- held
          intro x hx
          rcases hnext x hx with hxA | hxr
          · have hxr : x ∉ stm.results := fun e => (hresults x e).1 hxA
            obtain ⟨v, hv, hh⟩ := hheld x hxA
            refine ⟨v, ?_, ?_⟩
            · show regs' x = some v
              rw [setMany_other hset hxr, hv]
            have hnd : ¬ D x := by
              have h4 : x < st0.nextVreg := H.cert.small b j x hxA
              intro hd
              have h3 : sl.st.nextVreg ≤ x := hd.1
              exact absurd (Nat.lt_of_lt_of_le h4 hst0) (Nat.not_lt.mpr h3)
            have h1 : ρ₀' x = ρ₀ x := seqRun_fall_frame (fun m hm hxm => hnd (hdefs m hm x hxm)) hsr
            have h2 := hAg' x (.inr (hnoclob x hxA))
            show VHolds v (ρ' (gn x))
            rw [← h2, h1]
            exact hh
          · obtain ⟨m, v, hxm, hvm, hrv⟩ := setMany_mem hset hnodup x hxr
            refine ⟨v, hrv, ?_⟩
            rcases hrh with h0 | ⟨hl, hh⟩
            · rw [h0] at hxr; cases hxr
            · have hml : m < sl.rss.length := by
                have := (List.getElem?_eq_some_iff.mp hvm).1; omega
              obtain ⟨out, cls, he, hout, hvo⟩ :=
                hh m sl.rss[m] v (List.getElem?_eq_getElem hml) hvm
              have hal := halias m x out cls hxm (by rw [List.getElem?_eq_getElem hml, he])
              have hcond : D out ∨ ¬ D (gn out) := by
                rcases hout with h | h
                · by_cases h' : out < sl.st'.nextVreg
                  · exact .inl ⟨h, h'⟩
                  · right; rw [H.shape.temps out (by omega)]; intro hd; exact h' hd.2
                · right; exact hnoclob out (restrict_regs_isSome h)
              show VHolds v (ρ' (gn x))
              rw [hal, ← hAg' out hcond]
              exact hvo
        · -- DFG consistency
          refine ⟨?_, ?_⟩
          rotate_left
          · -- the frame is typed
            intro x t v ht hv
            have hxA' : x ∈ A b (j + 1) := restrict_regs_isSome (by rw [hv]; rfl)
            have hv' : regs' x = some v := by
              have := restrict_regs_of_mem
                (fr := { s.frame with regs := regs', body := rest }) hxA'
              rw [this] at hv; exact hv
            by_cases hxr : x ∈ stm.results
            · obtain ⟨m, v', hxm, hvm, hrv⟩ := setMany_mem hset hnodup x hxr
              have hvv : v' = v := Option.some.inj (hrv.symm.trans hv')
              obtain ⟨tys, hrt, hrty, -⟩ := H.shape.ctxInvT.resTys _ info stm.inst hinfo hclif
              have hvt := instOutcome_types hO (by rw [hfunc]; exact hrt)
              have htm : info.resTys[m]? = some (CTy.ofClif v'.ty) := by
                rw [hrty, ← hvt]
                simp [List.getElem?_map, hvm]
              have := H.cert.resTy _ info hinfo m x _ (by rw [hres]; exact hxm) htm
              rw [this] at ht
              rw [← hvv]; exact Option.some.inj ht
            · have hxA : x ∈ A b j := (hnext x hxA').resolve_right hxr
              refine hcons.2 x t v ht ?_
              rw [restrict_regs_of_mem hxA, ← setMany_other hset hxr]
              exact hv'
          intro x d info' cl v hd hinfo' hcl hp hv
          have hxA' : x ∈ A b (j + 1) := restrict_regs_isSome (by rw [hv]; rfl)
          have hv' : regs' x = some v := by
            have := restrict_regs_of_mem
              (fr := { s.frame with regs := regs', body := rest }) hxA'
            rw [this] at hv; exact hv
          have hcl_args := H.cert.closed b (j + 1) x d info' cl hxA' hd hinfo' hcl hp
          rcases hnext x hxA' with hxA | hxr
          · have hxr : x ∉ stm.results := fun e => (hresults x e).1 hxA
            have hvx : (restrict s.frame (A b j)).regs x = some v := by
              rw [restrict_regs_of_mem hxA, ← setMany_other hset hxr]; exact hv'
            obtain ⟨vals0, hev, hlk⟩ := hcons.1 x d info' cl v hd hinfo' hcl hp hvx
            refine ⟨vals0, fun cm => ?_, hlk⟩
            rw [← hev cm]
            refine evalInst_congr ?_ ?_ cm cl ?_
            · rfl
            · rfl
            intro y hy
            have hyA := H.cert.closed b j x d info' cl hxA hd hinfo' hcl hp y hy
            have hyr : y ∉ stm.results := fun e => (hresults y e).1 hyA
            rw [restrict_regs_of_mem (hcl_args y hy), restrict_regs_of_mem hyA]
            exact setMany_other hset hyr
          · have hd' := (hresults x hxr).2
            rw [hd] at hd'
            cases hd'
            rw [hinfo] at hinfo'
            cases hinfo'
            rw [hclif] at hcl
            cases hcl
            have hev : Clif.evalInst s.frame s.mem stm.inst = .ok (vals, cm') := by
              rw [← instOutcome_of_pure (env := env) (p := p) hp]; exact hO
            obtain ⟨-, hall⟩ := evalInst_pure hp hev
            obtain ⟨m, v', hxm, hvm, hrv⟩ := setMany_mem hset hnodup x hxr
            rw [hrv] at hv'
            cases hv'
            refine ⟨vals, fun cm => ?_, ?_⟩
            · rw [← hall cm]
              refine evalInst_congr ?_ ?_ cm _ ?_
              · rfl
              · rfl
              intro y hy
              have hyA := hargs y hy
              have hyr : y ∉ stm.results := fun e => (hresults y e).1 hyA
              rw [restrict_regs_of_mem (hcl_args y hy)]
              exact setMany_other hset hyr
            · rw [hres]
              exact lookup_zip_nodup hnodup (setMany_length hset) m x _ hxm hvm
        · -- the tracked values are typed
          intro x hx
          rcases hnext x hx with hxA | hxr
          · exact htyA x hxA
          · obtain ⟨tys, -, hrty, hrl⟩ := H.shape.ctxInvT.resTys _ info stm.inst hinfo hclif
            obtain ⟨m, hxm⟩ := List.mem_iff_getElem?.mp hxr
            have hml : m < tys.length := by
              have := (List.getElem?_eq_some_iff.mp hxm).1; rw [← hres] at this; omega
            have htm : info.resTys[m]? = some (CTy.ofClif tys[m]) := by
              rw [hrty]; simp [List.getElem?_map, List.getElem?_eq_getElem hml]
            exact ⟨_, H.cert.resTy _ info hinfo m x _ (by rw [hres]; exact hxm) htm⟩
      · cases hs
  · intro c hs hexp
    rw [hstep] at hs
    cases hO : instOutcome env p s.frame s.mem stm.inst with
    | ok r => rw [hO] at hs; simp only [Clif.StepResult.ofRes, Clif.continueWith] at hs; split at hs <;> cases hs
    | stuck m => rw [hO] at hs; cases hs
    | trap c' =>
      rw [hO] at hs hrun'
      cases hs
      obtain ⟨hU, k', i, ops, ρ₁, w₁, outs, w₂, hsr, htc⟩ := hrun' hexp
      obtain ⟨ρ₁', hsr', -, -⟩ := (hren (huses_of hU) hAg).2 hsr
      have hsegat := hcodeseg.1
      rw [seg_eqT hB hL hstm hsl, List.map_append] at hsegat
      obtain ⟨hstar, -, hi, hops, hsem, -, -⟩ := seqRun_stop_star hvb hsegat.append_left hsr'
      exact ⟨b, _, ρ₁', w₁, vb, _, _, outs, w₂, hstar, hvb, hi, hops, hsem,
        by rw [trapCode?_mapRegs]; exact htc⟩


/-- **Entering a successor block.** The CLIF frame after `enterBlock` and the VCode file after
the parallel copy of the (renamed) arguments into the parameters match at the successor. -/
theorem enter_matchT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b : Nat} {B : Clif.Block} (hB : f.blocks[b]? = some B)
    (hcall : s.callers = []) (hfunc : s.frame.func = f) (hslots : s.frame.slots = slots)
    {ρ : Nat → CV} (hheld : Held gn (A b B.body.length) ρ s.frame)
    (hcons : DFGCons ctx (restrict s.frame (A b B.body.length)))
    (htyA : TypedA ctx (A b B.body.length))
    {bc : Clif.BlockCall} (hbc : bc.block ∈ edgeIds B.term) {tl : Nat}
    (htl : blockIdx? f bc.block = some tl)
    {fr2 : Clif.Frame} (hent : Clif.enterBlock s.frame bc = .ok fr2) {ρ₂ : Nat → CV}
    (hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x)) {xs : List Nat}
    (hxl : xs.length = bc.args.length)
    (hxv : ∀ (m : Nat) a v x, bc.args[m]? = some a → s.frame.regs a = some v → xs[m]? = some x →
      VHolds v (ρ₂ x))
    {w₂ : W} (hmr : MR slots s.mem w₂) :
    ∃ TB, f.blocks[tl]? = some TB ∧ bc.args.length = TB.params.length ∧ tl ≠ 0 ∧
      MatchT f ctx R gn bl A MR slots { s with frame := fr2 }
        ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) xs, w₂⟩ := by
  obtain ⟨TB, args, regs, hTBf, hargs, hty, hset, rfl⟩ := enterBlock_spec hent
  rw [hfunc] at hTBf
  have hTB := blockIdx_block htl hTBf
  have hne0 : tl ≠ 0 := fun e => H.cert.noEntry b B hB bc.block hbc (e ▸ htl)
  obtain ⟨hl1, hgm⟩ := getMany_spec hargs
  have hl2 := setMany_length hset
  have hlen : bc.args.length = TB.params.length := by simp at hl2; omega
  obtain ⟨-, -, hedge⟩ := H.cert.term b B _ hB (H.blow hB).choose_spec
  obtain ⟨hnd, hpA, hA0⟩ := hedge bc.block hbc tl TB htl hTB
  have hTBmem : TB ∈ f.blocks := List.mem_of_getElem? hTB
  have hpos : posT f ctx R bl tl 0 = 0 := by
    simp [posT, preT]
    cases tl with
    | zero => exact absurd rfl hne0
    | succ n => rfl
  refine ⟨TB, hTB, hlen, hne0, hcall, hfunc, hslots, hmr, TB, 0, hTB, rfl, Nat.zero_le _,
    by simp, hpos.symm, ?_, ?_, ?_⟩
  · intro x hx
    rcases hA0 x hx with ⟨hxp, -⟩ | ⟨hxp, hxA, hgx⟩
    · obtain ⟨m, v, hxm, hvm, hrv⟩ := setMany_mem hset hnd x hxp
      refine ⟨v, hrv, ?_⟩
      have hm : m < bc.args.length := by
        have := (List.getElem?_eq_some_iff.mp hxm).1; simp at this; omega
      have ha := List.getElem?_eq_getElem hm
      obtain ⟨v', hv', hvm'⟩ := hgm m _ ha
      rw [hvm] at hvm'; cases hvm'
      have hgp : gn x = x := by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxp
        exact H.shape.params TB hTBmem q hq
      have hxm' : xs[m]? = some xs[m] := List.getElem?_eq_getElem (by omega)
      show VHolds v (parCopyEnv ρ₂ (TB.params.map (·.1)) xs (gn x))
      rw [hgp, parCopyEnv_param hnd (by simp; omega) m hxm hxm']
      exact hxv m _ v _ ha hv' hxm'
    · obtain ⟨v, hv, hh⟩ := hheld x hxA
      refine ⟨v, by show regs x = some v; rw [setMany_other hset hxp]; exact hv, ?_⟩
      show VHolds v (parCopyEnv ρ₂ (TB.params.map (·.1)) xs (gn x))
      rw [parCopyEnv_other hgx, hρ₂ x hxA]
      exact hh
  rotate_left
  · intro x hx
    rcases hA0 x hx with ⟨hxp, -⟩ | ⟨-, hxA, -⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxp
      exact ⟨_, H.cert.paramTy TB hTBmem q hq⟩
    · exact htyA x hxA
  refine ⟨?_, ?_⟩
  rotate_left
  · -- the frame is typed
    intro x t v ht hv
    have hx0 : x ∈ A tl 0 := restrict_regs_isSome (by rw [hv]; rfl)
    have hv' : regs x = some v := by
      have := restrict_regs_of_mem (fr := { s.frame with regs, body := TB.body, term := TB.term }) hx0
      rw [this] at hv; exact hv
    by_cases hxp : x ∈ TB.params.map (·.1)
    · obtain ⟨q, hq, rfl, hqt⟩ := setMany_param_ty hset hnd hty hxp hv'
      rw [H.cert.paramTy TB hTBmem q hq] at ht
      rw [hqt]; exact Option.some.inj ht
    · rcases hA0 x hx0 with ⟨hxp', -⟩ | ⟨-, hxA, -⟩
      · exact absurd hxp' hxp
      · refine hcons.2 x t v ht ?_
        rw [restrict_regs_of_mem hxA, ← setMany_other hset hxp]
        exact hv'
  · intro x d info cl v hd hinfo hcl hp hv
    have hx0 : x ∈ A tl 0 := restrict_regs_isSome (by rw [hv]; rfl)
    have hv' : regs x = some v := by
      have := restrict_regs_of_mem (fr := { s.frame with regs, body := TB.body, term := TB.term }) hx0
      rw [this] at hv; exact hv
    rcases hA0 x hx0 with ⟨-, hdn⟩ | ⟨hxp, hxA, -⟩
    · rw [hdn] at hd; cases hd
    · have hvx : (restrict s.frame (A b B.body.length)).regs x = some v := by
        rw [restrict_regs_of_mem hxA, ← setMany_other hset hxp]; exact hv'
      obtain ⟨vals0, hev, hlk⟩ := hcons.1 x d info cl v hd hinfo hcl hp hvx
      refine ⟨vals0, fun cm => ?_, hlk⟩
      rw [← hev cm]
      refine evalInst_congr ?_ ?_ cm cl ?_
      · rfl
      · rfl
      intro y hy
      have hy0 := H.cert.closed tl 0 x d info cl hx0 hd hinfo hcl hp y hy
      have hyA := H.cert.closed b B.body.length x d info cl hxA hd hinfo hcl hp y hy
      have hyp : y ∉ TB.params.map (·.1) := hpA x hx0 hxp d info cl hd hinfo hcl y hy
      rw [restrict_regs_of_mem hy0, restrict_regs_of_mem hyA]
      exact setMany_other hset hyp

/-- **Entering a branch's successor** (`enter_matchT` with the branch arguments' vregs). -/
theorem enter_match_brT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b : Nat} {B : Clif.Block} (hB : f.blocks[b]? = some B)
    (hcall : s.callers = []) (hfunc : s.frame.func = f) (hslots : s.frame.slots = slots)
    {ρ : Nat → CV} (hheld : Held gn (A b B.body.length) ρ s.frame)
    (hcons : DFGCons ctx (restrict s.frame (A b B.body.length)))
    (htyA : TypedA ctx (A b B.body.length))
    {bc : Clif.BlockCall} (hbc : bc ∈ dests B.term) {tl : Nat} (htl : blockIdx? f bc.block = some tl)
    {fr2 : Clif.Frame} (hent : Clif.enterBlock s.frame bc = .ok fr2) {ρ₂ : Nat → CV}
    (hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x)) {w₂ : W}
    (hmr : MR slots s.mem w₂) :
    ∃ TB, f.blocks[tl]? = some TB ∧ bc.args.length = TB.params.length ∧ tl ≠ 0 ∧
      MatchT f ctx R gn bl A MR slots { s with frame := fr2 }
        ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) (bc.args.map gn), w₂⟩ := by
  refine enter_matchT H hB hcall hfunc hslots hheld hcons htyA (mem_edgeIds_of_dests hbc) htl hent
    hρ₂
    (by simp) (fun m a v x ha hv hx => ?_) hmr
  have haA : a ∈ A b B.body.length :=
    (H.cert.term b B _ hB (H.blow hB).choose_spec).1 _
      (termArgs_abiTerm (args_termArgs hbc _ (List.mem_of_getElem? ha)))
  obtain ⟨v', hv', hh⟩ := hheld a haA
  rw [hv] at hv'; cases hv'
  simp only [List.getElem?_map, ha, Option.map_some, Option.some.injEq] at hx
  subst hx
  rw [hρ₂ a haA]; exact hh

/-- A `return` that completes returns values of the function's return types. -/
theorem stepTerm_ret_tys {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {xs : List Clif.ValueId} (hcall : s.callers = []) {vals : List Clif.Val} {cm : Clif.Mem}
    (h : Clif.stepTerm env p s (.ret xs) = .done vals cm) :
    vals.map (·.ty) = Clif.AbiParam.tys s.frame.func.sig.returns := by
  obtain ⟨-, -, hdn⟩ := stepTerm_ret (env := env) (p := p) (s := s) (xs := xs) hcall
  obtain ⟨hg, -⟩ := hdn vals cm h
  simp only [Clif.stepTerm, hg, Clif.StepResult.ofRes, Clif.returnValues, hcall] at h
  rcases checkTys_cases s!"return values of %{s.frame.func.name}" vals
    (Clif.AbiParam.tys s.frame.func.sig.returns) with ⟨-, hty⟩ | ⟨m, hc⟩
  · exact hty
  · rw [hc] at h; cases h

/-- **Terminator step**, typed, with the ABI return values: a `return` also returns the frame's
`sretRet f` values (`abiTerm`), all held by the VCode return's use values, whose return
registers pin the CLIF values to their classes' return registers (`RetRegsOk vals us`, the
`sret` pointer in x8 after them). `term_stepT` is the CLIF-values-only corollary. -/
theorem term_stepT_abi (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchT f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
        MatchT f ctx R gn bl A MR slots s' vs') ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w' sv, VRetFrom vc sem ⟨b, k, ρ, w⟩ us outs w' ∧
        RetRegsOk vals us ∧ us.length = outs.length ∧
        s.frame.getMany (sretRet f) = .ok sv ∧ AllHold (vals ++ sv) outs ∧
        MR slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c, Clif.step env p s = .trapped c → VTrapFrom vc sem ⟨b, k, ρ, w⟩ c) := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons, htyA⟩ := hm
  simp only at hk hheld hcons hB hmem htyA
  subst hk
  have hjn : j = B.body.length := by
    rw [hbd] at hbody
    have := List.drop_eq_nil_iff.mp hbody
    omega
  subst hjn
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, -, -, htemp, hst0t, hnontry, -, hcode, htne, -, hbargs, hsucc⟩ :=
    H.shape.blk b B L hB hL
  have hBnt : B.term.isTry = false := hterm ▸ hnt
  obtain ⟨htl0, hdata, out, tr, hrunT⟩ := hnontry hBnt
  obtain ⟨ranges, hctx⟩ := H.shape.hctx
  have htlen : TargetsLen B.term L.targets := by
    intro x d tbl hT
    have hs := hsucc
    rw [hT] at hs
    obtain ⟨hlt, -⟩ := hs
    rw [hlt]
    simp [dests]
  have hok := H.terms (L.start + B.body.length) (abiTerm f B.term) L.data L.targets out
    L.tst L.tst' tr (brIdxTyped_abiTerm (H.brIdx B (List.mem_of_getElem? hB)))
    (termIntPos_abiTerm (H.termIntPos (List.mem_of_getElem? hB)))
    (targetsLen_abiTerm htlen) (H.shape.tslot b B L hB hL)
    (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0t) hdata htemp
    (by rw [termCall_abiTerm]; exact hrunT)
  obtain ⟨hargsTA, hnoclobT, -⟩ := H.cert.term b B L hB hL
  have hargsT : ∀ y ∈ termArgs B.term, y ∈ A b B.body.length :=
    fun y hy => hargsTA y (termArgs_abiTerm hy)
  let fr' := restrict s.frame (A b B.body.length)
  let ρ₀ : Nat → CV := fun n => ρ (gn n)
  have hvh : ValsHeld fr' ρ₀ := by
    intro x v hx
    have hxA : x ∈ A b B.body.length := restrict_regs_isSome (by rw [hx]; rfl)
    obtain ⟨v', hv', hh⟩ := hheld x hxA
    rw [restrict_regs_of_mem hxA, hv'] at hx
    cases hx
    exact hh
  have hrun' := hok.run fr' s.mem ρ₀ w
    (by simp [fr', restrict, hfunc, termCtx, H.shape.ctxInvT.func]) hvh (dfgCons_termCtx hcons _ _)
    (by simpa [fr', restrict, hslots] using hmem)
  let D : Nat → Prop := fun n => L.tst.nextVreg ≤ n ∧ n < L.tst'.nextVreg
  have hD : ∀ d, D d → gn d = d := fun d hd => H.shape.temps d (by
    have : L.tst.nextVreg ≤ d := hd.1; omega)
  have hdefs : ∀ m ∈ L.tst'.emitted.toList, ∀ d ∈ vdefs m, D d := hok.defs
  have hAg : Agree gn D ρ₀ ρ := fun _ _ => rfl
  have huses_of : UsesOk L.tst fr' L.tst'.emitted.toList →
      ∀ m ∈ L.tst'.emitted.toList, ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
    intro hU m hm u hu
    rcases hU m hm u hu with h | h
    · by_cases h' : u < L.tst'.nextVreg
      · exact .inl ⟨h, h'⟩
      · right
        rw [H.shape.temps u (by omega)]
        intro hd; exact h' hd.2
    · right; exact hnoclobT u (restrict_regs_isSome h)
  have hren := seqRun_rename (sem := sem) (ρ₀ := ρ₀) (ρ := ρ) (w := w) H.shape.ren
    (H.dsem.rename R gn H.shape.ren) hD hdefs
  obtain ⟨hsegat, hsize⟩ := tseg_atT hcode
  rw [tseg_eq_none hL htl0] at hsegat hsize htne
  have hstep : Clif.step env p s = Clif.stepTerm env p s B.term := by
    rw [Clif.step_term env p s hbody, hterm]
  -- tracked values keep their registers across the terminator's code
  have hkeep : ∀ {k' i ops ρ₁ w₁ outs w₂ ctl ρ₁'},
      seqRun sem L.tst'.emitted.toList ρ₀ w = some (.stop k' i ops ρ₁ w₁ outs w₂ ctl) →
      Agree gn D (vdefUpd ops outs ρ₁) (vdefUpd (ops.map (rnOp gn)) outs ρ₁') →
      ∀ x ∈ A b B.body.length, vdefUpd (ops.map (rnOp gn)) outs ρ₁' (gn x) = ρ (gn x) := by
    intro k' i ops ρ₁ w₁ outs w₂ ctl ρ₁' hsr hA2 x hx
    have hnd : ¬ D x := by
      have h4 : x < st0.nextVreg := H.cert.small _ _ x hx
      intro hd
      have h3 : L.tst.nextVreg ≤ x := hd.1
      exact absurd (Nat.lt_of_lt_of_le h4 hst0t) (Nat.not_lt.mpr h3)
    rw [← hA2 x (.inr (hnoclobT x hx))]
    exact (seqRun_stop_frame (fun m hm hxm => hnd (hdefs m hm x hxm)) hsr).2
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  have hargsR : ∀ y ∈ termArgs B.term, fr'.regs y = s.frame.regs y :=
    fun y hy => restrict_regs_of_mem (hargsT y hy)
  -- branches
  have hnext_br : dests B.term ≠ [] → ∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, posT f ctx R bl b B.body.length, ρ, w⟩) (.run vs') ∧
        MatchT f ctx R gn bl A MR slots s' vs' := by
    intro hne s' hs
    rw [hstep] at hs
    obtain ⟨j', bc, fr2, hbi, hbc, hent, rfl⟩ := stepTerm_branch hne hs
    have hbr : (∀ i, L.tst'.emitted.toList.getLast? = some i → i.targets = L.targets) ∧
        ∀ j, branchIdx fr' B.term = .ok j → UsesOk L.tst fr' L.tst'.emitted.toList ∧
          ∃ k i ops ρ₁ w₁ outs w₂,
            seqRun sem L.tst'.emitted.toList ρ₀ w = some (.stop k i ops ρ₁ w₁ outs w₂ (.goto j)) ∧
            k + 1 = L.tst'.emitted.toList.length ∧ MR fr'.slots s.mem w₂ := by
      cases hT : B.term with
      | jump bc0 => rw [hT] at hrun'; exact hrun'
      | brif c t e => rw [hT] at hrun'; exact hrun'
      | brTable x d tbl => rw [hT] at hrun'; exact hrun'
      | _ => rw [hT] at hne; simp [dests] at hne
    obtain ⟨htg, hgo⟩ := hbr
    have hbi' : branchIdx fr' B.term = .ok j' := by
      rw [← hbi]
      cases hT : B.term with
      | brif c t e =>
        rw [hT] at hargsR
        simp only [branchIdx, Clif.Frame.get, hargsR c (by simp [termArgs])]
      | brTable x d tbl =>
        rw [hT] at hargsR
        simp only [branchIdx, Clif.Frame.get, hargsR x (by simp [termArgs])]
      | _ => rfl
    obtain ⟨hU, k', i, ops, ρ₁, w₁, outs, w₂, hsr, hk1, hmr⟩ := hgo j' hbi'
    obtain ⟨ρ₁', hsr', -, hA2⟩ := (hren (huses_of hU) hAg).2 hsr
    obtain ⟨hstar, -, hi, hops, hsem, hlen, -⟩ := seqRun_stop_star hvb hsegat hsr'
    obtain ⟨hmk, -⟩ := seqRun_stop_mem hsr
    have hlast : L.tst'.emitted.toList.getLast? = some i := by
      rw [List.getLast?_eq_getElem?, ← hk1, Nat.add_sub_cancel]; exact hmk
    have hK : posT f ctx R bl b B.body.length + k' + 1 = vb.insts.size := by
      rw [hsize, List.length_map, ← hk1]; omega
    have hback : vb.insts.back? = some (i.mapRegs R) := by
      rw [Array.back?_eq_getElem?, ← hK, Nat.add_sub_cancel]; exact hi
    obtain ⟨ss, ps, hcfg⟩ := H.cfg
    have hsucc_eq : ∀ jj, succOf vc b jj = L.targets[jj]? := fun jj => by
      rw [succOf_eq H.shape.labels hcfg hvb hback, targets_mapRegs, htg i hlast]
    have hρ₂ := hkeep hsr hA2
    have hbcmem : bc ∈ dests B.term := List.mem_of_getElem? hbc
    have hmr' : MR slots s.mem w₂ := by simpa [fr', restrict, hslots] using hmr
    -- the successor
    split at hsucc
    · rename_i bc0 hT
      rw [hT] at hbargs hbc
      obtain ⟨tl, htl, htgs⟩ := hsucc
      have hj0 : j' = 0 ∧ bc = bc0 := by
        cases j' with
        | zero => simp [dests] at hbc; exact ⟨rfl, hbc.symm⟩
        | succ n => simp [dests] at hbc
      obtain ⟨rfl, rfl⟩ := hj0
      obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match_brT H hB hcall hfunc hslots hheld hcons htyA
        hbcmem htl hent hρ₂ hmr'
      obtain ⟨Lt, hLt⟩ := H.blow hTB
      obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
      simp only [hne0, ite_false] at hpt
      have henv := edgeEnv_eqT (V := CV) hvb hvbt (as := bc.args) (qs := TB.params)
        (gx := fun a => R (vregOf ctx a)) (nx := gn) (gp := fun q => vregOf ctx q.1) (np := (·.1))
        (by rw [hbargs]) (fun a _ => ⟨_, H.shape.ren.vreg _ _⟩) (by rw [hpt]) (fun q _ => ⟨_, rfl⟩)
        (by omega) (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
      refine ⟨_, hstar.trans (Star.single (VStep.step hvb hi hops hsem hlen
        (VNext.goto hK (by rw [hsucc_eq, htgs]; rfl) henv))), hM⟩
    · rename_i fn0 args0 et0 hT
      rw [hT] at hBnt; cases hBnt
    · rename_i callee0 args0 et0 hT
      rw [hT] at hBnt; cases hBnt
    · rename_i hnj _ _
      have hbargs' : vb.branchArgs = #[] := by
        rw [hbargs]; split
        · rename_i bc0 hT; exact absurd hT (hnj bc0)
        · rfl
      obtain ⟨hlt, hall⟩ := hsucc
      have hjlt : j' < L.targets.length := by
        rw [hlt]; exact (List.getElem?_eq_some_iff.mp hbc).1
      obtain ⟨tl, htl, hnil, hedge⟩ := hall j' bc L.targets[j'] hbc (List.getElem?_eq_getElem hjlt)
      obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match_brT H hB hcall hfunc hslots hheld hcons htyA
        hbcmem htl hent hρ₂ hmr'
      obtain ⟨Lt, hLt⟩ := H.blow hTB
      obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
      simp only [hne0, ite_false] at hpt
      by_cases hargs0 : bc.args = []
      · have hp0 : TB.params = [] := by
          rw [hargs0] at hlenA; exact List.eq_nil_of_length_eq_zero hlenA.symm
        have henv := edgeEnv_eq (V := CV) hvb hvbt (xs := []) (ps := [])
          (by rw [hbargs']; rfl) (by rw [hpt, hp0]; rfl) rfl (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
        rw [hargs0, hp0] at hM
        refine ⟨_, hstar.trans (Star.single (VStep.step hvb hi hops hsem hlen
          (VNext.goto hK (by rw [hsucc_eq, List.getElem?_eq_getElem hjlt, hnil hargs0]) henv))), hM⟩
      · obtain ⟨eb, heb, hebi, hebp, hebba⟩ := hedge hargs0
        have henv1 := edgeEnv_eq (V := CV) hvb heb (xs := []) (ps := [])
          (by rw [hbargs']; rfl) (by rw [hebp]; rfl) rfl (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
        have henv2 := edgeEnv_eqT (V := CV) heb hvbt (as := bc.args) (qs := TB.params)
          (gx := fun a => R (vregOf ctx a)) (nx := gn) (gp := fun q => vregOf ctx q.1) (np := (·.1))
          (by rw [hebba]) (fun a _ => ⟨_, H.shape.ren.vreg _ _⟩) (by rw [hpt]) (fun q _ => ⟨_, rfl⟩)
          (by omega)
          (parCopyEnv (vdefUpd (ops.map (rnOp gn)) outs ρ₁') [] [])
        have hpc : parCopyEnv (vdefUpd (ops.map (rnOp gn)) outs ρ₁') [] [] =
            vdefUpd (ops.map (rnOp gn)) outs ρ₁' := rfl
        rw [hpc] at henv2
        have hebback : eb.insts.back? = some (.jump tl) := by rw [hebi]; rfl
        have hstep1 := VStep.step hvb hi hops hsem hlen
          (VNext.goto hK (by rw [hsucc_eq, List.getElem?_eq_getElem hjlt]) henv1)
        have hstep2 : VStep vc sem (.run ⟨L.targets[j'], 0,
            parCopyEnv (vdefUpd (ops.map (rnOp gn)) outs ρ₁') [] [], w₂⟩)
            (.run ⟨tl, 0, parCopyEnv (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
              (TB.params.map (·.1)) (bc.args.map gn), w₂⟩) := by
          rw [hpc]
          refine VStep.step heb (by rw [hebi]; rfl) (i := .jump tl) (ops := #[]) rfl
            (H.dsem.jump tl w₂) rfl (VNext.goto (by rw [hebi]; rfl) ?_ henv2)
          rw [succOf_eq H.shape.labels hcfg heb hebback]; rfl
        exact ⟨_, hstar.trans (.step hstep1 (Star.single hstep2)), hM⟩
  cases hT : B.term with
  | ret xs =>
    rw [hT] at hrun' hstep hargsR hargsTA
    simp only [abiTerm] at hrun' hargsTA
    obtain ⟨hn, htr, hdn⟩ := stepTerm_ret (env := env) (p := p) (s := s) (xs := xs) hcall
    refine ⟨fun s' hs => ?_, fun vals cm hs => ?_, fun c hs => ?_⟩
    · rw [hstep] at hs; exact absurd hs (hn s')
    rotate_left
    · rw [hstep] at hs; exact absurd hs (htr c)
    rw [hstep] at hs
    obtain ⟨hg, hcm⟩ := hdn vals cm hs
    have hg0 : fr'.getMany xs = .ok vals := by
      rw [getMany_congr (fun x hx => hargsR x (by simpa [termArgs] using hx))]; exact hg
    -- the returned `sret` pointer (`abiTerm`) is a tracked value, defined in the frame
    have hyA : ∀ y ∈ sretRet f, y ∈ A b B.body.length :=
      fun y hy => hargsTA y (by simp [termArgs, hy])
    obtain ⟨vs, hvs0⟩ := getMany_append_of (fr := fr') (ys := sretRet f) (xs := []) (vals := [])
      (fun y hy => by
        obtain ⟨v, hv, -⟩ := hheld y (hyA y hy)
        exact ⟨v, by rw [restrict_regs_of_mem (hyA y hy)]; exact hv⟩) rfl
    simp only [List.nil_append] at hvs0
    have hg' := getMany_append hg0 hvs0
    have hvsS : s.frame.getMany (sretRet f) = .ok vs := by
      rw [← hvs0]
      exact (getMany_congr (fun y hy => restrict_regs_of_mem (hyA y hy))).symm
    obtain ⟨hU, k', us, ops, ρ₁, w₁, outs, w₂, hsr, hus, hlen, hall, hmr⟩ := hrun' _ hg'
    obtain ⟨ρ₁', hsr', hA1, -⟩ := (hren (huses_of hU) hAg).2 hsr
    obtain ⟨hstar, -, hi, hops, hsem, -, -⟩ := seqRun_stop_star hvb hsegat hsr'
    obtain ⟨hmk, hopsU⟩ := seqRun_stop_mem hsr
    have hvu : vuses (ops.map (rnOp gn)) ρ₁' = vuses ops ρ₁ := by
      apply vuses_rename hA1
      intro o ho hu
      apply huses_of hU _ (List.mem_of_getElem? hmk) o.vreg
      simp only [vuseNums, hopsU, List.mem_map, List.mem_filter]
      exact ⟨o, ⟨by simpa using ho, hu⟩, rfl⟩
    refine ⟨_, vuses ops ρ₁, w₂, vs, ⟨b, _, ρ₁', w₁, vb, ops.map (rnOp gn), outs, hstar, hvb, hi, hops,
      hvu.symm, by rw [← hvu]; exact hsem⟩, ?_, ?_, hvsS, hall,
      by simpa [fr', restrict, hslots] using hmr, by rw [hcm, hslots],
      by rw [← hfunc]; exact stepTerm_ret_tys hcall hs⟩
    · -- `RetRegsOk vals us`: the classes of the returned values are the driver's
      have hvC : valClassOf (termCtx ctx (L.start + B.body.length) L.data) = valClassOf ctx := by
        funext x; rfl
      have hclT : (xs ++ sretRet f).map
            (valClassOf (termCtx ctx (L.start + B.body.length) L.data)) =
          (vals ++ vs).map (fun v => tyClass v.ty) :=
        getMany_classes hcons.2 hg' (fun x hx => htyA x (hargsTA x (by simp [termArgs, hx])))
      have hcl0 : xs.map (valClassOf (termCtx ctx (L.start + B.body.length) L.data)) =
          vals.map (fun v => tyClass v.ty) :=
        getMany_classes hcons.2 hg0 (fun x hx => htyA x (hargsTA x (by simp [termArgs, hx])))
      rw [hvC] at hclT hcl0
      have hl0 : (xs.map (valClassOf ctx)).length =
          (vals.map (fun v => tyClass v.ty)).length := by rw [hcl0]
      have hclS : (sretRet f).map (valClassOf ctx) = vs.map (fun v => tyClass v.ty) :=
        (List.append_inj (by rw [← List.map_append, ← List.map_append]; exact hclT) hl0).2
      refine ⟨vs.map (fun v => tyClass v.ty), ?_⟩
      have hRaw : List.map (fun x => x.snd)
          (List.map (fun x => match x with | (v, p) => (R v, p)) us) =
          List.map (·.2) us := by
        rw [List.map_map]
        apply List.map_congr_left
        intro q _
        obtain ⟨v, p⟩ := q
        simp
      have hus' : List.map (fun x => x.snd)
          (List.map (fun x => match x with | (v, p) => (R v, p)) us) =
          retRegsT
            ((xs.map (valClassOf ctx) ++ (sretRet f).map (valClassOf ctx)).take xs.length) 0 0 ++
            List.replicate (sretRet f).length (Reg.x 8) := by
        rw [hRaw, hus, hvC,
          show (termCtx ctx (L.start + B.body.length) L.data).func = ctx.func from by
            simp [termCtx], H.shape.ctxInvT.func, ← List.map_append, List.length_append,
          Nat.add_sub_cancel, Nat.add_sub_cancel_left, List.map_append]
      rw [← hcl0, ← hclS, (getMany_spec hg0).1.symm,
        List.take_left' (l₁ := xs.map (valClassOf ctx)) (i := xs.length)
          (by rw [List.length_map]), List.length_append, List.length_map, Nat.add_sub_cancel_left]
      rw [hus', List.take_left' (l₁ := xs.map (valClassOf ctx)) (i := xs.length)
        (by rw [List.length_map]), List.length_map]
    · simp only [List.length_map]; rw [hlen]; exact hall.1
  | trap c =>
    rw [hT] at hrun' hstep
    refine ⟨fun s' hs => ?_, fun vals cm hs => ?_, fun c' hs => ?_⟩
    · rw [hstep] at hs; cases hs
    · rw [hstep] at hs; cases hs
    rw [hstep] at hs
    simp only [Clif.stepTerm, Clif.StepResult.trapped.injEq] at hs
    subst hs
    obtain ⟨hU, k', i, ops, ρ₁, w₁, outs, w₂, hsr, htc⟩ := hrun'
    obtain ⟨ρ₁', hsr', -, -⟩ := (hren (huses_of hU) hAg).2 hsr
    obtain ⟨hstar, -, hi, hops, hsem, -, -⟩ := seqRun_stop_star hvb hsegat hsr'
    exact ⟨b, _, ρ₁', w₁, vb, _, _, outs, w₂, hstar, hvb, hi, hops, hsem,
      by rw [trapCode?_mapRegs]; exact htc⟩
  | returnCall fn args => exact absurd hT (H.noTail B hBmem fn args)
  | tryCall _ _ _ => rw [hT] at hBnt; cases hBnt
  | tryCallIndirect _ _ _ => rw [hT] at hBnt; cases hBnt
  | jump bc =>
    have hne : dests B.term ≠ [] := by rw [hT]; simp [dests]
    refine ⟨hnext_br hne, fun vals cm hs => ?_, fun c hs => ?_⟩
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).1 vals cm)
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).2 c)
  | brif c t e =>
    have hne : dests B.term ≠ [] := by rw [hT]; simp [dests]
    refine ⟨hnext_br hne, fun vals cm hs => ?_, fun c hs => ?_⟩
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).1 vals cm)
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).2 c)
  | brTable x d tbl =>
    have hne : dests B.term ≠ [] := by rw [hT]; simp [dests]
    refine ⟨hnext_br hne, fun vals cm hs => ?_, fun c hs => ?_⟩
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).1 vals cm)
    · rw [hstep] at hs; exact absurd hs ((stepTerm_branch_ne hne).2 c)

/-- **Terminator step**, typed: returns put each returned value in the ABI return register of its
type's class (`RetRegsOk`). -/
theorem term_stepT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchT f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
        MatchT f ctx R gn bl A MR slots s' vs') ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w', VRetFrom vc sem ⟨b, k, ρ, w⟩ us outs w' ∧
        RetRegsOk vals us ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MR slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave ∧
        vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns) ∧
    (∀ c, Clif.step env p s = .trapped c → VTrapFrom vc sem ⟨b, k, ρ, w⟩ c) := by
  obtain ⟨T1, T2, T3⟩ := term_stepT_abi H hm hbody hnt
  refine ⟨T1, fun vals cm hs => ?_, T3⟩
  obtain ⟨us, outs, w', sv, h1, h2, h3, -, h5, h6, h7, h8⟩ := T2 vals cm hs
  exact ⟨us, outs, w', h1, h2, h3, AllHold.prefix_append h5, h6, h7, h8⟩

/-- **`try_call`/`try_call_indirect` step**, typed (the normal return; the edge block passes
value arguments in their classes' vregs, `normArgRegT`). -/
theorem term_step_tryT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : MatchT f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith s.frame.term et)
    (hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ vals cm, Clif.step env p s ≠ .done vals cm) ∧
    ∀ s', Clif.step env p s = .next s' →
      (∀ c, Clif.step env p s' ≠ .trapped c) ∧ (∀ vals cm, Clif.step env p s' ≠ .done vals cm) ∧
      ∀ s'', Clif.step env p s' = .next s'' →
        ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
          MatchT f ctx R gn bl A MR slots s'' vs' := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons, htyA⟩ := hm
  simp only at hk hheld hcons hB hmem htyA
  subst hk
  have hjn : j = B.body.length := by
    rw [hbd] at hbody
    have := List.drop_eq_nil_iff.mp hbody
    omega
  subst hjn
  have hBT : IsTryWith B.term et := hterm ▸ hT
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  have hstep : Clif.step env p s = Clif.stepTerm env p s B.term := by
    rw [Clif.step_term env p s hbody, hterm]
  -- the lowering of the terminator
  obtain ⟨L, hL⟩ := H.blow hB
  obtain ⟨vb, hvb, -, -, -, hst0t, -, htry, hcode, -, -, hbargs, hsucc⟩ :=
    H.shape.blk b B L hB hL
  obtain ⟨T, hTl, hdata, hexn, hregs, hinfo, out, tr, hrun⟩ := htry et hBT
  have hvbL : ValsBelow ctx L.tst := fun x r h =>
    Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0t
  obtain ⟨hargsTA, hnoclobT, -⟩ := H.cert.term b B L hB hL
  have hnr : abiTerm f B.term = B.term := by
    rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> rfl
  have htA : ∀ y ∈ termArgs B.term, y ∈ A b B.body.length := fun y hy =>
    hargsTA y (by rw [hnr]; exact hy)
  -- the call `ci` of the terminator: its CLIF step and its lowering
  obtain ⟨ci, hciA, hnd, hnx, hok⟩ : ∃ ci : Clif.Inst,
      (∀ y ∈ instArgs ci, y ∈ termArgs B.term) ∧
      (∀ vals cm, Clif.stepTerm env p s B.term ≠ .done vals cm) ∧
      (∀ s', Clif.stepTerm env p s B.term = .next s' → ∃ bc rvals cm' regs',
        Clif.tryNormal et s.frame.func.freshValue = .ok bc ∧
        instOutcome env p s.frame s.mem ci = .ok (rvals, cm') ∧
        s.frame.regs.setMany ((List.range T.sig.returns.length).map
          (s.frame.func.freshValue + ·)) rvals = some regs' ∧
        s' = tryNext s regs' bc cm') ∧
      LowerTryOk sem MR env p (tryCtx ctx (L.start + B.body.length) L.data T.regs) ci T.info
        { T.st1 with emitted := #[] } L.tst' L.tst'.emitted.toList := by
    rcases hBT with ⟨fn, args, hBT⟩ | ⟨callee, args, hBT⟩
    · have hext : ∀ e, s.frame.func.extern? fn = some e → p.func? e.name = none :=
        fun e he => H.tryExt B hBmem fn args et hBT e (hfunc ▸ he)
      have hdata' : tryCallData f (.tryCall fn args et) = .ok L.data := hBT ▸ hdata
      obtain ⟨sig0, items0, ext0, hexn0, hx0, hsig0⟩ := tryCallData_spec hdata'
      rw [hexn] at hexn0
      simp only [Except.ok.injEq, Prod.mk.injEq] at hexn0
      obtain ⟨rfl, rfl⟩ := hexn0
      obtain ⟨hnd, hnx⟩ := stepTry_spec (env := env) (p := p) (args := args) (et := et) hext
      rw [hBT]
      refine ⟨.call fn args, fun y hy => by
          simp only [instArgs] at hy; simp [termArgs, hy], hnd,
        fun s' hs => ?_, H.tries.choose_spec.1 (L.start + B.body.length) fn args et L.data
          T.sig T.items L.targets T.info T.regs L.tst T.st1 out L.tst' tr
          (H.tries.choose_spec.2 B hBmem fn args et hBT) hdata' (hBT ▸ H.termIntPos hBmem) hexn
          (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun⟩
      obtain ⟨ext, bc, rvals, cm', regs', hx, htn, hO, hset, rfl⟩ := hnx s' hs
      rw [hfunc, hx0] at hx
      cases hx
      exact ⟨bc, rvals, cm', regs', htn, hO, by rw [← hsig0]; exact hset, rfl⟩
    · have hdata' : tryCallData f (.tryCallIndirect callee args et) = .ok L.data := hBT ▸ hdata
      have hsd := exnTableOpnd_sig hexn
      obtain ⟨hsin, h8⟩ := H.tryIndSig B hBmem callee args et T.sig hBT hsd
      obtain ⟨hnd, hnx⟩ := stepTryInd_spec (env := env) (p := p) (args := args) (et := et)
        (hind callee args (hterm.trans hBT))
      rw [hBT]
      refine ⟨.callIndirect et.sig callee args,
        fun y hy => by
          simp only [instArgs] at hy
          simp only [termArgs, List.cons_append]
          exact List.mem_cons.mpr ((List.mem_cons.mp hy).imp id fun h => List.mem_append_left _ h),
        hnd, fun s' hs => ?_,
        H.tryInd (L.start + B.body.length) callee args et L.data T.sig T.items L.targets
          T.info T.regs L.tst T.st1 out L.tst' tr hdata' (hBT ▸ H.termIntPos hBmem) hexn hsin h8
          (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun⟩
      obtain ⟨declared, bc, rvals, cm', regs', hd, htn, hO, hset, rfl⟩ := hnx s' hs
      rw [hfunc, hsd] at hd
      cases hd
      exact ⟨bc, rvals, cm', regs', htn, hO, hset, rfl⟩
  refine ⟨fun vals cm h => hnd vals cm (hstep.symm.trans h), fun s' hs => ?_⟩
  rw [hstep] at hs
  obtain ⟨bc, rvals, cm', regs', htn, hO, hset, rfl⟩ := hnx s' hs
  have hbc := tryNormal_ok htn
  rw [hfunc] at hbc hset
  have hstep' : Clif.step env p (tryNext s regs' bc cm') =
      Clif.stepTerm env p (tryNext s regs' bc cm') (.jump bc) := Clif.step_term env p _ rfl
  have hjne : dests (.jump bc) ≠ [] := by simp [dests]
  refine ⟨fun c h => (stepTerm_branch_ne hjne).2 c (hstep'.symm.trans h),
    fun vals cm h => (stepTerm_branch_ne hjne).1 vals cm (hstep'.symm.trans h), fun s'' hs' => ?_⟩
  rw [hstep'] at hs'
  obtain ⟨j', bc', fr2, -, hbc', hent, rfl⟩ := stepTerm_branch hjne hs'
  have hbcbc : bc = bc' := by
    cases j' with
    | zero => simp [dests] at hbc'; exact hbc'
    | succ n => simp [dests] at hbc'
  subst hbcbc
  have hsucc2 : L.targets.length = et.dests.length ∧
      ∃ tl tlab T eb, blockIdx? f et.normal.block = some tl ∧ L.targets.getLast? = some tlab ∧
        L.tl = some T ∧ vc.blocks[tlab]? = some eb ∧ eb.insts = #[.jump tl] ∧ eb.params = #[] ∧
        eb.branchArgs = (et.normal.args.map (normArgRegT ctx R T.regs.1)).toArray ∧
        ∀ a ∈ et.normal.args, match a with
          | .val _ => True
          | .ret i => i < T.sig.returns.length
          | .exn _ => False := by
    rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] at hsucc <;> exact hsucc
  obtain ⟨-, tl, tlab, T', eb, htl, hlast, hTl', heb, hebi, hebp, hebba, hargsOk⟩ := hsucc2
  rw [hTl] at hTl'
  cases hTl'
  have hbargs' : vb.branchArgs = #[] := by
    rw [hbargs]; rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  obtain ⟨-, hregsEq, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc hexn) hregs
  obtain ⟨pre, ci', hms, hpre, hcd⟩ := hok.shape
  have hmono : T.st1.nextVreg ≤ L.tst'.nextVreg := hok.mono
  have hmax1 : (sigRets T.sig).length ≤ max (sigRets T.sig).length 2 := Nat.le_max_left _ _
  have hmax2 : 2 ≤ max (sigRets T.sig).length 2 := Nat.le_max_right _ _
  have hfix : tryFix T.info L.tst'.emitted.toList = pre ++ [.tryCall ci' T.info] := by
    rw [hms, tryFix_append]
  have hargsA : ∀ y ∈ instArgs ci, y ∈ A b B.body.length := fun y hy => htA y (hciA y hy)
  -- the call's results are not tracked values
  have hnotres : ∀ x ∈ A b B.body.length,
      x ∉ (List.range T.sig.returns.length).map (f.freshValue + ·) := by
    intro x hx hm
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hm
    have h1 : f.freshValue + a < st0.nextVreg := H.cert.small _ _ _ hx
    exact absurd (Nat.lt_of_lt_of_le h1 H.shape.fresh) (Nat.not_lt.mpr (Nat.le_add_right _ _))
  let fr' := restrict s.frame (A b B.body.length)
  let ρ₀ : Nat → CV := fun n => ρ (gn n)
  have hvh : ValsHeld fr' ρ₀ := by
    intro x v hx
    have hxA : x ∈ A b B.body.length := restrict_regs_isSome (by rw [hx]; rfl)
    obtain ⟨v', hv', hh⟩ := hheld x hxA
    rw [restrict_regs_of_mem hxA, hv'] at hx
    cases hx
    exact hh
  have hrun' := hok.run fr' s.mem ρ₀ w
    (by simp [fr', restrict, hfunc, tryCtx, termCtx, H.shape.ctxInvT.func]) hvh
    (dfgCons_termCtx hcons _ _) (by simpa [fr', restrict, hslots] using hmem)
  have hio : instOutcome env p fr' s.mem ci = instOutcome env p s.frame s.mem ci :=
    instOutcome_congr (fr := s.frame) (fr' := fr') rfl rfl env p s.mem _
      fun x hx => restrict_regs_of_mem (hargsA x hx)
  rw [hio, hO] at hrun'
  obtain ⟨hU, k', i, ops, ρ₁, w₁, outs, w₂, hsr, hk1, hrets, hmr⟩ := hrun'
  rw [hfix] at hsr
  let D : Nat → Prop := fun n => L.tst.nextVreg ≤ n ∧ n < L.tst'.nextVreg
  have hD : ∀ d, D d → gn d = d := fun d hd => H.shape.temps d (by
    have : L.tst.nextVreg ≤ d := hd.1; omega)
  have hdefs : ∀ m ∈ pre ++ [.tryCall ci' T.info], ∀ d ∈ vdefs m, D d := by
    intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨h1, h2⟩ := hpre m hm d hd
      have h1' : T.st1.nextVreg ≤ d := h1
      exact ⟨by omega, h2⟩
    · rw [List.mem_singleton] at hm
      subst hm
      rw [vdefs_tryCall] at hd
      have hmem' : Reg.vreg d .int ∈ T.regs.1 ++ T.regs.2 := hcd d hd
      rw [hregsEq] at hmem'
      simp only [List.mem_append, List.mem_map, List.mem_range, Reg.vreg.injEq, and_true,
        List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      show L.tst.nextVreg ≤ d ∧ d < L.tst'.nextVreg
      rcases hmem' with ⟨a, ha, rfl⟩ | rfl | rfl <;> constructor <;> omega
  have huses : UsesOk { T.st1 with emitted := #[] } fr' L.tst'.emitted.toList →
      ∀ m ∈ pre ++ [.tryCall ci' T.info], ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
    intro hU m hm u hu
    have hU' : ∀ m ∈ L.tst'.emitted.toList, ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
      intro m hm u hu
      rcases hU m hm u hu with h | h
      · have h' : T.st1.nextVreg ≤ u := h
        by_cases h'' : u < L.tst'.nextVreg
        · exact .inl ⟨by omega, h''⟩
        · right
          rw [H.shape.temps u (by omega)]
          intro hd; exact h'' hd.2
      · right; exact hnoclobT u (restrict_regs_isSome h)
    rcases List.mem_append.mp hm with hm | hm
    · exact hU' m (by rw [hms]; exact List.mem_append_left _ hm) u hu
    · rw [List.mem_singleton] at hm
      subst hm
      rw [vuseNums_tryCall] at hu
      exact hU' _ (by rw [hms]; simp) u hu
  have hAg : Agree gn D ρ₀ ρ := fun _ _ => rfl
  have hren := seqRun_rename (sem := sem) (ρ₀ := ρ₀) (ρ := ρ) (w := w) H.shape.ren
    (H.dsem.rename R gn H.shape.ren) hD hdefs
  obtain ⟨ρ₁', hsr', -, hA2⟩ := (hren (huses hU) hAg).2 hsr
  obtain ⟨hsegat, hsize⟩ := tseg_atT hcode
  have htseg : tseg R bl b = (pre ++ [MInst.tryCall ci' T.info]).map (·.mapRegs R) := by
    rw [tseg_eq hL, hTl]
    show (tryFix T.info _).map _ = _
    rw [hfix]
  rw [htseg] at hsegat hsize
  obtain ⟨hstar, -, hi, hops, hsem, hlen, -⟩ := seqRun_stop_star hvb hsegat hsr'
  obtain ⟨hmk, -⟩ := seqRun_stop_mem hsr
  have hk' : k' = pre.length := by
    rw [hms] at hk1; simp only [List.length_append, List.length_singleton] at hk1; omega
  subst hk'
  have hiT : i = .tryCall ci' T.info := by
    rw [List.getElem?_append_right (Nat.le_refl _)] at hmk
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hmk
    exact hmk.symm
  subst hiT
  have hK : posT f ctx R bl b B.body.length + pre.length + 1 = vb.insts.size := by
    rw [hsize]; simp only [List.length_map, List.length_append, List.length_singleton]; omega
  have hback : vb.insts.back? = some ((MInst.tryCall ci' T.info).mapRegs R) := by
    rw [Array.back?_eq_getElem?, ← hK, Nat.add_sub_cancel]; exact hi
  obtain ⟨ss, ps, hcfg⟩ := H.cfg
  obtain ⟨hcont, -⟩ := tryInfoOf_spec hinfo
  have hsucc1 : succOf vc b T.info.handlers.length = some tlab := by
    rw [succOf_eq H.shape.labels hcfg hvb hback, targets_mapRegs]
    simp only [MInst.targets, hcont]
    rw [List.getElem?_append_right (by simp), List.length_map, Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.some.injEq]
    rw [List.getLastD_eq_getLast?, hlast]; rfl
  -- tracked values keep their registers across the terminator's code
  let ρ₂ := vdefUpd (ops.map (rnOp gn)) outs ρ₁'
  have hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x) := by
    intro x hx
    have hnd : ¬ D x := by
      have h4 : x < st0.nextVreg := H.cert.small _ _ x hx
      intro hd
      have h3 : L.tst.nextVreg ≤ x := hd.1
      exact absurd (Nat.lt_of_lt_of_le h4 hst0t) (Nat.not_lt.mpr h3)
    show vdefUpd (ops.map (rnOp gn)) outs ρ₁' (gn x) = ρ (gn x)
    rw [← hA2 x (.inr (hnoclobT x hx))]
    exact (seqRun_stop_frame (fun m hm hxm => hnd (hdefs m hm x hxm)) hsr).2
  have henv1 := edgeEnv_eq (V := CV) hvb heb (xs := []) (ps := []) (by rw [hbargs']; rfl)
    (by rw [hebp]; rfl) rfl ρ₂
  have hstep1 := VStep.step hvb hi hops hsem hlen (VNext.goto hK hsucc1 henv1)
  -- the successor
  let xs := et.normal.args.map (tryArgNum gn L.tst.nextVreg)
  have hbcb : bc.block ∈ edgeIds B.term := by
    rw [hbc]; rcases hBT with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> simp [edgeIds]
  have htl' : blockIdx? f bc.block = some tl := by rw [hbc]; exact htl
  have hheld' : Held gn (A b B.body.length) ρ (tryNext s regs' bc cm').frame := by
    intro x hx
    obtain ⟨v, hv, hh⟩ := hheld x hx
    refine ⟨v, ?_, hh⟩
    show regs' x = some v
    rw [setMany_other hset (hnotres x hx), hv]
  have hcons' : DFGCons ctx (restrict (tryNext s regs' bc cm').frame (A b B.body.length)) := by
    refine dfgCons_congr (fr := restrict s.frame (A b B.body.length)) rfl rfl
      (funext fun x => ?_) hcons
    by_cases hx : x ∈ A b B.body.length
    · simp only [restrict, tryNext, hx, ite_true]
      exact setMany_other hset (hnotres x hx)
    · simp only [restrict, tryNext, hx, ite_false]
  have hxl : xs.length = bc.args.length := by rw [hbc]; simp [xs]
  have hlr := setMany_length hset
  simp only [List.length_map, List.length_range] at hlr
  have hxv : ∀ (m : Nat) a v x, bc.args[m]? = some a → (tryNext s regs' bc cm').frame.regs a = some v →
      xs[m]? = some x → VHolds v (ρ₂ x) := by
    intro m a v x ha hv hx
    rw [hbc] at ha
    simp only [List.getElem?_map, xs] at ha hx
    cases hta : et.normal.args[m]? with
    | none => rw [hta] at ha; cases ha
    | some ta =>
      rw [hta] at ha hx
      simp only [Option.map_some, Option.some.injEq] at ha hx
      subst ha hx
      have htam := List.mem_of_getElem? hta
      have hv' : regs' _ = some v := hv
      cases ta with
      | val v0 =>
        have hv0A : v0 ∈ A b B.body.length := htA v0 (etVals_termArgs hBT v0 (by
          simp only [Clif.ExnTable.vals, Clif.TryDest.vals, List.mem_append, List.mem_filterMap]
          exact .inl ⟨.val v0, htam, rfl⟩))
        show VHolds v (ρ₂ (gn v0))
        rw [hρ₂ v0 hv0A]
        simp only [tryArgVal] at hv'
        rw [setMany_other hset (hnotres v0 hv0A)] at hv'
        obtain ⟨v', hv'', hh⟩ := hheld v0 hv0A
        rw [hv'] at hv''; cases hv''
        exact hh
      | ret ii =>
        have hii : ii < T.sig.returns.length := hargsOk _ htam
        have hiN : ii < T.sig.returns.length := hii
        have hvi : regs' (f.freshValue + ii) = some rvals[ii] :=
          setMany_nodup hset (List.Pairwise.map _ (fun a b h e => h (Nat.add_left_cancel e)) List.nodup_range) ii _ _
            (by simp [List.getElem?_map, hii]) (List.getElem?_eq_getElem (by omega))
        simp only [tryArgVal] at hv'
        rw [hvi] at hv'
        cases hv'
        have hr : (tryCtx ctx (L.start + B.body.length) L.data T.regs).tryRegs.1[ii]? =
            some (.vreg (L.tst.nextVreg + ii) .int) := by
          show T.regs.1[ii]? = _
          rw [hregsEq]; simp [hiN]
        obtain ⟨n, hn, hvh⟩ := hrets ii _ _ hr (List.getElem?_eq_getElem (by omega))
        cases hn
        have hDi : D (L.tst.nextVreg + ii) := ⟨by omega, by omega⟩
        show VHolds rvals[ii] (ρ₂ (L.tst.nextVreg + ii))
        rw [show ρ₂ (L.tst.nextVreg + ii) = ρ₂ (gn (L.tst.nextVreg + ii)) by rw [hD _ hDi]]
        show VHolds rvals[ii] (vdefUpd (ops.map (rnOp gn)) outs ρ₁' (gn (L.tst.nextVreg + ii)))
        rw [← hA2 _ (.inl hDi)]
        exact hvh
      | exn _ => exact absurd (hargsOk _ htam) id
  have hmr' : MR slots cm' w₂ := by simpa [fr', restrict, hslots] using hmr
  obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_matchT H hB (s := tryNext s regs' bc cm') hcall hfunc
    hslots hheld' hcons' htyA hbcb htl' hent hρ₂ hxl hxv hmr'
  obtain ⟨Lt, hLt⟩ := H.blow hTB
  obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
  simp only [hne0, ite_false] at hpt
  have hgx : ∀ a ∈ et.normal.args,
      ∃ c, normArgRegT ctx R T.regs.1 a = .vreg (tryArgNum gn L.tst.nextVreg a) c := by
    intro a ha
    cases a with
    | val v => exact ⟨_, H.shape.ren.vreg _ _⟩
    | ret ii =>
      have hii : ii < T.sig.returns.length := hargsOk _ ha
      have hiN : ii < T.sig.returns.length := hii
      have hg : gn (L.tst.nextVreg + ii) = L.tst.nextVreg + ii := H.shape.temps _ (by omega)
      exact ⟨.int, by simp [normArgRegT, tryArgNum, hregsEq, hiN, H.shape.ren.vreg, hg]⟩
    | exn _ => exact absurd (hargsOk _ ha) id
  have henv2 := edgeEnv_eqT (V := CV) heb hvbt (as := et.normal.args) (qs := TB.params)
    (gx := normArgRegT ctx R T.regs.1) (nx := tryArgNum gn L.tst.nextVreg)
    (gp := fun q => vregOf ctx q.1) (np := (·.1)) (by rw [hebba]) hgx (by rw [hpt])
    (fun q _ => ⟨_, rfl⟩) (by have h1 := hxl; simp only [xs, List.length_map] at h1; omega)
    (parCopyEnv ρ₂ [] [])
  have hpc : parCopyEnv ρ₂ [] [] = ρ₂ := rfl
  rw [hpc] at henv2
  have hebback : eb.insts.back? = some (.jump tl) := by rw [hebi]; rfl
  have hstep2 : VStep vc sem (.run ⟨tlab, 0, parCopyEnv ρ₂ [] [], w₂⟩)
      (.run ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) xs, w₂⟩) := by
    rw [hpc]
    refine VStep.step heb (by rw [hebi]; rfl) (i := .jump tl) (ops := #[]) rfl
      (H.dsem.jump tl w₂) rfl (VNext.goto (by rw [hebi]; rfl) ?_ henv2)
    rw [succOf_eq H.shape.labels hcfg heb hebback]; rfl
  exact ⟨_, hstar.trans (.step hstep1 (Star.single hstep2)), hM⟩

end

/-! ## The typed entry -/

/-- `(vreg n, p)` pairs of an `Args`, of classes `c`. -/
def argPairsT (c : Nat → RegClass) (ns : List (Nat × Reg)) : List (Reg × Reg) :=
  ns.map fun q => (Reg.vreg q.1 (c q.1), q.2)

/-- The operands of `Args (argPairsT c ns)`: fixed late defs. -/
def argOpsT (c : Nat → RegClass) (ns : List (Nat × Reg)) : List Operand :=
  ns.map fun q => (⟨q.1, c q.1, .def, .late, .fixed q.2⟩ : Operand)

theorem mapM_fixedDefT (c : Nat → RegClass) (ns : List (Nat × Reg)) : ∀ (s : Array Operand),
    ((argPairsT c ns).mapM
      (fun (x : Reg × Reg) => do let r ← collectOp (OpSpec.fixedDef x.2) x.1; pure (r, x.2))).run s =
      .ok (argPairsT c ns, s ++ (argOpsT c ns).toArray) := by
  induction ns with
  | nil => intro s; simp [argPairsT, argOpsT] <;> rfl
  | cons q ns ih =>
    intro s
    simp only [argPairsT, argOpsT, List.map_cons, List.mapM_cons, StateT.run_bind] at ih ⊢
    have h1 : (collectOp (OpSpec.fixedDef q.2) (Reg.vreg q.1 (c q.1))).run s =
        .ok (Reg.vreg q.1 (c q.1), s.push ⟨q.1, c q.1, .def, .late, .fixed q.2⟩) := rfl
    rw [h1, except_ok_bind, StateT.run_pure, except_pure, except_ok_bind, ih, except_ok_bind,
      StateT.run_pure, except_pure]
    simp

theorem operands_argsT (c : Nat → RegClass) (ns : List (Nat × Reg)) :
    (MInst.args (argPairsT c ns)).operands = .ok (argOpsT c ns).toArray := by
  rw [operands_eq]
  simp only [MInst.visitOperands, StateT.run_bind, mapM_fixedDefT]
  simp [bind, Except.bind, StateT.run, pure, StateT.pure, Except.pure]

theorem vdefUpd_argOpsT {c : Nat → RegClass} {ns : List (Nat × Reg)} {outs : List CV}
    {ρ : Nat → CV} (hnd : (ns.map (·.1)).Nodup) (hl : outs.length = ns.length) (m : Nat)
    {q : Nat × Reg} {x : CV} (hq : ns[m]? = some q) (hx : outs[m]? = some x) :
    vdefUpd (argOpsT c ns).toArray outs ρ q.1 = x := by
  have hdef : (argOpsT c ns).filter Operand.isDef = argOpsT c ns := by
    rw [List.filter_eq_self]
    intro o ho
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
    rw [← hq']; rfl
  have hearly : ((argOpsT c ns).zip outs).filter (·.1.isEarly) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp (List.of_mem_zip hp).1
    rw [← hq']; simp [Operand.isEarly]
  have hlate : ((argOpsT c ns).zip outs).filter (·.1.isLate) = (argOpsT c ns).zip outs := by
    rw [List.filter_eq_self]
    intro p hp
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp (List.of_mem_zip hp).1
    rw [← hq']; rfl
  simp only [vdefUpd, List.toList_toArray, hdef, hearly, hlate]
  have hmem : ((argOpsT c ns).zip outs)[m]? = some (⟨q.1, c q.1, .def, .late, .fixed q.2⟩, x) := by
    simp [argOpsT, List.getElem?_zip_eq_some, hq, hx]
  have := writeV_nodup (ρ := writeV ρ []) (dv := (argOpsT c ns).zip outs) ?_ m _ x hmem
  · simpa using this
  · have : ((argOpsT c ns).zip outs).map (·.1.vreg) = ns.map (·.1) := by
      rw [show (fun x : Operand × CV => x.fst.vreg) = Operand.vreg ∘ Prod.fst from rfl,
        ← List.map_map, List.map_fst_zip (by simp [argOpsT]; omega)]
      simp [argOpsT]
    rw [this]; exact hnd

/-- The value an entry load of class `cls` leaves (`stackArgLoad`): an integer `ldr` of `b`
bytes, extended into an X register, an `ldr s`/`ldr d` of `b` bytes into the low lanes
of a V register. -/
def stackVal (cls : RegClass) (b : Nat) (a : BitVec 64) (w : Arm.ArmState) : CV :=
  match cls with
  | .int => ofX (loadVal (loadOpOfBytes b) a w)
  | .float => (Arm.read_mem_bytes b a w).setWidth 128

theorem stackVal_congr {F : BitVec 64 → Prop} {s t : Arm.ArmState} (cls : RegClass) {b : Nat}
    {a : BitVec 64} (h : ∀ x, ¬ F x → s.mem x = t.mem x) (hav : Avoids F b a)
    (hb : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) : stackVal cls b a s = stackVal cls b a t := by
  cases cls with
  | int =>
    simp only [stackVal]
    rw [loadVal_congr (F := F) _ h (by rw [(loadOpOfBytes_facts hb).1]; exact hav)]
  | float =>
    simp only [stackVal]
    rw [read_mem_bytes_congr _ a (fun k hk => h _ (hav k hk))]

/-- A float-classed type is 4 or 8 bytes wide. -/
theorem bytes_of_float {t : Clif.Ty} (h : tyClass t = .float) : t.bytes = 4 ∨ t.bytes = 8 := by
  cases t <;> simp_all [tyClass, Clif.Ty.bytes, Clif.Ty.width]

/-- One float entry load: the parameter's vreg gets the loaded value. -/
theorem seqRun_fpuLoad_cons {sem : Sem} {sz : ScalarSize} {x : Nat} {k : Int} {fl : Clif.MemFlags}
    {ρ : Nat → CV} {w w1 : Arm.ArmState} {o : CV}
    (h : sem (.fpuLoad sz (.vreg x .float) (.fpOffset k) fl) [] w = some ([o], w1, .next))
    (ms : List MInst) :
    seqRun sem (.fpuLoad sz (.vreg x .float) (.fpOffset k) fl :: ms) ρ w =
      (seqRun sem ms (upd ρ x o) w1).map SeqEnd.succ := by
  have hops : (MInst.fpuLoad sz (.vreg x .float) (.fpOffset k) fl).operands =
      .ok #[⟨x, .float, .def, .late, .reg⟩] := rfl
  have hv : vuses #[(⟨x, .float, .def, .late, .reg⟩ : Operand)] ρ = [] := rfl
  simp only [seqRun, hops, hv, h]
  simp [Operand.isDef, Operand.isEarly, Operand.isLate, vdefUpd, writeV]

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- **The typed entry loads** of the stack-passed parameters: each reads its parameter from the
caller's outgoing area (an integer `ldr` under `MemRefines`, an `ldr s`/`ldr d` under
`MemRefinesFP`), the world changes only outside the memory relation's view. -/
theorem entryLoads_runT {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hFP : MemRefinesFP (fun _ => True) F sb sem)
    (hMR : MRStable F MR) :
    ∀ (E : List (((Nat × Clif.Ty) × ArgLoc) × Nat)) (ρ : Nat → CV) (sl : List (Clif.SlotId × Nat))
      (cm : Clif.Mem) (w : Arm.ArmState),
      (∀ q ∈ E, R (vregOf ctx q.1.1.1) = vregOf ctx q.1.1.1) →
      (E.map (·.1.1.1)).Nodup →
      (∀ q ∈ E, ∀ off, q.1.2 = .stack off → (q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8) ∧
        (valClassOf ctx q.1.1.1 = .float → q.2 = 4 ∨ q.2 = 8) ∧
        Avoids F q.2 (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)))) →
      MR sl cm w →
      ∃ ρ' w', seqRun sem (E.filterMap (entryLoadOfT ctx R)) ρ w = some (.fall ρ' w') ∧
        MR sl cm w' ∧
        (∀ y, y ∉ E.map (·.1.1.1) → ρ' y = ρ y) ∧
        (∀ q ∈ E, ∀ p, q.1.2 = .reg p → ρ' q.1.1.1 = ρ q.1.1.1) ∧
        (∀ q ∈ E, ∀ off, q.1.2 = .stack off →
          ρ' q.1.1.1 = stackVal (valClassOf ctx q.1.1.1) q.2
            (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w) ∧
        SameWorld F w' w
  | [], ρ, _, _, w, _, _, _, hmr => ⟨ρ, w, rfl, hmr, fun _ _ => rfl, by simp, by simp,
      SameWorld.refl F w⟩
  | q :: E, ρ, sl, cm, w, hR, hnd, hst, hmr => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨⟨⟨x, ty⟩, loc⟩, b⟩ := q
    simp only at hnd
    have hnx : ∀ q ∈ E, q.1.1.1 ≠ x := fun q hq e => hnd.1 (List.mem_map.mpr ⟨q, hq, e⟩)
    cases loc with
    | reg p =>
      obtain ⟨ρ', w', hrun, hmr', hfr, hreg, hstk, hsw'⟩ := entryLoads_runT hMem hFP hMR E ρ sl cm w
        (fun q hq => hR q (List.mem_cons_of_mem _ hq)) hnd.2
        (fun q hq => hst q (List.mem_cons_of_mem _ hq)) hmr
      refine ⟨ρ', w', by exact hrun, hmr', fun y hy => hfr y (fun h => hy
        (List.mem_cons_of_mem _ h)), fun q hq p' hp => ?_, fun q hq off ho => ?_, hsw'⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact hfr x hnd.1
        · exact hreg q hq p' hp
      · rcases List.mem_cons.mp hq with rfl | hq
        · cases ho
        · exact hstk q hq off ho
    | stack off =>
      obtain ⟨hb, hbf, hav⟩ := hst (((x, ty), ArgLoc.stack off), b) (List.mem_cons_self ..) off rfl
      have hRx : R (vregOf ctx x) = vregOf ctx x := hR _ (List.mem_cons_self ..)
      -- the load of this parameter: its world and value
      obtain ⟨o, w1, hrun1, hsw, hov⟩ : ∃ o w1, (∀ ms ρ0, seqRun sem
          (stackArgLoad (vregOf ctx x) b (.fpOffset (16 + (off : Int))) :: ms) ρ0 w =
            (seqRun sem ms (upd ρ0 x o) w1).map SeqEnd.succ) ∧ SameWorld F w1 w ∧
          o = stackVal (valClassOf ctx x) b
            (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w := by
        cases hc : valClassOf ctx x with
        | int =>
          obtain ⟨hob, hop, -⟩ := loadOpOfBytes_facts hb
          have ha : amodeAddr sb (.fpOffset (16 + (off : Int))) (loadOpOfBytes b).bytes [] w =
              some (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) := rfl
          obtain ⟨w1, hw1, hsw⟩ := hMem.1 (loadOpOfBytes b) x (.fpOffset (16 + (off : Int)))
            trustedFlags [] w _ hop ha (by rw [hob]; exact hav)
          refine ⟨_, w1, fun ms ρ0 => ?_, hsw, rfl⟩
          simp only [vregOf, hc, stackArgLoad, Reg.homeCls]
          exact seqRun_load_cons hw1 ms
        | float =>
          have hb48 := hbf hc
          let sz : ScalarSize := if b == 4 then .size32 else .size64
          have hsz : sz = .size32 ∨ sz = .size64 := by
            simp only [sz]; split <;> simp
          have hszb : sz.bytes = b := by
            simp only [sz]; rcases hb48 with rfl | rfl <;> rfl
          have ha : amodeAddr sb (.fpOffset (16 + (off : Int))) sz.bytes [] w =
              some (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) := rfl
          obtain ⟨w1, hw1, hsw⟩ := hFP.1 sz x (.fpOffset (16 + (off : Int))) trustedFlags [] w _
            hsz ha (by rw [hszb]; exact hav) (fun _ _ => trivial)
          refine ⟨(Arm.read_mem_bytes sz.bytes
            (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w).setWidth 128, w1,
            fun ms ρ0 => ?_, hsw, by rw [hszb]; rfl⟩
          simp only [vregOf, hc, stackArgLoad, Reg.homeCls]
          exact seqRun_fpuLoad_cons hw1 ms
      have hmr1 : MR sl cm w1 := hMR _ _ _ _ ⟨fun f hf _ => hsw.1 f hf, hsw.2.1, hsw.2.2⟩ hmr
      have h29 : Arm.r (.GPR 29#5) w1 = Arm.r (.GPR 29#5) w :=
        hsw.1 (.GPR 29#5) (by simp [Masked])
      obtain ⟨ρ', w', hrun, hmr', hfr, hreg, hstk, hsw'⟩ := entryLoads_runT hMem hFP hMR E
        (upd ρ x o) sl cm w1 (fun q hq => hR q (List.mem_cons_of_mem _ hq)) hnd.2
        (fun q hq o ho => by rw [h29]; exact hst q (List.mem_cons_of_mem _ hq) o ho) hmr1
      refine ⟨ρ', w', ?_, hmr', fun y hy => ?_, fun q hq p hp => ?_, fun q hq o' ho => ?_,
        ⟨fun f hf => (hsw'.1 f hf).trans (hsw.1 f hf), fun a ha => (hsw'.2.1 a ha).trans
          (hsw.2.1 a ha), hsw'.2.2.trans hsw.2.2⟩⟩
      · simp only [List.filterMap_cons, entryLoadOfT, hRx]
        rw [hrun1, hrun]; rfl
      · have hyx : y ≠ x := fun e => hy (by rw [e]; exact List.mem_cons_self ..)
        rw [hfr y (fun h => hy (List.mem_cons_of_mem _ h))]
        simp [upd, hyx]
      · rcases List.mem_cons.mp hq with rfl | hq
        · cases hp
        · rw [hreg q hq p hp]
          simp [upd, hnx q hq]
      · rcases List.mem_cons.mp hq with rfl | hq
        · simp only [ArgLoc.stack.injEq] at ho
          subst ho
          rw [hfr x hnd.1, hov]
          simp [upd]
        · rw [hstk q hq o' ho, h29]
          obtain ⟨hb', -, hav'⟩ := hst q (List.mem_cons_of_mem _ hq) o' ho
          exact stackVal_congr _ (fun a ha => hsw.2.1 a ha) hav' hb'

/-- The typed entry `Args` pairs: each register-passed parameter's vreg of its class. -/
theorem entryRegs_eqT : ∀ (E : List (((Nat × Clif.Ty) × ArgLoc) × Nat)),
    (∀ q ∈ E, R (vregOf ctx q.1.1.1) = vregOf ctx q.1.1.1) →
    E.filterMap (entryRegOfT ctx R) = argPairsT (valClassOf ctx) (entryNs E)
  | [], _ => rfl
  | ((⟨x, ty⟩, .reg p), b) :: E, h => by
    simp only [List.filterMap_cons, entryRegOfT, entryNs, argPairsT, List.map_cons]
    rw [h _ (List.mem_cons_self ..)]
    congr 1
    exact entryRegs_eqT E (fun q hq => h q (List.mem_cons_of_mem _ hq))
  | ((⟨x, ty⟩, .stack o), b) :: E, h => by
    simp only [List.filterMap_cons, entryRegOfT, entryNs]
    exact entryRegs_eqT E (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- **Entry**: the entry block's `Args` defines the register-passed parameters from their
argument registers, then the loads the stack-passed ones from the caller's outgoing area. -/
theorem entry_stepT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hFP : MemRefinesFP (fun _ => True) F sb sem)
    (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) :
    ∃ k ρ₁ w₁, Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, k, ρ₁, w₁⟩) ∧
      MatchT f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁⟩ := by
  obtain ⟨L, hL⟩ := H.blow hB0
  obtain ⟨vb, hvb, -, -, -, -, -, -, hcode, htne, -⟩ := H.shape.blk 0 B0 L hB0 hL
  obtain ⟨hnd, hA⟩ := H.cert.entry B0 hB0
  have hB0mem : B0 ∈ f.blocks := List.mem_of_getElem? hB0
  obtain ⟨hlocs, bytes, hb⟩ := H.entryLocs
  have hbm := sigParamBytes_eq_map hb
  -- lengths: parameters, arguments, locations, byte sizes
  have hla : args.length = B0.params.length := by
    have := congrArg List.length hty; simpa using this
  have hls : args.length = f.sig.params.length := by
    have := congrArg List.length hsig; simpa using this
  have hlb : bytes.length = f.sig.params.length := by rw [hbm, List.length_map]
  obtain ⟨E, hEdef⟩ : ∃ E, E = entryParams f B0 := ⟨_, rfl⟩
  have hE : E = (B0.params.zip (locsOf f.sig)).zip bytes := by
    rw [hEdef]; simp only [entryParams, hb]
  have hEids : E.map (·.1.1.1) = B0.params.map (·.1) := by
    rw [hE]
    have h1 : (B0.params.zip (locsOf f.sig)).length = B0.params.length := by
      simp [List.length_zip]; omega
    have h2 : ((B0.params.zip (locsOf f.sig)).zip bytes).map Prod.fst =
        B0.params.zip (locsOf f.sig) := List.map_fst_zip (by omega)
    have h3 : (B0.params.zip (locsOf f.sig)).map Prod.fst = B0.params :=
      List.map_fst_zip (by omega)
    rw [show (fun q : ((Nat × Clif.Ty) × ArgLoc) × Nat => q.1.1.1) =
      (fun q : Nat × Clif.Ty => q.1) ∘ Prod.fst ∘ Prod.fst from rfl, ← List.map_map,
      ← List.map_map, h2, h3]
  have hRid : ∀ q ∈ E, R (vregOf ctx q.1.1.1) = vregOf ctx q.1.1.1 := by
    intro q hq
    have hq1 : q.1.1 ∈ B0.params := by
      rw [hE] at hq
      exact (List.of_mem_zip (List.of_mem_zip hq).1).1
    simp [vregOf, H.shape.ren.vreg, H.shape.params B0 hB0mem q.1.1 hq1]
  -- parameter `m`: its entry, argument and location
  have hEget : ∀ (m : Nat) (q : Clif.ValueId × Clif.Ty), B0.params[m]? = some q →
      ∃ (loc : ArgLoc) (b : Nat), (locsOf f.sig)[m]? = some loc ∧
      bytes[m]? = some b ∧ E[m]? = some ((q, loc), b) := by
    intro m q hq
    have hm : m < B0.params.length := (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨loc, hloc⟩ : ∃ loc, (locsOf f.sig)[m]? = some loc :=
      ⟨(locsOf f.sig)[m]'(by omega), by simp⟩
    obtain ⟨b, hbb⟩ : ∃ b, bytes[m]? = some b := ⟨bytes[m]'(by omega), by simp⟩
    exact ⟨loc, b, hloc, hbb, by rw [hE]; simp [List.getElem?_zip_eq_some, hq, hloc, hbb]⟩
  have hbyte : ∀ (m : Nat) (v : Clif.Val) (b : Nat), args[m]? = some v → bytes[m]? = some b → b = v.ty.bytes := by
    intro m v b hv hbb
    rw [hbm, List.getElem?_map] at hbb
    have := congrArg (·[m]?) hsig
    simp only [List.getElem?_map, hv, Option.map_some] at this
    cases hp : f.sig.params[m]? with
    | none => rw [hp] at this; cases this
    | some p =>
      rw [hp] at this hbb
      simp only [Option.map_some, Option.some.injEq] at this hbb
      rw [← hbb, this]
  -- every entry of `E` is a parameter's
  have hEmem : ∀ q ∈ E, ∃ (m : Nat) (v : Clif.Val), E[m]? = some q ∧ args[m]? = some v := by
    intro q hq
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hq
    have hmE : m < E.length := (List.getElem?_eq_some_iff.mp hm).1
    have : E.length ≤ args.length := by rw [hE]; simp [List.length_zip]; omega
    exact ⟨m, args[m]'(by omega), hm, by simp⟩
  have hentry : ∀ q ∈ E, ∀ (m : Nat) (v : Clif.Val), E[m]? = some q → args[m]? = some v →
      (q.1.2, v) ∈ (locsOf f.sig).zip args ∧ q.2 = v.ty.bytes ∧ bytes[m]? = some q.2 := by
    intro q hq m v hm hv
    rw [hE] at hm
    simp only [List.getElem?_zip_eq_some] at hm
    obtain ⟨⟨-, hl⟩, hbb⟩ := hm
    exact ⟨List.mem_iff_getElem?.mpr ⟨m, by simp [List.getElem?_zip_eq_some, hl, hv]⟩,
      hbyte m v _ hv hbb, hbb⟩
  -- a parameter's class is its argument's
  have hcls : ∀ q ∈ E, ∀ (m : Nat) (v : Clif.Val), E[m]? = some q → args[m]? = some v →
      valClassOf ctx q.1.1.1 = tyClass v.ty := by
    intro q hq m v hm hv
    have hm' := hm
    rw [hE] at hm'
    simp only [List.getElem?_zip_eq_some] at hm'
    obtain ⟨⟨hp, -⟩, -⟩ := hm'
    have hpt := H.cert.paramTy B0 hB0mem q.1.1 (List.mem_of_getElem? hp)
    have hvt : v.ty = q.1.1.2 := by
      have := congrArg (·[m]?) hty
      simp only [List.getElem?_map, hv, hp, Option.map_some, Option.some.injEq] at this
      exact this
    simp only [valClassOf, hpt, Option.map_some, Option.getD_some, valClass_ofClif, hvt]
  -- the code before the statements
  obtain ⟨ns, hnsdef⟩ : ∃ ns, ns = entryNs E := ⟨_, rfl⟩
  have hpre : preT f ctx R 0 =
      .args (argPairsT (valClassOf ctx) ns) :: E.filterMap (entryLoadOfT ctx R) := by
    simp only [preT, hB0, entryRegsT, entryLoadsT, ← hEdef]
    rw [entryRegs_eqT E hRid, ← hnsdef]
  have hnsnd : (ns.map (·.1)).Nodup := by
    rw [hnsdef]
    exact (entryNs_sublist E).nodup (by rw [hEids]; exact hnd)
  -- `Args`
  have hops := operands_argsT (valClassOf ctx) ns
  have hvu : vuses (argOpsT (valClassOf ctx) ns).toArray ρ₀ = [] := by
    simp only [vuses, List.toList_toArray, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro o ho
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
    rw [← hq']; simp [Operand.isUse]
  have hsem := hds.args (argPairsT (valClassOf ctx) ns) w₀
  rw [← hvu] at hsem
  have hlen : ((argPairsT (valClassOf ctx) ns).map fun d => regVal w₀ d.2).length =
      ((argOpsT (valClassOf ctx) ns).toArray.toList.filter Operand.isDef).length := by
    have : (argOpsT (valClassOf ctx) ns).filter Operand.isDef = argOpsT (valClassOf ctx) ns := by
      rw [List.filter_eq_self]
      intro o ho
      obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
      rw [← hq']; rfl
    rw [List.toList_toArray, this]
    simp only [List.length_map, argPairsT, argOpsT]
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁, ρ₁ = vdefUpd (argOpsT (valClassOf ctx) ns).toArray
      ((argPairsT (valClassOf ctx) ns).map fun d => regVal w₀ d.2) ρ₀ :=
    ⟨_, rfl⟩
  -- the loads
  obtain ⟨ρ₂, w₂, hrun, hmr₂, -, hreg, hstk, -⟩ := entryLoads_runT hMem hFP hMR E ρ₁ slots cs.mem
    w₀ hRid (by rw [hEids]; exact hnd)
    (fun q hq off ho => by
      obtain ⟨m, v, hm, hv⟩ := hEmem q hq
      obtain ⟨hmem, hqb, hqbm⟩ := hentry q hq m v hm hv
      have h := hargs _ _ hmem
      rw [ho] at h
      obtain ⟨hav, -⟩ := h
      rw [hqb]
      refine ⟨hqb ▸ sigParamBytes_bytes hb _ (List.mem_of_getElem? hqbm), fun hf => ?_, hav⟩
      rw [hcls q hq m v hm hv] at hf
      exact bytes_of_float hf) hmr
  have hseq : seqRun sem (E.filterMap (entryLoadOfT ctx R)) ρ₁ w₀ = some (.fall ρ₂ w₂) := hrun
  have hsz : (preT f ctx R 0).length < vb.insts.size := by
    have h1 : vb.insts.size = vb.insts.toList.length := by simp
    have h2 : 0 < (tseg R bl 0).length := List.length_pos_iff.mpr htne
    rw [h1, hcode]; simp only [List.length_append]; omega
  have hseg0 : SegAt vb 0 (preT f ctx R 0) := by
    intro k hk
    rw [Nat.zero_add, ← Array.getElem?_toList, hcode, List.append_assoc,
      List.getElem?_append_left hk, List.getElem?_eq_getElem hk]
  have hvb0 : vb.insts[0]? = some (.args (argPairsT (valClassOf ctx) ns)) := by
    exact SegAt.head (show SegAt vb 0 (MInst.args (argPairsT (valClassOf ctx) ns) ::
      E.filterMap (entryLoadOfT ctx R)) by rw [← hpre]; exact hseg0)
  have hstep : VStep vc sem (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, 1, ρ₁, w₀⟩) := by
    rw [hρ₁]
    exact VStep.step hvb hvb0 hops hsem hlen (VNext.next (by rw [hpre] at hsz; simp at hsz; omega))
  have hseg1 : SegAt vb 1 (E.filterMap (entryLoadOfT ctx R)) := by
    have := (show SegAt vb 0 (.args (argPairsT (valClassOf ctx) ns) ::
      E.filterMap (entryLoadOfT ctx R)) by rw [← hpre]; exact hseg0).tail
    simpa using this
  have hstar := seqRun_fall_star hvb hseg1 (by rw [hpre] at hsz; simp at hsz; omega) hseq
  refine ⟨1 + (E.filterMap (entryLoadOfT ctx R)).length, ρ₂, w₂, .step hstep hstar, hcall, hfunc,
    hslots, hmr₂, B0, 0, hB0, hterm, Nat.zero_le _, by simp [hbody],
    by simp [posT, hpre]; omega, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxp, -⟩ := hA x hx
    obtain ⟨m, hm, hxm⟩ := List.getElem_of_mem hxp
    have hm' : m < B0.params.length := by simpa using hm
    have hqm : B0.params[m]? = some B0.params[m] := List.getElem?_eq_getElem hm'
    have hxq : B0.params[m].1 = x := by simpa using hxm
    have hma : m < args.length := by omega
    have hrx : cs.frame.regs x = some args[m] :=
      setMany_nodup hregs hnd m x args[m] (by rw [← hxq]; simp [hqm]) (List.getElem?_eq_getElem hma)
    refine ⟨args[m], hrx, ?_⟩
    have hgx : gn x = x := by
      rw [← hxq]; exact H.shape.params B0 hB0mem _ (List.getElem_mem hm')
    show VHolds args[m] (ρ₂ (gn x))
    rw [hgx]
    obtain ⟨loc, b, hloc, hbb, hEm⟩ := hEget m _ hqm
    have hqE : ((B0.params[m], loc), b) ∈ E := List.mem_of_getElem? hEm
    have hmem : (loc, args[m]) ∈ (locsOf f.sig).zip args :=
      List.mem_iff_getElem?.mpr ⟨m, by simp [List.getElem?_zip_eq_some, hloc, hma]⟩
    have hb' : b = args[m].ty.bytes := hbyte m _ b (List.getElem?_eq_getElem hma) hbb
    have h := hargs _ _ hmem
    cases loc with
    | reg r =>
      have h1 := hreg _ hqE r rfl
      simp only at h1
      rw [← hxq, h1]
      have hns : (B0.params[m].1, r) ∈ ns := hnsdef ▸ mem_entryNs hqE rfl
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hns
      rw [hρ₁, vdefUpd_argOpsT hnsnd (by simp [argPairsT]) i hi (x := regVal w₀ r)
        (by simp [argPairsT, hi])]
      exact h
    | stack off =>
      have h1 := hstk _ hqE off rfl
      simp only at h1
      rw [← hxq, h1, hb']
      obtain ⟨-, hrd⟩ := h
      have hbs : args[m].ty.bytes = 1 ∨ args[m].ty.bytes = 2 ∨ args[m].ty.bytes = 4 ∨
          args[m].ty.bytes = 8 := hb' ▸ sigParamBytes_bytes hb _ (List.mem_of_getElem? hbb)
      cases hc : valClassOf ctx B0.params[m].1 with
      | int =>
        obtain ⟨hob, -, hsg⟩ := loadOpOfBytes_facts hbs
        have hw : args[m].ty.width ≤ 64 :=
          (show ∀ t : Clif.Ty, (t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8) →
            t.width ≤ 64 by intro t; cases t <;> decide) _ hbs
        simp only [stackVal, VHolds, ofX, loadVal, hsg, Bool.false_eq_true, ↓reduceIte]
        rw [hob, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ hw]
        exact hrd
      | float =>
        have hw : args[m].ty.width ≤ 128 := by cases args[m].ty <;> decide
        simp only [stackVal, VHolds]
        rw [BitVec.setWidth_setWidth_of_le _ hw]
        exact hrd
  · refine ⟨fun x d info cl v hd _ _ _ hv => ?_, fun x t v ht hv => ?_⟩
    · have hx0 : x ∈ A 0 0 := restrict_regs_isSome (by rw [hv]; rfl)
      rw [(hA x hx0).2] at hd
      cases hd
    · have hx0 : x ∈ A 0 0 := restrict_regs_isSome (by rw [hv]; rfl)
      rw [restrict_regs_of_mem hx0] at hv
      obtain ⟨q, hq, rfl, hqt⟩ := setMany_param_ty hregs hnd hty (hA x hx0).1 hv
      rw [H.cert.paramTy B0 hB0mem q hq] at ht
      rw [hqt]; exact Option.some.inj ht
  · intro x hx
    obtain ⟨hxp, -⟩ := hA x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxp
    exact ⟨_, H.cert.paramTy B0 hB0mem q hq⟩

/-- An entry load's value depends only on the loaded bytes. -/
theorem stackVal_congr_bytes {s t : Arm.ArmState} (cls : RegClass) {b : Nat} {a : BitVec 64}
    (h : ∀ k < b, s.mem (a + BitVec.ofNat 64 k) = t.mem (a + BitVec.ofNat 64 k))
    (hb : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) : stackVal cls b a s = stackVal cls b a t := by
  cases cls with
  | int =>
    simp only [stackVal, loadVal]
    rw [read_mem_bytes_congr _ _ (fun k hk => h k (by rw [(loadOpOfBytes_facts hb).1] at hk; exact hk))]
  | float =>
    simp only [stackVal]
    rw [read_mem_bytes_congr _ _ h]

/-- **Entry on two worlds** (agent/link-widen, stage 2): from two body-entry worlds related to
the same CLIF entry, with the same register arguments (in the parameter registers) and the same
stack-argument bytes (`x29` the same), the entry code (`Args`, then the loads) reaches the first
statement in both with the same vreg file; each world agrees with its entry world outside the
allocatable registers (`SameWorld F`). -/
theorem entry_step2T (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hFP : MemRefinesFP (fun _ => True) F sb sem)
    (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ w₀' : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hmr' : MR slots cs.mem w₀') (hargs : ArgsAtEntry F f.sig args w₀)
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) :
    ∃ k ρ₁ w₁ w₁', Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, k, ρ₁, w₁⟩) ∧
      MatchT f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁⟩ ∧ SameWorld F w₁ w₀ ∧
      Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀'⟩) (.run ⟨0, k, ρ₁, w₁'⟩) ∧
      MatchT f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁'⟩ ∧ SameWorld F w₁' w₀' := by
  obtain ⟨L, hL⟩ := H.blow hB0
  obtain ⟨vb, hvb, -, -, -, -, -, -, hcode, htne, -⟩ := H.shape.blk 0 B0 L hB0 hL
  obtain ⟨hnd, hA⟩ := H.cert.entry B0 hB0
  have hB0mem : B0 ∈ f.blocks := List.mem_of_getElem? hB0
  obtain ⟨hlocs, bytes, hb⟩ := H.entryLocs
  have hbm := sigParamBytes_eq_map hb
  have hla : args.length = B0.params.length := by
    have := congrArg List.length hty; simpa using this
  have hls : args.length = f.sig.params.length := by
    have := congrArg List.length hsig; simpa using this
  have hlb : bytes.length = f.sig.params.length := by rw [hbm, List.length_map]
  obtain ⟨E, hEdef⟩ : ∃ E, E = entryParams f B0 := ⟨_, rfl⟩
  have hE : E = (B0.params.zip (locsOf f.sig)).zip bytes := by
    rw [hEdef]; simp only [entryParams, hb]
  have hEids : E.map (·.1.1.1) = B0.params.map (·.1) := by
    rw [hE]
    have h1 : (B0.params.zip (locsOf f.sig)).length = B0.params.length := by
      simp [List.length_zip]; omega
    have h2 : ((B0.params.zip (locsOf f.sig)).zip bytes).map Prod.fst =
        B0.params.zip (locsOf f.sig) := List.map_fst_zip (by omega)
    have h3 : (B0.params.zip (locsOf f.sig)).map Prod.fst = B0.params :=
      List.map_fst_zip (by omega)
    rw [show (fun q : ((Nat × Clif.Ty) × ArgLoc) × Nat => q.1.1.1) =
      (fun q : Nat × Clif.Ty => q.1) ∘ Prod.fst ∘ Prod.fst from rfl, ← List.map_map,
      ← List.map_map, h2, h3]
  have hRid : ∀ q ∈ E, R (vregOf ctx q.1.1.1) = vregOf ctx q.1.1.1 := by
    intro q hq
    have hq1 : q.1.1 ∈ B0.params := by
      rw [hE] at hq
      exact (List.of_mem_zip (List.of_mem_zip hq).1).1
    simp [vregOf, H.shape.ren.vreg, H.shape.params B0 hB0mem q.1.1 hq1]
  have hEget : ∀ (m : Nat) (q : Clif.ValueId × Clif.Ty), B0.params[m]? = some q →
      ∃ (loc : ArgLoc) (b : Nat), (locsOf f.sig)[m]? = some loc ∧
      bytes[m]? = some b ∧ E[m]? = some ((q, loc), b) := by
    intro m q hq
    have hm : m < B0.params.length := (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨loc, hloc⟩ : ∃ loc, (locsOf f.sig)[m]? = some loc :=
      ⟨(locsOf f.sig)[m]'(by omega), by simp⟩
    obtain ⟨b, hbb⟩ : ∃ b, bytes[m]? = some b := ⟨bytes[m]'(by omega), by simp⟩
    exact ⟨loc, b, hloc, hbb, by rw [hE]; simp [List.getElem?_zip_eq_some, hq, hloc, hbb]⟩
  have hbyte : ∀ (m : Nat) (v : Clif.Val) (b : Nat), args[m]? = some v → bytes[m]? = some b → b = v.ty.bytes := by
    intro m v b hv hbb
    rw [hbm, List.getElem?_map] at hbb
    have := congrArg (·[m]?) hsig
    simp only [List.getElem?_map, hv, Option.map_some] at this
    cases hp : f.sig.params[m]? with
    | none => rw [hp] at this; cases this
    | some p =>
      rw [hp] at this hbb
      simp only [Option.map_some, Option.some.injEq] at this hbb
      rw [← hbb, this]
  have hEmem : ∀ q ∈ E, ∃ (m : Nat) (v : Clif.Val), E[m]? = some q ∧ args[m]? = some v := by
    intro q hq
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hq
    have hmE : m < E.length := (List.getElem?_eq_some_iff.mp hm).1
    have : E.length ≤ args.length := by rw [hE]; simp [List.length_zip]; omega
    exact ⟨m, args[m]'(by omega), hm, by simp⟩
  have hentry : ∀ q ∈ E, ∀ (m : Nat) (v : Clif.Val), E[m]? = some q → args[m]? = some v →
      (q.1.2, v) ∈ (locsOf f.sig).zip args ∧ q.2 = v.ty.bytes ∧ bytes[m]? = some q.2 := by
    intro q hq m v hm hv
    rw [hE] at hm
    simp only [List.getElem?_zip_eq_some] at hm
    obtain ⟨⟨-, hl⟩, hbb⟩ := hm
    exact ⟨List.mem_iff_getElem?.mpr ⟨m, by simp [List.getElem?_zip_eq_some, hl, hv]⟩,
      hbyte m v _ hv hbb, hbb⟩
  have hcls : ∀ q ∈ E, ∀ (m : Nat) (v : Clif.Val), E[m]? = some q → args[m]? = some v →
      valClassOf ctx q.1.1.1 = tyClass v.ty := by
    intro q hq m v hm hv
    have hm' := hm
    rw [hE] at hm'
    simp only [List.getElem?_zip_eq_some] at hm'
    obtain ⟨⟨hp, -⟩, -⟩ := hm'
    have hpt := H.cert.paramTy B0 hB0mem q.1.1 (List.mem_of_getElem? hp)
    have hvt : v.ty = q.1.1.2 := by
      have := congrArg (·[m]?) hty
      simp only [List.getElem?_map, hv, hp, Option.map_some, Option.some.injEq] at this
      exact this
    simp only [valClassOf, hpt, Option.map_some, Option.getD_some, valClass_ofClif, hvt]
  have htyA : TypedA ctx (A 0 0) := by
    intro x hx
    obtain ⟨hxp, -⟩ := hA x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxp
    exact ⟨_, H.cert.paramTy B0 hB0mem q hq⟩
  obtain ⟨ns, hnsdef⟩ : ∃ ns, ns = entryNs E := ⟨_, rfl⟩
  have hpre : preT f ctx R 0 =
      .args (argPairsT (valClassOf ctx) ns) :: E.filterMap (entryLoadOfT ctx R) := by
    simp only [preT, hB0, entryRegsT, entryLoadsT, ← hEdef]
    rw [entryRegs_eqT E hRid, ← hnsdef]
  have hnsnd : (ns.map (·.1)).Nodup := by
    rw [hnsdef]
    exact (entryNs_sublist E).nodup (by rw [hEids]; exact hnd)
  have hops := operands_argsT (valClassOf ctx) ns
  have hvu : vuses (argOpsT (valClassOf ctx) ns).toArray ρ₀ = [] := by
    simp only [vuses, List.toList_toArray, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro o ho
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
    rw [← hq']; simp [Operand.isUse]
  -- the argument registers agree
  have hargsEq : (argPairsT (valClassOf ctx) ns).map (fun d => regVal w₀' d.2) =
      (argPairsT (valClassOf ctx) ns).map (fun d => regVal w₀ d.2) := by
    apply List.map_congr_left
    intro d hd
    obtain ⟨⟨x, p⟩, hxp, rfl⟩ := List.mem_map.mp hd
    rw [hnsdef] at hxp
    obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp hxp
    obtain ⟨m, v, hm, hv⟩ := hEmem q hq
    obtain ⟨hmem, -, -⟩ := hentry q hq m v hm hv
    revert hqe hmem
    cases hl : q.1.2 with
    | stack o => intro hqe; cases hqe
    | reg r =>
      intro hqe hmem
      simp only [Option.some.injEq, Prod.mk.injEq] at hqe
      obtain ⟨-, rfl⟩ := hqe
      exact hreg r v hmem
  have hsem := hds.args (argPairsT (valClassOf ctx) ns) w₀
  rw [← hvu] at hsem
  have hsem' := hds.args (argPairsT (valClassOf ctx) ns) w₀'
  rw [← hvu, hargsEq] at hsem'
  have hlen : ((argPairsT (valClassOf ctx) ns).map fun d => regVal w₀ d.2).length =
      ((argOpsT (valClassOf ctx) ns).toArray.toList.filter Operand.isDef).length := by
    have : (argOpsT (valClassOf ctx) ns).filter Operand.isDef = argOpsT (valClassOf ctx) ns := by
      rw [List.filter_eq_self]
      intro o ho
      obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
      rw [← hq']; rfl
    rw [List.toList_toArray, this]
    simp only [List.length_map, argPairsT, argOpsT]
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁, ρ₁ = vdefUpd (argOpsT (valClassOf ctx) ns).toArray ((argPairsT (valClassOf ctx) ns).map fun d => regVal w₀ d.2) ρ₀ :=
    ⟨_, rfl⟩
  have hloadsF : ∀ (w : Arm.ArmState), Arm.r (.GPR 29#5) w = Arm.r (.GPR 29#5) w₀ →
      ∀ q ∈ E, ∀ off, q.1.2 = .stack off → (q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8) ∧
        (valClassOf ctx q.1.1.1 = .float → q.2 = 4 ∨ q.2 = 8) ∧ Avoids F q.2 (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) := by
    intro w hw q hq off ho
    obtain ⟨m, v, hm, hv⟩ := hEmem q hq
    obtain ⟨hmem, hqb, hqbm⟩ := hentry q hq m v hm hv
    have h := hargs _ _ hmem
    rw [ho] at h
    obtain ⟨hav, -⟩ := h
    rw [hqb, hw]
    refine ⟨hqb ▸ sigParamBytes_bytes hb _ (List.mem_of_getElem? hqbm), fun hf => ?_, hav⟩
    rw [hcls q hq m v hm hv] at hf
    exact bytes_of_float hf
  obtain ⟨ρ₂, w₂, hrun, hmr₂, hfr, hreg2, hstk2, hsw2⟩ := entryLoads_runT hMem hFP hMR E ρ₁ slots
    cs.mem w₀ hRid (by rw [hEids]; exact hnd) (hloadsF w₀ rfl) hmr
  obtain ⟨ρ₂', w₂', hrun', hmr₂', hfr', hreg2', hstk2', hsw2'⟩ := entryLoads_runT hMem hFP hMR E ρ₁
    slots cs.mem w₀' hRid (by rw [hEids]; exact hnd) (hloadsF w₀' h29) hmr'
  have hρ₂ : ρ₂' = ρ₂ := by
    funext y
    by_cases hy : y ∈ E.map (·.1.1.1)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      cases hl : q.1.2 with
      | reg p => rw [hreg2' q hq p hl, hreg2 q hq p hl]
      | stack off =>
        rw [hstk2' q hq off hl, hstk2 q hq off hl, h29]
        obtain ⟨m, v, hm, hv⟩ := hEmem q hq
        obtain ⟨hmem, hqb, hqbm⟩ := hentry q hq m v hm hv
        have hbs : q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8 :=
          sigParamBytes_bytes hb _ (List.mem_of_getElem? hqbm)
        exact stackVal_congr_bytes _ (fun k hk => by rw [hqb] at hk; exact hstk off v (hl ▸ hmem) k hk) hbs
    · rw [hfr' y hy, hfr y hy]
  rw [hρ₂] at hrun'
  have hsz : (preT f ctx R 0).length < vb.insts.size := by
    have h1 : vb.insts.size = vb.insts.toList.length := by simp
    have h2 : 0 < (tseg R bl 0).length := List.length_pos_iff.mpr htne
    rw [h1, hcode]; simp only [List.length_append]; omega
  have hseg0 : SegAt vb 0 (preT f ctx R 0) := by
    intro k hk
    rw [Nat.zero_add, ← Array.getElem?_toList, hcode, List.append_assoc,
      List.getElem?_append_left hk, List.getElem?_eq_getElem hk]
  have hvb0 : vb.insts[0]? = some (.args (argPairsT (valClassOf ctx) ns)) := by
    exact SegAt.head (show SegAt vb 0 (MInst.args (argPairsT (valClassOf ctx) ns) :: E.filterMap (entryLoadOfT ctx R)) by
      rw [← hpre]; exact hseg0)
  have hnext : 0 + 1 < vb.insts.size := by rw [hpre] at hsz; simp at hsz; omega
  have hstep : VStep vc sem (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, 1, ρ₁, w₀⟩) := by
    rw [hρ₁]
    exact VStep.step hvb hvb0 hops hsem hlen (VNext.next hnext)
  have hstep' : VStep vc sem (.run ⟨0, 0, ρ₀, w₀'⟩) (.run ⟨0, 1, ρ₁, w₀'⟩) := by
    rw [hρ₁]
    exact VStep.step hvb hvb0 hops hsem' hlen (VNext.next hnext)
  have hseg1 : SegAt vb 1 (E.filterMap (entryLoadOfT ctx R)) := by
    have := (show SegAt vb 0 (.args (argPairsT (valClassOf ctx) ns) :: E.filterMap (entryLoadOfT ctx R)) by
      rw [← hpre]; exact hseg0).tail
    simpa using this
  have hlt : 1 + (E.filterMap (entryLoadOfT ctx R)).length < vb.insts.size := by
    rw [hpre] at hsz; simp at hsz; omega
  have hstar := seqRun_fall_star hvb hseg1 hlt hrun
  have hstar' := seqRun_fall_star hvb hseg1 hlt hrun'
  -- the vreg file holds the parameters, the DFG facts
  have hheld : Held gn (A 0 0) ρ₂ cs.frame := by
    intro x hx
    obtain ⟨hxp, -⟩ := hA x hx
    obtain ⟨m, hm, hxm⟩ := List.getElem_of_mem hxp
    have hm' : m < B0.params.length := by simpa using hm
    have hqm : B0.params[m]? = some B0.params[m] := List.getElem?_eq_getElem hm'
    have hxq : B0.params[m].1 = x := by simpa using hxm
    have hma : m < args.length := by omega
    have hrx : cs.frame.regs x = some args[m] :=
      setMany_nodup hregs hnd m x args[m] (by rw [← hxq]; simp [hqm]) (List.getElem?_eq_getElem hma)
    refine ⟨args[m], hrx, ?_⟩
    have hgx : gn x = x := by
      rw [← hxq]; exact H.shape.params B0 hB0mem _ (List.getElem_mem hm')
    show VHolds args[m] (ρ₂ (gn x))
    rw [hgx]
    obtain ⟨loc, b, hloc, hbb, hEm⟩ := hEget m _ hqm
    have hqE : ((B0.params[m], loc), b) ∈ E := List.mem_of_getElem? hEm
    have hmem : (loc, args[m]) ∈ (locsOf f.sig).zip args :=
      List.mem_iff_getElem?.mpr ⟨m, by simp [List.getElem?_zip_eq_some, hloc, hma]⟩
    have hb' : b = args[m].ty.bytes := hbyte m _ b (List.getElem?_eq_getElem hma) hbb
    have h := hargs _ _ hmem
    cases loc with
    | reg r =>
      have h1 := hreg2 _ hqE r rfl
      simp only at h1
      rw [← hxq, h1]
      have hns : (B0.params[m].1, r) ∈ ns := hnsdef ▸ mem_entryNs hqE rfl
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hns
      rw [hρ₁, vdefUpd_argOpsT hnsnd (by simp [argPairsT]) i hi (x := regVal w₀ r) (by simp [argPairsT, hi])]
      exact h
    | stack off =>
      have h1 := hstk2 _ hqE off rfl
      simp only at h1
      rw [← hxq, h1, hb']
      obtain ⟨-, hrd⟩ := h
      have hbs : args[m].ty.bytes = 1 ∨ args[m].ty.bytes = 2 ∨ args[m].ty.bytes = 4 ∨
          args[m].ty.bytes = 8 := hb' ▸ sigParamBytes_bytes hb _ (List.mem_of_getElem? hbb)
      cases hc : valClassOf ctx B0.params[m].1 with
      | int =>
        obtain ⟨hob, -, hsg⟩ := loadOpOfBytes_facts hbs
        have hw : args[m].ty.width ≤ 64 :=
          (show ∀ t : Clif.Ty, (t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8) →
            t.width ≤ 64 by intro t; cases t <;> decide) _ hbs
        simp only [stackVal, VHolds, ofX, loadVal, hsg, Bool.false_eq_true, ↓reduceIte]
        rw [hob, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ hw]
        exact hrd
      | float =>
        have hw : args[m].ty.width ≤ 128 := by cases args[m].ty <;> decide
        simp only [stackVal, VHolds]
        rw [BitVec.setWidth_setWidth_of_le _ hw]
        exact hrd
  have hdfg : DFGCons ctx (restrict cs.frame (A 0 0)) := by
    refine ⟨fun x d info cl v hd _ _ _ hv => ?_, fun x t v ht hv => ?_⟩
    · have hx0 : x ∈ A 0 0 := restrict_regs_isSome (by rw [hv]; rfl)
      rw [(hA x hx0).2] at hd
      cases hd
    · have hx0 : x ∈ A 0 0 := restrict_regs_isSome (by rw [hv]; rfl)
      rw [restrict_regs_of_mem hx0] at hv
      obtain ⟨q, hq, rfl, hqt⟩ := setMany_param_ty hregs hnd hty (hA x hx0).1 hv
      rw [H.cert.paramTy B0 hB0mem q hq] at ht
      rw [hqt]; exact Option.some.inj ht
  refine ⟨1 + (E.filterMap (entryLoadOfT ctx R)).length, ρ₂, w₂, w₂', .step hstep hstar,
    ⟨hcall, hfunc, hslots, hmr₂, B0, 0, hB0, hterm, Nat.zero_le _, by simp [hbody],
      by simp [posT, hpre]; omega, hheld, hdfg, htyA⟩, hsw2, .step hstep' hstar',
    ⟨hcall, hfunc, hslots, hmr₂', B0, 0, hB0, hterm, Nat.zero_le _, by simp [hbody],
      by simp [posT, hpre]; omega, hheld, hdfg, htyA⟩, hsw2'⟩

end

/-! ## Whole runs -/

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
  {slots : List (Clif.SlotId × Nat)}

/-- What a VCode run from `vs` does when the CLIF run from the matching state ends (`RunOk`
with the returned values in their classes' return registers, `RetRegsOk`). -/
def RunOkT (rt : List Clif.Ty) (vc : VCode) (sem : ISem CV W) (MR : MemRelTW W)
    (slots : List (Clif.SlotId × Nat)) (vs : VState CV W) : Clif.Outcome → Prop
  | .returned vals cm => ∃ us outs w cm0, VRetFrom vc sem vs us outs w ∧
      RetRegsOk vals us ∧ us.length = outs.length ∧
      PrefixHold vals outs ∧ MR slots cm0 w ∧ cm = (cm0.free (slots.map (·.2))).leave ∧
      vals.map (·.ty) = rt
  | .trapped c => VTrapFrom vc sem vs c
  | .stuck _ | .outOfFuel => True

/-- `RunOkT` with the ABI return values: a return also returns `sv` (the frame's `sretRet f`
values at the `return`, which satisfy `Q`); the return registers pin the CLIF values
(`RetRegsOk vals us`, the `sret` pointer in x8 after them), all the use values held
(`AllHold (vals ++ sv)`). -/
def RunOkTAbi (rt : List Clif.Ty) (vc : VCode) (sem : ISem CV W) (MR : MemRelTW W)
    (slots : List (Clif.SlotId × Nat)) (Q : List Clif.Val → Prop) (vs : VState CV W) :
    Clif.Outcome → Prop
  | .returned vals cm => ∃ us outs w cm0 sv, VRetFrom vc sem vs us outs w ∧
      RetRegsOk vals us ∧ us.length = outs.length ∧
      Q sv ∧ AllHold (vals ++ sv) outs ∧ MR slots cm0 w ∧
      cm = (cm0.free (slots.map (·.2))).leave ∧ vals.map (·.ty) = rt
  | .trapped c => VTrapFrom vc sem vs c
  | .stuck _ | .outOfFuel => True

theorem RunOkTAbi.prefix {rt : List Clif.Ty} {Q : List Clif.Val → Prop} {vs vs' : VState CV W}
    {o : Clif.Outcome}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : RunOkTAbi rt vc sem MR slots Q vs' o) :
    RunOkTAbi rt vc sem MR slots Q vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, sv, hr, h1, h2, h3, h4, h5, h6, h7⟩ := h'
    exact ⟨us, outs, w, cm0, sv, VRetFrom.prefix h hr, h1, h2, h3, h4, h5, h6, h7⟩
  | trapped c => exact VTrapFrom.prefix h h'
  | _ => trivial

theorem RunOkTAbi.runOkT {rt : List Clif.Ty} {Q : List Clif.Val → Prop} {vs : VState CV W}
    {o : Clif.Outcome}
    (h : RunOkTAbi rt vc sem MR slots Q vs o) : RunOkT rt vc sem MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, sv, hr, h1, h2, -, h4, h5, h6, h7⟩ := h
    refine ⟨us, outs, w, cm0, hr, h1, h2, AllHold.prefix_append h4, h5, h6, h7⟩
  | trapped c => exact h
  | _ => trivial

theorem RunOkT.prefix {rt : List Clif.Ty} {vs vs' : VState CV W} {o : Clif.Outcome}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : RunOkT rt vc sem MR slots vs' o) :
    RunOkT rt vc sem MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, hr, h1⟩ := h'
    exact ⟨us, outs, w, cm0, VRetFrom.prefix h hr, h1⟩
  | trapped c => exact VTrapFrom.prefix h h'
  | _ => trivial

/-- **Whole runs with the ABI return values** (`RunOkTAbi`): a return also returns `sv`, the
frame's `sretRet f` values at the `return`, satisfying `Q` in every reachable state (`hQ`); the
return registers of the combined list and all the use values held. -/
theorem sim_runT_abi (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p) {cs : Clif.State}
    (hP : RunPrem env p f cs) {Q : List Clif.Val → Prop}
    (hQ : ∀ s sv, Reach env p cs s → s.frame.getMany (sretRet f) = .ok sv → Q sv) :
    ∀ fuel s (vs : VState CV W), Reach env p cs s →
      MatchT f ctx R gn bl A MR slots s vs →
        RunOkTAbi (Clif.AbiParam.tys f.sig.returns) vc sem MR slots Q vs
          (Clif.runLoop env p fuel s) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro s vs hr hm
  cases fuel with
  | zero => trivial
  | succ n =>
    obtain ⟨b, k, ρ, w⟩ := vs
    rw [Clif.runLoop_succ]
    have hfunc : s.frame.func = f := hm.2.1
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, T3⟩ := term_stepT_abi H hm hbody hty
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨vs', hstar, hm'⟩ := T1 s' hs
          exact RunOkTAbi.prefix hstar (ih n (by omega) s' vs' (hr.snoc hs) hm')
        | done vals cm =>
          obtain ⟨us, outs, w', sv, hret, h1, h2, h3, h4, h5, h6, h7⟩ := T2 vals cm hs
          exact ⟨us, outs, w', s.mem, sv, hret, h1, h2, hQ s sv hr h3, h4, h5, h6, h7⟩
        | trapped c => exact T3 c hs
        | stuck => trivial
      | true =>
        obtain ⟨B, j, hB, hterm, -⟩ := hm.2.2.2.2
        have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
        obtain ⟨et, hT⟩ : ∃ et, IsTryWith s.frame.term et := by
          cases ht : s.frame.term with
          | tryCall fn args et => exact ⟨et, .inl ⟨fn, args, rfl⟩⟩
          | tryCallIndirect c args et => exact ⟨et, .inr ⟨c, args, rfl⟩⟩
          | _ => rw [ht] at hty; cases hty
        have hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
            s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
          fun callee args ht => hP.tryIndirect s callee args et hr hbody ht ⟨B, hBmem, hterm.symm.trans ht⟩
        obtain ⟨Tnd, Tnx⟩ := term_step_tryT H hm hbody hT hind
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨N1, N2, N3⟩ := Tnx s' hs
          cases n with
          | zero => trivial
          | succ m =>
            show RunOkTAbi _ vc sem MR slots _ _ (Clif.runLoop env p (m + 1) s')
            rw [Clif.runLoop_succ]
            cases hs' : Clif.step env p s' with
            | next s'' =>
              obtain ⟨vs', hstar, hm'⟩ := N3 s'' hs'
              exact RunOkTAbi.prefix hstar (ih m (by omega) s'' vs' ((hr.snoc hs).snoc hs') hm')
            | done vals cm => exact absurd hs' (N2 vals cm)
            | trapped c => exact absurd hs' (N1 c)
            | stuck => trivial
        | done vals cm => exact absurd hs (Tnd vals cm)
        | trapped c =>
          rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
          · exact absurd (hterm.symm.trans hT) (hP.tryCall s c fn args et hr hs hbody hT B hBmem)
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCallInd s c callee args et hr hs hbody hT B hBmem)
        | stuck => trivial
    | cons st rest =>
      obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := id hm
      have hst : st ∈ B.body := by
        rw [hbd] at hbody
        exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
      have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
      have hext : ∀ fn args, st.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
          p.func? e.name = none := by
        intro fn args hi e he
        exact H.ext B hBmem st hst fn args hi e (hfunc ▸ he)
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr hbody hi ⟨B, hBmem, hst⟩
      obtain ⟨S1, S2⟩ := stmt_stepT H hm hbody hind
      cases hs : Clif.step env p s with
      | next s' =>
        obtain ⟨vs', hstar, hm'⟩ := S1 s' hs
        exact RunOkTAbi.prefix hstar (ih n (by omega) s' vs' (hr.snoc hs) hm')
      | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
      | trapped c => exact S2 c hs (hP.stmt s c st rest hr hs hbody)
      | stuck => trivial

/-- **Whole runs**: from matching states, every CLIF outcome is realised by the VCode run
(`RunOkT`), without a claim on the frame's `sretRet f` values. -/
theorem sim_runT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p) {cs : Clif.State}
    (hP : RunPrem env p f cs) :
    ∀ fuel s (vs : VState CV W), Reach env p cs s →
      MatchT f ctx R gn bl A MR slots s vs →
        RunOkT (Clif.AbiParam.tys f.sig.returns) vc sem MR slots vs (Clif.runLoop env p fuel s) :=
  fun fuel s vs hr hm =>
    (sim_runT_abi H hP (Q := fun _ => True) (fun _ _ _ _ => trivial) fuel s vs hr hm).runOkT
end

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- **The typed driver lemma with the ABI return values** (`RunOkTAbi`): a return also returns
`sv`, the frame's `sretRet f` values, satisfying `Q` (`hQ`), all held (`AllHold`); the return
registers pin the CLIF values to their classes' registers (`RetRegsOk`, the `sret` pointer in
x8 after them). -/
theorem driver_correctT_abi (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p)
    (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hFP : MemRefinesFP (fun _ => True) F sb sem)
    (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPrem env p f cs) {Q : List Clif.Val → Prop}
    (hQ : ∀ s sv, Reach env p cs s → s.frame.getMany (sretRet f) = .ok sv → Q sv) (fuel : Nat) :
    RunOkTAbi (Clif.AbiParam.tys f.sig.returns) vc sem MR slots Q ⟨0, 0, ρ₀, w₀⟩
      (Clif.runLoop env p fuel cs) := by
  obtain ⟨k, ρ₁, w₁, hstar, hm⟩ := entry_stepT H hds hMem hFP hMR hB0 hcall hfunc hslots hbody
    hterm hregs hty hsig hmr hargs (ρ₀ := ρ₀)
  exact RunOkTAbi.prefix hstar (sim_runT_abi H hP hQ fuel cs _ (.refl _) hm)

/-- **The typed driver lemma (CLIF → VCode).** A CLIF run of `f` from an entry state
(parameters bound to `args`, which the VCode world holds at their ABI locations) is realised by
the VCode run from the entry: returns through `rets` with the returned values held in their
classes' return registers, and memory related; explicit traps reach an instruction halting with
the same code. -/
theorem driver_correctT (H : DriverHypT f vc ctx st0 R gn bl A sem MR env p) (hds : DriverSem sem)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hFP : MemRefinesFP (fun _ => True) F sb sem)
    (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPrem env p f cs) (fuel : Nat) :
    RunOkT (Clif.AbiParam.tys f.sig.returns) vc sem MR slots ⟨0, 0, ρ₀, w₀⟩
      (Clif.runLoop env p fuel cs) :=
  (driver_correctT_abi H hds hMem hFP hMR hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr
    hargs hP (Q := fun _ => True) (fun _ _ _ _ => trivial) fuel).runOkT

end

/-! ## Integer specialization -/

/-- **An integer driver hypothesis is a typed one** (`LowerShape` is a `LowerShapeT`, the
integer calls of a `CtxInv` context are the typed calls of that context). -/
theorem DriverHyp.toT {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {W : Type} {sem : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) :
    DriverHypT f vc ctx st0 R gn bl A sem MR env p where
  shape := lowerShapeT_of_lowerShape H.shape
  cert := H.cert
  dsem := H.dsem
  insts := H.insts.toT H.shape.ctxInv H.subE
  terms := H.terms.toT H.shape.ctxInv
  ext := H.ext
  indSig := H.indSig
  subET := Compile.functionET_of_functionE H.subE
  brIdx := H.brIdx
  noTail := H.noTail
  tries := let ⟨out, h1, h2⟩ := H.tries; ⟨out, h1.toT H.shape.ctxInv, h2⟩
  tryExt := H.tryExt
  tryInd := H.tryInd.toT H.shape.ctxInv
  tryIndSig := H.tryIndSig
  cfg := H.cfg
  entryLocs := H.entryLocs

end Backend.Proof.Driver
