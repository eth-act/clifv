import FV.Backend.Proof.LowerLemmas
import FV.Backend.Proof.TryRegs

/-!
# The driver simulation: CLIF steps ↦ VCode steps (M7)

`Match s vs`: the CLIF state `s` (one activation of `f`, no callers) is at statement `j` of
block `bi`, the VCode state `vs` at the start of that statement's segment; every tracked value
(`A bi j`) is held (low bits) by its resolved vreg `gn x`; the restriction of the frame to the
tracked values is DFG-consistent; memory and world are related by `MR`.

* `stmt_step`: a CLIF statement step is matched by the straight-line run of its segment (or,
  for an explicit trap, reaches the halting instruction);
* `term_step`: returns, traps, and branches (jump arguments as the VCode parallel copy, edge
  blocks for `brif`/`br_table` arguments);
* `term_step_try`: a `try_call` (its normal return: the call and the pending jump, two CLIF
  steps) is matched by the terminator's code up to the `tryCall`, the normal-return edge block
  and its `jump`;
* `entry_step`: the entry `Args`;
* `sim_run`: whole runs (`Clif.runLoop`), by strong induction on the fuel.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- Every tracked value is held by its resolved vreg. -/
def Held (gn : Nat → Nat) (A : List Clif.ValueId) (ρ : Nat → CV) (fr : Clif.Frame) : Prop :=
  ∀ x ∈ A, ∃ v, fr.regs x = some v ∧ VHolds v (ρ (gn x))

/-- The simulation relation. -/
def Match (f : Clif.Function) (ctx : Ctx) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
    (A : Nat → Nat → List Clif.ValueId) (MR : MemRelT) (slots : List (Clif.SlotId × Nat))
    (s : Clif.State) (vs : VState CV Arm.ArmState) : Prop :=
  s.callers = [] ∧ s.frame.func = f ∧ s.frame.slots = slots ∧ MR slots s.mem vs.w ∧
  ∃ B j, f.blocks[vs.b]? = some B ∧ s.frame.term = B.term ∧ j ≤ B.body.length ∧
    s.frame.body = B.body.drop j ∧ vs.k = pos f R bl vs.b j ∧
    Held gn (A vs.b j) vs.ρ s.frame ∧ DFGCons ctx (restrict s.frame (A vs.b j))

/-- From `vs`, the VCode run reaches an instruction that halts with trap code `c`. -/
def VTrapFrom (vc : VCode) (sem : Sem) (vs : VState CV Arm.ArmState) (c : Clif.TrapCode) : Prop :=
  ∃ b k ρ w vb i ops outs w', Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.operands = .ok ops ∧
    sem i (vuses ops ρ) w = some (outs, w', .halt) ∧ trapCode? i = some c

/-- From `vs`, the VCode run executes `rets us` with use values `vals`, final world `w`. -/
def VRetFrom (vc : VCode) (sem : Sem) (vs : VState CV Arm.ArmState) (us : List (Reg × Reg))
    (vals : List CV) (w : Arm.ArmState) : Prop :=
  ∃ b k ρ w₁ vb ops outs, Star (VStep vc sem) (.run vs) (.run ⟨b, k, ρ, w₁⟩) ∧
    vc.blocks[b]? = some vb ∧ vb.insts[k]? = some (.rets us) ∧
    (MInst.rets us).operands = .ok ops ∧ vals = vuses ops ρ ∧
    sem (.rets us) vals w₁ = some (outs, w, .ret)

theorem VTrapFrom.prefix {vc : VCode} {sem : Sem} {vs vs' : VState CV Arm.ArmState}
    {c : Clif.TrapCode} (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : VTrapFrom vc sem vs' c) :
    VTrapFrom vc sem vs c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, h1⟩ := h'
  exact ⟨b, k, ρ, w, vb, i, ops, outs, w', h.trans hs, h1⟩

theorem VRetFrom.prefix {vc : VCode} {sem : Sem} {vs vs' : VState CV Arm.ArmState}
    {us : List (Reg × Reg)} {vals : List CV} {w : Arm.ArmState}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : VRetFrom vc sem vs' us vals w) :
    VRetFrom vc sem vs us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, h1⟩ := h'
  exact ⟨b, k, ρ, w₁, vb, ops, outs, h.trans hs, h1⟩

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow}

/-! ## Segments -/

theorem seg_eq {bi j : Nat} {B : Clif.Block} {L : BLow} {stm : Clif.Stmt} {sl : SLow}
    (hB : f.blocks[bi]? = some B) (hL : bl[bi]? = some L) (hs : B.body[j]? = some stm)
    (hsl : L.sl[j]? = some sl) :
    seg f R bl bi j = (sl.st'.emitted.toList ++ extraOf stm.results sl.rss).map (·.mapRegs R) := by
  simp [seg, hB, hL, hs, hsl]

theorem tseg_eq {bi : Nat} {L : BLow} (hL : bl[bi]? = some L) :
    tseg R bl bi = (fixTry L.tl L.tst'.emitted.toList).map (·.mapRegs R) := by
  simp [tseg, hL]

theorem tseg_eq_none {bi : Nat} {L : BLow} (hL : bl[bi]? = some L) (h : L.tl = none) :
    tseg R bl bi = L.tst'.emitted.toList.map (·.mapRegs R) := by
  simp [tseg, hL, h, fixTry]

theorem pos_succ (bi j : Nat) : pos f R bl bi (j + 1) = pos f R bl bi j + (seg f R bl bi j).length := by
  simp [pos, List.range_succ, Nat.add_assoc]

theorem seg_at {vb : VBlock} {bi : Nat} {B : Clif.Block}
    (hcode : vb.insts.toList = pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten ++
      tseg R bl bi) (htne : tseg R bl bi ≠ []) {j : Nat} (hj : j < B.body.length) :
    SegAt vb (pos f R bl bi j) (seg f R bl bi j) ∧ pos f R bl bi (j + 1) < vb.insts.size := by
  have hsplit := flatten_range_split (seg f R bl bi) hj
  rw [hsplit] at hcode
  have hlen : (pre f R bi ++ ((List.range j).map (seg f R bl bi)).flatten).length = pos f R bl bi j := by
    simp [pos, List.length_flatten, List.map_map, Function.comp_def]
  constructor
  · have : vb.insts.toList = (pre f R bi ++ ((List.range j).map (seg f R bl bi)).flatten) ++
        seg f R bl bi j ++ ((((List.range (B.body.length - (j + 1))).map
          fun i => seg f R bl bi (j + 1 + i))).flatten ++ tseg R bl bi) := by
      rw [hcode]; simp [List.append_assoc]
    have h := segAt_of_toList this
    rwa [hlen] at h
  · have hsz : vb.insts.size = vb.insts.toList.length := by simp
    rw [hsz, hcode, pos_succ, ← hlen]
    have : 0 < (tseg R bl bi).length := List.length_pos_iff.mpr htne
    simp only [List.length_append]
    omega

theorem tseg_at {vb : VBlock} {bi : Nat} {B : Clif.Block}
    (hcode : vb.insts.toList = pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten ++
      tseg R bl bi) :
    SegAt vb (pos f R bl bi B.body.length) (tseg R bl bi) ∧
      vb.insts.size = pos f R bl bi B.body.length + (tseg R bl bi).length := by
  have hlen : (pre f R bi ++ ((List.range B.body.length).map (seg f R bl bi)).flatten).length =
      pos f R bl bi B.body.length := by
    simp [pos, List.length_flatten, List.map_map, Function.comp_def]
  constructor
  · have h := segAt_of_toList (L₂ := []) (by rw [hcode, List.append_nil])
    rwa [hlen] at h
  · have hsz : vb.insts.size = vb.insts.toList.length := by simp
    rw [hsz, hcode, List.length_append, hlen]

theorem extraOf_nil {results : List Nat} {rss : List (List Reg)}
    (h : ∀ (k : Nat) rs, rss[k]? = some rs → ∃ out cls, rs = [.vreg out cls]) :
    extraOf results rss = [] := by
  unfold extraOf
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

end

/-! ## Hypotheses of the driver simulation -/

/-- Everything the simulation assumes: the structure of the VCode (`LowerShape`), the SSA
certificate, the driver-level semantics facts, M4's contracts, extern-only calls, and a
successful `VCode.cfg`. -/
structure DriverHyp (f : Clif.Function) (vc : VCode) (ctx : Ctx) (st0 : LState) (R : Reg → Reg)
    (gn : Nat → Nat) (bl : List BLow) (A : Nat → Nat → List Clif.ValueId) (sem : Sem)
    (MR : MemRelT) (env : Clif.Env) (p : Clif.Program) : Prop where
  shape : LowerShape f vc ctx st0 R gn bl
  cert : Cert f ctx st0 gn bl A
  dsem : DriverSem sem
  /-- M4: `lower` on statements (`instCalls_of_rules`) -/
  insts : InstCalls f sem MR env p
  /-- M4 (open): terminator calls -/
  terms : TermCalls sem MR
  ext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  /-- the signature of an indirect call is among `f`'s indirect-call signatures, with register
  arguments (`E2E.InSubset.indSigs`) -/
  indSig : ∀ B ∈ f.blocks, ∀ st ∈ B.body, IndSigOk f (indSigs f) st.inst
  /-- `f` is in subset E (`E2E.InSubset.subsetE`; new since `call_indirect`/`func_addr` compile) -/
  subE : Compile.functionE f = true
  /-- a `try_call` calls an extern with at most 8 (register) parameters
  (`E2E.InSubset.tryRegArgs`) -/
  tryRegArgs : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
    ∀ e, f.extern? fn = some e → e.sig.params.length ≤ 8
  /-- `br_table` indices have at most 32 bits (`lowerCheck`'s `brIdxOk`) -/
  brIdx : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term
  /-- no tail calls (`return_call` is outside clif-subset-v2 E) -/
  noTail : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args
  /-- M4: `lower_branch` on `try_call`s (`tryCalls_of_rules`) -/
  tries : TryCalls f sem MR env p
  /-- a `try_call` calls an extern (`E2E.InSubset.tryExterns`) -/
  tryExt : ∀ B ∈ f.blocks, ∀ fn args et, B.term = .tryCall fn args et →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  /-- M4: `lower_branch` on `try_call_indirect`s (`tryIndCalls_of_rules`) -/
  tryInd : TryIndCalls sem MR env p (indSigs f)
  /-- the signature of a `try_call_indirect` is among `f`'s indirect-call signatures, with
  register arguments (`E2E.InSubset.indSigs`) -/
  tryIndSig : ∀ B ∈ f.blocks, ∀ c args et s, B.term = .tryCallIndirect c args et →
    f.sigDecls.lookup et.sig = some s → s ∈ indSigs f ∧ s.params.length ≤ 8
  cfg : ∃ ss ps, vc.cfg = .ok (ss, ps)
  /-- the signature's parameter locations and byte sizes compute, one per parameter
  (`lowerCheck`'s `entryOkB`) -/
  entryLocs : (locsOf f.sig).length = f.sig.params.length ∧ ∃ bytes, sigParamBytes f.sig = .ok bytes

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

theorem DriverHyp.blow (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) {bi : Nat}
    {B : Clif.Block} (hB : f.blocks[bi]? = some B) : ∃ L, bl[bi]? = some L := by
  have hlt : bi < f.blocks.length := (List.getElem?_eq_some_iff.mp hB).1
  exact ⟨bl[bi]'(by rw [H.shape.len]; exact hlt), List.getElem?_eq_getElem _⟩

/-- **Statement step.** -/
theorem stmt_step (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
        Match f ctx R gn bl A MR slots s' vs') ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vc sem ⟨b, k, ρ, w⟩ c) := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := hm
  simp only at hk hheld hcons hB hmem
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
  have hok := H.insts ctx (L.start + j) info stm.inst sl.st sl.rss sl.st' tr
    H.shape.ctxInv ⟨B, hBmem, stm, hstmmem, rfl⟩ H.subE hinfo hclif (H.indSig B hBmem stm hstmmem) hemp
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
  have hrun' := hok.run fr' s.mem ρ₀ w (by simp [fr', restrict, hfunc, H.shape.ctxInv.func])
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
  have hcodeseg := seg_at hcode htne hjlt
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
        have hextra : extraOf stm.results sl.rss = [] := by
          rcases hrh with h0 | ⟨hl, hh⟩
          · rw [h0]; rfl
          · apply extraOf_nil
            intro k rs hk
            have : k < vals.length := by
              have := (List.getElem?_eq_some_iff.mp hk).1; omega
            obtain ⟨out, cls, he, -, -⟩ := hh k rs vals[k] hk (List.getElem?_eq_getElem this)
            exact ⟨out, cls, he⟩
        have hseg : seg f R bl b j = sl.st'.emitted.toList.map (·.mapRegs R) := by
          rw [seg_eq hB hL hstm hsl, hextra, List.append_nil]
        obtain ⟨hsegat, hlt⟩ := hcodeseg
        rw [hseg] at hsegat
        rw [pos_succ, hseg] at hlt
        have hstar := seqRun_fall_star hvb hsegat (by simpa using hlt) hsr'
        rw [List.length_map] at hstar
        refine ⟨_, hstar, hcall, hfunc, hslots, by simpa [fr', restrict, hslots] using hmr,
          B, j + 1, hB, hterm, hjlt, hrest, ?_, ?_, ?_⟩
        · simp [pos_succ, hseg]
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
              obtain ⟨tys, hrt, hrty, -⟩ := H.shape.ctxInv.resTys _ info stm.inst hinfo hclif
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
      rw [seg_eq hB hL hstm hsl, List.map_append] at hsegat
      obtain ⟨hstar, -, hi, hops, hsem, -, -⟩ := seqRun_stop_star hvb hsegat.append_left hsr'
      exact ⟨b, _, ρ₁', w₁, vb, _, _, outs, w₂, hstar, hvb, hi, hops, hsem,
        by rw [trapCode?_mapRegs]; exact htc⟩

theorem abiTerm_cases (f : Clif.Function) (t : Clif.Terminator) :
    abiTerm f t = t ∨ ∃ xs, t = .ret xs ∧ abiTerm f t = .ret (xs ++ sretRet f) := by
  cases t with
  | ret xs => exact .inr ⟨xs, rfl, rfl⟩
  | _ => exact .inl rfl

theorem termCall_abiTerm (f : Clif.Function) (t : Clif.Terminator) (ti : Nat)
    (targets : List Label) : termCall (abiTerm f t) ti targets = termCall t ti targets := by
  cases t <;> rfl

theorem termArgs_abiTerm {f : Clif.Function} {t : Clif.Terminator} {y : Clif.ValueId}
    (h : y ∈ termArgs t) : y ∈ termArgs (abiTerm f t) := by
  rcases abiTerm_cases f t with e | ⟨xs, rfl, e⟩
  · rw [e]; exact h
  · rw [e]; simp only [termArgs] at h ⊢; exact List.mem_append_left _ h

theorem brIdxTyped_abiTerm {ctx : Ctx} {f : Clif.Function} {t : Clif.Terminator}
    (h : BrIdxTyped ctx t) : BrIdxTyped ctx (abiTerm f t) := by
  rcases abiTerm_cases f t with e | ⟨xs, rfl, e⟩
  · rw [e]; exact h
  · rw [e]; intro x d tbl h'; cases h'

theorem targetsLen_abiTerm {f : Clif.Function} {t : Clif.Terminator} {targets : List Label}
    (h : TargetsLen t targets) : TargetsLen (abiTerm f t) targets := by
  rcases abiTerm_cases f t with e | ⟨xs, rfl, e⟩
  · rw [e]; exact h
  · rw [e]; intro x d tbl h'; cases h'

theorem args_termArgs {t : Clif.Terminator} {bc : Clif.BlockCall} (h : bc ∈ dests t) :
    ∀ a ∈ bc.args, a ∈ termArgs t := by
  intro a ha
  cases t with
  | jump bc' => simp [dests] at h; subst h; exact ha
  | brif c t e =>
    simp [dests] at h
    rcases h with rfl | rfl <;> simp [termArgs, ha]
  | brTable x d tbl =>
    simp [dests] at h
    rcases h with rfl | h
    · simp [termArgs, ha]
    · simp only [termArgs, List.mem_cons, List.mem_append, List.mem_flatMap]
      exact .inr ⟨bc, h, ha⟩
  | _ => simp [dests] at h

theorem edgeEnv_eq {V : Type} {vc : VCode} {b s : Nat} {vb sb : VBlock}
    (hvb : vc.blocks[b]? = some vb) (hsb : vc.blocks[s]? = some sb) {ps xs : List Nat}
    (hba : vb.branchArgs = (xs.map fun n => Reg.vreg n .int).toArray)
    (hpa : sb.params = (ps.map fun n => Reg.vreg n .int).toArray) (hl : ps.length = xs.length)
    (ρ : Nat → V) : edgeEnv vc b s ρ = some (parCopyEnv ρ ps xs) := by
  unfold edgeEnv
  have hv : ∀ ns : List Nat, List.mapM (vregNum ∘ fun n => Reg.vreg n RegClass.int) ns = .ok ns := by
    intro ns
    induction ns with
    | nil => rfl
    | cons n ns ih => simp [List.mapM_cons, vregNum, ih] <;> rfl
  simp [hvb, hsb, hba, hpa, hl, Except.toOption, hv]

/-- **Entering a successor block.** The CLIF frame after `enterBlock` and the VCode file after
the parallel copy of the (renamed) arguments into the parameters match at the successor. -/
theorem enter_match (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b : Nat} {B : Clif.Block} (hB : f.blocks[b]? = some B)
    (hcall : s.callers = []) (hfunc : s.frame.func = f) (hslots : s.frame.slots = slots)
    {ρ : Nat → CV} (hheld : Held gn (A b B.body.length) ρ s.frame)
    (hcons : DFGCons ctx (restrict s.frame (A b B.body.length)))
    {bc : Clif.BlockCall} (hbc : bc.block ∈ edgeIds B.term) {tl : Nat}
    (htl : blockIdx? f bc.block = some tl)
    {fr2 : Clif.Frame} (hent : Clif.enterBlock s.frame bc = .ok fr2) {ρ₂ : Nat → CV}
    (hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x)) {xs : List Nat}
    (hxl : xs.length = bc.args.length)
    (hxv : ∀ (m : Nat) a v x, bc.args[m]? = some a → s.frame.regs a = some v → xs[m]? = some x →
      VHolds v (ρ₂ x))
    {w₂ : Arm.ArmState} (hmr : MR slots s.mem w₂) :
    ∃ TB, f.blocks[tl]? = some TB ∧ bc.args.length = TB.params.length ∧ tl ≠ 0 ∧
      Match f ctx R gn bl A MR slots { s with frame := fr2 }
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
  have hpos : pos f R bl tl 0 = 0 := by
    simp [pos, pre]
    cases tl with
    | zero => exact absurd rfl hne0
    | succ n => rfl
  refine ⟨TB, hTB, hlen, hne0, hcall, hfunc, hslots, hmr, TB, 0, hTB, rfl, Nat.zero_le _,
    by simp, hpos.symm, ?_, ?_⟩
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

theorem mem_edgeIds_of_dests {t : Clif.Terminator} {bc : Clif.BlockCall} (h : bc ∈ dests t) :
    bc.block ∈ edgeIds t := by
  cases t <;> first | (simp [dests] at h; done) | exact List.mem_map_of_mem h

/-- **Entering a branch's successor** (`enter_match` with the branch arguments' vregs). -/
theorem enter_match_br (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b : Nat} {B : Clif.Block} (hB : f.blocks[b]? = some B)
    (hcall : s.callers = []) (hfunc : s.frame.func = f) (hslots : s.frame.slots = slots)
    {ρ : Nat → CV} (hheld : Held gn (A b B.body.length) ρ s.frame)
    (hcons : DFGCons ctx (restrict s.frame (A b B.body.length)))
    {bc : Clif.BlockCall} (hbc : bc ∈ dests B.term) {tl : Nat} (htl : blockIdx? f bc.block = some tl)
    {fr2 : Clif.Frame} (hent : Clif.enterBlock s.frame bc = .ok fr2) {ρ₂ : Nat → CV}
    (hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x)) {w₂ : Arm.ArmState}
    (hmr : MR slots s.mem w₂) :
    ∃ TB, f.blocks[tl]? = some TB ∧ bc.args.length = TB.params.length ∧ tl ≠ 0 ∧
      Match f ctx R gn bl A MR slots { s with frame := fr2 }
        ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) (bc.args.map gn), w₂⟩ := by
  refine enter_match H hB hcall hfunc hslots hheld hcons (mem_edgeIds_of_dests hbc) htl hent hρ₂
    (by simp) (fun m a v x ha hv hx => ?_) hmr
  have haA : a ∈ A b B.body.length :=
    (H.cert.term b B _ hB (H.blow hB).choose_spec).1 _
      (termArgs_abiTerm (args_termArgs hbc _ (List.mem_of_getElem? ha)))
  obtain ⟨v', hv', hh⟩ := hheld a haA
  rw [hv] at hv'; cases hv'
  simp only [List.getElem?_map, ha, Option.map_some, Option.some.injEq] at hx
  subst hx
  rw [hρ₂ a haA]; exact hh

/-- DFG consistency only depends on the frame's function, slots and registers. -/
theorem dfgCons_congr {fr fr' : Clif.Frame} (hf : fr'.func = fr.func) (hs : fr'.slots = fr.slots)
    (hr : fr'.regs = fr.regs) (h : DFGCons ctx fr) : DFGCons ctx fr' := by
  refine ⟨fun x j info cl v hd hi hc hp hv => ?_, fun x t v ht hv => h.2 x t v ht (hr ▸ hv)⟩
  obtain ⟨vals, hev, hlk⟩ := h.1 x j info cl v hd hi hc hp (hr ▸ hv)
  exact ⟨vals, fun cm => by rw [evalInst_congr hf hs cm cl (fun y _ => by rw [hr])]; exact hev cm,
    hlk⟩

/-! ## CLIF terminator steps -/

theorem stepTerm_branch {env : Clif.Env} {p : Clif.Program} {s s' : Clif.State}
    {t : Clif.Terminator} (hb : dests t ≠ [])
    (h : Clif.stepTerm env p s t = .next s') :
    ∃ j bc fr2, branchIdx s.frame t = .ok j ∧ (dests t)[j]? = some bc ∧
      Clif.enterBlock s.frame bc = .ok fr2 ∧ s' = { s with frame := fr2 } := by
  cases t with
  | jump bc =>
    simp only [Clif.stepTerm] at h
    cases he : Clif.enterBlock s.frame bc with
    | ok fr2 =>
      rw [he] at h; simp only [Clif.StepResult.ofRes, Clif.StepResult.next.injEq] at h
      exact ⟨0, bc, fr2, rfl, rfl, he, h.symm⟩
    | _ => rw [he] at h; cases h
  | brif c t e =>
    simp only [Clif.stepTerm] at h
    cases hc : s.frame.get c with
    | ok cv =>
      rw [hc] at h
      simp only [Clif.StepResult.ofRes] at h
      cases he : Clif.enterBlock s.frame (if Clif.Sem.truthy cv.bits then t else e) with
      | ok fr2 =>
        rw [he] at h; simp only [Clif.StepResult.next.injEq] at h
        refine ⟨if Clif.Sem.truthy cv.bits then 0 else 1, _, fr2, ?_, ?_, he, h.symm⟩
        · simp [branchIdx, hc, Clif.Res.bind]
        · split <;> simp [dests]
      | _ => rw [he] at h; cases h
    | _ => rw [hc] at h; cases h
  | brTable x d tbl =>
    simp only [Clif.stepTerm] at h
    cases hc : s.frame.get x with
    | ok xv =>
      rw [hc] at h
      simp only [Clif.StepResult.ofRes] at h
      cases he : Clif.enterBlock s.frame (tbl[xv.toNat]?.getD d) with
      | ok fr2 =>
        rw [he] at h; simp only [Clif.StepResult.next.injEq] at h
        refine ⟨if xv.toNat < tbl.length then xv.toNat + 1 else 0, _, fr2, ?_, ?_, he, h.symm⟩
        · simp [branchIdx, hc, Clif.Res.bind]
        · split
          · rename_i hlt; simp [dests, List.getElem?_eq_getElem hlt]
          · rename_i hge; simp [dests, List.getElem?_eq_none (Nat.le_of_not_lt hge)]
      | _ => rw [he] at h; cases h
    | _ => rw [hc] at h; cases h
  | _ => simp [dests] at hb

theorem stepTerm_branch_ne {env : Clif.Env} {p : Clif.Program} {s : Clif.State}
    {t : Clif.Terminator} (hb : dests t ≠ []) :
    (∀ vals cm, Clif.stepTerm env p s t ≠ .done vals cm) ∧
    (∀ c, Clif.stepTerm env p s t ≠ .trapped c) := by
  constructor
  · intro vals cm h
    cases t with
    | jump bc =>
      simp only [Clif.stepTerm] at h
      cases he : Clif.enterBlock s.frame bc <;> rw [he] at h <;> cases h
    | brif c t e =>
      simp only [Clif.stepTerm] at h
      cases hc : s.frame.get c with
      | ok cv =>
        rw [hc] at h; simp only [Clif.StepResult.ofRes] at h
        cases he : Clif.enterBlock s.frame (if Clif.Sem.truthy cv.bits then t else e) <;>
          rw [he] at h <;> cases h
      | _ => rw [hc] at h; cases h
    | brTable x d tbl =>
      simp only [Clif.stepTerm] at h
      cases hc : s.frame.get x with
      | ok xv =>
        rw [hc] at h; simp only [Clif.StepResult.ofRes] at h
        cases he : Clif.enterBlock s.frame (tbl[xv.toNat]?.getD d) <;> rw [he] at h <;> cases h
      | _ => rw [hc] at h; cases h
    | _ => simp [dests] at hb
  · intro c h
    cases t with
    | jump bc =>
      simp only [Clif.stepTerm] at h
      cases he : Clif.enterBlock s.frame bc with
      | trap c' => exact enterBlock_ne_trap he
      | _ => rw [he] at h; cases h
    | brif c t e =>
      simp only [Clif.stepTerm] at h
      cases hc : s.frame.get c with
      | ok cv =>
        rw [hc] at h; simp only [Clif.StepResult.ofRes] at h
        cases he : Clif.enterBlock s.frame (if Clif.Sem.truthy cv.bits then t else e) with
        | trap c' => exact enterBlock_ne_trap he
        | _ => rw [he] at h; cases h
      | trap c' => simp [Clif.Frame.get, Clif.Res.ofOption] at hc; split at hc <;> cases hc
      | stuck => rw [hc] at h; cases h
    | brTable x d tbl =>
      simp only [Clif.stepTerm] at h
      cases hc : s.frame.get x with
      | ok xv =>
        rw [hc] at h; simp only [Clif.StepResult.ofRes] at h
        cases he : Clif.enterBlock s.frame (tbl[xv.toNat]?.getD d) with
        | trap c' => exact enterBlock_ne_trap he
        | _ => rw [he] at h; cases h
      | trap c' => simp [Clif.Frame.get, Clif.Res.ofOption] at hc; split at hc <;> cases hc
      | stuck => rw [hc] at h; cases h
    | _ => simp [dests] at hb

theorem stepTerm_ret {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {xs : List Clif.ValueId}
    (hcall : s.callers = []) :
    (∀ s', Clif.stepTerm env p s (.ret xs) ≠ .next s') ∧
    (∀ c, Clif.stepTerm env p s (.ret xs) ≠ .trapped c) ∧
    (∀ vals cm, Clif.stepTerm env p s (.ret xs) = .done vals cm →
      s.frame.getMany xs = .ok vals ∧ cm = s.mem.free (s.frame.slots.map (·.2))) := by
  have key : ∀ r, Clif.stepTerm env p s (.ret xs) = r →
      (∃ vals, s.frame.getMany xs = .ok vals ∧ r = .done vals (s.mem.free (s.frame.slots.map (·.2)))) ∨
      ∃ m, r = .stuck m := by
    intro r h
    subst h
    simp only [Clif.stepTerm]
    cases hg : s.frame.getMany xs with
    | ok vals =>
      simp only [Clif.StepResult.ofRes, Clif.returnValues, hcall]
      rcases checkTys_cases s!"return values of %{s.frame.func.name}" vals
        (Clif.AbiParam.tys s.frame.func.sig.returns) with ⟨hc, -⟩ | ⟨m, hc⟩
      · rw [hc]; exact .inl ⟨vals, rfl, rfl⟩
      · rw [hc]; exact .inr ⟨m, rfl⟩
    | trap c => exact absurd hg getMany_ne_trap
    | stuck m => exact .inr ⟨m, rfl⟩
  refine ⟨fun s' h => ?_, fun c h => ?_, fun vals cm h => ?_⟩
  · rcases key _ h with ⟨_, _, e⟩ | ⟨_, e⟩ <;> cases e
  · rcases key _ h with ⟨_, _, e⟩ | ⟨_, e⟩ <;> cases e
  · rcases key _ h with ⟨vals', hg, e⟩ | ⟨_, e⟩
    · cases e; exact ⟨hg, rfl⟩
    · cases e

/-- A frame defining every `y ∈ ys` extends a successful `getMany xs` to `xs ++ ys`. -/
theorem getMany_append_of {fr : Clif.Frame} {ys : List Clif.ValueId}
    (hy : ∀ y ∈ ys, ∃ v, fr.regs y = some v) :
    ∀ {xs : List Clif.ValueId} {vals : List Clif.Val}, fr.getMany xs = .ok vals →
      ∃ vs, fr.getMany (xs ++ ys) = .ok (vals ++ vs) := by
  intro xs
  induction xs with
  | nil =>
    intro vals h
    simp only [Clif.Frame.getMany, Clif.Res.ok.injEq] at h
    subst h
    induction ys with
    | nil => exact ⟨[], rfl⟩
    | cons y ys ih =>
      obtain ⟨v, hv⟩ := hy y (by simp)
      obtain ⟨vs, hvs⟩ := ih (fun z hz => hy z (by simp [hz]))
      refine ⟨v :: vs, ?_⟩
      simp only [List.nil_append] at hvs ⊢
      simp only [Clif.Frame.getMany, Clif.Frame.get, hv, Clif.Res.ofOption_some, Clif.Res.ok_bind,
        hvs, Clif.Res.pure_eq]
  | cons x xs ih =>
    intro vals h
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
        obtain ⟨vs, hvs⟩ := ih hr
        refine ⟨vs, ?_⟩
        simp only [List.cons_append, Clif.Frame.getMany, Clif.Frame.get, hx, Clif.Res.ofOption_some,
          Clif.Res.ok_bind, hvs, Clif.Res.pure_eq]
      | trap => rw [hr] at h; cases h
      | stuck => rw [hr] at h; cases h

/-- **Terminator step**: returns, traps, branches (a `try_call`: `term_step_try`). -/
theorem term_step (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
        Match f ctx R gn bl A MR slots s' vs') ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w', VRetFrom vc sem ⟨b, k, ρ, w⟩ us outs w' ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MR slots s.mem w' ∧ cm = s.mem.free (slots.map (·.2))) ∧
    (∀ c, Clif.step env p s = .trapped c → VTrapFrom vc sem ⟨b, k, ρ, w⟩ c) := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := hm
  simp only at hk hheld hcons hB hmem
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
  have hok := H.terms f ctx (L.start + B.body.length) (abiTerm f B.term) L.data L.targets out
    L.tst L.tst' tr H.shape.ctxInv (brIdxTyped_abiTerm (H.brIdx B (List.mem_of_getElem? hB)))
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
    (by simp [fr', restrict, hfunc, termCtx, H.shape.ctxInv.func]) hvh (dfgCons_termCtx hcons _ _)
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
  obtain ⟨hsegat, hsize⟩ := tseg_at hcode
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
      ∃ vs', Star (VStep vc sem) (.run ⟨b, pos f R bl b B.body.length, ρ, w⟩) (.run vs') ∧
        Match f ctx R gn bl A MR slots s' vs' := by
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
    have hK : pos f R bl b B.body.length + k' + 1 = vb.insts.size := by
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
      obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match_br H hB hcall hfunc hslots hheld hcons hbcmem
        htl hent hρ₂ hmr'
      obtain ⟨Lt, hLt⟩ := H.blow hTB
      obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
      simp only [hne0, ite_false] at hpt
      have henv := edgeEnv_eq (V := CV) hvb hvbt (xs := bc.args.map gn) (ps := TB.params.map (·.1))
        (by rw [hbargs]; simp [List.map_map, Function.comp_def, H.shape.ren.vreg])
        (by rw [hpt]; simp [List.map_map, Function.comp_def]) (by simp; omega)
        (vdefUpd (ops.map (rnOp gn)) outs ρ₁')
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
      obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match_br H hB hcall hfunc hslots hheld hcons hbcmem
        htl hent hρ₂ hmr'
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
        have henv2 := edgeEnv_eq (V := CV) heb hvbt (xs := bc.args.map gn) (ps := TB.params.map (·.1))
          (by rw [hebba]; simp [List.map_map, Function.comp_def, H.shape.ren.vreg])
          (by rw [hpt]; simp [List.map_map, Function.comp_def]) (by simp; omega)
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
    obtain ⟨vs, hg'⟩ := getMany_append_of (fr := fr') (ys := sretRet f) (fun y hy => by
      have hyA : y ∈ A b B.body.length := hargsTA y (by simp [termArgs, hy])
      obtain ⟨v, hv, -⟩ := hheld y hyA
      exact ⟨v, by rw [restrict_regs_of_mem hyA]; exact hv⟩) hg0
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
    refine ⟨_, vuses ops ρ₁, w₂, ⟨b, _, ρ₁', w₁, vb, ops.map (rnOp gn), outs, hstar, hvb, hi, hops,
      hvu.symm, by rw [← hvu]; exact hsem⟩, ?_, ?_, hall.prefix_append,
      by simpa [fr', restrict, hslots] using hmr, by rw [hcm, hslots]⟩
    · simp only [List.map_map, List.length_map]
      exact hus
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

/-! ## `try_call` (the normal return) -/

/-- The state after the call of a `try_call` (results bound, the jump to the normal return
pending). -/
def tryNext (s : Clif.State) (regs : Clif.Regs) (bc : Clif.BlockCall) (cm : Clif.Mem) :
    Clif.State :=
  { s with frame := { s.frame with regs, body := [], term := .jump bc }, mem := cm }

/-- The CLIF value `Clif.tryNormal` passes for a normal-return argument (`base`: the first of
the fresh values the call's results are bound to). -/
def tryArgVal (base : Nat) : Clif.TryArg → Clif.ValueId
  | .val v => v
  | .ret i => base + i
  | .exn _ => 0

theorem mapM_tryArg {base : Nat} {F : Clif.TryArg → Clif.Res Clif.ValueId}
    (hF : ∀ a y, F a = .ok y → y = tryArgVal base a) :
    ∀ {l : List Clif.TryArg} {xs : List Clif.ValueId}, l.mapM F = .ok xs →
      xs = l.map (tryArgVal base) := by
  intro l
  induction l with
  | nil =>
    intro xs h
    simp only [List.mapM_nil, Clif.Res.pure_eq, Clif.Res.ok.injEq] at h
    subst h; rfl
  | cons a l ih =>
    intro xs h
    simp only [List.mapM_cons] at h
    cases ha : F a with
    | ok y =>
      rw [ha, Clif.Res.ok_bind] at h
      cases hl : l.mapM F with
      | ok ys =>
        rw [hl, Clif.Res.ok_bind, Clif.Res.pure_eq, Clif.Res.ok.injEq] at h
        subst h
        rw [hF a y ha, ih hl]; rfl
      | trap c => rw [hl, Clif.Res.trap_bind] at h; cases h
      | stuck m => rw [hl, Clif.Res.stuck_bind] at h; cases h
    | trap c => rw [ha, Clif.Res.trap_bind] at h; cases h
    | stuck m => rw [ha, Clif.Res.stuck_bind] at h; cases h

theorem tryNormal_ok {et : Clif.ExnTable} {base : Nat} {bc : Clif.BlockCall}
    (h : Clif.tryNormal et base = .ok bc) :
    bc = { block := et.normal.block, args := et.normal.args.map (tryArgVal base) } := by
  unfold Clif.tryNormal at h
  rw [res_bind_eq_ok] at h
  obtain ⟨xs, hxs, h⟩ := h
  simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq] at h
  subst h
  rw [mapM_tryArg (fun a y ha => by
    cases a <;> simp only [Clif.Res.pure_eq, Clif.Res.ok.injEq, tryArgVal] at ha ⊢ <;>
      first | exact ha.symm | cases ha) hxs]

theorem stepTry_spec {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {fn : Clif.FnRef}
    {args : List Clif.ValueId} {et : Clif.ExnTable}
    (hext : ∀ e, s.frame.func.extern? fn = some e → p.func? e.name = none) :
    (∀ vals cm, Clif.stepTerm env p s (.tryCall fn args et) ≠ .done vals cm) ∧
    ∀ s', Clif.stepTerm env p s (.tryCall fn args et) = .next s' →
      ∃ ext bc rvals cm' regs', s.frame.func.extern? fn = some ext ∧
        Clif.tryNormal et s.frame.func.freshValue = .ok bc ∧
        instOutcome env p s.frame s.mem (.call fn args) = .ok (rvals, cm') ∧
        s.frame.regs.setMany ((List.range ext.sig.returns.length).map
          (s.frame.func.freshValue + ·)) rvals = some regs' ∧
        s' = tryNext s regs' bc cm' := by
  have key : ∀ r, Clif.stepTerm env p s (.tryCall fn args et) = r →
      (∃ m, r = .stuck m) ∨ (∃ c, r = .trapped c) ∨
      ∃ ext bc rvals cm' regs', s.frame.func.extern? fn = some ext ∧
        Clif.tryNormal et s.frame.func.freshValue = .ok bc ∧
        instOutcome env p s.frame s.mem (.call fn args) = .ok (rvals, cm') ∧
        s.frame.regs.setMany ((List.range ext.sig.returns.length).map
          (s.frame.func.freshValue + ·)) rvals = some regs' ∧
        r = .next (tryNext s regs' bc cm') := by
    intro r hr
    subst hr
    simp only [Clif.stepTerm, Clif.stepTryCall]
    cases hx : s.frame.func.extern? fn with
    | none => left; simp [hx]
    | some ext =>
      cases hsd : s.frame.func.sigDecls.lookup et.sig with
      | none => left; simp [hx, hsd]
      | some sig =>
        cases hck : (Clif.AbiParam.tys sig.params == Clif.AbiParam.tys ext.sig.params &&
            Clif.AbiParam.tys sig.returns == Clif.AbiParam.tys ext.sig.returns)
        · left
          simp only [hx, hsd, hck, Clif.Res.check, Clif.Res.ofOption_some, Clif.Res.ok_bind,
            Bool.false_eq_true, ite_false, Clif.Res.stuck_bind, Clif.StepResult.ofRes_stuck]
          exact ⟨_, rfl⟩
        · cases htn : Clif.tryNormal et s.frame.func.freshValue with
          | trap c =>
            right; left
            simp only [hx, hsd, hck, htn, Clif.Res.check, Clif.Res.ofOption_some, Clif.Res.ok_bind,
              ite_true, Clif.Res.trap_bind, Clif.StepResult.ofRes_trap]
            exact ⟨_, rfl⟩
          | stuck m =>
            left
            simp only [hx, hsd, hck, htn, Clif.Res.check, Clif.Res.ofOption_some, Clif.Res.ok_bind,
              ite_true, Clif.Res.stuck_bind, Clif.StepResult.ofRes_stuck]
            exact ⟨_, rfl⟩
          | ok bc =>
            simp only [hx, hsd, hck, htn, Clif.Res.check, Clif.Res.ofOption_some, Clif.Res.ok_bind,
              ite_true, Clif.Res.pure_eq, Clif.StepResult.ofRes_ok]
            rw [stepCall_eq env p { s with frame := { s.frame with body := [], term := .jump bc } }
              [] _ fn args hext]
            have hio : instOutcome env p { s.frame with body := [], term := .jump bc } s.mem
                (.call fn args) = instOutcome env p s.frame s.mem (.call fn args) :=
              instOutcome_congr (fr := s.frame) (fr' := { s.frame with body := [], term := .jump bc })
                rfl rfl env p s.mem (.call fn args) (fun _ _ => rfl)
            simp only [hio]
            cases hO : instOutcome env p s.frame s.mem (.call fn args) with
            | trap c => right; left; exact ⟨c, rfl⟩
            | stuck m => left; exact ⟨m, rfl⟩
            | ok r =>
              obtain ⟨rvals, cm'⟩ := r
              simp only [Clif.StepResult.ofRes, Clif.continueWith]
              cases hset : s.frame.regs.setMany ((List.range ext.sig.returns.length).map
                  (s.frame.func.freshValue + ·)) rvals with
              | none => left; simp only [hset]; exact ⟨_, rfl⟩
              | some regs' =>
                right; right
                simp only [hset]
                exact ⟨ext, bc, rvals, cm', regs', rfl, rfl, rfl, hset, rfl⟩
  refine ⟨fun vals cm h => ?_, fun s' h => ?_⟩
  · rcases key _ h with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, _, _, _, _, _, _, _, _, e⟩ <;> cases e
  · rcases key _ h with ⟨_, e⟩ | ⟨_, e⟩ | ⟨ext, bc, rvals, cm', regs', h1, h2, h3, h4, e⟩
    · cases e
    · cases e
    · cases e; exact ⟨ext, bc, rvals, cm', regs', h1, h2, h3, h4, rfl⟩

theorem stepTryInd_spec {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {callee : Nat}
    {args : List Clif.ValueId} {et : Clif.ExnTable}
    (hnp : ∀ cv, s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ vals cm, Clif.stepTerm env p s (.tryCallIndirect callee args et) ≠ .done vals cm) ∧
    ∀ s', Clif.stepTerm env p s (.tryCallIndirect callee args et) = .next s' →
      ∃ declared bc rvals cm' regs', s.frame.func.sigDecls.lookup et.sig = some declared ∧
        Clif.tryNormal et s.frame.func.freshValue = .ok bc ∧
        instOutcome env p s.frame s.mem (.callIndirect et.sig callee args) = .ok (rvals, cm') ∧
        s.frame.regs.setMany ((List.range declared.returns.length).map
          (s.frame.func.freshValue + ·)) rvals = some regs' ∧
        s' = tryNext s regs' bc cm' := by
  have key : ∀ r, Clif.stepTerm env p s (.tryCallIndirect callee args et) = r →
      (∃ m, r = .stuck m) ∨ (∃ c, r = .trapped c) ∨
      ∃ declared bc rvals cm' regs', s.frame.func.sigDecls.lookup et.sig = some declared ∧
        Clif.tryNormal et s.frame.func.freshValue = .ok bc ∧
        instOutcome env p s.frame s.mem (.callIndirect et.sig callee args) = .ok (rvals, cm') ∧
        s.frame.regs.setMany ((List.range declared.returns.length).map
          (s.frame.func.freshValue + ·)) rvals = some regs' ∧
        r = .next (tryNext s regs' bc cm') := by
    intro r hr
    subst hr
    simp only [Clif.stepTerm, Clif.stepTryCallIndirect]
    cases hsd : s.frame.func.sigDecls.lookup et.sig with
    | none => left; simp [hsd]
    | some sig =>
      cases htn : Clif.tryNormal et s.frame.func.freshValue with
      | trap c =>
        right; left
        simp only [hsd, htn, Clif.Res.ofOption_some, Clif.Res.ok_bind, Clif.Res.trap_bind,
          Clif.StepResult.ofRes_trap]
        exact ⟨_, rfl⟩
      | stuck m =>
        left
        simp only [hsd, htn, Clif.Res.ofOption_some, Clif.Res.ok_bind, Clif.Res.stuck_bind,
          Clif.StepResult.ofRes_stuck]
        exact ⟨_, rfl⟩
      | ok bc =>
        simp only [hsd, htn, Clif.Res.ofOption_some, Clif.Res.ok_bind, Clif.Res.pure_eq,
          Clif.StepResult.ofRes_ok]
        rw [stepCallIndirect_eq env p { s with frame := { s.frame with body := [], term := .jump bc } }
          [] _ et.sig callee args (fun cv hcv g hg => hnp cv hcv g hg)]
        have hio : instOutcome env p { s.frame with body := [], term := .jump bc } s.mem
            (.callIndirect et.sig callee args) =
            instOutcome env p s.frame s.mem (.callIndirect et.sig callee args) :=
          instOutcome_congr (fr := s.frame) (fr' := { s.frame with body := [], term := .jump bc })
            rfl rfl env p s.mem _ (fun _ _ => rfl)
        simp only [hio]
        cases hO : instOutcome env p s.frame s.mem (.callIndirect et.sig callee args) with
        | trap c => right; left; exact ⟨c, rfl⟩
        | stuck m => left; exact ⟨m, rfl⟩
        | ok r =>
          obtain ⟨rvals, cm'⟩ := r
          simp only [Clif.StepResult.ofRes, Clif.continueWith]
          cases hset : s.frame.regs.setMany ((List.range sig.returns.length).map
              (s.frame.func.freshValue + ·)) rvals with
          | none => left; simp only [hset]; exact ⟨_, rfl⟩
          | some regs' =>
            right; right
            simp only [hset]
            exact ⟨sig, bc, rvals, cm', regs', rfl, rfl, rfl, hset, rfl⟩
  refine ⟨fun vals cm h => ?_, fun s' h => ?_⟩
  · rcases key _ h with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, _, _, _, _, _, _, _, _, e⟩ <;> cases e
  · rcases key _ h with ⟨_, e⟩ | ⟨_, e⟩ | ⟨d, bc, rvals, cm', regs', h1, h2, h3, h4, e⟩
    · cases e
    · cases e
    · cases e; exact ⟨d, bc, rvals, cm', regs', h1, h2, h3, h4, rfl⟩

theorem vdefs_tryCall (c : CallInfo) (info : TryInfo) :
    vdefs (.tryCall c info) = vdefs (.call c) := by
  simp only [vdefs, operands_tryCall_call]

theorem vuseNums_tryCall (c : CallInfo) (info : TryInfo) :
    vuseNums (.tryCall c info) = vuseNums (.call c) := by
  simp only [vuseNums, operands_tryCall_call]

/-- The vreg number of a normal-return argument on the edge block (`normArgReg`; `bb`: the first
return vreg). -/
def tryArgNum (gn : Nat → Nat) (bb : Nat) : Clif.TryArg → Nat
  | .val v => gn v
  | .ret i => bb + i
  | .exn _ => 0

/-- The exception table's values are operands of a `try_call`/`try_call_indirect`. -/
theorem etVals_termArgs {t : Clif.Terminator} {et : Clif.ExnTable} (h : IsTryWith t et) :
    ∀ y ∈ et.vals, y ∈ termArgs t := by
  intro y hy
  rcases h with ⟨fn, args, rfl⟩ | ⟨c, args, rfl⟩ <;> simp [termArgs, hy]

/-- **`try_call`/`try_call_indirect` step** (the normal return). The CLIF call of the extern
(its results bound to fresh values, the jump to the normal return pending) and the jump are
matched by the terminator's code, ending in the `tryCall` (which continues at the normal-return
edge block), and the edge block's `jump` (the parallel copy of the renamed arguments). `hind`:
an indirect callee is no function of `p`. -/
theorem term_step_try (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith s.frame.term et)
    (hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ vals cm, Clif.step env p s ≠ .done vals cm) ∧
    ∀ s', Clif.step env p s = .next s' →
      (∀ c, Clif.step env p s' ≠ .trapped c) ∧ (∀ vals cm, Clif.step env p s' ≠ .done vals cm) ∧
      ∀ s'', Clif.step env p s' = .next s'' →
        ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
          Match f ctx R gn bl A MR slots s'' vs' := by
  obtain ⟨hcall, hfunc, hslots, hmem, B, j, hB, hterm, hj, hbd, hk, hheld, hcons⟩ := hm
  simp only at hk hheld hcons hB hmem
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
        fun s' hs => ?_, H.tries ctx (L.start + B.body.length) fn args et L.data T.sig T.items
          L.targets T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv
          (H.tryRegArgs B hBmem fn args et hBT) hdata' hexn
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
        H.tryInd f ctx (L.start + B.body.length) callee args et L.data T.sig T.items L.targets
          T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv hdata' hexn hsin h8
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
        eb.branchArgs = (et.normal.args.map (normArgReg R T.regs.1)).toArray ∧
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
    (by simp [fr', restrict, hfunc, tryCtx, termCtx, H.shape.ctxInv.func]) hvh
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
  obtain ⟨hsegat, hsize⟩ := tseg_at hcode
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
  have hK : pos f R bl b B.body.length + pre.length + 1 = vb.insts.size := by
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
        have hiN : ii < (sigRets T.sig).length :=
          Nat.lt_of_lt_of_le hii (returns_le_sigRets _)
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
  obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match H hB (s := tryNext s regs' bc cm') hcall hfunc
    hslots hheld' hcons' hbcb htl' hent hρ₂ hxl hxv hmr'
  obtain ⟨Lt, hLt⟩ := H.blow hTB
  obtain ⟨vbt, hvbt, -, -, -, -, -, -, -, -, hpt, -, -⟩ := H.shape.blk tl TB Lt hTB hLt
  simp only [hne0, ite_false] at hpt
  have hebba' : eb.branchArgs = (xs.map fun n => Reg.vreg n .int).toArray := by
    rw [hebba]
    refine congrArg List.toArray ?_
    simp only [xs, List.map_map]
    apply List.map_congr_left
    intro a ha
    cases a with
    | val v => simp [normArgReg, tryArgNum, H.shape.ren.vreg]
    | ret ii =>
      have hii : ii < T.sig.returns.length := hargsOk _ ha
      have hiN : ii < (sigRets T.sig).length := Nat.lt_of_lt_of_le hii (returns_le_sigRets _)
      have hg : gn (L.tst.nextVreg + ii) = L.tst.nextVreg + ii := H.shape.temps _ (by omega)
      simp [normArgReg, tryArgNum, hregsEq, hiN, H.shape.ren.vreg, hg]
    | exn _ => exact absurd (hargsOk _ ha) id
  have henv2 := edgeEnv_eq (V := CV) heb hvbt (xs := xs) (ps := TB.params.map (·.1)) hebba'
    (by rw [hpt]; simp [List.map_map, Function.comp_def]) (by simp only [List.length_map]; omega)
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

/-! ## Entry -/

theorem writeV_nodup {V : Type} {ρ : Nat → V} :
    ∀ {dv : List (Operand × V)}, (dv.map (·.1.vreg)).Nodup →
      ∀ (m : Nat) o x, dv[m]? = some (o, x) → writeV ρ dv o.vreg = x := by
  intro dv
  induction dv generalizing ρ with
  | nil => intro _ m o x h; simp at h
  | cons p dv ih =>
    intro hnd m o x h
    simp only [List.map_cons, List.nodup_cons] at hnd
    change writeV (upd ρ p.1.vreg p.2) dv o.vreg = x
    cases m with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [writeV_other (dv := dv) (fun q hq e => hnd.1 (List.mem_map.mpr ⟨q, hq, e⟩))]
      simp [upd]
    | succ m =>
      simp only [List.getElem?_cons_succ] at h
      exact ih hnd.2 m o x h

theorem vdefUpd_argOps {ns : List (Nat × Reg)} {outs : List CV} {ρ : Nat → CV}
    (hnd : (ns.map (·.1)).Nodup) (hl : outs.length = ns.length) (m : Nat) {q : Nat × Reg} {x : CV}
    (hq : ns[m]? = some q) (hx : outs[m]? = some x) :
    vdefUpd (argOps ns).toArray outs ρ q.1 = x := by
  have hdef : (argOps ns).filter Operand.isDef = argOps ns := by
    rw [List.filter_eq_self]
    intro o ho
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
    rw [← hq']; rfl
  have hearly : ((argOps ns).zip outs).filter (·.1.isEarly) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp (List.of_mem_zip hp).1
    rw [← hq']; simp [Operand.isEarly]
  have hlate : ((argOps ns).zip outs).filter (·.1.isLate) = (argOps ns).zip outs := by
    rw [List.filter_eq_self]
    intro p hp
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp (List.of_mem_zip hp).1
    rw [← hq']; rfl
  simp only [vdefUpd, List.toList_toArray, hdef, hearly, hlate]
  have hmem : ((argOps ns).zip outs)[m]? = some (⟨q.1, .int, .def, .late, .fixed q.2⟩, x) := by
    simp [argOps, List.getElem?_zip_eq_some, hq, hx]
  have := writeV_nodup (ρ := writeV ρ []) (dv := (argOps ns).zip outs) ?_ m _ x hmem
  · simpa using this
  · have : ((argOps ns).zip outs).map (·.1.vreg) = ns.map (·.1) := by
      rw [show (fun x : Operand × CV => x.fst.vreg) = Operand.vreg ∘ Prod.fst from rfl,
        ← List.map_map, List.map_fst_zip (by simp [argOps]; omega)]
      simp [argOps]
    rw [this]; exact hnd

/-- The arguments in the body-entry world `w` as the entry code reads them (the driver's entry
premise): a register-passed parameter in its argument register (low bits), a stack-passed one
in the caller's outgoing area at `fp + 16 + off` (above the saved fp/lr pair), whose bytes avoid
the frame addresses `F`. -/
def ArgsAtEntry (F : BitVec 64 → Prop) (sig : Clif.Signature) (args : List Clif.Val)
    (w : Arm.ArmState) : Prop :=
  ∀ loc v, (loc, v) ∈ (locsOf sig).zip args → match loc with
    | .reg r => VHolds v (regVal w r)
    | .stack off =>
      Avoids F v.ty.bytes (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) ∧
      (Arm.read_mem_bytes v.ty.bytes (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)))
        w).setWidth v.ty.width = v.bits

theorem loadVal_congr {F : BitVec 64 → Prop} {s t : Arm.ArmState} (op : LoadOp) {a : BitVec 64}
    (h : ∀ x, ¬ F x → s.mem x = t.mem x) (hav : Avoids F op.bytes a) :
    loadVal op a s = loadVal op a t := by
  have hr : Arm.read_mem_bytes op.bytes a s = Arm.read_mem_bytes op.bytes a t :=
    read_mem_bytes_congr _ a (fun k hk => h _ (hav k hk))
  simp only [loadVal, hr]

theorem loadOpOfBytes_facts {b : Nat} (hb : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) :
    (loadOpOfBytes b).bytes = b ∧ loadOpOfBytes b ≠ .fpuLoad128 ∧ loadSigned (loadOpOfBytes b) = false := by
  rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide, rfl⟩

/-- One entry load: the parameter's vreg gets the loaded value. -/
theorem seqRun_load_cons {sem : Sem} {op : LoadOp} {x : Nat} {k : Int} {fl : Clif.MemFlags}
    {ρ : Nat → CV} {w w1 : Arm.ArmState} {o : CV}
    (h : sem (.load op (.vreg x .int) (.fpOffset k) fl) [] w = some ([o], w1, .next))
    (ms : List MInst) :
    seqRun sem (.load op (.vreg x .int) (.fpOffset k) fl :: ms) ρ w =
      (seqRun sem ms (upd ρ x o) w1).map SeqEnd.succ := by
  have hops : (MInst.load op (.vreg x .int) (.fpOffset k) fl).operands =
      .ok #[⟨x, .int, .def, .late, .reg⟩] := rfl
  have hv : vuses #[(⟨x, .int, .def, .late, .reg⟩ : Operand)] ρ = [] := rfl
  simp only [seqRun, hops, hv, h]
  simp [Operand.isDef, Operand.isEarly, Operand.isLate, vdefUpd, writeV]

/-- **The entry loads** of the stack-passed parameters: each reads its parameter from the
caller's outgoing area (unchanged by the earlier loads: its bytes avoid `F`), the world changes
only outside the memory relation's view. -/
theorem entryLoads_run {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR) :
    ∀ (E : List (((Nat × Clif.Ty) × ArgLoc) × Nat)) (ρ : Nat → CV) (sl : List (Clif.SlotId × Nat))
      (cm : Clif.Mem) (w : Arm.ArmState),
      (∀ q ∈ E, R (.vreg q.1.1.1 .int) = .vreg q.1.1.1 .int) →
      (E.map (·.1.1.1)).Nodup →
      (∀ q ∈ E, ∀ off, q.1.2 = .stack off → (q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8) ∧
        Avoids F q.2 (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int)))) →
      MR sl cm w →
      ∃ ρ' w', seqRun sem (E.filterMap (entryLoadOf R)) ρ w = some (.fall ρ' w') ∧
        MR sl cm w' ∧
        (∀ y, y ∉ E.map (·.1.1.1) → ρ' y = ρ y) ∧
        (∀ q ∈ E, ∀ p, q.1.2 = .reg p → ρ' q.1.1.1 = ρ q.1.1.1) ∧
        (∀ q ∈ E, ∀ off, q.1.2 = .stack off →
          ρ' q.1.1.1 = ofX (loadVal (loadOpOfBytes q.2)
            (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w))
  | [], ρ, _, _, w, _, _, _, hmr => ⟨ρ, w, rfl, hmr, fun _ _ => rfl, by simp, by simp⟩
  | q :: E, ρ, sl, cm, w, hR, hnd, hst, hmr => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨⟨⟨x, ty⟩, loc⟩, b⟩ := q
    simp only at hnd
    have hnx : ∀ q ∈ E, q.1.1.1 ≠ x := fun q hq e => hnd.1 (List.mem_map.mpr ⟨q, hq, e⟩)
    cases loc with
    | reg p =>
      obtain ⟨ρ', w', hrun, hmr', hfr, hreg, hstk⟩ := entryLoads_run hMem hMR E ρ sl cm w
        (fun q hq => hR q (List.mem_cons_of_mem _ hq)) hnd.2
        (fun q hq => hst q (List.mem_cons_of_mem _ hq)) hmr
      refine ⟨ρ', w', by simpa [entryLoadOf] using hrun, hmr', fun y hy => hfr y (fun h => hy
        (List.mem_cons_of_mem _ h)), fun q hq p' hp => ?_, fun q hq off ho => ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact hfr x hnd.1
        · exact hreg q hq p' hp
      · rcases List.mem_cons.mp hq with rfl | hq
        · cases ho
        · exact hstk q hq off ho
    | stack off =>
      obtain ⟨hb, hav⟩ := hst ((x, ty), .stack off, b) (List.mem_cons_self ..) off rfl
      obtain ⟨hob, hop, -⟩ := loadOpOfBytes_facts hb
      have ha : amodeAddr sb (.fpOffset (16 + (off : Int))) (loadOpOfBytes b).bytes [] w =
          some (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) := rfl
      obtain ⟨w1, hw1, hsw⟩ := hMem.1 (loadOpOfBytes b) x (.fpOffset (16 + (off : Int))) trustedFlags
        [] w _ hop ha (by rw [hob]; exact hav)
      have hmr1 : MR sl cm w1 := hMR _ _ _ _ (SameWorld.nf hsw) hmr
      have h29 : Arm.r (.GPR 29#5) w1 = Arm.r (.GPR 29#5) w :=
        hsw.1 (.GPR 29#5) (by simp [Masked])
      obtain ⟨ρ', w', hrun, hmr', hfr, hreg, hstk⟩ := entryLoads_run hMem hMR E
        (upd ρ x (ofX (loadVal (loadOpOfBytes b) (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w)))
        sl cm w1 (fun q hq => hR q (List.mem_cons_of_mem _ hq)) hnd.2
        (fun q hq o ho => by rw [h29]; exact hst q (List.mem_cons_of_mem _ hq) o ho) hmr1
      have hRx : R (.vreg x .int) = .vreg x .int := hR _ (List.mem_cons_self ..)
      refine ⟨ρ', w', ?_, hmr', fun y hy => ?_, fun q hq p hp => ?_, fun q hq o ho => ?_⟩
      · simp only [List.filterMap_cons, entryLoadOf, hRx]
        rw [seqRun_load_cons hw1, hrun]; rfl
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
          rw [hfr x hnd.1]
          simp [upd]
        · rw [hstk q hq o ho, h29]
          obtain ⟨hb', hav'⟩ := hst q (List.mem_cons_of_mem _ hq) o ho
          rw [loadVal_congr (F := F) _ (fun a ha => hsw.2.1 a ha)
            (by rw [(loadOpOfBytes_facts hb').1]; exact hav')]

/-- The register pairs of the entry's `Args` (parameter id, argument register). -/
def entryNs (E : List (((Nat × Clif.Ty) × ArgLoc) × Nat)) : List (Nat × Reg) :=
  E.filterMap fun q => match q.1.2 with
    | .reg p => some (q.1.1.1, p)
    | .stack _ => none

theorem entryRegs_eq : ∀ (E : List (((Nat × Clif.Ty) × ArgLoc) × Nat)),
    (∀ q ∈ E, R (.vreg q.1.1.1 .int) = .vreg q.1.1.1 .int) →
    E.filterMap (entryRegOf R) = argPairs (entryNs E)
  | [], _ => rfl
  | ((⟨x, ty⟩, .reg p), b) :: E, h => by
    simp only [List.filterMap_cons, entryRegOf, entryNs, argPairs, List.map_cons]
    rw [h _ (List.mem_cons_self ..)]
    congr 1
    exact entryRegs_eq E (fun q hq => h q (List.mem_cons_of_mem _ hq))
  | ((⟨x, ty⟩, .stack o), b) :: E, h => by
    simp only [List.filterMap_cons, entryRegOf, entryNs]
    exact entryRegs_eq E (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem entryNs_sublist : ∀ (E : List (((Nat × Clif.Ty) × ArgLoc) × Nat)),
    (entryNs E).map (·.1) <+ E.map (·.1.1.1)
  | [] => by simp [entryNs]
  | ((⟨x, ty⟩, .reg p), b) :: E => by
    simpa [entryNs] using (entryNs_sublist E).cons₂ x
  | ((⟨x, ty⟩, .stack o), b) :: E => by
    simpa [entryNs] using (entryNs_sublist E).cons x

theorem mem_entryNs {E : List (((Nat × Clif.Ty) × ArgLoc) × Nat)} {q : ((Nat × Clif.Ty) × ArgLoc) × Nat}
    {p : Reg} (hq : q ∈ E) (hp : q.1.2 = .reg p) : (q.1.1.1, p) ∈ entryNs E := by
  unfold entryNs
  exact List.mem_filterMap.mpr ⟨q, hq, by rw [hp]⟩

/-- **Entry**: the entry block's `Args` defines the register-passed parameters from their
argument registers, then the loads the stack-passed ones from the caller's outgoing area. -/
theorem entry_step (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) :
    ∃ k ρ₁ w₁, Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, k, ρ₁, w₁⟩) ∧
      Match f ctx R gn bl A MR slots cs ⟨0, k, ρ₁, w₁⟩ := by
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
  set E := entryParams f B0 with hEdef
  have hE : E = (B0.params.zip (locsOf f.sig)).zip bytes := by
    rw [hEdef]; simp only [entryParams, hb]
  have hEids : E.map (·.1.1.1) = B0.params.map (·.1) := by
    rw [hE]
    have h1 : (B0.params.zip (locsOf f.sig)).length = B0.params.length := by
      simp [List.length_zip]; omega
    rw [show (fun q : ((Nat × Clif.Ty) × ArgLoc) × Nat => q.1.1.1) = (fun q => q.1) ∘ (fun q => q.1)
      from rfl, ← List.map_map, List.map_fst_zip (by omega), ← List.map_map,
      List.map_fst_zip (by omega)]
  have hRid : ∀ q ∈ E, R (.vreg q.1.1.1 .int) = .vreg q.1.1.1 .int := by
    intro q hq
    have hq1 : q.1.1 ∈ B0.params := by
      rw [hE] at hq
      exact (List.of_mem_zip (List.of_mem_zip hq).1).1
    simp [H.shape.ren.vreg, H.shape.params B0 hB0mem q.1.1 hq1]
  -- parameter `m`: its entry, argument and location
  have hEget : ∀ m q, B0.params[m]? = some q → ∃ loc b, (locsOf f.sig)[m]? = some loc ∧
      bytes[m]? = some b ∧ E[m]? = some ((q, loc), b) := by
    intro m q hq
    have hm : m < B0.params.length := (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨loc, hloc⟩ : ∃ loc, (locsOf f.sig)[m]? = some loc :=
      ⟨(locsOf f.sig)[m]'(by omega), by simp⟩
    obtain ⟨b, hbb⟩ : ∃ b, bytes[m]? = some b := ⟨bytes[m]'(by omega), by simp⟩
    exact ⟨loc, b, hloc, hbb, by rw [hE]; simp [List.getElem?_zip_eq_some, hq, hloc, hbb]⟩
  have hbyte : ∀ m v b, args[m]? = some v → bytes[m]? = some b → b = v.ty.bytes := by
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
  have hEmem : ∀ q ∈ E, ∃ m v, E[m]? = some q ∧ args[m]? = some v := by
    intro q hq
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hq
    have hmE : m < E.length := (List.getElem?_eq_some_iff.mp hm).1
    have : E.length ≤ args.length := by rw [hE]; simp [List.length_zip]; omega
    exact ⟨m, args[m]'(by omega), hm, by simp⟩
  have hentry : ∀ q ∈ E, ∀ m v, E[m]? = some q → args[m]? = some v →
      (q.1.2, v) ∈ (locsOf f.sig).zip args ∧ q.2 = v.ty.bytes ∧ bytes[m]? = some q.2 := by
    intro q hq m v hm hv
    rw [hE] at hm
    simp only [List.getElem?_zip_eq_some] at hm
    obtain ⟨⟨-, hl⟩, hbb⟩ := hm
    exact ⟨List.mem_iff_getElem?.mpr ⟨m, by simp [List.getElem?_zip_eq_some, hl, hv]⟩,
      hbyte m v _ hv hbb, hbb⟩
  -- the code before the statements
  set ns := entryNs E with hnsdef
  have hpre : pre f R 0 = .args (argPairs ns) :: E.filterMap (entryLoadOf R) := by
    simp only [pre, hB0, entryRegs, entryLoads, ← hEdef]
    rw [entryRegs_eq E hRid]
  have hnsnd : (ns.map (·.1)).Nodup := by
    have := (entryNs_sublist E).nodup (by rw [hEids]; exact hnd)
    exact this
  -- `Args`
  have hops := operands_args ns
  have hvu : vuses (argOps ns).toArray ρ₀ = [] := by
    simp only [vuses, List.toList_toArray, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro o ho
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
    rw [← hq']; simp [Operand.isUse]
  have hsem := H.dsem.args (argPairs ns) w₀
  rw [← hvu] at hsem
  have hlen : ((argPairs ns).map fun d => regVal w₀ d.2).length =
      ((argOps ns).toArray.toList.filter Operand.isDef).length := by
    have : (argOps ns).filter Operand.isDef = argOps ns := by
      rw [List.filter_eq_self]
      intro o ho
      obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
      rw [← hq']; rfl
    rw [List.toList_toArray, this]
    simp only [List.length_map, argPairs, argOps]
  set ρ₁ := vdefUpd (argOps ns).toArray ((argPairs ns).map fun d => regVal w₀ d.2) ρ₀ with hρ₁
  -- the loads
  obtain ⟨ρ₂, w₂, hrun, hmr₂, -, hreg, hstk⟩ := entryLoads_run hMem hMR E ρ₁ slots cs.mem w₀ hRid
    (by rw [hEids]; exact hnd)
    (fun q hq off ho => by
      obtain ⟨m, v, hm, hv⟩ := hEmem q hq
      obtain ⟨hmem, hqb, hqbm⟩ := hentry q hq m v hm hv
      have h := hargs _ _ hmem
      rw [ho] at h
      obtain ⟨hav, -⟩ := h
      rw [hqb]
      exact ⟨hqb ▸ sigArgs_bytes hb _ (List.mem_of_getElem? hqbm), hav⟩) hmr
  have hseq : seqRun sem (E.filterMap (entryLoadOf R)) ρ₁ w₀ = some (.fall ρ₂ w₂) := hrun
  have hsz : (pre f R 0).length < vb.insts.size := by
    have h1 : vb.insts.size = vb.insts.toList.length := by simp
    have h2 : 0 < (tseg R bl 0).length := List.length_pos_iff.mpr htne
    rw [h1, hcode]; simp only [List.length_append]; omega
  have hseg0 : SegAt vb 0 (pre f R 0) := by
    intro k hk
    rw [Nat.zero_add, ← Array.getElem?_toList, hcode, List.append_assoc,
      List.getElem?_append_left hk, List.getElem?_eq_getElem hk]
  have hvb0 : vb.insts[0]? = some (.args (argPairs ns)) := by
    have := hseg0.head (ms := E.filterMap (entryLoadOf R)) (by rw [← hpre]; exact hseg0)
    exact this
  have hstep : VStep vc sem (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, 1, ρ₁, w₀⟩) :=
    VStep.step hvb hvb0 hops hsem hlen (VNext.next (by rw [hpre] at hsz; simp at hsz; omega))
  have hseg1 : SegAt vb 1 (E.filterMap (entryLoadOf R)) := by
    have := (show SegAt vb 0 (.args (argPairs ns) :: E.filterMap (entryLoadOf R)) by
      rw [← hpre]; exact hseg0).tail
    simpa using this
  have hstar := seqRun_fall_star hvb hseg1 (by rw [hpre] at hsz; simp at hsz; omega) hseq
  refine ⟨1 + (E.filterMap (entryLoadOf R)).length, ρ₂, w₂, .step hstep hstar, hcall, hfunc,
    hslots, hmr₂, B0, 0, hB0, hterm, Nat.zero_le _, by simp [hbody],
    by simp [pos, hpre]; omega, ?_, ?_⟩
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
      have hns : (B0.params[m].1, r) ∈ ns := mem_entryNs hqE rfl
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hns
      rw [vdefUpd_argOps hnsnd (by simp [argPairs]) i hi (x := regVal w₀ r) (by simp [argPairs, hi])]
      exact h
    | stack off =>
      have h1 := hstk _ hqE off rfl
      simp only at h1
      rw [← hxq, h1, hb']
      obtain ⟨-, hrd⟩ := h
      have hbs : args[m].ty.bytes = 1 ∨ args[m].ty.bytes = 2 ∨ args[m].ty.bytes = 4 ∨
          args[m].ty.bytes = 8 := hb' ▸ sigArgs_bytes hb _ (List.mem_of_getElem? hbb)
      obtain ⟨hob, -, hsg⟩ := loadOpOfBytes_facts hbs
      have hw : args[m].ty.width ≤ 64 := by
        rcases hbs with h | h | h | h <;> cases ht : args[m].ty <;>
          simp_all [Clif.Ty.bytes, Clif.Ty.width]
      simp only [VHolds, ofX, loadVal, hsg, Bool.false_eq_true, ↓reduceIte]
      rw [hob, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ hw]
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

/-! ## Whole runs -/

end

/-- `s'` is reachable from `s` by CLIF steps that continue. -/
inductive Reach (env : Clif.Env) (p : Clif.Program) : Clif.State → Clif.State → Prop
  | refl (s : Clif.State) : Reach env p s s
  | step {s s' s'' : Clif.State} : Clif.step env p s = .next s' → Reach env p s' s'' →
      Reach env p s s''

theorem Reach.snoc {env : Clif.Env} {p : Clif.Program} {s s' s'' : Clif.State}
    (h : Reach env p s s') (h' : Clif.step env p s' = .next s'') : Reach env p s s'' := by
  induction h with
  | refl => exact .step h' (.refl _)
  | step h1 _ ih => exact .step h1 (ih h')

theorem stmt_not_done {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {st : Clif.Stmt}
    {rest : List Clif.Stmt} (h : s.frame.body = st :: rest)
    (hext : ∀ fn args, st.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
      p.func? e.name = none)
    (hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat)
    {vals : List Clif.Val} {cm : Clif.Mem} :
    Clif.step env p s ≠ .done vals cm := by
  rw [step_stmt env p s st rest h hext hind]
  cases instOutcome env p s.frame s.mem st.inst with
  | ok r =>
    simp only [Clif.StepResult.ofRes, Clif.continueWith]
    split <;> simp
  | _ => simp [Clif.StepResult.ofRes]

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- What a VCode run from `vs` does when the CLIF run from the matching state ends. -/
def RunOk (vc : VCode) (sem : Sem) (MR : MemRelT) (slots : List (Clif.SlotId × Nat))
    (vs : VState CV Arm.ArmState) : Clif.Outcome → Prop
  | .returned vals cm => ∃ us outs w cm0, VRetFrom vc sem vs us outs w ∧
      us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
      PrefixHold vals outs ∧ MR slots cm0 w ∧ cm = cm0.free (slots.map (·.2))
  | .trapped c => VTrapFrom vc sem vs c
  | .stuck _ | .outOfFuel => True

theorem RunOk.prefix {vs vs' : VState CV Arm.ArmState} {o : Clif.Outcome}
    (h : Star (VStep vc sem) (.run vs) (.run vs')) (h' : RunOk vc sem MR slots vs' o) :
    RunOk vc sem MR slots vs o := by
  cases o with
  | returned vals cm =>
    obtain ⟨us, outs, w, cm0, hr, h1⟩ := h'
    exact ⟨us, outs, w, cm0, VRetFrom.prefix h hr, h1⟩
  | trapped c => exact VTrapFrom.prefix h h'
  | _ => trivial

/-- The run premises of the driver simulation from the CLIF state `cs` of `f` (the trap and
indirect-call clauses of `E2E.TrapsExplicit`): statements trap only explicitly; the step of one
of `f`'s `try_call`/`try_call_indirect` terminators does not trap (the callee returns
normally); an indirect call of `f` (a `call_indirect` statement or a `try_call_indirect`) calls
no function of `p` (its callee is an extern). -/
structure RunPrem (env : Clif.Env) (p : Clif.Program) (f : Clif.Function) (cs : Clif.State) :
    Prop where
  stmt : ∀ s c st rest, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = st :: rest → explicitTrapInst st.inst = true
  tryCall : ∀ s c fn args et, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCall fn args et → ∀ B ∈ f.blocks,
      B.term ≠ .tryCall fn args et
  tryCallInd : ∀ s c callee args et, Reach env p cs s → Clif.step env p s = .trapped c →
    s.frame.body = [] → s.frame.term = .tryCallIndirect callee args et → ∀ B ∈ f.blocks,
      B.term ≠ .tryCallIndirect callee args et
  indirect : ∀ s st rest sig callee args, Reach env p cs s → s.frame.body = st :: rest →
    st.inst = .callIndirect sig callee args → (∃ B ∈ f.blocks, st ∈ B.body) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat
  tryIndirect : ∀ s callee args et, Reach env p cs s → s.frame.body = [] →
    s.frame.term = .tryCallIndirect callee args et →
    (∃ B ∈ f.blocks, B.term = .tryCallIndirect callee args et) → ∀ cv,
    s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat

/-- **Whole runs**: from matching states, every CLIF outcome is realised by the VCode run
(under the run premises `RunPrem`). -/
theorem sim_run (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) {cs : Clif.State}
    (hP : RunPrem env p f cs) :
    ∀ fuel s (vs : VState CV Arm.ArmState), Reach env p cs s →
      Match f ctx R gn bl A MR slots s vs → RunOk vc sem MR slots vs (Clif.runLoop env p fuel s) := by
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
        obtain ⟨T1, T2, T3⟩ := term_step H hm hbody hty
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨vs', hstar, hm'⟩ := T1 s' hs
          exact RunOk.prefix hstar (ih n (by omega) s' vs' (hr.snoc hs) hm')
        | done vals cm =>
          obtain ⟨us, outs, w', hret, h1, h2, h3, h4, h5⟩ := T2 vals cm hs
          exact ⟨us, outs, w', s.mem, hret, h1, h2, h3, h4, h5⟩
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
        obtain ⟨Tnd, Tnx⟩ := term_step_try H hm hbody hT hind
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨N1, N2, N3⟩ := Tnx s' hs
          cases n with
          | zero => trivial
          | succ m =>
            show RunOk vc sem MR slots _ (Clif.runLoop env p (m + 1) s')
            rw [Clif.runLoop_succ]
            cases hs' : Clif.step env p s' with
            | next s'' =>
              obtain ⟨vs', hstar, hm'⟩ := N3 s'' hs'
              exact RunOk.prefix hstar (ih m (by omega) s'' vs' ((hr.snoc hs).snoc hs') hm')
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
      obtain ⟨S1, S2⟩ := stmt_step H hm hbody hind
      cases hs : Clif.step env p s with
      | next s' =>
        obtain ⟨vs', hstar, hm'⟩ := S1 s' hs
        exact RunOk.prefix hstar (ih n (by omega) s' vs' (hr.snoc hs) hm')
      | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
      | trapped c => exact S2 c hs (hP.stmt s c st rest hr hs hbody)
      | stuck => trivial

/-- **The driver lemma (CLIF → VCode).** A CLIF run of `f` from an entry state (parameters
bound to `args`, which the VCode world holds in x0..) is realised by the VCode run from the
entry: returns through `rets` with the returned values held, and memory related; explicit traps
reach an instruction halting with the same code (a `try_call`: its normal return). -/
theorem driver_correct (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefines F sb syms sem) (hMR : MRStable F MR)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hP : RunPrem env p f cs) (fuel : Nat) :
    RunOk vc sem MR slots ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoop env p fuel cs) := by
  obtain ⟨k, ρ₁, w₁, hstar, hm⟩ := entry_step H hMem hMR hB0 hcall hfunc hslots hbody hterm hregs
    hty hsig hmr hargs (ρ₀ := ρ₀)
  exact RunOk.prefix hstar (sim_run H hP fuel cs _ (.refl _) hm)

end

end Backend.Proof.Driver
