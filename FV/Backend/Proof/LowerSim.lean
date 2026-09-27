import FV.Backend.Proof.LowerLemmas

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
* `entry_step`: the entry `Args`;
* `sim_run`: whole runs (`Clif.runLoop`).
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
    tseg R bl bi = L.tst'.emitted.toList.map (·.mapRegs R) := by
  simp [tseg, hL]

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
  insts : InstCalls sem MR env p
  /-- M4 (open): terminator calls -/
  terms : TermCalls sem MR
  ext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  /-- no tail calls (`return_call` is outside clif-subset-v2 E) -/
  noTail : ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args
  cfg : ∃ ss ps, vc.cfg = .ok (ss, ps)

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
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest) :
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
  have hok := H.insts f ctx (L.start + j) info stm.inst sl.st sl.rss sl.st' tr
    H.shape.ctxInv hinfo hclif hemp
    (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0) hrun
  rw [hres] at hok
  obtain ⟨hargs, hresults, hnodup, hnext, hnoclob⟩ := H.cert.stmt b B L j stm sl hB hL hstm hsl
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  have hstmmem : stm ∈ B.body := List.mem_of_getElem? hstm
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
  have hstep := step_stmt env p s stm rest hbody fun fn args hi e he =>
    H.ext B hBmem stm hstmmem fn args hi e (by rw [← hfunc]; exact he)
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
    {bc : Clif.BlockCall} (hbc : bc ∈ dests B.term) {tl : Nat} (htl : blockIdx? f bc.block = some tl)
    {fr2 : Clif.Frame} (hent : Clif.enterBlock s.frame bc = .ok fr2) {ρ₂ : Nat → CV}
    (hρ₂ : ∀ x ∈ A b B.body.length, ρ₂ (gn x) = ρ (gn x)) {w₂ : Arm.ArmState}
    (hmr : MR slots s.mem w₂) :
    ∃ TB, f.blocks[tl]? = some TB ∧ bc.args.length = TB.params.length ∧ tl ≠ 0 ∧
      Match f ctx R gn bl A MR slots { s with frame := fr2 }
        ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) (bc.args.map gn), w₂⟩ := by
  obtain ⟨TB, args, regs, hTBf, hargs, hty, hset, rfl⟩ := enterBlock_spec hent
  rw [hfunc] at hTBf
  have hTB := blockIdx_block htl hTBf
  have hne0 : tl ≠ 0 := fun e => H.cert.noEntry b B hB bc hbc (e ▸ htl)
  obtain ⟨hl1, hgm⟩ := getMany_spec hargs
  have hl2 := setMany_length hset
  have hlen : bc.args.length = TB.params.length := by simp at hl2; omega
  obtain ⟨-, -, hedge⟩ := H.cert.term b B _ hB (H.blow hB).choose_spec
  obtain ⟨hnd, hpA, hA0⟩ := hedge bc hbc tl TB htl hTB
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
      have haA : bc.args[m] ∈ A b B.body.length :=
        (H.cert.term b B _ hB (H.blow hB).choose_spec).1 _ (args_termArgs hbc _ (List.getElem_mem hm))
      obtain ⟨v'', hv'', hh⟩ := hheld _ haA
      rw [hv'] at hv''; cases hv''
      have hgp : gn x = x := by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hxp
        exact H.shape.params TB hTBmem q hq
      show VHolds v (parCopyEnv ρ₂ (TB.params.map (·.1)) (bc.args.map gn) (gn x))
      rw [hgp, parCopyEnv_param hnd (by simp; omega) m (x := gn bc.args[m]) hxm (by simp [ha]),
        hρ₂ _ haA]
      exact hh
    · obtain ⟨v, hv, hh⟩ := hheld x hxA
      refine ⟨v, by show regs x = some v; rw [setMany_other hset hxp]; exact hv, ?_⟩
      show VHolds v (parCopyEnv ρ₂ (TB.params.map (·.1)) (bc.args.map gn) (gn x))
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
      have hyp : y ∉ TB.params.map (·.1) := by
        intro e
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp e
        exact hpA q hq hyA
      rw [restrict_regs_of_mem hy0, restrict_regs_of_mem hyA]
      exact setMany_other hset hyp

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

/-- **Terminator step**: returns, traps, branches. -/
theorem term_step (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = []) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ vs', Star (VStep vc sem) (.run ⟨b, k, ρ, w⟩) (.run vs') ∧
        Match f ctx R gn bl A MR slots s' vs') ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w', VRetFrom vc sem ⟨b, k, ρ, w⟩ us outs w' ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        AllHold vals outs ∧ MR slots s.mem w' ∧ cm = s.mem.free (slots.map (·.2))) ∧
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
  obtain ⟨vb, hvb, -, -, hdata, htemp, hst0t, ⟨out, tr, hrunT⟩, hcode, htne, -, hbargs, hsucc⟩ :=
    H.shape.blk b B L hB hL
  obtain ⟨ranges, hctx⟩ := H.shape.hctx
  have hok := H.terms f ctx (L.start + B.body.length) B.term L.data L.targets out
    L.tst L.tst' tr H.shape.ctxInv (H.shape.tslot b B L hB hL)
    (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0t) hdata htemp hrunT
  obtain ⟨hargsT, hnoclobT, -⟩ := H.cert.term b B L hB hL
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
  rw [tseg_eq hL] at hsegat hsize htne
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
      obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match H hB hcall hfunc hslots hheld hcons hbcmem
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
    · rename_i hnj
      have hbargs' : vb.branchArgs = #[] := by
        rw [hbargs]; split
        · rename_i bc0 hT; exact absurd hT (hnj bc0)
        · rfl
      obtain ⟨hlt, hall⟩ := hsucc
      have hjlt : j' < L.targets.length := by
        rw [hlt]; exact (List.getElem?_eq_some_iff.mp hbc).1
      obtain ⟨tl, htl, hnil, hedge⟩ := hall j' bc L.targets[j'] hbc (List.getElem?_eq_getElem hjlt)
      obtain ⟨TB, hTB, hlenA, hne0, hM⟩ := enter_match H hB hcall hfunc hslots hheld hcons hbcmem
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
    rw [hT] at hrun' hstep hargsR
    obtain ⟨hn, htr, hdn⟩ := stepTerm_ret (env := env) (p := p) (s := s) (xs := xs) hcall
    refine ⟨fun s' hs => ?_, fun vals cm hs => ?_, fun c hs => ?_⟩
    · rw [hstep] at hs; exact absurd hs (hn s')
    rotate_left
    · rw [hstep] at hs; exact absurd hs (htr c)
    rw [hstep] at hs
    obtain ⟨hg, hcm⟩ := hdn vals cm hs
    have hg' : fr'.getMany xs = .ok vals := by
      rw [getMany_congr (fun x hx => hargsR x (by simpa [termArgs] using hx))]; exact hg
    obtain ⟨hU, k', us, ops, ρ₁, w₁, outs, w₂, hsr, hus, hlen, hall, hmr⟩ := hrun' vals hg'
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
      hvu.symm, by rw [← hvu]; exact hsem⟩, ?_, ?_, hall, by simpa [fr', restrict, hslots] using hmr,
      by rw [hcm, hslots]⟩
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

/-- **Entry**: the entry block's `Args` defines the parameters from the argument registers. -/
theorem entry_step (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ∀ (i : Nat) v, args[i]? = some v → VHolds v (regVal w₀ (.x i))) :
    ∃ ρ₁, VStep vc sem (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, 1, ρ₁, w₀⟩) ∧
      Match f ctx R gn bl A MR slots cs ⟨0, 1, ρ₁, w₀⟩ := by
  obtain ⟨L, hL⟩ := H.blow hB0
  obtain ⟨vb, hvb, -, -, -, -, -, -, hcode, htne, -⟩ := H.shape.blk 0 B0 L hB0 hL
  obtain ⟨hnd, hA⟩ := H.cert.entry B0 hB0
  have hB0mem : B0 ∈ f.blocks := List.mem_of_getElem? hB0
  let ns : List (Nat × Reg) := B0.params.zipIdx.map fun q => (q.1.1, Reg.x q.2)
  have hpre : pre f R 0 = [.args (argPairs ns)] := by
    simp only [pre, hB0, argPairs, ns, List.map_map]
    congr 2
    apply List.map_congr_left
    intro q hq
    have hq1 : q.1 ∈ B0.params := (List.mem_zipIdx hq).2.2 ▸ List.getElem_mem _
    simp [Function.comp_def, H.shape.ren.vreg, H.shape.params B0 hB0mem q.1 hq1]
  have hns1 : ns.map (·.1) = B0.params.map (·.1) := by
    simp only [ns, List.map_map, Function.comp_def]
    rw [show (fun q : (Nat × Clif.Ty) × Nat => q.1.1) = (fun x => x.1) ∘ Prod.fst from rfl,
      ← List.map_map, List.zipIdx_map_fst]
  have hnsm : ∀ (m : Nat) q, B0.params[m]? = some q → ns[m]? = some (q.1, Reg.x m) := by
    intro m q hq
    simp [ns, List.getElem?_zipIdx, hq]
  have hvb0 : vb.insts[0]? = some (.args (argPairs ns)) := by
    rw [← Array.getElem?_toList, hcode, hpre]; rfl
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
  have hsz : 0 + 1 < vb.insts.size := by
    have h1 : vb.insts.size = vb.insts.toList.length := by simp
    have h2 : 0 < (tseg R bl 0).length := List.length_pos_iff.mpr htne
    rw [h1, hcode, hpre]; simp only [List.length_append, List.length_singleton]; omega
  refine ⟨_, VStep.step hvb hvb0 hops hsem hlen (VNext.next hsz), hcall, hfunc, hslots, hmr,
    B0, 0, hB0, hterm, Nat.zero_le _, by simp [hbody], by simp [pos, hpre], ?_, ?_⟩
  · intro x hx
    obtain ⟨hxp, -⟩ := hA x hx
    obtain ⟨m, hm, hxm⟩ := List.getElem_of_mem hxp
    have hm' : m < B0.params.length := by simpa using hm
    have hqm : B0.params[m]? = some B0.params[m] := List.getElem?_eq_getElem hm'
    have hxq : B0.params[m].1 = x := by simpa using hxm
    have hla := setMany_length hregs
    have hma : m < args.length := by simp at hla; omega
    have hrx : cs.frame.regs x = some args[m] :=
      setMany_nodup hregs hnd m x args[m] (by rw [← hxq]; simp [hqm]) (List.getElem?_eq_getElem hma)
    refine ⟨args[m], hrx, ?_⟩
    have hgx : gn x = x := by
      rw [← hxq]; exact H.shape.params B0 hB0mem _ (List.getElem_mem hm')
    show VHolds args[m] (vdefUpd (argOps ns).toArray _ ρ₀ (gn x))
    rw [hgx, ← hxq]
    rw [vdefUpd_argOps (by rw [hns1]; exact hnd) (by simp [argPairs]) m (hnsm m _ hqm)
      (x := regVal w₀ (.x m)) (by simp [argPairs, hnsm m _ hqm])]
    exact hargs m _ (List.getElem?_eq_getElem hma)
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
      p.func? e.name = none) {vals : List Clif.Val} {cm : Clif.Mem} :
    Clif.step env p s ≠ .done vals cm := by
  rw [step_stmt env p s st rest h hext]
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
      AllHold vals outs ∧ MR slots cm0 w ∧ cm = cm0.free (slots.map (·.2))
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

/-- **Whole runs**: from matching states, every CLIF outcome is realised by the VCode run. -/
theorem sim_run (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) {cs : Clif.State}
    (htr : ∀ s c st rest, Reach env p cs s → Clif.step env p s = .trapped c →
      s.frame.body = st :: rest → explicitTrapInst st.inst = true) :
    ∀ fuel s (vs : VState CV Arm.ArmState), Reach env p cs s →
      Match f ctx R gn bl A MR slots s vs → RunOk vc sem MR slots vs (Clif.runLoop env p fuel s) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _; trivial
  | succ n ih =>
    intro s vs hr hm
    obtain ⟨b, k, ρ, w⟩ := vs
    rw [Clif.runLoop_succ]
    have hfunc : s.frame.func = f := hm.2.1
    cases hbody : s.frame.body with
    | nil =>
      obtain ⟨T1, T2, T3⟩ := term_step H hm hbody
      cases hs : Clif.step env p s with
      | next s' =>
        obtain ⟨vs', hstar, hm'⟩ := T1 s' hs
        exact RunOk.prefix hstar (ih s' vs' (hr.snoc hs) hm')
      | done vals cm =>
        obtain ⟨us, outs, w', hret, h1, h2, h3, h4, h5⟩ := T2 vals cm hs
        exact ⟨us, outs, w', s.mem, hret, h1, h2, h3, h4, h5⟩
      | trapped c => exact T3 c hs
      | stuck => trivial
    | cons st rest =>
      have hext : ∀ fn args, st.inst = .call fn args → ∀ e, s.frame.func.extern? fn = some e →
          p.func? e.name = none := by
        obtain ⟨-, -, -, -, B, j, hB, -, -, hbd, -⟩ := hm
        have hst : st ∈ B.body := by
          rw [hbd] at hbody
          exact List.mem_of_mem_drop (hbody ▸ List.mem_cons_self)
        intro fn args hi e he
        exact H.ext B (List.mem_of_getElem? hB) st hst fn args hi e (hfunc ▸ he)
      obtain ⟨S1, S2⟩ := stmt_step H hm hbody
      cases hs : Clif.step env p s with
      | next s' =>
        obtain ⟨vs', hstar, hm'⟩ := S1 s' hs
        exact RunOk.prefix hstar (ih s' vs' (hr.snoc hs) hm')
      | done vals cm => exact absurd hs (stmt_not_done hbody hext)
      | trapped c => exact S2 c hs (htr s c st rest hr hs hbody)
      | stuck => trivial

/-- **The driver lemma (CLIF → VCode).** A CLIF run of `f` from an entry state (parameters
bound to `args`, which the VCode world holds in x0..) is realised by the VCode run from the
entry: returns through `rets` with the returned values held, and memory related; explicit traps
reach an instruction halting with the same code. -/
theorem driver_correct (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ∀ (i : Nat) v, args[i]? = some v → VHolds v (regVal w₀ (.x i)))
    (htr : ∀ s c st rest, Reach env p cs s → Clif.step env p s = .trapped c →
      s.frame.body = st :: rest → explicitTrapInst st.inst = true) (fuel : Nat) :
    RunOk vc sem MR slots ⟨0, 0, ρ₀, w₀⟩ (Clif.runLoop env p fuel cs) := by
  obtain ⟨ρ₁, hstep, hm⟩ := entry_step H hB0 hcall hfunc hslots hbody hterm hregs hty hmr hargs
    (ρ₀ := ρ₀)
  exact RunOk.prefix (Star.single hstep) (sim_run H htr fuel cs _ (.refl _) hm)

end

end Backend.Proof.Driver
