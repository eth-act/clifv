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

open Backend

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
  rules : LowerRulesCorrect sem MR env p
  ext : ∀ B ∈ f.blocks, ∀ st ∈ B.body, ∀ fn args, st.inst = .call fn args →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
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
  have hok := H.rules.1 f ctx ranges st0 (L.start + j) info stm.inst sl.st sl.rss sl.st' tr
    hctx hinfo hclif hemp hrun
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
  have hrun' := hok.run fr' s.mem ρ₀ w (by simp [fr', restrict, hfunc, H.shape.func])
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
  have huses_of : Uses sl.st fr' sl.st'.emitted.toList →
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
            obtain ⟨vals0, hev, hlk⟩ := hcons x d info' cl v hd hinfo' hcl hp hvx
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
    | cons n ns ih => simp [List.mapM_cons, vregNum, ih]; rfl
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
  · intro x d info cl v hd hinfo hcl hp hv
    have hx0 : x ∈ A tl 0 := restrict_regs_isSome (by rw [hv]; rfl)
    have hv' : regs x = some v := by
      have := restrict_regs_of_mem (fr := { s.frame with regs, body := TB.body, term := TB.term }) hx0
      rw [this] at hv; exact hv
    rcases hA0 x hx0 with ⟨-, hdn⟩ | ⟨hxp, hxA, -⟩
    · rw [hdn] at hd; cases hd
    · have hvx : (restrict s.frame (A b B.body.length)).regs x = some v := by
        rw [restrict_regs_of_mem hxA, ← setMany_other hset hxp]; exact hv'
      obtain ⟨vals0, hev, hlk⟩ := hcons x d info cl v hd hinfo hcl hp hvx
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

end

end Backend.Proof.Driver
