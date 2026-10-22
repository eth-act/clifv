import FV.Concurrency.IselRefines

/-!
# Layer 2 from the function's entry (T2h, #311, layer 2e)

* `entry_matchN`: `LowerSim.entry_step` with the entry code exposed: the `Args` step, then the
  run of the stack-argument loads, to the match before the first statement (a copy of the
  `LowerSim` proof, so `LowerSim` is not rebuilt);
* `entryLoads_nil`: no stack-passed parameter, no entry load;
* **`isel_refines_entry`**: `IselRefines.isel_refines` for a run of the VCode thread from the
  function's entry `⟨0, 0, ρ₀, w₀⟩` (the configuration layers 3 and 4a start from), for a
  function whose parameters are all passed in registers: the entry code is the one `Args`
  instruction, without events.
-/

namespace Concurrency.IselEntry

open Arm ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread IselCheck CorrRefine ClifCStepTerm IselThread ThreadRefine IselStep

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {sem : Sem}
  {MR : MemRelT} {env : Clif.Env} {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- **The entry with its code exposed** (module doc). -/
theorem entry_matchN (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p) (hds : DriverSem sem)
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
    ∃ vb ps ρ₁ ρ₂ w₂, vc.blocks[0]? = some vb ∧ vb.insts[0]? = some (.args ps) ∧
      VStep vc sem (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, 1, ρ₁, w₀⟩) ∧
      seqRun sem (entryLoads f R B0) ρ₁ w₀ = some (.fall ρ₂ w₂) ∧
      Match f ctx R gn bl A MR slots cs ⟨0, 1 + (entryLoads f R B0).length, ρ₂, w₂⟩ := by
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
  have hRid : ∀ q ∈ E, R (.vreg q.1.1.1 .int) = .vreg q.1.1.1 .int := by
    intro q hq
    have hq1 : q.1.1 ∈ B0.params := by
      rw [hE] at hq
      exact (List.of_mem_zip (List.of_mem_zip hq).1).1
    simp [H.shape.ren.vreg, H.shape.params B0 hB0mem q.1.1 hq1]
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
  -- the code before the statements
  obtain ⟨ns, hnsdef⟩ : ∃ ns, ns = entryNs E := ⟨_, rfl⟩
  have hpre : pre f R 0 = .args (argPairs ns) :: E.filterMap (entryLoadOf R) := by
    simp only [pre, hB0, entryRegs, entryLoads, ← hEdef]
    rw [entryRegs_eq E hRid, ← hnsdef]
  have hnsnd : (ns.map (·.1)).Nodup := by
    rw [hnsdef]
    exact (entryNs_sublist E).nodup (by rw [hEids]; exact hnd)
  -- `Args`
  have hops := operands_args ns
  have hvu : vuses (argOps ns).toArray ρ₀ = [] := by
    simp only [vuses, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro o ho
    obtain ⟨q', -, hq'⟩ := List.mem_map.mp ho
    rw [← hq']; simp [Operand.isUse]
  have hsem := hds.args (argPairs ns) w₀
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
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁, ρ₁ = vdefUpd (argOps ns).toArray ((argPairs ns).map fun d => regVal w₀ d.2) ρ₀ :=
    ⟨_, rfl⟩
  -- the loads
  obtain ⟨ρ₂, w₂, hrun, hmr₂, -, hreg, hstk, -⟩ := entryLoads_run hMem hMR E ρ₁ slots cs.mem w₀ hRid
    (by rw [hEids]; exact hnd)
    (fun q hq off ho => by
      obtain ⟨m, v, hm, hv⟩ := hEmem q hq
      obtain ⟨hmem, hqb, hqbm⟩ := hentry q hq m v hm hv
      have h := hargs _ _ hmem
      rw [ho] at h
      obtain ⟨hav, -⟩ := h
      rw [hqb]
      exact ⟨hqb ▸ sigParamBytes_bytes hb _ (List.mem_of_getElem? hqbm), hav⟩) hmr
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
    exact SegAt.head (show SegAt vb 0 (MInst.args (argPairs ns) :: E.filterMap (entryLoadOf R)) by
      rw [← hpre]; exact hseg0)
  have hstep : VStep vc sem (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨0, 1, ρ₁, w₀⟩) := by
    rw [hρ₁]
    exact VStep.step hvb hvb0 hops hsem hlen (VNext.next (by rw [hpre] at hsz; simp at hsz; omega))
  have hEL : entryLoads f R B0 = E.filterMap (entryLoadOf R) := by
    simp only [entryLoads, ← hEdef]
  rw [hEL]
  refine ⟨vb, _, ρ₁, ρ₂, w₂, hvb, hvb0, hstep, hseq, hcall, hfunc,
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
      have hns : (B0.params[m].1, r) ∈ ns := hnsdef ▸ mem_entryNs hqE rfl
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hns
      rw [hρ₁, vdefUpd_argOps hnsnd (by simp [argPairs]) i hi (x := regVal w₀ r) (by simp [argPairs, hi])]
      exact h
    | stack off =>
      have h1 := hstk _ hqE off rfl
      simp only at h1
      rw [← hxq, h1, hb']
      obtain ⟨-, hrd⟩ := h
      have hbs : args[m].ty.bytes = 1 ∨ args[m].ty.bytes = 2 ∨ args[m].ty.bytes = 4 ∨
          args[m].ty.bytes = 8 := hb' ▸ sigParamBytes_bytes hb _ (List.mem_of_getElem? hbb)
      obtain ⟨hob, -, hsg⟩ := loadOpOfBytes_facts hbs
      have hw : args[m].ty.width ≤ 64 :=
        (show ∀ t : Clif.Ty, (t.bytes = 1 ∨ t.bytes = 2 ∨ t.bytes = 4 ∨ t.bytes = 8) →
          t.width ≤ 64 by intro t; cases t <;> decide) _ hbs
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

/-- No stack-passed parameter, no entry load. -/
theorem entryLoads_nil {B : Clif.Block} (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig) :
    entryLoads f R B = [] := by
  unfold entryLoads entryParams
  rw [List.filterMap_eq_nil_iff]
  intro q hq
  have hloc : q.1.2 ∈ locsOf f.sig := (List.of_mem_zip (List.of_mem_zip hq).1).2
  unfold entryLoadOf
  split
  · rename_i off h
    exact absurd (h ▸ hloc) (hreg off)
  · rfl

end

section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **Layer 2 from the function's entry, with progress** (T2j): as `isel_refines_entry`; when the
realized prefix is the whole VCode trace, the trace's last configuration has a `VStep` (the
VCode run is not stuck there), else the CLIF thread stops. -/
theorem isel_refines_entryP (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (hMem : MemRefines F sb syms (csem F fc X)) (hMRs : MRStable F MR)
    (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨0, 0, ρ₀, w₀⟩) tr cT) :
    ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
      ((n = tr.length ∧ ∃ c', VStep vc (csem F fc X) cT c') ∨ Stop env p t) := by
  obtain ⟨vb, ps, ρ₁, ρ₂, w₂, hvb, hvb0, hstep, hseq, hm⟩ :=
    entry_matchN H (driverSem_csem F fc X) hMem hMRs hB0 hcall hfunc hslots hbody hterm hregs
      hty hsig hmr hargs
  rw [entryLoads_nil hreg] at hseq hm
  simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at hseq
  obtain ⟨rfl, rfl⟩ := hseq
  have hsim : SimResP env p vc (csem F fc X) cs tr cT := by
    cases hr with
    | nil => exact ⟨0, [], .run cs, Nat.le_refl _, .nil, .nil, .inl ⟨rfl, _, hstep⟩⟩
    | @cons _ c' _ evs tr' hs hr' =>
      obtain ⟨vb', i, ops, hb', hi, -, hev, -, hst⟩ := IselMemMain.vtstep_evs hs
      rw [hvb] at hb'; cases hb'
      rw [hvb0] at hi; cases hi
      have he : evs = [] := hev.trans (VCodeEvents.cEvs_nil rfl _ _)
      subst he
      have e := vstep_det hst hstep
      subst e
      obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ :=
        simResP_of_seg (IselRefines.seg_resP H hchk hMR hMRw hX) cs _ tr' cT hm hr'
      refine ⟨n + 1, trS, t, by simp; omega, hrun, ?_, ?_⟩
      · simpa [conv] using hcorr.tgt
      · rcases hend with ⟨h, hv⟩ | h
        · exact .inl ⟨by simp [h], hv⟩
        · exact .inr h
  obtain ⟨n, trS, t, hn, hrun, hcorr, hend⟩ := hsim
  obtain ⟨ψ, href⟩ := refines_of_corr hcorr hrun.length_le
  exact ⟨n, trS, t, ψ, hn, hrun, href, hend⟩

/-- **Layer 2 from the function's entry** (module doc). -/
theorem isel_refines_entry (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hchk : threadCheckBl f bl = true) (hMR : MemRelOk F sb syms f MR)
    (hMRw : ∀ sl cm w, MR sl cm w → Arm.r .ERR w = .None ∧ Arm.CheckSPAlignment w)
    (hX : TlsMemFree X) (hMem : MemRefines F sb syms (csem F fc X)) (hMRs : MRStable F MR)
    (hreg : ∀ off, ArgLoc.stack off ∉ locsOf f.sig)
    {cs : Clif.State} {B0 : Clif.Block} (hB0 : f.blocks[0]? = some B0)
    (hcall : cs.callers = []) (hfunc : cs.frame.func = f) (hslots : cs.frame.slots = slots)
    (hbody : cs.frame.body = B0.body) (hterm : cs.frame.term = B0.term) {args : List Clif.Val}
    (hregs : Clif.Regs.empty.setMany (B0.params.map (·.1)) args = some cs.frame.regs)
    (hty : args.map (·.ty) = B0.params.map (·.2))
    (hsig : args.map (·.ty) = f.sig.params.map (·.ty))
    {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} (hmr : MR slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀) {tr : List (List Ev)} {cT : VConf CV ArmState}
    (hr : VTRun vc (csem F fc X) (cEvs F fc) (.run ⟨0, 0, ρ₀, w₀⟩) tr cT) :
    ∃ n trS t ψ, n ≤ tr.length ∧ CRun env p (.run cs) trS t ∧
      Refines Maps (fun _ => False) (StepPair (conv (tr.take n))) trS (conv (tr.take n)) ψ ∧
      (n = tr.length ∨ Stop env p t) := by
  obtain ⟨n, trS, t, ψ, hn, hrun, href, hend⟩ := isel_refines_entryP H hchk hMR hMRw hX hMem
    hMRs hreg hB0 hcall hfunc hslots hbody hterm hregs hty hsig hmr hargs hr
  exact ⟨n, trS, t, ψ, hn, hrun, href, hend.imp_left And.left⟩

end

end Concurrency.IselEntry
