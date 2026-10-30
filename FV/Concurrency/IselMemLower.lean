import FV.Backend.Proof.LowerCover
import FV.Concurrency.IselVar
import FV.Concurrency.IselMemSeg
import FV.Concurrency.IselMemHelp
import FV.Backend.Proof.IselAtomic

/-!
# The memory instruction of a matched statement, on the thread's code (T2h, #311, layer 2e)

**`mem_vreg`**: at a match (`LowerSim.Match`) with a memory statement whose CLIF outcome
succeeds, the renamed code before the statement's one memory instruction runs (`seqRun`) to a
world where the memory instruction's footprint (`cEvs`) is nonempty and lies at the CLIF access,
with `csem` succeeding there. It is `IselVar.events_at_access` on the driver's lowering
(`DriverHyp.insts`, as in `IselStep.stmt_matchN`), carried to the renamed code
(`LowerRename.seqRun_rename`, `vuses_rename`, `CEvsInv.cEvs_mapRegs`).
-/

namespace Concurrency.IselMemLower

open Arm ArmFoot ArmThread Prog ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread
  PrepThread SegRun IselStep IselCheck IselSeg CorrRefine ClifCStepTerm IselThread IselMem Code
  IselMemSeg IselMemHelp IselClif VCodeAddr ClifCStep

/-- The access depends only on the statement's arguments. -/
theorem access_congr {fr fr' : Clif.Frame} {i : Clif.Inst}
    (h : ∀ x ∈ instArgs i, fr'.regs x = fr.regs x) : access fr' i = access fr i := by
  cases i <;> simp only [instArgs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [access]
  all_goals first
    | rfl
    | rw [h]
    | rw [h.1]
    | rw [h.2]
    | rw [h.2.1]

theorem instOkB_mapRegs {g : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming g gn) (i : MInst) :
    instOkB (i.mapRegs g) = instOkB i := by
  have h1 : isCallB (i.mapRegs g) = isCallB i := by cases i <;> rfl
  have h2 : isRetsB (i.mapRegs g) = isRetsB i := by cases i <;> rfl
  simp only [instOkB, isCtl_mapRegs, h1, h2]
  rw [show FormOk default (i.mapRegs g) = FormOk default i from formOk_mapRegs hg default i]

theorem setMany_of_length : ∀ {r : Clif.Regs} {xs : List Clif.ValueId} {vs : List Clif.Val},
    xs.length = vs.length → ∃ r', r.setMany xs vs = some r'
  | r, [], [], _ => ⟨r, rfl⟩
  | r, _ :: _, _ :: _, h => setMany_of_length (r := r.set _ _) (by simpa using h)
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-- A memory statement's outcome keeps the allocations and has one result (a load-like
statement) or none (a store). -/
theorem outcome_shape {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {c : Clif.Mem}
    {inst : Clif.Inst} (hthr : threadInstB inst = true) (hnp : pureInst inst = false)
    (hfe : inst ≠ .fence) {vals : List Clif.Val} {c' : Clif.Mem}
    (h : instOutcome env p fr c inst = .ok (vals, c')) :
    c'.allocs = c.allocs ∧ vals.length = (if isStore inst then 0 else 1) := by
  cases inst <;> simp only [threadInstB, pureInst, Bool.not_eq_true'] at hthr hnp
  all_goals first
    | (exact absurd rfl hfe)
    | (cases hthr; done)
    | (cases hnp; done)
    | skip
  case load op ty fl pp off =>
    obtain ⟨pv, raw, -, -, -, -, rfl, rfl⟩ := evalInst_load_inv (by simpa [bigOf] using hthr) h
    exact ⟨rfl, rfl⟩
  case atomicLoad ty fl pp =>
    obtain ⟨pv, raw, -, -, -, rfl, rfl⟩ := evalInst_atomicLoad_inv (by simpa [bigOf] using hthr) h
    exact ⟨rfl, rfl⟩
  case atomicRmw op ty fl pp x =>
    obtain ⟨pv, a, old, -, -, -, -, rfl, rfl⟩ :=
      evalInst_atomicRmw_inv (by simpa [bigOf] using hthr) h
    exact ⟨rfl, rfl⟩
  case atomicCas ty fl pp ex x =>
    obtain ⟨pv, ev, a, old, -, -, -, -, -, rfl, rfl⟩ :=
      evalInst_atomicCas_inv (by simpa [bigOf] using hthr) h
    refine ⟨?_, rfl⟩
    split <;> rfl
  case store op ty fl x pp off =>
    cases hp : fr.regs pp with
    | none =>
      simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hp, ofOption_none] at h
      cases hx : fr.getAs x ty <;> simp [hx] at h <;> cases h
    | some pv =>
      obtain ⟨-, big, wd, v, hall⟩ := store_facts h hp
      have e := hall c rfl
      rw [h] at e
      simp only [Clif.Res.ok.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨rfl, rfl⟩
  case atomicStore ty fl x pp =>
    cases hp : fr.regs pp with
    | none =>
      simp only [instOutcome, Clif.evalInst, Clif.Frame.get, hp, ofOption_none] at h
      cases hx : fr.getAs x ty <;> simp [hx] at h <;> cases h
    | some pv =>
      obtain ⟨-, big, wd, v, hall⟩ := atomicStore_facts h hp
      have e := hall c rfl
      rw [h] at e
      simp only [Clif.Res.ok.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨rfl, rfl⟩

/-- A statement that steps on some bytes steps on every memory where its outcome succeeds with
as many results. -/
theorem step_next_of {env : Clif.Env} {p : Clif.Program} {s : Clif.State} {stm : Clif.Stmt}
    {rest : List Clif.Stmt} (hb : s.frame.body = stm :: rest)
    (hc : ∀ fn args, stm.inst ≠ .call fn args)
    (hci : ∀ sig callee args, stm.inst ≠ .callIndirect sig callee args)
    {B0 : Bytes} {s0 : Clif.State} (hs0 : Clif.step env p (withBytes s B0) = .next s0)
    {vals0 : List Clif.Val} {m0 : Clif.Mem}
    (h0 : instOutcome env p s.frame (withB s.mem B0) stm.inst = .ok (vals0, m0))
    {c : Clif.Mem} {vals : List Clif.Val} {c' : Clif.Mem}
    (h : instOutcome env p s.frame c stm.inst = .ok (vals, c')) (hlen : vals.length = vals0.length) :
    ∃ s', Clif.step env p { s with mem := c } = .next s' ∧ s'.mem = c' := by
  have hext : ∀ (s1 : Clif.State), ∀ fn args, stm.inst = .call fn args → ∀ e,
      s1.frame.func.extern? fn = some e → p.func? e.name = none :=
    fun _ fn args h => absurd h (hc fn args)
  have hind : ∀ (s1 : Clif.State), ∀ sig callee args, stm.inst = .callIndirect sig callee args →
      ∀ cv, s1.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s1.mem.symbols g.name ≠ some cv.toNat :=
    fun _ sig callee args h => absurd h (hci sig callee args)
  rw [step_stmt env p (withBytes s B0) stm rest hb (hext _) (hind _)] at hs0
  have h0' : instOutcome env p (withBytes s B0).frame (withBytes s B0).mem stm.inst =
      .ok (vals0, m0) := h0
  rw [h0'] at hs0
  simp only [Clif.StepResult.ofRes, Clif.continueWith] at hs0
  have hl0 : stm.results.length = vals0.length := by
    cases hm : (withBytes s B0).frame.regs.setMany stm.results vals0 with
    | none => rw [hm] at hs0; cases hs0
    | some r => exact setMany_length hm
  obtain ⟨regs, hregs⟩ := setMany_of_length (r := s.frame.regs) (hl0.trans hlen.symm)
  have hb' : ({ s with mem := c } : Clif.State).frame.body = stm :: rest := hb
  rw [step_stmt env p _ stm rest hb' (hext _) (hind _)]
  have h' : instOutcome env p ({ s with mem := c } : Clif.State).frame
      ({ s with mem := c } : Clif.State).mem stm.inst = .ok (vals, c') := h
  rw [h']
  simp only [Clif.StepResult.ofRes, Clif.continueWith]
  have hr : ({ s with mem := c } : Clif.State).frame.regs = s.frame.regs := rfl
  rw [hr, hregs]
  exact ⟨_, rfl, rfl⟩

/-- Patching with events at one access stores one value there. -/
theorem patch_local {A : BitVec 64} {n : Nat} (hn : n ≤ 2 ^ 64) {evs : List Ev}
    (h : AtA A n evs) (w : ArmState) :
    patch evs w = write_mem_bytes n A (readM n A (applyR evs w.mem)) w := by
  rw [write_mem_bytes_eq]
  unfold patch
  rw [← applyR_local hn w.mem h]

/-- The memory after a CLIF thread step on its own bytes. -/
theorem cstep_own {env : Clif.Env} {p : Clif.Program} {s s' : Clif.State}
    {evs : List (Prog.Ev SKind BVal)} (hc : CStep env p (.run s) evs (.run s'))
    (hs : Clif.step env p s = .next s') (hag : Agrees bytesI s.mem.bytes evs) :
    s'.mem.bytes = applyEvs bytesI s.mem.bytes evs := by
  obtain ⟨-, -, hf⟩ := hc
  obtain ⟨t'', h1, -⟩ := hf s.mem.bytes hag
  rw [withBytes_self, hs] at h1
  simp only [res, Option.some.injEq, Prod.mk.injEq] at h1
  exact h1.2


/-! ## The parts of a memory statement's outcome -/

theorem store_parts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {c : Clif.Mem}
    {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x pp : Nat} {off : Int}
    {r : List Clif.Val × Clif.Mem} (h : instOutcome env p fr c (.store op ty fl x pp off) = .ok r) :
    ∃ v pv, fr.getAs x ty = .ok v ∧ fr.regs pp = some pv := by
  have h' : Clif.evalInst fr c (.store op ty fl x pp off) = .ok r := h
  simp only [Clif.evalInst] at h'
  obtain ⟨v, hv, h'⟩ := res_bind_eq_ok h'
  obtain ⟨pv, hpv, -⟩ := res_bind_eq_ok h'
  exact ⟨v, pv, hv, get_regs hpv⟩

theorem atomicStore_parts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {c : Clif.Mem}
    {ty : Clif.Ty} {fl : Clif.MemFlags} {x pp : Nat} {r : List Clif.Val × Clif.Mem}
    (h : instOutcome env p fr c (.atomicStore ty fl x pp) = .ok r) :
    ∃ v pv, fr.getAs x ty = .ok v ∧ fr.regs pp = some pv := by
  have h' : Clif.evalInst fr c (.atomicStore ty fl x pp) = .ok r := h
  simp only [Clif.evalInst] at h'
  obtain ⟨v, hv, h'⟩ := res_bind_eq_ok h'
  obtain ⟨pv, hpv, -⟩ := res_bind_eq_ok h'
  exact ⟨v, pv, hv, get_regs hpv⟩

theorem rmw_parts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {c : Clif.Mem}
    {op : Clif.AtomicRmwOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {pp x : Nat}
    {r : List Clif.Val × Clif.Mem} (h : instOutcome env p fr c (.atomicRmw op ty fl pp x) = .ok r) :
    ∃ pv v old, fr.regs pp = some pv ∧ fr.getAs x ty = .ok v ∧
      c.load fl (Clif.effAddr pv 0) ty.bytes ty.width = .ok old := by
  have h' : Clif.evalInst fr c (.atomicRmw op ty fl pp x) = .ok r := h
  simp only [Clif.evalInst] at h'
  obtain ⟨pv, hpv, h'⟩ := res_bind_eq_ok h'
  obtain ⟨v, hv, h'⟩ := res_bind_eq_ok h'
  obtain ⟨_, -, h'⟩ := res_bind_eq_ok h'
  obtain ⟨old, hl, -⟩ := res_bind_eq_ok h'
  exact ⟨pv, v, old, get_regs hpv, hv, hl⟩

theorem cas_parts {env : Clif.Env} {p : Clif.Program} {fr : Clif.Frame} {c : Clif.Mem}
    {ty : Clif.Ty} {fl : Clif.MemFlags} {pp ex x : Nat} {r : List Clif.Val × Clif.Mem}
    (h : instOutcome env p fr c (.atomicCas ty fl pp ex x) = .ok r) :
    ∃ pv ev v old, fr.regs pp = some pv ∧ fr.getAs ex ty = .ok ev ∧ fr.getAs x ty = .ok v ∧
      c.load fl (Clif.effAddr pv 0) ty.bytes ty.width = .ok old := by
  have h' : Clif.evalInst fr c (.atomicCas ty fl pp ex x) = .ok r := h
  simp only [Clif.evalInst] at h'
  obtain ⟨pv, hpv, h'⟩ := res_bind_eq_ok h'
  obtain ⟨ev, he, h'⟩ := res_bind_eq_ok h'
  obtain ⟨v, hv, h'⟩ := res_bind_eq_ok h'
  obtain ⟨_, -, h'⟩ := res_bind_eq_ok h'
  obtain ⟨old, hl, -⟩ := res_bind_eq_ok h'
  exact ⟨pv, ev, v, old, get_regs hpv, he, hv, hl⟩

/-- **The `atomic_cas` comparisons agree**: the CLIF statement's (the loaded value against the
expected value) and its loop's (the bytes at the address against the expected value's vreg). -/
theorem cas_cmp {cm : Clif.Mem} {a n : Nat} {ty : Clif.Ty} (hn : ty.bytes = n) (hn8 : n ≤ 8)
    {old : BitVec ty.width} (hrd : cm.readBits false a n ty.width = some old)
    (ha : a + n ≤ 2 ^ 64) {s : ArmState}
    (hb : ∀ i < n, ∀ b, cm.bytes (a + i) = some b → Arm.read_mem (BitVec.ofNat 64 (a + i)) s = b)
    {ev : BitVec ty.width} {u : CV} (hh : VHolds ⟨ty, ev⟩ u) :
    old = ev ↔ readM n (BitVec.ofNat 64 a) s.mem = (lo64 u).setWidth (n * 8) := by
  simp only [VHolds] at hh
  have hW : ty.width = 8 * n := by rw [← width_bytes, hn]
  revert old ev hrd hh
  rw [hW]
  intro old hrd ev hh
  have hac := readBits_getLsbD_eq hrd ha hb
  refine bits_eq_iff (by omega) (fun j => by rw [hac j, read_mem_bytes_eq]) (fun j => ?_)
  rw [← hh]
  simp only [lo64, BitVec.getLsbD_setWidth]
  by_cases hj : j < 8 * n
  · have h1 : j < n * 8 := by omega
    have h2 : j < 64 := by omega
    simp [hj, h1, h2]
  · have h1 : ¬ j < n * 8 := by omega
    simp [hj, h1]


section
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {F : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem} {MR : MemRelT} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)} {sb : Nat} {syms : String → Option Nat}

/-- **The memory instruction of a matched statement, on the thread's code** (module doc; on
`DriverHypT`). -/
theorem mem_vregT (H : DriverHypT f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hMR : MemRelOk F sb syms f MR) (hX : TlsMemFree X)
    {s : Clif.State} {b : Nat} {ρ : Nat → CV} {w : ArmState}
    (hfunc : s.frame.func = f) (hslots : s.frame.slots = slots) (hmem : MR slots s.mem w)
    {B : Clif.Block} {j : Nat} (hB : f.blocks[b]? = some B) {stm : Clif.Stmt}
    (hstm : B.body[j]? = some stm) (hheld : Held gn (A b j) ρ s.frame)
    (hcons : DFGCons ctx (restrict s.frame (A b j)))
    (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w)
    {L : BLow} {sl : SLow} (hL : bl[b]? = some L) (hsl : L.sl[j]? = some sl)
    {pre0 : List MInst} {mi0 : MInst} {post0 : List MInst}
    (hms : sl.st'.emitted.toList = pre0 ++ mi0 :: post0)
    (hpre0 : ∀ y ∈ pre0, akinds y = []) (hpost0 : ∀ y ∈ post0, akinds y = [])
    (hcov : ∀ i ∈ pre0 ++ mi0 :: post0, SegFoot.Covered fc i)
    (hres : isStore stm.inst = false → stm.results ≠ [])
    (hcas : casOkB stm.inst (pre0 ++ mi0 :: post0) = true)
    {vs : List Clif.Val} {cm' : Clif.Mem}
    (h : instOutcome env p s.frame s.mem stm.inst = .ok (vs, cm'))
    {a n : Nat} (hacc : access s.frame stm.inst = some (a, n))
    (hro : isCas stm.inst = true → s.mem.readonlyAt a n = false)
    (hn : SegShape.memBytes mi0 = some n) (hn0 : 0 < n) :
    ∃ ρb wb ops, seqRun (csem F fc X) (pre0.map (·.mapRegs R)) ρ w = some (.fall ρb wb) ∧
      (mi0.mapRegs R).operands = .ok ops ∧
      cEvs F fc mi0 (vuses ops ρb) wb ≠ [] ∧
      AtA (BitVec.ofNat 64 a) n (cEvs F fc mi0 (vuses ops ρb) wb) ∧
      (∃ r, csem F fc X mi0 (vuses ops ρb) wb = some r) ∧
      (mi0.isCtl = false → csemWF fc mi0 (vuses ops ρb) = true) ∧
      Arm.r .ERR wb = .None ∧ Arm.CheckSPAlignment wb ∧ extraOf stm.results sl.rss = [] ∧
      (∀ ty fl pp ex x, stm.inst = .atomicCas ty fl pp ex x → ∀ ev, s.frame.getAs ex ty = .ok ev →
        ∃ ua uex ux, vuses ops ρb = [ua, uex, ux] ∧ VHolds ⟨ty, ev⟩ uex) := by
  obtain ⟨vb, hvb, hsllen, hstmts, -, -, -, -, hcode, htne, -⟩ := H.shape.blk b B L hB hL
  obtain ⟨⟨info, hinfo, hclif, hres'⟩, hemp, hst0, ⟨tr, hrun⟩, halias⟩ := hstmts j stm sl hstm hsl
  have hBmem : B ∈ f.blocks := List.mem_of_getElem? hB
  have hstmmem : stm ∈ B.body := List.mem_of_getElem? hstm
  have hok := H.insts ctx (L.start + j) info stm.inst sl.st sl.rss sl.st' tr
    H.shape.ctxInv ⟨B, hBmem, stm, hstmmem, rfl⟩ H.subE hinfo hclif (H.indSig B hBmem stm hstmmem) hemp
    (fun x r h => Nat.lt_of_lt_of_le (H.shape.valsBelow x r h) hst0) hrun
  rw [hres'] at hok
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
  have hf' : fr'.func = ctx.func := by simp [fr', restrict, hfunc, H.shape.ctxInv.func]
  have hmr' : MR fr'.slots s.mem w := by simpa [fr', restrict, hslots] using hmem
  have hregs : ∀ x ∈ instArgs stm.inst, fr'.regs x = s.frame.regs x :=
    fun x hx => restrict_regs_of_mem (hargs x hx)
  have hio : instOutcome env p fr' s.mem stm.inst = instOutcome env p s.frame s.mem stm.inst :=
    instOutcome_congr (fr := s.frame) (fr' := fr') rfl rfl env p s.mem stm.inst hregs
  have hrun' := hok.run fr' s.mem ρ₀ w hf' hvh hcons hmr'
  rw [hio, h] at hrun'
  obtain ⟨hU, ρ₀', w', hsr, hrh, -⟩ := hrun'
  have hextra : extraOf stm.results sl.rss = [] := by
    rcases hrh with h0 | ⟨hl, hh⟩
    · rw [h0]; rfl
    · apply extraOf_nil
      intro k rs hk
      have : k < vs.length := by
        have := (List.getElem?_eq_some_iff.mp hk).1; omega
      obtain ⟨out, cls, he, -, -⟩ := hh k rs vs[k] hk (List.getElem?_eq_getElem this)
      exact ⟨out, cls, he⟩
  have hacc' : access fr' stm.inst = some (a, n) := by rw [access_congr hregs]; exact hacc
  rw [hms] at hok hsr hU
  obtain ⟨ρm, wm, ops, hat, hops, hne, hAt, hcs, hem, halm⟩ :=
    IselVar.events_at_access hok hMR hres hX hcov hpre0 hpost0 hf' hvh hcons hmr' he hal
      (by rw [hio]; exact h) hacc' hro hn hn0 hsr
  -- the run to the memory instruction, renamed
  obtain ⟨-, hpre⟩ := IselMemAux.runAt_take hsr hat
  rw [show (pre0 ++ mi0 :: post0).take pre0.length = pre0 by simp] at hpre
  let D : Nat → Prop := fun n => sl.st.nextVreg ≤ n ∧ n < sl.st'.nextVreg
  have hD : ∀ d, D d → gn d = d := fun d hd => H.shape.temps d (by simp only [D] at hd; omega)
  have hdefs : ∀ m ∈ pre0 ++ mi0 :: post0, ∀ d ∈ vdefs m, D d := hok.defs
  have huses : ∀ m ∈ pre0 ++ mi0 :: post0, ∀ u ∈ vuseNums m, D u ∨ ¬ D (gn u) := by
    intro m hm u hu
    rcases hU m hm u hu with hh | hh
    · by_cases h' : u < sl.st'.nextVreg
      · exact .inl ⟨hh, h'⟩
      · right
        rw [H.shape.temps u (by omega)]
        intro hd; exact h' hd.2
    · right; exact hnoclob u (restrict_regs_isSome hh)
  have hAg : Agree gn D ρ₀ ρ := fun _ _ => rfl
  obtain ⟨ρb, hsrb, hAgb⟩ := (seqRun_rename (sem := csem F fc X) (ρ₀ := ρ₀) (ρ := ρ) (w := w)
    H.shape.ren (H.dsem.rename R gn H.shape.ren) hD
    (fun m hm => hdefs m (List.mem_append_left _ hm))
    (fun m hm => huses m (List.mem_append_left _ hm)) hAg).1 hpre
  have hmi : mi0 ∈ pre0 ++ mi0 :: post0 := by simp
  have hu : ∀ o ∈ ops.toList, o.isUse = true → D o.vreg ∨ ¬ D (gn o.vreg) := by
    intro o ho hou
    exact huses mi0 hmi o.vreg (by simp [vuseNums, hops]; exact ⟨o, ⟨by simpa using ho, hou⟩, rfl⟩)
  have hvu : vuses (ops.map (rnOp gn)) ρb = vuses ops ρm := vuses_rename hAgb hu
  have hops' : (mi0.mapRegs R).operands = .ok (ops.map (rnOp gn)) := by
    rw [operands_mapRegs H.shape.ren, hops]; rfl
  have hwf : mi0.isCtl = false → csemWF fc mi0 (vuses ops ρm) = true := fun hc => by
    rcases IselMemAux.covered_cov (hcov mi0 hmi) hops ρm with h' | h'
    · rw [hc] at h'; cases h'
    · exact h'
  have hcasx : ∀ ty fl pp ex x, stm.inst = .atomicCas ty fl pp ex x → ∀ ev,
      s.frame.getAs ex ty = .ok ev → ∃ ua uex ux, vuses ops ρm = [ua, uex, ux] ∧
        VHolds ⟨ty, ev⟩ uex := by
    intro ty fl pp ex x hi ev hev
    have hmk : (!(akinds mi0).isEmpty) = true := by
      cases hk : akinds mi0 with
      | nil => rw [VCodeEvents.cEvs_nil hk] at hne; exact absurd rfl hne
      | cons _ _ => rfl
    have hmm : mi0 ∈ SegShape.memInsts (pre0 ++ mi0 :: post0) := List.mem_filter.mpr ⟨hmi, hmk⟩
    rw [hi] at hcas
    have hP := List.all_eq_true.mp hcas mi0 hmm
    have hxA : ex ∈ A b j := hargs ex (by rw [hi]; simp [instArgs])
    have hnd : ¬ D ex := by
      have h4 : ex < st0.nextVreg := H.cert.small b j ex hxA
      intro hd
      have h3 : sl.st.nextVreg ≤ ex := hd.1
      exact absurd (Nat.lt_of_lt_of_le h4 hst0) (Nat.not_lt.mpr h3)
    have hfr : ρm ex = ρ₀ ex :=
      seqRun_fall_frame (fun m hm hxm => hnd (hdefs m (List.mem_append_left _ hm) ex hxm)) hpre
    obtain ⟨v, hv, hhv⟩ := hheld ex hxA
    rw [Backend.Proof.getAs_ok hev] at hv
    cases hv
    split at hP
    · rename_i t fl' p' e x' d d1
      have he : e = ex := by simpa using hP
      subst he
      rw [operands_casLoop] at hops
      cases hops
      refine ⟨_, _, _, rfl, ?_⟩
      show VHolds _ (ρm _)
      rw [hfr]
      exact hhv
    · cases hP
  refine ⟨ρb, wm, ops.map (rnOp gn), hsrb, hops', ?_, ?_, ?_, ?_, hem, halm, hextra, ?_⟩
  · rw [hvu]; exact hne
  · rw [hvu]; exact hAt
  · rw [hvu]; exact hcs
  · rw [hvu]; exact hwf
  · rw [hvu]; exact hcasx

/-- **The memory instruction of a matched statement, on the thread's code** (`mem_vregT` on
`DriverHyp`). -/
theorem mem_vreg (H : DriverHyp f vc ctx st0 R gn bl A (csem F fc X) MR env p)
    (hMR : MemRelOk F sb syms f MR) (hX : TlsMemFree X)
    {s : Clif.State} {b : Nat} {ρ : Nat → CV} {w : ArmState}
    (hfunc : s.frame.func = f) (hslots : s.frame.slots = slots) (hmem : MR slots s.mem w)
    {B : Clif.Block} {j : Nat} (hB : f.blocks[b]? = some B) {stm : Clif.Stmt}
    (hstm : B.body[j]? = some stm) (hheld : Held gn (A b j) ρ s.frame)
    (hcons : DFGCons ctx (restrict s.frame (A b j)))
    (he : Arm.r .ERR w = .None) (hal : Arm.CheckSPAlignment w)
    {L : BLow} {sl : SLow} (hL : bl[b]? = some L) (hsl : L.sl[j]? = some sl)
    {pre0 : List MInst} {mi0 : MInst} {post0 : List MInst}
    (hms : sl.st'.emitted.toList = pre0 ++ mi0 :: post0)
    (hpre0 : ∀ y ∈ pre0, akinds y = []) (hpost0 : ∀ y ∈ post0, akinds y = [])
    (hcov : ∀ i ∈ pre0 ++ mi0 :: post0, SegFoot.Covered fc i)
    (hres : isStore stm.inst = false → stm.results ≠ [])
    (hcas : casOkB stm.inst (pre0 ++ mi0 :: post0) = true)
    {vs : List Clif.Val} {cm' : Clif.Mem}
    (h : instOutcome env p s.frame s.mem stm.inst = .ok (vs, cm'))
    {a n : Nat} (hacc : access s.frame stm.inst = some (a, n))
    (hro : isCas stm.inst = true → s.mem.readonlyAt a n = false)
    (hn : SegShape.memBytes mi0 = some n) (hn0 : 0 < n) :
    ∃ ρb wb ops, seqRun (csem F fc X) (pre0.map (·.mapRegs R)) ρ w = some (.fall ρb wb) ∧
      (mi0.mapRegs R).operands = .ok ops ∧
      cEvs F fc mi0 (vuses ops ρb) wb ≠ [] ∧
      AtA (BitVec.ofNat 64 a) n (cEvs F fc mi0 (vuses ops ρb) wb) ∧
      (∃ r, csem F fc X mi0 (vuses ops ρb) wb = some r) ∧
      (mi0.isCtl = false → csemWF fc mi0 (vuses ops ρb) = true) ∧
      Arm.r .ERR wb = .None ∧ Arm.CheckSPAlignment wb ∧ extraOf stm.results sl.rss = [] ∧
      (∀ ty fl pp ex x, stm.inst = .atomicCas ty fl pp ex x → ∀ ev, s.frame.getAs ex ty = .ok ev →
        ∃ ua uex ux, vuses ops ρb = [ua, uex, ux] ∧ VHolds ⟨ty, ev⟩ uex) :=
  mem_vregT H.toT hMR hX hfunc hslots hmem hB hstm hheld hcons he hal hL hsl hms hpre0 hpost0
    hcov hres hcas h hacc hro hn hn0

end

end Concurrency.IselMemLower
