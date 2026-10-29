import FV.Concurrency.ArmAllocLS

/-!
# Layer 4b with the stack offsets built in `x16` (T2j, #473)

The scope of `arm_alloc_refines_ls` (`MemScopeLS`) covers the plain loads/stores at the final
addressing modes and at the stack modes whose offset `memFinalize` encodes as an immediate. The
other stack offsets lower to **an event-free prefix** (`loadConst64 x16 off`: `movz`/`movk`) and
**one access** at `[sp|fp, x16, sxtx]`. This module covers them:

* `OneEvPreForm`: **a straight-line form whose lines are an event-free prefix and one access**
  (`OneEvForm` with the prefix): the access's events on any memory, from the prefix's end state,
  are the canonical run's (**event equality**, `OneEvPreForm.ev`), and the canonical access's pc,
  error and program do not depend on the memory (`CtlIndep`); a one-event form is one with an
  empty prefix (`oneEvPreForm_of_oneEv`);
* `straightSem_preC`, `straightSem_pre_some`: the canonical run of such a form at any memory
  (**receptiveness**, from `straightSem_pre`/`preMem`);
* `oneEvPre_op`: **the per-item obligation at such a form**: the Arm takes the prefix's event-free
  steps (`nomem_execLines`; a run ending inside them has no event, `privW_of_nil`), then the
  access step, whose events are the source step's on the Arm's read bytes; the event-free steps
  commute with the patch of the read bytes (`iterN_comm`), so `Q` holds after the item;
* `load_stackX_form` … `fpuStore_stackX_form`: **the plain loads/stores at the stack modes that
  `memFinalize` lowers through `x16`** are such forms (`stackFinX`: the prefix is
  `loadConst64 x16 off`, the access `[B, x16, sxtx]` with `B` = `sp` or `fp`, which `SameWorld`
  keeps; both runs put the same constant in `x16`);
* `LSFormX`, `MemScopeLSX`, `itemSim_lsx`: the scope with every plain load/store at a final or
  stack mode, and its per-item obligation; **`arm_alloc_refines_lsx`**: `arm_alloc_refines_ls`'s
  conclusion for the functions of `MemScopeLSX`; `lsFormX_covered`: the forms are straight-line,
  covered, and no calls;
* witness: `ArmAllocLSXWitness.lsx_premises`.
-/

namespace Concurrency.ArmAllocThread

open Arm ArmFoot ArmThread ArmInstFoot ArmPrecise VCodeThread Backend Backend.Proof AllocThread
  ThreadRefine
open Code VCodeEvents VCodeAddr

/-! ## Forms with an event-free prefix -/

/-- Event-free prefix lines: instructions without memory kind. -/
def PreLines (pre : List Line) : Prop := ∀ ln ∈ pre, ∃ x t', ln = .ins x t' ∧ insnKind x = none

theorem kinds_preLines {pre : List Line} (h : PreLines pre) : kinds pre = [] := by
  unfold kinds
  rw [List.filterMap_eq_nil_iff]
  intro ln hln
  obtain ⟨x, t', rfl, hk⟩ := h ln hln
  simpa [lineKind] using hk

/-- **A straight-line form whose lines are an event-free prefix and one Arm instruction** (the
stack accesses through `x16`): the per-form facts `oneEvPre_op` needs. `ev` is the **event
equality**: the allocated access's events on any memory, from the allocated prefix's end state,
are the canonical run's (`cEvs`) on that memory. -/
structure OneEvPreForm (F : BitVec 64 → Prop) (ctx : FnCtx) (i : MInst) : Prop where
  ctl : i.isCtl = false
  form : FormOk ctx i = true
  canon : ∃ ops ic pre x t a, i.operands = .ok ops ∧ i.assign (canonRegs ops) = .ok ic ∧
    ic.lines ctx {} = .ok (pre ++ [.ins x t], {}) ∧ PreLines pre ∧ x.toArmInst env0 = .ok a ∧
    x.toArmInst { env0 with pc := env0.pc + 4 * pre.length } = .ok a ∧ CtlIndep a
  line : ∀ ops regs i', i.operands = .ok ops → regs.size = ops.size → i.assign regs = .ok i' →
    ∃ pre x t, PreLines pre ∧ ∀ ps, i'.lines ctx ps = .ok (pre ++ [.ins x t], ps)
  arm : ∀ ops regs i' pre x t env a, i.operands = .ok ops → regs.size = ops.size →
    i.assign regs = .ok i' → i'.lines ctx {} = .ok (pre ++ [.ins x t], {}) →
    x.toArmInst env = .ok a → (∀ rel rs rn, clsOf a ≠ .stx rel rs rn) ∧
      ∀ y, ∀ e ∈ instEvs a y, e.k ≠ .relXW ∧ (e.k.dir ≠ .F → 0 < e.n)
  ev : ∀ (s w y : ArmState) ops regs i' pre x t env env' a, SameWorld F s w → CheckSPAlignment s →
    i.operands = .ok ops → regs.size = ops.size →
    (∀ p ∈ (ops.zip regs).toList, p.2.allocatable = true) →
    i.assign regs = .ok i' → i'.lines ctx {} = .ok (pre ++ [.ins x t], {}) →
    execLines env pre s = some y → x.toArmInst env' = .ok a →
    ∀ M, instEvs a (setMem M y) = cEvs F ctx i (useVals ops regs s) (setMem M w)

theorem lines_eq {ctx : FnCtx} {i' : MInst} {ls ls' : List Line}
    (h1 : ∀ ps, i'.lines ctx ps = .ok (ls, ps)) (h2 : ∀ ps, i'.lines ctx ps = .ok (ls', ps)) :
    ls = ls' := by
  have := (h1 {}).symm.trans (h2 {})
  simp only [Except.ok.injEq, Prod.mk.injEq] at this
  exact this.1

theorem ins_last {L L' : List Line} {x x' : Insn} {t t' : Option Clif.TrapCode}
    (h : L ++ [.ins x t] = L' ++ [.ins x' t']) : L = L' ∧ x = x' ∧ t = t' := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, Line.ins.injEq, and_true] at h2
  exact ⟨h1, h2⟩

/-- **A one-event form is a form with an empty event-free prefix.** -/
theorem oneEvPreForm_of_oneEv {F : BitVec 64 → Prop} {ctx : FnCtx} {i : MInst}
    (h : OneEvForm F ctx i) : OneEvPreForm F ctx i := by
  obtain ⟨ops, ic, x, t, a, hops, hic, hl, ha, hc⟩ := h.canon
  refine ⟨h.ctl, h.form, ⟨ops, ic, [], x, t, a, hops, hic, hl,
    fun _ h => absurd h List.not_mem_nil, ha, ha, hc⟩, ?_, ?_, ?_⟩
  · intro ops regs i' hops hsz hasg
    obtain ⟨x, t, hxl⟩ := h.line ops regs i' hops hsz hasg
    exact ⟨[], x, t, fun _ h => absurd h List.not_mem_nil, hxl⟩
  · intro ops regs i' pre x t env a hops hsz hasg hl ha
    obtain ⟨x', t', hxl⟩ := h.line ops regs i' hops hsz hasg
    have e := (hl.symm.trans (hxl {}))
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := ins_last (L' := []) e.1
    exact h.arm ops regs i' x t env a hops hsz hasg hl ha
  · intro s w y ops regs i' pre x t env env' a hsw _ hops hsz hall hasg hl hy ha M
    obtain ⟨x', t', hxl⟩ := h.line ops regs i' hops hsz hasg
    have e := (hl.symm.trans (hxl {}))
    simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := ins_last (L' := []) e.1
    simp only [execLines, Option.some.injEq] at hy
    subst hy
    exact h.ev s w ops regs i' x t env' a hsw hops hsz hall hasg hl ha M

open Classical in
/-- **Receptiveness of a form with an event-free prefix**: `straightSem_pre` with the access's
memory-independent control (`CtlIndep`): the step's condition does not depend on the memory. -/
theorem straightSem_preC {F : BitVec 64 → Prop} {ctx : FnCtx} {i ic : MInst} {uses : List CV}
    {w : ArmState} {ops : Array Operand} {pre : List Line} {x : Insn}
    {t : Option Clif.TrapCode} {a : ArmInst}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hl : ic.lines ctx {} = .ok (pre ++ [.ins x t], {})) (hk : PreLines pre)
    (ha : x.toArmInst env0 = .ok a)
    (ha' : x.toArmInst { env0 with pc := env0.pc + 4 * pre.length } = .ok a)
    (hc : CtlIndep a) (y1 : ArmState)
    (hy1 : execLines env0 pre (placeUses ops (canonRegs ops) uses w) = some y1) (M : Memory) :
    straightSem F ctx i uses (setMem M w) =
      if AccessOk F ctx ic (placeUses ops (canonRegs ops) uses w) ∧
          Arm.r .PC (exec_inst a y1) = Arm.r .PC y1 + 4#64 ∧
          Arm.r .ERR (exec_inst a y1) = .None ∧
          (exec_inst a y1).program = w.program then
        some (defVals ops (canonRegs ops) (exec_inst a (setMem M y1)),
          exec_inst a (setMem M y1), Ctl.next)
      else none := by
  rw [straightSem_pre hops hic hl hk ha ha' hc y1 hy1 M]
  obtain ⟨h1, h2, h3⟩ := hc M y1
  simp only [h1, h2, h3, r_setMem]

/-- A source step of a form with an event-free prefix runs the canonical prefix. -/
theorem straightSem_pre_some {F : BitVec 64 → Prop} {ctx : FnCtx} {i ic : MInst} {uses : List CV}
    {w : ArmState} {ops : Array Operand} {pre : List Line} {x : Insn}
    {t : Option Clif.TrapCode}
    (hops : i.operands = .ok ops) (hic : i.assign (canonRegs ops) = .ok ic)
    (hl : ic.lines ctx {} = .ok (pre ++ [.ins x t], {})) (hk : PreLines pre) {M : Memory}
    {r : List CV × ArmState × Ctl} (h : straightSem F ctx i uses (setMem M w) = some r) :
    ∃ y1, execLines env0 pre (placeUses ops (canonRegs ops) uses w) = some y1 := by
  cases hy : execLines env0 pre (placeUses ops (canonRegs ops) uses w) with
  | some y1 => exact ⟨y1, rfl⟩
  | none =>
    exfalso
    unfold straightSem at h
    simp only [hops, hic, placeUses_setMem, accessOk_setMem, execMInst, hl] at h
    rw [execLines_append env0 pre [.ins x t] (setMem M (placeUses ops (canonRegs ops) uses w)),
      preMem hk M (placeUses ops (canonRegs ops) uses w), hy] at h
    split at h
    · simp at h
    · cases h

/-- **The per-item obligation at a straight-line form with an event-free prefix and one access**
(`OneEvPreForm`): the Arm's prefix steps have no event; its access step reads (writes) what the
canonical run reads (writes), on every memory, so the source steps with the Arm's read bytes
(**receptiveness**, `straightSem_preC`), and `Q` holds after both patched with them (`q_patch`;
the prefix's steps commute with the patch, `iterN_comm`). A run ending inside the prefix has no
event. -/
theorem oneEvPre_op {R : RL} (hR : R.Wf) {s : ArmState} {mon : Mon} {b k : Nat}
    {allocs : Array Loc} {its' : List RItem} {m : Loc → CV} {w : ArmState} {evs0 : List Ev}
    {c0 : MConf CV ArmState}
    (hq : Q R s (OpC b k allocs its' m w)) (hA : AInv R (OpC b k allocs its' m w))
    (hs0 : SrcStep R (OpC b k allocs its' m w) evs0 c0)
    (hform : ∀ vb i, R.vc.blocks[b]? = some vb → vb.insts[k]? = some i → OneEvPreForm R.F R.ctx i)
    {ls : List Lab} {t' : ArmState × Mon}
    (hr : PRun Policy.arm R.step (fun _ _ => True) (s, mon) ls t') :
    OpOut R (s, mon) (OpC b k allocs its' m w) ls := by
  cases hs0 with
  | @op _ _ _ _ _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
  have hf := hform vb i hvb hi
  obtain ⟨regs, hal, hsz, hall, huses⟩ := q_regs hq hvb hi hops
  have hstr := q_stRel hq
  have herrw : Arm.r .ERR w = .None := by
    rw [← hstr.world.1 .ERR (by simp [Masked]), hstr.err]
  have halw : CheckSPAlignment w :=
    align_of_sp (show Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s from
      (hstr.world.1 (.GPR 31#5) (by simp [Masked])).symm) hstr.align
  have hnc : ∀ info, i ≠ .call info := by
    rintro info rfl; exact absurd hf.ctl (by simp [MInst.isCtl])
  have hnt : ∀ info ti, i ≠ .tryCall info ti := by
    rintro info ti rfl; exact absurd hf.ctl (by simp [MInst.isCtl])
  have hwf : csemWF R.ctx i (itemUses ops allocs m) = true := by
    rw [huses]; simp [csemWF, hf.form, hops, useVals_length ops regs hsz]
  have hsemM : ∀ M, R.sem i (itemUses ops allocs m) (setMem M w) =
      straightSem R.F R.ctx i (itemUses ops allocs m) (setMem M w) := fun M => by
    rw [R.sem_eq hnc hnt, csem_of_wf hf.ctl hwf (by rw [r_setMem]; exact herrw)
      (by rw [spAlign_setMem]; exact halw)]
  obtain ⟨ops', ic, pre0, x', t', a', hops', hic, hlc, hkc, hac, hac', hci⟩ := hf.canon
  rw [hops] at hops'
  cases hops'
  obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hf.form
  cases hst with
  | @op _ _ _ _ _ _ vb1 i1 ops1 outs outs' w' ctl m2 c' hvb1 hi1 hops1 hsz1 hsem hlen hho hcl hn =>
  rw [hvb] at hvb1; cases hvb1; rw [hi] at hi1; cases hi1; rw [hops] at hops1; cases hops1
  obtain rfl := csem_ctl hf.ctl (R.sem_csem hsem)
  cases hn with
  | next hk =>
  -- the canonical prefix's end state and the step's condition
  obtain ⟨y1, hy1⟩ := straightSem_pre_some (F := R.F) (uses := itemUses ops allocs m) hops hic hlc
    hkc ((hsemM (applyR evs0 w.mem)).symm.trans hsem)
  have hss := fun M => straightSem_preC (F := R.F) (uses := itemUses ops allocs m) (w := w) hops hic
    hlc hkc hac hac' hci y1 hy1 M
  have hsem' := hsem
  rw [show patch evs0 w = setMem (applyR evs0 w.mem) w from rfl, hsemM, hss] at hsem'
  split at hsem'
  case isFalse => cases hsem'
  rename_i hC
  simp only [Option.some.injEq, Prod.mk.injEq] at hsem'
  obtain ⟨rfl, -, -⟩ := hsem'
  -- the source step at the unpatched world: the allocated lines from `s`
  have hsem0 : R.sem i (itemUses ops allocs m) (setMem w.mem w) =
      some (defVals ops (canonRegs ops) (exec_inst a' (setMem w.mem y1)),
        exec_inst a' (setMem w.mem y1), .next) := by
    rw [hsemM, hss, ite_eq_left hC]
  have hlen0 : (defVals ops (canonRegs ops) (exec_inst a' (setMem w.mem y1))).length =
      ((ops.zip allocs).toList.filter (·.1.isDef)).length := by
    rw [defVals_length _ _ _ (exec_inst a' (setMem (applyR evs0 w.mem) y1))]
    exact hlen
  obtain ⟨j, regs', i', ls1, T, s', c'', hal', hasg, hl1, hins, hdrop, hpc, hrun, hint, -, -, -⟩ :=
    realizes_op_lines hR hq hvb hi hops hsz1 hsem0 hlen0 hk hOS hL
      (csem_next_world' (R.sem_csem hsem0) hnc herrw)
  obtain rfl : regs' = regs := regs_inj (hal'.symm.trans hal)
  obtain ⟨pre, x, t, hkp, hxl⟩ := hf.line ops regs' i' hops hsz hasg
  obtain rfl := lines_eq hl1 hxl
  have hat := lines_at hdrop
  have hhook : ∀ x0 t0, Line.ins x0 t0 ∈ pre ++ [.ins x t] → x0.hooked = false := fun x0 t0 h => by
    obtain ⟨x1, t1, e, hh⟩ := hins _ h; cases e; exact hh
  have htk : (pre ++ [Line.ins x t]).take pre.length = pre := by simp
  obtain ⟨y, hy⟩ := execLines_take hrun pre.length
  rw [htk] at hy
  have hintp : InterOk (R.envOf j) pre s := by
    have := interOk_take hint pre.length; rwa [htk] at this
  have hatp : ∀ k ln, pre[k]? = some ln → R.fa.lines.toList[j + k]? = some ln := fun k ln h =>
    hat k ln (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h)
  have hhookp : ∀ x0 t0, Line.ins x0 t0 ∈ pre → x0.hooked = false := fun x0 t0 h =>
    hhook x0 t0 (List.mem_append_left _ h)
  have hnom := nomem_execLines (X := R.X) (H := R.H) hR.layout hR.lm hR.fit (kinds_preLines hkp)
    hatp hhookp hstr.prog hpc hstr.err hintp hy
  have hity : iterN R.step pre.length s = y :=
    iterN_execLines hR.layout hR.lm hR.fit pre j s y hatp hhookp hstr.prog hpc hstr.err hintp hy
  obtain ⟨x2, t2, a, hli, ha, hdec, hev, -⟩ := step_execLines (X := R.X) (H := R.H) hR.layout
    hR.lm hR.fit hat hhook hstr.prog hpc hstr.err hint hrun pre.length (by simp)
  rw [show (pre ++ [Line.ins x t])[pre.length]? = some (.ins x t) by simp] at hli
  simp only [Option.some.injEq, Line.ins.injEq] at hli
  obtain ⟨rfl, rfl⟩ := hli
  rw [show iterN (ArmStepX R.X R.H R.fa) pre.length s = y from hity] at hdec hev
  obtain ⟨hnostx, hevk⟩ := hf.arm ops regs' i' pre x t _ a hops hsz hasg (hxl {}) ha
  have hevq : ∀ M', instEvs a (setMem M' y) =
      cEvs R.F R.ctx i (itemUses ops allocs m) (setMem M' w) := fun M' => by
    rw [huses]
    exact hf.ev s w y ops regs' i' pre x t _ _ a hstr.world hstr.align hops hsz hall hasg (hxl {}) hy
      ha M'
  -- the Arm run
  by_cases hN : ls.length ≤ pre.length
  · obtain ⟨-, hev0, -⟩ := prun_nil hr fun i hi => hnom i (by omega)
    exact .inr (.inr (.inr (privW_of_nil hev0)))
  obtain ⟨A, l, B, rfl, hAl⟩ : ∃ A l B, ls = A ++ l :: B ∧ A.length = pre.length := by
    refine ⟨ls.take pre.length, ls[pre.length], ls.drop (pre.length + 1), ?_, by simp; omega⟩
    rw [List.getElem_cons_drop, List.take_append_drop]
  obtain ⟨⟨sm, monm⟩, r1, r2⟩ := PRun.split A (l :: B) hr
  obtain ⟨hsm, hevA, hfpA⟩ := prun_nil r1 fun i hi => hnom i (by omega)
  have hsm' : sm = y := by simp only at hsm; rw [hsm, hAl, hity]
  have hfp : ∀ i < pre.length, Footprint R.step (iterN R.step i s) [] := fun i hi =>
    hfpA i (by omega)
  subst sm
  cases r2 with
  | @cons _ t1 _ _ _ hs hp _ hr' =>
  have hxf : l.xfail = false := by
    cases hs with
    | exec => rfl
    | xfail hc => rw [cls_of_decode hdec] at hc; exact absurd hc (hnostx _ _ _)
  obtain ⟨M, hM⟩ : ∃ M, l.evs = stepEvs (setMem M y) := by
    rcases hp with h | h
    · rw [hxf] at h; cases h
    · exact h
  have hl : l.evs = instEvs a (setMem M y) := by
    rw [hM, ArmPrecise.stepEvs_setMem, hev, ArmPrecise.instEvs_setMem]
  have hfix : l.evs = cEvs R.F R.ctx i (itemUses ops allocs m) (patch l.evs w) := by
    show l.evs = cEvs R.F R.ctx i (itemUses ops allocs m) (setMem (applyR l.evs w.mem) w)
    rw [← hevq, ArmPrecise.instEvs_setMem, hl, ArmPrecise.instEvs_setMem,
      reread_applyR_reread (len_instEvs a y) (ArmPrecise.n_instEvs a y)]
  -- the source step reading the Arm's bytes
  have hsem1 : R.sem i (itemUses ops allocs m) (patch l.evs w) =
      some (defVals ops (canonRegs ops) (exec_inst a' (setMem (applyR l.evs w.mem) y1)),
        exec_inst a' (setMem (applyR l.evs w.mem) y1), .next) := by
    show R.sem i _ (setMem _ w) = _
    rw [hsemM, hss, ite_eq_left hC]
  have hlen1 : (defVals ops (canonRegs ops) (exec_inst a' (setMem (applyR l.evs w.mem) y1))).length =
      ((ops.zip allocs).toList.filter (·.1.isDef)).length := by
    rw [defVals_length _ _ _ (exec_inst a' (setMem (applyR evs0 w.mem) y1))]
    exact hlen
  have hav1 : ∀ e ∈ l.evs, Avoids R.F e.n e.addr := by
    rw [hfix]
    exact cEvs_avoid (by rw [patch, r_setMem]; exact herrw)
      (fun _ => ⟨hwf, by rw [patch, spAlign_setMem]; exact halw⟩) (R.sem_csem hsem1)
  have hq1 := q_patch hR hq hav1
  obtain ⟨j2, regs2, i2, ls2, T2, s2, c2, hal2, hasg2, hl2, hins2, hdrop2, hpc2, hrun2, hint2,
    ⟨m2', w2, rfl⟩, hm2, hq2⟩ := realizes_op_lines hR hq1 hvb hi hops hsz1 hsem1 hlen1 hk hOS hL
      (csem_next_world' (R.sem_csem hsem1) hnc (by rw [patch, r_setMem]; exact herrw))
  obtain rfl : regs2 = regs' := regs_inj (hal2.symm.trans hal)
  obtain rfl : i2 = i' := by rw [hasg] at hasg2; cases hasg2; rfl
  obtain rfl := lines_eq hl2 hxl
  have hstr1 := q_stRel hq1
  have hhook2 : ∀ x0 t0, Line.ins x0 t0 ∈ pre ++ [Line.ins x t] → x0.hooked = false :=
    fun x0 t0 h => by obtain ⟨x1, t1, e, hh⟩ := hins2 _ h; cases e; exact hh
  have hit : iterN R.step (pre ++ [Line.ins x t]).length (patch l.evs s) = s2 :=
    iterN_execLines hR.layout hR.lm hR.fit _ j2 _ s2 (lines_at hdrop2) hhook2 hstr1.prog hpc2
      hstr1.err hint2 hrun2
  have hcomm : iterN R.step pre.length (patch l.evs s) = patch l.evs y := by
    show iterN R.step pre.length (setMem (applyR l.evs s.mem) s) = setMem (applyR l.evs y.mem) y
    rw [iterN_comm hfp, ← hity, iterN_nil_mem hfp]
  have hend : R.step (patch l.evs y) = s2 := by
    rw [← hit, List.length_append, List.length_singleton, iterN_succ', hcomm]
  obtain ⟨s1, mon1⟩ := t1
  have ht1 : s1 = R.step (patch l.evs y) := by
    cases hs with
    | exec => rfl
    | xfail => cases hxf
  subst ht1
  -- the item's image
  have hfoot1 : IFoot R.sem i (itemUses ops allocs m) (patch l.evs w) l.evs := by
    have hfo := straightSem_foot (F := R.F) (ctx := R.ctx) (i := i) (uses := itemUses ops allocs m)
      (w := patch l.evs w)
    have hce : cEvs R.F R.ctx i (itemUses ops allocs m) (patch l.evs w) =
        straightEvs R.ctx i (itemUses ops allocs m) (patch l.evs w) := by
      unfold cEvs; simp only [hf.ctl, Bool.false_eq_true, ite_false]
    rw [← hce, ← hfix] at hfo
    refine ⟨hfo.1, fun m' hm' => ?_⟩
    rw [show setMem m' (patch l.evs w) = setMem m' w from rfl, hsemM, show patch l.evs w =
      setMem (applyR l.evs w.mem) w from rfl, hsemM]
    exact hfo.2 m' hm'
  have hlen : l.evs.length ≤ 1 := by rw [hl]; exact len_instEvs a _
  have htake : (A ++ l :: B).take (pre.length + 1) = A ++ [l] := by
    rw [← hAl]
    simp [List.take_append, List.take_of_length_le (show A.length ≤ A.length + 1 by omega)]
  have hlenA : (evTr A).length = pre.length := by rw [evTr_length, hAl]
  refine .inr (.inl ⟨pre.length + 1, l.evs, _, (R.step (patch l.evs y), mon1),
    fun k => (pre.length, k), by simp only [List.length_append, List.length_cons]; omega,
    .inl (Nat.succ_pos _), .op hvb hi hops hfix hfoot1 hm2,
    by rw [htake]; exact PRun.append r1 (PRun.cons hs hp trivial .nil),
    .inl ⟨by show Q R (R.step (patch l.evs y)) _; rw [hend]; exact hq2,
      aInv_step hR hq1 (aInv_patch hA _) hm2⟩, ?_⟩)
  have htr : evTr ((A ++ l :: B).take (pre.length + 1)) = evTr A ++ [l.evs] := by
    rw [htake, evTr_append]; rfl
  rw [htr]
  refine ⟨fun k hk => ?_, fun k k' h1 h2 => Or.inr ⟨rfl, h1⟩, fun p y' hy' hW hn => ?_,
    fun e he hF => ?_, .inl ⟨hlen, fun e he => ?_⟩, fun h => by omega⟩
  · rw [evAt_append_ge _ _ (by simp only [hlenA]; exact Nat.le_refl _)]
    simp only [hlenA, Nat.sub_self, evAt_single]
    exact List.getElem?_eq_getElem hk
  · obtain ⟨j', k'⟩ := p
    by_cases hj : j' < pre.length
    · rw [evAt_append_lt _ _ (by simp only [hlenA]; exact hj), evAt_evTr_nil hevA] at hy'
      cases hy'
    · rw [evAt_append_ge _ _ (by simp only [hlenA]; omega)] at hy'
      simp only [hlenA] at hy'
      rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hj) with hj2 | hj2
      · subst hj2
        rw [Nat.sub_self, evAt_single] at hy'
        exact absurd rfl (hn k' (List.getElem?_eq_some_iff.mp hy').1)
      · obtain ⟨q, hq'⟩ : ∃ q, j' - pre.length = q + 1 := ⟨j' - pre.length - 1, by omega⟩
        rw [hq'] at hy'
        simp [evAt] at hy'
  · have he' : e ∈ instEvs a (setMem M y) := hl ▸ he
    have hn0 := (hevk _ e he').2 hF
    have := hav1 e he 0 hn0
    simpa [PrivA] using this
  · exact (hevk _ e (hl ▸ he)).1

/-! ## The stack accesses through `x16` -/

/-- **`memFinalize` at a stack mode with a prefix**: the prefix is `loadConst64 x16 off`, the
access mode `[B, x16, sxtx]` with `B` = `sp` or `fp`. -/
theorem stackFinX {ctx : FnCtx} {m m' : AMode} {n : Nat} {pre : List Line} (hm : StackMode m)
    (hf : memFinalize ctx m n = .ok (pre, m')) (hpre : pre ≠ []) :
    ∃ B o, (B = .sp ∨ B = .x 29) ∧ pre = loadConst64 (.x 16) (u64 o) ∧
      m' = .regExtended B (.x 16) .sxtx := by
  have key : ∀ (B : Reg) (o : Int), (B = .sp ∨ B = .x 29) →
      (match simm9? o with
        | some s => (([] : List Line), AMode.unscaled B s)
        | none => match uimm12Scaled? o n with
          | some k => ([], .unsignedOffset B k)
          | none => (loadConst64 (.x 16) (u64 o), .regExtended B (.x 16) .sxtx)) = (pre, m') →
      ∃ B o, (B = .sp ∨ B = .x 29) ∧ pre = loadConst64 (.x 16) (u64 o) ∧
        m' = .regExtended B (.x 16) .sxtx := by
    intro B o hB h
    split at h
    · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hpre
    · split at h
      · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hpre
      · simp only [Prod.mk.injEq] at h; exact ⟨B, o, hB, h.1.symm, h.2.symm⟩
  rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;>
    simp only [memFinalize, pure, Except.pure, Except.ok.injEq] at hf
  · exact key .sp _ (.inl rfl) hf
  · exact key .sp _ (.inl rfl) hf
  · exact key (.x 29) _ (.inr rfl) hf

theorem preLines_loadConst64 (rd : Reg) (v : Nat) : PreLines (loadConst64 rd v) := by
  intro ln hln
  simp only [loadConst64, List.mem_cons, List.mem_filterMap] at hln
  rcases hln with rfl | ⟨j, _, hj⟩
  · exact ⟨_, _, rfl, rfl⟩
  · split at hj
    · cases hj; exact ⟨_, _, rfl, rfl⟩
    · cases hj

theorem finX {n : Nat} {B : Reg} (hB : B = .sp ∨ B = .x 29) :
    FinalAM n (.regExtended B (.x 16) .sxtx) :=
  ⟨by rcases hB with rfl | rfl <;> simp [BaseOk], by simp [IdxOk], by simp⟩

theorem straightEvs_lines {ctx : FnCtx} {i ic : MInst} {uses : List CV} {w : ArmState}
    {ops : Array Operand} {ls : List Line} (hops : i.operands = .ok ops)
    (hic : i.assign (canonRegs ops) = .ok ic) (hl : ic.lines ctx {} = .ok (ls, {})) :
    straightEvs ctx i uses w = linesEvs env0 ls (placeUses ops (canonRegs ops) uses w) := by
  unfold straightEvs
  simp only [hops, hic, hl]

theorem pcx_setMem (Y : ArmState) (M : Memory) (n : Nat) (P X : BitVec 64) :
    pcx (setMem M Y) n P X = setMem M (pcx Y n P X) := by
  simp only [pcx, w_setMem]

theorem pcx16_sp (Y : ArmState) (M : Memory) (P X : BitVec 64) :
    Arm.r (.GPR 31#5) (setMem M (pcx Y 16 P X)) = Arm.r (.GPR 31#5) Y := by
  simp [pcx, r_setMem, Arm.r_of_w_different]

theorem pcx16_regX {Y : ArmState} {M : Memory} {P X : BitVec 64} {B : Reg}
    (hB : B = .sp ∨ B = .x 29) : regX (setMem M (pcx Y 16 P X)) B = regX Y B := by
  rw [regX_setMem]
  rcases hB with rfl | rfl <;> simp [pcx, regX, spOf, rnum, Arm.r_of_w_different]

theorem pcx16_x16 (Y : ArmState) (M : Memory) (P X : BitVec 64) :
    regX (setMem M (pcx Y 16 P X)) (.x 16) = X := by
  rw [regX_setMem]
  simp [pcx, regX, rnum, Arm.r_of_w_different, Arm.r_of_w_same]

theorem addrX_eq {ctx : FnCtx} {n : Nat} {B : Reg} {Y Z : ArmState} (hB : regX Y B = regX Z B)
    (h16 : regX Y (.x 16) = regX Z (.x 16)) :
    AMode.addr ctx (.regExtended B (.x 16) .sxtx) n Y =
      AMode.addr ctx (.regExtended B (.x 16) .sxtx) n Z := by
  rw [show AMode.addr ctx (.regExtended B (.x 16) .sxtx) n Y = regX Y B +
      Arm.extend_reg (regX Y (.x 16)) (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 from rfl,
    show AMode.addr ctx (.regExtended B (.x 16) .sxtx) n Z = regX Z B +
      Arm.extend_reg (regX Z (.x 16)) (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 from rfl, hB, h16]

/-- The allocated and the canonical access through `x16` are at the same address: both prefixes
put the same constant in `x16`, and the base (`sp` or `fp`) is kept by `SameWorld`. -/
theorem addrX_pcx {F : BitVec 64 → Prop} {ctx : FnCtx} {n : Nat} {B : Reg} {s w W : ArmState}
    (hsw : SameWorld F s w) (hB : B = .sp ∨ B = .x 29) (hW : regX W B = regX w B) (M : Memory)
    (P P' X : BitVec 64) :
    AMode.addr ctx (.regExtended B (.x 16) .sxtx) n (setMem M (pcx s 16 P X)) =
      AMode.addr ctx (.regExtended B (.x 16) .sxtx) n (setMem M (pcx W 16 P' X)) :=
  addrX_eq (by rw [pcx16_regX hB, pcx16_regX hB, regX_stack hsw hB, hW])
    (by rw [pcx16_x16, pcx16_x16])

theorem addr_pcx16 {ctx : FnCtx} {n : Nat} {B : Reg} {Y : ArmState} {M : Memory} {P X : BitVec 64}
    (hB : B = .sp ∨ B = .x 29) :
    AMode.addr ctx (.regExtended B (.x 16) .sxtx) n (setMem M (pcx Y 16 P X)) =
      regX Y B + Arm.extend_reg X (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 := by
  rw [show AMode.addr ctx (.regExtended B (.x 16) .sxtx) n (setMem M (pcx Y 16 P X)) =
      regX (setMem M (pcx Y 16 P X)) B + Arm.extend_reg (regX (setMem M (pcx Y 16 P X)) (.x 16))
        (Arm.decode_reg_extend ExtendOp.sxtx.bits) 0 from rfl, pcx16_regX hB, pcx16_x16]

/-- **A GPR load at a stack mode that `memFinalize` lowers through `x16`** is a form with an
event-free prefix and one access (`OneEvPreForm`). -/
theorem load_stackX_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : LoadOp} {d : Nat}
    {m m' : AMode} {pre : List Line} {fl : Clif.MemFlags} (hm : StackMode m)
    (hfo : FormOk ctx (.load op (.vreg d .int) m fl) = true)
    (hf : memFinalize ctx m op.bytes = .ok (pre, m')) (hpre : pre ≠ []) :
    OneEvPreForm F ctx (.load op (.vreg d .int) m fl) := by
  have hop : op ≠ .fpuLoad128 := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> simpa [FormOk, memOk] using hfo
  obtain ⟨B, o, hBB, rfl, rfl⟩ := stackFinX hm hf hpre
  have hfin : FinalAM op.bytes (.regExtended B (.x 16) .sxtx) := finX hBB
  have hops : (MInst.load op (.vreg d .int) m fl).operands = .ok #[⟨d, .int, .def, .late, .reg⟩] := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hasg : ∀ r0 : Reg, (MInst.load op (.vreg d .int) m fl).assign #[r0] = .ok (.load op r0 m fl) := by
    intro r0; rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hlines : ∀ (r0 : Reg) ps, (MInst.load op r0 m fl).lines ctx ps =
      .ok (loadConst64 (.x 16) (u64 o) ++
        [.ins (.load op r0 (.regExtended B (.x 16) .sxtx)) fl.trapCode], ps) := by
    intro r0 ps; simp [MInst.lines, hf, bind, Except.bind, pure, Except.pure]
  have hpl := preLines_loadConst64 (.x 16) (u64 o)
  have henv : ∀ (env env' : Env) (r0 : Reg) (mm : AMode),
      Insn.toArmInst env (.load op r0 mm) = Insn.toArmInst env' (.load op r0 mm) :=
    fun _ _ _ _ => rfl
  obtain ⟨a0, ha0, -⟩ := exec_load_line env0 ctx op hop 0 (by omega) _ hfin s16 (fun _ => s16_align)
  refine ⟨rfl, hfo, ⟨_, _, _, _, _, a0, hops, hasg (.x 0), hlines _ _, hpl, ha0,
    (henv _ env0 _ _).trans ha0, (load_line_shape env0 ctx op hop 0 (by omega) _ hfin s16 ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, _, hpl, hlines _⟩
  · intro ops regs i' pre' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := ins_last hl.1
    exact plain_arm ha (.inl ⟨_, _, _, rfl⟩)
  · intro s w y ops regs i' pre' x t env env' a hsw hal hops' hsz hall hasg' hl hy ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := ins_last hl.1
    rcases x_or_v (hall (⟨d, .int, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop) <;> ldst_noV
    rw [(steps_loadConst64 env (n := 16) (by omega) (u64 o) s).exec, Option.some.injEq] at hy
    subst hy
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [straightEvs_lines (ic := .load op (.x 0) m fl) hops (hasg _) (hlines _ _)]
    have hpu : placeUses #[⟨d, .int, .def, .late, .reg⟩] (canonRegs #[⟨d, .int, .def, .late, .reg⟩])
        (useVals #[⟨d, .int, .def, .late, .reg⟩] #[.x p] s) (setMem M w) = setMem M w := by
      simp [placeUses, useVals, Operand.isUse]
    rw [hpu, linesEvs_steps _ (steps_loadConst64 env0 (n := 16) (by omega) (u64 o) (setMem M w))
      (kinds_loadConst64 _ _), linesEvs_single ((henv _ env0 _ _).trans ha0), pcx_setMem]
    have hsw' : Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s :=
      (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
    rw [load_line_cf env' ctx op hop p (by omega) _ hfin ha _
        (fun _ => align_of_spEq (pcx16_sp _ _ _ _) hal),
      load_line_cf env0 ctx op hop 0 (by omega) _ hfin ha0 _
        (fun _ => align_of_spEq ((pcx16_sp _ _ _ _).trans hsw') hal),
      addrX_pcx hsw hBB rfl, setMem_mem, setMem_mem]

theorem pcx16_gpr {Y : ArmState} {M : Memory} {P X : BitVec 64} {q : Nat} (hq : q < 29)
    (h16 : q ≠ 16) :
    Arm.r (.GPR (BitVec.ofNat 5 q)) (setMem M (pcx Y 16 P X)) = Arm.r (.GPR (BitVec.ofNat 5 q)) Y := by
  have hne : BitVec.ofNat 5 q ≠ BitVec.ofNat 5 16 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  simp [pcx, r_setMem, Arm.r_of_w_different, hne]

theorem pcx16_sfp (Y : ArmState) (M : Memory) (P X : BitVec 64) (q : BitVec 5) :
    Arm.r (.SFP q) (setMem M (pcx Y 16 P X)) = Arm.r (.SFP q) Y := by
  simp [pcx, r_setMem, Arm.r_of_w_different]

/-- **A GPR store at a stack mode that `memFinalize` lowers through `x16`** is a form with an
event-free prefix and one access (`OneEvPreForm`). -/
theorem store_stackX_form {F : BitVec 64 → Prop} {ctx : FnCtx} {op : StoreOp} {d : Nat}
    {m m' : AMode} {pre : List Line} {fl : Clif.MemFlags} (hm : StackMode m)
    (hfo : FormOk ctx (.store op (.vreg d .int) m fl) = true)
    (hf : memFinalize ctx m op.bytes = .ok (pre, m')) (hpre : pre ≠ []) :
    OneEvPreForm F ctx (.store op (.vreg d .int) m fl) := by
  have hop : op ≠ .fpuStore128 := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> simpa [FormOk, memOk] using hfo
  obtain ⟨B, o, hBB, rfl, rfl⟩ := stackFinX hm hf hpre
  have hfin : FinalAM op.bytes (.regExtended B (.x 16) .sxtx) := finX hBB
  have hops : (MInst.store op (.vreg d .int) m fl).operands = .ok #[⟨d, .int, .use, .early, .reg⟩] := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hasg : ∀ r0 : Reg, (MInst.store op (.vreg d .int) m fl).assign #[r0] = .ok (.store op r0 m fl) := by
    intro r0; rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hlines : ∀ (r0 : Reg) ps, (MInst.store op r0 m fl).lines ctx ps =
      .ok (loadConst64 (.x 16) (u64 o) ++
        [.ins (.store op r0 (.regExtended B (.x 16) .sxtx)) fl.trapCode], ps) := by
    intro r0 ps; simp [MInst.lines, hf, bind, Except.bind, pure, Except.pure]
  have hpl := preLines_loadConst64 (.x 16) (u64 o)
  have henv : ∀ (env env' : Env) (r0 : Reg) (mm : AMode),
      Insn.toArmInst env (.store op r0 mm) = Insn.toArmInst env' (.store op r0 mm) :=
    fun _ _ _ _ => rfl
  obtain ⟨a0, ha0, -⟩ := exec_store_line env0 ctx op hop 0 (by omega) _ hfin s16 (fun _ => s16_align)
  refine ⟨rfl, hfo, ⟨_, _, _, _, _, a0, hops, hasg (.x 0), hlines _ _, hpl, ha0,
    (henv _ env0 _ _).trans ha0, (store_line_shape env0 ctx op hop 0 (by omega) _ hfin s16 ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, _, hpl, hlines _⟩
  · intro ops regs i' pre' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := ins_last hl.1
    exact plain_arm ha (.inr (.inl ⟨_, _, _, rfl⟩))
  · intro s w y ops regs i' pre' x t env env' a hsw hal hops' hsz hall hasg' hl hy ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := ins_last hl.1
    rcases allocatable_cases (hall (⟨d, .int, .use, .early, .reg⟩, r0) (by simp)) with
      ⟨p, rfl, hp, hp16, -, -⟩ | ⟨p, rfl, -⟩
    rotate_left
    · cases op <;> (try exact absurd rfl hop) <;> ldst_noV
    rw [(steps_loadConst64 env (n := 16) (by omega) (u64 o) s).exec, Option.some.injEq] at hy
    subst hy
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [straightEvs_lines (ic := .store op (.x 0) m fl) hops (hasg _) (hlines _ _)]
    have hpu : placeUses #[⟨d, .int, .use, .early, .reg⟩] (canonRegs #[⟨d, .int, .use, .early, .reg⟩])
        (useVals #[⟨d, .int, .use, .early, .reg⟩] #[.x p] s) (setMem M w) =
        setMem M (setReg w (.x 0) (regVal s (.x p))) := by
      simp [placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase, setReg, w_setMem]
    rw [hpu, linesEvs_steps _ (steps_loadConst64 env0 (n := 16) (by omega) (u64 o) _)
      (kinds_loadConst64 _ _), linesEvs_single ((henv _ env0 _ _).trans ha0), pcx_setMem]
    have hsw' : Arm.r (.GPR 31#5) (setReg w (.x 0) (regVal s (.x p))) = Arm.r (.GPR 31#5) s := by
      simp [setReg, Arm.r_of_w_different, rnum]; exact (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
    have hW : regX (setReg w (.x 0) (regVal s (.x p))) B = regX w B := by
      rcases hBB with rfl | rfl <;> simp [regX, spOf, setReg, Arm.r_of_w_different, rnum]
    rw [store_line_cf env' ctx op hop p (by omega) _ hfin ha _
        (fun _ => align_of_spEq (pcx16_sp _ _ _ _) hal),
      store_line_cf env0 ctx op hop 0 (by omega) _ hfin ha0 _
        (fun _ => align_of_spEq ((pcx16_sp _ _ _ _).trans hsw') hal),
      addr_pcx16 hBB, addr_pcx16 hBB, hW, regX_stack hsw hBB, pcx16_gpr hp hp16,
      pcx16_gpr (q := 0) (by omega) (by omega)]
    simp [setReg, Arm.r_of_w_same, regVal, rnum, lo64, BitVec.setWidth_setWidth_of_le]

/-- **A SIMD&FP load at a stack mode that `memFinalize` lowers through `x16`** is a form with an
event-free prefix and one access (`OneEvPreForm`). -/
theorem fpuLoad_stackX_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d : Nat}
    {m m' : AMode} {pre : List Line} {fl : Clif.MemFlags} (hm : StackMode m)
    (hfo : FormOk ctx (.fpuLoad sz (.vreg d .float) m fl) = true)
    (hf : memFinalize ctx m sz.bytes = .ok (pre, m')) (hpre : pre ≠ []) :
    OneEvPreForm F ctx (.fpuLoad sz (.vreg d .float) m fl) := by
  have hop : FpSz sz := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> simpa [FormOk, memOk, FpSz] using hfo
  obtain ⟨B, o, hBB, rfl, rfl⟩ := stackFinX hm hf hpre
  have hfin : FinalAM sz.bytes (.regExtended B (.x 16) .sxtx) := finX hBB
  have hops : (MInst.fpuLoad sz (.vreg d .float) m fl).operands = .ok #[⟨d, .float, .def, .late, .reg⟩] := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hasg : ∀ r0 : Reg, (MInst.fpuLoad sz (.vreg d .float) m fl).assign #[r0] = .ok (.fpuLoad sz r0 m fl) := by
    intro r0; rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hlines : ∀ (r0 : Reg) ps, (MInst.fpuLoad sz r0 m fl).lines ctx ps =
      .ok (loadConst64 (.x 16) (u64 o) ++
        [.ins (.fpuLoad sz r0 (.regExtended B (.x 16) .sxtx)) fl.trapCode], ps) := by
    intro r0 ps; simp [MInst.lines, hf, bind, Except.bind, pure, Except.pure]
  have hpl := preLines_loadConst64 (.x 16) (u64 o)
  have henv : ∀ (env env' : Env) (r0 : Reg) (mm : AMode),
      Insn.toArmInst env (.fpuLoad sz r0 mm) = Insn.toArmInst env' (.fpuLoad sz r0 mm) :=
    fun _ _ _ _ => rfl
  obtain ⟨a0, ha0, -⟩ := exec_fpuLoad_line env0 ctx sz hop 0 (by omega) _ hfin s16 (fun _ => s16_align)
  refine ⟨rfl, hfo, ⟨_, _, _, _, _, a0, hops, hasg (.v 0), hlines _ _, hpl, ha0,
    (henv _ env0 _ _).trans ha0, (fpuLoad_line_cf env0 ctx sz hop 0 (by omega) _ hfin ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, _, hpl, hlines _⟩
  · intro ops regs i' pre' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := ins_last hl.1
    exact plain_arm ha (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
  · intro s w y ops regs i' pre' x t env env' a hsw hal hops' hsz hall hasg' hl hy ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := ins_last hl.1
    rcases v_or_x (hall (⟨d, .float, .def, .late, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop with rfl | rfl <;> ldst_noV
    rw [(steps_loadConst64 env (n := 16) (by omega) (u64 o) s).exec, Option.some.injEq] at hy
    subst hy
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [straightEvs_lines (ic := .fpuLoad sz (.v 0) m fl) hops (hasg _) (hlines _ _)]
    have hpu : placeUses #[⟨d, .float, .def, .late, .reg⟩] (canonRegs #[⟨d, .float, .def, .late, .reg⟩])
        (useVals #[⟨d, .float, .def, .late, .reg⟩] #[.v p] s) (setMem M w) = setMem M w := by
      simp [placeUses, useVals, Operand.isUse]
    rw [hpu, linesEvs_steps _ (steps_loadConst64 env0 (n := 16) (by omega) (u64 o) (setMem M w))
      (kinds_loadConst64 _ _), linesEvs_single ((henv _ env0 _ _).trans ha0), pcx_setMem]
    have hsw' : Arm.r (.GPR 31#5) w = Arm.r (.GPR 31#5) s :=
      (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
    rw [(fpuLoad_line_cf env' ctx sz hop p hp _ hfin ha).2 _
        (fun _ => align_of_spEq (pcx16_sp _ _ _ _) hal),
      (fpuLoad_line_cf env0 ctx sz hop 0 (by omega) _ hfin ha0).2 _
        (fun _ => align_of_spEq ((pcx16_sp _ _ _ _).trans hsw') hal),
      addrX_pcx hsw hBB rfl, setMem_mem, setMem_mem]

/-- **A SIMD&FP store at a stack mode that `memFinalize` lowers through `x16`** is a form with an
event-free prefix and one access (`OneEvPreForm`). -/
theorem fpuStore_stackX_form {F : BitVec 64 → Prop} {ctx : FnCtx} {sz : ScalarSize} {d : Nat}
    {m m' : AMode} {pre : List Line} {fl : Clif.MemFlags} (hm : StackMode m)
    (hfo : FormOk ctx (.fpuStore sz (.vreg d .float) m fl) = true)
    (hf : memFinalize ctx m sz.bytes = .ok (pre, m')) (hpre : pre ≠ []) :
    OneEvPreForm F ctx (.fpuStore sz (.vreg d .float) m fl) := by
  have hop : FpSz sz := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> simpa [FormOk, memOk, FpSz] using hfo
  obtain ⟨B, o, hBB, rfl, rfl⟩ := stackFinX hm hf hpre
  have hfin : FinalAM sz.bytes (.regExtended B (.x 16) .sxtx) := finX hBB
  have hops : (MInst.fpuStore sz (.vreg d .float) m fl).operands = .ok #[⟨d, .float, .use, .early, .reg⟩] := by
    rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hasg : ∀ r0 : Reg, (MInst.fpuStore sz (.vreg d .float) m fl).assign #[r0] = .ok (.fpuStore sz r0 m fl) := by
    intro r0; rcases hm with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ <;> rfl
  have hlines : ∀ (r0 : Reg) ps, (MInst.fpuStore sz r0 m fl).lines ctx ps =
      .ok (loadConst64 (.x 16) (u64 o) ++
        [.ins (.fpuStore sz r0 (.regExtended B (.x 16) .sxtx)) fl.trapCode], ps) := by
    intro r0 ps; simp [MInst.lines, hf, bind, Except.bind, pure, Except.pure]
  have hpl := preLines_loadConst64 (.x 16) (u64 o)
  have henv : ∀ (env env' : Env) (r0 : Reg) (mm : AMode),
      Insn.toArmInst env (.fpuStore sz r0 mm) = Insn.toArmInst env' (.fpuStore sz r0 mm) :=
    fun _ _ _ _ => rfl
  obtain ⟨a0, ha0, -⟩ := exec_fpuStore_line env0 ctx sz hop 0 (by omega) _ hfin s16 (fun _ => s16_align)
  refine ⟨rfl, hfo, ⟨_, _, _, _, _, a0, hops, hasg (.v 0), hlines _ _, hpl, ha0,
    (henv _ env0 _ _).trans ha0, (fpuStore_line_cf env0 ctx sz hop 0 (by omega) _ hfin ha0).1⟩,
    ?_, ?_, ?_⟩
  · intro ops regs i' hops' hsz hasg'
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    exact ⟨_, _, _, hpl, hlines _⟩
  · intro ops regs i' pre' x t env a hops' hsz hasg' hl ha
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := ins_last hl.1
    exact plain_arm ha (.inr (.inr (.inr ⟨_, _, _, rfl⟩)))
  · intro s w y ops regs i' pre' x t env env' a hsw hal hops' hsz hall hasg' hl hy ha M
    rw [hops] at hops'; cases hops'
    obtain ⟨r0, rfl⟩ := regs1 hsz
    rw [hasg] at hasg'; cases hasg'
    rw [hlines] at hl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := ins_last hl.1
    rcases v_or_x (hall (⟨d, .float, .use, .early, .reg⟩, r0) (by simp)) with ⟨p, rfl, hp⟩ | ⟨p, rfl⟩
    rotate_left
    · rcases hop with rfl | rfl <;> ldst_noV
    rw [(steps_loadConst64 env (n := 16) (by omega) (u64 o) s).exec, Option.some.injEq] at hy
    subst hy
    unfold cEvs
    simp only [MInst.isCtl, Bool.false_eq_true, ite_false]
    rw [straightEvs_lines (ic := .fpuStore sz (.v 0) m fl) hops (hasg _) (hlines _ _)]
    have hpu : placeUses #[⟨d, .float, .use, .early, .reg⟩] (canonRegs #[⟨d, .float, .use, .early, .reg⟩])
        (useVals #[⟨d, .float, .use, .early, .reg⟩] #[.v p] s) (setMem M w) =
        setMem M (setReg w (.v 0) (regVal s (.v p))) := by
      simp [placeUses, useVals, Operand.isUse, canonRegs, canonReg, canonBase, setReg, w_setMem]
    rw [hpu, linesEvs_steps _ (steps_loadConst64 env0 (n := 16) (by omega) (u64 o) _)
      (kinds_loadConst64 _ _), linesEvs_single ((henv _ env0 _ _).trans ha0), pcx_setMem]
    have hsw' : Arm.r (.GPR 31#5) (setReg w (.v 0) (regVal s (.v p))) = Arm.r (.GPR 31#5) s := by
      simp [setReg, Arm.r_of_w_different, rnum]; exact (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
    have hW : regX (setReg w (.v 0) (regVal s (.v p))) B = regX w B := by
      rcases hBB with rfl | rfl <;> simp [regX, spOf, setReg, Arm.r_of_w_different, rnum]
    rw [(fpuStore_line_cf env' ctx sz hop p hp _ hfin ha).2 _
        (fun _ => align_of_spEq (pcx16_sp _ _ _ _) hal),
      (fpuStore_line_cf env0 ctx sz hop 0 (by omega) _ hfin ha0).2 _
        (fun _ => align_of_spEq ((pcx16_sp _ _ _ _).trans hsw') hal),
      addr_pcx16 hBB, addr_pcx16 hBB, hW, regX_stack hsw hBB, pcx16_sfp, pcx16_sfp]
    simp [setReg, Arm.r_of_w_same, regVal, rnum]

/-! ## The scope with every plain load/store and the run level -/

/-- **The modes of a plain access of `bytes` bytes**: a final mode (`LSMode`), or a stack mode
that `memFinalize` lowers (with or without the `x16` prefix). -/
def LSModeX (ctx : FnCtx) (bytes : Nat) (m : AMode) : Prop :=
  LSMode m = true ∨ (StackMode m ∧ ∃ pre m', memFinalize ctx m bytes = .ok (pre, m'))

/-- **The plain load/store forms**: a covered (`FormOk`) GPR or SIMD&FP load/store at a final or
stack mode (`LSModeX`). -/
def LSFormX (ctx : FnCtx) (i : MInst) : Prop :=
  FormOk ctx i = true ∧ match i with
    | .load op _ m _ | .store op _ m _ => LSModeX ctx op.bytes m
    | .fpuLoad sz _ m _ | .fpuStore sz _ m _ => LSModeX ctx sz.bytes m
    | _ => False

theorem lsFormX_of_lsForm {ctx : FnCtx} {i : MInst} (h : LSForm ctx i) : LSFormX ctx i := by
  obtain ⟨hfo, hm⟩ := h
  have hx : ∀ {n m}, LSModeOk ctx n m → LSModeX ctx n m := fun h =>
    h.imp id fun ⟨hs, m', hf⟩ => ⟨hs, [], m', hf⟩
  refine ⟨hfo, ?_⟩
  cases i <;> simp only at hm ⊢ <;> exact hx hm

/-- **The forms of `LSFormX` are straight-line, covered, and no calls.** -/
theorem lsFormX_covered {ctx : FnCtx} {i : MInst} (h : LSFormX ctx i) :
    i.isCtl = false ∧ FormOk ctx i = true ∧ (∀ info, i ≠ .call info) ∧
      (∀ info ti, i ≠ .tryCall info ti) := by
  obtain ⟨hfo, hm⟩ := h
  cases i <;> simp only at hm <;>
    exact ⟨rfl, hfo, fun _ h => (by cases h), fun _ _ h => (by cases h)⟩

/-- **Every plain load/store form is a one-event form** (`LSForm`: no prefix) **or a form with an
event-free prefix and one access** (the stack offsets through `x16`). -/
theorem lsFormX_cases {F : BitVec 64 → Prop} {ctx : FnCtx} {i : MInst} (h : LSFormX ctx i) :
    LSForm ctx i ∨ OneEvPreForm F ctx i := by
  obtain ⟨hfo, hm⟩ := h
  cases i <;> simp only at hm
  case load op rt m fl =>
    rcases hm with hm | ⟨hs, pre, m', hf⟩
    · exact .inl ⟨hfo, .inl hm⟩
    by_cases hp : pre = []
    · subst hp; exact .inl ⟨hfo, .inr ⟨hs, m', hf⟩⟩
    refine .inr ?_
    rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
    all_goals exact load_stackX_form hs hfo hf hp
  case store op rt m fl =>
    rcases hm with hm | ⟨hs, pre, m', hf⟩
    · exact .inl ⟨hfo, .inl hm⟩
    by_cases hp : pre = []
    · subst hp; exact .inl ⟨hfo, .inr ⟨hs, m', hf⟩⟩
    refine .inr ?_
    rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
    all_goals exact store_stackX_form hs hfo hf hp
  case fpuLoad sz rt m fl =>
    rcases hm with hm | ⟨hs, pre, m', hf⟩
    · exact .inl ⟨hfo, .inl hm⟩
    by_cases hp : pre = []
    · subst hp; exact .inl ⟨hfo, .inr ⟨hs, m', hf⟩⟩
    refine .inr ?_
    rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
    all_goals exact fpuLoad_stackX_form hs hfo hf hp
  case fpuStore sz rt m fl =>
    rcases hm with hm | ⟨hs, pre, m', hf⟩
    · exact .inl ⟨hfo, .inl hm⟩
    by_cases hp : pre = []
    · subst hp; exact .inl ⟨hfo, .inr ⟨hs, m', hf⟩⟩
    refine .inr ?_
    rcases rt with ⟨d, _ | _⟩ | _ | _ | _ | _ <;> try (simp [FormOk] at hfo; done)
    all_goals exact fpuStore_stackX_form hs hfo hf hp

theorem noGoto_lsx {ctx : FnCtx} {i : MInst} (h : LSFormX ctx i) : ¬ GotoForm i := by
  intro hg
  rcases hg with (⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩) | ⟨_, _, rfl⟩ |
      ⟨_, _, _, _, _, rfl⟩ <;>
    exact h.2

/-- **The scope of `arm_alloc_refines_lsx`**: every instruction is a memory form, an LL/SC loop
(`MemFormL`), a block-ending branch (`BrForm`) or a plain load/store at a final or stack mode
(`LSFormX`). -/
def MemScopeLSX (R : RL) : Prop :=
  ∀ (b : Nat) (vb : VBlock) (k : Nat) (i : MInst), R.vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → MemFormL R.ctx i ∨ BrForm i ∨ LSFormX R.ctx i

theorem memScopeLSX_of_memScopeLS {R : RL} (h : MemScopeLS R) : MemScopeLSX R :=
  fun b vb k i hb hi => (h b vb k i hb hi).imp_right (Or.imp_right lsFormX_of_lsForm)

/-- **The per-item obligation of the scope with every plain load/store, with moves**, on ranked
configurations (`μR`; the statement before #553 used a measure of the configuration only, which
`MachBuffer`'s layout falsifies: `ArmAllocBranch` module doc). -/
theorem itemSim_lsx {R : RL} (hR : R.Wf) (hsc : MemScopeLSX R) :
    ItemSim Policy.arm R.step (OkPriv R) (SrcStepR R) (RelQR R) (DoneR R) (μR R) (PrivA R) := by
  rintro ⟨s, mon⟩ ⟨c, r⟩ ⟨hqa, hk⟩ ls t' hr
  match c, hqa, hk with
  | .ret vals m w, _, _ => exact .inl (.inl ⟨vals, m, w, rfl⟩)
  | .halt w, _, _ => exact .inl (.inr (.inl ⟨w, rfl⟩))
  | .run ⟨b, its, m, w⟩, hqa, hk =>
  by_cases hS : ∃ evs c', SrcStep R (.run ⟨b, its, m, w⟩) evs c'
  case neg => exact .inl (.inr (.inr fun evs c' h => hS ⟨evs, c', h⟩))
  obtain ⟨evs0, c0, hs0⟩ := hS
  cases hs0 with
  | @move _ src dst its' =>
    rcases move_op hR hqa hr with h | h
    · exact .inr (.inl (isOut_μR noGotoAt_move hk h))
    · exact .inr (.inr (.inr h))
  | @op _ k allocs its' _ _ vb i ops _ _ hvb hi hops hevs hfoot hst =>
    have hs : SrcStep R (OpC b k allocs its' m w) _ _ := .op hvb hi hops hevs hfoot hst
    rcases RelQ.op' hqa hs with ⟨hq, hA⟩ | ⟨rfl, vals, m', w', rfl⟩
    case inr => exact .inr (.inl (itemSimOut_retR hs (RkC.pos hk)))
    have uniq : ∀ vb' i', R.vc.blocks[b]? = some vb' → vb'.insts[k]? = some i' → i' = i :=
      fun vb' i' h1 h2 => by rw [hvb] at h1; cases h1; rw [hi] at h2; cases h2; rfl
    rcases hsc b vb k i hvb hi with hl | hbr | hls
    · refine opOutR_of (noGotoAt_op hvb hi (noGoto_memFormL hl)) hk ?_
      rcases hl with (h | h | ⟨ty, rt, rn, fl, rfl, hfo⟩ | ⟨ty, rt, rn, fl, rfl, hfo⟩) | hl | hl
      · exact opOut_okPriv (fun ls t' hr => noev_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => fence_op hR hq hA hs
          (fun vb' i' h1 h2 => (uniq vb' i' h1 h2).trans h) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ ldar_form hfo) hr) hr
      · exact opOut_okPriv (fun ls t' hr => oneEv_op hR hq hA hs
          (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ stlr_form hfo) hr) hr
      · exact rmw_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
      · exact cas_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hl) hr
    · exact goto_op hR hq hA hk hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hbr) hr
    · rcases lsFormX_cases (F := R.F) hls with hls' | hpf
      · exact opOutR_of (noGotoAt_op hvb hi (noGoto_ls hls')) hk (opOut_okPriv (fun ls t' hr =>
          oneEv_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ lsForm_oneEv hls') hr) hr)
      · exact opOutR_of (noGotoAt_op hvb hi (noGoto_lsx hls)) hk (opOut_okPriv (fun ls t' hr =>
          oneEvPre_op hR hq hA hs (fun vb' i' h1 h2 => uniq vb' i' h1 h2 ▸ hpf) hr) hr)

/-- **Layer 4b with every plain load/store** (module doc): every precise Arm run under `OkPriv`
from a `Q`-related state realizes a run of the allocated code (`MTRun`) with `Refines` (equal
kinds, the addresses outside the world private, the atomic updates monitor pairs), up to the
allocated code's return, trap or undefined behaviour (`Done`), for functions whose instructions
are event-free, `fence`, `ldar`, `stlr`, LL/SC loops, block-ending branches or plain loads/stores
at final or stack addressing modes, including the stack offsets built in `x16`
(`MemScopeLSX`), whatever their moves. -/
theorem arm_alloc_refines_lsx {R : RL} (hR : R.Wf) (hsc : MemScopeLSX R)
    {s : ArmState} {mon : Mon} {c : MConf CV ArmState} (hq : Q R s c) (hA : AInv R c)
    {ls : List Lab} {t' : ArmState × Mon} (hr : PRun Policy.arm R.step (OkPriv R) (s, mon) ls t') :
    ∃ n trS cE ψ, n ≤ ls.length ∧ MTRun R.vc R.rf R.sem ckeep (cEvs R.F R.ctx) c trS cE ∧
      Refines (· = ·) (PrivA R) (MonPair (evTr (ls.take n))) (PrepThread.conv trS)
        (PrepThread.conv (evTr (ls.take n))) ψ ∧ (n = ls.length ∨ Done R cE) := by
  obtain ⟨r, hrel⟩ := RelQR.of (t := (s, mon)) hq hA
  obtain ⟨n, trS, cE, ψ, hn, hs, href, hend⟩ :=
    refines_of_itemSim (itemSim_lsx hR hsc) hr hrel
  exact ⟨n, trS, cE.1, ψ, hn, mtrun_of_srun (SRun.fst hs), href, hend⟩

end Concurrency.ArmAllocThread
