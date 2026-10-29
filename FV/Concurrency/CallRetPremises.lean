import FV.Concurrency.CallRetResume
import FV.Concurrency.CallLoadResume

/-!
# The caller's resume premises from the call's operands and the callee's return (#473, step (1))

Completes the premises of `CallRetResume.resume_layersR`/`resume_premises_of_retEnd` and of
`IselResume.isel_resumeC` that come from the call itself and from the callee's `RetEnd`:

* `defOp`, `mapM_defsV`, **`defOps_eq`** (a call with virtual def registers has one fixed late
  def operand per def, in order), `defPairs_locs` (past `checkStatic`, the def locations are the
  def registers), **`hdef_of_static`** and **`hdef_of_q`** (`resume_premises_of_retEnd`'s
  `hdef`, from `checkStatic`'s fixed check / from `Q` at the `call` item);
* **`prefixHold_outs`**: `isel_resumeC`'s `PrefixHold rvals outs` for the call's outputs from the
  callee's `RetEnd` (its returned values held by its `rets`' uses, those uses in the registers
  that are the caller's def registers);
* **`relW_after_callee`**: `isel_resumeC`'s memory relation at the caller's slots after the
  return, from the caller's at the call and the callee's `MemRel` at its `rets`;
* **`realized_rets`**: the callee's epilogue up to its `ret` as a private segment
  (`rets_privP`, `CallSeg.prun_privF`, `CallSeg.realized_privSegS`).
-/

namespace Concurrency.CallRetResume
open Backend Backend.Proof Backend.Proof.Driver E2E

/-! ## The call's def operands -/

/-- The operand a virtual def register `(p, v)` of a call contributes. -/
def defOp (d : Reg × Reg) : Operand :=
  match d.2 with
  | .vreg n c => ⟨n, c, .def, .late, .fixed d.1⟩
  | _ => default

theorem defOp_eq {d : Reg × Reg} {n : Nat} {c : RegClass} (h : d.2 = .vreg n c) :
    defOp d = ⟨n, c, .def, .late, .fixed d.1⟩ := by
  simp [defOp, h]

theorem mapM_defsV : ∀ (D : List (Reg × Reg)), (∀ d ∈ D, ∃ n c, d.2 = .vreg n c) →
    ∀ (s : Array Operand),
    (D.mapM (fun (x : Reg × Reg) => do
        let r ← collectOp (OpSpec.fixedDef x.1) x.2; pure (x.1, r))).run s =
      .ok (D, s ++ (D.map defOp).toArray)
  | [], _, s => by simp
  | d :: D, hv, s => by
    obtain ⟨n, c, hd⟩ := hv d (List.mem_cons_self ..)
    obtain ⟨p, v⟩ := d
    simp only at hd
    subst hd
    simp only [List.mapM_cons, StateT.run_bind]
    have h1 : (collectOp (OpSpec.fixedDef p) (Reg.vreg n c)).run s =
        .ok (Reg.vreg n c, s.push ⟨n, c, .def, .late, .fixed p⟩) := rfl
    rw [h1, Driver.except_ok_bind, StateT.run_pure, Driver.except_pure, Driver.except_ok_bind,
      mapM_defsV D (fun d hd => hv d (List.mem_cons_of_mem _ hd)), Driver.except_ok_bind,
      StateT.run_pure, Driver.except_pure]
    simp [defOp]

/-- **The def operands of a call with virtual def registers**: one `defOp` per def, in order. -/
theorem defOps_eq {info : CallInfo} (hv : ∀ d ∈ info.defs, ∃ n c, d.2 = .vreg n c)
    {ops : Array Operand} (h : (MInst.call info).operands = .ok ops) :
    ops.toList.filter Operand.isDef = info.defs.map defOp := by
  obtain ⟨dest, uses, defs⟩ := info
  simp only at hv ⊢
  rw [operands_eq] at h
  have fin : ∀ (s0 : Array Operand), s0.toList.filter (·.kind == .def) = [] →
      ∀ (s1 : Array Operand) (a : List (Reg × Reg)),
      (uses.mapM (fun (x : Reg × Reg) => do
        let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run s0 = .ok (a, s1) →
      (s1 ++ (defs.map defOp).toArray) = ops →
      ops.toList.filter Operand.isDef = defs.map defOp := by
    intro s0 h0 s1 a hu he
    subst he
    have h1 := Kill.asm_mapM_use uses s0 s1 a hu
    rw [h0] at h1
    rw [Array.toList_append, List.filter_append, List.toList_toArray]
    have e1 : s1.toList.filter Operand.isDef = [] := h1
    rw [e1, List.nil_append, List.filter_eq_self]
    intro o ho
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ho
    obtain ⟨n, c, hdv⟩ := hv d hd
    simp [defOp_eq hdv, Operand.isDef]
  cases dest with
  | reg r =>
    simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure] at h
    cases hr : (collectOp OpSpec.use r).run #[] with
    | error e => rw [hr] at h; cases h
    | ok p0 =>
      obtain ⟨r', s0⟩ := p0
      have h0 : s0.toList.filter (·.kind == .def) = [] := by
        rw [Kill.asm_collect_kind hr (by simp [OpSpec.use])]; rfl
      rw [hr, Driver.except_ok_bind, Driver.except_pure, Driver.except_ok_bind] at h
      cases hu : (uses.mapM (fun (x : Reg × Reg) => do
          let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run s0 with
      | error e => rw [hu] at h; cases h
      | ok p =>
        obtain ⟨a, s1⟩ := p
        rw [hu, Driver.except_ok_bind, mapM_defsV defs hv, Driver.except_ok_bind] at h
        exact fin s0 h0 s1 a hu
          (by simpa only [Driver.except_pure, Driver.except_ok_bind, Except.ok.injEq] using h)
  | _ =>
    simp only [MInst.visitOperands, StateT.run_bind, StateT.run_pure, Driver.except_pure,
      Driver.except_ok_bind] at h
    cases hu : (uses.mapM (fun (x : Reg × Reg) => do
        let r ← collectOp (OpSpec.fixedUse x.2) x.1; pure (r, x.2))).run #[] with
    | error e => rw [hu] at h; cases h
    | ok p =>
      obtain ⟨a, s1⟩ := p
      rw [hu, Driver.except_ok_bind, mapM_defsV defs hv, Driver.except_ok_bind] at h
      exact fin #[] rfl s1 a hu
        (by simpa only [Driver.except_pure, Driver.except_ok_bind, Except.ok.injEq] using h)

/-- The location a fixed-constraint operand is allocated to. -/
def conLoc (o : Operand) : Loc :=
  match o.con with
  | .fixed r => .reg r
  | _ => .reg .xzr

theorem filter_zip_fst {L : List (Operand × Loc)} (P : Operand → Bool) :
    (L.filter (P ·.1)).map (·.1) = (L.map (·.1)).filter P := by
  induction L with
  | nil => rfl
  | cons q L ih => by_cases h : P q.1 <;> simp [h, ih]

theorem filter_snd_conLoc {L : List (Operand × Loc)} (P : Operand → Bool)
    (hfix : ∀ p ∈ L, P p.1 = true → ∀ r, p.1.con = .fixed r → p.2 = .reg r)
    (hcon : ∀ p ∈ L, P p.1 = true → ∃ r, p.1.con = .fixed r) :
    (L.filter (P ·.1)).map (·.2) = ((L.filter (P ·.1)).map (·.1)).map conLoc := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    have ih := ih (fun p hp => hfix p (List.mem_cons_of_mem _ hp))
      (fun p hp => hcon p (List.mem_cons_of_mem _ hp))
    by_cases h : P q.1 = true
    · obtain ⟨r, hr⟩ := hcon q (List.mem_cons_self ..) h
      simp [h, ih, conLoc, hr, hfix q (List.mem_cons_self ..) h r hr]
    · simp [h, ih]

/-- **The def locations of a call** (with virtual def registers, past `checkStatic`): the
registers of `info.defs`, in order. -/
theorem defPairs_locs {c : CheckCtx} {wh : String} {info : CallInfo} {ops : Array Operand}
    {allocs : Array Loc} {clob : List Reg}
    (hv : ∀ d ∈ info.defs, ∃ n c, d.2 = .vreg n c)
    (hops : (MInst.call info).operands = .ok ops)
    (hs : c.checkStatic wh ops allocs clob = .ok ()) :
    (defPairs ops allocs).map (·.2) = info.defs.map (fun d => Loc.reg d.1) := by
  obtain ⟨hsz, hfix, -, -⟩ := checkStatic_facts hs
  have hE := defOps_eq hv hops
  have hfst : (defPairs ops allocs).map (·.1) = ops.toList.filter Operand.isDef := by
    unfold defPairs
    rw [filter_zip_fst Operand.isDef, Array.toList_zip, List.map_fst_zip (by simp [hsz])]
  have hmemD : ∀ o ∈ ops.toList.filter Operand.isDef, ∃ r, o.con = .fixed r := by
    intro o ho
    rw [hE] at ho
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ho
    obtain ⟨n, cl, hdv⟩ := hv d hd
    exact ⟨d.1, by simp [defOp_eq hdv]⟩
  unfold defPairs
  rw [filter_snd_conLoc Operand.isDef (fun p hp _ r hr => (hfix p hp).2 r hr) (fun p hp hd => ?_)]
  · unfold defPairs at hfst
    rw [hfst, hE, List.map_map]
    refine List.map_congr_left fun d hd => ?_
    obtain ⟨n, cl, hdv⟩ := hv d hd
    simp [conLoc, defOp_eq hdv]
  · refine hmemD p.1 (List.mem_filter.mpr ⟨?_, hd⟩)
    have := List.mem_map_of_mem (f := (·.1)) hp
    rw [Array.toList_zip, List.map_fst_zip (by simp [hsz])] at this
    exact this

/-- **`hdef` from the call's operands** (step (1)): every def register of a call whose def
registers are virtual is the location of a late def operand, by `checkStatic`'s fixed check. -/
theorem hdef_of_static {c : CheckCtx} {wh : String} {info : CallInfo} {ops : Array Operand}
    {allocs : Array Loc} {clob : List Reg}
    (hv : ∀ d ∈ info.defs, ∃ n c, d.2 = .vreg n c)
    (hops : (MInst.call info).operands = .ok ops)
    (hs : c.checkStatic wh ops allocs clob = .ok ()) :
    ∀ d ∈ info.defs, ∃ q ∈ defPairs ops allocs, q.1.isLate = true ∧ q.2 = .reg d.1 := by
  obtain ⟨hsz, hfix, -, -⟩ := checkStatic_facts hs
  intro d hd
  obtain ⟨n, cl, hdv⟩ := hv d hd
  have hm : defOp d ∈ ops.toList := by
    have := List.mem_map_of_mem (f := defOp) hd
    rw [← defOps_eq hv hops] at this
    exact (List.mem_filter.mp this).1
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hm
  have hia : i < allocs.size := by simp at hi; omega
  have hz : (ops.toList[i], allocs[i]) ∈ (ops.zip allocs).toList := by
    rw [Array.toList_zip]
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  rw [hget, defOp_eq hdv] at hz
  refine ⟨_, List.mem_filter.mpr ⟨hz, by simp [Operand.isDef]⟩, by simp [Operand.isLate], ?_⟩
  exact (hfix _ hz).2 d.1 rfl

/-- **`hdef` at a `call` item from `Q`** (`hdef_of_static` with the item's static check,
`op_checked`; a forwarding block's only instruction is a `jump`, no `call`). -/
theorem hdef_of_q {R : RL} {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {info : CallInfo}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hv : ∀ d ∈ info.defs, ∃ n c, d.2 = .vreg n c) {ops : Array Operand}
    (hops : (MInst.call info).operands = .ok ops) :
    ∀ d ∈ info.defs, ∃ q ∈ defPairs ops allocs, q.1.isLate = true ∧ q.2 = .reg d.1 := by
  rcases Q.cases hq with hqs | ⟨vb', allocs', regs', i', x, -, hvb', he, -, -, hins, hasg', -⟩
  rotate_left
  · rw [hvb] at hvb'
    cases hvb'
    simp only [RItem.op.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [hins] at hi
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact absurd (ArmAllocThread.assign_jump hasg').1 (by simp)
  obtain ⟨j, vb0, items, pre, code, X, ps1, psm, ps2, x, hvb0, hit, hsplit, hchk, -⟩ := hqs
  rw [hvb] at hvb0
  cases hvb0
  obtain ⟨c, wh, i2, ops2, hi2, hops2, hstat, -⟩ := op_checked hchk
  rw [hi] at hi2
  cases hi2
  rw [hops] at hops2
  cases hops2
  exact hdef_of_static hv hops hstat

/-! ## The returned values and the memory relation after the return -/

/-- **`PrefixHold` of the call's outputs from the callee's returned values** (step (1)): the
callee's `rets` put value `j` in register `q_j` (`hus`, `RetEnd`'s last clause) holding its
`j`-th returned value (`hpre`); the caller's `j`-th def register is `q_j` (`hreg`, the ABI). -/
theorem prefixHold_outs {c : CheckCtx} {wh : String} {info : CallInfo} {ops : Array Operand}
    {allocs : Array Loc} {clob : List Reg}
    (hv : ∀ d ∈ info.defs, ∃ n c, d.2 = .vreg n c)
    (hops : (MInst.call info).operands = .ok ops)
    (hs : c.checkStatic wh ops allocs clob = .ok ()) (fr : RAFrame) {y : Arm.ArmState}
    {vals : List Clif.Val} {ys : List CV} {us : List (Reg × Reg)}
    (hpre : PrefixHold vals ys)
    (hus : ∀ (j : Nat) (v q : Reg) (u : CV), us[j]? = some (v, q) → ys[j]? = some u →
      regVal y q = u)
    (hreg : ∀ (j : Nat) (d : Reg × Reg), info.defs[j]? = some d → ∃ v, us[j]? = some (v, d.1))
    (hlen : vals.length ≤ info.defs.length) :
    PrefixHold vals ((defPairs ops allocs).map fun p => locVal fr y p.2) := by
  have hL : (defPairs ops allocs).map (fun p => locVal fr y p.2) =
      info.defs.map (fun d => regVal y d.1) := by
    have h := congrArg (List.map (locVal fr y)) (defPairs_locs hv hops hs)
    simpa [List.map_map, Function.comp_def, locVal] using h
  rw [hL]
  refine ⟨by simpa using hlen, fun j v x hvj hxj => ?_⟩
  obtain ⟨d, hd, rfl⟩ : ∃ d, info.defs[j]? = some d ∧ x = regVal y d.1 := by
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hxj
    obtain ⟨d, hd, rfl⟩ := hxj
    exact ⟨d, hd, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, ys[j]? = some u := by
    have hj : j < vals.length := (List.getElem?_eq_some_iff.mp hvj).1
    exact ⟨ys[j]'(by have := hpre.1; omega), List.getElem?_eq_getElem _⟩
  obtain ⟨v', hv'⟩ := hreg j d hd
  rw [hus j v' d.1 u hv' hu]
  exact hpre.2 j v u hvj hu

/-- **The caller's memory relation after the callee's return** (step (1)): the callee's CLIF
memory at its `rets` relates (`MemRel FB`) to its world `wB`; the state `y` after the return
has `wB`'s memory outside `FB` and the caller's `sp`; the memory after the CLIF return (the
callee's slots freed) has only allocations live at the call. -/
theorem relW_after_callee {Γ : E2E.Rel} {f : Clif.Function} {c : BitVec 64}
    {slots : List (Clif.SlotId × Nat)} {cm cmB : Clif.Mem} {w wB y : Arm.ArmState}
    {FB : BitVec 64 → Prop} {bases : List Nat}
    (hA : RelW Γ f c slots cm w) (hB : MemRel FB Γ.syms cmB wB)
    (hval : ∀ a n, ((cmB.free bases).leave).valid a n = true → cm.valid a n = true)
    (hmem : ∀ a, ¬ FB a → y.mem a = wB.mem a) (hsp : spv y = spv w)
    (herr : Arm.r .ERR y = .None) :
    RelW Γ f c slots ((cmB.free bases).leave) y := by
  obtain ⟨⟨hM, hS, hO⟩, hc, -⟩ := hA
  have hvB : ∀ a n, ((cmB.free bases).leave).valid a n = true → cmB.valid a n = true := by
    intro a n h
    rw [Clif.Mem.leave_valid] at h
    simp only [Clif.Mem.valid, Clif.Mem.free, List.any_eq_true, List.mem_filter] at h ⊢
    obtain ⟨x, ⟨hx, -⟩, hx2⟩ := h
    exact ⟨x, hx, hx2⟩
  refine ⟨⟨⟨fun a b hv hb => ?_, fun a n hv => hM.valid a n (hval a n hv), ?_⟩, ?_, ?_⟩,
    hsp.trans hc, herr⟩
  · have hv' := hvB a 1 hv
    have hb' : cmB.bytes a = some b := by simpa [Clif.Mem.free] using hb
    have hF : ¬ FB (BitVec.ofNat 64 a) := by
      simpa using (hB.valid a 1 hv').2 0 Nat.zero_lt_one
    have := hB.bytes a b hv' hb'
    unfold Arm.read_mem at this ⊢
    rw [← this]
    simp only [Arm.read_store, hmem _ hF]
  · simpa [Clif.Mem.free] using hB.symbols
  · simpa [Rel.slotReg, hsp] using hS
  · exact ⟨hO.1, hsp ▸ hO.2.1, fun a n hv k hk j hj => hsp ▸ hO.2.2 a n (hval a n hv) k hk j hj⟩

/-! ## The epilogue as a private segment -/

open Arm ArmThread ArmAllocThread CallSeg ClifThread ArmInstFoot in
/-- **The epilogue and `ret` from a `rets` item realize nothing, privately** (step (1)): from
`Q` at a `rets` item, the epilogue and `ret` take `n` steps of `R.step` (`rets_privP`, with its
end facts); every precise run of a machine `g` agreeing with `R` (`AgreesAt`) of fewer steps
(before the `ret`, which the linked machine steps on its own) follows `R.step` and realizes
every event-free CLIF run, with `R`'s private set. -/
theorem realized_rets {R : RL} (hR : R.Wf) {ra : BitVec 64}
    (hent : AbiCall R.fb R.base ra R.s0) {g : ArmState → ArmState} (hg : AgreesAt R g)
    {s : ArmState} {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV}
    {w : ArmState} (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock}
    {us : List (Reg × Reg)} (hvb : R.vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some (.rets us)) :
    ∃ n, 0 < n ∧ Arm.r .PC (iterN R.step n s) = ra ∧ Arm.r .ERR (iterN R.step n s) = .None ∧
      spv (iterN R.step n s) = spv R.s0 ∧ (iterN R.step n s).mem = s.mem ∧
      (iterN R.step n s).program = s.program ∧
      ∀ {L : List Lab} {mon : Mon} {t' : ArmState × Mon}, L.length < n →
        PRun Policy.arm g (OkPriv R) (s, mon) L t' →
        t'.1 = iterN R.step L.length s ∧
        ∀ {env : Clif.Env} {p : Clif.Program} {c c' : ClifThread.TState}
          {trS : List (List (Prog.Ev SKind BVal))}, (∀ x ∈ trS, x = []) →
          ClifCStepTerm.CRun env p c trS c' →
          CallCompose.Realized env p (PrivA R) L L.length c c' := by
  obtain ⟨n, hpath, hpc, herr, hsp, hmem, hprog, -, hnr, hn0, -⟩ := rets_privP hR hent hq hvb hi
  refine ⟨n, hn0, hpc, herr, hsp, hmem, hprog, fun {L mon t'} hlt hr => ?_⟩
  have hstep : ∀ i < L.length, (∀ e ∈ stepEvs (iterN R.step i s), R.F e.addr) ∧
      NoStx (iterN R.step i s) ∧ g (iterN R.step i s) = R.step (iterN R.step i s) := by
    intro i hi
    obtain ⟨⟨hF, hx⟩, hpg, -⟩ := hpath i (by omega)
    exact ⟨hF, hx, hg _ hpg (hnr i (by omega))⟩
  obtain ⟨h1, hev, hk⟩ := prun_privF hr hstep
  refine ⟨h1, fun {env p c c' trS} hS hrun => ?_⟩
  exact realized_privSegS (fun _ h => h) hev (fun i hi => (hstep i hi).1)
    (fun l hl => (hk l hl).2) hS hrun

end Concurrency.CallRetResume
