import FV.E2E.RegLevelNext

/-!
# Calls and symbol addresses on the machine (M6)

The machine `ArmStepX` runs the callee of `bl`/`blr` as one hooked step (`H.call`) and the
relocated address pairs `adrp`/`ldr got` and `adrp`/`add lo12` as two hooked steps (`X.sym`).

* `CalleeOk F K X H S`: the callee contract of an activation whose addresses outside the world
  are `F` and whose callees may use the `K` bytes below `sp` (the dead stack), for its call
  sites `S`: the hooked call (`callExec H`) satisfies `CallSoundCtl` against `csem`'s call clause (`X.call`: the AAPCS64
  contract — results, preserved registers, `sp` kept, the world as `X.call` says outside `F`,
  the frame kept outside the dead stack), returns to the next instruction, and `X.call` keeps
  the program and yields no model error.
* `realizes_call`, `realizes_symAddr`: the `op`/`next` case of `Realizes` for calls and
  `loadExtNameGot/Near`, instances of `realizes_op_coreX`.
-/

namespace Backend.Proof

open Backend E2E

/-- The instruction of the laid-out function at the pc of a state at line `j`. -/
theorem insnAt_pc {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {i : Insn}
    {t : Option Clif.TrapCode} (hj : R.L[j]? = some (.ins i t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    insnAt R.fa (progBase s) (Arm.r .PC s) = some i := by
  obtain ⟨_, w, hw, hk⟩ := FnAsm.layout_word hR.layout hR.lm hj rfl
  have hne : R.fb.words.toList ≠ [] := by
    intro h
    have : R.fb.words.size = 0 := by simpa using congrArg List.length h
    simp [this] at hk
  have hb : progBase s = R.base := progBase_eq (by rw [hprog]; rfl) hne
  have hsum := layout_sum hR.layout
  have hfit := hR.fit
  rw [hb, hpc]
  exact insnAt_line (by simp only [RL.L] at *; omega) hj

/-! The machine at a hooked line: one step. -/

theorem step_bl {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {t : Option Clif.TrapCode}
    {n : String} {off : Int} {r rd rn : Reg} (hj : R.L[j]? = some (.ins (.bl n) t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    R.step s = R.H.call (some n) s := by
  simp only [RL.step, ArmStepX, insnAt_pc hR hj hprog hpc]

theorem step_blr {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {t : Option Clif.TrapCode}
    {n : String} {off : Int} {r rd rn : Reg} (hj : R.L[j]? = some (.ins (.blr r) t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    R.step s = R.H.call none s := by
  simp only [RL.step, ArmStepX, insnAt_pc hR hj hprog hpc]

theorem step_adrpGot {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {t : Option Clif.TrapCode}
    {n : String} {off : Int} {r rd rn : Reg} (hj : R.L[j]? = some (.ins (.adrpGot rd n) t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    R.step s = Arm.w .PC (Arm.r .PC s + 4) (Arm.w (.GPR (rd.encZR.toOption.getD 31#5)) (R.X.sym n 0) s) := by
  simp only [RL.step, ArmStepX, insnAt_pc hR hj hprog hpc]

theorem step_ldrGotLo12 {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {t : Option Clif.TrapCode}
    {n : String} {off : Int} {r rd rn : Reg} (hj : R.L[j]? = some (.ins (.ldrGotLo12 rd rn n) t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    R.step s = Arm.w .PC (Arm.r .PC s + 4) s := by
  simp only [RL.step, ArmStepX, insnAt_pc hR hj hprog hpc]

theorem step_adrp {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {t : Option Clif.TrapCode}
    {n : String} {off : Int} {r rd rn : Reg} (hj : R.L[j]? = some (.ins (.adrp rd n off) t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    R.step s = Arm.w .PC (Arm.r .PC s + 4) (Arm.w (.GPR (rd.encZR.toOption.getD 31#5)) (R.X.sym n off) s) := by
  simp only [RL.step, ArmStepX, insnAt_pc hR hj hprog hpc]

theorem step_addLo12 {R : RL} (hR : R.Wf) {s : Arm.ArmState} {j : Nat} {t : Option Clif.TrapCode}
    {n : String} {off : Int} {r rd rn : Reg} (hj : R.L[j]? = some (.ins (.addLo12 rd rn n off) t))
    (hprog : s.program = R.fb.program R.base) (hpc : Arm.r .PC s = R.pcOf j) :
    R.step s = Arm.w .PC (Arm.r .PC s + 4) s := by
  simp only [RL.step, ArmStepX, insnAt_pc hR hj hprog hpc]

/-- `Q` at a run state gives the store/world relation. -/
theorem q_stRel {R : RL} {s : Arm.ArmState} {b : Nat} {its : List RItem} {m : Loc → CV}
    {w : Arm.ArmState} (hq : Q R s (.run ⟨b, its, m, w⟩)) : StRel R s m w := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hst⟩ := hq
  exact hst

/-- The pc of line `j + 1` after an instruction line `j`. -/
theorem pcOf_succ {R : RL} {j : Nat} {i : Insn} {t : Option Clif.TrapCode}
    (hj : R.L[j]? = some (.ins i t)) : R.pcOf (j + 1) = R.pcOf j + 4 := by
  simp only [RL.pcOf]
  rw [lineOffset_succ _ _ _ hj, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [Line.size, BitVec.toNat_add]

theorem drop_get1 {L ls T : List Line} {j : Nat} {a b : Line} (hd : L.drop j = a :: b :: ls ++ T) :
    L[j + 1]? = some b := by
  have := congrArg (·[1]?) hd
  simpa [List.getElem?_drop] using this

/-! ## Calls -/

open Classical in
/-- The callee as the machine runs it (`bl name` / `blr`; also the call of a `try_call`), from a
state whose `sp` is 16-byte aligned (AAPCS64; every call site of the body is). -/
noncomputable def callExec (H : ArmHooks) : MInst → Arm.ArmState → Option Arm.ArmState
  | .call info, s => if Arm.CheckSPAlignment s then
      some (H.call (match info.dest with | .sym n => some n | .reg _ => none) s) else none
  | .tryCall info _, s => if Arm.CheckSPAlignment s then
      some (H.call (match info.dest with | .sym n => some n | .reg _ => none) s) else none
  | _, _ => none

/-- The call sites of `vc`: the `CallInfo` of a `call` or of a `try_call`'s call in one of its
blocks. -/
def _root_.Backend.VCode.CallSite (vc : VCode) (info : CallInfo) : Prop :=
  ∃ (b : Nat) (vb : VBlock) (k : Nat), vc.blocks[b]? = some vb ∧
    (vb.insts[k]? = some (MInst.call info) ∨ ∃ ti, vb.insts[k]? = some (MInst.tryCall info ti))

/-- **The callee contract** of an activation whose addresses outside the world are `F`, with a
stack budget of `K` bytes for its callees, for its call sites `S` (AAPCS64, stated for the
machine's hook `H` and `csem`'s callee semantics `X.call`, which does not depend on the function
context):

* `os`: `CallSoundCtl` of every call of `S` against the hooked callee: from every state whose `K` bytes
  below `sp` (the dead stack, where the callee pushes its frame: the return address, the
  callee-saved registers, spills) are outside the world, the results are in the fixed result
  registers, the world is the one `X.call` computes (memory compared outside `F`, which contains
  the dead stack), allocatable registers outside the clobber set are preserved, the low 64 bits
  of v8–v15 are preserved, `sp` is kept and the bytes of `F` outside the dead stack untouched;
* `pc`: the callee returns to the instruction after the call (from an aligned `sp`);
* `ext`: `X.call` keeps the program and yields no model error.

The dead stack makes the contract satisfiable by callees that save state-dependent bytes below
`sp` (`calleeOk_witness`, `FV/E2E/NonVacuity.lean`): the former contract compared all memory
outside `F`, and no callee pushing its return address could meet it. The call sites `S` (the
theorems take the compiled code's, `VCode.CallSite`) make it satisfiable by callees that return
values: over every `CallInfo` it would also constrain calls whose def registers are not the
callee's return registers (e.g. a def in x19, which another call of the same callee must
preserve). -/
structure CalleeOk (F : BitVec 64 → Prop) (K : Nat) (X : ExtSem) (H : ArmHooks)
    (S : CallInfo → Prop) : Prop where
  os : ∀ ctx info, S info → CallSoundCtl F K (callExec H) (csem F ctx X) (.call info) .next
  pc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (H.call d s) = Arm.r .PC s + 4
  ext : ∀ d uses w outs w', X.call d uses w = some (outs, w') → Arm.r .ERR w = .None →
    Arm.r .ERR w' = .None ∧ w'.program = w.program

/-- **The callee contract relative to the kept addresses `G`** of the activation entered in
`s0`: `CalleeOk` whose operand-view obligation (`CallSoundCtlG`) is required only at the states
that keep `G` (`StRel.gkeep`), and for the calls the VCode run reaches (`csemV gv`: a call through
the GOT, `gv t n`, only with `n`'s address as its target). `CalleeOk` gives it (`CalleeOk.g`). -/
structure CalleeOkG (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop) (s0 : Arm.ArmState)
    (Pc : BitVec 64 → MInst → Prop) (X : ExtSem) (H : ArmHooks) (S : CallInfo → Prop)
    (gv : Nat → String → Prop) : Prop where
  os : ∀ ctx info, S info → CallSoundCtlG F K G s0 Pc (callExec H) (csemV gv F ctx X) (.call info) .next
  pc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (H.call d s) = Arm.r .PC s + 4
  ext : ∀ d uses w outs w', X.call d uses w = some (outs, w') → Arm.r .ERR w = .None →
    Arm.r .ERR w' = .None ∧ w'.program = w.program

/-- `CallSoundCtlG` of `csem` gives that of `csemV gv` (a guarded semantics). -/
theorem CallSoundCtlG.v {F : BitVec 64 → Prop} {K : Nat} {G : BitVec 64 → Prop} {s0 : Arm.ArmState}
    {Pc : BitVec 64 → MInst → Prop} {exec : MInst → Arm.ArmState → Option Arm.ArmState}
    {ctx : FnCtx} {X : ExtSem} {i : MInst} {ctl : Ctl}
    (h : CallSoundCtlG F K G s0 Pc exec (csem F ctx X) i ctl) (gv : Nat → String → Prop) :
    CallSoundCtlG F K G s0 Pc exec (csemV gv F ctx X) i ctl :=
  fun s h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg hp hw hal herr hsem =>
    h s h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg hp hw hal herr (csemV_sub hsem)

theorem CalleeOk.g {F : BitVec 64 → Prop} {K : Nat} {X : ExtSem} {H : ArmHooks}
    {S : CallInfo → Prop} (h : CalleeOk F K X H S) (G : BitVec 64 → Prop) (s0 : Arm.ArmState)
    (Pc : BitVec 64 → MInst → Prop) (gv : Nat → String → Prop) : CalleeOkG F K G s0 Pc X H S gv :=
  ⟨fun ctx info hs => ((h.os ctx info hs).g G s0 Pc).v gv, h.pc, h.ext⟩

theorem ftStep_call {x : Insn} (hx : (∃ n, x = .bl n) ∨ (∃ r, x = .blr r)) (n1 n2 : Option Line) :
    ftStep (.ins x none) n1 n2 = ([.ins x none], 1) := by
  have hc : x.condTarget? = none := by rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  have hb : ∀ y, x ≠ .b y := by rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> intro y h <;> cases h
  unfold ftStep
  split
  · rename_i h
    simp only [Line.ins.injEq] at h
    exact absurd h.1 (hb _)
  · split
    · rename_i heq _
      simp only [Line.ins.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [hc]
    · rfl

theorem regs_of_map : ∀ {a b : List Reg}, a.map Loc.reg = b.map Loc.reg → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq, Loc.reg.injEq] at h
    rw [h.1, regs_of_map h.2]

theorem regsArr_of_map {a b : Array Reg} (h : a.map Loc.reg = b.map Loc.reg) : a = b := by
  have h' := congrArg Array.toList h
  simp only [Array.toList_map] at h'
  exact Array.toList_inj.mp (regs_of_map h')

/-- The pc of a `Q` state at a call item (`call` or `try_call`) is the call instruction of the
item's allocated form (`CallAt`). -/
theorem callAt_of_q {R : RL} {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩)) {vb : VBlock} {i : MInst}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hcall : ∀ regs i', i.assign regs = .ok i' → (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us) ∧
      ∃ x ls, (∀ ps, i'.lines R.ctx ps = .ok (.ins x none :: ls, ps)) ∧
        ((∃ n, x = .bl n) ∨ (∃ r, x = .blr r)) ∧ i'.callInsn? = some x) :
    ∀ regs i', allocs = regs.map Loc.reg → i.assign regs = .ok i' →
      CallAt R.fa R.base (Arm.r .PC s) i' := by
  intro regs0 i0 hal0 hasg0
  obtain ⟨j0, items, pre, regs, i', c1, c2, ls1, ls2, ps1, psm, ps2, T, cc, wh, ops, hal, -, -, hasg,
    hc1', -, -, -, -, h1, -, -, hdrop, hpc, -⟩ := q_op hq hvb hi
  rw [hal] at hal0
  obtain rfl := regsArr_of_map hal0
  rw [hasg] at hasg0
  injection hasg0 with e
  subst e
  obtain ⟨hna, hnr, x, ls, hl, hx, hxi⟩ := hcall regs i' hasg
  rcases hc1' with ⟨rfl, -, -⟩ | ⟨ds, rfl, -⟩ | ⟨us, rfl, -⟩
  · have h1' := codeLinesE_single h1
    rw [hl ps1] at h1'
    simp only [Except.ok.injEq, Prod.mk.injEq] at h1'
    obtain ⟨rfl, -⟩ := h1'
    rw [List.cons_append, ftList_cons, ftStep_call hx] at hdrop
    simp only [List.drop_one, List.tail_cons, List.singleton_append, List.cons_append] at hdrop
    rw [relaxLines_cons, relaxLine_of_none (by rcases hx with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl),
      List.singleton_append, List.cons_append] at hdrop
    have hj : R.L[j0]? = some (.ins x none) := drop_get (Z := []) (by rw [hdrop]; rfl)
    exact ⟨j0, x, none, hj, hxi, hpc⟩
  · exact absurd rfl (hna ds)
  · exact absurd rfl (hnr us)

/-- The lines of an allocated `call`: one `bl`/`blr`. -/
theorem call_hcall {ctx : FnCtx} {info : CallInfo} :
    ∀ regs i', (MInst.call info).assign regs = .ok i' → (∀ ds, i' ≠ .args ds) ∧
      (∀ us, i' ≠ .rets us) ∧ ∃ x ls, (∀ ps, i'.lines ctx ps = .ok (.ins x none :: ls, ps)) ∧
        ((∃ n, x = .bl n) ∨ (∃ r, x = .blr r)) ∧ i'.callInsn? = some x := by
  intro regs i' hasg
  obtain ⟨ic, rfl⟩ := assign_call_form hasg
  refine ⟨fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h, ?_⟩
  cases hd : ic.dest with
  | sym n => exact ⟨.bl n, [], fun ps => by simp [MInst.lines, hd, pure, Except.pure], .inl ⟨n, rfl⟩,
      by simp [MInst.callInsn?, hd]⟩
  | reg r => exact ⟨.blr r, [], fun ps => by simp [MInst.lines, hd, pure, Except.pure], .inr ⟨r, rfl⟩,
      by simp [MInst.callInsn?, hd]⟩

/-- The lines of an allocated `try_call`: a `bl`/`blr`, then the branch to the continuation. -/
theorem tryCall_hcall {ctx : FnCtx} {info : CallInfo} {ti : TryInfo} :
    ∀ regs i', (MInst.tryCall info ti).assign regs = .ok i' → (∀ ds, i' ≠ .args ds) ∧
      (∀ us, i' ≠ .rets us) ∧ ∃ x ls, (∀ ps, i'.lines ctx ps = .ok (.ins x none :: ls, ps)) ∧
        ((∃ n, x = .bl n) ∨ (∃ r, x = .blr r)) ∧ i'.callInsn? = some x := by
  intro regs i' hasg
  obtain ⟨ic, rfl, -⟩ := (assign_call_tryCall info regs).2 ti i' hasg
  refine ⟨fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h, ?_⟩
  cases hd : ic.dest with
  | sym n => exact ⟨.bl n, _, fun ps => by simp [MInst.lines, hd, pure, Except.pure]; rfl, .inl ⟨n, rfl⟩,
      by simp [MInst.callInsn?, hd]⟩
  | reg r => exact ⟨.blr r, _, fun ps => by simp [MInst.lines, hd, pure, Except.pure]; rfl, .inr ⟨r, rfl⟩,
      by simp [MInst.callInsn?, hd]⟩

/-- The register an allocated call goes through, when the call's target is a vreg: the target's
allocation `regs[0]`. -/
theorem assign_call_dest {info ic : CallInfo} {regs : Array Reg} {r : Reg}
    (h : (MInst.call info).assign regs = .ok (.call ic)) (hr : ic.dest = .reg r)
    (hv : ∀ r', info.dest = .reg r' → ∃ t c, r' = .vreg t c) : regs[0]? = some r := by
  obtain ⟨d, us, ds⟩ := info
  cases d with
  | sym n =>
    unfold MInst.assign at h
    simp only [MInst.visitOperands, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      StateT.run, get, set, getThe, MonadStateOf.get, MonadStateOf.set] at h
    split at h
    · cases h
    · rename_i v hv'
      split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        split at hv'
        · cases hv'
        · split at hv'
          · cases hv'
          · simp only [Except.ok.injEq] at hv'
            subst hv'
            simp only [MInst.call.injEq] at h
            subst h
            simp at hr
  | reg r' =>
    obtain ⟨t, c, rfl⟩ := hv r' rfl
    unfold MInst.assign at h
    simp only [MInst.visitOperands, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      StateT.run, get, set, getThe, MonadStateOf.get, StateT.get, MonadStateOf.set, StateT.set] at h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        cases h0 : regs[0]? with
        | none => rw [h0] at hv; simp [throw, throwThe, MonadExceptOf.throw, StateT.lift] at hv
        | some r0 =>
          rw [h0] at hv
          simp only [StateT.pure, pure, Except.pure] at hv
          split at hv
          · cases hv
          · split at hv
            · cases hv
            · simp only [Except.ok.injEq] at hv
              subst hv
              simp only [MInst.call.injEq] at h
              subst h
              simp at hr
              rw [hr]

/-- The registers of an allocation the checker accepts are allocatable. -/
theorem checkStatic_allocatable {c : CheckCtx} {wh : String} {ops : Array Operand}
    {regs : Array Reg} {clob : List Reg} (h : c.checkStatic wh ops (regs.map Loc.reg) clob = .ok ())
    {k : Nat} {r : Reg} (hk : regs[k]? = some r) : r.allocatable = true := by
  obtain ⟨hsz, hloc, -, -⟩ := checkStatic_facts h
  have hk' : k < ops.size := by
    rw [hsz, Array.size_map]; exact (Array.getElem?_eq_some_iff.1 hk).1
  have hm : (ops[k], Loc.reg r) ∈ (ops.zip (regs.map Loc.reg)).toList := by
    apply List.mem_of_getElem? (i := k)
    rw [Array.toList_zip, List.getElem?_zip_eq_some]
    simp [hk]
  exact (locOk_reg (hloc _ hm).1).2

/-- The `blr` of an allocated call whose target is an int vreg (`hdest`): not through `xzr`. -/
theorem callDest_ne_xzr {info ic : CallInfo} {regs : Array Reg} {c : CheckCtx} {wh : String}
    {ops : Array Operand} {clob : List Reg}
    (hdest : ∀ r, info.dest = .reg r → ∃ t, r = .vreg t .int)
    (hst : c.checkStatic wh ops (regs.map Loc.reg) clob = .ok ())
    (hasg : (MInst.call info).assign regs = .ok (.call ic)) {r : Reg} (hr : ic.dest = .reg r) :
    r ≠ .xzr := by
  have h0 := assign_call_dest hasg hr fun r' e => by
    obtain ⟨t, e'⟩ := hdest r' e; exact ⟨t, .int, e'⟩
  have ha := checkStatic_allocatable hst h0
  rintro rfl
  exact absurd ha (by decide)

/-- **A call on the machine**: one hooked step, from a state satisfying `GoodX` (its `blr` is not
through `xzr` when the calls through a register are through int vregs, `VCode.DestsInt`). -/
theorem realizes_call {R : RL} (hR : R.Wf)
    (hC : CalleeOkG R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {info : CallInfo} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.call info))
    (hops : (MInst.call info).operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem (.call info) (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have hsem := R.sem_csem hsem
    simp only [csem, Option.map_eq_some_iff] at hsem
    obtain ⟨⟨o, w2⟩, hx, he⟩ := hsem
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact hC.ext _ _ _ _ _ hx herr
  -- the callee contract's premise at the call state
  have hpre : R.CallPre s := by
    obtain ⟨-, -, -, regs, i', -, -, -, -, -, -, -, -, cc, wh, ops', hal, -, -, hasg, -, hops', hstat,
      -, -, -, -, -, -, -, hst⟩ := q_op hq hvb hi
    rw [hops] at hops'; cases hops'
    have hm : ∀ r, r.allocatable = true → m (.reg r) = regVal s r := fun r hr =>
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
    have hsemU := hsem
    rw [hal, useVals_of_store hstat hm] at hsemU
    exact ⟨R.ctx, .call info, .next, ⟨info, ⟨b, vb, k, hvb, .inl hi⟩, .inl rfl⟩, by rw [hst.sp]; exact RL.K_le hR,
      fun a ha => by rw [hst.sp] at ha; exact RL.below_F ha, hst.gkeep, cc, wh, ops, regs, i', w,
      outs, w', hops, hstat, hasg, callAt_of_q hq hvb hi call_hcall regs i' hal hasg, hst.world,
      hst.align, hst.err, hsemU⟩
  refine realizes_op_coreX hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => callExec R.H)
    (fun _ => RL.callAtG hR (hC.os R.ctx info ⟨b, vb, k, hvb, .inl hi⟩) (q_stRel hq).sp
      (q_stRel hq).gkeep fun i' ⟨regs, hal, hasg⟩ => callAt_of_q hq hvb hi call_hcall regs i' hal hasg)
    hpre (fun regs i' hasg _ hcs => ?_) hW'
  obtain ⟨info', rfl⟩ := assign_call_form hasg
  have hgen : ∀ x, (∀ ps, (MInst.call info').lines R.ctx ps = .ok ([.ins x], ps)) →
      (Line.ins x).plain = true → x.tlsTail = false → (∀ rd rn n, x ≠ .ldrGotLo12 rd rn n) →
      (∀ r, x = .blr r → R.vc.DestsInt → r ≠ .xzr) →
      (∀ s j, R.L[j]? = some (.ins x) → s.program = R.fb.program R.base →
        Arm.r .PC s = R.pcOf j → R.step s = R.H.call
          (match info'.dest with | .sym n => some n | .reg _ => none) s) →
      ∃ ls1, (∀ ps, (MInst.call info').lines R.ctx ps = .ok (ls1, ps)) ∧
        (∀ ln ∈ ls1, ln.plain = true) ∧ (∀ ds, MInst.call info' ≠ .args ds) ∧
        (∀ us, MInst.call info' ≠ .rets us) ∧
        RunsAs R (fun _ => callExec R.H) (.call info') ls1 R.CallPre := by
    intro x hl1 hpl hxt hxg hxz hstep
    refine ⟨[.ins x], hl1, fun ln hln => by simp only [List.mem_singleton] at hln; subst hln; exact hpl,
      fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h,
      fun j T s _ _ s' hd hst hpc hpre' hex => ?_⟩
    have hj : R.L[j]? = some (.ins x) := drop_get (Z := []) hd
    simp only [callExec] at hex
    split at hex
    · rename_i hal
      simp only [Option.some.injEq] at hex
      subst hex
      have hs := hstep s j hj hst.prog hpc
      refine ⟨1, by simp only [iterN]; exact hs, ?_, fun i hi => ?_⟩
      · rw [hC.pc _ _ hst.err hal, hpc, List.length_singleton, pcOf_succ hj]
      · obtain rfl : i = 0 := by omega
        show R.GoodX s
        exact RL.goodX_line hR hj hpc hxt (RL.good_of_sp hst.sp) hst.err hst.prog
          (RL.nextOk_pc4 (by rw [hs, hC.pc _ _ hst.err hal]))
          (fun rd rn n e => absurd e (hxg rd rn n)) (fun r e => ⟨hxz r e, hst.code⟩) fun _ => hpre'
    · cases hex
  cases hd : info'.dest with
  | sym n =>
    refine hgen (.bl n) (fun ps => by simp [MInst.lines, hd, pure, Except.pure])
      (by simp [Line.plain, Insn.condTarget?]) rfl (fun _ _ _ h => by cases h)
      (fun _ h => by cases h) fun s j hj hprog hpc => ?_
    rw [step_bl (off := 0) (r := .xzr) (rd := .xzr) (rn := .xzr) hR hj hprog hpc, hd]
  | reg r =>
    obtain ⟨c, wh, hcs⟩ := hcs
    have hne : R.vc.DestsInt → r ≠ .xzr := fun hD =>
      callDest_ne_xzr (hD b vb k info hvb (.inl hi)) hcs hasg hd
    refine hgen (.blr r) (fun ps => by simp [MInst.lines, hd, pure, Except.pure])
      (by simp [Line.plain, Insn.condTarget?]) rfl (fun _ _ _ h => by cases h)
      (fun _ h => by cases h; exact hne) fun s j hj hprog hpc => ?_
    rw [step_blr (off := 0) (n := "") (rd := .xzr) (rn := .xzr) hR hj hprog hpc, hd]

/-! ## Symbol addresses -/

/-- The two hooked lines of `loadExtNameGot/Near`, as one execution: the destination gets the
link-time address, the pc advances by 8. -/
def symExec (X : ExtSem) : MInst → Arm.ArmState → Option Arm.ArmState
  | .loadExtNameGot rd n, s =>
    some (Arm.w (.GPR (rd.encZR.toOption.getD 31#5)) (X.sym n 0) (Arm.w .PC (Arm.r .PC s + 8) s))
  | .loadExtNameNear rd n off, s =>
    some (Arm.w (.GPR (rd.encZR.toOption.getD 31#5)) (X.sym n off) (Arm.w .PC (Arm.r .PC s + 8) s))
  | _, _ => none

/-- `OperandsSound` of an instruction with one late int def, no use and no clobber, whose
allocated form `mk r` writes `v` to `r` and advances the pc by 8. -/
theorem os_oneDef {F : BitVec 64 → Prop} {sem : ISem CV Arm.ArmState}
    {exec : MInst → Arm.ArmState → Option Arm.ArmState} {i : MInst} {mk : Reg → MInst} {d : Nat}
    {v : BitVec 64}
    (hops : i.operands = .ok #[⟨d, .int, .def, .late, .reg⟩])
    (hasg : ∀ regs i', i.assign regs = .ok i' → ∃ r, regs = #[r] ∧ i' = mk r)
    (hcl : i.clobbers = [])
    (hsem : ∀ w, sem i [] w = some ([ofX v], w, .next))
    (hex : ∀ r s, exec (mk r) s =
      some (Arm.w (.GPR (r.encZR.toOption.getD 31#5)) v (Arm.w .PC (Arm.r .PC s + 8) s))) :
    OperandsSound F exec sem i := by
  intro c wh ops regs i' s w outs w' hops' hst hasg' hw hal _herr hsem'
  rw [hops] at hops'
  cases hops'
  obtain ⟨r, rfl, rfl⟩ := hasg regs i' hasg'
  obtain ⟨-, hloc, -, -⟩ := checkStatic_facts hst
  have hr := hloc (⟨d, .int, .def, .late, .reg⟩, .reg r) (by simp)
  obtain ⟨n0, rfl, hn0, h16, h17, h18⟩ := locOk_int hr.1
  have huse : useVals #[⟨d, .int, .def, .late, .reg⟩] #[.x n0] s = [] := by
    simp [useVals, Operand.isUse]
  rw [huse, hsem] at hsem'
  simp only [Option.some.injEq, Prod.mk.injEq] at hsem'
  obtain ⟨rfl, rfl, -⟩ := hsem'
  have henc : (Reg.x n0).encZR.toOption.getD 31#5 = rnum n0 := by
    simp [Reg.encZR, show n0 ≤ 30 by omega, pure, Except.pure, Except.toOption, rnum]
  obtain ⟨hW, hd, ho⟩ := gpr_write_sound (F := F) ⟨hn0, h16, h17, h18⟩ hw v (Arm.r .PC s + 8)
  refine ⟨_, hex (.x n0) s, ?_, ?_, ?_, ?_, ?_⟩
  · rw [henc]; exact hW
  · rw [henc]
    refine ⟨?_, fun a _ => ?_⟩
    · simp only [spOf]
      rw [Arm.r_of_w_different (by simp; exact fun e => rnum_ne31 hn0 e.symm),
        Arm.r_of_w_different (by simp)]
    · simp [Arm.ArmState.mem_w_eq_mem]
  · intro p hp
    simp only [defRegs] at hp
    have : p = ((⟨d, .int, .def, .late, .reg⟩, .x n0), ofX v) := by
      simpa [Operand.isDef] using hp
    subst this
    rw [henc]; exact hd
  · intro r' hr' hnd _
    rw [henc]
    have hmem : ((⟨d, .int, .def, .late, .reg⟩ : Operand), Reg.x n0) ∈
        (#[(⟨d, .int, .def, .late, .reg⟩ : Operand)].zip #[Reg.x n0]).toList := by simp
    exact ho r' hr' (fun e => hnd _ hmem rfl e.symm)
  · intro r' hr'; rw [hcl] at hr'; simp at hr'

theorem ops_oneDef {i : MInst} {d : Nat} {mk : Reg → MInst}
    (hvo : ∀ (f : OpSpec → Reg → StateT (Array Operand) (Except String) Reg),
      MInst.visitOperands f i = do let r ← f .def_ (.vreg d .int); pure (mk r)) :
    i.operands = .ok #[⟨d, .int, .def, .late, .reg⟩] := by
  rw [MInst.operands]
  simp only [hvo]
  simp [StateT.run, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  exact ⟨rfl, rfl, rfl⟩

/-- `OperandsSound` of a symbol-address load (destination an int vreg). -/
theorem os_symAddr {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    (hi : (∃ d n, i = .loadExtNameGot (.vreg d .int) n) ∨
      (∃ d n off, i = .loadExtNameNear (.vreg d .int) n off)) :
    OperandsSound F (symExec X) (csem F ctx X) i := by
  rcases hi with ⟨d, n, rfl⟩ | ⟨d, n, off, rfl⟩
  · exact os_oneDef (mk := fun r => .loadExtNameGot r n) (ops_oneDef fun f => rfl)
      (fun regs i' h => assign_one (fun f => rfl) h) rfl (fun w => rfl) (fun r s => rfl)
  · exact os_oneDef (mk := fun r => .loadExtNameNear r n off) (ops_oneDef fun f => rfl)
      (fun regs i' h => assign_one (fun f => rfl) h) rfl (fun w => rfl) (fun r s => rfl)

/-- The machine runs the two hooked lines as `symExec`; its first step changes only the pc and
the destination register (`hmid`). -/
theorem runsAs_symAddr {R : RL} (hR : R.Wf) {i' : MInst} {x1 x2 : Insn}
    (hl : ∀ ps, i'.lines R.ctx ps = .ok ([.ins x1, .ins x2], ps))
    (hstep : ∀ s j, R.L[j]? = some (.ins x1) → R.L[j + 1]? = some (.ins x2) →
      s.program = R.fb.program R.base → Arm.r .PC s = R.pcOf j →
      R.step (R.step s) = match symExec R.X i' s with | some s' => s' | none => s)
    (hx1 : (∀ n, x1 ≠ .bl n) ∧ (∀ r, x1 ≠ .blr r)) (hx2 : (∀ n, x2 ≠ .bl n) ∧ (∀ r, x2 ≠ .blr r))
    (ht : x1.tlsTail = false ∧ x2.tlsTail = false)
    (hmid : ∀ s j, R.L[j]? = some (.ins x1) → s.program = R.fb.program R.base →
      Arm.r .PC s = R.pcOf j → Arm.r .PC (R.step s) = R.pcOf (j + 1) ∧
        Arm.r .ERR (R.step s) = Arm.r .ERR s ∧ (R.step s).program = s.program ∧
        (R.step s).mem = s.mem) :
    RunsAs R (fun _ => symExec R.X) i' [.ins x1, .ins x2] fun _ => True := by
  intro j T s _ _ s' hd hst hpc _ hex
  have hprog := hst.prog
  have hj : R.L[j]? = some (.ins x1) := drop_get (Z := [.ins x2]) hd
  have hj1 : R.L[j + 1]? = some (.ins x2) := drop_get1 (ls := []) hd
  have e := hstep s j hj hj1 hprog hpc
  simp only [hex] at e
  -- the pc: `symExec` advances by 8
  have hpc8 : Arm.r .PC s' = Arm.r .PC s + 8 := by
    revert hex
    cases i' <;> simp only [symExec, Option.some.injEq, reduceCtorEq, false_implies] <;>
      intro hex <;> subst hex <;> simp [Arm.r_of_w_different, Arm.r_of_w_same]
  obtain ⟨hm1, hm2, hm3, hm4⟩ := hmid s j hj hprog hpc
  refine ⟨2, by simpa [iterN] using e, ?_, fun i hi => ?_⟩
  rotate_left
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · show R.GoodX s
      exact RL.goodX_line hR hj hpc ht.1 (RL.good_of_sp hst.sp) hst.err hprog
        (RL.nextOk_pc4 (by rw [hm1, pcOf_succ hj, hpc])) (fun _ _ _ _ a ha => hst.gkeep a ha)
        (fun r e => absurd e (hx1.2 r)) (not_call_insn hx1.1 hx1.2)
    · show R.GoodX (R.step s)
      exact RL.goodX_line hR hj1 hm1 ht.2 (R.good_succ hR hj hx1.1 hx1.2 hm1)
        (by rw [hm2]; exact hst.err) (by rw [hm3, hprog])
        (RL.nextOk_pc4 (by rw [e, hpc8, hm1, pcOf_succ hj, hpc]; bv_omega))
        (fun _ _ _ _ a ha => by rw [hm4]; exact hst.gkeep a ha) (fun r e => absurd e (hx2.2 r))
        (not_call_insn hx2.1 hx2.2)
  simp only [List.length_cons, List.length_nil, Nat.zero_add]
  rw [hpc8, hpc, ← Nat.add_assoc, pcOf_succ hj1, pcOf_succ hj, BitVec.add_assoc]
  rfl

/-- **`loadExtNameGot/Near` on the machine**: two hooked steps. -/
theorem realizes_symAddr {R : RL} (hR : R.Wf) {s : Arm.ArmState}
    {b k : Nat} {allocs : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i)
    (hform : (∃ d n, i = .loadExtNameGot (.vreg d .int) n) ∨
      (∃ d n off, i = .loadExtNameNear (.vreg d .int) n off))
    (hops : i.operands = .ok ops) (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodX (iterN R.step i s) := by
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    have hsem := R.sem_csem hsem
    rcases hform with ⟨d, n, rfl⟩ | ⟨d, n, off, rfl⟩ <;>
    · simp only [csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, rfl, -⟩ := hsem
      exact ⟨herr, rfl⟩
  refine realizes_op_coreX hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => symExec R.X)
    (fun _ => (((os_symAddr hform).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun _ => True) trivial
    (fun regs i' _ hex _ => ?_) hW'
  obtain ⟨_, s0, _, hex⟩ := hex
  cases i' with
  | loadExtNameGot rd n =>
    refine ⟨[.ins (.adrpGot rd n), .ins (.ldrGotLo12 rd rd n)],
      fun ps => by simp [MInst.lines, pure, Except.pure], ?_, fun _ h => MInst.noConfusion h,
      fun _ h => MInst.noConfusion h, runsAs_symAddr hR (fun ps => by simp [MInst.lines, pure,
        Except.pure]) (fun s j hj hj1 hprog hpc => ?_) ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩
        ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩ ⟨rfl, rfl⟩
        (fun s j hj hprog hpc => ?_)⟩
    · intro ln hln; simp at hln; rcases hln with rfl | rfl <;> simp [Line.plain, Insn.condTarget?]
    · rw [step_adrpGot (off := 0) (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      rw [step_ldrGotLo12 (off := 0) (r := .xzr) hR hj1 (by simp [Arm.w_program, hprog])
        (by rw [Arm.r_of_w_same, hpc, pcOf_succ hj])]
      simp only [symExec, Arm.r_of_w_same, Arm.w_of_w_shadow, BitVec.add_assoc]
      rw [Arm.w_of_w_commute (by simp)]
      rfl
    · rw [step_adrpGot (off := 0) (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      exact ⟨by rw [Arm.r_of_w_same, hpc, pcOf_succ hj],
        by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)],
        by simp [Arm.w_program], by simp [Arm.ArmState.mem_w_eq_mem]⟩
  | loadExtNameNear rd n off =>
    refine ⟨[.ins (.adrp rd n off), .ins (.addLo12 rd rd n off)],
      fun ps => by simp [MInst.lines, pure, Except.pure], ?_, fun _ h => MInst.noConfusion h,
      fun _ h => MInst.noConfusion h, runsAs_symAddr hR (fun ps => by simp [MInst.lines, pure,
        Except.pure]) (fun s j hj hj1 hprog hpc => ?_) ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩
        ⟨fun _ h => Insn.noConfusion h, fun _ h => Insn.noConfusion h⟩ ⟨rfl, rfl⟩
        (fun s j hj hprog hpc => ?_)⟩
    · intro ln hln; simp at hln; rcases hln with rfl | rfl <;> simp [Line.plain, Insn.condTarget?]
    · rw [step_adrp (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      rw [step_addLo12 (r := .xzr) hR hj1 (by simp [Arm.w_program, hprog])
        (by rw [Arm.r_of_w_same, hpc, pcOf_succ hj])]
      simp only [symExec, Arm.r_of_w_same, Arm.w_of_w_shadow, BitVec.add_assoc]
      rw [Arm.w_of_w_commute (by simp)]
      rfl
    · rw [step_adrp (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      exact ⟨by rw [Arm.r_of_w_same, hpc, pcOf_succ hj],
        by rw [Arm.r_of_w_different (by simp), Arm.r_of_w_different (by simp)],
        by simp [Arm.w_program], by simp [Arm.ArmState.mem_w_eq_mem]⟩
  | _ => simp [symExec] at hex

end Backend.Proof
