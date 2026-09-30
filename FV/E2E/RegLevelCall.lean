import FV.E2E.RegLevelNext

/-!
# Calls and symbol addresses on the machine (M6)

The machine `ArmStepX` runs the callee of `bl`/`blr` as one hooked step (`H.call`) and the
relocated address pairs `adrp`/`ldr got` and `adrp`/`add lo12` as two hooked steps (`X.sym`).

* `CalleeOk F X H`: the callee contract of an activation with frame addresses `F`: the hooked
  call (`callExec H`) satisfies `OperandsSound` against `csem`'s call clause (`X.call`: the
  AAPCS64 contract — results, preserved registers, frame and `sp` kept, world as `X.call` says),
  returns to the next instruction, and `X.call` keeps the program and yields no model error.
* `realizes_call`, `realizes_symAddr`: the `op`/`next` case of `Realizes` for calls and
  `loadExtNameGot/Near`, instances of `realizes_op_core`.
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

/-- The callee as the machine runs it (`bl name` / `blr`; also the call of a `try_call`). -/
def callExec (H : ArmHooks) : MInst → Arm.ArmState → Option Arm.ArmState
  | .call info, s => some (H.call (match info.dest with | .sym n => some n | .reg _ => none) s)
  | .tryCall info _, s => some (H.call (match info.dest with | .sym n => some n | .reg _ => none) s)
  | _, _ => none

/-- **The callee contract** of an activation with frame addresses `F` (AAPCS64, stated for
the machine's hook `H` and `csem`'s callee semantics `X.call`, which does not depend on the
function context):

* `os`: `OperandsSound` of every call against the hooked callee: results in the fixed result
  registers, the world `X.call` computes, allocatable registers outside the clobber set
  preserved, the low 64 bits of v8–v15 preserved, `sp` and the frame bytes `F` untouched;
* `pc`: the callee returns to the instruction after the call;
* `ext`: `X.call` keeps the program and yields no model error. -/
structure CalleeOk (F : BitVec 64 → Prop) (X : ExtSem) (H : ArmHooks) : Prop where
  os : ∀ ctx info, OperandsSound F (callExec H) (csem F ctx X) (.call info)
  pc : ∀ d s, Arm.r .ERR s = .None → Arm.r .PC (H.call d s) = Arm.r .PC s + 4
  ext : ∀ d uses w outs w', X.call d uses w = some (outs, w') → Arm.r .ERR w = .None →
    Arm.r .ERR w' = .None ∧ w'.program = w.program

/-- **A call on the machine**: one hooked step. -/
theorem realizes_call {R : RL} (hR : R.Wf) (hC : CalleeOk R.F R.X R.H) {s : Arm.ArmState}
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
      Q R (iterN R.step n s) c'' := by
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    simp only [RL.sem, csem, Option.map_eq_some_iff] at hsem
    obtain ⟨⟨o, w2⟩, hx, he⟩ := hsem
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    exact hC.ext _ _ _ _ _ hx herr
  refine realizes_op_core hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => callExec R.H)
    (fun _ => hC.os R.ctx info) (fun regs i' hasg _ => ?_) hW'
  obtain ⟨info', rfl⟩ := assign_call_form hasg
  have hgen : ∀ x, (∀ ps, (MInst.call info').lines R.ctx ps = .ok ([.ins x], ps)) →
      (Line.ins x).plain = true →
      (∀ s j, R.L[j]? = some (.ins x) → s.program = R.fb.program R.base →
        Arm.r .PC s = R.pcOf j → R.step s = R.H.call
          (match info'.dest with | .sym n => some n | .reg _ => none) s) →
      ∃ ls1, (∀ ps, (MInst.call info').lines R.ctx ps = .ok (ls1, ps)) ∧
        (∀ ln ∈ ls1, ln.plain = true) ∧ (∀ ds, MInst.call info' ≠ .args ds) ∧
        (∀ us, MInst.call info' ≠ .rets us) ∧
        RunsAs R (fun _ => callExec R.H) (.call info') ls1 := by
    intro x hl1 hpl hstep
    refine ⟨[.ins x], hl1, fun ln hln => by simp only [List.mem_singleton] at hln; subst hln; exact hpl,
      fun _ h => MInst.noConfusion h, fun _ h => MInst.noConfusion h,
      fun j T s s' hd hprog hpc herr hex => ?_⟩
    have hj : R.L[j]? = some (.ins x) := drop_get (Z := []) hd
    simp only [callExec, Option.some.injEq] at hex
    subst hex
    refine ⟨by simp only [List.length_singleton, iterN]; exact hstep s j hj hprog hpc, ?_⟩
    rw [hC.pc _ _ herr, hpc, List.length_singleton, pcOf_succ hj]
  cases hd : info'.dest with
  | sym n =>
    refine hgen (.bl n) (fun ps => by simp [MInst.lines, hd, pure, Except.pure])
      (by simp [Line.plain, Insn.condTarget?]) fun s j hj hprog hpc => ?_
    rw [step_bl (off := 0) (r := .xzr) (rd := .xzr) (rn := .xzr) hR hj hprog hpc, hd]
  | reg r =>
    refine hgen (.blr r) (fun ps => by simp [MInst.lines, hd, pure, Except.pure])
      (by simp [Line.plain, Insn.condTarget?]) fun s j hj hprog hpc => ?_
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

/-- The machine runs the two hooked lines as `symExec`. -/
theorem runsAs_symAddr {R : RL} (hR : R.Wf) {i' : MInst} {x1 x2 : Insn}
    (hl : ∀ ps, i'.lines R.ctx ps = .ok ([.ins x1, .ins x2], ps))
    (hstep : ∀ s j, R.L[j]? = some (.ins x1) → R.L[j + 1]? = some (.ins x2) →
      s.program = R.fb.program R.base → Arm.r .PC s = R.pcOf j →
      R.step (R.step s) = match symExec R.X i' s with | some s' => s' | none => s) :
    RunsAs R (fun _ => symExec R.X) i' [.ins x1, .ins x2] := by
  intro j T s s' hd hprog hpc herr hex
  have hj : R.L[j]? = some (.ins x1) := drop_get (Z := [.ins x2]) hd
  have hj1 : R.L[j + 1]? = some (.ins x2) := drop_get1 (ls := []) hd
  have e := hstep s j hj hj1 hprog hpc
  simp only [hex] at e
  refine ⟨by simpa [iterN] using e, ?_⟩
  -- the pc: `symExec` advances by 8
  have hpc8 : Arm.r .PC s' = Arm.r .PC s + 8 := by
    revert hex
    cases i' <;> simp only [symExec, Option.some.injEq, reduceCtorEq, false_implies] <;>
      intro hex <;> subst hex <;> simp [Arm.r_of_w_different, Arm.r_of_w_same]
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
      Q R (iterN R.step n s) c'' := by
  have hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
    have herr : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    rcases hform with ⟨d, n, rfl⟩ | ⟨d, n, off, rfl⟩ <;>
    · simp only [RL.sem, csem, Option.some.injEq, Prod.mk.injEq] at hsem
      obtain ⟨-, rfl, -⟩ := hsem
      exact ⟨herr, rfl⟩
  refine realizes_op_core hR hq hvb hi hops hsz hsem hlen hk (exec := fun _ => symExec R.X)
    (fun _ => os_symAddr hform) (fun regs i' _ hex => ?_) hW'
  obtain ⟨_, s0, _, hex⟩ := hex
  cases i' with
  | loadExtNameGot rd n =>
    refine ⟨[.ins (.adrpGot rd n), .ins (.ldrGotLo12 rd rd n)],
      fun ps => by simp [MInst.lines, pure, Except.pure], ?_, fun _ h => MInst.noConfusion h,
      fun _ h => MInst.noConfusion h, runsAs_symAddr hR (fun ps => by simp [MInst.lines, pure,
        Except.pure]) fun s j hj hj1 hprog hpc => ?_⟩
    · intro ln hln; simp at hln; rcases hln with rfl | rfl <;> simp [Line.plain, Insn.condTarget?]
    · rw [step_adrpGot (off := 0) (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      rw [step_ldrGotLo12 (off := 0) (r := .xzr) hR hj1 (by simp [Arm.w_program, hprog])
        (by rw [Arm.r_of_w_same, hpc, pcOf_succ hj])]
      simp only [symExec, Arm.r_of_w_same, Arm.w_of_w_shadow, BitVec.add_assoc]
      rw [Arm.w_of_w_commute (by simp)]
      rfl
  | loadExtNameNear rd n off =>
    refine ⟨[.ins (.adrp rd n off), .ins (.addLo12 rd rd n off)],
      fun ps => by simp [MInst.lines, pure, Except.pure], ?_, fun _ h => MInst.noConfusion h,
      fun _ h => MInst.noConfusion h, runsAs_symAddr hR (fun ps => by simp [MInst.lines, pure,
        Except.pure]) fun s j hj hj1 hprog hpc => ?_⟩
    · intro ln hln; simp at hln; rcases hln with rfl | rfl <;> simp [Line.plain, Insn.condTarget?]
    · rw [step_adrp (r := .xzr) (rn := .xzr) hR hj hprog hpc]
      rw [step_addLo12 (r := .xzr) hR hj1 (by simp [Arm.w_program, hprog])
        (by rw [Arm.r_of_w_same, hpc, pcOf_succ hj])]
      simp only [symExec, Arm.r_of_w_same, Arm.w_of_w_shadow, BitVec.add_assoc]
      rw [Arm.w_of_w_commute (by simp)]
      rfl
  | _ => simp [symExec] at hex

end Backend.Proof
