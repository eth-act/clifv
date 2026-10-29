import FV.E2E.RegLevelCorrectCW
import FV.E2E.PairGuardS

/-!
# The world-read guard on reads only (SEM1 #537, #699)

`WGuard` (`RegLevelCorrectCY.lean`) asks `csem Y` to be defined at every world-reading
instruction, stores included; `csem Y` of a store needs the *written* bytes to avoid `Y`
(`straightSem`'s `AccessOk`), so with the lock-step's `Ok w Y := Y = Zof F D cm` the guard fails
at every store into a byte of `D` the CLIF memory has not yet initialised (#699). The lock-step
needs only the *reads* to avoid `Y`. Here the guard admits, besides `csem Y`, any instruction
that is not a load form (`MInst.loadForm`: loads, `ldar`, scalar SIMD&FP loads, atomic loops):
a covered straight-line form of that kind reads no memory once allocated
(`formOk_noLoad_memRd`, so its lines read nothing, `lines_noLoads`). The condition is syntactic,
so it is invariant under the driver's renaming and retargeting. `WGuard` implies `WGuardS`
(`wGuardS_of_wGuard`); at `Ok := (· = F)` both are no restriction.

* `MInst.loadForm`, `formOk_noLoad_memRd`;
* `WGuardS`, `csemVGS`, `csemVIGS`, `RL.semGS` (+ `_inv`, `_le`, `_agree`, `_eqF`,
  `csemVGS_of_csemVG`);
* `realizes_op_nextNYS`, `realizes_op_nextNAS`: `realizes_op_nextNY`/`realizes_op_nextNA` with
  the store alternative;
* **`realizes_allCYS`**, `realizes_allC_spYS`, **`realizes_allCWS`**, `realizes_allC_spWS`: the
  dispatchers on the new guard (same proofs).
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

set_option maxHeartbeats 4000000 in
/-- **A covered form other than the loads reads no memory once allocated**
(`formOk_reads`' case analysis). -/
theorem formOk_noLoad_memRd {ctx : FnCtx} {i : MInst} (h : FormOk ctx i = true)
    (hl : i.loadForm = false) {regs : Array Reg} {i' : MInst} (hasg : i.assign regs = .ok i') :
    i'.memRd = false := by
  by_cases hmr : i'.memRd = false
  · exact hmr
  exfalso
  unfold FormOk at h
  split at h
  all_goals first
    | (simp [MInst.loadForm] at hl; done)
    | exact hmr (formOk_fpuStore_memRd h hasg)
    | (cases h; done)
    | (assign_inv hasg <;> exact hmr rfl)
    | skip
  all_goals
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hop, hm⟩ := h
    unfold memOk at hm
    split at hm <;> (try cases hm)
    all_goals (assign_inv hasg <;> exact hmr (memRd_store hop))

/-- **The guard of the world reads, reads only**: a set `Y ⊇ F` admitted by `Ok` at the world
at which, for a world-reading instruction, `csem Y` gives a result, or the instruction is not a
load form (`MInst.loadForm`: a store or a form without memory access, whose allocated lines read
nothing, `formOk_noLoad_memRd`). -/
def WGuardS (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem)
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) (i : MInst) (us : List CV) (w : Arm.ArmState) :
    Prop :=
  ∃ Y, (∀ a, F a → Y a) ∧ Ok w Y ∧
    (i.wReads = true → (∃ r, csem Y ctx X i us w = some r) ∨ i.loadForm = false)

theorem wGuardS_of_wGuard {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {i : MInst} {us : List CV} {w : Arm.ArmState}
    (h : WGuard F ctx X Ok i us w) : WGuardS F ctx X Ok i us w :=
  let ⟨Y, hYF, hOk, hr⟩ := h
  ⟨Y, hYF, hOk, fun hw => .inl (hr hw)⟩

open Classical in
/-- **The guarded semantics, reads only**: `csemV` where `WGuardS` holds, undefined elsewhere. -/
noncomputable def csemVGS (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) : ISem CV Arm.ArmState :=
  fun i us w => if WGuardS F ctx X Ok i us w then csemV gv F ctx X i us w else none

/-- **The counted guarded semantics, reads only.** -/
noncomputable def csemVIGS (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSemI) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) :
    ISem CV (Arm.ArmState × Nat) :=
  ISem.counted fun n => csemVGS gv F ctx (X.at n) Ok

theorem csemVGS_inv {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {i : MInst} {us : List CV}
    {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemVGS gv F ctx X Ok i us w = some r) :
    WGuardS F ctx X Ok i us w ∧ csemV gv F ctx X i us w = some r := by
  unfold csemVGS at h
  split at h
  · exact ⟨‹_›, h⟩
  · cases h

/-- A step of the counted guarded semantics is one of `csemVI`. -/
theorem csemVIGS_sub {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSemI} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {i : MInst} {us : List CV}
    {w : Arm.ArmState × Nat} {r : List CV × (Arm.ArmState × Nat) × Ctl}
    (h : csemVIGS gv F ctx X Ok i us w = some r) : csemVI gv F ctx X i us w = some r := by
  simp only [csemVIGS, csemVI, ISem.counted, Option.map_eq_some_iff] at h ⊢
  obtain ⟨r', h1, h2⟩ := h
  exact ⟨r', (csemVGS_inv h1).2, h2⟩

/-- **The old guard's steps are steps of the new one.** -/
theorem csemVGS_of_csemVG {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {i : MInst} {us : List CV}
    {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : csemVG gv F ctx X Ok i us w = some r) : csemVGS gv F ctx X Ok i us w = some r := by
  obtain ⟨hg, hs⟩ := csemVG_inv h
  simp only [csemVGS, if_pos (wGuardS_of_wGuard hg)]
  exact hs

/-- **The guard at `Y := F` is no restriction**: `csemVGS … (fun _ Y => Y = F)` is `csemV`. -/
theorem csemVGS_eqF (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    csemVGS gv F ctx X (fun _ Y => Y = F) = csemV gv F ctx X := by
  funext i us w
  unfold csemVGS
  split
  · rfl
  · rename_i hg
    cases h : csemV gv F ctx X i us w with
    | none => rfl
    | some r => exact absurd ⟨F, fun _ h => h, rfl, fun _ => .inl ⟨r, csemV_sub h⟩⟩ hg

theorem csemVIGS_eqF (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSemI) : csemVIGS gv F ctx X (fun _ Y => Y = F) = csemVI gv F ctx X := by
  simp only [csemVIGS, csemVI, csemVGS_eqF]

/-- The activation's guarded semantics, reads only. -/
noncomputable def RL.semGS (R : RL) (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop) :
    ISem CV Arm.ArmState :=
  csemVGS R.gv R.F R.ctx R.X Ok

theorem RL.semGS_inv {R : RL} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {i : MInst}
    {us : List CV} {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : R.semGS Ok i us w = some r) : WGuardS R.F R.ctx R.X Ok i us w ∧ R.sem i us w = some r :=
  csemVGS_inv h

theorem RL.semGS_le {R : RL} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} :
    ∀ i us w r r', R.semGS Ok i us w = some r → R.sem i us w = some r' →
      R.semGS Ok i us w = some r' := by
  intro i us w r r' h h'
  have hg := (RL.semGS_inv h).1
  simp only [RL.semGS, csemVGS, if_pos hg]
  exact h'

/-- Two guarded semantics of one activation agree where both are defined. -/
theorem RL.semGS_agree {R : RL} {Ok Ok' : Arm.ArmState → (BitVec 64 → Prop) → Prop} :
    ∀ i us w r r', R.semGS Ok' i us w = some r → R.semGS Ok i us w = some r' →
      R.semGS Ok' i us w = some r' := by
  intro i us w r r' h h'
  have e : r = r' := by
    have a := (RL.semGS_inv h).2
    have b := (RL.semGS_inv h').2
    rw [a] at b
    exact Option.some.inj b
  rw [h, e]

/-- **`realizes_op_nextNY` with the store alternative**: the reads of the lines avoid `Y` when
`csem Y` gives a result, and read nothing when the allocated instructions are not `memRd`. -/
theorem realizes_op_nextNYS {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} (hYF : ∀ a, R.F a → Y a)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    (hq : Q R s (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hsemY : (∃ rY, csem Y R.ctx R.X i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2))
      w = some rY) ∨ ∀ (regs : Array Reg) i', i.assign regs = .ok i' → i'.memRd = false)
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    (hOS : ∀ env, OperandsSound R.F (execMInst R.ctx env) (csem R.F R.ctx R.X) i)
    (hL : ∀ regs i', i.assign regs = .ok i' →
      LinesOk R.ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us))
    (hRd : ∀ {F' : BitVec 64 → Prop} {regs : Array Reg} {i' : MInst} {ls : List Line}
      {ps ps' : PState} {u v : Arm.ArmState}
      {r : List CV × Arm.ArmState × Ctl}, AllocOk ops regs → i.assign regs = .ok i' →
      i'.lines R.ctx ps = .ok (ls, ps') → SameWorld F' u v → Arm.r .ERR v = .None →
      Arm.CheckSPAlignment v → csem F' R.ctx R.X i (useVals ops regs u) v = some r → ∀ env,
      LinesReads env ls u (fun a => ¬ F' a))
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      Q R (iterN R.step n s) c'' ∧ ∀ i < n, R.GoodXNY Y (iterN R.step i s) := by
  rcases hsemY with ⟨rY, hsemY⟩ | hnr
  · exact realizes_op_nextNY hR hYF hq hvb hi hops hsz hsem hsemY hlen hk hOS hL hRd hW'
  have hpre : ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
      (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 s (R.ReadInY Y false) :=
    fun regs i' _ _ hasg hl1 _ => linesReads_noLoads (lines_noLoads (hl1 {}) (hnr regs i' hasg))
  exact realizes_op_coreXNR hR hq hvb hi hops hsz hsem hlen hk (exec := fun env => execMInst R.ctx env)
    (fun env => (((hOS env).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun u =>
      ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
        (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 u (R.ReadInY Y false))
    hpre
    (fun regs i' hasg hal' _ _ => by
      obtain ⟨⟨ls1, hl1, hins, hpl, hint⟩, hna, hnr⟩ := hL regs i' hasg
      exact ⟨ls1, hl1, hpl, hna, hnr, (runsAs_of_linesOkNR hR hl1 hins hint).mono
        fun u hu env => hu regs i' ls1 hal' hasg hl1 env⟩) hW'

/-- **`realizes_op_nextNA` with the store alternative.** -/
theorem realizes_op_nextNAS {R : RL} (hR : R.Wf) {Y : BitVec 64 → Prop} (hYF : ∀ a, R.F a → Y a)
    {s : Arm.ArmState} {b k : Nat} {allocs : Array Loc}
    {its : List RItem} {m : Loc → CV} {w : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    (hq : QW R s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩))
    {vb : VBlock} {i : MInst} {ops : Array Operand} {outs : List CV} {w' : Arm.ArmState}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops)
    (hsz : allocs.size = ops.size)
    (hsem : R.sem i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2)) w =
      some (outs, w', .next))
    (hsemY : (∃ rY, csem Y R.ctx R.X i (((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2))
      w = some rY) ∨ ∀ (regs : Array Reg) i', i.assign regs = .ok i' → i'.memRd = false)
    (hlen : outs.length = ((ops.zip allocs).toList.filter (·.1.isDef)).length)
    (hk : k + 1 < vb.insts.size)
    (hOS : ∀ env, OperandsSound R.F (execMInst R.ctx env) (csem R.F R.ctx R.X) i)
    (hL : ∀ regs i', i.assign regs = .ok i' →
      LinesOk R.ctx i' ∧ (∀ ds, i' ≠ .args ds) ∧ (∀ us, i' ≠ .rets us))
    (hRd : ∀ {F' : BitVec 64 → Prop} {regs : Array Reg} {i' : MInst} {ls : List Line}
      {ps ps' : PState} {u v : Arm.ArmState}
      {r : List CV × Arm.ArmState × Ctl}, AllocOk ops regs → i.assign regs = .ok i' →
      i'.lines R.ctx ps = .ok (ls, ps') → SameWorld F' u v → Arm.r .ERR v = .None →
      Arm.CheckSPAlignment v → csem F' R.ctx R.X i (useVals ops regs u) v = some r → ∀ env,
      LinesReads env ls u (fun a => ¬ F' a))
    (hW' : Arm.r .ERR w' = .None ∧ w'.program = w.program) :
    ∃ n c'', MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' ∧
      R.SegNA Y s j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' n := by
  rcases hsemY with ⟨rY, hsemY⟩ | hnr
  · exact realizes_op_nextNA hR hYF hq hvb hi hops hsz hsem hsemY hlen hk hOS hL hRd hW'
  have hpre : ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
      (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 s (R.ReadInY Y false) :=
    fun regs i' _ _ hasg hl1 _ => linesReads_noLoads (lines_noLoads (hl1 {}) (hnr regs i' hasg))
  exact realizes_op_coreXNA hR hq hvb hi hops hsz hsem hlen hk (exec := fun env => execMInst R.ctx env)
    (fun env => (((hOS env).at (fun _ => RL.FK_F) s).toI _).v R.gv) (Pre := fun u =>
      ∀ regs i' ls1, allocs = regs.map Loc.reg → i.assign regs = .ok i' →
        (∀ ps, i'.lines R.ctx ps = .ok (ls1, ps)) → ∀ env, LinesReads env ls1 u (R.ReadInY Y false))
    hpre
    (fun regs i' hasg hal' _ _ => by
      obtain ⟨⟨ls1, hl1, hins, hpl, hint⟩, hna, hnr⟩ := hL regs i' hasg
      exact ⟨ls1, hl1, hpl, hna, hnr, (runsAs_of_linesOkNA hR hl1 hins hint).mono
        fun u hu env => hu regs i' ls1 hal' hasg hl1 env⟩) hW'

/-- A `Rets` step of the reads-only guarded semantics ends the run. -/
theorem rets_mstepGS {R : RL} {Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop} {b k : Nat}
    {a : Array Loc} {its : List RItem} {m : Loc → CV} {w : Arm.ArmState}
    {c' : MConf CV Arm.ArmState} {vb : VBlock} {us : List (Reg × Reg)}
    (hvb : R.vc.blocks[b]? = some vb) (hi : vb.insts[k]? = some (.rets us))
    (h : MStep R.vc (R.semGS Ok) ckeep R.rf (.run ⟨b, .op k a :: its, m, w⟩) c') :
    ∃ vals m' w', c' = .ret vals m' w' := by
  cases h with
  | op hvb' hi' hops hsz hsemG hlen hho hcl hn =>
    rw [hvb] at hvb'; cases hvb'
    rw [hi] at hi'; cases hi'
    obtain ⟨-, hsem⟩ := RL.semGS_inv hsemG
    simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    cases hn with
    | ret _ => exact ⟨_, _, _, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **One step from `Q ∧ AInv` on the reads-only guard** that is not a callee restore
(`realizes_allCYS`'s non-restore case; `realizes_stepCY`'s proof, a store taking the `memRd`
alternative of `WGuardS`). -/
theorem realizes_stepCYS {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    ∀ s c c', Q R s c → AInv R c → P s → MStep R.vc (R.semGS Ok) ckeep R.rf c c' →
      (∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) →
      ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c := by
  intro s c c' hq hA hP hG hns
  have lift : ∀ c'', MStep R.vc R.sem ckeep R.rf c c'' → MStep R.vc (R.semGS Ok) ckeep R.rf c c'' :=
    fun c'' h'' => MStep.guardLift h'' hG RL.semGS_le
  have fin1 : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) →
      countIn R.CallSt R.step s n = opCalls R.vc c →
      ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c :=
    fun Y hYF hYO n c'' hm hq' ht hc => ⟨n, c'', lift c'' hm, ⟨hq', aInv_step hR hq hA hm⟩,
      fun i hi => ⟨(ht i hi).1, Y, hYF, hYO, (ht i hi).2⟩, hc⟩
  have fin : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' → Q R (iterN R.step n s) c'' →
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) → opCalls R.vc c = 0 →
      ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ (Q R (iterN R.step n s) c'' ∧ AInv R c'') ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c :=
    fun Y hYF hYO n c'' hm hq' ht h0 => fin1 Y hYF hYO n c'' hm hq'
      (fun i hi => ⟨(ht i hi).1.1, (ht i hi).2⟩)
      (by rw [h0]; exact countIn_zero_of fun i hi => (ht i hi).1.2)
  have finT := fin (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have fin1T := fin1 (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have nil : ∀ i < 0, R.GoodXNY (fun _ => True) (iterN R.step i s) :=
    fun _ h => absurd h (Nat.not_lt_zero _)
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases hG with
  | move =>
    obtain ⟨n, hn, ht⟩ := realizes_moveNR (Y := fun _ => True) hR hq (hns _ _ _ _ _ _ rfl)
    exact finT n _ MStep.move hn ht rfl
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsemG hlen hho hcl hn =>
    obtain ⟨hguard, hsem⟩ := RL.semGS_inv hsemG
    have hoc : opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = if i.isCallI then 1 else 0 := by
      simp only [opCalls, hvb, hi]
    have hoc0 : i.isCallI = false → opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = 0 :=
      fun h => by rw [hoc, h]; rfl
    have hstep : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    have herrw : Arm.r .ERR w = .None := by
      have hst := q_stRel hq
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    obtain ⟨Y, hYF, hOk, hwr⟩ := hguard
    have hYO : (∀ a, Y a) ∨ ∃ w, Ok w Y := .inr ⟨w, hOk⟩
    cases hct : i.isCtl
    · rcases (hcov b vb k i hvb hi).resolve_left (by simp [hct]) with hfo | hpl
      rotate_left
      · -- the literal-pool load (#565)
        obtain ⟨sz, d, v, fl, rfl, -⟩ := isPoolLoad_form hpl
        obtain ⟨-, rfl⟩ := pool_world hsem
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_poolLoadNR (Y := fun _ => True) hR hq hvb hi hpl
            hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
      -- a covered straight-line form
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      have hwi : i.wReads = true := by
        simp [MInst.wReads, hct]
      have hsemY := (hwr hwi).imp_right fun h (regs : Array Reg) (i' : MInst) hasg =>
        formOk_noLoad_memRd hfo h (regs := regs) (i' := i') hasg
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_op_nextNYS hR hYF hq hvb hi hops hsz hsem hsemY hlen
          hk hOS hL
          (fun ha hasg hl hw he hal hs env => formOk_reads hfo hops ha hasg hl hw he hal hs env)
          (csem_next_world' (R.sem_csem hsem) hnc herrw)
        exact fin Y hYF hYO n c'' hm hq' ht
          (hoc0 (by cases i <;> first | rfl | simp [MInst.isCtl] at hct))
    · cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hct
      case call info =>
        have hc : ctl = .next := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, i0, hi0, hc0, hnc⟩ := realizes_callNR (Y := fun _ => True)
            hR hC hP hq hvb hi hops hsz hsem hlen hk
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
      case args ds => exact finT 0 c' hstep (realizes_args hR hq hA hvb hi hstep) nil (hoc0 rfl)
      case rets us =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact finT 0 _ hstep trivial nil (hoc0 rfl)
      case loadExtNameGot rd nm =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddrNR (Y := fun _ => True) hR hq hvb hi
            (.inl ⟨d, nm, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_symAddrNR (Y := fun _ => True) hR hq hvb hi
            (.inr ⟨d, nm, off, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
      case jump l =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoNR (Y := fun _ => True) hR hq hvb hi (.inl ⟨l, rfl⟩) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
      case condBr t e kk =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoNR (Y := fun _ => True) hR hq hvb hi
          (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, hq', ht⟩ := realizes_gotoNR (Y := fun _ => True) hR hq hvb hi
          (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact finT 0 _ hstep trivial nil (hoc0 rfl)
        · obtain ⟨n, hq', ht⟩ := realizes_trapIf_nextNR (Y := fun _ => True) hR hq hvb hi hstep
            (fun w'' e => hh ⟨w'', e⟩)
          exact finT n c' hstep hq' ht (hoc0 rfl)
      case udf code =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact finT 0 _ hstep trivial nil (hoc0 rfl)
      case emitIsland nb => exact finT 0 c' hstep (realizes_island hq hvb hi hstep) nil (hoc0 rfl)
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_jtNR (Y := fun _ => True) hR hq hvb hi hstep
        exact finT n c'' hm hq' ht (hoc0 rfl)
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_rmwLoopNY hR hq hvb hi hstep fun ops' hops' => by
          rw [hops] at hops'; cases hops'
          exact (hwr rfl).resolve_right fun h => by simp [MInst.loadForm] at h
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨n, c'', hm, hq', ht⟩ := realizes_casLoopNY hR hq hvb hi hstep fun ops' hops' => by
          rw [hops] at hops'; cases hops'
          exact (hwr rfl).resolve_right fun h => by simp [MInst.loadForm] at h
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht, i0, hi0, hc0, hnc⟩ := realizes_tryCallNR (Y := fun _ => True)
            hR hC (hT (hasTryCall_of_mem hvb hi)) hP hq hvb hi hops hsz hsem hlen hk1 hsucc hitems rfl
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
      case elfTlsGetAddr nm rd tmp =>
        have hv := ctlCheck_inst hck hvb hi
        simp only [ctlInstOk, Bool.and_eq_true] at hv
        obtain ⟨d, rfl⟩ := isVregInt_iff hv.1
        obtain ⟨t, rfl⟩ := isVregInt_iff hv.2
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht⟩ := realizes_tlsNR (Y := fun _ => True) hR
            (hTls (hasTls_of_mem hvb hi)) hq hvb hi hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)

/-- **`realizes_allCY` on the reads-only guard**: under `QA` (`realizesQA_CP` on
`realizes_stepCYS`). -/
theorem realizes_allCYS {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    RealizesCP R.vc R.rf (R.semGS Ok) ckeep R.step (QA R)
      (fun u => R.GoodX u ∧ R.WReadsIn Ok u) R.CallSt P :=
  realizesQA_CP hR (realizes_stepCYS hR Ok hC hT hTls hcov)
    (fun _ _ _ _ _ _ _ hq hs => let ⟨n, h1, h2⟩ := realizes_moveNR (Y := fun _ => True) hR hq hs
      ⟨n, h1, fun i hi => ⟨(h2 i hi).1.1, fun _ => True, fun _ _ => trivial, .inl fun _ => trivial,
        (h2 i hi).2⟩, countIn_zero_of fun i hi => (h2 i hi).1.2⟩)
    (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstepGS hvb hi h)

/-- **`realizes_allCYS` with the body `sp` at the contract's states.** -/
theorem realizes_allC_spYS {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
      R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
        R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) :
    RealizesCP R.vc R.rf (R.semGS Ok) ckeep R.step (QA R)
      (fun u => R.GoodX u ∧ R.WReadsIn Ok u) R.CallSt P := by
  intro s c c' hqa hP h
  have hsp : spOf s = R.spB := by
    cases c with
    | run st => obtain ⟨b, its, m, w⟩ := st; obtain ⟨mt, hq⟩ := qa_q hqa; exact (q_stRel hq).sp
    | _ => cases h
  exact realizes_allCYS hR Ok hC hT hTls hcov s c c' hqa ⟨hP, hsp⟩ h

set_option maxHeartbeats 4000000 in
/-- **`realizes_stepCW` on the reads-only guard** (same proof). -/
theorem realizes_stepCWS {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c c' : MConf CV Arm.ArmState} (hq : QW R s j ps1 T c) (hA : AInv R c) (hP : P s)
    (hG : MStep R.vc (R.semGS Ok) ckeep R.rf c c')
    (hns : ∀ b src dst its m w, c = .run ⟨b, .move src dst :: its, m, w⟩ → src.isSave = false) :
    ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
      countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n := by
  have lift : ∀ c'', MStep R.vc R.sem ckeep R.rf c c'' → MStep R.vc (R.semGS Ok) ckeep R.rf c c'' :=
    fun c'' h'' => MStep.guardLift h'' hG RL.semGS_le
  have fin1 : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' →
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' →
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.ReadsInY Y (iterN R.step i s)) →
      countIn R.CallSt R.step s n = opCalls R.vc c → R.SegLenA j ps1 T c c'' s n →
      ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
        QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
          (R.nextW j ps1 T c c'').2.2 c'' ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n :=
    fun Y hYF hYO n c'' hm hq' ht hc hs => ⟨n, c'', lift c'' hm, MStep.shapeEq (lift c'' hm) hG,
      aInv_step hR hq.q hA hm, hq', fun i hi => ⟨(ht i hi).1, Y, hYF, hYO, (ht i hi).2⟩, hc, hs⟩
  have fin : ∀ Y, (∀ a, R.F a → Y a) → ((∀ a, Y a) ∨ ∃ w, Ok w Y) →
      ∀ n c'', MStep R.vc R.sem ckeep R.rf c c'' →
      QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' →
      (∀ i < n, R.GoodXNY Y (iterN R.step i s)) → opCalls R.vc c = 0 →
      R.SegLenA j ps1 T c c'' s n →
      ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧ AInv R c'' ∧
        QW R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
          (R.nextW j ps1 T c c'').2.2 c'' ∧
        (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
        countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n :=
    fun Y hYF hYO n c'' hm hq' ht h0 hs => fin1 Y hYF hYO n c'' hm hq'
      (fun i hi => ⟨(ht i hi).1.1, (ht i hi).2⟩)
      (by rw [h0]; exact countIn_zero_of fun i hi => (ht i hi).1.2) hs
  have finT := fin (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have fin1T := fin1 (fun _ => True) (fun _ _ => trivial) (.inl fun _ => trivial)
  have nil : ∀ i < 0, R.GoodXNY (fun _ => True) (iterN R.step i s) :=
    fun _ h => absurd h (Nat.not_lt_zero _)
  have hck := (lowerRFunc_ok hR.alloc).2.2
  cases hG with
  | move =>
    obtain ⟨n, hq', ht, hs⟩ := realizes_moveNA (Y := fun _ => True) hR hq (hns _ _ _ _ _ _ rfl)
    exact finT n _ MStep.move hq' ht rfl hs
  | @op b k allocs its m w vb i ops outs outs' w' ctl m2 c' hvb hi hops hsz hsemG hlen hho hcl hn =>
    obtain ⟨hguard, hsem⟩ := RL.semGS_inv hsemG
    have hoc : opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = if i.isCallI then 1 else 0 := by
      simp only [opCalls, hvb, hi]
    have hoc0 : i.isCallI = false → opCalls R.vc (.run ⟨b, .op k allocs :: its, m, w⟩) = 0 :=
      fun h => by rw [hoc, h]; rfl
    have hstep : MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c' :=
      MStep.op hvb hi hops hsz hsem hlen hho hcl hn
    have toA : ∀ {c'' : MConf CV Arm.ArmState} {n : Nat},
        MStep R.vc R.sem ckeep R.rf (.run ⟨b, .op k allocs :: its, m, w⟩) c'' →
        (∀ us, i ≠ .rets us) →
        ((∃ cd, i = .udf cd) ∨ (∃ kk cd, i = .trapIf kk cd) → ∀ w'', c'' ≠ .halt w'') →
        R.SegLen j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n →
        R.SegLenA j ps1 T (.run ⟨b, .op k allocs :: its, m, w⟩) c'' s n :=
      fun hm hnr hnh hs => RL.segLenA_of_run (RL.mstep_run hm hvb hi hnr hnh) hs
    have herrw : Arm.r .ERR w = .None := by
      have hst := q_stRel hq.q
      rw [← hst.world.1 .ERR (by simp [Masked]), hst.err]
    obtain ⟨Y, hYF, hOk, hwr⟩ := hguard
    have hYO : (∀ a, Y a) ∨ ∃ w, Ok w Y := .inr ⟨w, hOk⟩
    cases hct : i.isCtl
    · rcases (hcov b vb k i hvb hi).resolve_left (by simp [hct]) with hfo | hpl
      rotate_left
      · -- the literal-pool load (#565)
        obtain ⟨sz, d, v, fl, rfl, -⟩ := isPoolLoad_form hpl
        obtain ⟨-, rfl⟩ := pool_world hsem
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_poolLoadNA (Y := fun _ => True) hR hq hvb hi
            hpl hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      -- a covered straight-line form
      obtain ⟨hOS, hL⟩ := formOk_sound (F := R.F) (X := R.X) hfo
      obtain rfl := csem_ctl hct (R.sem_csem hsem)
      have hwi : i.wReads = true := by
        simp [MInst.wReads, hct]
      have hsemY := (hwr hwi).imp_right fun h (regs : Array Reg) (i' : MInst) hasg =>
        formOk_noLoad_memRd hfo h (regs := regs) (i' := i') hasg
      cases hn with
      | next hk =>
        have hnc : ∀ info, i ≠ .call info := by rintro info rfl; simp [MInst.isCtl] at hct
        obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_op_nextNAS hR hYF hq hvb hi hops hsz hsem hsemY
          hlen hk hOS hL
          (fun ha hasg hl hw he hal hs env => formOk_reads hfo hops ha hasg hl hw he hal hs env)
          (csem_next_world' (R.sem_csem hsem) hnc herrw)
        refine fin Y hYF hYO n c'' hm hq' ht
          (hoc0 (by cases i <;> first | rfl | simp [MInst.isCtl] at hct))
          (toA hm (fun us h => by subst h; simp [MInst.isCtl] at hct)
            (fun h => by rcases h with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [MInst.isCtl] at hct) hs)
    · cases i <;> simp only [MInst.isCtl, reduceCtorEq] at hct
      case call info =>
        have hc : ctl = .next := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, ⟨i0, hi0, hc0, hnc⟩, hs⟩ := realizes_callNA (Y := fun _ => True)
            hR hC hP hq hvb hi hops hsz hsem hlen hk
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case args ds =>
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          have hQ := realizes_args hR hq.q hA hvb hi hstep
          obtain ⟨hq', -, hs⟩ := realizes_zeroNA (Y := fun _ => True) hq hvb hi (.inl ⟨ds, rfl⟩)
            (q_stRel hQ)
          exact finT 0 _ hstep hq' nil (hoc0 rfl) hs
      case rets us =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | ret _ => exact finT 0 _ hstep trivial nil (hoc0 rfl) rfl
      case loadExtNameGot rd nm =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_symAddrNA (Y := fun _ => True) hR hq hvb hi
            (.inl ⟨d, nm, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case loadExtNameNear rd nm off =>
        obtain ⟨d, rfl⟩ := isVregInt_iff (by simpa [ctlInstOk] using ctlCheck_inst hck hvb hi)
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_symAddrNA (Y := fun _ => True) hR hq hvb hi
            (.inr ⟨d, nm, off, rfl⟩) hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case jump l =>
        obtain ⟨n, hq', ht, hs⟩ := realizes_gotoNA (Y := fun _ => True) hR hq hvb hi
          (.inl ⟨l, rfl⟩) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
          (toA hstep (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case condBr t e kk =>
        obtain ⟨n, hq', ht, hs⟩ := realizes_gotoNA (Y := fun _ => True) hR hq hvb hi
          (.inr (.inl ⟨t, e, kk, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
          (toA hstep (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case testBitAndBranch kd t e rn bit =>
        obtain ⟨n, hq', ht, hs⟩ := realizes_gotoNA (Y := fun _ => True) hR hq hvb hi
          (.inr (.inr ⟨kd, t, e, rn, bit, rfl⟩)) hstep
        exact finT n c' hstep hq' ht (hoc0 rfl)
          (toA hstep (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case trapIf kk code =>
        by_cases hh : ∃ w'', c' = .halt w''
        · obtain ⟨w'', rfl⟩ := hh
          exact finT 0 _ hstep trivial nil (hoc0 rfl) rfl
        · obtain ⟨n, hq', ht, hs⟩ := realizes_trapIf_nextNA (Y := fun _ => True) hR hq hvb hi hstep
            (fun w'' e => hh ⟨w'', e⟩)
          exact finT n c' hstep hq' ht (hoc0 rfl)
            (toA hstep (fun _ h => by cases h) (fun _ w'' e => hh ⟨w'', e⟩) hs)
      case udf code =>
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, rfl⟩ := hsem
        cases hn with
        | halt => exact finT 0 _ hstep trivial nil (hoc0 rfl) rfl
      case emitIsland nb =>
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          have hQ := realizes_island hq.q hvb hi hstep
          obtain ⟨hq', -, hs⟩ := realizes_zeroNA (Y := fun _ => True) hq hvb hi (.inr ⟨nb, rfl⟩)
            (q_stRel hQ)
          exact finT 0 _ hstep hq' nil (hoc0 rfl) hs
      case jtSequence d ts ridx t1 t2 =>
        obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_jtNA (Y := fun _ => True) hR hq hvb hi hstep
        exact finT n c'' hm hq' ht (hoc0 rfl)
          (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case atomicRmwLoop ty op fl ra ro rd r1 r2 =>
        obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_rmwLoopNA hR hq hvb hi hstep fun ops' hops' => by
          rw [hops] at hops'; cases hops'
          exact (hwr rfl).resolve_right fun h => by simp [MInst.loadForm] at h
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
          (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case atomicCasLoop ty fl ra re rx rd r1 =>
        obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_casLoopNA hR hq hvb hi hstep fun ops' hops' => by
          rw [hops] at hops'; cases hops'
          exact (hwr rfl).resolve_right fun h => by simp [MInst.loadForm] at h
        exact fin Y hYF hYO n c'' hm hq' ht (hoc0 rfl)
          (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case tryCall info ti =>
        have hc : ctl = .goto ti.handlers.length := by
          have hsem := R.sem_csem hsem
          simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
          obtain ⟨_, -, -, -, h⟩ := hsem; exact h.symm
        subst hc
        cases hn with
        | goto hk1 hsucc hitems =>
          obtain ⟨n, c'', hm, hq', ht, ⟨i0, hi0, hc0, hnc⟩, hs⟩ := realizes_tryCallNA (Y := fun _ => True)
            hR hC (hT (hasTryCall_of_mem hvb hi)) hP hq hvb hi hops hsz hsem hlen hk1 hsucc hitems rfl
          exact fin1T n c'' hm hq' ht (by rw [hoc]; exact countIn_one_of hi0 hc0 hnc)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)
      case elfTlsGetAddr nm rd tmp =>
        have hv := ctlCheck_inst hck hvb hi
        simp only [ctlInstOk, Bool.and_eq_true] at hv
        obtain ⟨d, rfl⟩ := isVregInt_iff hv.1
        obtain ⟨t, rfl⟩ := isVregInt_iff hv.2
        have hsem' := hsem
        simp only [RL.sem, csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
        obtain ⟨-, -, rfl⟩ := hsem'
        cases hn with
        | next hk =>
          obtain ⟨n, c'', hm, hq', ht, hs⟩ := realizes_tlsNA (Y := fun _ => True) hR
            (hTls (hasTls_of_mem hvb hi)) hq hvb hi hops hsz hsem hlen hk
          exact finT n c'' hm hq' ht (hoc0 rfl)
            (toA hm (fun _ h => by cases h) (fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h) hs)

/-- **`realizes_allCW` on the reads-only guard** (`realizesQWA` on `realizes_stepCWS`). -/
theorem realizes_allCWS {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP P R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) {s : Arm.ArmState} {j : Nat} {ps1 : PState} {T : List Line}
    {c c' : MConf CV Arm.ArmState} (hq : QWA R s j ps1 T c) (hP : P s)
    (hG : MStep R.vc (R.semGS Ok) ckeep R.rf c c') :
    ∃ n c'', MStep R.vc (R.semGS Ok) ckeep R.rf c c'' ∧ MConf.ShapeEq c'' c' ∧
      QWA R (iterN R.step n s) (R.nextW j ps1 T c c'').1 (R.nextW j ps1 T c c'').2.1
        (R.nextW j ps1 T c c'').2.2 c'' ∧
      (∀ i < n, R.GoodX (iterN R.step i s) ∧ R.WReadsIn Ok (iterN R.step i s)) ∧
      countIn R.CallSt R.step s n = opCalls R.vc c ∧ R.SegLenA j ps1 T c c'' s n := by
  obtain ⟨n, c'', hm, hsh, hq', ht, hc, hs, -⟩ :=
    realizesQWA (Tr := fun u => R.GoodX u ∧ R.WReadsIn Ok u) (Ex := fun _ _ => True) hR
      (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ hvb hi h => rets_mstepGS hvb hi h)
      (fun s j ps1 T b src dst its m w hq hs =>
        let ⟨n, h1, h2, h3⟩ := realizes_moveNA (Y := fun _ => True) hR hq hs
        ⟨n, h1, fun i hi => ⟨(h2 i hi).1.1, fun _ => True, fun _ _ => trivial,
          .inl fun _ => trivial, (h2 i hi).2⟩, countIn_zero_of fun i hi => (h2 i hi).1.2, h3,
          trivial⟩)
      (fun hq hA hns =>
        let ⟨n, c'', h1, h2, h3, h4, h5, h6, h7⟩ :=
          realizes_stepCWS hR Ok hC hT hTls hcov hq hA hP hG hns
        ⟨n, c'', h1, h2, h3, h4, h5, h6, h7, trivial⟩) hq hG
  exact ⟨n, c'', hm, hsh, hq', ht, hc, hs⟩

/-- **`realizes_allC_spW` on the reads-only guard.** -/
theorem realizes_allC_spWS {R : RL} (hR : R.Wf) {P : Arm.ArmState → Prop}
    (Ok : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hC : CalleeOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
      R.vc.CallSite R.gv)
    (hT : R.vc.hasTryCall = true →
      CalleeTryOkGP (fun u => P u ∧ spOf u = R.spB) R.F R.K R.G R.s0 (CallAt R.fa R.base) R.X R.H
        R.vc.TrySite R.gv)
    (hTls : R.vc.hasTls = true → TlsOk R.F R.K R.X R.H)
    (hcov : FormsCovered R.ctx R.vc) (s₀ : Arm.ArmState) (W₀ : Nat × PState × List Line)
    (c₀ : MConf CV Arm.ArmState) :
    RealizesCP R.vc R.rf (R.semGS Ok) ckeep R.step
      (fun u c => ∃ l W, R.SegChain (fun u => R.Good u ∧ R.WReadsIn Ok u) s₀ W₀ c₀ l u W c ∧
        QWA R u W.1 W.2.1 W.2.2 c)
      (fun u => R.GoodX u ∧ R.WReadsIn Ok u) R.CallSt P := by
  intro s c c' ⟨l, W, hch, hq⟩ hP h
  have hsp : spOf s = R.spB := by
    cases c with
    | run st =>
      obtain ⟨b, its, m, w⟩ := st
      obtain ⟨mt, hq'⟩ := qa_q hq.qa
      exact (q_stRel hq').sp
    | _ => cases h
  obtain ⟨n, c'', hm, -, hq', ht, hcnt, hs⟩ := realizes_allCWS hR Ok hC hT hTls hcov hq ⟨hP, hsp⟩ h
  exact ⟨n, c'', hm, ⟨_, _, .snoc hch hs fun i hi => ⟨(ht i hi).1.good, (ht i hi).2⟩, hq'⟩, ht, hcnt⟩

end Backend.Proof
