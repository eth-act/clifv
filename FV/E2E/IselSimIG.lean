import FV.E2E.IselSimITry
import FV.E2E.RegLevelCorrectI

/-!
# CLIF → counted VCode for any counted family of semantics (SEM1 #537, item (3))

`sim_runI` (`IselSimI.lean`, `IselSimITry.lean`) is stated for `csemI F fctx XI` on the Arm world.
The determinism clause needs the same counted simulation for the paired semantics
(`pairSem (csem F fctx (XI.at n))` on two worlds, one counter). The proofs only use that the
non-call instructions do not read the call number (`NcIndep`) and that the probe semantics of a
step without calls projects into the counted one (`NoCallProj`); here they are restated for any
world `W` and family `semF` with its probes `semN` (the proofs are copies with `semF n` for
`csem F fctx (XI.at n)`; the `csem` statements stay):

* `NcIndep`, `NoCallProj`, `counted_noncall`, `counted_call`, `MRIG`;
* `SeqEnd.liftG`, **`seqRun_counted_le1`**;
* `stmt_stepI_noCallG`, `stmt_stepI_callG`, `term_stepIG`, `term_step_tryIG`, **`sim_runIG`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {W : Type}

/-- **The non-call instructions do not read the call number.** -/
def NcIndep (semF : Nat → ISem CV W) : Prop :=
  ∀ m n i, i.isCallI = false → semF m i = semF n i

/-- **The probe semantics `semN n` projects into the counted one at counter `n`.** -/
def NoCallProj (semF semN : Nat → ISem CV W) : Prop :=
  ∀ n, ISem.ProjW (fun w => (w, n)) (semN n) (ISem.counted semF)

/-- The counted relation: `MR` on the first component. -/
def MRIG (MR : MemRelTW W) : MemRelTW (W × Nat) := fun sl cm w => MR sl cm w.1

theorem counted_noncall {semF : Nat → ISem CV W} (hI : NcIndep semF) {i : MInst}
    (h : i.isCallI = false) (uses : List CV) (w : W) (n n' : Nat) :
    ISem.counted semF i uses (w, n) = (semF n' i uses w).map
      fun r => (r.1, (r.2.1, n), r.2.2) := by
  simp only [ISem.counted, h, Bool.false_eq_true, ↓reduceIte, hI n n' i h]

theorem counted_call {semF : Nat → ISem CV W} {i : MInst}
    (h : i.isCallI = true) (uses : List CV) (w : W) (n : Nat) :
    ISem.counted semF i uses (w, n) = (semF n i uses w).map
      fun r => (r.1, (r.2.1, n + 1), r.2.2) := by
  simp only [ISem.counted, h, ↓reduceIte]

/-- `SeqEnd.liftI` on any world. -/
def SeqEnd.liftG (ms : List MInst) (n : Nat) : SeqEnd CV W → SeqEnd CV (W × Nat)
  | .fall ρ w => .fall ρ (w, n + callsI ms)
  | .stop k i ops ρ w outs w' ctl =>
    .stop k i ops ρ (w, n + callsI (ms.take k)) outs
      (w', n + callsI (ms.take k) + if i.isCallI then 1 else 0) ctl

theorem SeqEnd.liftG_noncall {i : MInst} (hi : i.isCallI = false) (ms : List MInst) (n : Nat)
    (e : SeqEnd CV W) : (SeqEnd.liftG ms n e).succ = SeqEnd.liftG (i :: ms) n e.succ := by
  cases e with
  | fall ρ w => simp [SeqEnd.liftG, SeqEnd.succ, callsI_cons, hi]
  | stop k j ops ρ w outs w' ctl =>
    simp [SeqEnd.liftG, SeqEnd.succ, List.take_succ_cons, callsI_cons, hi]

theorem SeqEnd.liftG_call {i : MInst} (hi : i.isCallI = true) {ms : List MInst}
    (h0 : callsI ms = 0) (n : Nat) (e : SeqEnd CV W) :
    (SeqEnd.liftG ms (n + 1) e).succ = SeqEnd.liftG (i :: ms) n e.succ := by
  cases e with
  | fall ρ w => simp [SeqEnd.liftG, SeqEnd.succ, callsI_cons, hi, h0]
  | stop k j ops ρ w outs w' ctl =>
    simp [SeqEnd.liftG, SeqEnd.succ, List.take_succ_cons, callsI_cons, hi, callsI_take_zero h0,
      Nat.add_assoc, Nat.add_comm 1]

/-- `seqRun_csemI_le1_at` for a counted family. -/
theorem seqRun_counted_le1_at {semF : Nat → ISem CV W} (hI : NcIndep semF) :
    ∀ (ms : List MInst) (m n : Nat), callsI ms ≤ 1 → (callsI ms = 1 → m = n) →
      ∀ (ρ : Nat → CV) (w : W),
        seqRun (ISem.counted semF) ms ρ (w, n) =
          (seqRun (semF m) ms ρ w).map (SeqEnd.liftG ms n)
  | [], _, n, _, _, ρ, w => by simp [seqRun, SeqEnd.liftG]
  | i :: ms, m, n, hle, hmn, ρ, w => by
    simp only [seqRun]
    cases ho : i.operands with
    | error _ => rfl
    | ok ops =>
      simp only
      cases hc : i.isCallI with
      | false =>
        have hle' : callsI ms ≤ 1 := by rw [callsI_cons, hc] at hle; simpa using hle
        have hmn' : callsI ms = 1 → m = n := fun h => hmn (by rw [callsI_cons, hc]; simpa using h)
        rw [counted_noncall hI hc _ w n m]
        cases hs : semF m i (vuses ops ρ) w with
        | none => rfl
        | some r =>
          obtain ⟨outs, w', ctl⟩ := r
          simp only [Option.map_some]
          by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
          · simp only [hl, ↓reduceIte]
            cases ctl with
            | next =>
              simp only
              rw [seqRun_counted_le1_at hI ms m n hle' hmn' _ w']
              cases seqRun (semF m) ms (vdefUpd ops outs ρ) w' with
              | none => rfl
              | some e => simp only [Option.map_some, SeqEnd.liftG_noncall hc]
            | goto j => simp [SeqEnd.liftG, hc]
            | ret => simp [SeqEnd.liftG, hc]
            | halt => simp [SeqEnd.liftG, hc]
          · simp only [hl, ↓reduceIte]; rfl
      | true =>
        have h1 : callsI (i :: ms) = callsI ms + 1 := by rw [callsI_cons, hc]; rfl
        have h0 : callsI ms = 0 := by omega
        have e : m = n := hmn (by omega)
        subst e
        rw [counted_call hc _ w m]
        cases hs : semF m i (vuses ops ρ) w with
        | none => rfl
        | some r =>
          obtain ⟨outs, w', ctl⟩ := r
          simp only [Option.map_some]
          by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
          · simp only [hl, ↓reduceIte]
            cases ctl with
            | next =>
              simp only
              rw [seqRun_counted_le1_at hI ms m (m + 1) (by omega) (by omega) _ w']
              cases seqRun (semF m) ms (vdefUpd ops outs ρ) w' with
              | none => rfl
              | some e => simp only [Option.map_some, SeqEnd.liftG_call hc h0]
            | goto j => simp [SeqEnd.liftG, hc]
            | ret => simp [SeqEnd.liftG, hc]
            | halt => simp [SeqEnd.liftG, hc]
          · simp only [hl, ↓reduceIte]; rfl

/-- **A straight-line run with at most one call under a counted family** (`seqRun_csemI_le1`). -/
theorem seqRun_counted_le1 {semF : Nat → ISem CV W} (hI : NcIndep semF) {ms : List MInst}
    (hle : callsI ms ≤ 1) (ρ : Nat → CV) (w : W) (n : Nat) :
    seqRun (ISem.counted semF) ms ρ (w, n) = (seqRun (semF n) ms ρ w).map (SeqEnd.liftG ms n) :=
  seqRun_counted_le1_at hI ms n n hle (fun _ => rfl) ρ w

end

section steps
variable {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState} {R : Reg → Reg}
  {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId} {W : Type}
  {semF semN : Nat → ISem CV W} {MR : MemRelTW W} {env : Clif.Env}
  {p : Clif.Program} {slots : List (Clif.SlotId × Nat)}

/-- `stmt_stepI_noCall` for a counted family. -/
theorem stmt_stepI_noCallG (hN : NoCallProj semF semN) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semN n) MR (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hnc : stm.inst.isCallLike = false)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vc (ISem.counted semF)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n)⟩) ∧ Match f ctx R gn bl A MR slots s' ⟨b', k', ρ', w'⟩) ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vc (ISem.counted semF) ⟨b, k, ρ, (w, n)⟩ c) := by
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnc]) (fun _ _ h => by rw [hbody] at h; cases h)
  obtain ⟨S1, S2⟩ := stmt_step Hb hm hbody hind
  have hp := hN n
  refine ⟨fun s' hs => ?_, fun c hs hexp => vTrapFrom_mapW hp (S2 c (hstep.trans hs) hexp)⟩
  obtain ⟨⟨b', k', ρ', w'⟩, hstar, hM⟩ := S1 s' (hstep.trans hs)
  exact ⟨b', k', ρ', w', vstar_mapW hp hstar, hM⟩

/-- `stmt_stepI_call` for a counted family. -/
theorem stmt_stepI_callG (hI : NcIndep semF) {n : Nat} {s : Clif.State}
    (Hs : DriverHyp f vc ctx st0 R gn bl A (semF n) MR (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩)
    {stm : Clif.Stmt} {rest : List Clif.Stmt} (hbody : s.frame.body = stm :: rest)
    (hcl : stm.inst.isCallLike = true)
    (hind : ∀ sig callee args, stm.inst = .callIndirect sig callee args → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vc (ISem.counted semF)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n + 1)⟩) ∧ Match f ctx R gn bl A MR slots s' ⟨b', k', ρ', w'⟩) ∧
    (∀ c, Clif.step env p s = .trapped c → explicitTrapInst stm.inst = true →
      VTrapFrom vc (ISem.counted semF) ⟨b, k, ρ, (w, n)⟩ c) := by
  have hstep : Clif.step (env.only (Clif.Invoked env p s)) p s = Clif.step env p s :=
    Clif.step_only fun _ _ _ h => h
  obtain ⟨B, j, hB, -, hjlt, hstm, rfl, hnext, htrap⟩ := stmt_run Hs hm hbody hind
  obtain ⟨L, hL⟩ := Hs.blow hB
  obtain ⟨vb, hvb, -, -, -, -, -, -, hcode, htne, -⟩ := Hs.shape.blk b B L hB hL
  obtain ⟨hsegat, hlt⟩ := seg_at hcode htne hjlt
  have h1 := hseg b B j stm hB hstm hcl
  have hle : callsI (seg f R bl b j) ≤ 1 := by omega
  refine ⟨fun s' hs => ?_, fun c hs hexp => ?_⟩
  · obtain ⟨ρ', w', hsr, hM⟩ := hnext s' (hstep.trans hs)
    have hsrI : seqRun (ISem.counted semF) (seg f R bl b j) ρ (w, n) =
        some (.fall ρ' (w', n + 1)) := by
      rw [seqRun_counted_le1 hI hle ρ w n, hsr]
      simp [SeqEnd.liftG, h1]
    rw [pos_succ] at hlt hM
    exact ⟨_, _, ρ', w', seqRun_fall_star hvb hsegat hlt hsrI, hM⟩
  · obtain ⟨k', i, ops, ρ₁, w₁, outs, w₂, hsr, htc⟩ := htrap c (hstep.trans hs) hexp
    have hsrI := seqRun_counted_le1 hI hle ρ w n
    rw [hsr] at hsrI
    obtain ⟨hstar, -, hi, hops, hsem, -, -⟩ := seqRun_stop_star hvb hsegat hsrI
    exact ⟨b, _, ρ₁, _, vb, i, ops, outs, _, hstar, hvb, hi, hops, hsem, htc⟩

/-- `term_stepI` for a counted family. -/
theorem term_stepIG (hN : NoCallProj semF semN) {n : Nat}
    (Hb : DriverHyp f vc ctx st0 R gn bl A (semN n) MR (env.only fun _ _ _ => False) p)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    (hnt : s.frame.term.isTry = false) :
    (∀ s', Clif.step env p s = .next s' →
      ∃ b' k' ρ' w', Star (VStep vc (ISem.counted semF)) (.run ⟨b, k, ρ, (w, n)⟩)
        (.run ⟨b', k', ρ', (w', n)⟩) ∧ Match f ctx R gn bl A MR slots s' ⟨b', k', ρ', w'⟩) ∧
    (∀ vals cm, Clif.step env p s = .done vals cm →
      ∃ us outs w' sv, VRetFrom vc (ISem.counted semF) ⟨b, k, ρ, (w, n)⟩ us outs (w', n) ∧
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        s.frame.getMany (sretRet f) = .ok sv ∧ AllHold (vals ++ sv) outs ∧
        MR slots s.mem w' ∧ cm = (s.mem.free (slots.map (·.2))).leave) ∧
    (∀ c, Clif.step env p s = .trapped c →
      VTrapFrom vc (ISem.counted semF) ⟨b, k, ρ, (w, n)⟩ c) := by
  have hnr : ∀ fn args, s.frame.body = [] → s.frame.term ≠ .returnCall fn args := by
    intro fn args _ h
    obtain ⟨-, -, -, -, B, j, hB, hterm, -⟩ := hm
    exact Hb.noTail B (List.mem_of_getElem? hB) fn args (hterm.symm.trans h)
  have hstep : Clif.step (env.only fun _ _ _ => False) p s = Clif.step env p s :=
    step_none_of_callNum (by simp [callNum, hbody, hnt]) hnr
  obtain ⟨T1, T2, T3⟩ := term_step_abi Hb hm hbody hnt
  have hp := hN n
  refine ⟨fun s' hs => ?_, fun vals cm hs => ?_,
    fun c hs => vTrapFrom_mapW hp (T3 c (hstep.trans hs))⟩
  · obtain ⟨⟨b', k', ρ', w'⟩, hstar, hM⟩ := T1 s' (hstep.trans hs)
    exact ⟨b', k', ρ', w', vstar_mapW hp hstar, hM⟩
  · obtain ⟨us, outs, w', sv, hret, h1, h2, h3, h4, h5, h6⟩ := T2 vals cm (hstep.trans hs)
    exact ⟨us, outs, w', sv, vRetFrom_mapW hp hret, h1, h2, h3, h4, h5, h6⟩

/-- **`term_step_tryI` for a counted family** (its proof, `semF n` for `csem F fctx (XI.at n)`). -/
theorem term_step_tryIG (hI : NcIndep semF) {n : Nat}
    (H : DriverHyp f vc ctx st0 R gn bl A (semF n) MR env p) (htc : TryCallsOne f)
    {s : Clif.State} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hm : Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩) (hbody : s.frame.body = [])
    {et : Clif.ExnTable} (hT : IsTryWith s.frame.term et)
    (hind : ∀ callee args, s.frame.term = .tryCallIndirect callee args et → ∀ cv,
      s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat) :
    (∀ vals cm, Clif.step env p s ≠ .done vals cm) ∧
    ∀ s', Clif.step env p s = .next s' →
      (s'.frame.body = [] ∧ ∃ bc, s'.frame.term = .jump bc) ∧
      (∀ c, Clif.step env p s' ≠ .trapped c) ∧ (∀ vals cm, Clif.step env p s' ≠ .done vals cm) ∧
      ∀ s'', Clif.step env p s' = .next s'' →
        ∃ b' k' ρ' w', Star (VStep vc (ISem.counted semF)) (.run ⟨b, k, ρ, (w, n)⟩)
          (.run ⟨b', k', ρ', (w', n + 1)⟩) ∧
          Match f ctx R gn bl A MR slots s'' ⟨b', k', ρ', w'⟩ := by
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
  -- the moves before the call contain no VCode call
  have hpre0 : ∀ pre ci, L.tst'.emitted.toList = pre ++ [.call ci] → callsI pre = 0 := by
    rcases id hBT with ⟨fn, args, hBT'⟩ | ⟨callee, args, hBT'⟩
    · exact htc.1 ctx (L.start + B.body.length) fn args et L.data T.sig T.items L.targets
        T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv ⟨B, hBmem, hBT'⟩ (hBT' ▸ hdata) hexn
        (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun
    · exact htc.2 ctx (L.start + B.body.length) callee args et L.data T.sig T.items L.targets
        T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv ⟨B, hBmem, hBT'⟩ (hBT' ▸ hdata) hexn
        (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun
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
      LowerTryOk (semF n) MR env p
        (tryCtx ctx (L.start + B.body.length) L.data T.regs) ci T.info
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
        fun s' hs => ?_, H.tries.choose_spec.1 ctx (L.start + B.body.length) fn args et L.data
          T.sig T.items L.targets T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv
          (H.tries.choose_spec.2 B hBmem fn args et hBT) hdata' hexn
          (H.shape.tslot b B L hB hL) hinfo hregs hvbL hrun⟩
      obtain ⟨ext, bc, rvals, cm', regs', hx, htn, hO, hset, rfl⟩ := hnx s' hs
      rw [hfunc, hx0] at hx
      cases hx
      exact ⟨bc, rvals, cm', regs', htn, hO, by rw [← hsig0]; exact hset, rfl⟩
    · have hdata' : tryCallData f (.tryCallIndirect callee args et) = .ok L.data := hBT ▸ hdata
      have hsd := exnTableOpnd_sig hexn
      have hsin := H.tryIndSig B hBmem callee args et T.sig hBT hsd
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
          T.info T.regs L.tst T.st1 out L.tst' tr H.shape.ctxInv hdata' hexn hsin
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
  refine ⟨⟨rfl, bc, rfl⟩, fun c h => (stepTerm_branch_ne hjne).2 c (hstep'.symm.trans h),
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
  have hren := seqRun_rename (sem := semF n) (ρ₀ := ρ₀) (ρ := ρ) (w := w)
    H.shape.ren (H.dsem.rename R gn H.shape.ren) hD hdefs
  obtain ⟨ρ₁', hsr', -, hA2⟩ := (hren (huses hU) hAg).2 hsr
  obtain ⟨hsegat, hsize⟩ := tseg_at hcode
  have htseg : tseg R bl b = (pre ++ [MInst.tryCall ci' T.info]).map (·.mapRegs R) := by
    rw [tseg_eq hL, hTl]
    show (tryFix T.info _).map _ = _
    rw [hfix]
  rw [htseg] at hsegat hsize
  obtain ⟨hmk, -⟩ := seqRun_stop_mem hsr
  have hk' : k' = pre.length := by
    rw [hms] at hk1; simp only [List.length_append, List.length_singleton] at hk1; omega
  subst hk'
  have hiT : i = .tryCall ci' T.info := by
    rw [List.getElem?_append_right (Nat.le_refl _)] at hmk
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hmk
    exact hmk.symm
  subst hiT
  -- the counted run of the terminator's code: no call before the `try_call`'s
  have hp0 : callsI pre = 0 := hpre0 pre ci' hms
  have hle : callsI ((pre ++ [MInst.tryCall ci' T.info]).map (·.mapRegs R)) ≤ 1 := by
    rw [callsI_map_mapRegs, callsI_append, hp0]
    simp [callsI, MInst.isCallI]
  have htk : callsI (((pre ++ [MInst.tryCall ci' T.info]).map (·.mapRegs R)).take pre.length) = 0 := by
    rw [List.map_append, List.take_left' (by simp), callsI_map_mapRegs, hp0]
  have hsrI := seqRun_counted_le1 hI hle ρ w n
  rw [hsr'] at hsrI
  simp only [Option.map_some, SeqEnd.liftG, htk, Nat.add_zero, MInst.isCallI] at hsrI
  obtain ⟨hstar, -, hi, hops, hsem, hlen, -⟩ := seqRun_stop_starP hvb hsegat hsrI
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
  have hjump : ISem.counted semF (.jump tl) [] (w₂, n + 1) = some ([], (w₂, n + 1), .goto 0) := by
    rw [counted_noncall hI (by rfl) [] w₂ (n + 1) n, H.dsem.jump tl w₂]
    rfl
  have hstep2 : VStep vc (ISem.counted semF) (.run ⟨tlab, 0, parCopyEnv ρ₂ [] [], (w₂, n + 1)⟩)
      (.run ⟨tl, 0, parCopyEnv ρ₂ (TB.params.map (·.1)) xs, (w₂, n + 1)⟩) := by
    rw [hpc]
    refine VStep.step heb (by rw [hebi]; rfl) (i := .jump tl) (ops := #[]) rfl
      hjump rfl (VNext.goto (by rw [hebi]; rfl) ?_ henv2)
    rw [succOf_eq H.shape.labels hcfg heb hebback]; rfl
  exact ⟨_, _, _, _, hstar.star.trans (.step hstep1 (.single hstep2)), hM⟩

/-- **`sim_runI` for a counted family** (its proof). -/
theorem sim_runIG (hI : NcIndep semF) (hN : NoCallProj semF semN) {cs : Clif.State} (hP : RunPrem env p f cs)
    (Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A (semN n) MR
      (env.only fun _ _ _ => False) p)
    (Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A (semF n) MR
      (env.only (Clif.Invoked env p s)) p)
    (hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1)
    (htc : TryCallsOne f) :
    ∀ fuel s n b k ρ w, ReachN env p cs s n →
      Match f ctx R gn bl A MR slots s ⟨b, k, ρ, w⟩ →
        RunOkAbi vc (ISem.counted semF) (MRIG MR) slots (fun _ => True) ⟨b, k, ρ, (w, n)⟩
          (Clif.runLoop env p fuel s) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
  intro s n b k ρ w hr hm
  cases fuel with
  | zero => trivial
  | succ m =>
    rw [Clif.runLoop_succ]
    have hfunc : s.frame.func = f := hm.2.1
    cases hbody : s.frame.body with
    | nil =>
      cases hty : s.frame.term.isTry with
      | false =>
        obtain ⟨T1, T2, T3⟩ := term_stepIG hN (Hb n) hm hbody hty
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hty]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := T1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbi.prefix hstar h
        | done vals cm =>
          obtain ⟨us, outs, w', sv, hret, h1, h2, hsv, h3, h4, h5⟩ := T2 vals cm hs
          exact ⟨us, outs, (w', n), s.mem, sv, hret, h1, h2, trivial, h3, h4, h5⟩
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
          fun callee args ht => hP.tryIndirect s callee args et hr.reach hbody ht
            ⟨B, hBmem, hterm.symm.trans ht⟩
        obtain ⟨Tnd, Tnx⟩ := term_step_tryIG hI (Hs s n hr) htc hm hbody hT hind
        have hst : Clif.step (env.only (Clif.Invoked env p s)) p s = Clif.step env p s :=
          Clif.step_only fun _ _ _ h => h
        have hc1 : callNum s = 1 := by simp [callNum, hbody, hty]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨⟨hb', bc, ht'⟩, N1, N2, N3⟩ := Tnx s' (hst.trans hs)
          have hst' : Clif.step (env.only (Clif.Invoked env p s)) p s' = Clif.step env p s' := by
            apply Clif.step_only
            intro _ _ _ ⟨_, hI⟩
            simp [hb', ht'] at hI
          have hc0 : callNum s' = 0 := by simp [callNum, hb', ht', Clif.Terminator.isTry]
          cases m with
          | zero => trivial
          | succ m' =>
            show RunOkAbi vc (ISem.counted semF) (MRIG MR) slots (fun _ => True) _
              (Clif.runLoop env p (m' + 1) s')
            rw [Clif.runLoop_succ]
            cases hs' : Clif.step env p s' with
            | next s'' =>
              obtain ⟨b', k', ρ', w', hstar, hm'⟩ := N3 s'' (hst'.trans hs')
              have h := ih m' (by omega) s'' (n + callNum s + callNum s') b' k' ρ' w'
                ((hr.snoc hs).snoc hs') hm'
              rw [hc1, hc0, Nat.add_zero] at h
              exact RunOkAbi.prefix hstar h
            | done vals cm => exact absurd (hst'.trans hs') (N2 vals cm)
            | trapped c => exact absurd (hst'.trans hs') (N1 c)
            | stuck => trivial
        | done vals cm => exact absurd (hst.trans hs) (Tnd vals cm)
        | trapped c =>
          rcases hT with ⟨fn, args, hT⟩ | ⟨callee, args, hT⟩
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCall s c fn args et hr.reach hs hbody hT B hBmem)
          · exact absurd (hterm.symm.trans hT)
              (hP.tryCallInd s c callee args et hr.reach hs hbody hT B hBmem)
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
        exact (Hb n).ext B hBmem st hst fn args hi e (hfunc ▸ he)
      have hind : ∀ sig callee args, st.inst = .callIndirect sig callee args → ∀ cv,
          s.frame.get callee = .ok cv → ∀ g ∈ p.funcs, s.mem.symbols g.name ≠ some cv.toNat :=
        fun sig callee args hi => hP.indirect s st rest sig callee args hr.reach hbody hi
          ⟨B, hBmem, hst⟩
      cases hcl : st.inst.isCallLike with
      | false =>
        obtain ⟨S1, S2⟩ := stmt_stepI_noCallG hN (Hb n) hm hbody hcl hind
        have hc0 : callNum s = 0 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc0, Nat.add_zero] at h
          exact RunOkAbi.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c => exact S2 c hs (hP.stmt s c st rest hr.reach hs hbody)
        | stuck => trivial
      | true =>
        obtain ⟨S1, S2⟩ := stmt_stepI_callG hI (Hs s n hr) hseg hm hbody hcl hind
        have hc1 : callNum s = 1 := by simp [callNum, hbody, hcl]
        cases hs : Clif.step env p s with
        | next s' =>
          obtain ⟨b', k', ρ', w', hstar, hm'⟩ := S1 s' hs
          have h := ih m (by omega) s' (n + callNum s) b' k' ρ' w' (hr.snoc hs) hm'
          rw [hc1] at h
          exact RunOkAbi.prefix hstar h
        | done vals cm => exact absurd hs (stmt_not_done hbody hext hind)
        | trapped c => exact S2 c hs (hP.stmt s c st rest hr.reach hs hbody)
        | stuck => trivial


end steps

end E2E
