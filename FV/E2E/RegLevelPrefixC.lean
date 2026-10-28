import FV.E2E.RegLevelCorrectC

/-!
# The counted register level up to call `N` (SEM1 #537, item (d), docs/plans/uninit.md §5.9)

`regLevelCorrect_world_atC` needs the callee contract of every index `n`. The prefix form needs
only the contracts of the calls `j < N`, and concludes, for every state of the counted VCode run
with counter `N` at a call instruction, a state of the machine run with `N` call states before
it (`OnCall … N`) at the call, with the VCode world (`SameWorld F`) and the VCode arguments in
the argument registers (`useVals`), i.e. the premises of the call-`N` contract at that state
(`CallSiteAt`).

* `ExtSemI.upTo XI N`: the calls `j < N` of `XI`, failing calls from `N` on; its contracts of
  index `j ≥ N` are vacuous (`calleeOkGP_upTo_ge`, `calleeTryOkGP_upTo_ge`), and the counted VCode
  run of `XI` to counter `N` is one of `XI.upTo N` (`vstar_upTo`);
* `isSimulation_match`, `match_init`: `checkedAt_sound` with its relation `Match` named;
  `match_op_uses` (at an instruction item the machine's operands are the VCode's);
* `CallSiteAt`, **`regLevel_prefixC`**.
-/

namespace Backend.Proof

open Backend E2E Backend.Proof.Driver

/-! ## The calls before `N` -/

/-- **The calls `j < N` of `XI`**; the calls from `N` on fail. -/
def ExtSemI.upTo (XI : ExtSemI) (N : Nat) : ExtSemI :=
  { XI with call := fun j => if j < N then XI.call j else fun _ _ _ => none }

theorem ExtSemI.upTo_at_lt (XI : ExtSemI) {N j : Nat} (h : j < N) : (XI.upTo N).at j = XI.at j := by
  simp [ExtSemI.at, ExtSemI.upTo, h]

theorem ExtSemI.upTo_at_ge (XI : ExtSemI) {N j : Nat} (h : N ≤ j) :
    (XI.upTo N).at j = { XI.at j with call := fun _ _ _ => none } := by
  simp [ExtSemI.at, ExtSemI.upTo, Nat.not_lt.2 h]

theorem csemV_call_congr (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (X : ExtSem) (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState))
    {i : MInst} (h : i.isCallI = false) :
    csemV gv F ctx { X with call := c } i = csemV gv F ctx X i := by
  funext uses w
  unfold csemV
  split
  · simp [MInst.isCallI] at h
  · simp [MInst.isCallI] at h
  · exact congrFun (congrFun (csem_call_congr F ctx X c h) uses) w

theorem csemV_noCall_call {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {X : ExtSem} {i : MInst} (h : i.isCallI = true) (uses : List CV) (w : Arm.ArmState) :
    csemV gv F ctx { X with call := fun _ _ _ => none } i uses w = none := by
  cases hs : csemV gv F ctx { X with call := fun _ _ _ => none } i uses w with
  | none => rfl
  | some r =>
    have h2 := csemV_sub hs
    cases i <;> simp_all [MInst.isCallI, csem]

/-- The counted semantics of `XI.upTo N` agrees with `XI`'s at the counters `j < N` and on the
non-calls. -/
theorem csemVI_upTo_eq (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (XI : ExtSemI) {N j : Nat} {i : MInst} (h : j < N ∨ i.isCallI = false) :
    csemV gv F ctx ((XI.upTo N).at j) i = csemV gv F ctx (XI.at j) i := by
  rcases h with h | h
  · rw [XI.upTo_at_lt h]
  · exact csemV_call_congr gv F ctx (XI.at j) _ h

/-- The counter of a counted VCode configuration. -/
def vctr {V W : Type} : VConf V (W × Nat) → Nat
  | .run vs => vs.w.2
  | .ret _ w => w.2
  | .halt w => w.2

theorem vnext_ctr {V W : Type} {vc : VCode} {b k n : Nat} {i : MInst} {uses : List V}
    {ρ : Nat → V} {w : W × Nat} {ctl : Ctl} {c : VConf V (W × Nat)}
    (h : VNext vc b k n i uses ρ w ctl c) : vctr c = w.2 := by
  cases h <;> rfl

/-- A counted VCode step does not decrease the counter, and a call step increments it. -/
theorem vstep_counted_ctr {V W : Type} {vc : VCode} {sem : Nat → ISem V W}
    {v v' : VConf V (W × Nat)} (h : VStep vc (ISem.counted sem) v v') :
    vctr v ≤ vctr v' ∧ ∀ b k ρ w vb i, v = .run ⟨b, k, ρ, w⟩ → vc.blocks[b]? = some vb →
      vb.insts[k]? = some i → i.isCallI = true → vctr v < vctr v' := by
  cases h with
  | @step b k ρ w vb i ops outs w' ctl c' hvb hi hops hsem hlen hn =>
    have hc := vnext_ctr hn
    obtain ⟨-, hw⟩ := ISem.counted_some hsem
    refine ⟨?_, fun b' k' ρ' w'' vb' i' he hvb' hi' hcall => ?_⟩
    · show w.2 ≤ _
      rw [hc, hw]; split <;> omega
    · cases he
      rw [hvb] at hvb'; cases hvb'
      rw [hi] at hi'; cases hi'
      show w.2 < _
      rw [hc, hw]; simp [hcall]

theorem vstar_counted_ctr {V W : Type} {vc : VCode} {sem : Nat → ISem V W}
    {v v' : VConf V (W × Nat)} (h : Star (VStep vc (ISem.counted sem)) v v') : vctr v ≤ vctr v' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h1 _ ih => exact Nat.le_trans (vstep_counted_ctr h1).1 ih

/-- **A counted run to counter `≤ N` uses only the calls `j < N`**: it is a run of any family
agreeing with `sem` at the counters `j < N` and on the non-calls. -/
theorem vstar_counted_upTo {V W : Type} {vc : VCode} {sem sem' : Nat → ISem V W} {N : Nat}
    (hag : ∀ j i, (j < N ∨ i.isCallI = false) → sem j i = sem' j i)
    {v v' : VConf V (W × Nat)} (h : Star (VStep vc (ISem.counted sem)) v v') (hN : vctr v' ≤ N) :
    Star (VStep vc (ISem.counted sem')) v v' := by
  induction h with
  | refl => exact .refl _
  | @step v1 v2 v3 h1 h2 ih =>
    refine .step ?_ (ih hN)
    have h23 := vstar_counted_ctr h2
    have hlt := (vstep_counted_ctr h1).2
    cases h1 with
    | @step b k ρ w vb i ops outs w' ctl c' hvb hi hops hsem hlen hn =>
      have heq : sem w.2 i = sem' w.2 i := by
        apply hag
        cases hc : i.isCallI
        · exact .inr rfl
        · exact .inl (Nat.lt_of_lt_of_le (hlt b k ρ w vb i rfl hvb hi hc) (Nat.le_trans h23 hN))
      refine VStep.step hvb hi hops ?_ hlen hn
      simp only [ISem.counted] at hsem ⊢
      rw [← heq]; exact hsem

/-- The counted VCode run of `XI` to counter `≤ N` is one of `XI.upTo N`. -/
theorem vstar_upTo {vc : VCode} {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {XI : ExtSemI} {N : Nat} {v v' : VConf CV (Arm.ArmState × Nat)}
    (h : Star (VStep vc (csemVI gv F ctx XI)) v v') (hN : vctr v' ≤ N) :
    Star (VStep vc (csemVI gv F ctx (XI.upTo N))) v v' :=
  vstar_counted_upTo (sem := fun n => csemV gv F ctx (XI.at n))
    (sem' := fun n => csemV gv F ctx ((XI.upTo N).at n))
    (fun _ _ h => (csemVI_upTo_eq gv F ctx XI h).symm) h hN

/-- From index `N` on, `XI.upTo N`'s call contract is vacuous (its calls fail), given the
hook's pc behaviour. -/
theorem calleeOkGP_upTo_ge {P : Arm.ArmState → Prop} {F : BitVec 64 → Prop} {K : Nat}
    {G : BitVec 64 → Prop} {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop} {XI : ExtSemI}
    {H : ArmHooks} {S : CallInfo → Prop} {gv : Nat → String → Prop} {N j : Nat} (hj : N ≤ j)
    (hpc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (H.call d s) = Arm.r .PC s + 4) :
    CalleeOkGP P F K G s0 Pc ((XI.upTo N).at j) H S gv := by
  rw [XI.upTo_at_ge hj]
  refine ⟨fun ctx info _ s _ _ _ _ c wh ops regs i' w outs w' _ _ _ _ _ _ _ hsem => ?_, hpc,
    fun _ _ _ _ _ h => by simp at h⟩
  rw [csemV_noCall_call rfl] at hsem; cases hsem

theorem calleeTryOkGP_upTo_ge {P : Arm.ArmState → Prop} {F : BitVec 64 → Prop} {K : Nat}
    {G : BitVec 64 → Prop} {s0 : Arm.ArmState} {Pc : BitVec 64 → MInst → Prop} {XI : ExtSemI}
    {H : ArmHooks} {S : CallInfo → TryInfo → Prop} {gv : Nat → String → Prop} {N j : Nat}
    (hj : N ≤ j) : CalleeTryOkGP P F K G s0 Pc ((XI.upTo N).at j) H S gv := by
  rw [XI.upTo_at_ge hj]
  intro ctx info ti _ c wh ops regs i' s w outs w' s' _ _ _ _ _ _ _ _ _ _ _ hsem
  rw [csemV_noCall_call rfl] at hsem; cases hsem

theorem tlsOk_upTo {F : BitVec 64 → Prop} {K : Nat} {XI : ExtSemI} {H : ArmHooks} {N j : Nat}
    (h : TlsOk F K (XI.at j) H) : TlsOk F K ((XI.upTo N).at j) H :=
  ⟨h.pc, h.seq, h.flags⟩

/-! ## The register allocator's relation, named -/

section
variable {V W : Type} {vc : VCode} {rf : RFunc} {c : CheckCtx} {ins : Array (Option AState)}
  {sem : ISem V W} {keep : Reg → V → V}

/-- `checkedAt_sound` with its relation named (`Match`). -/
theorem isSimulation_match {a0 : AState} (hc : CheckedAt vc rf c ins a0) (r₀ : Reg → V) :
    IsSimulation vc rf sem keep (Match c ins keep r₀) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro cf v c' hR hs
    cases cf with
    | run ms =>
      cases v with
      | run vs =>
        rcases sim_step_at sem keep hc hR hs with ⟨ms', rfl, hmr, hlt⟩ | hr
        · exact .inl ⟨hmr, hlt⟩
        · exact .inr hr
      | ret => exact hR.elim
      | halt => exact hR.elim
    | ret => cases hs
    | halt => cases hs
  · intro cf v v' hR hv
    cases cf with
    | run ms =>
      cases v with
      | run vs => exact sim_progress_at sem keep hc hR hv
      | ret => exact hR.elim
      | halt => exact hR.elim
    | ret => cases v <;> first | exact hR.elim | cases hv
    | halt => cases v <;> first | exact hR.elim | cases hv
  · intro vals m w v hR
    cases v with
    | ret vals' w' => obtain ⟨rfl, rfl, -⟩ := hR; rfl
    | _ => exact hR.elim
  · intro w v hR
    cases v with
    | halt w' => cases hR; rfl
    | _ => exact hR.elim
  · intro s v hR
    cases v with
    | run s' => exact ⟨s', rfl⟩
    | _ => exact hR.elim
  · intro b src dst its m w v hR
    cases v with
    | run vs =>
      obtain ⟨hb, hw, vb, a, out, hvb, hrun, hinv, hedges⟩ := hR
      obtain ⟨-, hrun'⟩ := runItems_move hrun
      exact ⟨hb, hw, vb, _, out, hvb, hrun', Inv_move _ _ hinv, hedges⟩
    | _ => exact hR.elim
  · intro b k a its m w vs hR
    obtain ⟨hb, hw, vb, a, out, hvb, hrun, -⟩ := hR
    obtain ⟨-, hk, -⟩ := runItems_op hrun
    exact ⟨hb.symm, hk.symm, hw.symm⟩

theorem match_init {a0 : AState} (hc : CheckedAt vc rf c ins a0) (m₀ : Loc → V) (ρ₀ : Nat → V)
    (w₀ : W) (hinv0 : Inv keep a0 m₀ ρ₀ (fun r => m₀ (.reg r))) :
    Match c ins keep (fun r => m₀ (.reg r)) (MConf.init rf m₀ w₀) (VConf.init ρ₀ w₀) := by
  obtain ⟨a, out, ha, hrb, hedges⟩ :=
    verifyBlock_ok (hc.blocks 0 (Nat.pos_of_ne_zero hc.nonempty))
  rw [hc.entry] at ha
  cases ha
  obtain ⟨vb, items, hvb, hitems, hrun⟩ := runBlock_ok hrb
  rw [hc.rf_eq] at hitems
  have : rf.blocks[0]! = items := by simp [getElem!_def, hitems]
  simp only [MConf.init, VConf.init, this]
  exact ⟨rfl, rfl, vb, a0, out, hvb, hrun, hinv0, hedges⟩

/-- **At an instruction item the machine's operands are the VCode's.** -/
theorem match_op_uses {a0 : AState} (hc : CheckedAt vc rf c ins a0) {r₀ : Reg → V} {b k : Nat}
    {allocs : Array Loc} {its : List RItem} {m : Loc → V} {w : W} {vs : VState V W}
    (hm : Match c ins keep r₀ (.run ⟨b, .op k allocs :: its, m, w⟩) (.run vs))
    {vb : VBlock} {i : MInst} {ops : Array Operand} (hvb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops) :
    ops.size = allocs.size ∧
    ((ops.zip allocs).toList.filter (·.1.isUse)).map (m ·.2) =
      (ops.toList.filter Operand.isUse).map (vs.ρ ·.vreg) := by
  obtain ⟨hb, -, vb', a, out, hvb', hrun, hinv, -⟩ := hm
  simp only at hb
  subst hb
  rw [hc.vc_eq, hvb] at hvb'; cases hvb'
  obtain ⟨-, hk, i', ops', a', hi', hops', hstep, -⟩ := runItems_op hrun
  subst hk
  rw [hi] at hi'; cases hi'
  rw [hops] at hops'; cases hops'
  obtain ⟨hst, hE, hL, -, -⟩ := stepOp_ok hstep
  obtain ⟨hsz, hdisj⟩ := checkStatic_ok hst
  refine ⟨hsz, uses_eq hsz fun p hp hu => ?_⟩
  have hk : p.1.kind = .use := by simpa [Operand.isUse] using hu
  cases hpos : p.1.pos with
  | early =>
    have := hE p (List.mem_filter.mpr ⟨hp, by simp [hk, hpos]⟩)
    exact hinv _ _ this
  | late =>
    have := hL p (List.mem_filter.mpr ⟨hp, by simp [hk, hpos]⟩)
    refine hinv _ _ (mem_get_defineAll ?_ this)
    intro hm
    obtain ⟨d, hd, e⟩ := List.mem_map.mp hm
    exact hdisj d hd p hp hk e.symm

/-- **Past the pending moves**: from a configuration related to a VCode state at an instruction,
the machine reaches (through the moves, realised under `Q`) the item of that instruction, still
related. -/
theorem match_to_op {a0 : AState} (hc : CheckedAt vc rf c ins a0) {r₀ : Reg → V} {S : Type}
    {step : S → S} {Q : S → MConf V W → Prop} {T : S → Prop}
    (hQ : Realizes vc rf sem keep step Q T) {vb : VBlock} {i : MInst} :
    ∀ (its : List RItem) (b : Nat) (m : Loc → V) (w : W) (vs : VState V W) (s : S),
      Match c ins keep r₀ (.run ⟨b, its, m, w⟩) (.run vs) → Q s (.run ⟨b, its, m, w⟩) →
      vc.blocks[vs.b]? = some vb → vb.insts[vs.k]? = some i →
      ∃ n a its' m', Q (iterN step n s) (.run ⟨b, .op vs.k a :: its', m', w⟩) ∧
        Match c ins keep r₀ (.run ⟨b, .op vs.k a :: its', m', w⟩) (.run vs)
  | [], b, m, w, vs, s, hm, _, hvb, hi => by
    obtain ⟨hb, -, vb', a, out, hvb', hrun, -⟩ := hm
    rw [hc.vc_eq, hvb] at hvb'; cases hvb'
    obtain ⟨hk, -⟩ := runItems_nil hrun
    rw [hk] at hi
    simp at hi
  | .move src dst :: its, b, m, w, vs, s, hm, hq, hvb, hi => by
    obtain ⟨n1, c'', hs, hq', -⟩ := hQ s _ _ hq MStep.move
    cases hs
    obtain ⟨n2, a, its', m', hq2, hm2⟩ := match_to_op hc hQ its b _ w vs _
      ((isSimulation_match (sem := sem) hc r₀).move hm) hq' hvb hi
    exact ⟨n1 + n2, a, its', m', by rw [iterN_add]; exact hq2, hm2⟩
  | .op k a :: its, b, m, w, vs, s, hm, hq, _, _ => by
    have hk : vs.k = k := ((isSimulation_match (sem := sem) hc r₀).at_op hm).2.1
    subst hk
    exact ⟨0, a, its, m, hq, hm⟩

end

/-! ## The prefix theorem -/

/-- **The premises of a call contract at the machine state `u`** for the VCode call `i` with the
arguments `uses` in the world `w` (`CallSoundCtlGP`/`OperandsSoundCtlAtI`'s, without the call's
result): the stack, the kept bytes, the call instruction at the pc, the world outside `F`, and the
arguments in the operand registers. -/
def CallSiteAt (F : BitVec 64 → Prop) (K : Nat) (G : BitVec 64 → Prop) (s0 : Arm.ArmState)
    (fa : FnAsm) (base : BitVec 64) (i : MInst) (uses : List CV) (w u : Arm.ArmState) : Prop :=
  K ≤ (spOf u).toNat ∧ (∀ a, StackBelow K (spOf u) a → F a) ∧ (∀ a, G a → u.mem a = s0.mem a) ∧
  ∃ (c : CheckCtx) (wh : String) (ops : Array Operand) (regs : Array Reg) (i' : MInst),
    i.operands = .ok ops ∧ c.checkStatic wh ops (regs.map .reg) i.clobbers = .ok () ∧
    i.assign regs = .ok i' ∧ CallAt fa base (Arm.r .PC u) i' ∧
    SameWorld F u w ∧ Arm.CheckSPAlignment u ∧ Arm.r .ERR u = .None ∧ useVals ops regs u = uses

theorem armStepX_call_irrel (X : ExtSem)
    (c : Option String → List CV → Arm.ArmState → Option (List CV × Arm.ArmState)) (H : ArmHooks)
    (fa : FnAsm) : ArmStepX { X with call := c } H fa = ArmStepX X H fa := rfl

/-- **The counted register level up to call `N`**: with the callee contracts of the calls
`n < N` only, every state of the counted VCode run with counter `N` at a call instruction is
matched by a state `u` of the machine run with `N` call states before it (`OnCall … N`), at the
call, with the contract's premises for the VCode's arguments and world (`CallSiteAt`). -/
theorem regLevel_prefixC {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm}
    {fb : FnBin} {k : Nat} {cc : CheckCtx} {ins : Array (Option AState)}
    {a0 : AState} (hcheck : CheckedAt vcp rf cc ins a0) (hok : EntryOk a0)
    (halloc : lowerRFunc vcp rf = .ok af)
    (hemit : emitFunc k af = .ok fa) (hlayout : fa.layout = .ok fb) {XI : ExtSemI} {H : ArmHooks}
    {K : Nat} {G : BitVec 64 → Prop} {gv : Nat → String → Prop}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {base ra : BitVec 64} {s : Arm.ArmState} (hent : AbiCall fb base ra s)
    (hres : StackAvail K af s) (hG : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a)
    {N : Nat}
    (hC : ∀ n < N, CalleeOkGP (OnCall (ArmStepX (XI.at 0) H fa) fa base s n)
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
      K G s (CallAt fa base) (XI.at n) H vcp.CallSite gv)
    (hCT : vcp.hasTryCall = true → ∀ n < N, CalleeTryOkGP (OnCall (ArmStepX (XI.at 0) H fa) fa base s n)
      (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K G s
      (CallAt fa base) (XI.at n) H vcp.TrySite gv)
    (hpc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
      Arm.r .PC (H.call d s) = Arm.r .PC s + 4)
    (hTls : vcp.hasTls = true → ∀ n,
      TlsOk (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s) K (XI.at n) H)
    {w₀ : Arm.ArmState} (hbe : BodyEntryW (frameWG K (RAFrame.compute vcp rf).intBase
      (RAFrame.compute vcp rf).size af G s) vcp.EntryArg af s w₀)
    (ρsel : (Loc → CV) → Nat → CV)
    (hsel : ∀ m₀ : Loc → CV, Inv ckeep a0 m₀ (ρsel m₀) (fun r => m₀ (.reg r))) :
    ∃ m₀ : Loc → CV, ∀ b k ρ w vb i,
      Star (VStep vcp (csemVI gv (frameWG K (RAFrame.compute vcp rf).intBase
        (RAFrame.compute vcp rf).size af G s) ⟨fa.k, af.slotBase⟩ XI)) (.run ⟨0, 0, ρsel m₀, (w₀, 0)⟩)
        (.run ⟨b, k, ρ, (w, N)⟩) →
      vcp.blocks[b]? = some vb → vb.insts[k]? = some i →
      (∃ info, i = .call info ∨ ∃ ti, i = .tryCall info ti) → ∀ ops, i.operands = .ok ops →
      ∃ u, OnCall (ArmStepX (XI.at 0) H fa) fa base s N u ∧
        CallSiteAt (frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s)
          K G s fa base i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w u := by
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hlayout
  obtain ⟨body, psF, hb, -, hk⟩ := emitFunc_ok hemit
  subst hk
  let XN := XI.upTo N
  let Rn : Nat → RL := fun n => ⟨vcp, rf, af, fa, fb, lm, base, s, XN.at n, H, psF, K, G, gv⟩
  let R : RL := Rn 0
  have hRn : ∀ n, (Rn n).Wf := fun _ => ⟨⟨cc, ins, a0, hcheck, hok⟩, halloc, hemit, hlayout, hlm,
    by show 4 * fb.words.size ≤ 2 ^ 64; have := hent.fits; omega, hres, ⟨body, hb⟩, hent.program, hG⟩
  have hR : R.Wf := hRn 0
  have hstep : R.step = ArmStepX (XI.at 0) H fa := rfl
  have hC' : ∀ n, CalleeOkGP (OnCall R.step fa base s n) R.F K G s (CallAt fa base) (XN.at n) H
      vcp.CallSite gv := fun n => by
    by_cases h : n < N
    · rw [hstep]; show CalleeOkGP _ _ _ _ _ _ ((XI.upTo N).at n) _ _ _
      rw [XI.upTo_at_lt h]; exact hC n h
    · exact calleeOkGP_upTo_ge (by omega) hpc
  have hCT' : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (OnCall R.step fa base s n) R.F K G s
      (CallAt fa base) (XN.at n) H vcp.TrySite gv := fun ht n => by
    by_cases h : n < N
    · rw [hstep]; show CalleeTryOkGP _ _ _ _ _ _ ((XI.upTo N).at n) _ _ _
      rw [XI.upTo_at_lt h]; exact hCT ht n h
    · exact calleeTryOkGP_upTo_ge (by omega)
  obtain ⟨n0, ht0, hq0, hA0, -⟩ := q_initN hR hent hbe
  let m₀ := locVal R.fr (iterN R.step n0 s)
  have hSim := isSimulation_match (sem := csemVI R.gv R.F R.ctx XN) (keep := ckeep) hcheck
    (fun r => m₀ (.reg r))
  have hinit := match_init (W := Arm.ArmState × Nat) hcheck m₀ (ρsel m₀) (w₀, 0) (hsel _)
  have hP0 : countIn R.CallSt R.step s n0 = 0 := countIn_zero_of fun i hi => (ht0 i hi).2
  have hRz := Realizes.ofStepC (vc := R.vc) (rf := R.rf) (keep := ckeep) (C := R.CallSt) (T := R.Good)
    (Q := fun p c => (Q R p.1 (c.mapW Prod.fst) ∧ AInv R (c.mapW Prod.fst)) ∧ p.2 = c.world.2 ∧
      ∃ i, p = iterN (stepC R.CallSt R.step) i (iterN R.step n0 s, 0)) (by
    refine RealizesCP.countedRun (vc := R.vc) (rf := R.rf) (keep := ckeep)
      (sem := fun n => csemV R.gv R.F R.ctx (XN.at n))
      (Q := fun u c => Q R u c ∧ AInv R c) (T := R.Good) (C := R.CallSt)
      (P := fun n u => OnCall R.step fa base s n u) (s0 := iterN R.step n0 s) (fun n => ?_)
      (onCall_of_run hP0)
    have hq : ∀ u c, Q (Rn n) u c ∧ AInv (Rn n) c ↔ Q R u c ∧ AInv R c := fun u c =>
      and_congr (RL.Q_withX (Rn n) (XN.at 0) u c).symm Iff.rfl
    exact ((realizes_allC (hRn n) (hC' n) (fun h => hCT' h n)
      (fun h => tlsOk_upTo (hTls h n)) hcov).mono_T
      (T' := R.Good) fun _ h => h.good).congr_Q hq)
  refine ⟨m₀, fun b k ρ w vb i hstar hvb hi hcall ops hops => ?_⟩
  have hstar' : Star (VStep R.vc (csemVI R.gv R.F R.ctx XN)) (VConf.init (ρsel m₀) (w₀, 0))
      (.run ⟨b, k, ρ, (w, N)⟩) := vstar_upTo hstar (Nat.le_refl _)
  obtain ⟨n1, c1, ⟨k1, hz1⟩, hr1, -⟩ :=
    forward hSim hRz hstar' hinit ⟨0, ⟨hq0, hA0⟩, rfl, 0, rfl⟩
  cases c1 with
  | ret => exact hr1.elim
  | halt => exact hr1.elim
  | run ms =>
  obtain ⟨b1, its1, m1, w1⟩ := ms
  obtain ⟨n2, al, its', m', ⟨k2, hz2⟩, hm2⟩ := match_to_op (vs := ⟨b, k, ρ, (w, N)⟩) hcheck
    hRz its1 b1 m1 w1 _ hr1 ⟨k1, hz1⟩ hvb hi
  obtain ⟨hb1, hw1, -⟩ := id hm2
  simp only at hb1 hw1
  subst hb1 hw1
  obtain ⟨⟨hq, -⟩, hk2, i2, hi2⟩ := hz2
  rw [iterN_stepC] at hi2
  simp only [Prod.mk.injEq, Nat.zero_add] at hi2
  obtain ⟨hu, hcnt⟩ := hi2
  simp only [MConf.world] at hk2
  subst hk2
  rw [← iterN_add] at hu
  refine ⟨iterN R.step (n1 + n2) (iterN R.step n0 s), ?_, ?_⟩
  · rw [← hstep, hu, hcnt]
    exact onCall_of_run hP0 i2
  · obtain ⟨-, huse⟩ := match_op_uses hcheck hm2 hvb hi hops
    rw [← iterN_add] at hq
    have hq' := hq
    simp only [MConf.mapW] at hq'
    obtain ⟨info, hci⟩ := hcall
    have hcpc : ∀ regs i', al = regs.map Loc.reg → i.assign regs = .ok i' →
        CallAt fa base (Arm.r .PC (iterN R.step (n1 + n2) (iterN R.step n0 s))) i' := by
      rcases hci with rfl | ⟨ti, rfl⟩
      · exact callAt_of_q hq' hvb hi call_hcall
      · exact callAt_of_q hq' hvb hi tryCall_hcall
    obtain ⟨j0, vb0, items0, pre, code, ls, ps1, ps2, T, hvb0, hit, hsplit, hchk, hcode, hls, htr,
      hdrop, hpc', hst⟩ := hq'
    rw [hvb] at hvb0; cases hvb0
    obtain ⟨c1, c2, hc1, hc2, rfl⟩ := itemsCode_cons hcode
    obtain ⟨regs, i0, i', rfl, hi0, hasg, -⟩ := itemCode_op hc1
    rw [hi] at hi0; cases hi0
    obtain ⟨cc', wh, i2', ops2, hi2', hops2, hstat, -⟩ := op_checked hchk
    rw [hi] at hi2'; cases hi2'
    rw [hops] at hops2; cases hops2
    have hm : ∀ r, r.allocatable = true →
        m' (.reg r) = regVal (iterN R.step (n1 + n2) (iterN R.step n0 s)) r := fun r hr =>
      hst.store (.reg r) (fun r' e => by cases e; exact hr) trivial
    have hK : K ≤ (spOf (iterN R.step (n1 + n2) (iterN R.step n0 s))).toNat := by
      rw [hst.sp]; exact RL.K_le hR
    have hF : ∀ a, StackBelow K (spOf (iterN R.step (n1 + n2) (iterN R.step n0 s))) a → R.F a :=
      fun a ha => by rw [hst.sp] at ha; exact RL.below_F (R := R) ha
    refine ⟨hK, hF, hst.gkeep, cc', wh, ops, regs, i', hops, hstat, hasg, hcpc regs i' rfl hasg,
      hst.world, hst.align, hst.err, ?_⟩
    rw [← useVals_of_store hstat hm]; exact huse

end Backend.Proof
