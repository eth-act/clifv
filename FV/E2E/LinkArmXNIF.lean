import FV.E2E.LinkArmLockRet
import FV.E2E.LinkArmTwinCE
import FV.E2E.LinkArmStage2Prog
import FV.E2E.LinkArmStage2Base
import FV.E2E.PairDriverF

/-!
# Non-interference at the exterior of the link's guarded call semantics (SEM1 #537, #713)

The two-run lock of an activation (`backend_twoRunLERWZIUPF_either`) runs both entries in the
paired semantics of one `XI`, the canonical activation's `XPBTGY` (the induction step's guarded
semantics), and asks its call `n` to be non-interfering at the exterior `F` (`XNIF`) at every
call the CLIF run of count `n` admits. Two worlds `w`, `w'` that agree outside `F` (masked
registers free) are compared:

* a base call (every invocation of count `n` is a base extern): stage 2 holds at every world
  (`stage2Y_base`), so both answers are `Xb`'s, and `Ok.baseNI` (under `NeedNI`) relates them;
* a call of a function `h` of `P`: the guard's predicate (`CallPostNXR` of the invocation of
  count `n`) is the same at `w` and `w'` (`callPostXR_progTransfer`: the program callee's
  stack-passed arguments are in the caller's outgoing area, outside `F`, `Ok.outFits`), and the
  unguarded answers are related (`progXBT_rel`): the worlds with the call's prophecies
  (`worldPR … (P n) (R n)`) have the same registers but the pc, the prophecy in the callee
  region and memories equal outside `F`; the condition `CondBT` carries over (the canonical
  callee table by `CallTwinCET` one level down, the canonical table given, `tableOf_twinC`),
  and the canonical callee runs
  from both return with the same results and worlds equal outside `F` (`progCallPRBRLR`). A
  guard whose predicate is the same at both worlds and respects the relation keeps it, also for
  its ε-chosen answers (`guardR_rel`).

Results: `guardR_rel`, `r_w_congrX`, `r_setReg_congrX`, `placeArgs_r_congrX`, `r_canon_congr`,
**`progXBT_rel`**, `callPost_progTransfer`, `callPostXR_progTransfer`, `worldPR_rel`,
**`xnifXPBTGY`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem choose_eq_of_eq {α : Type} {p q : α → Prop} (e : p = q) (hp : ∃ x, p x)
    (hq : ∃ x, q x) : Classical.choose hp = Classical.choose hq := by
  subst e; rfl

/-- **A guard keeps a relation of the answers** at two worlds where its predicate is the same
and respects the relation (the ε-chosen answers coincide). -/
theorem guardR_rel {X : ExtSem}
    {Q : Option String → List CV → Arm.ArmState → List CV × Arm.ArmState → Prop}
    {d : Option String} {uses : List CV} {w w' : Arm.ArmState}
    (Rr : List CV × Arm.ArmState → List CV × Arm.ArmState → Prop) (hrefl : ∀ r, Rr r r)
    (hQ : ∀ r r', Rr r r' → (Q d uses w r ↔ Q d uses w' r'))
    (hnone : X.call d uses w = none ↔ X.call d uses w' = none)
    (hX : ∀ r r', X.call d uses w = some r → X.call d uses w' = some r' → Rr r r')
    {r r' : List CV × Arm.ArmState} (h : (X.guardR Q).call d uses w = some r)
    (h' : (X.guardR Q).call d uses w' = some r') : Rr r r' := by
  have e : Q d uses w = Q d uses w' := funext fun r => propext (hQ r r (hrefl r))
  have hexi : (∃ r', Q d uses w r') ↔ ∃ r', Q d uses w' r' := by rw [e]
  have halli : (∀ r', Q d uses w r') ↔ ∀ r', Q d uses w' r' := by rw [e]
  simp only [ExtSem.guardR] at h h'
  cases hx : X.call d uses w with
  | none =>
    have hx' := hnone.1 hx
    rw [hx] at h
    rw [hx'] at h'
    dsimp only at h h'
    by_cases hc : (∃ r', Q d uses w r') ∧ ¬ ∀ r', Q d uses w r'
    · have hc' : (∃ r', Q d uses w' r') ∧ ¬ ∀ r', Q d uses w' r' :=
        ⟨hexi.1 hc.1, fun h2 => hc.2 (halli.2 h2)⟩
      rw [dif_pos hc] at h
      rw [dif_pos hc'] at h'
      cases h
      cases h'
      rw [choose_eq_of_eq e hc.1 hc'.1]
      exact hrefl _
    · rw [dif_neg hc] at h
      cases h
  | some a =>
    cases hx' : X.call d uses w' with
    | none => exact absurd (hnone.2 hx') (by simp [hx])
    | some b =>
      have hab := hX a b hx hx'
      have hq := hQ a b hab
      rw [hx] at h
      rw [hx'] at h'
      dsimp only at h h'
      by_cases hqa : Q d uses w a
      · rw [if_pos hqa] at h
        rw [if_pos (hq.1 hqa)] at h'
        cases h
        cases h'
        exact hab
      · rw [if_neg hqa] at h
        rw [if_neg (fun h2 => hqa (hq.2 h2))] at h'
        by_cases hex : ∃ r', Q d uses w r'
        · rw [dif_pos hex] at h
          rw [dif_pos (hexi.1 hex)] at h'
          cases h
          cases h'
          rw [choose_eq_of_eq e hex (hexi.1 hex)]
          exact hrefl _
        · rw [dif_neg hex] at h
          rw [dif_neg (fun h2 => hex (hexi.2 h2))] at h'
          cases h
          cases h'
          exact hab

theorem r_w_congrX {s t : Arm.ArmState} (h : ∀ f, f ≠ .PC → Arm.r f s = Arm.r f t)
    (g : Arm.StateField) (v : Arm.state_value g) {f : Arm.StateField} (hf : f ≠ .PC) :
    Arm.r f (Arm.w g v s) = Arm.r f (Arm.w g v t) := by
  by_cases hfg : f = g
  · subst hfg; rw [Arm.r_of_w_same, Arm.r_of_w_same]
  · rw [Arm.r_of_w_different hfg, Arm.r_of_w_different hfg]; exact h f hf

theorem r_setReg_congrX {s t : Arm.ArmState} (h : ∀ f, f ≠ .PC → Arm.r f s = Arm.r f t)
    (r : Reg) (v : CV) {f : Arm.StateField} (hf : f ≠ .PC) :
    Arm.r f (setReg s r v) = Arm.r f (setReg t r v) := by
  cases r <;> simp only [setReg] <;> first | exact r_w_congrX h _ _ hf | exact h f hf

/-- `placeArgs` keeps an agreement on the registers but the pc. -/
theorem placeArgs_r_congrX : ∀ (rs : List Reg) (us : List CV) {s t : Arm.ArmState},
    (∀ f, f ≠ .PC → Arm.r f s = Arm.r f t) →
    ∀ f, f ≠ .PC → Arm.r f (placeArgs rs us s) = Arm.r f (placeArgs rs us t)
  | [], _, _, _, h, f, hf => h f hf
  | _ :: _, [], s, t, h, f, hf => by rw [placeArgs_nil_right, placeArgs_nil_right]; exact h f hf
  | r :: rs, u :: us, _, _, h, f, hf => by
    rw [placeArgs_cons, placeArgs_cons]
    exact placeArgs_r_congrX rs us (fun f' hf' => r_setReg_congrX h r u hf') f hf

namespace LinkSys

variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The canonical state's registers depend on the world's registers but the pc only.** -/
theorem r_canon_congr (g : Clif.Function) (uses : List CV) {w w' : Arm.ArmState}
    (h : ∀ f, f ≠ .PC → Arm.r f w = Arm.r f w') (f : Arm.StateField) :
    Arm.r f (L.canon g uses w) = Arm.r f (L.canon g uses w') := by
  simp only [canon]
  by_cases hf : f = .PC
  · subst hf; rw [Arm.r_of_w_same, Arm.r_of_w_same]
  · rw [Arm.r_of_w_different hf, Arm.r_of_w_different hf]
    exact placeArgs_r_congrX _ _ (fun f' hf' => by rw [r_withImg, r_withImg]; exact h f' hf') f hf

set_option maxHeartbeats 1000000 in
/-- **The program call answer at two worlds with the same registers but the pc, the same
callee region and memories equal outside `F`**: one is defined iff the other is (`CondBT`
carries over, the callee table by `CallTwinCET`), with the same results and worlds equal outside
`F` (`progCallPRBRLRU`). -/
theorem progXBT_rel (hL : L.Ok) [hR : L.CrunOk] {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    (htw : 0 < M → L.CallTwinCET κ M) {h : Clif.Function} (hh : h ∈ L.P.funcs)
    (hcal : ∃ g ∈ L.P.funcs, L.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {uses : List CV} {W W' : Arm.ArmState}
    (hr : ∀ f, f ≠ .PC → Arm.r f W = Arm.r f W') (hp : W.program = W'.program)
    (hm : ∀ a, ¬ F a → W.mem a = W'.mem a)
    (hrgn : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv W) a → W.mem a = W'.mem a)
    {o : List CV} {x : Arm.ArmState} (hx : L.progXBT κ M F h uses W = some (o, x)) :
    ∃ x', L.progXBT κ M F h uses W' = some (o, x') ∧ SameWorld F x x' := by
  have hpf := func?_of_mem hL.names hh
  unfold progXBT at hx
  split at hx
  case isFalse => cases hx
  rename_i hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨⟨hM, herr, hal, hroom, hdead, vals, cm, cs, rvals, cm', ini, hmr, hargs, hsav, hpl, htab,
    hinit, hrun⟩, -⟩ := hc
  have hsp : spv W' = spv W := by simp only [spv]; exact (hr _ (by simp)).symm
  have herr' : Arm.r .ERR W' = .None := by rw [← hr _ (by simp)]; exact herr
  have hmr' : MemRel F L.syms cm W' := by
    refine ⟨fun a b ha hb => ?_, hmr.valid, hmr.symbols⟩
    have hF := (hmr.valid a 1 ha).2 0 (by omega)
    simp only [Nat.add_zero] at hF
    rw [← hmr.bytes a b ha hb]
    simp only [Arm.read_mem, Arm.read_store]
    rw [hm _ hF]
  have hargs' : ArgsAt h.sig vals uses W' :=
    ⟨hargs.1, hargs.2.1, fun off v hmz => by
      rw [show spOf W' = spOf W from hsp]
      have e := hargs.2.2 off v hmz
      rw [← e]
      congr 1
      exact read_mem_bytes_congr _ _ fun k hk => (hm _ (hsav off v hmz k hk)).symm⟩
  have hsav' : StackArgsAvoid F h.sig vals W' := fun off v hmz => by
    rw [hsp]; exact hsav off v hmz
  have hpl' : L.NeedSlots → L.PlaceAtB cm (spv W') ini ∧ ∀ a, L.SlotByte h (spv W') a →
      ini.bytes (ini.next + 1) a = W'.mem (BitVec.ofNat 64 a) := fun hN => by
    obtain ⟨h1, h2⟩ := hpl hN
    rw [hsp]
    refine ⟨h1, fun a ha => ?_⟩
    obtain ⟨g, hg, hcg⟩ := hcal
    rw [h2 a ha, hrgn _ (stackBelow_mono (L.slotByte_below hL hg hcg (by omega) ha).1
      (Nat.le_add_right _ _))]
  -- the canonical states
  have hc0 := L.callerOk_canon hL hh himgF uses W
  have hc1 := L.callerOk_canon hL hh himgF uses W'
  have hsw : SameWorld F W' W :=
    ⟨fun f hf => (hr f (fun e => by subst e; exact hf trivial)).symm, fun a ha => (hm a ha).symm,
      hp.symm⟩
  have hcok : L.CallerOk F h uses W (L.canon h uses W') :=
    ⟨hc1.world.trans hsw, hc1.img,
      fun r hr' => L.regVal_canon_eq hL hh (argsAt_regLocs hargs) W W' r hr', hc1.ra⟩
  have hmsk : ∀ f, Masked f → f ≠ .PC → f ≠ .GPR 30#5 →
      Arm.r f (L.canon h uses W') = Arm.r f (L.canon h uses W) :=
    fun f _ _ _ => L.r_canon_congr h uses (fun f hf => (hr f hf).symm) f
  have hdd : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv W) a →
      (L.canon h uses W').mem a = (L.canon h uses W).mem a := fun a ha => by
    rw [L.mem_canon, L.mem_canon, mem_withImg, mem_withImg]
    by_cases hi : L.Img a
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi]; exact (hrgn a ha).symm
  -- the canonical callee table at the other world
  have htwc := htw hM h.name h hpf hcal F himgF uses W herr hal hroom hdead vals cm cs rvals cm' ini
    hmr hargs hsav (fun hN => (hpl hN).1) (fun hN => (hpl hN).2) (L.tableOfE_of htab) hinit hrun _
    hcok hmsk hdd
  have htab' : L.TableOf (M - 1) h (enterAt (L.A h) (L.canon h uses W')) (calleeIni h ini) :=
    L.tableOf_twinC (TwinCE.twinC L (TwinCE.symm L htwc)) htab
  have hcond' : L.CondBT κ M F h uses W' :=
    ⟨hM, herr', by rw [hsp]; exact hal, by rw [hsp]; exact hroom,
      fun a ha => hdead a (by rw [← hsp]; exact ha), vals, cm, cs, rvals, cm', ini, hmr', hargs',
      hsav', hpl', htab', hinit, hrun⟩
  -- the canonical callee runs from both canonical states
  obtain ⟨us, outs, wf, e, hus, hlen, hhold, -, hrs, -, hall⟩ := L.progCallPRBRLRU hL hM (ih hM)
    (hdet hM) hpf hcal himgF herr hal hroom hdead hmr hargs hsav (fun hN => (hpl hN).1)
    (fun hN => (hpl hN).2) htab hinit hrun
  obtain ⟨k₀, hpc₀, hret₀, -⟩ := hall _ hc0 (fun _ _ _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨k, hpc, hret, -⟩ := hall _ hcok hmsk hdd
  have herrt : Arm.r .ERR (L.pcall M h (L.canon h uses W')) = .None := by
    rw [hpc, r_set_program]; exact hret.ret.err
  -- the callee's declared results are among the defs of its return site (an `sret` pointer is
  -- returned in x8 after them, #587)
  have hlenR : rvals.length = h.sig.returns.length := by
    have hce := clifEntry_initState hpf hinit
    obtain ⟨Nr, hrunN⟩ := hR.runs M cs _ hrun (.inl ⟨_, _, rfl⟩)
    have hrt := Clif.runLoop_returned_tys hL.free Nr cs rvals cm' (runInv_entry hh hce) hrunN
    have hbot : cs.bottom = h := by simp [Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    have e := congrArg List.length hrt
    simpa only [List.length_map, Clif.AbiParam.tys] using e
  have hsr : h.sig.returns.length ≤ us.length := by
    have := hhold.1
    omega
  have hres : ∀ (u : Arm.ArmState) (kk : Nat) (Y : BitVec 64 → Prop) (G : BitVec 64 → Prop),
      ActRet (Arm.r .PC u + 4) Y G us outs wf (enterAt (L.A h) u)
        (runX (L.mach (M - 1) h) kk (enterAt (L.A h) u)) →
      ∀ j (hj : j < h.sig.returns.length),
        regVal (Arm.set_program (runX (L.mach (M - 1) h) kk (enterAt (L.A h) u)) u.program)
          (.x j) = outs[j]'(by omega) := by
    intro u kk Y G hr j hj
    have hju : j < us.length := by omega
    have hus_j : us[j]? = some ((us[j]'hju).1, Reg.x j) := by
      have := congrArg (·[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some, Option.some.injEq] at this
      rw [retX_lt (show j < rvals.length by omega)] at this
      rw [List.getElem?_eq_getElem hju, ← this]
    rw [regVal_set_program, hr.regs j _ _ _ hus_j (List.getElem?_eq_getElem _)]
  refine ⟨L.pcall M h (L.canon h uses W'), ?_, ?_⟩
  · unfold progXBT
    rw [if_pos ⟨hcond', herrt⟩]
    congr 2
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    rw [hpc, hpc₀, hres _ k _ _ hret j h1, hres _ k₀ _ _ hret₀ j h1]
  · rw [hpc₀, hpc]
    refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
    · rw [r_set_program, r_set_program]
      by_cases h29 : f = .GPR 29#5
      · subst h29
        have e1 := hret₀.ret.savedX 29 (by unfold calleeSavedX; decide)
        have e2 := hret.ret.savedX 29 (by unfold calleeSavedX; decide)
        simp only [xreg] at e1 e2
        rw [show (BitVec.ofNat 5 29) = 29#5 from rfl] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp)]
        exact L.r_canon_congr h uses hr _
      by_cases h31 : f = .GPR 31#5
      · subst h31
        have e1 := hret₀.ret.sp
        have e2 := hret.ret.sp
        simp only [spv] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp)]
        exact L.r_canon_congr h uses hr _
      rw [hret₀.fields f hf h29 h31, hret.fields f hf h29 h31]
    · rw [mem_set_program, mem_set_program, hret₀.mem a ha, hret.mem a ha]
    · rw [program_set_program, program_set_program, L.program_canon, L.program_canon]
      exact hp

/-- **The accepted results of a program invocation do not depend on the world outside `F`**:
when every invocation `A` admits is of a function of `P`, a result accepted at `w` is accepted,
up to the world outside `F`, at a world `w'` that agrees with `w` outside `F` (the stack-passed
arguments are in the caller's outgoing area, outside `F`, `Ok.outFits`). -/
theorem callPost_progTransfer (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F : BitVec 64 → Prop} {c : BitVec 64} {A : String → List Clif.Val → Clif.Mem → Prop}
    (hA : ∀ nm vals cm, A nm vals cm → (L.P.func? nm).isSome)
    {d : Option String} {uses : List CV} {w w' : Arm.ArmState} (hsw : SameWorld F w w')
    {r r' : List CV × Arm.ArmState} (hr1 : r.1 = r'.1) (hr2 : SameWorld F r.2 r'.2)
    (hcp : CallPost ((L.envOfB M g c).only A) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w r) :
    CallPost ((L.envOfB M g c).only A) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w' r' := by
  refine ⟨fun ext hin G sl cm args vals rvals cm' hG hd hargs hmr hret hlen => ?_,
    fun sig hs m G sl cm u args vals rvals cm' hdn hu hG hsg hlo h8 hall hmr hret hlen hty => ?_⟩
  · have hmr0 := mrStable_relW _ g c sl cm w' w hsw.toNF hmr
    obtain ⟨hAi, hb | ⟨h, hpf, -, -, cs', hinit, -⟩⟩ := L.envOfB_only_some hG hret
    · exact absurd (hA _ _ _ hAi) (by simp [hb.1])
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    have hsig := hL.declSig g hg ext hin h hpf
    rw [hsig] at hargs
    -- the stack-passed arguments are in the caller's outgoing area, outside `F`
    have hsav : StackArgsAvoid F h.sig vals w' := by
      intro off v hm k hk
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      rw [List.getElem?_zip_eq_some] at hi
      obtain ⟨hli, hvi⟩ := hi
      have hty := (clifEntry_initState (f := h) (by rw [hname]; exact hpf)
        (by rw [hname]; exact hinit)).sig
      obtain ⟨p, hp⟩ : ∃ p, h.sig.params[i]? = some p := by
        have := congrArg (·[i]?) hty
        simp only [List.getElem?_map, hvi, Option.map_some] at this
        cases hp : h.sig.params[i]? with
        | none => rw [hp] at this; cases this
        | some p => exact ⟨p, rfl⟩
      have hvp : v.ty = p.ty := by
        have := congrArg (·[i]?) hty
        simp only [List.getElem?_map, hvi, hp, Option.map_some, Option.some.injEq] at this
        exact this
      have hfit := hL.outFits g hg ext hin (by simp [hpf]) i off p (by rw [hsig]; exact hli)
        (by rw [hsig]; exact hp)
      rw [hvp] at hk
      rw [add_ofNat_add]
      have hav : Avoids F (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase (spv w') := hmr.1.2.2.2.1
      exact hav (off + k) (by omega)
    have hargs0 : ArgsAt ext.sig vals args w := by
      rw [hsig]
      refine ⟨hargs.1, hargs.2.1, fun off v hmz => ?_⟩
      rw [show spOf w = spOf w' from hsw.1 (.GPR 31#5) (by simp [Masked])]
      have e := hargs.2.2 off v hmz
      rw [← e]
      congr 1
      exact read_mem_bytes_congr _ _ fun k hk => hsw.2.1 _ (hsav off v hmz k hk)
    obtain ⟨h1, h2, h3⟩ := hcp.1 ext hin G sl cm args vals rvals cm' hG hd hargs0 hmr0 hret hlen
    exact ⟨hr1 ▸ h1, hr1 ▸ h2, mrStable_relW _ g c sl cm' _ _ hr2.symm.toNF h3⟩
  · have hmr0 := mrStable_relW _ g c sl cm w' w hsw.toNF hmr
    obtain ⟨h1, h2, h3⟩ := hcp.2 sig hs m G sl cm u args vals rvals cm' hdn hu hG hsg hlo h8 hall
      hmr0 hret hlen hty
    exact ⟨hr1 ▸ h1, hr1 ▸ h2, mrStable_relW _ g c sl cm' _ _ hr2.symm.toNF h3⟩

/-- **`callPost_progTransfer` for the guard's predicate** (`CallPostXR`). -/
theorem callPostXR_progTransfer (hL : L.Ok) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F : BitVec 64 → Prop} {c : BitVec 64} {A : String → List Clif.Val → Clif.Mem → Prop}
    (hA : ∀ nm vals cm, A nm vals cm → (L.P.func? nm).isSome)
    {d : Option String} {uses : List CV} {w w' : Arm.ArmState} (hsw : SameWorld F w w')
    {r r' : List CV × Arm.ArmState} (hr1 : r.1 = r'.1) (hr2 : SameWorld F r.2 r'.2)
    (hcp : CallPostXR ((L.envOfB M g c).only A) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w r) :
    CallPostXR ((L.envOfB M g c).only A) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w' r' := by
  refine ⟨L.callPost_progTransfer hL hg hA hsw hr1 hr2 hcp.1, fun hn hE => ?_⟩
  have hn0 : ¬ ∀ r'', CallPost ((L.envOfB M g c).only A) (g.externs.map (·.2)) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩ g c)
      L.Xb.sym d uses w r'' := fun hall => hn fun r'' =>
    L.callPost_progTransfer hL hg hA hsw rfl (SameWorld.refl F _) (hall r'')
  have hE0 : Arm.r .ERR w = .None := by rw [hsw.1 .ERR (by simp [Masked])]; exact hE
  obtain ⟨e1, e2⟩ := hcp.2 hn0 hE0
  exact ⟨by rw [← hr2.1 .ERR (by simp [Masked])]; exact e1,
    by rw [← hr2.2.2, e2]; exact hsw.2.2⟩

/-- **The worlds with a call's prophecies at two worlds agreeing outside `F`**: the same
registers but the pc, the same program, memories equal outside `F` and in the callee region. -/
theorem worldPR_rel {M : Nat} (h : Clif.Function) (Pn : BitVec 64 → BitVec 8) (Sn : Arm.ArmState)
    {F : BitVec 64 → Prop} {w w' : Arm.ArmState} (hsw : SameWorld F w w') :
    (∀ f, f ≠ .PC → Arm.r f (L.worldPR κ M h Pn Sn w) = Arm.r f (L.worldPR κ M h Pn Sn w')) ∧
      (L.worldPR κ M h Pn Sn w).program = (L.worldPR κ M h Pn Sn w').program ∧
      (∀ a, ¬ F a → (L.worldPR κ M h Pn Sn w).mem a = (L.worldPR κ M h Pn Sn w').mem a) ∧
      (∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv (L.worldPR κ M h Pn Sn w)) a →
        (L.worldPR κ M h Pn Sn w).mem a = (L.worldPR κ M h Pn Sn w').mem a) := by
  have hsp : spv w = spv w' := hsw.1 (.GPR 31#5) (by simp [Masked])
  have hspW : spv (L.worldPR κ M h Pn Sn w) = spv w :=
    L.r_worldPR_out h Pn Sn w (fun hm => (by simp [Masked] : ¬ Masked (.GPR 31#5)) hm.1)
  have hrg : L.calleeRgn κ M h w' = L.calleeRgn κ M h w := by
    unfold calleeRgn; rw [hsp]
  refine ⟨fun f hf => ?_, by rw [L.program_worldPR, L.program_worldPR]; exact hsw.2.2,
    fun a ha => ?_, fun a ha => ?_⟩
  · by_cases hmr : MaskedReg f
    · rw [L.r_worldPR_in h Pn w hmr, L.r_worldPR_in h Pn w' hmr]
    · rw [L.r_worldPR_out h Pn Sn w hmr, L.r_worldPR_out h Pn Sn w' hmr]
      exact hsw.1 f (fun hM => hmr ⟨hM, hf⟩)
  · rw [L.mem_worldPR, L.mem_worldPR, worldP, worldP, hrg]
    by_cases hR : L.calleeRgn κ M h w a
    · rw [mem_overlay_in hR, mem_overlay_in hR]
    · rw [mem_overlay_out hR, mem_overlay_out hR]; exact hsw.2.1 a ha
  · rw [hspW] at ha
    have hR : L.calleeRgn κ M h w a := ha
    rw [L.mem_worldPR, L.mem_worldPR, worldP, worldP, hrg, mem_overlay_in hR, mem_overlay_in hR]

set_option maxHeartbeats 1000000 in
/-- **Step 1 of the determinism induction: `XNIF` of the induction step's guarded semantics**
(module doc): call `n` of `XPBTGY` at the calls the CLIF run of count `n` admits, under
`NeedNI`, from `ThmPRBRL`/`DetPRBRU` (#732) one level down and `CallTwinCET` at this level. -/
theorem xnifXPBTGY (hL : L.Ok) [hR : L.CrunOk] (hN : L.NeedNI) {M : Nat}
    (ih : 0 < M → L.ThmPRBRL κ (M - 1)) (hdet : 0 < M → L.DetPRBRU κ (M - 1))
    (htw : 0 < M → L.CallTwinCET κ M) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) (P : Nat → BitVec 64 → BitVec 8)
    (R : Nat → Arm.ArmState) {c : BitVec 64} {cs : Clif.State}
    (hnrc : NoRetCall (L.envOfB M g c) L.P.bare cs) {s : Clif.State} {n : Nat}
    (hs : ReachN (L.envOfB M g c) L.P.bare cs s n) :
    XNIF F L.syms (g.externs.map (·.2)) (indSigs g) c
      (CallLg ((L.envOfB M g c).only (Clif.Invoked (L.envOfB M g c) L.P.bare s))
        (g.externs.map (·.2)) (indSigs g))
      ((L.XPBTGY κ M g F P R (L.envOfB M g c) cs c).at n) := by
  intro nm sig vals cm args d uses w w' o x o' x' hlg hd hsw hm hm' hc1 hc2 hA hx hx'
  obtain ⟨hkind, G, rv, cm'', hG, hGo⟩ := hlg
  have hinvN := invoked_sub_invokedN hnrc hs _ _ _ (L.envOfB_only_some hG hGo).1
  obtain ⟨-, hb | ⟨h, hpf, hmay, -, -, -, -⟩⟩ := L.envOfB_only_some hG hGo
  · -- a base call: both answers are `Xb`'s
    obtain ⟨hpf, G0, hG0, hr0⟩ := hb
    have hbN : ∀ nm' vals' m', InvokedN (L.envOfB M g c) L.P.bare cs n nm' vals' m' →
        L.P.func? nm' = none := fun nm' vals' m' hi => by
      obtain ⟨rfl, -, -⟩ := invokedN_unique hinvN hi; exact hpf
    have hx1 := L.XPBTGY_sub hL (L.stage2Y_base hL hg F P R c cs c (fun u => u = w) n hbN) rfl
      (SameWorld.refl F w) hx
    have hx1' := L.XPBTGY_sub hL (L.stage2Y_base hL hg F P R c cs c (fun u => u = w') n hbN) rfl
      (SameWorld.refl F w') hx'
    have hbase := hL.baseNI hN g hg F c nm sig vals cm args d uses F w w' o x o' x'
      ⟨hpf, hkind, G0, rv, cm'', hG0, hr0⟩ hd (fun _ h => h) hsw hm hm' hc1 hc2 hA
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.XPRBT_base hpf] at hx1 hx1'
      exact hbase hx1 hx1'
    · have hsc : symCallee L.Xb L.P (lo64 u) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
        rw [hu]; exact (L.find_sym hL nm).2 hpf
      rw [L.XPRBT_none hsc] at hx1 hx1'
      exact hbase hx1 hx1'
  · -- a call of a function of `P`
    obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    have hpN : ∀ nm' vals' m', InvokedN (L.envOfB M g c) L.P.bare cs n nm' vals' m' →
        (L.P.func? nm').isSome := fun nm' vals' m' hi => by
      obtain ⟨rfl, -, -⟩ := invokedN_unique hinvN hi; simp [hpf]
    have hcal : ∃ g' ∈ L.P.funcs, L.Callee g' h :=
      ⟨g, hg, .inr (.inr ⟨hh, by rw [hname]; exact hmay⟩)⟩
    obtain ⟨hWr, hWp, hWm, hWg⟩ := L.worldPR_rel (κ := κ) (M := M) h (P n) (R n) hsw
    obtain ⟨hWr', hWp', hWm', hWg'⟩ := L.worldPR_rel (κ := κ) (M := M) h (P n) (R n) hsw.symm
    -- the unguarded answers relate
    have key : ∀ args' : List CV,
        (L.progXPRBT κ M F h args' (P n) (R n) w = none ↔
          L.progXPRBT κ M F h args' (P n) (R n) w' = none) ∧
        ∀ r r', L.progXPRBT κ M F h args' (P n) (R n) w = some r →
          L.progXPRBT κ M F h args' (P n) (R n) w' = some r' → r.1 = r'.1 ∧ SameWorld F r.2 r'.2 := by
      intro args'
      have fw : ∀ r : List CV × Arm.ArmState, L.progXPRBT κ M F h args' (P n) (R n) w = some r →
          ∃ x2, L.progXPRBT κ M F h args' (P n) (R n) w' = some (r.1, x2) ∧ SameWorld F r.2 x2 :=
        fun r hr => L.progXBT_rel hL ih hdet htw hh hcal himgF hWr hWp hWm hWg hr
      have bw : ∀ r : List CV × Arm.ArmState, L.progXPRBT κ M F h args' (P n) (R n) w' = some r →
          ∃ x2, L.progXPRBT κ M F h args' (P n) (R n) w = some (r.1, x2) :=
        fun r hr => (L.progXBT_rel hL ih hdet htw hh hcal himgF hWr' hWp' hWm' hWg' hr).imp
          fun _ h => h.1
      refine ⟨⟨fun h0 => ?_, fun h0 => ?_⟩, fun r r' h1 h2 => ?_⟩
      · cases e : L.progXPRBT κ M F h args' (P n) (R n) w' with
        | none => rfl
        | some r => obtain ⟨_, h2⟩ := bw r e; rw [h0] at h2; cases h2
      · cases e : L.progXPRBT κ M F h args' (P n) (R n) w with
        | none => rfl
        | some r => obtain ⟨_, h2, -⟩ := fw r e; rw [h0] at h2; cases h2
      · obtain ⟨x2, h3, h4⟩ := fw r h1
        rw [h2] at h3
        cases h3
        exact ⟨rfl, h4⟩
    have hXr : ((L.XPRBT κ M g F P R n).call d uses w = none ↔
          (L.XPRBT κ M g F P R n).call d uses w' = none) ∧
        ∀ r r', (L.XPRBT κ M g F P R n).call d uses w = some r →
          (L.XPRBT κ M g F P R n).call d uses w' = some r' → r.1 = r'.1 ∧ SameWorld F r.2 r'.2 := by
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
      · rw [L.XPRBT_prog hpf, L.XPRBT_prog hpf]
        exact key _
      · have hsc : symCallee L.Xb L.P (lo64 u) = some h := by
          show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
          rw [hu]; exact (L.find_sym hL nm).1 h hpf
        rw [L.XPRBT_ind hsc, L.XPRBT_ind hsc]
        by_cases hcnd : L.IndTo g h ∧ args.length = (regLocs h.sig).length
        · rw [if_pos hcnd, if_pos hcnd]
          exact key args
        · rw [if_neg hcnd, if_neg hcnd]
          exact ⟨Iff.rfl, fun _ _ h1 => by cases h1⟩
    have hQ : ∀ r r' : List CV × Arm.ArmState, r.1 = r'.1 ∧ SameWorld F r.2 r'.2 →
        (CallPostNXR (L.envOfB M g c) L.P.bare cs (g.externs.map (·.2)) (indSigs g)
          (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
            g c) L.Xb.sym n d uses w r ↔
        CallPostNXR (L.envOfB M g c) L.P.bare cs (g.externs.map (·.2)) (indSigs g)
          (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
            g c) L.Xb.sym n d uses w' r') := fun _ _ hr =>
      ⟨L.callPostXR_progTransfer (M := M) (c := c) hL hg hpN hsw hr.1 hr.2,
        L.callPostXR_progTransfer (M := M) (c := c) hL hg hpN hsw.symm hr.1.symm hr.2.symm⟩
    exact guardR_rel (X := L.XPRBT κ M g F P R n) (fun r r' => r.1 = r'.1 ∧ SameWorld F r.2 r'.2)
      (fun _ => ⟨rfl, SameWorld.refl F _⟩) hQ hXr.1 hXr.2 hx hx'

end LinkSys

end E2E
