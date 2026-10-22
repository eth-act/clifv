import FV.E2E.LinkArmUInd
import FV.E2E.WorldUnwindNI

/-!
# The linking statement with unwinding with non-interference (S10f, #233)

`LinkSys.progX_ni`/`xni`/`xTls`/`thm_of` (`FV/E2E/LinkArm.lean`) for the linked machine with
unwinding, without `¬ NeedNI`: the non-interference of an activation's normal callees (`xniU`,
`XNI` for `XU`) and of its raising callees (`xrniU`, `XRNI` for `XRU`: a program callee's raise
from `progCallUN`'s non-interference clause, a base callee's from `OkUNI.baseRaiseNI`), and the
induction step by the per-function world theorem with non-interference
(`backend_correct_world_ni_pipelineU`, `FV/E2E/WorldUnwindNI.lean`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

namespace LinkSysU

variable (L : LinkSysU)
variable {κ : Nat → Clif.Function → Nat}

/-- **The base premise of non-interference with unwinding**: two raises of a base callee (outside
`P`) from worlds agreeing outside `Z ⊇ F`, related to the same CLIF memory, with the same
stack pointer and arguments, give worlds that agree outside `Z` (`XRNI`, `baseNI`'s counterpart;
needed only when the linking needs non-interference). -/
structure OkUNI : Prop where
  baseRaiseNI : L.NeedNI → ∀ g ∈ L.P.funcs, ∀ F c, XRNI F L.syms (g.externs.map (·.2)) (indSigs g)
    c (fun n sig vals cm => L.P.func? n = none ∧
      CallLgR L.envX (g.externs.map (·.2)) (indSigs g) n sig vals cm) L.Xb L.XRb

/-- Two returns (or raises) from caller states related to `w`, `w'` (agreeing outside `Z ⊇ F`),
whose memory outside `F` resp. `Z` and fields are `wf`'s, give worlds agreeing outside `Z`. -/
theorem sameWorld_endsZ {a : Art} {F Z : BitVec 64 → Prop} (hFZ : ∀ x, F x → Z x)
    {t c w w' rs rc wf : Arm.ArmState} (ht : SameWorld F t w) (hc : SameWorld F c w')
    (hsw : SameWorld Z w w')
    (rts : ArmRet (Arm.r .PC t + 4) (enterAt a t) rs)
    (rtc : ArmRet (Arm.r .PC c + 4) (enterAt a c) rc)
    (ms : ∀ x, ¬ F x → rs.mem x = wf.mem x) (mc : ∀ x, ¬ Z x → rc.mem x = wf.mem x)
    (fs : ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f rs = Arm.r f wf)
    (fc : ∀ f, ¬ Masked f → f ≠ .GPR 29#5 → f ≠ .GPR 31#5 → Arm.r f rc = Arm.r f wf) :
    SameWorld Z (Arm.set_program rs t.program) (Arm.set_program rc c.program) := by
  refine ⟨fun f hf => ?_, fun x hx => ?_, ?_⟩
  · rw [r_set_program, r_set_program]
    by_cases h29 : f = .GPR 29#5
    · subst h29
      have e1 := rts.savedX 29 (by decide)
      have e2 := rtc.savedX 29 (by decide)
      simp only [xreg] at e1 e2
      rw [show (BitVec.ofNat 5 29) = 29#5 from rfl] at e1 e2
      rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
        ht.1 _ hf, hc.1 _ hf, hsw.1 _ hf]
    by_cases h31 : f = .GPR 31#5
    · subst h31
      have e1 := rts.sp
      have e2 := rtc.sp
      simp only [spv] at e1 e2
      rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
        ht.1 _ hf, hc.1 _ hf, hsw.1 _ hf]
    · rw [fs f hf h29 h31, fc f hf h29 h31]
  · simp only [mem_set_program]
    rw [ms x (fun hf => hx (hFZ x hf)), mc x hx]
  · simp only [program_set_program]
    rw [ht.2.2, hc.2.2, hsw.2.2]

/-- **Non-interference of a call of a function `h` of `P` that returns** (`progX_ni`'s
counterpart). -/
theorem progXU_ni (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX] (hN : L.NeedNI) {M : Nat}
    (ih : 0 < M → L.ThmU κ (M - 1)) {g h : Clif.Function} (hg : g ∈ L.P.funcs)
    (hh : h ∈ L.P.funcs) (hcallee : L.Callee g h) {F Z : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (hFZ : ∀ a, F a → Z a) {w w' : Arm.ArmState}
    (hsw : SameWorld Z w w') {cm : Clif.Mem} {vals : List Clif.Val} {args : List CV}
    (hm : MemRel F L.syms cm w) (hm' : MemRel F L.syms cm w') (ha : ArgsAt h.sig vals args w)
    (ha' : ArgsAt h.sig vals args w') {cs : Clif.State} {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hpl : L.NeedSlots → L.PlaceAt cm (spv w)) (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crunX M cs = .returned rvals cm') {o o' : List CV}
    {x x' : Arm.ArmState} (hx : L.progXU κ M F h args w = some (o, x))
    (hx' : L.progXU κ M F h args w' = some (o', x')) : o = o' ∧ SameWorld Z x x' := by
  have hpf := func?_of_mem hL.names hh
  unfold progXU at hx hx'
  split at hx
  case isFalse => cases hx
  rename_i hc
  split at hx'
  case isFalse => cases hx'
  simp only [Option.some.injEq, Prod.mk.injEq] at hx hx'
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨rfl, rfl⟩ := hx'
  obtain ⟨⟨hM, herr, hal, hroom, hdead, vals1, cm1, cs1, -, -, hsav1, -, hinit1, -⟩, -⟩ := hc
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hty : vals.map (·.ty) = vals1.map (·.ty) := by
    rw [(clifEntry_initState hpf hinit).sig, (clifEntry_initState hpf hinit1).sig]
  have hsav := LinkSys.stackArgsAvoid_tys hsav1 hty
  obtain ⟨us, outs, wf, hus, hlen, hhold, -, hrs, hall, hni⟩ :=
    (L.progCallUN hL hU (M := M') (ih hM) hpf ⟨g, hg, hcallee⟩ himgF herr hal hroom hdead hm ha
      hsav hpl hinit).1 rvals cm' hrun
  have hc0 := L.callerOk_canon hL hh himgF args w
  have hc1 := L.callerOk_canon hL hh himgF args w'
  have hsp' : spv w' = spv w := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨k, heq, -, hret⟩ := hall _ hc0
  obtain ⟨k', heq', hret'⟩ := hni hN Z (L.canon h args w') hFZ
    ((SameWorld.mono hFZ hc1.world).trans hsw.symm) hc1.img
    (L.toLinkSys.regVal_canon_eq hL hh (argsAt_regLocs ha) w w') hc1.ra
    (L.toLinkSys.memRel_canon himgF hm' h args)
    (fun off v hmz j hj => by
      rw [L.mem_canon, mem_withImg, if_neg (fun hi => hsav off v hmz j hj (himgF _ hi))]
      exact LinkSys.stackArgs_bytes ha.2.2 ha'.2.2 hsp' off v hmz j hj)
  have hsr : (sigRets h.sig).length ≤ us.length := by
    cases hs : h.sig.params.any (·.purpose == .sret)
    · have hce := clifEntry_initState hpf hinit
      obtain ⟨Nr, hrunN⟩ := hR.runs (M' + 1) cs _ hrun (.inl ⟨_, _, rfl⟩)
      have hrt := Clif.runLoopX_returned_tys hL.free Nr cs.toX rvals cm'
        (Clif.initState_xinv hinit) hrunN
      have hbot : cs.toX.s.bottom = h := by
        simp [Clif.State.toX, Clif.State.bottom, hce.callers, hce.func]
      rw [hbot] at hrt
      have e := congrArg List.length hrt
      simp only [List.length_map, Clif.AbiParam.tys] at e
      rw [sigRets_of_noSret hs, ← e]
      have := hhold.1
      omega
    · exact hL.sretRets h hh hs us hrs
  have hres : ∀ (u : Arm.ArmState) (kk : Nat) (Y : BitVec 64 → Prop) (G : BitVec 64 → Prop),
      ActRet (Arm.r .PC u + 4) Y G us outs wf (enterAt (L.A h) u)
        (runX (L.machU M' h) kk (enterAt (L.A h) u)) →
      ∀ j (hj : j < (sigRets h.sig).length),
        regVal (Arm.set_program (runX (L.machU M' h) kk (enterAt (L.A h) u)) u.program)
          (.x j) = outs[j]'(by omega) := by
    intro u kk Y G hr j hj
    have hju : j < us.length := by omega
    have hus_j : us[j]? = some ((us[j]'hju).1, Reg.x j) := by
      have := congrArg (·[j]?) hus
      simp only [List.getElem?_map, List.getElem?_range hju, List.getElem?_eq_getElem hju,
        Option.map_some, Option.some.injEq] at this
      rw [List.getElem?_eq_getElem hju, ← this]
    rw [regVal_set_program, hr.regs j _ _ _ hus_j (List.getElem?_eq_getElem _)]
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    rw [heq, heq', hres _ k _ _ hret j h1, hres _ k' _ _ hret' j h1]
  · rw [heq, heq']
    exact sameWorld_endsZ hFZ hc0.world hc1.world hsw hret.ret hret'.ret hret.mem hret'.mem
      hret.fields hret'.fields

/-- **Non-interference of a call of a function `h` of `P` that raises.** -/
theorem progXR_ni (hL : L.Ok) (hU : L.OkU) [hR : L.CrunOkX] (hN : L.NeedNI) {M : Nat}
    (ih : 0 < M → L.ThmU κ (M - 1)) {g h : Clif.Function} (hg : g ∈ L.P.funcs)
    (hh : h ∈ L.P.funcs) (hcallee : L.Callee g h) {F Z : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (hFZ : ∀ a, F a → Z a) {w w' : Arm.ArmState}
    (hsw : SameWorld Z w w') {cm : Clif.Mem} {vals : List Clif.Val} {args : List CV}
    (hm : MemRel F L.syms cm w) (hm' : MemRel F L.syms cm w') (ha : ArgsAt h.sig vals args w)
    (ha' : ArgsAt h.sig vals args w') {cs : Clif.State} {e : Clif.Exn} {cm' : Clif.Mem}
    (hpl : L.NeedSlots → L.PlaceAt cm (spv w)) (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crunX M cs = .unwound e cm') {o o' : BitVec 64}
    {x x' : Arm.ArmState} (hx : L.progXR κ M F h args w = some (o, x))
    (hx' : L.progXR κ M F h args w' = some (o', x')) : SameWorld Z x x' := by
  have hpf := func?_of_mem hL.names hh
  obtain ⟨hc, hpr, -, -, -⟩ := L.progXR_ext hx
  obtain ⟨-, hpr', -, -, -⟩ := L.progXR_ext hx'
  obtain ⟨hM, herr, hal, hroom, hdead, vals1, cm1, cs1, -, -, hsav1, -, hinit1, -⟩ := hc
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hty : vals.map (·.ty) = vals1.map (·.ty) := by
    rw [(clifEntry_initState hpf hinit).sig, (clifEntry_initState hpf hinit1).sig]
  have hsav := LinkSys.stackArgsAvoid_tys hsav1 hty
  obtain ⟨obj, wf, -, -, hall, hni⟩ :=
    (L.progCallUN hL hU (M := M') (ih hM) hpf ⟨g, hg, hcallee⟩ himgF herr hal hroom hdead hm ha
      hsav hpl hinit).2 e cm' hrun
  have hc0 := L.callerOk_canon hL hh himgF args w
  have hc1 := L.callerOk_canon hL hh himgF args w'
  have hsp' : spv w' = spv w := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨k, heq, hret⟩ := hall _ hc0
  obtain ⟨k', heq', hret'⟩ := hni hN Z (L.canon h args w') hFZ
    ((SameWorld.mono hFZ hc1.world).trans hsw.symm) hc1.img
    (L.toLinkSys.regVal_canon_eq hL hh (argsAt_regLocs ha) w w') hc1.ra
    (L.toLinkSys.memRel_canon himgF hm' h args)
    (fun off v hmz j hj => by
      rw [L.mem_canon, mem_withImg, if_neg (fun hi => hsav off v hmz j hj (himgF _ hi))]
      exact LinkSys.stackArgs_bytes ha.2.2 ha'.2.2 hsp' off v hmz j hj)
  rw [heq, Option.some.injEq, Prod.mk.injEq] at hpr
  rw [heq', Option.some.injEq, Prod.mk.injEq] at hpr'
  obtain ⟨-, rfl⟩ := hpr
  obtain ⟨-, rfl⟩ := hpr'
  exact sameWorld_endsZ hFZ hc0.world hc1.world hsw hret.ret hret'.ret hret.mem hret'.mem
    hret.fields hret'.fields

/-- The argument facts of a program call admitted by the non-interference contracts. -/
theorem argsAt_prog (hL : L.Ok) {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hpf : L.P.func? h.name = some h) (hdecl : L.MayCall g h.name) {sig : Clif.Signature}
    {vals : List Clif.Val} {args : List CV} {w w' : Arm.ArmState} {cm : Clif.Mem} {cs : Clif.State}
    (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hkind : (∃ e ∈ g.externs.map (·.2), e.name = h.name ∧ e.sig = sig) ∨
      sig ∈ indSigs g ∧ vals.map (·.ty) = Clif.AbiParam.tys sig.params)
    (hA : (∃ e ∈ g.externs.map (·.2), e.name = h.name ∧ e.sig = sig) ∧ ArgsAt sig vals args w ∧
        ArgsAt sig vals args w' ∨
      sig ∈ indSigs g ∧ ArgsAt sig vals args w ∧ ArgsAt sig vals args w') :
    ArgsAt h.sig vals args w ∧ ArgsAt h.sig vals args w' := by
  have hce := clifEntry_initState (f := h) hpf hinit
  have hvl : vals.length = h.sig.params.length := by
    have := congrArg List.length hce.sig
    simpa using this
  rcases hA with ⟨⟨e', he', hen', hes⟩, h1, h2⟩ | ⟨hsig, h1, h2⟩
  · have := hL.declSig g hg e' he' h (by rw [hen']; exact hpf)
    rw [← hes, this] at h1 h2
    exact ⟨h1, h2⟩
  · have hnf : ¬ Clif.IndFree g := fun hif => by
      rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
    have hdeclS := hL.indSig g hg hnf
    have hmatch : LinkSys.IndTyMatch sig h := by
      rcases hkind with ⟨e', he', hen', hes⟩ | ⟨-, hty⟩
      · have := hL.declSig g hg e' he' h (by rw [hen']; exact hpf)
        rw [← hes, this]
        rfl
      · exact hce.sig.symm.trans hty
    obtain ⟨⟨bytes, hb, hb8⟩, -⟩ := hdeclS h hh hdecl (L.toLinkSys.indReach hpf hdecl hsig hmatch)
    have habi := (hL.subset g hg).indSigs sig hsig
    exact ⟨LinkSys.argsAt_of_tyMatch habi hmatch hb hb8 hvl h1,
      LinkSys.argsAt_of_tyMatch habi hmatch hb hb8 hvl h2⟩

/-- **Non-interference of the external semantics of an activation of `g`** with unwinding
(`xni`'s counterpart): the base externs' (`baseNI`), and `progXU_ni` for a function of `P`. -/
theorem xniU (hL : L.Ok) (hU : L.OkU) [L.CrunOkX] (hN : L.NeedNI) {M : Nat}
    (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) (c : BitVec 64) :
    XNI F L.syms (g.externs.map (·.2)) (indSigs g) c
      (CallLg (L.envOfX M g c).toEnv (g.externs.map (·.2)) (indSigs g)) (L.XU κ M g F) := by
  intro n sig vals cm args d uses Z w w' o x o' x' hlg hd hFZ hsw hm hm' hc1 hc2 hA hx hx'
  obtain ⟨hkind, G, rv, cm'', hG, hGo⟩ := hlg
  simp only [Clif.XEnv.toEnv, Option.map_eq_some_iff] at hG
  obtain ⟨Gx, hGx, rfl⟩ := hG
  have hGo' := Clif.toOutcome_returned hGo
  rcases L.envOfX_some hGx with ⟨hpf, hb⟩ | ⟨h, hpf, hdecl, G0, hGl, hG0⟩
  · have hb' : L.base.extern n = some fun vals mem => (Gx vals mem).toOutcome := by
      rw [← hU.envX]; simp [Clif.XEnv.toEnv, hb]
    have hbase := hL.baseNI hN g hg F c n sig vals cm args d uses Z w w' o x o' x'
      ⟨hpf, hkind, _, rv, cm'', hb', hGo⟩ hd hFZ hsw hm hm' hc1 hc2 hA
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.XU_base hpf] at hx hx'
      exact hbase hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
        rw [hu]; exact (L.toLinkSys.find_sym hL n).2 hpf
      rw [L.XU_none hs] at hx hx'
      exact hbase hx hx'
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    obtain ⟨hpl, he0⟩ := hG0 vals cm (by rw [hGo']; intro _ e; cases e)
    rw [hGo'] at he0
    obtain ⟨cs, hinit, hrun⟩ := L.linkEnvRX_run hpf hGl he0 (.inl ⟨_, _, rfl⟩)
    have hplw : L.NeedSlots → L.PlaceAt cm (spv w) := fun hS => hc1 ▸ hpl hS
    have hcallee : L.Callee g h := .inr (.inr ⟨hh, hdecl⟩)
    have hAA := L.argsAt_prog hL hg hh hpf hdecl hinit hkind hA
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.XU_prog hpf] at hx hx'
      exact L.progXU_ni hL hU hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hplw hinit
        hrun hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
        rw [hu]; exact (L.toLinkSys.find_sym hL h.name).1 h hpf
      rw [L.XU_ind hs] at hx hx'
      split at hx
      · rename_i hif
        rw [if_pos hif] at hx'
        exact L.progXU_ni hL hU hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hplw hinit
          hrun hx hx'
      · cases hx

/-- The TLSDESC flags of an activation's external semantics are the base's. -/
theorem xTlsU (hL : L.Ok) (hN : L.NeedNI) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} :
    XTls F (L.XU κ M g F) :=
  fun Z n w w' hFZ hsw => hL.baseTlsNI hN F Z n w w' hFZ hsw

/-- **Non-interference of the raising callees of an activation of `g`** (`XRNI` for `XRU`): the
base callees' (`OkUNI.baseRaiseNI`), and `progXR_ni` for a function of `P`. -/
theorem xrniU (hL : L.Ok) (hU : L.OkU) (hNI : L.OkUNI) [L.CrunOkX] (hN : L.NeedNI) {M : Nat}
    (ih : 0 < M → L.ThmU κ (M - 1)) {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) (c : BitVec 64) :
    XRNI F L.syms (g.externs.map (·.2)) (indSigs g) c
      (CallLgR (L.envOfX M g c) (g.externs.map (·.2)) (indSigs g)) (L.XU κ M g F)
      (L.XRU κ M g F) := by
  intro n sig vals cm args d uses Z w w' o x o' x' hlg hd hFZ hsw hm hm' hc1 hc2 hA hx hx'
  obtain ⟨hkind, Gx, e, m, hGx, hGo⟩ := hlg
  rcases L.envOfX_some hGx with ⟨hpf, hb⟩ | ⟨h, hpf, hdecl, G0, hGl, hG0⟩
  · have hbase := hNI.baseRaiseNI hN g hg F c n sig vals cm args d uses Z w w' o x o' x'
      ⟨hpf, hkind, Gx, e, m, hb, hGo⟩ hd hFZ hsw hm hm' hc1 hc2 hA
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.XRU_base hpf] at hx hx'
      exact hbase hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
        rw [hu]; exact (L.toLinkSys.find_sym hL n).2 hpf
      rw [L.XRU_none hs] at hx hx'
      exact hbase hx hx'
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    obtain ⟨hpl, he0⟩ := hG0 vals cm (by rw [hGo]; intro _ e; cases e)
    rw [hGo] at he0
    obtain ⟨cs, hinit, hrun⟩ := L.linkEnvRX_run hpf hGl he0 (.inr ⟨_, _, rfl⟩)
    have hplw : L.NeedSlots → L.PlaceAt cm (spv w) := fun hS => hc1 ▸ hpl hS
    have hcallee : L.Callee g h := .inr (.inr ⟨hh, hdecl⟩)
    have hAA := L.argsAt_prog hL hg hh hpf hdecl hinit hkind hA
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.XRU_prog hpf] at hx hx'
      exact L.progXR_ni hL hU hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hplw hinit
        hrun hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
        rw [hu]; exact (L.toLinkSys.find_sym hL h.name).1 h hpf
      rw [L.XRU_ind hs] at hx hx'
      split at hx
      · rename_i hif
        rw [if_pos hif] at hx'
        exact L.progXR_ni hL hU hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hplw hinit
          hrun hx hx'
      · cases hx

/-- **The induction step with unwinding** (`thm_of`'s counterpart, with non-interference): the
linking statement with unwinding at depth `M` from the one at depth `M - 1`. -/
theorem thm_ofUN (hL : L.Ok) (hU : L.OkU) (hNI : L.OkUNI) [L.CrunOkX] (hκ : L.Budget κ)
    {M : Nat} (ih : 0 < M → L.ThmU κ (M - 1)) : L.ThmU κ M := by
  intro g hg F vals cs w₀ fuel hWE
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInvX g (spv w₀) cs.toX :=
    ⟨⟨hI, by simp [Clif.XState.Aligned, Clif.State.toX]⟩, hWE.clif.callers, hWE.place⟩
  have hrunEq := fun n => L.runLoopX_envOfX hL hU (M := M) hg n cs.toX hJ
  obtain ⟨lsda, hsites⟩ := hU.sites g hg
  obtain ⟨rows, hrows⟩ := hU.rows g hg
  obtain ⟨hlsda, hcie, hfde⟩ := Art.tables_eq hsites hrows
  have pipe := fun (htr : TrapsExplicitX (L.envOfX M g (spv w₀)) L.P.bare cs) =>
    backend_correct_world_ni_pipelineU (hL.subset g hg) hc (hU.lowerU g hg)
      (X := L.XU κ M g F) (XR := L.XRU κ M g F) (syms := L.syms)
      (env := L.envOfX M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
      (L.xCallsOkU hL hU hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xCallsIndOkU hL hU hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xRaiseOkU hL hU hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
      (L.xRaiseIndOkU hL hU hκ ih hg hWE.img hWE.room hWE.dead hWE.align)
      (fun d uses w hx => L.XU_excl hU.baseExcl d uses w hx)
      (fun n b hn => hL.symOk n b hn) rfl (T := (L.A g).tables) hsites hlsda hrows hcie hfde
      (hU.pads g hg) (hU.last g hg) (hU.saved g hg) hWE.clif hWE.rel hWE.args htr fuel
  have hAE : ∀ G ra s w₀', L.MachEntry κ M g F G ra s w₀' →
      ActEntryU (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G
        (L.XU κ M g F) (L.hooksU M) (L.XRU κ M g F) (L.UU M) (L.A g).base ra s w₀' :=
    fun G ra s w₀' hME =>
      { abi := hME.abi, stack := hME.stack, gfree := hME.gfree, hF := hME.hF,
        calls := L.calleeOkU hL hU hκ ih hg hME,
        tries := fun _ => L.calleeTryOkU hL hU hκ ih hg hME,
        tls := fun ht =>
          L.tlsOk_hooksU (hL.baseTls g hg (hasTls_of_vcode_pipeline hc ht) F (κ M g)),
        body := hME.body,
        unw := L.calleeUnwOkU hL hU hκ ih hg hME }
  refine ⟨fun rvals cm' hrun => ?_, fun htrX c hrun G ra s hME => ?_, fun e cm' hrun => ?_⟩
  · have hrun' : Clif.runLoopX (L.envOfX M g (spv w₀)) L.P.bare fuel cs.toX = .returned rvals cm' :=
      (hrunEq fuel).trans hrun
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hni⟩ :=
      (pipe (Clif.trapsExplicitX_of_ended (.inl ⟨_, _, hrun'⟩))).1 rvals cm' hrun'
    exact ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs,
      fun G ra s hME => hall (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s w₀ hME),
      fun hN D w₀' hrel' hsw hreg hstk G ra s hME =>
        hni (L.xniU hL hU hN ih hg hWE.img (spv w₀)) (L.xTlsU hL hN)
          (L.xrniU hL hU hNI hN ih hg hWE.img (spv w₀)) D w₀' hrel' hsw hreg hstk (L.hooksU M)
          (L.UU M) G (L.A g).base ra s (hAE G ra s w₀' hME)⟩
  · exact (pipe (L.trapsExplicitX_envOfX hL hU hg hJ htrX)).2.1 c ((hrunEq fuel).trans hrun)
      (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s w₀ hME)
  · have hrun' : Clif.runLoopX (L.envOfX M g (spv w₀)) L.P.bare fuel cs.toX = .unwound e cm' :=
      (hrunEq fuel).trans hrun
    obtain ⟨obj, wf, hex, hmem, hall, hni⟩ :=
      (pipe (Clif.trapsExplicitX_of_ended (.inr ⟨_, _, hrun'⟩))).2.2 e cm' hrun'
    exact ⟨obj, wf, hex, hmem,
      fun G ra s hME => hall (L.hooksU M) (L.UU M) G (L.A g).base ra s (hAE G ra s w₀ hME),
      fun hN D w₀' hrel' hsw hreg hstk G ra s hME =>
        hni (L.xniU hL hU hN ih hg hWE.img (spv w₀)) (L.xTlsU hL hN)
          (L.xrniU hL hU hNI hN ih hg hWE.img (spv w₀)) D w₀' hrel' hsw hreg hstk (L.hooksU M)
          (L.UU M) G (L.A g).base ra s (hAE G ra s w₀' hME)⟩

/-- **The linking statement with unwinding at every depth**, with non-interference. -/
theorem thmUN (hL : L.Ok) (hU : L.OkU) (hNI : L.OkUNI) [L.CrunOkX] (hκ : L.Budget κ) :
    ∀ M, L.ThmU κ M
  | 0 => L.thm_ofUN hL hU hNI hκ fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thm_ofUN hL hU hNI hκ fun _ => thmUN hL hU hNI hκ M

end LinkSysU

end E2E
