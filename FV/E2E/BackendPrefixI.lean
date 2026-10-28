import FV.E2E.IselSimIPrefix
import FV.E2E.BackendWorldI
import FV.E2E.RegLevelPrefixC

/-!
# The counted pipeline up to call `N` (SEM1 #537, item (d), docs/plans/uninit.md §5.9)

The induction step of the slot-byte statement (`thmPRB_of`) needs, at the machine's call `N`, the
correspondence of every earlier call `j < N` of the activation: the machine's call-`j` state and
the VCode call it realises, with the VCode call's arguments and world. The contracts of the
machine's calls are given only for `j < N` (the induction hypothesis).

* `vstar_call_at`: a counted VCode run from counter `≤ j` to counter `> j` passes a call
  instruction at counter `j` whose call succeeds;
* `prep_prefixW`: `prepare` maps every run prefix of the VCode to one of the prepared VCode;
* `ActEntryPRN`: `ActEntryPR` with the contracts of the calls `n < N` only (and the hook's pc);
* **`backend_prefixPRI`** (`Compiled` path): for a CLIF calling state reached after `N` calls,
  every call `j < N` of the counted VCode run is realised by the machine's call-`j` state `u`
  (`OnCall … j`, at the body `sp`, `CallSiteAt` with the VCode's arguments and world), and
  `XI`'s call `j` answers it.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- The callee name of a call (`csem`'s first argument of `X.call`). -/
def callDest (info : CallInfo) : Option String :=
  match info.dest with | .sym n => some n | .reg _ => none

theorem callLike_of_isCallI {i : MInst} (h : i.isCallI = true) :
    ∃ info, i = .call info ∨ ∃ ti, i = .tryCall info ti := by
  cases i <;> simp_all [MInst.isCallI]

/-- **A successful call of `csem` is an answer of `X.call`.** -/
theorem csem_call_some {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem} {i : MInst}
    {info : CallInfo} (hi : i = .call info ∨ ∃ ti, i = .tryCall info ti) {uses : List CV}
    {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl} (h : csem F ctx X i uses w = some r) :
    ∃ r', X.call (callDest info) uses w = some r' := by
  rcases hi with rfl | ⟨ti, rfl⟩
  · simp only [csem, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', -⟩ := h
    exact ⟨r', hr'⟩
  · simp only [csem, Option.map_eq_some_iff, Option.filter_eq_some_iff] at h
    obtain ⟨r', ⟨hr', -⟩, -⟩ := h
    exact ⟨r', hr'⟩

/-- **A counted run past counter `j` passes a successful call at counter `j`.** -/
theorem vstar_call_at {V W : Type} {vc : VCode} {sem : Nat → ISem V W} {j : Nat}
    {v v' : VConf V (W × Nat)} (h : Star (VStep vc (ISem.counted sem)) v v') (h0 : vctr v ≤ j)
    (h1 : j < vctr v') :
    ∃ b k ρ w vb i ops r, Star (VStep vc (ISem.counted sem)) v (.run ⟨b, k, ρ, (w, j)⟩) ∧
      vc.blocks[b]? = some vb ∧ vb.insts[k]? = some i ∧ i.isCallI = true ∧ i.operands = .ok ops ∧
      sem j i ((ops.toList.filter Operand.isUse).map (ρ ·.vreg)) w = some r := by
  induction h with
  | refl => omega
  | @step v1 v2 v3 hs h23 ih =>
    by_cases hv2 : vctr v2 ≤ j
    · obtain ⟨b, k, ρ, w, vb, i, ops, r, hst, rest⟩ := ih hv2 h1
      exact ⟨b, k, ρ, w, vb, i, ops, r, .step hs hst, rest⟩
    · cases hs with
      | @step b k ρ w vb i ops outs w' ctl c' hvb hi hops hsem hlen hn =>
        have hc := vnext_ctr hn
        obtain ⟨hs1, hw⟩ := ISem.counted_some hsem
        obtain ⟨w1, m⟩ := w
        simp only [vctr] at h0
        cases hcall : i.isCallI
        · rw [hcall] at hw; simp only [Bool.false_eq_true, ite_false] at hw
          omega
        · rw [hcall] at hw; simp only [ite_true] at hw
          obtain rfl : m = j := by omega
          exact ⟨b, k, ρ, w1, vb, i, ops, _, .refl _, hvb, hi, hcall, hops, hs1⟩

/-- **`prepare` maps run prefixes**: every state the VCode reaches from the entry is reached, in a
renamed block, by the prepared VCode. -/
theorem prep_prefixW {W : Type} {vc vcp : VCode} {sem : ISem CV W} (hds : DriverSemG sem)
    (h : prepCheck vc vcp = true) {ρ₀ : Nat → CV} {w₀ : W} {b k : Nat} {ρ : Nat → CV} {w : W}
    (hs : Star (VStep vc sem) (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨b, k, ρ, w⟩)) :
    ∃ b', Star (VStep vcp sem) (.run ⟨0, 0, ρ₀, w₀⟩) (.run ⟨b', k, ρ, w⟩) := by
  unfold prepCheck at h
  split at h
  · rename_i ss ps ss' ps' hcfg hcfg'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h0, hl0⟩, hall⟩, -⟩ := h
    let L : Nat → Prop := fun b => b < vc.blocks.size ∧ liveOf ss b = true
    have hchk : ∀ b, L b → ∃ b', sigmaOf vc vcp b = some b' ∧ keptOk vc vcp ss ss' b b' = true ∧
        (ss[b]?.getD #[]).all (fun s => decide (s < vc.blocks.size) && liveOf ss s) = true := by
      intro b ⟨hlt, hlb⟩
      have := all_range hall hlt
      rw [hlb] at this
      simp only [Bool.not_true, Bool.false_or] at this
      split at this
      · cases this
      · rename_i b' hσ
        simp only [Bool.and_eq_true] at this
        exact ⟨b', hσ, this.1, this.2⟩
    have hk : ∀ b b', L b → sigmaOf vc vcp b = some b' → Kept vc vcp ss ss' b b' := by
      intro b b' hLb hσ
      obtain ⟨b'', hσ', hkept, -⟩ := hchk b hLb
      rw [hσ] at hσ'; cases hσ'
      exact keptOk_sound hkept
    have hL : ∀ (b : Nat) (sb : Array Nat) (j s : Nat), L b → ss[b]? = some sb → sb[j]? = some s → L s := by
      intro b sb j s hLb hsb hs
      obtain ⟨-, -, -, hall'⟩ := hchk b hLb
      rw [hsb, Option.getD_some] at hall'
      have := (Array.all_eq_true_iff_forall_mem.mp hall') s (Array.mem_of_getElem? hs)
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
    have hL0 : L 0 := by
      refine ⟨?_, hl0⟩
      unfold sigmaOf at h0
      split at h0
      · rename_i vb hvb; exact (Array.getElem?_eq_some_iff.mp hvb).1
      · cases h0
    obtain ⟨b', -, -, hstar'⟩ := prep_starW hds hcfg hcfg' hL hk hs ⟨0, 0, ρ₀, w₀⟩
      ⟨b, k, ρ, w⟩ 0 rfl rfl hL0 h0
    exact ⟨b', hstar'⟩
  · cases h

/-- **`ActEntryPR` up to call `N`**: the callee contracts of the calls `n < N` only; the hook's
pc behaviour (which the contracts carry) separately. -/
structure ActEntryPRN (vcp : VCode) (rf : RFunc) (af : AFunc) (fa : FnAsm) (fb : FnBin) (K : Nat)
    (F G : BitVec 64 → Prop) (XI : ExtSemI) (H : ArmHooks) (base ra : BitVec 64)
    (Kp : Nat) (c : BitVec 64) (P : Nat → BitVec 64 → BitVec 8) (R : Nat → Arm.ArmState)
    (s w₀ : Arm.ArmState) (N : Nat) : Prop where
  abi : AbiCall fb base ra s
  stack : StackAvail K af s
  gfree : ∀ a, G a → ¬ StackBelow (frameDrop af + K) (spv s) a
  hF : frameWG K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af G s = F
  proph : ProphOk Kp c (ArmStepX (XI.at 0) H fa) fa base s P
  regp : ProphRegOkM c (ArmStepX (XI.at 0) H fa) fa base s R
  calls : ∀ n < N, CalleeOkGP (fun u => OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
    F K G s (CallAt fa base) (XI.at n) H vcp.CallSite (GotV vcp)
  tries : vcp.hasTryCall = true → ∀ n < N, CalleeTryOkGP (fun u =>
      OnCallPR Kp c P R (ArmStepX (XI.at 0) H fa) fa base s n u ∧
        spOf u = spv s - BitVec.ofNat 64 (frameDrop af))
    F K G s (CallAt fa base) (XI.at n) H vcp.TrySite (GotV vcp)
  pc : ∀ d s, Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (H.call d s) = Arm.r .PC s + 4
  tls : vcp.hasTls = true → ∀ n, TlsOk F K (XI.at n) H
  body : BodyEntryW F vcp.EntryArg af s w₀

/-- `ActEntryPR` gives `ActEntryPRN` at every `N` (its contracts carry the hook's pc). -/
theorem ActEntryPR.toN {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin} {K : Nat}
    {F G : BitVec 64 → Prop} {XI : ExtSemI} {H : ArmHooks} {base ra : BitVec 64} {Kp : Nat}
    {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState} {s w₀ : Arm.ArmState}
    (h : ActEntryPR vcp rf af fa fb K F G XI H base ra Kp c P R s w₀) (N : Nat) :
    ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp c P R s w₀ N :=
  ⟨h.abi, h.stack, h.gfree, h.hF, h.proph, h.regp, fun n _ => h.calls n, fun ht n _ => h.tries ht n,
    (h.calls 0).pc, h.tls, h.body⟩

/-- **The counted pipeline up to call `N`** (`Compiled` path, `backend_correct_worldPRI`'s
premises; the machine contracts of the calls `j < N` only): for a CLIF state reached from the
entry after `N` calls that makes a call, every call `j < N` of the counted VCode run is realised
by the machine's call-`j` state `u` (at the body `sp`, with the VCode call's arguments `uses` and
world `w`: `CallSiteAt`), and `XI`'s call `j` answers `uses` in `w`. -/
theorem backend_prefixPRI {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) {N : Nat} {H : ArmHooks} {G : BitVec 64 → Prop}
    {base ra : BitVec 64} {Kp : Nat} {cc : BitVec 64} {P : Nat → BitVec 64 → BitVec 8}
    {R : Nat → Arm.ArmState} {s : Arm.ArmState}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P R s w₀ N)
    {t : Clif.State} (hr : ReachN env p cs t N) (hcn : callNum t = 1) :
    ∀ j < N, ∃ u i info uses w r, OnCall (ArmStepX (XI.at 0) H fa) fa base s j u ∧
      spOf u = spv s - BitVec.ofNat 64 (frameDrop af) ∧ CallSiteAt F K G s fa base i uses w u ∧
      (i = .call info ∨ ∃ ti, i = .tryCall info ti) ∧ (XI.at j).call (callDest info) uses w = some r := by
  intro j hj
  obtain ⟨b, k, ρ, w, hstar, -⟩ :=
    iselSim_prefixWI hsub hc hone htc hX hsym hslot (fun _ => 0) hcs hrel hargs htr t N hr hcn
  obtain ⟨b', hstar'⟩ := prep_prefixW (DriverSemG.csemI fun m =>
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at m)).toDriverSemG) hc.prepOk hstar
  obtain ⟨hstar'', -⟩ := gotInvI_star
    (show GotInvI vcp XI ⟨0, 0, fun _ => 0, (w₀, 0)⟩ from gotInv_entry vcp (XI.at 0) _ w₀) hstar'
  obtain ⟨b1, k1, ρ1, w1, vb, i, ops, r, hs1, hvb, hi, hcall, hops, hsem⟩ :=
    vstar_call_at (j := j) hstar'' (Nat.zero_le _) hj
  have hM := regLevel_prefixPRS hc.check hc.alloc hc.emit hc.layout (XI := XI) (H := H)
    (K := K) (G := G) (gv := GotV vcp) (N := j) hcov he.abi he.stack he.gfree he.proph he.regp
    (fun n hn => by rw [he.hF]; exact he.calls n (by omega))
    (fun ht n hn => by rw [he.hF]; exact he.tries ht n (by omega)) he.pc
    (by rw [he.hF]; exact he.tls) (by rw [he.hF]; exact he.body) (fun _ => 0)
  rw [he.hF] at hM
  obtain ⟨info, hci⟩ := callLike_of_isCallI hcall
  obtain ⟨u, hon, hsp, hsite⟩ := hM b1 k1 ρ1 w1 vb i hs1 hvb hi ⟨info, hci⟩ ops hops
  obtain ⟨r', hr'⟩ := csem_call_some hci (csemV_sub hsem)
  exact ⟨u, i, info, _, w1, r', hon, hsp, hsite, hci, hr'⟩

end E2E
