import FV.Front.RawExeUnwindSrc
import FV.E2E.SrcBoundedX
import FV.E2E.SrcBoundedLegal
import FV.E2E.LinkArmUAct
import FV.E2E.Legal
import FV.Link.DeadCleanupExeSourceNB

/-!
# The exceptional edges on cg_clif's program without the memory-bound premise (A2/B1, S10f)

`bundle_correct_raw_unwind_src` takes the run premise
`∀ u, ReachesX E (rawLink us sc) cs.toX u → MemBounded u.s.mem` (`Clif.runLoopX`'s allocations
need not lie below `2^64`). `bundle_correct_raw_unwind_src_nobnd` has the same premises without
it, and the same conclusion:

* a program mentioning `i128`: for a source run that ends within `N` steps (a return, a trap or
  an exception leaving `f`), the machine premise `StackAvail (κ M g)` of `MachAt` at some
  `M ≥ N` bounds it (`E2E.SrcBoundedX`): the run's call depth stays below `N`
  (`reachesX_depth`), so the budget `κ (M - k)` of an activation at depth `k` covers its callees
  (`Budget`). With program callees having stack slots (`NeedSlots`) the oracle places every
  activation's slots in its compiled frame below the body's stack pointer `spv w₀` (`hpl`), so
  they never wrap (`srcBoundedX_placed`); without, no entered function has slots
  (`srcBoundedX_slotless`). The externs keep valid ranges below `2^64` (`EnvKeepsBounded`,
  `EnvKeepsAllocsX`, the `i128` premises) and the oracle (`envX_keepsPlace`). When no such `M`
  exists, `MachAt` at every `M ≥ N` holds vacuously (the return's split results exist:
  `expRel_exists`);
* a program without `i128`: the legalisation is the identity, so the source run under the linked
  names is the compiled program's run from the same state.

`raw_legal_unwind` (the CLIF half) has no premise bounding its entry memory or its stack, so it
keeps its memory-bound premise.
-/

namespace Front
set_option autoImplicit false

open Clif E2E E2E.LinkCheck E2E.DeadCleanupBinary Link Opt.Legalize128 Backend Backend.Proof
  Backend.Proof.Driver E2E.LegalProgram Opt.Legal Opt.Legal.X

/-! ## Runs with unwinding, renamed forward -/

theorem stepX_ren_fwd {σ : Ren} {E : XEnv} {p : Program} {xs xs' : XState}
    (h : stepX E p xs = .next xs') :
    stepX (E.ren σ) (p.rename σ.fwd) (xs.ren σ) = .next (xs'.ren σ) := by
  have := stepX_ren σ E p xs
  rw [h] at this
  cases hs : stepX (E.ren σ) (p.rename σ.fwd) (xs.ren σ) <;> rw [hs] at this <;>
    simp [XStepResult.ren, XStepResult.erase] at this
  rw [this]

theorem reachesX_ren_fwd {σ : Ren} {E : XEnv} {p : Program} {xs u : XState}
    (h : ReachesX E p xs u) : ReachesX (E.ren σ) (p.rename σ.fwd) (xs.ren σ) (u.ren σ) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact .next (stepX_ren_fwd hs) ih

/-! ## The ABI split of return values exists -/

theorem i128_halves_split (r : BitVec 128) : r = r.extractLsb' 64 64 ++ r.extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [append_toNat]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  have := r.isLt
  omega

theorem halves_exists (v : Val) (hv : v.ty = .i128) : ∃ a b, Halves v a b := by
  obtain ⟨ty, bits⟩ := v
  simp only at hv
  subst hv
  exact ⟨_, _, bits.extractLsb' 0 64, bits.extractLsb' 64 64,
    congrArg (Val.mk .i128) (i128_halves_split bits), rfl, rfl⟩

/-- Values of the types of parameters with ABI groups `gs` have a split by `gs`. -/
theorem expRel_exists : ∀ {ps : List AbiParam} {gs : List (List SlotEl)} {vs : List Val},
    GroupsOf ps gs → vs.map (·.ty) = ps.map (·.ty) → ∃ vs', ExpRel gs vs vs'
  | [], [], [], _, _ => ⟨[], trivial⟩
  | p :: ps, g :: gs, v :: vs, hg, ht => by
    simp only [List.map_cons, List.cons.injEq] at ht
    rcases groupsOf_cons.1 hg with ⟨hg1, hg2⟩ | ⟨hpt, hx⟩
    · obtain ⟨vs', hvs'⟩ := expRel_exists hg2 ht.2
      rcases hg1 with ⟨rfl, -⟩ | ⟨hpt, rfl | rfl⟩
      · exact ⟨v :: vs', rfl, hvs'⟩
      · obtain ⟨a, b, hab⟩ := halves_exists v (ht.1.trans hpt)
        exact ⟨a :: b :: vs', hab, hvs'⟩
      · obtain ⟨a, b, hab⟩ := halves_exists v (ht.1.trans hpt)
        exact ⟨⟨.i64, 0⟩ :: a :: b :: vs', rfl, hab, hvs'⟩
    · rcases ps with _ | ⟨q, qs⟩ <;> rcases gs with _ | ⟨g2, gs2⟩
      · cases hx
      · cases hx
      · cases hx
      rcases g2 with _ | ⟨e, es⟩
      rotate_left
      · cases hx
      obtain ⟨rfl, -, hg2⟩ := hx
      rcases vs with _ | ⟨u, vs2⟩
      · simp at ht
      simp only [List.map_cons, List.cons.injEq] at ht
      obtain ⟨vs', hvs'⟩ := expRel_exists hg2 ht.2.2
      obtain ⟨a, b, hab⟩ := halves_exists v (ht.1.trans hpt)
      exact ⟨u :: a :: b :: vs', hab, rfl, hvs'⟩
  | [], _ :: _, _, hg, _ => by cases hg
  | _ :: _, [], _, hg, _ => by cases hg
  | [], [], _ :: _, _, ht => by cases ht
  | _ :: _, _ :: _, [], _, ht => by cases ht

theorem groups_returns_of_sigExp {s s' : Signature} (h : sigExp s = some s') :
    ∃ gs, groups s.returns = some gs := by
  unfold groups
  cases hr : expandGroups s.returns with
  | ok gs => exact ⟨gs, rfl⟩
  | error e =>
    unfold sigExp expandSig at h
    cases hp : expandGroups s.params <;>
      simp [hp, hr, bind, Except.bind, Except.toOption] at h

/-! ## The theorem -/

/-- `bundle_correct_raw_unwind_src` without the premise that the source run's memories lie below
`2^64` (A2/B1). **The shipped executable compiler with the unwind tables checked refines cg_clif's
program's runs with unwinding, `i128` included**: the same premises otherwise, the same
conclusion. -/
theorem bundle_correct_raw_unwind_src_nobnd {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (E : XEnv) (B : BaseEnv) (F : BitVec 64 → Prop)
    (hB : BaseOk (LinkSys.ofInputCleanup S.inputCleanup B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup S.inputCleanup B F).Img a → F a)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.inputCleanup B F)
    (hEX : L.envX = E.ren σ)
    (hbU : Link.DeadCleanup.BaseU L) (hNI : L.OkUNI) {κ : Nat → Clif.Function → Nat}
    (hκ : L.Budget κ)
    (hlegal : (∃ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true) →
      HelperOk L.envX.toEnv ∧ ExtLegal L.envX.toEnv ∧ EnvKeepsBounded L.envX.toEnv ∧
        ExtLegalX L.envX ∧ EnvKeepsAllocsX L.envX ∧ ExnArityOk L.envX)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, L.envX.sigOf n = none)
    (hexn : ∀ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true → ∀ g' cert,
      function128Cert g = .ok (g', cert) → exnOk g g' cert = true)
    {ra : BitVec 64} {s w₀ : Arm.ArmState} {args args' : List Val} {cs cs' : State}
    (hent : AbiEntry (L.A (legalize (f.rename σ.fwd))).fb (L.A (legalize (f.rename σ.fwd))).base
      ra s)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A (legalize (f.rename σ.fwd))).af s w₀)
    (hargs : ArgsIn (legalize (f.rename σ.fwd)).sig args' s)
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry (legalize (f.rename σ.fwd)) args' cs')
    (hexp : ExpRel ((groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hsav : StackArgsAvoid L.Img (legalize (f.rename σ.fwd)).sig args' s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A (legalize (f.rename σ.fwd))).af.slotBase,
      (RAFrame.compute (L.A (legalize (f.rename σ.fwd))).vcp
        (L.A (legalize (f.rename σ.fwd))).rf).intBase⟩
      (legalize (f.rename σ.fwd)) cs'.frame.slots cs'.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs'.mem (spv w₀)) :
    (∀ g' ∈ L.P.funcs, ∀ pc, (L.A g').base.toNat ≤ pc →
        pc < (L.A g').base.toNat + (L.A g').fb.size →
        EhCheck.unwTables file pc = some ((L.A g').base.toNat, (L.A g').tables)) ∧
    (∀ N rv m2, runLoopX E (rawLink us sc) N cs.toX = .returned rv m2 →
      ∃ rv', ExpRel ((groups f.sig.returns).getD []) rv rv' ∧
        ∃ K, ∀ M, K ≤ M →
          MachAt L κ (legalize (f.rename σ.fwd)) ra s cs' M (.returned rv' (m2.ren σ))) ∧
    (∀ N c, (∀ u, ReachesX E (rawLink us sc) cs.toX u → MemTrapFree E.toEnv (rawLink us sc) u.s) →
      runLoopX E (rawLink us sc) N cs.toX = .trapped c →
      ∃ K, ∀ M, K ≤ M → MachAt L κ (legalize (f.rename σ.fwd)) ra s cs' M (.trapped c)) ∧
    (∀ N e m2, runLoopX E (rawLink us sc) N cs.toX = .unwound e m2 →
      ∃ K, ∀ M, K ≤ M →
        MachAt L κ (legalize (f.rename σ.fwd)) ra s cs' M (.unwound e (m2.ren σ))) := by
  obtain ⟨hL, hU, ht⟩ := Link.DeadCleanup.compileExeU_facts h hB hF hLs hbU
  -- the programs
  have hsrcP : S.inputCleanup.srcProg = (rawLink us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hPL : L.P = prog S.inputCleanup := by rw [hLs]; rfl
  have hpe := Link.DeadCleanup.prog_eq_legal S
  have hpe' : S.inputCleanup.prog = prog S.inputCleanup := (Link.DeadCleanup.prog_eq S).symm
  have hLP : L.P = legalProg S.inputCleanup.srcProg := hPL.trans hpe
  -- the source domain with unwinding
  have hbase : L.base = L.envX.toEnv := hU.envX.symm
  have hctx : ProgCtx S.inputCleanup.srcProg L.envX.toEnv L.syms :=
    srcCtx hsrc (by rw [hpe', ← hPL]; exact hL.names) (by rw [hpe', ← hPL]; exact hL.free)
      (by rw [hpe', ← hPL]; exact hL.declSig)
      (by rw [hpe', ← hPL, ← hbase]; exact hL.indScope)
      (fun h' => ⟨(hlegal h').1, (hlegal h').2.1, (hlegal h').2.2.1⟩)
      (by rw [hpe']; exact hsig)
  have hC : ProgCtxX S.inputCleanup.srcProg L.envX L.syms :=
    { ctx := hctx
      baseX := fun h' => (hlegal h').2.2.2
      indX := fun ⟨g0, hg0, hnf⟩ => by
        rw [← hLP]
        exact hbU.indScopeX g0 (by rw [hLP]; exact hg0) hnf
      exn := hexn }
  -- the CLIF half, given the bound
  have hC' := hC
  rw [hsrcP, hEX] at hC'
  have hraw := fun hbnd : (∀ u, ReachesX E (rawLink us sc) cs.toX u → MemBounded u.s.mem) =>
    raw_legal_unwind hC' hf hcs hcs' hexp hsl hmem (fun _ => hrel.1.symbols) hbnd
  rw [← hEX, ← hsrcP, ← hLP] at hraw
  -- the compiled function
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hsrcP, Clif.Program.rename_func?, hf]; rfl
  have hfP := (Clif.Program.func?_some hf').1
  have hgP : legalize (f.rename σ.fwd) ∈ L.P.funcs := by
    rw [hLP]; exact List.mem_map_of_mem hfP
  -- from the legalised run to the machine
  have hmach : ∀ o, (∃ k, runLoopX L.envX L.P k cs'.toX = o) → o ≠ .outOfFuel →
      ∃ K, ∀ M, K ≤ M → MachAt L κ (legalize (f.rename σ.fwd)) ra s cs' M o := by
    rintro o ⟨k, hk⟩ hof
    refine ⟨k, fun M hM hres hFw hgfree htr => ?_⟩
    have hr := (Link.DeadCleanup.compileExe_correct_unwind h B F hB hF L hLs hbU hNI hκ hgP M
      hent hres hFw hgfree himg hbe hargs hcs' hsav hrel hpl htr).2
    have hfuel : runLoopX L.envX L.P (M + 1) cs'.toX = o := by
      have := runLoopX_add L.envX L.P k _ (by rw [hk]; exact hof) (M + 1 - k)
      rw [Nat.add_sub_cancel' (by omega)] at this
      rw [this, hk]
    rw [hfuel] at hr
    exact hr
  -- the source entry under the linked names
  have hcsR := clifEntry_ren (σ := σ) hcs
  have hLe : LInv S.inputCleanup.srcProg (cs.ren σ) := by
    obtain ⟨b, hb, h2, h3, -, -⟩ := hcsR.entry
    refine ⟨⟨by rw [hcsR.func]; exact hfP, .inl ⟨b, by rw [hcsR.func]; exact entry_mem hb, ?_, ?_⟩⟩,
      fun c hc => by rw [hcsR.callers] at hc; cases hc⟩
    · rw [h2]; exact List.suffix_refl _
    · rw [h3]
  have hXI : XInv S.inputCleanup.srcProg (cs.ren σ).toX :=
    ⟨hLe, by simp [XState.Aligned, State.toX, State.ren, hcs.callers]⟩
  have hXE : (cs.ren σ).toX = cs.toX.ren σ := State.toX_ren σ cs
  have hc0 : (cs.ren σ).toX.s.callers.length = 0 := by simp [State.toX, State.ren, hcs.callers]
  -- the source runs under the linked names
  have hrenR : ∀ N rv m2, runLoopX E (rawLink us sc) N cs.toX = .returned rv m2 →
      runLoopX L.envX S.inputCleanup.srcProg N (cs.ren σ).toX = .returned rv (m2.ren σ) := by
    intro N rv m2 hr
    rw [hEX, hsrcP, hXE]; exact runLoopX_ren_returned σ E _ N cs.toX hr
  have hrenT : ∀ N c, runLoopX E (rawLink us sc) N cs.toX = .trapped c →
      runLoopX L.envX S.inputCleanup.srcProg N (cs.ren σ).toX = .trapped c := by
    intro N c hr
    rw [hEX, hsrcP, hXE]; exact runLoopX_ren_trapped σ E _ N cs.toX hr
  have hrenU : ∀ N e m2, runLoopX E (rawLink us sc) N cs.toX = .unwound e m2 →
      runLoopX L.envX S.inputCleanup.srcProg N (cs.ren σ).toX = .unwound e (m2.ren σ) := by
    intro N e m2 hr
    rw [hEX, hsrcP, hXE]; exact runLoopX_ren_unwound σ E _ N cs.toX hr
  -- the bound under the linked names gives cg_clif's run's
  have hback : (∀ u, ReachesX L.envX S.inputCleanup.srcProg (cs.ren σ).toX u →
      MemBounded u.s.mem) → ∀ u, ReachesX E (rawLink us sc) cs.toX u → MemBounded u.s.mem := by
    intro hbd u hu
    have h1 := reachesX_ren_fwd (σ := σ) hu
    rw [← hXE, ← hEX, ← hsrcP] at h1
    have h2 := hbd _ h1
    exact fun a k hv => h2 a k (by simpa [XState.ren_s, State.ren, Mem.ren, Mem.valid] using hv)
  -- the return types
  have hty : ∀ N rv m, runLoopX L.envX S.inputCleanup.srcProg N (cs.ren σ).toX = .returned rv m →
      rv.map (·.ty) = f.sig.returns.map (·.ty) := by
    intro N rv m hr
    have := runLoopX_returned_tys hctx.free N _ rv m hXI hr
    simpa [State.bottom, State.toX, State.ren, Frame.ren, hcs.callers, hcs.func,
      Clif.Function.rename_sig, AbiParam.tys] using this
  have hexists : ∀ rv : List Val, rv.map (·.ty) = f.sig.returns.map (·.ty) →
      ∃ rv', ExpRel ((groups f.sig.returns).getD []) rv rv' := by
    have hsx := (legalFacts (hctx.ok _ hfP)).sig
    rw [Clif.Function.rename_sig] at hsx
    obtain ⟨gs, hgs⟩ := groups_returns_of_sigExp hsx
    intro rv hrv
    rw [hgs, Option.getD_some]
    exact expRel_exists (groups_spec hgs) hrv
  -- the bound from the stack of `MachAt` at `M0 ≥ N` (`i128`)
  have hBound : (∃ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true) → ∀ N,
      runLoopX L.envX S.inputCleanup.srcProg N (cs.ren σ).toX ≠ .outOfFuel → ∀ M0, N ≤ M0 →
      StackAvail (κ M0 (legalize (f.rename σ.fwd))) (L.A (legalize (f.rename σ.fwd))).af s →
      ∀ u, ReachesX L.envX S.inputCleanup.srcProg (cs.ren σ).toX u → MemBounded u.s.mem := by
    intro hm N hN M0 hNM hSA
    obtain ⟨-, -, hkb, -, hka, -⟩ := hlegal hm
    have hM : MemBounded (cs.ren σ).toX.s.mem := by
      show MemBounded (cs.mem.ren σ)
      rw [← hmem]; exact memBounded_of_holds hrel
    have hms : ∀ (t : XState) (g : Clif.Function),
        ReachesX L.envX S.inputCleanup.srcProg (cs.ren σ).toX t →
        g ∈ S.inputCleanup.srcProg.funcs → (∃ sig, IndSite g sig) → t.s.mem.symbols = L.syms := by
      intro t g ht hg ⟨sig, hs⟩
      have hI : SomeInd (legalProg S.inputCleanup.srcProg) :=
        ⟨legalize g, by simp only [legalProg_funcs]; exact List.mem_map_of_mem hg,
          (legalFacts (hctx.ok g hg)).ind (SrcBounded.not_indFree_of_site hs)⟩
      have hS := (hC.indSrcX hI).scope
      rw [ht.symbols hC.ctx.free hS.keep hS.keepU hXI]
      show (cs.mem.ren σ).symbols = L.syms
      rw [← hmem]; exact hrel.1.symbols
    have hcallee : ∀ (t xs1 : XState), ReachesX L.envX S.inputCleanup.srcProg (cs.ren σ).toX t →
        XInv S.inputCleanup.srcProg t →
        SrcBounded.EnterVia S.inputCleanup.srcProg t.s.frame.func xs1.s.frame.func t.s.mem →
        L.Callee (legalize t.s.frame.func) (legalize xs1.s.frame.func) :=
      fun t xs1 ht hIt hv => SrcBounded.callee_of_enter (L := L.toLinkSys) hctx hLP rfl hIt.1.1.1 hv
        (hms t _ ht hIt.1.1.1)
    have hlegP : ∀ g ∈ S.inputCleanup.srcProg.funcs, legalize g ∈ L.P.funcs := fun g hg => by
      rw [hLP]; exact List.mem_map_of_mem hg
    by_cases hns : L.NeedSlots
    · obtain ⟨sps, hpl0⟩ := hpl hns
      have hkP := L.envX_keepsPlace hL hU hns
      have hL' : (LinkSys.ofInputCleanup S.inputCleanup B F).Ok := by rw [← hLs]; exact hL
      have hA : ∀ x, L.A x = art S.inputCleanup x := fun x => by
        rw [show L.A = L.toLinkSys.A from rfl, hLs]; rfl
      refine SrcBoundedX.srcBoundedX_placed hctx.free hkP.toEnv
        (fun n g hg vals m e m' hu => (hkP n g hg vals m).2 e m' hu) hkb hka.bounded
        (fun k h => κ (M0 - k) (legalize h)) (fun _ => True) L.frames hXI hM
        (by simp [State.toX, State.ren, hcs.callers]) (c := spv w₀) (sps := sps) ?_ ?_ trivial ?_
      · show (cs.mem.ren σ).place = _
        rw [← hmem]; exact hpl0
      · show κ (M0 - 0) (legalize (cs.ren σ).frame.func) ≤ (spv w₀).toNat
        rw [hcsR.func, Nat.sub_zero, hbe.sp]
        have h1 := hSA.1.1
        have h2 : frameDrop (L.A (legalize (f.rename σ.fwd))).af ≤
            (L.A (legalize (f.rename σ.fwd))).af.frameSize + 16 := by
          unfold frameDrop; split <;> omega
        rw [SrcBounded.toNat_sub_of_le (by omega)]
        omega
      · intro t xs1 hr hIt _ hs hlen hv
        have hcl := hcallee t xs1 hr hIt hv
        have hh := Link.DeadCleanup.enterVia_mem hv
        have hlh := hlegP _ hh
        have hlg := hlegP _ hIt.1.1.1
        have hFh := legalFacts (hctx.ok _ hh)
        have hpf : L.P.func? xs1.s.frame.func.name = some (legalize xs1.s.frame.func) := by
          rw [hLP]; exact hctx.func?_some (func?_of_mem hctx.nd hh)
        have hd := SrcBoundedX.reachesX_depth hctx.free (hr.snoc hs) hXI N hN
        rw [hlen, hc0] at hd
        have hbud := L.budget_step hκ (M := M0 - t.s.callers.length) (by omega) hlg hcl
        refine ⟨frameDrop (L.A (legalize xs1.s.frame.func)).af,
          fun id => (L.A (legalize xs1.s.frame.func)).af.slotBase +
            ((slotLayout (legalize xs1.s.frame.func).slots).1.lookup id).getD 0, ?_,
          fun p hp => ?_, ?_, trivial⟩
        · simp only [LinkSys.frames]
          rw [hpf]
          rfl
        · obtain ⟨off, hlk, hle⟩ := hL.slotFits _ hlg _ hcl p (by rw [hFh.slots]; exact hp)
          have hfr := (frame_facts hL' (f := legalize xs1.s.frame.func)
            (by rw [← hPL]; exact hlh)).1
          rw [hA] at hle ⊢
          show (art S.inputCleanup (legalize xs1.s.frame.func)).af.slotBase +
              ((slotLayout (legalize xs1.s.frame.func).slots).1.lookup p.1).getD 0 + p.2.size ≤
            frameDrop (art S.inputCleanup (legalize xs1.s.frame.func)).af
          rw [hlk, Option.getD_some, hfr]
          omega
        · show frameDrop _ + κ (M0 - (t.s.callers.length + 1)) _ ≤
            κ (M0 - t.s.callers.length) _
          have e : M0 - t.s.callers.length - 1 = M0 - (t.s.callers.length + 1) := by omega
          rw [← e]
          exact hbud
    · refine SrcBoundedX.srcBoundedX_slotless hctx.free hkb hka.bounded hXI hM
        fun t xs1 hr hIt _ _ hv => ?_
      have hcl := hcallee t xs1 hr hIt hv
      have hnil : (legalize xs1.s.frame.func).slots = [] :=
        Classical.byContradiction fun hne => hns ⟨_, hlegP _ hIt.1.1.1, _, hcl, hne⟩
      rwa [(legalFacts (hctx.ok _ (Link.DeadCleanup.enterVia_mem hv))).slots] at hnil
  -- without `i128`: the compiled program and entry are the source's under the linked names
  have hid : ¬ (∃ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true) →
      L.P = S.inputCleanup.srcProg ∧ cs' = cs.ren σ ∧ sig128 f.sig = false := by
    intro hm
    obtain ⟨hpP, hall⟩ := Link.DeadCleanup.prog_eq_src hm
    obtain ⟨hmf, hfl⟩ := hall _ hfP
    have hs := (not_mentions hmf).1
    rw [Clif.Function.rename_sig] at hs
    obtain ⟨gs, hgs, hG⟩ := groups_plain (sig128_params hs)
    have hexp' := hexp
    rw [hgs, Option.getD_some] at hexp'
    have hvv : args' = args := expRel_val hG (sig128_params hs) hexp'
    have hcs'' : ClifEntry (f.rename σ.fwd) args cs' := by rw [← hfl, ← hvv]; exact hcs'
    exact ⟨hPL.trans hpP, Link.DeadCleanup.ident_state hcsR hcs'' hsl hmem, hs⟩
  refine ⟨ht, fun N rv m2 hrun => ?_, fun N c hnmt hrun => ?_, fun N e m2 hrun => ?_⟩
  · have hrr := hrenR N rv m2 hrun
    by_cases hm : ∃ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true
    · by_cases hS : ∃ M0, N ≤ M0 ∧
          StackAvail (κ M0 (legalize (f.rename σ.fwd))) (L.A (legalize (f.rename σ.fwd))).af s
      · obtain ⟨M0, hNM, hSA⟩ := hS
        have hbd := hback (hBound hm N (by rw [hrr]; intro h; cases h) M0 hNM hSA)
        obtain ⟨rv', hrel', k, hk⟩ := (hraw hbd).1 N rv m2 hrun
        exact ⟨rv', hrel', hmach _ ⟨k, hk⟩ (fun h => by cases h)⟩
      · obtain ⟨rv', hrel'⟩ := hexists rv (hty N rv _ hrr)
        exact ⟨rv', hrel', N, fun M hM => by intro hSA; exact absurd ⟨M, hM, hSA⟩ hS⟩
    · obtain ⟨hLPs, hcseq, hs⟩ := hid hm
      obtain ⟨rg, hrg, hR⟩ := groups_plain (sig128_returns hs)
      refine ⟨rv, ?_, hmach _ ⟨N, ?_⟩ (fun h => by cases h)⟩
      · rw [hrg, Option.getD_some]
        refine expRel_refl_plain hR (sig128_returns hs) ?_
        have := congrArg List.length (hty N rv _ hrr)
        simpa using this
      · rw [hLPs, hcseq]; exact hrr
  · have hrr := hrenT N c hrun
    by_cases hm : ∃ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true
    · by_cases hS : ∃ M0, N ≤ M0 ∧
          StackAvail (κ M0 (legalize (f.rename σ.fwd))) (L.A (legalize (f.rename σ.fwd))).af s
      · obtain ⟨M0, hNM, hSA⟩ := hS
        have hbd := hback (hBound hm N (by rw [hrr]; intro h; cases h) M0 hNM hSA)
        obtain ⟨k, hk⟩ := (hraw hbd).2.1 N c hnmt hrun
        exact hmach _ ⟨k, hk⟩ (fun h => by cases h)
      · exact ⟨N, fun M hM => by intro hSA; exact absurd ⟨M, hM, hSA⟩ hS⟩
    · obtain ⟨hLPs, hcseq, -⟩ := hid hm
      exact hmach _ ⟨N, by rw [hLPs, hcseq]; exact hrr⟩ (fun h => by cases h)
  · have hrr := hrenU N e m2 hrun
    by_cases hm : ∃ g ∈ S.inputCleanup.srcProg.funcs, mentions128 g = true
    · by_cases hS : ∃ M0, N ≤ M0 ∧
          StackAvail (κ M0 (legalize (f.rename σ.fwd))) (L.A (legalize (f.rename σ.fwd))).af s
      · obtain ⟨M0, hNM, hSA⟩ := hS
        have hbd := hback (hBound hm N (by rw [hrr]; intro h; cases h) M0 hNM hSA)
        obtain ⟨k, hk⟩ := (hraw hbd).2.2 N e m2 hrun
        exact hmach _ ⟨k, hk⟩ (fun h => by cases h)
      · exact ⟨N, fun M hM => by intro hSA; exact absurd ⟨M, hM, hSA⟩ hS⟩
    · obtain ⟨hLPs, hcseq, -⟩ := hid hm
      exact hmach _ ⟨N, by rw [hLPs, hcseq]; exact hrr⟩ (fun h => by cases h)

end Front
