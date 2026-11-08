import FV.Link.OptExe
import FV.Link.OptKeepsInd
import FV.Link.ExeSourceNB

/-! # The optimising compiler's source theorems without the memory-bound premise (A2/B1)

`Link.compileExeOpt_correct_source{,_peak}` take the run premise
`∀ s', SReach B.env S.input.srcProg cs s' → MemBounded s'.mem` (`Clif.run`'s allocations
need not lie below `2^64`). Their variants here, `Link.compileExeOpt_correct_source_nobnd` and
`compileExeOpt_correct_source_peak_nobnd`, have the same premises without it, as the baseline
compiler's (`FV/Link/ExeSourceNB.lean`):

* a program mentioning `i128`: the bound is derived (`srcBoundedOpt_acyclic`,
  `srcBoundedOpt_peak`). The outside call enters the optimised function `f'`, whose reference run
  places every activation's slots in the compiled frame of the **optimised** function of its name
  (`ClifRun.place` of the optimised input). The source run enters `h` from `g` only when the
  optimised `h'` is a callee of the optimised `g'` (`callee_of_enter_opt`: the optimised functions
  keep the externs and, by `FnInput.opt`'s guard `keepsIndB`, the indirect calls) with `h`'s slots,
  so the optimised input's frames and budgets bound the source run's stack as in
  `srcBounded_gen`;
* a program without `i128`: the legalisation is the identity, so the source run is the input
  program's run from the same state and the theorems follow from
  `compileExeOpt_correct{,_peak}` directly.
-/

namespace Link
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128 E2E.SrcBounded

/-- The optimised input and the legalised source program. -/
theorem optRelK_legal (S : LinkSpec) :
    OptRelK (legalProg S.input.srcProg) (prog S.opt.input) := by
  rw [← prog_eq_legal S.input, prog_input, prog_input]; exact S.optRelK

/-! ## The bound, from a stack budget of the optimised input -/

/-- **The source run's memories are bounded** (a program mentioning `i128`, the optimising
compiler), for any budget `β` of the optimised compiled frames along the run's calls: `β k g`
bytes below the stack pointer of an activation of `g` at depth `k` (`Q g`), covering the frame
of the optimised callee `h'` and its own budget (`hstep`, `h'` a callee of `g`'s optimised `g'`),
and the entry's optimised frame and budget within the outside caller's stack `N`. -/
theorem srcBoundedOpt_gen {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B))
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    (hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true)
    {n : String} {f f' : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    {N : Nat} {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f' N r args' cs'.mem)
    (hr : ClifRun S.opt.input B f' r args' cs')
    (hcs : ClifEntry f args cs) (hmem : cs'.mem = cs.mem)
    (β : Nat → Clif.Function → Nat) (Q : Clif.Function → Prop)
    (hβ0 : frameDrop (art S.opt.input f').af + β 0 f ≤ N) (hQ0 : Q f)
    (hstep : ∀ (k : Nat) (g h g' h' : Clif.Function), g ∈ S.input.srcProg.funcs → Q g →
      (prog S.opt.input).func? g.name = some g' → (prog S.opt.input).func? h.name = some h' →
      (sys S.opt.input B).Callee g' h' →
      frameDrop (art S.opt.input h').af ≤ S.opt.input.D →
      (∃ t1, Opt.Legal.SReach B.env S.input.srcProg cs t1 ∧ t1.callers.length = k + 1) →
      frameDrop (art S.opt.input h').af + β (k + 1) h ≤ β k g ∧ Q h) :
    ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem := by
  have hL := linkOk_opt h B hB
  have hC := srcCtx_opt h hsrc B hB hlegal hsig
  have hRK := optRelK_legal S
  have hfP := (Clif.Program.func?_some hf).1
  have hkb : Opt.Legal.EnvKeepsBounded B.env := (hlegal hm).2.2
  have hLe : Clif.LInv S.input.srcProg cs := by
    obtain ⟨b, hb, h2, h3, -, -⟩ := hcs.entry
    refine ⟨⟨by rw [hcs.func]; exact hfP, .inl ⟨b, by rw [hcs.func]; exact entry_mem hb, ?_, ?_⟩⟩,
      fun c hc => by rw [hcs.callers] at hc; cases hc⟩
    · rw [h2]; exact List.suffix_refl _
    · rw [h3]
  have hM : Opt.Legal.MemBounded cs.mem := fun a k hv => (ho.valid a k (by rw [hmem]; exact hv)).1
  -- the symbols of the run, with an indirect call
  have hms : ∀ (t : Clif.State) (g : Clif.Function), Opt.Legal.SReach B.env S.input.srcProg cs t →
      g ∈ S.input.srcProg.funcs → (∃ sig, Opt.Legal.IndSite g sig) →
      t.mem.symbols = fun n => S.input.syms.lookup n := by
    intro t g ht hg ⟨sig, hs⟩
    have hI : SomeInd (legalProg S.input.srcProg) :=
      ⟨legalize g, by simp only [legalProg_funcs]; exact List.mem_map_of_mem hg,
        (legalFacts (hC.ok g hg)).ind (not_indFree_of_site hs)⟩
    rw [symbols_reach hC.free (hC.ind hI).1.keep hLe ht, ← hmem]
    exact ho.symbols
  -- an entered function's optimised counterpart is a callee of the caller's
  have hcallee : ∀ (t t1 : Clif.State), Opt.Legal.SReach B.env S.input.srcProg cs t →
      Clif.LInv S.input.srcProg t →
      EnterVia S.input.srcProg t.frame.func t1.frame.func t.mem →
      ∃ g' h', (prog S.opt.input).func? t.frame.func.name = some g' ∧
        (prog S.opt.input).func? t1.frame.func.name = some h' ∧
        h'.slots = t1.frame.func.slots ∧ (sys S.opt.input B).Callee g' h' :=
    fun t t1 ht hIt hv => callee_of_enter_opt (L := sys S.opt.input B) hC hRK rfl hIt.1.1 hv
      (hms t _ ht hIt.1.1)
  by_cases hns : (sys S.opt.input B).NeedSlots
  · -- the slots placed in the optimised compiled frames
    obtain ⟨sps, hpl⟩ := hr.place hns
    rw [hmem] at hpl
    have hN := ho.stack
    have hfd : frameDrop (art S.opt.input f').af ≤ (spv r).toNat := by omega
    have hc := toNat_sub_of_le hfd
    refine bounded_placed hC.free (hB.baseKeepsPlace hns) hkb β Q (sys S.opt.input B).frames hLe
      hM hcs.callers hpl ?_ (by rw [hcs.func]; exact hQ0) ?_
    · rw [hcs.func]
      show β 0 f ≤ (spv r - BitVec.ofNat 64 (frameDrop (art S.opt.input f').af)).toNat
      rw [hc]; omega
    · intro t t1 ht hIt hq hs hlen hv
      obtain ⟨g', h', hg', hh', hsl', hcl⟩ := hcallee t t1 ht hIt hv
      have hg := hIt.1.1
      have hlg : g' ∈ (prog S.opt.input).funcs := (Clif.Program.func?_some hg').1
      have hlh : h' ∈ (prog S.opt.input).funcs := (Clif.Program.func?_some hh').1
      obtain ⟨hb, hq'⟩ := hstep t.callers.length t.frame.func t1.frame.func g' h' hg hq hg' hh'
        hcl (hL.depth _ hlh) ⟨t1, ht.trans (.step hs (.refl _)), hlen⟩
      refine ⟨frameDrop (art S.opt.input h').af,
        fun id => (art S.opt.input h').af.slotBase +
          ((slotLayout h'.slots).1.lookup id).getD 0, ?_, fun p hp => ?_, hb, hq'⟩
      · simp only [LinkSys.frames]
        rw [show (sys S.opt.input B).P = prog S.opt.input from rfl, hh']
        rfl
      · obtain ⟨off, hlk, hle⟩ := hL.slotFits _ hlg _ hcl p (by rw [hsl']; exact hp)
        have hfr := (frame_facts hL hlh).1
        show (art S.opt.input h').af.slotBase +
            ((slotLayout h'.slots).1.lookup p.1).getD 0 + p.2.size ≤
          frameDrop (art S.opt.input h').af
        rw [hlk, Option.getD_some, hfr]
        have : (LinkSys.ofInput S.opt.input B fun _ => True).A h' = art S.opt.input h' := rfl
        rw [this] at hle
        omega
  · -- no program callee has slots
    refine bounded_slotless hC.free hkb hLe hM fun t t1 ht hIt _ _ hv => ?_
    obtain ⟨g', h', hg', -, hsl', hcl⟩ := hcallee t t1 ht hIt hv
    have hlg : g' ∈ (prog S.opt.input).funcs := (Clif.Program.func?_some hg').1
    rw [← hsl']
    exact Classical.byContradiction fun hne => hns ⟨_, hlg, _, hcl, hne⟩

/-- The optimised counterpart of a source function, by name. -/
def optOf (S : LinkSpec) (g : Clif.Function) : Clif.Function :=
  ((prog S.opt.input).func? g.name).getD g

theorem optOf_eq {S : LinkSpec} {g g' : Clif.Function}
    (h : (prog S.opt.input).func? g.name = some g') : optOf S g = g' := by
  simp only [optOf, h, Option.getD_some]

/-- **The bound for an optimised entry without a call cycle** (`compileExeOpt_correct_source`'s
stack). -/
theorem srcBoundedOpt_acyclic {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B))
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    (hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true)
    {n : String} {f f' : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.opt.input S.opt.input.results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (StackBound.stackFn S.opt.input f') r args' cs'.mem)
    (hr : ClifRun S.opt.input B f' r args' cs')
    (hcs : ClifEntry f args cs) (hmem : cs'.mem = cs.mem) :
    ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem := by
  obtain ⟨hin, hl⟩ := compileExe_spec (compileExeOpt_spec h)
  have hok := okB_leanLink hin hl
  have hfl : f' ∈ (prog S.opt.input).funcs := (Clif.Program.func?_some hf').1
  have hff : optOf S f = f' := optOf_eq (by rw [(Clif.Program.func?_some hf).2]; exact hf')
  have hQ0 : (StackBound.budO S.opt.input (optOf S f)).isSome = true := by
    rw [hff]; exact (E2E.StackBound.budC_isSome_iff (okB_names hok) hfl).2 hc
  refine srcBoundedOpt_gen h hsrc B hB hlegal hsig hm hf ho hr hcs hmem
    (fun _ g => StackBound.bud S.opt.input (optOf S g))
    (fun g => (StackBound.budO S.opt.input (optOf S g)).isSome = true)
    (by rw [hff]; exact Nat.le_refl _) hQ0 ?_
  intro k g h' g' h'' _ hq hg' hh' hcl _ _
  rw [optOf_eq hg'] at hq
  obtain ⟨bg, hbg⟩ := Option.isSome_iff_exists.1 hq
  obtain ⟨bh, hbh, hle⟩ := bud_callee hok B (fun _ => False) (Clif.Program.func?_some hg').1 hbg hcl
  refine ⟨?_, by rw [optOf_eq hh', hbh]; rfl⟩
  simp only [StackBound.bud, optOf_eq hg', optOf_eq hh', hbg, hbh, Option.getD_some]
  exact hle

/-- **The bound for a run of call depth at most `d`** (`compileExeOpt_correct_source_peak`'s
stack). -/
theorem srcBoundedOpt_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B))
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    (hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true)
    {n : String} {f f' : Clif.Function} (hf : S.input.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (frameDrop (art S.opt.input f').af + (S.opt.input.D * d + pbMax S.opt.input)) r args' cs'.mem)
    (hr : ClifRun S.opt.input B f' r args' cs')
    (hcs : ClifEntry f args cs) (hmem : cs'.mem = cs.mem)
    (hd : Clif.DepthLe B.env S.input.srcProg d cs) :
    ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem := by
  refine srcBoundedOpt_gen h hsrc B hB hlegal hsig hm hf ho hr hcs hmem
    (fun k _ => S.opt.input.D * (d - k) + pbMax S.opt.input) (fun _ => True) (by simp) trivial ?_
  intro k g h' g' h'' _ _ _ _ _ hD ⟨t1, ht1, hlen⟩
  have hk : k + 1 ≤ d := hlen ▸ hd t1 (reaches_of_sreach ht1)
  refine ⟨?_, trivial⟩
  have e : d - k = (d - (k + 1)) + 1 := by omega
  show frameDrop _ + (S.opt.input.D * (d - (k + 1)) + pbMax S.opt.input) ≤
    S.opt.input.D * (d - k) + pbMax S.opt.input
  rw [e, Nat.mul_succ]
  omega

/-! ## The theorems -/

/-- The input's function and the optimised entry, without `i128`: the input program is the
source program, and the input function's entry with the source entry's slots and memory is the
source entry. -/
theorem ident_opt {S : LinkSpec} (hm : ¬ ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true)
    {n : String} {f f' : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f')
    {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hcs' : ClifEntry f' args' cs') (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem) :
    args' = args ∧ prog S.input = S.input.srcProg ∧ (prog S.input).func? n = some f ∧
      cs.frame.regs = cs'.frame.regs ∧ cs.frame.slots = cs'.frame.slots ∧ cs.mem = cs'.mem ∧
      ∃ rg, Opt.Legal.groups f.sig.returns = some rg ∧
        ∀ vals : List Clif.Val, vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns →
          Opt.Legal.ExpRel rg vals vals := by
  obtain ⟨hpP, hall⟩ := prog_eq_src hm
  have hfP := (Clif.Program.func?_some hf).1
  obtain ⟨hmf, -⟩ := hall f hfP
  have hs := (not_mentions hmf).1
  obtain ⟨gs, hgs, hG⟩ := Opt.Legal.groups_plain (Opt.Legal.sig128_params hs)
  rw [hgs, Option.getD_some] at hexp
  have hvv : args' = args := Opt.Legal.expRel_val hG (Opt.Legal.sig128_params hs) hexp
  have hfI : (prog S.input).func? n = some f := by rw [hpP]; exact hf
  obtain ⟨csI, hcsI, hrI, hsI, hmI, -, -⟩ := (optRel_prog S).entry hfI hf' hcs'
  have hcsI' : ClifEntry f args csI := by rw [← hvv]; exact hcsI
  have hcseq : csI = cs := ident_state hcs hcsI' (hsI.trans hsl) (hmI.trans hmem)
  subst hcseq
  obtain ⟨rg, hrg, hR⟩ := Opt.Legal.groups_plain (Opt.Legal.sig128_returns hs)
  refine ⟨hvv, hpP, hfI, hrI, hsI, hmI, rg, hrg, fun vals hty => ?_⟩
  refine Opt.Legal.expRel_refl_plain hR (Opt.Legal.sig128_returns hs) ?_
  have := congrArg List.length hty
  simpa [Clif.AbiParam.tys] using this

/-- The returned values of the source run from `f`'s entry have `f`'s return types. -/
theorem returned_tys_src {P : Clif.Program} {B : Clif.Env} (hfree : ∀ g ∈ P.funcs, Clif.LinkFree g)
    {f : Clif.Function} (hfP : f ∈ P.funcs) {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs) {M : Nat} {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B P M cs = .returned vals cm) :
    vals.map (·.ty) = Clif.AbiParam.tys f.sig.returns := by
  have hLe : Clif.LInv P cs := by
    obtain ⟨b, hb, h2, h3, -, -⟩ := hcs.entry
    refine ⟨⟨by rw [hcs.func]; exact hfP, .inl ⟨b, by rw [hcs.func]; exact entry_mem hb,
      ?_, ?_⟩⟩, fun c hc => by rw [hcs.callers] at hc; cases hc⟩
    · rw [h2]; exact List.suffix_refl _
    · rw [h3]
  have hty := Clif.runLoop_returned_tys hfree M cs vals cm hLe hrun
  simpa only [Clif.State.bottom, hcs.callers, hcs.func, List.getLast?_nil, Option.map_none,
    Option.getD_none] using hty

/-- **The optimising executable compiler refines the original source program, without the
memory bound** (A2/B1): `compileExeOpt_correct_source` without the premise that the source run's
memories lie below `2^64`. -/
theorem compileExeOpt_correct_source_nobnd {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) (hH : HooksSim S.opt.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.opt.input S.opt.input.results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (StackBound.stackFn S.opt.input f') r args' cs'.mem)
    (hr : ClifRun S.opt.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
          (step S.opt.input B file) r (RelocAt S.opt.input) (.returned vals' cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.opt.input) B.env K) (prog S.opt.input).bare cs') →
      Opt.Legal.NoMemTrap B.env S.input.srcProg cs → ∀ c,
      Clif.runLoop B.env S.input.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.trapped c)) := by
  by_cases hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true
  · exact compileExeOpt_correct_source h hsrc B hB hH hkeep hlegal hsig hf hf' hc hX ho hr hcs
      hexp hsl hmem (srcBoundedOpt_acyclic h hsrc B hB hlegal hsig hm hf hf' hc ho hr hcs hmem) M
  -- the identity: the input program's run from the same state
  have hC := srcCtx_opt h hsrc B hB hlegal hsig
  obtain ⟨hvv, hpP, hfI, hrg, hsg, hmg, rg, hrgs, hR⟩ :=
    ident_opt hm hf hf' hr.entry hcs hexp hsl hmem
  subst hvv
  have H := compileExeOpt_correct h B hB hH hkeep hfI hf' hc hX ho hr hcs hrg hsg hmg M
  rw [hpP] at H
  refine ⟨fun vals cm hrun => ⟨vals, ?_, H.1 vals cm hrun⟩, fun htr _ c hrun => H.2 htr c hrun⟩
  rw [hrgs, Option.getD_some]
  exact hR vals (returned_tys_src hC.free (Clif.Program.func?_some hf).1 hcs hrun)

/-- **The optimising executable compiler refines the original source program, recursive
programs included, without the memory bound** (A2/B1): `compileExeOpt_correct_source_peak`
without the premise that the source run's memories lie below `2^64`. -/
theorem compileExeOpt_correct_source_peak_nobnd {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) (hH : HooksSim S.opt.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (frameDrop (art S.opt.input f').af + (S.opt.input.D * d + pbMax S.opt.input)) r args' cs'.mem)
    (hr : ClifRun S.opt.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hd : Clif.DepthLe B.env S.input.srcProg d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
          (step S.opt.input B file) r (RelocAt S.opt.input) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.opt.input) B.env F d)
        (prog S.opt.input).bare cs') →
      Opt.Legal.NoMemTrap B.env S.input.srcProg cs → ∀ c,
      Clif.runLoop B.env S.input.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.trapped c)) := by
  by_cases hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true
  · exact compileExeOpt_correct_source_peak h hsrc B hB hH hkeep hlegal hsig hf hf' d hX ho hr hcs
      hexp hsl hmem (srcBoundedOpt_peak h hsrc B hB hlegal hsig hm hf d ho hr hcs hmem hd) hd M
  -- the identity: the input program's run from the same state
  have hC := srcCtx_opt h hsrc B hB hlegal hsig
  obtain ⟨hvv, hpP, hfI, hrg, hsg, hmg, rg, hrgs, hR⟩ :=
    ident_opt hm hf hf' hr.entry hcs hexp hsl hmem
  subst hvv
  have H := compileExeOpt_correct_peak h B hB hH hkeep hfI hf' d hX ho hr hcs hrg hsg hmg
    (by rw [hpP]; exact hd) M
  rw [hpP] at H
  refine ⟨fun vals cm hrun => ⟨vals, ?_, H.1 vals cm hrun⟩, fun htr _ c hrun => H.2 htr c hrun⟩
  rw [hrgs, Option.getD_some]
  exact hR vals (returned_tys_src hC.free (Clif.Program.func?_some hf).1 hcs hrun)

end Link
