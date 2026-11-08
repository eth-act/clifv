import FV.Link.ExeSource
import FV.E2E.SrcBoundedLegal

/-! # The baseline compiler's source theorems without the memory-bound premise (A2/B1)

`Link.compileExe_correct_source{,_peak}` take the run premise
`∀ s', SReach B.env S.input.srcProg cs s' → MemBounded s'.mem` (`Clif.run`'s allocations
need not lie below `2^64`). Their variants here, `Link.compileExe_correct_source_nobnd` and
`compileExe_correct_source_peak_nobnd`, have the same premises without it:

* a program mentioning `i128`: the bound is derived (`srcBounded_acyclic`, `srcBounded_peak`).
  The source run enters only callees of the compiled program (`SrcBounded.callee_of_enter`).
  With program callees having stack slots (`NeedSlots`) the reference run places every
  activation's slots in its compiled frame (`ClifRun.place`), within the stack the outside caller
  provides (`OutsideCall.stack`: `stackFn`, or `frameDrop + (D * d + pbMax)` for call depth `d`;
  #581: the deepest activation's stack probes write up to `pbMax` bytes below its frame), so they
  never wrap (`SrcBounded.bounded_placed`); without, no entered function has slots
  (`SrcBounded.bounded_slotless`). The externs keep valid ranges below `2^64` (the `i128`
  premise `EnvKeepsBounded`) and the oracle (`BaseOk.baseKeepsPlace`);
* a program without `i128`: the legalisation is the identity, so the source run is the compiled
  program's run from the same state (`ident_*`) and the theorems follow from
  `compileExe_correct{,_peak}` directly.
-/

namespace Link
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128 E2E.SrcBounded

/-! ## Facts of the source run -/

theorem reaches_of_sreach {env : Clif.Env} {p : Clif.Program} {s s' : Clif.State}
    (h : Opt.Legal.SReach env p s s') : Clif.Reaches env p s s' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .next hs ih

/-- The symbols of a run under externs keeping them. -/
theorem symbols_reach {B : Clif.Env} {P : Clif.Program} (hP : ∀ g ∈ P.funcs, Clif.LinkFree g)
    (hk : Opt.EnvKeepsSymbols B) {s t : Clif.State} (hI : Clif.LInv P s)
    (hr : Opt.Legal.SReach B P s t) : t.mem.symbols = s.mem.symbols := by
  suffices ∀ a b, Opt.Legal.SReach B P a b → Clif.LInv P a → b.mem.symbols = a.mem.symbols from
    this s t hr hI
  intro a b h
  induction h with
  | refl => exact fun _ => rfl
  | step hs' _ ih =>
    intro hIa
    rw [ih (Clif.step_next_linv hP hIa hs').1, (Clif.step_symbols hP hk hIa).1 _ hs']

theorem enterVia_mem {P : Clif.Program} {g h : Clif.Function} {mem : Clif.Mem}
    (hv : EnterVia P g h mem) : h ∈ P.funcs := by
  rcases hv with ⟨e, -, hpf⟩ | ⟨hh, -⟩
  · exact (Clif.Program.func?_some hpf).1
  · exact hh

/-- `budget_of`'s step: a callee of a function with a budget has one, and its frame fits. -/
theorem bud_callee {I : LinkInput} (hI : okB I = true) (B : BaseEnv)
    (F : BitVec 64 → Prop) {g h : Clif.Function} (hg : g ∈ (progOf I.results).funcs)
    {bg : Nat} (hbg : StackBound.budO I g = some bg)
    (hcl : (LinkSys.ofInput I B F).Callee g h) :
    ∃ bh, StackBound.budO I h = some bh ∧
      frameDrop (artOf I.results h).af + bh ≤ bg := by
  have hok := E2E.StackBound.budOkW_budMap (I := I) (R := I.results) (okB_names hI)
  have he := StackBound.edgeB_of_callee hI hg hcl
  have hh : h ∈ (progOf I.results).funcs := (LinkSys.ofInput I B F).callee_mem hcl
  simp only [E2E.StackBound.budOkW, List.all_eq_true] at hok
  have h1 := hok g hg
  change E2E.StackBound.budC I I.results g = some bg at hbg
  rw [hbg] at h1
  simp only [List.all_eq_true] at h1
  have h2 := h1 h hh
  simp only [E2E.StackBound.edgeB] at he
  rw [he] at h2
  show ∃ bh, E2E.StackBound.budC I I.results h = some bh ∧ _
  cases hch : E2E.StackBound.budC I I.results h with
  | none => rw [hch] at h2; simp at h2
  | some bh =>
    rw [hch] at h2
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at h2
    exact ⟨bh, rfl, h2⟩

/-! ## The bound, from a stack budget -/

/-- **The source run's memories are bounded** (a program mentioning `i128`), for any budget `β`
of the compiled frames along the run's calls: `β k g` bytes below the stack pointer of an
activation of `g` at depth `k` (`Q g`), covering each callee's frame and its own budget
(`hstep`), and the entry's frame and budget within the outside caller's stack `N`. -/
theorem srcBounded_gen {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    (hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true)
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    {N : Nat} {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f) N r
      args' cs'.mem)
    (hr : ClifRun S.input B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs) (hmem : cs'.mem = cs.mem)
    (β : Nat → Clif.Function → Nat) (Q : Clif.Function → Prop)
    (hβ0 : frameDrop (art S.input (legalize f)).af + β 0 f ≤ N) (hQ0 : Q f)
    (hstep : ∀ (k : Nat) (g h : Clif.Function), g ∈ S.input.srcProg.funcs → Q g →
      legalize g ∈ (prog S.input).funcs →
      (sys S.input B).Callee (legalize g) (legalize h) →
      frameDrop (art S.input (legalize h)).af ≤ S.input.D →
      (∃ t1, Opt.Legal.SReach B.env S.input.srcProg cs t1 ∧ t1.callers.length = k + 1) →
      frameDrop (art S.input (legalize h)).af + β (k + 1) h ≤ β k g ∧ Q h) :
    ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hok := okB_leanLink hin hl
  have hL : (LinkSys.ofInput S.input B fun _ => True).Ok :=
    okB_sound hok (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal S.input
  have hpe' : S.input.prog = prog S.input := by
    rw [hpe, LinkInput.prog_eq]
  have hC : ProgCtx S.input.srcProg B.env (fun n => S.input.syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
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
  -- an entered function is a callee
  have hcallee : ∀ (t t1 : Clif.State), Opt.Legal.SReach B.env S.input.srcProg cs t →
      Clif.LInv S.input.srcProg t →
      EnterVia S.input.srcProg t.frame.func t1.frame.func t.mem →
      (sys S.input B).Callee (legalize t.frame.func) (legalize t1.frame.func) :=
    fun t t1 ht hIt hv => callee_of_enter hC hpe rfl hIt.1.1 hv (hms t _ ht hIt.1.1)
  by_cases hns : (sys S.input B).NeedSlots
  · -- the slots placed in the compiled frames
    obtain ⟨sps, hpl⟩ := hr.place hns
    rw [hmem] at hpl
    have hN := ho.stack
    have hfd : frameDrop (art S.input (legalize f)).af ≤ (spv r).toNat := by omega
    have hc := toNat_sub_of_le hfd
    refine bounded_placed hC.free (hB.baseKeepsPlace hns) hkb β Q (sys S.input B).frames hLe
      hM hcs.callers hpl ?_ (by rw [hcs.func]; exact hQ0) ?_
    · rw [hcs.func]
      show β 0 f ≤ (spv r - BitVec.ofNat 64 (frameDrop (art S.input (legalize f)).af)).toNat
      rw [hc]; omega
    · intro t t1 ht hIt hq hs hlen hv
      have hcl := hcallee t t1 ht hIt hv
      have hg := hIt.1.1
      have hh := enterVia_mem hv
      have hlh : legalize t1.frame.func ∈ (prog S.input).funcs := by
        rw [hpe]; simp only [legalProg_funcs]; exact List.mem_map_of_mem hh
      have hlg : legalize t.frame.func ∈ (prog S.input).funcs := by
        rw [hpe]; simp only [legalProg_funcs]; exact List.mem_map_of_mem hg
      have hFh := legalFacts (hC.ok _ hh)
      have hpf : (prog S.input).func? t1.frame.func.name = some (legalize t1.frame.func) := by
        rw [hpe]; exact hC.func?_some (func?_of_mem hC.nd hh)
      obtain ⟨hb, hq'⟩ := hstep t.callers.length t.frame.func t1.frame.func hg hq hlg hcl
        (hL.depth _ hlh) ⟨t1, ht.trans (.step hs (.refl _)), hlen⟩
      refine ⟨frameDrop (art S.input (legalize t1.frame.func)).af,
        fun id => (art S.input (legalize t1.frame.func)).af.slotBase +
          ((slotLayout (legalize t1.frame.func).slots).1.lookup id).getD 0, ?_, fun p hp => ?_, hb, hq'⟩
      · simp only [LinkSys.frames]
        rw [show (sys S.input B).P = prog S.input from rfl, hpf]
        rfl
      · obtain ⟨off, hlk, hle⟩ := hL.slotFits _ hlg _ hcl p (by rw [hFh.slots]; exact hp)
        have hfr := (frame_facts hL hlh).1
        show (art S.input (legalize t1.frame.func)).af.slotBase +
            ((slotLayout (legalize t1.frame.func).slots).1.lookup p.1).getD 0 + p.2.size ≤
          frameDrop (art S.input (legalize t1.frame.func)).af
        rw [hlk, Option.getD_some, hfr]
        have : (LinkSys.ofInput S.input B fun _ => True).A (legalize t1.frame.func) =
          art S.input (legalize t1.frame.func) := rfl
        rw [this] at hle
        omega
  · -- no program callee has slots
    refine bounded_slotless hC.free hkb hLe hM fun t t1 ht hIt _ _ hv => ?_
    have hcl := hcallee t t1 ht hIt hv
    have hlg : legalize t.frame.func ∈ (prog S.input).funcs := by
      rw [hpe]; simp only [legalProg_funcs]; exact List.mem_map_of_mem hIt.1.1
    have hnil : (legalize t1.frame.func).slots = [] :=
      Classical.byContradiction fun hne => hns ⟨_, hlg, _, hcl, hne⟩
    rwa [(legalFacts (hC.ok _ (enterVia_mem hv))).slots] at hnil

/-- **The bound for an entry without a call cycle** (`compileExe_correct_source`'s stack). -/
theorem srcBounded_acyclic {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    (hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true)
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hc : ¬ StackBound.CycleFrom
      (StackBound.Calls S.input S.input.results) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f)
      (StackBound.stackFn S.input (legalize f)) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs) (hmem : cs'.mem = cs.mem) :
    ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hok := okB_leanLink hin hl
  have hfl : legalize f ∈ (prog S.input).funcs := by
    rw [prog_eq_legal]; simp only [legalProg_funcs]
    exact List.mem_map_of_mem (Clif.Program.func?_some hf).1
  have hQ0 : (StackBound.budO S.input (legalize f)).isSome = true :=
    (E2E.StackBound.budC_isSome_iff (okB_names hok) hfl).2 hc
  refine srcBounded_gen h hsrc B hB hlegal hsig hm hf ho hr hcs hmem
    (fun _ g => StackBound.bud S.input (legalize g))
    (fun g => (StackBound.budO S.input (legalize g)).isSome = true)
    (Nat.le_refl _) hQ0 ?_
  intro k g h' _ hq hlg hcl _ _
  obtain ⟨bg, hbg⟩ := Option.isSome_iff_exists.1 hq
  obtain ⟨bh, hbh, hle⟩ := bud_callee hok B (fun _ => False) hlg hbg hcl
  refine ⟨?_, by rw [hbh]; rfl⟩
  simp only [StackBound.bud, hbg, hbh, Option.getD_some]
  exact hle

/-- **The bound for a run of call depth at most `d`** (`compileExe_correct_source_peak`'s
stack). -/
theorem srcBounded_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    (hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true)
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f)
      (frameDrop (art S.input (legalize f)).af + (S.input.D * d + pbMax S.input)) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs) (hmem : cs'.mem = cs.mem)
    (hd : Clif.DepthLe B.env S.input.srcProg d cs) :
    ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem := by
  refine srcBounded_gen h hsrc B hB hlegal hsig hm hf ho hr hcs hmem
    (fun k _ => S.input.D * (d - k) + pbMax S.input) (fun _ => True) (by simp) trivial ?_
  intro k g h' _ _ _ _ hD ⟨t1, ht1, hlen⟩
  have hk : k + 1 ≤ d := hlen ▸ hd t1 (reaches_of_sreach ht1)
  refine ⟨?_, trivial⟩
  have e : d - k = (d - (k + 1)) + 1 := by omega
  show frameDrop _ + (S.input.D * (d - (k + 1)) + pbMax S.input) ≤ S.input.D * (d - k) + pbMax S.input
  rw [e, Nat.mul_succ]
  omega

/-! ## Programs without `i128`: the identity -/

/-- Two entry states of `f` on `args` with the same slots and memory are equal. -/
theorem ident_state {f : Clif.Function} {args : List Clif.Val} {cs cs' : Clif.State}
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry f args cs')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem) : cs' = cs := by
  obtain ⟨b, hb, h2, h3, -, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  rw [hb] at hb'
  injection hb' with e
  subst e
  rw [h5] at h5'
  injection h5' with e5
  have e1 := hcs.func
  have e2 := hcs'.func
  have c1 := hcs.callers
  have c2 := hcs'.callers
  obtain ⟨⟨fn, rg, sl, bd, tm⟩, cl, m⟩ := cs
  obtain ⟨⟨fn', rg', sl', bd', tm'⟩, cl', m'⟩ := cs'
  simp only at h2 h3 h2' h3' e5 e1 e2 c1 c2 hsl hmem ⊢
  subst e1 e2 c1 c2 hsl hmem e5
  rw [h2, h2', h3, h3']

/-- Without `i128`, the compiled program is the source program. -/
theorem prog_eq_src {S : LinkSpec}
    (hm : ¬ ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true) :
    prog S.input = S.input.srcProg ∧
      ∀ g ∈ S.input.srcProg.funcs, mentions128 g = false ∧ legalize g = g := by
  have hmf : ∀ g ∈ S.input.srcProg.funcs, mentions128 g = false := fun g hg => by
    cases hx : mentions128 g
    · rfl
    · exact absurd ⟨g, hg, hx⟩ hm
  have hl : ∀ g ∈ S.input.srcProg.funcs, legalize g = g :=
    fun g hg => Opt.Legal.Complete.legalize_of_not_mentions (hmf g hg)
  refine ⟨?_, fun g hg => ⟨hmf g hg, hl g hg⟩⟩
  rw [prog_eq_legal]
  have : S.input.srcProg.funcs.map legalize = S.input.srcProg.funcs :=
    (List.map_congr_left hl).trans (List.map_id _)
  simp only [legalProg, this]

/-! ## The theorems -/

/-- **The shipped executable compiler refines the original source program, without the memory
bound** (A2/B1): `compileExe_correct_source` without the premise that the source run's memories
lie below `2^64`. -/
theorem compileExe_correct_source_nobnd {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hc : ¬ StackBound.CycleFrom
      (StackBound.Calls S.input S.input.results) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f)
      (StackBound.stackFn S.input (legalize f)) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base
          (xreg 30 r) (step S.input B file) r
          (E2E.BinCheck.RelocAt S.input) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M)
        (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap B.env S.input.srcProg cs → ∀ c,
      Clif.runLoop B.env S.input.srcProg M cs = .trapped c →
      ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base
        (xreg 30 r) (step S.input B file) r
        (E2E.BinCheck.RelocAt S.input) (.trapped c)) := by
  by_cases hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true
  · exact compileExe_correct_source h hsrc B hB hH hlegal hsig hf hc hX ho hr hcs hexp hsl hmem
      (srcBounded_acyclic h hsrc B hB hlegal hsig hm hf hc ho hr hcs hmem) M
  -- the identity: the compiled program's run from the same state
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hL : (LinkSys.ofInput S.input B fun _ => True).Ok :=
    okB_sound (okB_leanLink hin hl) (baseOk_F hB) fun _ _ => trivial
  obtain ⟨hpP, hall⟩ := prog_eq_src hm
  have hfP := (Clif.Program.func?_some hf).1
  obtain ⟨hmf, hfl⟩ := hall f hfP
  have hs := (not_mentions hmf).1
  obtain ⟨gs, hgs, hG⟩ := Opt.Legal.groups_plain (Opt.Legal.sig128_params hs)
  rw [hgs, Option.getD_some] at hexp
  have hvv : args' = args := Opt.Legal.expRel_val hG (Opt.Legal.sig128_params hs) hexp
  have hcs' := hr.entry
  have hcs'' : ClifEntry f args cs' := by rw [← hfl, ← hvv]; exact hcs'
  have hcseq : cs' = cs := ident_state hcs hcs'' hsl hmem
  have hf' : (prog S.input).func? n = some (legalize f) := by rw [hpP, hfl]; exact hf
  have hfP' : legalize f ∈ (prog S.input).funcs := (Clif.Program.func?_some hf').1
  refine ⟨fun vals cm hrun => ?_, fun htr _ c hrun => ?_⟩
  · cases M with
    | zero => simp at hrun
    | succ K =>
      have hK : Clif.runLoop B.env (prog S.input) (K + 1) cs' = .returned vals cm := by
        rw [hpP, hcseq]; exact hrun
      have H := compileExe_correct h B hB hH hf' hc K hX ho hr
        (trapsExplicit_of_run hL hfP' hcs' ho.symbols hK)
      rw [hK] at H
      refine ⟨vals, ?_, H⟩
      obtain ⟨rg, hrg, hR⟩ := Opt.Legal.groups_plain (Opt.Legal.sig128_returns hs)
      rw [hrg, Option.getD_some]
      have hLe : Clif.LInv S.input.srcProg cs := by
        rw [← hpP, ← hcseq]
        have := hcs'
        obtain ⟨b, hb, h2, h3, -, -⟩ := this.entry
        refine ⟨⟨by rw [this.func]; exact hfP', .inl ⟨b, by rw [this.func]; exact entry_mem hb,
          ?_, ?_⟩⟩, fun c hc => by rw [this.callers] at hc; cases hc⟩
        · rw [h2]; exact List.suffix_refl _
        · rw [h3]
      have hty := Clif.runLoop_returned_tys (by rw [← hpP]; exact hL.free) (K + 1) cs vals cm
        hLe hrun
      simp only [Clif.State.bottom, hcs.callers, hcs.func, List.getLast?_nil, Option.map_none,
        Option.getD_none] at hty
      refine Opt.Legal.expRel_refl_plain hR (Opt.Legal.sig128_returns hs) ?_
      have := congrArg List.length hty
      simpa [Clif.AbiParam.tys] using this
  · cases M with
    | zero => simp at hrun
    | succ K =>
      have hK : Clif.runLoop B.env (prog S.input) (K + 1) cs' = .trapped c := by
        rw [hpP, hcseq]; exact hrun
      have H := compileExe_correct h B hB hH hf' hc K hX ho hr (htr K)
      rw [hK] at H
      exact H

/-- **The shipped executable compiler refines the original source program, recursive programs
included, without the memory bound** (A2/B1): `compileExe_correct_source_peak` without the
premise that the source run's memories lie below `2^64`. -/
theorem compileExe_correct_source_peak_nobnd {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f)
      (frameDrop (art S.input (legalize f)).af + (S.input.D * d + pbMax S.input)) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hd : Clif.DepthLe B.env S.input.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base
          (xreg 30 r) (step S.input B file) r
          (E2E.BinCheck.RelocAt S.input) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d)
        (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap B.env S.input.srcProg cs → ∀ c,
      Clif.runLoop B.env S.input.srcProg M cs = .trapped c →
      ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base
        (xreg 30 r) (step S.input B file) r
        (E2E.BinCheck.RelocAt S.input) (.trapped c)) := by
  by_cases hm : ∃ g ∈ S.input.srcProg.funcs, mentions128 g = true
  · exact compileExe_correct_source_peak h hsrc B hB hH hlegal hsig hf d hX ho hr hcs hexp hsl
      hmem (srcBounded_peak h hsrc B hB hlegal hsig hm hf d ho hr hcs hmem hd) hd M
  -- the identity: the compiled program's run from the same state
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hL : (LinkSys.ofInput S.input B fun _ => True).Ok :=
    okB_sound (okB_leanLink hin hl) (baseOk_F hB) fun _ _ => trivial
  obtain ⟨hpP, hall⟩ := prog_eq_src hm
  have hfP := (Clif.Program.func?_some hf).1
  obtain ⟨hmf, hfl⟩ := hall f hfP
  have hs := (not_mentions hmf).1
  obtain ⟨gs, hgs, hG⟩ := Opt.Legal.groups_plain (Opt.Legal.sig128_params hs)
  rw [hgs, Option.getD_some] at hexp
  have hvv : args' = args := Opt.Legal.expRel_val hG (Opt.Legal.sig128_params hs) hexp
  have hcs' := hr.entry
  have hcs'' : ClifEntry f args cs' := by rw [← hfl, ← hvv]; exact hcs'
  have hcseq : cs' = cs := ident_state hcs hcs'' hsl hmem
  have hf' : (prog S.input).func? n = some (legalize f) := by rw [hpP, hfl]; exact hf
  have hfP' : legalize f ∈ (prog S.input).funcs := (Clif.Program.func?_some hf').1
  have hdT : Clif.DepthLe B.env (prog S.input) d cs' := by rw [hpP, hcseq]; exact hd
  refine ⟨fun vals cm hrun => ?_, fun htr _ c hrun => ?_⟩
  · cases M with
    | zero => simp at hrun
    | succ K =>
      have hK : Clif.runLoop B.env (prog S.input) (K + 1) cs' = .returned vals cm := by
        rw [hpP, hcseq]; exact hrun
      have H := compileExe_correct_peak h B hB hH hf' K d hX ho hr hdT
        (E2E.Binary.trapsExplicit_of_runD hL hfP' hcs' ho.symbols hdT hK)
      rw [hK] at H
      refine ⟨vals, ?_, H⟩
      obtain ⟨rg, hrg, hR⟩ := Opt.Legal.groups_plain (Opt.Legal.sig128_returns hs)
      rw [hrg, Option.getD_some]
      have hLe : Clif.LInv S.input.srcProg cs := by
        rw [← hpP, ← hcseq]
        have := hcs'
        obtain ⟨b, hb, h2, h3, -, -⟩ := this.entry
        refine ⟨⟨by rw [this.func]; exact hfP', .inl ⟨b, by rw [this.func]; exact entry_mem hb,
          ?_, ?_⟩⟩, fun c hc => by rw [this.callers] at hc; cases hc⟩
        · rw [h2]; exact List.suffix_refl _
        · rw [h3]
      have hty := Clif.runLoop_returned_tys (by rw [← hpP]; exact hL.free) (K + 1) cs vals cm
        hLe hrun
      simp only [Clif.State.bottom, hcs.callers, hcs.func, List.getLast?_nil, Option.map_none,
        Option.getD_none] at hty
      refine Opt.Legal.expRel_refl_plain hR (Opt.Legal.sig128_returns hs) ?_
      have := congrArg List.length hty
      simpa [Clif.AbiParam.tys] using this
  · cases M with
    | zero => simp at hrun
    | succ K =>
      have hK : Clif.runLoop B.env (prog S.input) (K + 1) cs' = .trapped c := by
        rw [hpP, hcseq]; exact hrun
      have H := compileExe_correct_peak h B hB hH hf' K d hX ho hr hdT (htr K)
      rw [hK] at H
      exact H

end Link
