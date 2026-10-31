import FV.Link.ExeSource
import FV.E2E.NonVacuityLegalProgram

/-! # `compileExe_correct_source` with the `__*ti3` helpers as the only outside code

`Link.compileExe_correct_source` needs, for a program mentioning `i128`, an outside environment
with the `__*ti3` division helpers (`Opt.Legal.HelperOk`) whose externs return split results for
split arguments (`ExtLegal`) and keep valid ranges below `2^64` (`EnvKeepsBounded`). The closed
base environment (`E2E.LinkCheck.closedBase`, no extern) has no helper.

`helperBase`: the closed base environment whose CLIF environment holds the trusted Rust `__*ti3`
helpers (`helperEnv`, `Clif.Rust.divOutcome`), the machine calling nothing outside the program.
It meets every base premise (`baseOk_helper`) of a program without TLS, without indirect calls
and declaring no helper outside it, the hooks premise (`hooksSim_helper`), and the `i128`
contracts (`helperOk`, `extLegal`, `keepsBounded`). `compileExe_correct_source_helper`:
`compileExe_correct_source` under `helperBase` with these premises decided on the program and
the source run's memory bound proven for slotless programs (`E2E.LegalProgram.Witness.
bounded_of_noSlots`). Its instance on a crate is
`crate-proofs/Crates/CompileExeSourceWitness.lean`.
-/

namespace Link.SourceWitness

open Clif E2E E2E.LinkCheck E2E.Binary E2E.ExecBytes E2E.BinCheck E2E.LegalProgram Opt.Legal
  Opt.Legalize128 Backend Backend.Proof

/-- The trusted Rust `__*ti3` helpers (`Clif.Rust.env`'s), no other extern. -/
def helperEnv : Clif.Env where
  extern n := if Clif.Rust.isDivHelper n then some (Clif.Rust.divOutcome n) else none

/-- The closed base environment with the `__*ti3` helpers in CLIF. -/
def helperBase : BaseEnv := { closedBase with env := helperEnv }

theorem helper_sub {n : String} {h : List Val → Mem → Outcome} (he : helperEnv.extern n = some h) :
    Clif.Rust.env.extern n = some h := by
  simp only [helperEnv] at he
  split at he
  · rename_i hd
    cases he
    simp [Clif.Rust.env, hd]
  · cases he

/-- The helpers return the caller's memory. -/
theorem helper_mem {n : String} {h : List Val → Mem → Outcome} {vals : List Val} {m : Mem}
    {rv : List Val} {m' : Mem} (he : helperEnv.extern n = some h) (hr : h vals m = .returned rv m') :
    m' = m := by
  simp only [helperEnv] at he
  split at he
  · cases he
    simp only [Clif.Rust.divOutcome] at hr
    split at hr
    · cases hr
    · cases hr
    · cases hr; rfl
  · cases he

theorem helperOk : HelperOk helperEnv := by
  intro op
  obtain ⟨h, he, hp⟩ := Clif.Rust.helperOk_env op
  have hd : Clif.Rust.isDivHelper (Opt.Legalize128.divHelper op) = true := by cases op <;> decide
  refine ⟨h, ?_, hp⟩
  have e : helperEnv.extern (Opt.Legalize128.divHelper op) =
      Clif.Rust.env.extern (Opt.Legalize128.divHelper op) := by
    simp [helperEnv, Clif.Rust.env, hd]
  rw [e]; exact he

theorem extLegal : ExtLegal helperEnv := fun name h he => Clif.Rust.extLegal_env name h (helper_sub he)

theorem keepsAllocs : Opt.Legal.EnvKeepsAllocs helperEnv := fun _ _ he _ _ _ _ hr => by
  rw [helper_mem he hr]

theorem keepsBounded : EnvKeepsBounded helperEnv := keepsAllocs.bounded

theorem clifKeepsAllocs : Clif.EnvKeepsAllocs helperEnv := fun _ _ he _ _ _ _ hr x hx => by
  rw [helper_mem he hr] at hx; exact hx

/-- **The base premises of `helperBase`** for results `R` without TLS, without indirect calls,
whose functions declare no `__*ti3` helper outside the program (the machine calls nothing
outside it: every machine-level contract is vacuous, as for `closedBase`). -/
theorem baseOk_helper {I : LinkInput} {R : Res} {F : BitVec 64 → Prop}
    (htls : ∀ g ∈ (progOf R).funcs, Backend.hasTls g = false)
    (hdiv : ∀ g ∈ (progOf R).funcs, ∀ e ∈ g.externs, (progOf R).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false)
    (hind : ∀ g ∈ (progOf R).funcs, Clif.IndFree g)
    (hsigs : ∀ g ∈ (progOf R).funcs, Backend.indSigs g = []) :
    BaseOk (ofRes I R helperBase F) where
  baseNoAlloc := fun _ _ _ hn _ _ _ _ hr _ _ hv => by rw [helper_mem hn hr] at hv; exact hv
  keepSyms := fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn
  aliasSyms := fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn
  baseOs := fun g hg info hs hb F' K G s0 Pc ctx s _ _ _ c wh ops regs i' w outs w' _ _ _ _ _ _
      _ hsem => by simp [csem, ofRes, helperBase, closedBase] at hsem
  basePc := fun d s _ _ _ => by simp [ofRes, helperBase, closedBase, Arm.r_of_w_same]
  baseExt := fun d uses w outs w' _ hx => by simp [ofRes, helperBase, closedBase] at hx
  baseX := fun g hg F' slotOff out c => by
    intro ext hext gs sl cm w d uses args vals rvals cm' he
    simp only [List.mem_filter, List.mem_map, Option.isNone_iff_eq_none] at hext
    obtain ⟨⟨e, he', rfl⟩, hnone⟩ := hext
    have hd := hdiv g hg e he' hnone
    simp [ofRes, helperBase, helperEnv, hd] at he
  baseXI := fun g hg F' slotOff out c => by
    rw [hsigs g hg]; exact xCallsIndOk_nil _ _ _
  baseTls := fun g hg ht => absurd ht (by simp [htls g hg])
  baseTry := fun g hg F' ctx info ti _ c wh ops regs i' s w outs w' s' _ _ _ _ _ _ hsem => by
    simp [csem, ofRes, helperBase, closedBase] at hsem
  baseNI := fun _ g hg F' c n sig vals cm args d uses Z w w' o x o' x' _ _ _ _ _ _ _ _ _ hx _ => by
    simp [ofRes, helperBase, closedBase] at hx
  baseTlsNI := fun _ F' => closedBase_tlsNI (I := I) (R := R) (F' := F) F'
  baseKeepsPlace := fun _ _ _ hn _ _ _ _ hr => by rw [helper_mem hn hr]
  baseKeepsAllocs := fun _ _ _ hn _ _ _ _ hr _ hx => by rw [helper_mem hn hr] at hx; exact hx

/-- The hooks of `helperBase` are `closedBase`'s. -/
theorem hooksSim_helper (I : LinkInput) : HooksSim I helperBase :=
  ⟨(hooksSim_closed I).call, (hooksSim_closed I).tls⟩

theorem lframe_of_entry {f : Function} {args : List Val} {cs : State} (hcs : ClifEntry f args cs)
    {Q : Program} (hh : f ∈ Q.funcs) : LFrame Q cs.frame := by
  obtain ⟨b, hb, h2, h3, -, -⟩ := hcs.entry
  refine ⟨by rw [hcs.func]; exact hh, .inl ⟨b, by rw [hcs.func]; exact entry_mem hb, ?_, h3⟩⟩
  rw [h2]; exact List.suffix_refl _

/-- **The source run's memories stay bounded** under `helperEnv`, for a program in the source
domain without stack slots, from an entry memory with valid ranges below `2^64`
(`E2E.LegalProgram.Witness.bounded_of_noSlots`). -/
theorem srcBounded {I : LinkInput} (hsrc : SrcScopeB I = true)
    (hslots : ∀ g ∈ I.srcProg.funcs, g.slots = []) {f : Clif.Function} (hfP : f ∈ I.srcProg.funcs)
    {args : List Clif.Val} {cs : Clif.State} (hcs : ClifEntry f args cs) (hM : MemBounded cs.mem) :
    ∀ s', Opt.Legal.SReach helperEnv I.srcProg cs s' → MemBounded s'.mem := by
  have hfree : ∀ g ∈ I.srcProg.funcs, LinkFree g := by
    simp only [SrcScopeB, Bool.and_eq_true, List.all_eq_true] at hsrc
    exact fun g hg => linkFreeB_sound (hsrc.1.1.2 g hg)
  have hI : LInv I.srcProg cs :=
    ⟨lframe_of_entry hcs hfP, fun c hc' => by rw [hcs.callers] at hc'; cases hc'⟩
  have hsl0 : Witness.SlotsNil cs := by
    intro fr hfr
    rw [hcs.callers] at hfr
    simp only [List.map_nil, List.mem_singleton] at hfr
    subst hfr
    have := hcs.slotIds
    rw [hslots f hfP] at this
    exact List.map_eq_nil_iff.mp this
  exact Witness.bounded_of_noSlots hfree hslots clifKeepsAllocs hI hsl0 hM

/-- **`compileExe_correct_source` under `helperBase`**: the base premises decided on the
program (no TLS, no indirect call, no `__*ti3` helper declared outside the program, no stack
slot in the source program), the source run's memory bound from an entry memory with valid
ranges below `2^64`. -/
theorem compileExe_correct_source_helper {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (htls : ∀ g ∈ (prog S.input).funcs, Backend.hasTls g = false)
    (hdiv : ∀ g ∈ (prog S.input).funcs, ∀ e ∈ g.externs, (prog S.input).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false)
    (hind : ∀ g ∈ (prog S.input).funcs, Clif.IndFree g)
    (hsigs : ∀ g ∈ (prog S.input).funcs, Backend.indSigs g = [])
    (hslots : ∀ g ∈ S.input.srcProg.funcs, g.slots = [])
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f)
      (StackBound.stackFn S.input (legalize f)) r args' cs'.mem)
    (hr : ClifRun S.input helperBase (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : MemBounded cs.mem) (M : Nat) :
    ∀ vals cm, Clif.runLoop helperEnv S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
          (step S.input helperBase file) r (RelocAt S.input) (.returned vals' cm) := by
  have hbnd := srcBounded hsrc hslots (Clif.Program.func?_some hf).1 hcs hM
  exact (compileExe_correct_source h hsrc helperBase (baseOk_helper htls hdiv hind hsigs)
    (hooksSim_helper _) (fun _ => ⟨helperOk, extLegal, keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf hc hX ho hr hcs hexp hsl hmem hbnd M).1

/-- **`compileExe_correct_source_peak` under `helperBase`** (`compileExe_correct_source_helper`
for recursive programs): the outside caller provides `frameDrop + (D * d + pbMax)` bytes of stack for the
source run's call depth `d` (`Clif.DepthLe`), no call-graph premise. -/
theorem compileExe_correct_source_peak_helper {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (htls : ∀ g ∈ (prog S.input).funcs, Backend.hasTls g = false)
    (hdiv : ∀ g ∈ (prog S.input).funcs, ∀ e ∈ g.externs, (prog S.input).func? e.2.name = none →
      Clif.Rust.isDivHelper e.2.name = false)
    (hind : ∀ g ∈ (prog S.input).funcs, Clif.IndFree g)
    (hsigs : ∀ g ∈ (prog S.input).funcs, Backend.indSigs g = [])
    (hslots : ∀ g ∈ S.input.srcProg.funcs, g.slots = [])
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f)
      (frameDrop (art S.input (legalize f)).af + (S.input.D * d + pbMax S.input)) r args' cs'.mem)
    (hr : ClifRun S.input helperBase (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hM : MemBounded cs.mem) (hd : Clif.DepthLe helperEnv S.input.srcProg d cs) (M : Nat) :
    ∀ vals cm, Clif.runLoop helperEnv S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
          (step S.input helperBase file) r (RelocAt S.input) (.returned vals' cm) :=
  (compileExe_correct_source_peak h hsrc helperBase (baseOk_helper htls hdiv hind hsigs)
    (hooksSim_helper _) (fun _ => ⟨helperOk, extLegal, keepsBounded⟩)
    (fun ⟨g, hg, hn⟩ => absurd (hind g hg) hn) hf d hX ho hr hcs hexp hsl hmem
    (srcBounded hsrc hslots (Clif.Program.func?_some hf).1 hcs hM) hd M).1

end Link.SourceWitness
