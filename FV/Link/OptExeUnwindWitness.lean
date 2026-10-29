module

public import FV.Link.OptExeUnwind
public import FV.Link.ExeUnwindWitness

@[expose] public section

/-!
# Witness: `compileExeOptU` succeeds and `compileExeOpt_correct_unwind{,_peak}` apply (S10g, #404)

`Link.DeadCleanup.UnwindWitness`'s self-recursive `%rec` (it calls itself: a frame, unwind rows)
in the same small static executable, now laid out for the optimised input: the region holds the
optimised functions' code (`specO`: the sizes of `spec.opt`'s compiled functions), and the
`.eh_frame_hdr`/`.eh_frame`/`.gcc_except_table` segments carry their FDEs as lean-backend writes
them, relocated as a linker does (`ehSegOf`). `compileExeOptU` (what `lake exe lean-link --opt`
decides) succeeds (`compile_eq`, `native_decide`):

* `stmt`: `compileExeOpt_correct_unwind`'s statement holds for the written executable;
* `peak_applies`: `compileExeOpt_correct_unwind_peak` instantiated at this executable, `%rec` of
  the input's program and its optimisation (open: the premises about the base environment, the
  budget and the entry); `f_mem`/`f'_mem`: both functions exist.
-/

namespace Link.DeadCleanup.OptUnwindWitness

open E2E E2E.LinkCheck E2E.DeadCleanupBinary Backend Backend.Proof UnwindWitness

/-- `%rec` placed at 16 MiB with the size the cleanup pipeline compiles its optimisation to. -/
def specO : LinkSpec :=
  { spec with sizes := spec.opt.funcs.map fun fi =>
      (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size }

/-- The compiled optimised functions (`compileExeOpt`'s). -/
def artsO : List Art := (tabOf (parResultsCleanupT specO.opt.input0)).map (·.2)

/-- **The executable before the compiler**: the region's placeholder, the unwind sections of the
optimised functions, the link map's symbols. -/
def file0 : ByteArray :=
  exeWith specO.opt.R specO.opt.size
    [(hdrAddr, ehSegOf artsO hdrAddr gccAddr 0x2200000), (gccAddr, (gccOf artsO).1 ++ [0, 0, 0, 0])]
    (12 + 8 * artsO.length) (specO.opt.addrs.map fun p => (BinCheck.symName p.1, p.2))

theorem compile_ok : (compileExeOptU specO file0).toBool = true := by native_decide

/-- The executable. -/
def file : ByteArray := getOk (compileExeOptU specO file0)

/-- **The optimising executable compiler with the unwind tables checked compiles `%rec`.** -/
theorem compile_eq : compileExeOptU specO file0 = .ok file := getOk_eq compile_ok

/-- `%rec` of the input's program. -/
def f : Clif.Function := ((prog specO.inputCleanup).func? "rec").getD default

/-- Its optimisation. -/
def f' : Clif.Function := ((prog specO.opt.inputCleanup).func? "rec").getD default

theorem f_eq : (prog specO.inputCleanup).func? "rec" = some f := by
  have : ((prog specO.inputCleanup).func? "rec").isSome = true := by native_decide
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 this
  rw [hg, show f = g by simp [f, hg]]

theorem f'_eq : (prog specO.opt.inputCleanup).func? "rec" = some f' := by
  have : ((prog specO.opt.inputCleanup).func? "rec").isSome = true := by native_decide
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 this
  rw [hg, show f' = g by simp [f', hg]]

theorem f_mem : f ∈ (prog specO.inputCleanup).funcs := (Clif.Program.func?_some f_eq).1

theorem f'_mem : f' ∈ (prog specO.opt.inputCleanup).funcs := (Clif.Program.func?_some f'_eq).1

/-- The optimised code is non-empty. -/
theorem size_pos : 0 < (art specO.opt.inputCleanup f').fb.size := by native_decide

/-- **`compileExeOpt_correct_unwind`'s statement holds for `file`.** -/
theorem stmt : UnwindStmt specO.opt file := compileExeOpt_correct_unwind compile_eq

/-- **`compileExeOpt_correct_unwind_peak` applies to `file`** (open: the premises about the base
environment, the budget and the entry). -/
theorem peak_applies (B : BaseEnv) (F : BitVec 64 → Prop)
    (hB : BaseOk (LinkSys.ofInputCleanup specO.opt.inputCleanup B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup specO.opt.inputCleanup B F).Img a → F a)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup specO.opt.inputCleanup B F)
    (hb : BaseU L) (hNI : L.OkUNI) (hkeep : Opt.EnvKeepsSymbolsX L.envX)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) (d : Nat) {ra : BitVec 64}
    {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hent : AbiEntry (L.A f').fb (L.A f').base ra s) (hres : StackAvail (κ d f') (L.A f').af s)
    (hFw : L.F = frameWG (κ d f') (RAFrame.compute (L.A f').vcp (L.A f').rf).intBase
      (RAFrame.compute (L.A f').vcp (L.A f').rf).size (L.A f').af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f').af + κ d f') (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f').af s w₀) (hargs : ArgsIn f'.sig args s)
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry f' args cs')
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) (hsav : StackArgsAvoid L.Img f'.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f').af.slotBase,
      (RAFrame.compute (L.A f').vcp (L.A f').rf).intBase⟩ f' cs'.frame.slots cs'.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs'.mem (spv w₀))
    (hd : Clif.DepthLeX L.envX L.P d cs'.toX)
    (htr : ∀ Fu, TrapsExplicitX ((L.peakX Fu).envRX d f') L.P.bare cs') (k : Nat) :
    ArmRefinesU (L.A f').fb (L.A f').base ra (L.machU d f') s
      (Clif.runLoopX L.envX (prog specO.inputCleanup) k cs.toX) :=
  (compileExeOpt_correct_unwind_peak compile_eq B F hB hF L hLs hb hNI hkeep hκ f_eq f'_eq d
    hent hres hFw hgfree himg hbe hargs hcs hcs' hregs hsl hmem hsav hrel hpl hd htr k).2

end Link.DeadCleanup.OptUnwindWitness
