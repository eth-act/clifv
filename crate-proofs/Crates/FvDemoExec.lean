import Crates.FvDemo
import FV.E2E.SemanticExecProven

/-! # `fv-demo`: the theorem about the executable's own words

`E2E.ExecBytes.binary_correct_exec_proven` (L3) for the `fv-demo` executable of `Crates.FvDemo`:
besides that file's checks (`okB_input`, `bin_ok`), the two per-program checks of the executable
machine, by `native_decide` on the same input and excerpts:

* the code map (`codeMap_ok`, `codeMapB`): `fv-demo`'s self-recursive `…punLyx` has the
  self-call alias `…punLyx__fvself` (`cargo fv`), a function of the program on `…punLyx`'s code
  (the same load address, lines alike: the self-call is `bl …punLyx__fvself` in one and
  `bl …punLyx` in the other, a call of the program in both) with a fresh link-map address that no
  `blr` of the program reaches (`noBlrB`: the alias is no CLIF image symbol, and `…punLyx`, which
  declares it, calls through registers only through the GOT entries of other symbols);
* the GOT (`gotB_ok`, `gotB`): every GOT pair's slot is loaded, `ro`/`relro` and no relocated
  instruction byte.

`binary_correct_exec` is `binary_correct_exec_proven` for every file agreeing with the excerpts
`exAll`: the premises left are those about the base environment and the outside caller.
-/

namespace Crates.FvDemo

open E2E E2E.LinkCheck E2E.SemanticBinary E2E.BinCheck E2E.SemanticExecBytes

/-- The code map check of the executable's program (`codeMapB`). -/
theorem codeMap_ok : codeMapB input (tabOf actualResults) = true := by native_decide

/-- The GOT check of the executable's program on the proof's excerpts (`gotB`). -/
theorem gotB_ok : gotB compilerInput exAll = true := by native_decide

/-- **`binary_correct_exec_proven` for `fv-demo`**: for every file agreeing with the excerpts,
under the base environment's premises (`BaseOk`, `HooksSim`) and those of the outside call, the
executable machine run from `r` refines the whole-program CLIF run of an entry whose calls reach no
call cycle. -/
theorem binary_correct_exec (file : ByteArray) (hfile : Elf.Agrees file exAll) (B : BaseEnv)
    (hB : BaseOk (sys compilerInput B)) (hH : HooksSim compilerInput B) {n : String} {f : Clif.Function}
    (hf : (prog compilerInput).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls compilerInput compilerInput.results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall compilerInput (BinCheck.roByte compilerInput dataObjs) f (SemanticStackBound.stackFn compilerInput f) r args
      cs.mem)
    (hav : OutsideAvoids (GotSlot compilerInput file) f (SemanticStackBound.stackFn compilerInput f) r args cs.mem)
    (hr : ClifRun compilerInput B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog compilerInput) B.env M) (prog compilerInput).bare cs) :
    ExecRefines (art compilerInput f).fb (art compilerInput f).base (xreg 30 r) (step compilerInput B file) r
      (BinCheck.RelocAtWithResults compilerInput actualResults) (Clif.runLoop B.env (prog compilerInput) (M + 1) cs) :=
  binary_correct_exec_proven okB_input codeMap_ok (bin_ok file hfile) (gotB_sound gotB_ok hfile) B
    hB hH hf hc M hX ho hav hr htr

end Crates.FvDemo
