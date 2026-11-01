import FV.E2E.CallReturnPins
import FV.E2E.LinkArm
import FV.E2E.SemanticNIBoundary

/-! Additive whole-program proofs for actual validated output.
Uses the existing LinkSys, hooks, CLIF runs, machine, depth/peak budgets and
binary artifacts. Only the proof contract's compilation field is generalized;
all38 non-compilation input/layout/environment conditions and old theorem variants are
preserved. Actual raw Stock artifacts use the paired semantic interface. Existing production theorem variants remain available. -/
set_option autoImplicit false

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
open Clif Opt

namespace LinkSys
variable (L : LinkSys)

structure OkSemanticNI : Prop where
  /-- distinct names, no `return_call` -/
  names : (L.P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ L.P.funcs, Clif.LinkFree g
  subset : ∀ g ∈ L.P.funcs, InSubset L.P.bare g
  compiled : ∀ g ∈ L.P.funcs, CompiledSemanticNI g (L.A g).k (L.A g).vc (L.A g).vcp (L.A g).rf
    (L.A g).af (L.A g).fa (L.A g).fb
  covered : ∀ g ∈ L.P.funcs, FormsCovered ⟨(L.A g).fa.k, (L.A g).af.slotBase⟩ (L.A g).vcp
  /-- scope: the outgoing-argument area of a function holds the stack-passed arguments of the
  functions of `P` it declares (checked per declaration; vacuous for register-only signatures) -/
  outFits : ∀ g ∈ L.P.funcs, ∀ e ∈ g.externs.map (·.2), (L.P.func? e.name).isSome →
    ∀ (i off : Nat) (p : Clif.AbiParam), (locsOf e.sig)[i]? = some (ArgLoc.stack off) →
      e.sig.params[i]? = some p →
      off + p.ty.bytes ≤ (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase
  /-- the base externs create no allocation (needed only when a function of `P` has an
  outgoing-argument area: the callees' runs keep it free of live CLIF bytes) -/
  baseNoAlloc : (∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    NoAllocEnv L.base
  argRegs : ∀ g ∈ L.P.funcs, (regLocs g.sig).Nodup ∧ (∀ r ∈ regLocs g.sig, r.isArgReg = true) ∧
    ∀ p ∈ g.sig.params, p.ty.width ≤ 64
  /-- an `sret` function's returns carry its ABI results (the struct pointer: `lowerFunction`
  appends it to every `return`), checked on the compiled code -/
  sretRets : ∀ g ∈ L.P.funcs, g.sig.params.any (·.purpose == .sret) = true → ∀ us,
    (L.A g).vc.RetsSite us → (sigRets g.sig).length ≤ us.length
  /-- layout: a function called from `P` without stack slots has no slot region, and the slots
  of one with stack slots fit in its slot region (checked per function; the slot layout of
  `lowerFunction`) -/
  calleeFrame : ∀ g ∈ L.P.funcs, ∀ h, L.Callee g h → h.slots = [] →
    (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves
  slotFits : ∀ g ∈ L.P.funcs, ∀ h, L.Callee g h → ∀ p ∈ h.slots, ∃ off,
    (slotLayout h.slots).1.lookup p.1 = some off ∧
      (L.A h).af.slotBase + off + p.2.size ≤ (L.A h).af.frameSize - clobberBytes (L.A h).af.saves
  /-- scope: a call of a function `h` of `P` passes integer arguments in `h`'s parameter
  registers and takes its results from x0.. (those of its defs that are results: the defs past
  them are a `try_call`'s exception payload registers; checked per call site) -/
  callRegs : ∀ g ∈ L.P.funcs, ∀ info h, L.ProgSite g info h →
    ∃ n Lu Ld, info = ⟨.sym n, retPairs Lu, callDefs Ld⟩ ∧ Lu.map (·.2) = regLocs h.sig ∧
      (Ld.map (·.1)).take (sigRets h.sig).length =
        (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x
  /-- scope: a `blr` call site (an indirect call, or a call through the GOT) passes integer
  arguments in the parameter registers of every function of `P` it may enter (`BlrTo`: one its
  function may reach, `MayCall`; at a call through the GOT only the GOT symbol's function, none
  for a base extern) that has as many register parameters, and takes the results its defs hold
  from x0.. (a site with fewer defs than that function's results constrains nothing more; checked
  per site; vacuous without `blr` sites) -/
  blrRegs : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → (∀ n, info.dest ≠ .sym n) →
    ∃ t Lu Ld, info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      ∀ h ∈ L.P.funcs, L.BlrTo g t h → (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x
  /-- layout: the return address of a `blr` is not in the code of a function of `P` it may call
  (`MayCall`), or is after a call instruction of that function's code, not at its entry
  (`RaOk`: functions sharing one copy of code) -/
  raBlr : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → (∀ n, info.dest ≠ .sym n) →
    ∀ h ∈ L.P.funcs, L.MayCall g h.name → ∀ pc, CallPc (L.A g).fa (L.A g).base pc →
      RaOk (L.A h) pc
  /-- scope of the indirect calls (`call_indirect`, `try_call_indirect`; vacuous without them):
  the base externs keep the symbols and distinct names of `P` and of the base environment have
  distinct addresses (`Clif.IndScope`) -/
  indScope : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g → Clif.IndScope L.P L.base L.syms
  /-- the functions `g` may reach whose signature one of its indirect calls matches
  (`IndSigMatch`: parameter types and purposes, return types; the whole-program run enters no
  other, `Clif.stepCallIndirect`), or, for a function `g` declares (which the per-function run
  may enter through any pointer to it), whose parameter types one of them has (`IndTyMatch`),
  take their arguments in registers (an `sret` pointer in x8), and an indirect call of `g` with
  their parameter types and as many declared returns has as many ABI returns (`sigRets`: both
  or neither pass an `sret` pointer) -/
  indSig : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g →
    ∀ h ∈ L.P.funcs, L.MayCall g h.name → ((∃ sig ∈ indSigs g, IndSigMatch sig h) ∨
      (DeclN g h.name ∧ ∃ sig ∈ indSigs g, IndTyMatch sig h)) →
      (∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8) ∧
      ∀ sig ∈ indSigs g, IndTyMatch sig h → h.sig.returns.length = sig.returns.length →
        (sigRets h.sig).length = (sigRets sig).length
  /-- when no program callee has stack slots (`NeedSlots` fails: the slot-placement oracle is
  not in play), a function of `P` has an outgoing-argument area and one has indirect calls, the
  functions with an address have no stack slots (an indirect call enters no slotted function);
  with `NeedSlots` the runs' allocations are the base's to keep (`baseKeepsAllocs`) -/
  addrSlots : ¬ L.NeedSlots → (∃ g ∈ L.P.funcs, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase ≠ 0) →
    (∃ g ∈ L.P.funcs, ¬ Clif.IndFree g) → ∀ h ∈ L.P.funcs, L.syms h.name ≠ none → h.slots = []
  /-- the link-time address of a function of `P` is no other symbol's -/
  symInj : ∀ h ∈ L.P.funcs, ∀ n, L.Xb.sym h.name 0 = L.Xb.sym n 0 → n = h.name
  /-- the declarations of the program's functions are their definitions' signatures -/
  declSig : ∀ g ∈ L.P.funcs, ∀ e ∈ g.externs.map (·.2), ∀ h, L.P.func? e.name = some h → e.sig = h.sig
  /-- the entry `Args` reads parameter registers -/
  entryRegs : ∀ g ∈ L.P.funcs, ∀ r, (L.A g).vcp.EntryArg r → r ∈ regLocs g.sig
  /-- layout: every function's words fit at its base -/
  fits : ∀ g ∈ L.P.funcs, (L.A g).base.toNat + 4 * (L.A g).fb.words.size ≤ 2 ^ 64
  /-- layout: the code image (`Img`, holding `imgMem`) contains every function's words -/
  imgAddr : ∀ g ∈ L.P.funcs, ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default
    ((L.A g).fb.program (L.A g).base)) a → L.Img a
  imgCode : ∀ g ∈ L.P.funcs, ∀ t : Arm.ArmState, (∀ a, L.Img a → t.mem a = L.imgMem a) →
    ∀ k w, (L.A g).fb.words[k]? = some w →
      Arm.read_mem_bytes 4 ((L.A g).base + BitVec.ofNat 64 (4 * k)) t = w
  /-- the code is outside every activation's world -/
  imgF : ∀ a, L.Img a → L.F a
  /-- layout: the return address of a call is not in the code of a function of `P` that `g`
  calls, or is after a call instruction of that function's code, not at its entry (`RaOk`;
  stated for the callees of `g`'s call sites, not for every function of `P`: the return address
  is in `g`'s own code, so a native recursive callee or a callee sharing `g`'s code
  takes the second case) -/
  raCall : ∀ g ∈ L.P.funcs, ∀ info h, L.ProgSite g info h → ∀ pc, CallPc (L.A g).fa (L.A g).base pc →
    RaOk (L.A h) pc
  raStar : ∀ h ∈ L.P.funcs, ∀ k < (L.A h).fb.words.size,
    L.raStar ≠ (L.A h).base + BitVec.ofNat 64 (4 * k)
  /-- the stack of one call level -/
  depth : ∀ g ∈ L.P.funcs, frameDrop (L.A g).af ≤ L.D
  /-- the base environment: symbols, the contracts of the calls outside `P` (at the program's
  call sites), the CLIF contract of the base externs, TLS -/
  symOk : ∀ n b, L.syms n = some b → L.Xb.sym n 0 = BitVec.ofNat 64 b
  baseOs : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → L.BaseDest (destOf info) →
    ∀ F K G s0 Pc ctx, CallSoundCtlG F K G s0 Pc (callExec L.Hb) (csem F ctx L.Xb) (.call info) .next
  basePc : ∀ d s, L.BaseDest d → Arm.r .ERR s = .None → Arm.CheckSPAlignment s →
    Arm.r .PC (L.Hb.call d s) = Arm.r .PC s + 4
  baseExt : ∀ d uses w outs w', L.BaseDest d → L.Xb.call d uses w = some (outs, w') →
    Arm.r .ERR w = .None → Arm.r .ERR w' = .None ∧ w'.program = w.program
  baseX : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XCallsOk L.base
    ((g.externs.map (·.2)).filter fun e => (L.P.func? e.name).isNone)
    (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  /-- the indirect calls of `g` that reach an extern outside `P`, whatever the call-site
  signature (`sigOf` erased: the linked environment knows only the signatures of `P`'s
  functions, `Clif.linkEnvN`; vacuous without indirect calls) -/
  baseXI : ∀ g ∈ L.P.funcs, ∀ F slotOff out c, XCallsIndOk { L.base with sigOf := fun _ => none }
    (indSigs g) (RelW ⟨F, L.syms, slotOff, out⟩ g c) L.Xb
  baseTls : ∀ g ∈ L.P.funcs, hasTls g = true → ∀ F K, TlsOk F K L.Xb L.Hb
  /-- the results of a `try_call` of an extern outside `P` (normal return; vacuous without such
  `try_call`s) -/
  baseTry : ∀ g ∈ L.P.funcs, ∀ F, CalleeTryOk F L.Xb L.Hb
    fun info ti => (L.A g).vcp.TrySite info ti ∧ L.BaseDest (destOf info)
  /-- **non-interference of the base externs** (needed only when a program callee has an
  outgoing-argument area or a slot region): a returning call of an extern outside `P`, pinned to
  its CLIF call, from two worlds that agree outside `Z ⊇ F`, related to the same CLIF memory, with
  the same stack pointer and the same argument bytes, gives the same results and worlds that agree
  outside `Z` -/
  baseNI : L.NeedNI → ∀ g ∈ L.P.funcs, ∀ F c, XNI F L.syms (g.externs.map (·.2)) (indSigs g) c
    (fun n sig vals cm => L.P.func? n = none ∧
      CallLg L.base (g.externs.map (·.2)) (indSigs g) n sig vals cm) L.Xb
  /-- the TLSDESC flags do not depend on the world outside `F` (needed only when a program
  callee has an outgoing-argument area) -/
  baseTlsNI : L.NeedNI → ∀ F, XTls F L.Xb
  /-- the base externs keep the slot-placement oracle and create no allocation (needed only when
  a program callee has stack slots) -/
  baseKeepsPlace : L.NeedSlots → Clif.EnvKeepsPlace L.base
  baseKeepsAllocs : L.NeedSlots → Clif.EnvKeepsAllocs L.base


/-- Every retained legacy system is an instance with the same actual artifacts. -/
theorem Ok.toSemanticNI {L : LinkSys} (h : L.Ok) : L.OkSemanticNI where
  names := h.names
  free := h.free
  subset := h.subset
  compiled := fun g hg => .compatible (.legacy (h.compiled g hg))
  covered := h.covered
  outFits := h.outFits
  baseNoAlloc := h.baseNoAlloc
  argRegs := h.argRegs
  sretRets := h.sretRets
  calleeFrame := h.calleeFrame
  slotFits := h.slotFits
  callRegs := h.callRegs
  blrRegs := h.blrRegs
  raBlr := h.raBlr
  indScope := h.indScope
  indSig := h.indSig
  addrSlots := h.addrSlots
  symInj := h.symInj
  declSig := h.declSig
  entryRegs := h.entryRegs
  fits := h.fits
  imgAddr := h.imgAddr
  imgCode := h.imgCode
  imgF := h.imgF
  raCall := h.raCall
  raStar := h.raStar
  depth := h.depth
  symOk := h.symOk
  baseOs := h.baseOs
  basePc := h.basePc
  baseExt := h.baseExt
  baseX := h.baseX
  baseXI := h.baseXI
  baseTls := h.baseTls
  baseTry := h.baseTry
  baseNI := h.baseNI
  baseTlsNI := h.baseTlsNI
  baseKeepsPlace := h.baseKeepsPlace
  baseKeepsAllocs := h.baseKeepsAllocs

end LinkSys

end E2E
