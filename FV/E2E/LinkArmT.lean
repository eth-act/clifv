import FV.E2E.LinkArm
import FV.E2E.CompiledEitherT
import FV.E2E.CompiledAnyTS
import FV.E2E.LinkSiteTC
import FV.E2E.TypedRulesProg
import FV.E2E.LinkWorldT

/-! # The typed link layer (S11e5 Stage C, slice 8)

Typed copies of the declarations of `FV/E2E/LinkArm.lean` that depend on the integer link
contract, for the typed contract `LinkSys.OkT` (names with suffix `T`; `LinkSys.Ok.*` as
`LinkSys.OkT.*`):

* `LinkSys.OkT`: `LinkSys.Ok` with the typed subset `InSubsetT` and the typed artifact contract
  `CompiledEitherT` per function, and two fields for the program callees: an `sret` function is
  in subset E with the integer contract, or its artifact returns in their `retX` registers
  (`sretE`, `RetsX`: its returned struct pointer is in x8, #587), and a function of `P` called
  from `P` returns integers (`calleeInt`);
* `LinkSys.ThmT`: `LinkSys.Thm` whose returns are in the ABI return registers of their classes
  (`RetsOkT`: `RetRegsOk`, and `RetPins` for an `sret` function); a call site of `P` reads an
  integer callee's results from their ABI return registers (`RetsOkT.x_at`, `retX`);
* `thm_ofT`/`thmT`: the induction with the typed world theorems
  (`backend_correct_world_ni_pipelineT` with the proven control families
  `E2E.typedRules_program`; the integer one for an `sret` function), and
  `backend_correct_program*T` with the class-aware conclusion `ArmRefinesT`. -/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck

/-- `hasTls_of_vcode_pipeline` for `CompiledEitherT`. -/
theorem hasTls_of_vcode_pipelineT {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hc : CompiledEitherT f k vc vcp rf af fa fb) (ht : vcp.hasTls = true) : hasTls f = true := by
  cases hc with
  | legacy hc => exact hasTls_of_vcodeAT hc.toA ht
  | cleanup hc => exact hasTls_of_vcodeCleanupAT hc.toA ht

/-- **The returns of `g` in the typed linking statement**: in the ABI return registers of their
classes (`RetRegsOk`), and, for an `sret` function, the returned registers are pinned by
`RetPins` (its struct pointer in x8, as in Cranelift, #587; before #587 this said x0, x1, …,
which the compiler no longer produces). -/
def RetsOkT (g : Clif.Function) (rvals : List Clif.Val) (us : List (Reg × Reg)) : Prop :=
  RetRegsOk rvals us ∧ (g.sig.params.any (·.purpose == .sret) = true → RetPins rvals us)

/-- The `j`-th returned register of a declared return is its class's return register
(`RetRegsOk`: `retRegsT` of the returned values' classes first). -/
theorem RetRegsOk.getElem? {rvals : List Clif.Val} {us : List (Reg × Reg)}
    (h : RetRegsOk rvals us) {j : Nat} (hj : j < rvals.length) :
    (us.map (·.2))[j]? = (retRegsT (rvals.map fun v => tyClass v.ty) 0 0)[j]? := by
  obtain ⟨cs, hcs⟩ := h
  rw [hcs, List.take_left' (by simp),
    List.getElem?_append_left (by simp [retRegsT_length]; omega)]

/-- **A call site reads an integer callee's `j`-th result from its ABI return register**
(`retX`: x`j` for a declared return, x8 for an `sret` callee's struct pointer): the callee's
returns (`RetsOkT`) of its declared (integer) return types. -/
theorem RetsOkT.x_at {h : Clif.Function} {rvals : List Clif.Val} {us : List (Reg × Reg)}
    (hus : RetsOkT h rvals us) (hrt : rvals.map (·.ty) = Clif.AbiParam.tys h.sig.returns)
    (hint : ∀ p ∈ h.sig.returns, p.ty.isInt = true) {j : Nat} (hj : j < (sigRets h.sig).length)
    (hju : j < us.length) : us[j]? = some ((us[j]'hju).1, retX h.sig.returns.length j) := by
  have hlen : rvals.length = h.sig.returns.length := by
    have := congrArg List.length hrt
    simpa [Clif.AbiParam.tys] using this
  have hx : (us.map (·.2))[j]? = some (retX h.sig.returns.length j) := by
    cases hsr : h.sig.params.any (·.purpose == .sret) with
    | true =>
      have hp := hus.2 hsr
      unfold RetPins at hp
      rw [hp, List.getElem?_map, List.getElem?_range hju, hlen]; rfl
    | false =>
      rw [sigRets_of_noSret hsr] at hj
      rw [retX_lt hj]
      have hint' : ∀ v ∈ rvals, v.ty.isInt = true := by
        intro v hv
        have hm : v.ty ∈ Clif.AbiParam.tys h.sig.returns := hrt ▸ List.mem_map_of_mem hv
        obtain ⟨q, hq, hqt⟩ := List.mem_map.mp hm
        rw [← hqt]
        exact hint q hq
      rw [RetRegsOk.getElem? hus.1 (by omega), classes_int hint', retRegsT_int, List.getElem?_map,
        List.getElem?_range' (by omega)]
      simp
  rw [List.getElem?_map, List.getElem?_eq_getElem hju] at hx
  simp only [Option.map_some, Option.some.injEq] at hx
  rw [List.getElem?_eq_getElem hju, ← hx]

/-- **A call site reads the callee's `j`-th declared result from its return register by class**
(`sigRetRegs`, #742): the callee's returns (`RetsOkT`) of its declared return types. Over the
declared returns since #587 (`hj`): the struct pointer of an `sret` callee is returned in x8
(`RetPins`), not in `sigRetRegs`' x0, and is no call result; the pre-#587 statement over
`sigRets` became false for it. -/
theorem RetsOkT.reg_at {h : Clif.Function} {rvals : List Clif.Val} {us : List (Reg × Reg)}
    (hus : RetsOkT h rvals us) (hrt : rvals.map (·.ty) = Clif.AbiParam.tys h.sig.returns)
    {j : Nat} (hj : j < h.sig.returns.length) (hju : j < us.length) {r : Reg}
    (hr : (sigRetRegs h.sig)[j]? = some r) :
    us[j]? = some ((us[j]'hju).1, r) := by
  suffices hx : (us.map (·.2))[j]? = (sigRetRegs h.sig)[j]? by
    rw [List.getElem?_map, List.getElem?_eq_getElem hju, hr] at hx
    simp only [Option.map_some, Option.some.injEq] at hx
    rw [List.getElem?_eq_getElem hju, ← hx]
  have hd : (sigRetRegs h.sig)[j]? = (declRetRegs h.sig)[j]? := by
    rw [declRetRegs_eq_take, List.getElem?_take, if_pos hj]
  rw [hd]
  have hcl : rvals.map (fun v => tyClass v.ty) = h.sig.returns.map fun p => tyClass p.ty := by
    have := congrArg (List.map tyClass) hrt
    simpa [Clif.AbiParam.tys, List.map_map, Function.comp_def] using this
  have hlen : rvals.length = h.sig.returns.length := by
    have := congrArg List.length hrt
    simpa [Clif.AbiParam.tys] using this
  rw [RetRegsOk.getElem? hus.1 (by omega), hcl, declRetRegs]

namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

open Classical in
/-- **A call of the function `g` of `P` at depth `M`, class-aware** (#742): `progX` with the
results (one per declared return, #587: an `sret` callee's struct pointer is no call result)
read from `g`'s return registers by class (`declRetRegs`: x0.. and v0..) instead of x0... -/
noncomputable def progXT (κ : Nat → Clif.Function → Nat) (M : Nat) (F : BitVec 64 → Prop)
    (g : Clif.Function) (uses : List CV) (w : Arm.ArmState) : Option (List CV × Arm.ArmState) :=
  if L.Cond κ M F g uses w ∧ Arm.r .ERR (L.pcall M g (L.canon g uses w)) = .None then
    some ((declRetRegs g.sig).map fun r => regVal (L.pcall M g (L.canon g uses w)) r,
      L.pcall M g (L.canon g uses w))
  else none

open Classical in
/-- **The external semantics of an activation of `g` at depth `M` in the typed link** (#742):
`X` with the class-aware calls of the functions of `P` (`progXT`). -/
noncomputable def XT (κ : Nat → Clif.Function → Nat) (M : Nat) (g : Clif.Function)
    (F : BitVec 64 → Prop) : ExtSem where
  call d uses w := match d with
    | some n => (match L.P.func? n with
      | some h => L.progXT κ M F h uses w
      | none => L.Xb.call d uses w)
    | none => (match uses with
      | u :: args => (match symCallee L.Xb L.P (lo64 u) with
        | some h => if L.IndTo g h ∧ args.length = (regLocs h.sig).length then
            L.progXT κ M F h args w else none
        | none => L.Xb.call none uses w)
      | [] => L.Xb.call none uses w)
  sym := L.Xb.sym
  tp := L.Xb.tp
  tlsFlags := L.Xb.tlsFlags

theorem XT_base {M : Nat} {g : Clif.Function} {n : String} (hn : L.P.func? n = none)
    (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.XT κ M g F).call (some n) uses w = L.Xb.call (some n) uses w := by
  simp [XT, hn]

theorem XT_prog {M : Nat} {g : Clif.Function} {n : String} {h : Clif.Function}
    (hpf : L.P.func? n = some h) (uses : List CV) (w : Arm.ArmState) (F : BitVec 64 → Prop) :
    (L.XT κ M g F).call (some n) uses w = L.progXT κ M F h uses w := by
  simp [XT, hpf]

theorem XT_none {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState} (hn : symCallee L.Xb L.P (lo64 u) = none) :
    (L.XT κ M g F).call none (u :: args) w = L.Xb.call none (u :: args) w := by
  simp [XT, hn]

open Classical in
theorem XT_ind {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {u : CV} {args : List CV}
    {w : Arm.ArmState}
    {h : Clif.Function} (hs : symCallee L.Xb L.P (lo64 u) = some h) :
    (L.XT κ M g F).call none (u :: args) w = if L.IndTo g h ∧ args.length = (regLocs h.sig).length
      then L.progXT κ M F h args w else none := by
  simp only [XT, hs]

theorem progXT_ext {M : Nat} {F : BitVec 64 → Prop} {h : Clif.Function}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : L.progXT κ M F h uses w = some (outs, w')) :
    Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  unfold progXT at hx
  split at hx
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    exact ⟨hc.2, by rw [(L.pcall_pc M h _).1, L.program_canon]⟩
  · cases hx

theorem tlsOk_hooksT {F F' : BitVec 64 → Prop} {K M : Nat} {g : Clif.Function}
    (h : TlsOk F K L.Xb L.Hb) : TlsOk F K (L.XT κ M g F') (L.hooks M) := by
  cases M <;> exact ⟨h.pc, h.seq, h.flags⟩

/-- The number of ABI returns of a signature (`sigRets`): the struct pointer of an `sret`
signature without returns, else its returns. -/
theorem sigRets_length_eq (s : Clif.Signature) : (sigRets s).length =
    if (s.params.any (·.purpose == .sret) && s.returns.isEmpty) then 1 else s.returns.length := by
  cases hs : s.params.any (·.purpose == .sret) with
  | false => simp [sigRets_of_noSret hs]
  | true =>
    rw [sigRets_of_sret hs]
    cases he : s.returns.isEmpty <;> simp

/-- **An indirect call entering `h` has as many ABI returns as `h`** (`IndSigMatch`: the same
parameter purposes, so both or neither pass an `sret` pointer, and as many returns). -/
theorem IndSigMatch.sigRets_length {sig : Clif.Signature} {h : Clif.Function}
    (hm : IndSigMatch sig h) : (sigRets h.sig).length = (sigRets sig).length := by
  obtain ⟨-, hp, -⟩ := Clif.Signature.abiMatch_eq_true.mp hm
  have hany : h.sig.params.any (·.purpose == .sret) = sig.params.any (·.purpose == .sret) := by
    have := congrArg (fun l => l.any (· == .sret)) hp
    simpa [Clif.AbiParam.purposes, List.any_map, Function.comp_def] using this.symm
  have hlen : h.sig.returns.length = sig.returns.length := hm.returns_length
  have he : h.sig.returns.isEmpty = sig.returns.isEmpty := by
    rw [Bool.eq_iff_iff, List.isEmpty_iff, List.isEmpty_iff, ← List.length_eq_zero_iff,
      ← List.length_eq_zero_iff, hlen]
  rw [sigRets_length_eq, sigRets_length_eq, hany, he, hlen]
end LinkSys
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The premises of the typed linked program** (`backend_correct_programT`): `Ok` with the
typed subset `InSubsetT` and the typed artifact contract `CompiledEitherT`, an `sret` function
in subset E with the integer contract or returning in x0.. (`sretE`), and class-aware program
call sites (`callRegs`, `blrRegs`, #742: arguments and results of either class in their ABI
registers; it had `calleeInt`, integer returns of the functions of `P` called from `P`). -/
structure OkT : Prop where
  /-- distinct names, no `return_call` -/
  names : (L.P.funcs.map (·.name)).Nodup
  free : ∀ g ∈ L.P.funcs, Clif.LinkFree g
  /-- S11f (#35): the scope with the proven float operations (it was `InSubsetTC`,
  `InSubsetTC.toTCF`) -/
  subset : ∀ g ∈ L.P.funcs, InSubsetTCF L.P.bare g
  /-- #722: either typed artifact, or the Stock artifact of an integer function without `sret`
  parameter (`CompiledAnyTS`; it was `CompiledAnyT`, its left case) -/
  compiled : ∀ g ∈ L.P.funcs, CompiledAnyTS L.P.bare g (L.A g).k (L.A g).vc (L.A g).vcp
    (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb
  /-- an `sret` function is in subset E, with the integer artifact contract, or (#722) its
  artifact's returns are in their `retX` registers (`RetsX`: the integer results in x0.., the
  struct pointer in x8 (#587), for any typed artifact) -/
  sretE : ∀ g ∈ L.P.funcs, g.sig.params.any (·.purpose == .sret) = true →
    (InSubset L.P.bare g ∧ CompiledEither g (L.A g).k (L.A g).vc (L.A g).vcp (L.A g).rf
      (L.A g).af (L.A g).fa (L.A g).fb) ∨ RetsX g.sig.returns.length (L.A g).vc
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
  /-- scope: a call of a function `h` of `P` passes its arguments (of either class) in `h`'s
  parameter registers and takes its results from `h`'s return registers by class (`sigRetRegs`:
  those of its defs that are results; the defs past them are a `try_call`'s exception payload
  registers; checked per call site; #742: it had integer vregs and x0..) -/
  callRegs : ∀ g ∈ L.P.funcs, ∀ info h, L.ProgSite g info h →
    ∃ n Lc Dc, info = ⟨.sym n, argPairsC Lc, callDefsC Dc⟩ ∧ Lc.map (·.2.2) = regLocs h.sig ∧
      (Dc.map (·.1)).take (sigRets h.sig).length = (sigRetRegs h.sig).take Dc.length
  /-- scope: a `blr` call site (an indirect call, or a call through the GOT) passes its arguments
  in the parameter registers of every function of `P` it may enter (`BlrTo`: one its function
  may reach, `MayCall`; at a call through the GOT only the GOT symbol's function, none for a base
  extern) that has as many register parameters, and takes the results its defs hold from that
  function's return registers by class (a site with fewer defs than that function's results
  constrains nothing more; checked per site; vacuous without `blr` sites; #742: it had integer
  vregs and x0.., or no function of `P` entered) -/
  blrRegs : ∀ g ∈ L.P.funcs, ∀ info, (L.A g).vcp.CallSite info → (∀ n, info.dest ≠ .sym n) →
    ∃ t Lc Dc, info = ⟨.reg (.vreg t .int), argPairsC Lc, callDefsC Dc⟩ ∧
      ∀ h ∈ L.P.funcs, L.BlrTo g t h → (regLocs h.sig).length = Lc.length →
        Lc.map (·.2.2) = regLocs h.sig ∧
        (Dc.map (·.1)).take (sigRets h.sig).length = (sigRetRegs h.sig).take Dc.length
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
  take their arguments in registers (an `sret` pointer in x8) (#742: it also had, for every
  indirect call of `g` with their parameter types and as many declared returns, as many ABI
  returns; `IndSigMatch` gives that, `IndSigMatch.sigRets_length`) -/
  indSig : ∀ g ∈ L.P.funcs, ¬ Clif.IndFree g →
    ∀ h ∈ L.P.funcs, L.MayCall g h.name → ((∃ sig ∈ indSigs g, IndSigMatch sig h) ∨
      (DeclN g h.name ∧ ∃ sig ∈ indSigs g, IndTyMatch sig h)) →
      ∃ bytes, sigParamBytes h.sig = .ok bytes ∧ bytes.length ≤ 8
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

/-- **The integer `blr` facts give `OkT.blrRegs`** when the functions of `P` the site may enter
return integers (`sigRetRegs` is x0..; a site entering no function of `P` constrains nothing). -/
theorem blrRegsC_of_int {g : Clif.Function} {info : CallInfo}
    (hint : ∀ t, ∀ h ∈ L.P.funcs, L.BlrTo g t h → ∀ p ∈ h.sig.returns, p.ty.isInt = true)
    (hb : (∃ t Lu Ld, info = ⟨.reg (.vreg t .int), retPairs Lu, callDefs Ld⟩ ∧
      ∀ h ∈ L.P.funcs, L.BlrTo g t h → (regLocs h.sig).length = Lu.length →
        Lu.map (·.2) = regLocs h.sig ∧
        (Ld.map (·.1)).take (sigRets h.sig).length =
          (List.range (min (sigRets h.sig).length Ld.length)).map Reg.x) ∨
      (∃ t Lc Dc, info = ⟨.reg (.vreg t .int), argPairsC Lc, callDefsC Dc⟩ ∧
        ∀ h ∈ L.P.funcs, ¬ L.BlrTo g t h)) :
    ∃ t Lc Dc, info = ⟨.reg (.vreg t .int), argPairsC Lc, callDefsC Dc⟩ ∧
      ∀ h ∈ L.P.funcs, L.BlrTo g t h → (regLocs h.sig).length = Lc.length →
        Lc.map (·.2.2) = regLocs h.sig ∧
        (Dc.map (·.1)).take (sigRets h.sig).length = (sigRetRegs h.sig).take Dc.length := by
  rcases hb with ⟨t, Lu, Ld, rfl, hall⟩ | ⟨t, Lc, Dc, rfl, hno⟩
  · refine ⟨t, _, _, by rw [retPairs_eq_argPairsC, callDefs_eq_callDefsC], fun h hh hbt hl => ?_⟩
    obtain ⟨h1, h2⟩ := hall h hh hbt (by simpa using hl)
    exact siteRegsC_of_int (hint t h hh hbt) h1 h2
  · exact ⟨t, Lc, Dc, rfl, fun h hh hbt => absurd hbt (hno h hh)⟩

/-- **The linking statement at depth `M`**: for every function `g` of `P` and every world-side
activation (addresses `F` outside its world) whose run of the program without functions
(`P.bare`: every program callee, `g` included, an atomic whole-program run of at most `M` steps)
returns, one VCode outcome that every machine-side activation at depth `M`
realises, and (when the linking needs non-interference, `NeedNI`) that every machine-side
activation entered with a body-entry world related to the same CLIF entry, agreeing outside
`F ∪ D` (with the same argument registers and stack-passed argument bytes), realises up to
`F ∪ D`; no state of the run before the return but the entry is at an address after a call of
`g`'s code with the entry `sp` (`PostTrace`). -/
def ThmT (κ : Nat → Clif.Function → Nat) (M : Nat) : Prop :=
  ∀ g ∈ L.P.funcs, ∀ (F : BitVec 64 → Prop) (vals : List Clif.Val) (cs : Clif.State)
    (w₀ : Arm.ArmState) (fuel : Nat)
    (rvals : List Clif.Val) (cm' : Clif.Mem), L.WorldEntry κ M g F vals cs w₀ →
    Clif.runLoop (L.envR M g) L.P.bare fuel cs = .returned rvals cm' →
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      RetsOkT g rvals us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A g).vc.RetsSite us ∧
      (∀ G ra s, L.MachEntry κ M g F G ra s w₀ →
        ∃ n, ActRet ra F G us outs wf s (runX (L.mach M g) n s) ∧
          PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n) ∧
      (L.NeedNI → ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
        RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
          g (spv w₀) cs.frame.slots cs.mem w₀' →
        SameWorld (fun a => F a ∨ D a) w₀ w₀' →
        (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf g.sig).zip vals → regVal w₀' r = regVal w₀ r) →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf g.sig).zip vals → ∀ k < v.ty.bytes,
          w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
            w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
        ∀ G ra s, L.MachEntry κ M g F G ra s w₀' →
          ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs wf s (runX (L.mach M g) n s) ∧
            PostTrace (L.A g).fa (L.A g).af (L.A g).base (L.mach M g) s n)
end LinkSys
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem callerOk_canonT (hL : L.OkT) {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (uses : List CV)
    (w : Arm.ArmState) : L.CallerOk F g uses w (L.canon g uses w) := by
  have harg := (hL.argRegs g hg).2.1
  refine ⟨⟨fun f hf => L.r_canon harg uses w hf, fun a ha => ?_, L.program_canon g uses w⟩,
    fun a ha => ?_, fun _ _ => rfl, .inl fun k hk => ?_⟩
  · rw [L.mem_canon, mem_withImg, if_neg (fun hi => ha (himgF a hi))]
  · rw [L.mem_canon, mem_withImg, if_pos ha]
  · simp only [canon, Arm.r_of_w_same, BitVec.sub_add_cancel]
    exact hL.raStar g hg k hk
end LinkSys
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- The body-entry world of the canonical call agrees with a compatible caller's callee entry. -/
theorem bodyEntryW_compatT (hL : L.OkT) {h : Clif.Function} (hh : h ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {uses : List CV}
    {w t : Arm.ArmState} (ht : L.CallerOk F h uses w t) :
    BodyEntryW F (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t)
      (bodyOf (L.A h).af (enterAt (L.A h) (L.canon h uses w))) := by
  have harg := (hL.argRegs h hh).2.1
  have hc := L.callerOk_canonT hL hh himgF uses w
  have hsp : spv (enterAt (L.A h) (L.canon h uses w)) = spv (enterAt (L.A h) t) := by
    rw [spv_enterAt, spv_enterAt]; simp only [spv]
    rw [hc.world.1 _ (by simp [Masked]), ht.world.1 _ (by simp [Masked])]
  have h29 : xreg 29 (enterAt (L.A h) (L.canon h uses w)) = xreg 29 (enterAt (L.A h) t) := by
    simp only [xreg]
    rw [r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
      hc.world.1 _ (by simp [Masked]), ht.world.1 _ (by simp [Masked])]
  refine ⟨by rw [spv_bodyOf, hsp], by rw [x29_bodyOf, hsp, h29], fun r hr => ?_, fun f hf h29' h31 => ?_,
    fun a ha => ?_, by simp⟩
  · have hra := harg r (hL.entryRegs h hh r hr)
    rw [regVal_bodyOf _ _ hra, regVal_enterAt _ _ hra, regVal_enterAt _ _ hra,
      ht.regs r (hL.entryRegs h hh r hr)]
  · have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
    have h30 : f ≠ .GPR 30#5 := by rintro rfl; exact hf (by simp [Masked])
    rw [r_bodyOf _ _ h29' h31, r_enterAt _ _ hpc h30, r_enterAt _ _ hpc h30,
      hc.world.1 f hf, ht.world.1 f hf]
  · rw [mem_bodyOf, mem_enterAt, mem_enterAt, hc.world.2.1 a ha, ht.world.2.1 a ha]
end LinkSys
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem frameSize_modT (hL : L.OkT) {h : Clif.Function} (hh : h ∈ L.P.funcs) :
    (L.A h).af.frameSize % 16 = 0 := by
  rw [(lowerRFunc_ok (hL.compiled h hh).alloc).1.1]
  have h1 := compute_saveBase (L.A h).vcp (L.A h).rf
  have h2 := clobberBytes_mod (L.A h).rf.saved
  omega

theorem frameDrop_eqT (hL : L.OkT) {h : Clif.Function} (hh : h ∈ L.P.funcs) :
    frameDrop (L.A h).af = (L.A h).af.frameSize + 16 := by
  simp [frameDrop, lowerRFunc_frame (hL.compiled h hh).alloc]

/-- **A call of a function `h` of `P`** at depth `M` (its callee run at depth `M`, `crun M`,
returns) from a world `w` with room for the callee's stack: one VCode outcome of `h`, which the
linked machine's call realises from every caller state compatible with `w` (`CallerOk`), in
particular from the canonical one. -/
theorem progCallT (hL : L.OkT) [hR : L.CrunOk] {M : Nat} (hM : 0 < M) (ih : L.ThmT κ (M - 1)) {n : String}
    {h : Clif.Function} (hpf : L.P.func? n = some h) (hcal : ∃ g ∈ L.P.funcs, L.Callee g h)
    (hib : ((RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves) ∨ L.NeedNI)
    {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a)
    {uses : List CV} {w : Arm.ArmState} (herr : Arm.r .ERR w = .None)
    (hal : (spv w).toNat % 16 = 0)
    (hroom : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat)
    (hdead : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a → F a ∧ ¬ L.Img a)
    {vals : List Clif.Val} {cm : Clif.Mem} {cs : Clif.State} {rvals : List Clif.Val}
    {cm' : Clif.Mem} (hmr : MemRel F L.syms cm w) (hargs : ArgsAt h.sig vals uses w)
    (hsav : StackArgsAvoid F h.sig vals w) (hpl : L.NeedSlots → L.PlaceAt cm (spv w))
    (hinit : Clif.initState L.P n vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm') :
    ∃ (us : List (Reg × Reg)) (outs : List CV) (wf : Arm.ArmState),
      RetsOkT h rvals us ∧ us.length = outs.length ∧
      PrefixHold rvals outs ∧ MemRel F L.syms cm' wf ∧ (L.A h).vc.RetsSite us ∧
      (∀ t, L.CallerOk F h uses w t → ∃ k,
        L.pcall M h t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) F
          (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t))) ∧
      (L.NeedNI → ∀ (Z : BitVec 64 → Prop) (t : Arm.ArmState), (∀ a, F a → Z a) →
        SameWorld Z t w → (∀ a, L.Img a → t.mem a = L.imgMem a) →
        (∀ r ∈ regLocs h.sig, regVal t r = regVal (L.canon h uses w) r) →
        RaOk (L.A h) (Arm.r .PC t) →
        MemRel F L.syms cm t →
        (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
          t.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
            w.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k)) → ∃ k,
        L.pcall M h t =
          Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
        ActRet (Arm.r .PC t + 4) Z
          (fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a)
          us outs wf (enterAt (L.A h) t) (runX (L.mach (M - 1) h) k (enterAt (L.A h) t))) := by
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  have hc := hL.compiled h hh
  have hfr := lowerRFunc_frame hc.alloc
  have hdrop := L.frameDrop_eqT hL hh
  have hfs := L.frameSize_modT hL hh
  obtain ⟨hnd, harg, hwid⟩ := hL.argRegs h hh
  have hsl0 : ¬ L.NeedSlots → h.slots = [] := fun hn => Classical.byContradiction fun hne => by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hn ⟨g, hg, h, hcg, hne⟩
  have hcase : h.slots = [] ∨ L.PlaceAt cm (spv w) := by
    by_cases hN : L.NeedSlots
    · exact .inr (hpl hN)
    · exact .inl (hsl0 hN)
  obtain ⟨hsl', hsym', hal', hby', hpl'⟩ := L.initState_mem hpf hinit hcase
  have hslotB : (L.A h).af.slotBase = (RAFrame.compute (L.A h).vcp (L.A h).rf).size :=
    (lowerRFunc_ok hc.alloc).1.2.1
  have hsz_le := size_le_frameSize hc.alloc
  have hfits : ∀ p ∈ h.slots, ∃ off, (slotLayout h.slots).1.lookup p.1 = some off ∧
      (L.A h).af.slotBase + off + p.2.size ≤ (L.A h).af.frameSize - clobberBytes (L.A h).af.saves := by
    obtain ⟨g, hg, hcg⟩ := hcal
    exact hL.slotFits g hg h hcg
  have hce : ClifEntry h vals cs := clifEntry_initState hpf hinit
  -- the run of the program without functions (program callees: the callee runs one level down)
  obtain ⟨m, hm⟩ := hR.link M hM h hh cs (runInv_entry hh hce)
    (runInv_entry (by simp [Clif.Program.only]) hce) (fun _ => hsym'.trans hmr.symbols)
    (L.envR (M - 1) h) rfl rfl (fun _ hn => L.envR_of (.inl hn)) (L.envR_link hL.names)
    (by rw [hrun]; intro _ e; cases e) (by rw [hrun]; intro e; cases e)
  rw [hrun] at hm
  obtain ⟨Nr, hrunN⟩ := hR.runs M cs _ hrun (.inl ⟨_, _, rfl⟩)
  -- the canonical state and the shared body-entry world
  let cn := L.canon h uses w
  let w₀ := bodyOf (L.A h).af (enterAt (L.A h) cn)
  have hcOk := L.callerOk_canonT hL hh himgF uses w
  have hsp0 : spv cn = spv w := hcOk.world.1 _ (by simp [Masked])
  have hspw₀ : spv w₀ = spv w - BitVec.ofNat 64 (frameDrop (L.A h).af) := by
    rw [spv_bodyOf, spv_enterAt, hsp0]
  obtain ⟨-, -, hB⟩ := off_toNat 0 (spv w) (frameDrop (L.A h).af) (by omega)
  -- the callee's outgoing area (in the caller's dead stack) is outside the callee's `F`
  let ib := (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase
  let spb := spv w - BitVec.ofNat 64 (frameDrop (L.A h).af)
  let sz := (RAFrame.compute (L.A h).vcp (L.A h).rf).size
  let Fh : BitVec 64 → Prop := fun a =>
    F a ∧ ¬ OutAt ib spb a ∧ ¬ SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a
  have hib_le : ib ≤ sz := intBase_le_size _ _
  have hspb : spb.toNat = (spv w).toNat - frameDrop (L.A h).af := hB
  have hlt := (spv w).isLt
  have hout_reg : ∀ a, OutAt ib spb a →
      StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hout_F : ∀ a, OutAt ib spb a → F a ∧ ¬ L.Img a := fun a ha => hdead a (hout_reg a ha)
  -- the callee's slot region (in the caller's dead stack) is outside the callee's `F`
  have hslot_reg : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a →
      StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a := by
    intro a ⟨h1, h2⟩
    rw [hspb] at h1 h2
    exact ⟨by omega, by omega⟩
  have hslot_F : ∀ a, SlotAt sz ((L.A h).af.frameSize - clobberBytes (L.A h).af.saves) spb a → F a ∧ ¬ L.Img a :=
    fun a ha => hdead a (hslot_reg a ha)
  have hspb_add : ∀ j < ib, OutAt ib spb (spb + BitVec.ofNat 64 j) := by
    intro j hj
    have e : (spb + BitVec.ofNat 64 j).toNat = spb.toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), hspb]
      exact Nat.mod_eq_of_lt (by omega)
    exact ⟨by omega, by omega⟩
  have hOut : ∀ (u : Arm.ArmState), spv u = spb →
      (∀ a n, cs.mem.valid a n = true → ∀ k < n, ¬ OutAt ib spb (BitVec.ofNat 64 (a + k))) →
      OutRel Fh ib cs.mem u := by
    intro u hu hv
    refine ⟨by omega, fun j hj hfh => hfh.2.1 (hu ▸ hspb_add j hj), fun a n hva k hk j hj e => ?_⟩
    rw [hu] at e
    exact hv a n hva k hk (e ▸ hspb_add j hj)
  -- the live allocations of the callee's entry: the caller's, and its slots in its slot region
  have hcsv : ∀ a n, cs.mem.valid a n = true → a + n ≤ 2 ^ 64 ∧ ∀ k < n,
      ¬ Fh (BitVec.ofNat 64 (a + k)) ∧ ¬ OutAt ib spb (BitVec.ofNat 64 (a + k)) := by
    intro a n hv
    simp only [Clif.Mem.valid, List.any_eq_true] at hv
    obtain ⟨x, hx, hcx⟩ := hv
    rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
    · have hv' : cm.valid a n = true := List.any_eq_true.mpr ⟨x, hx', hcx⟩
      obtain ⟨h1, h2⟩ := hmr.valid a n hv'
      exact ⟨h1, fun k hk => ⟨fun hf => h2 k hk hf.1, fun ho => h2 k hk (hout_F _ ho).1⟩⟩
    · obtain ⟨off, hoff, hle⟩ := hfits p hp
      simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq, hoff,
        Option.getD_some] at hcx
      refine ⟨by omega, fun k hk => ?_⟩
      have e : (BitVec.ofNat 64 (a + k)).toNat = a + k := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      refine ⟨fun hf => hf.2.2 ⟨by rw [e]; omega, by rw [e]; omega⟩,
        fun ⟨o1, o2⟩ => by rw [e] at o1 o2; omega⟩
  -- the callee's entry memory is related to a body-entry world agreeing with the caller's
  have hRel : ∀ u, spv u = spb → Arm.r .ERR u = .None →
      (∀ a b, cm.valid a 1 = true → cm.bytes a = some b → Arm.read_mem (BitVec.ofNat 64 a) u = b) →
      RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem u := by
    intro u hu herru hbu
    refine ⟨⟨⟨fun a b hv hb => ?_, fun a n hv => ⟨(hcsv a n hv).1,
      fun k hk => ((hcsv a n hv).2 k hk).1⟩, hsym'.trans hmr.symbols⟩, fun id b hl => ?_,
      hOut u hu (fun a n hv k hk => ((hcsv a n hv).2 k hk).2)⟩, by rw [hu, hspw₀], herru⟩
    · obtain ⟨hb', hnot⟩ := hby' a b hb
      refine hbu a b ?_ hb'
      simp only [Clif.Mem.valid, List.any_eq_true] at hv ⊢
      obtain ⟨x, hx, hcx⟩ := hv
      rcases hal' x hx with hx' | ⟨p, hp, rfl⟩
      · exact ⟨x, hx', hcx⟩
      · simp only [Clif.Alloc.contains, Bool.and_eq_true, decide_eq_true_eq] at hcx
        exact absurd ⟨hcx.1, by omega⟩ (hnot p hp)
    · rw [hsl'] at hl
      obtain ⟨p, hp, rfl, rfl⟩ := lookup_map_some hl
      obtain ⟨off, hoff, -⟩ := hfits p hp
      refine ⟨off, hoff, ?_⟩
      simp only [Rel.slotReg, hoff, Option.getD_some, hu]
      omega
  have hWE : L.WorldEntry κ (M - 1) h Fh vals cs w₀ := by
    refine ⟨hce, ?_, ?_, ?_, ?_, ?_, fun a ha => ⟨himgF a ha, fun ho => (hout_F a ho).2 ha,
      fun hs => (hslot_F a hs).2 ha⟩, fun hN => by rw [hspw₀]; exact hpl' (hpl hN)⟩
    · refine hRel w₀ hspw₀ ?_ fun a b hv hb => ?_
      · simp only [w₀]
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hcOk.world.1 _ (by simp [Masked])]
        exact herr
      · rw [← hmr.bytes a b hv hb]
        simp only [Arm.read_mem, Arm.read_store, w₀, mem_bodyOf, mem_enterAt]
        rw [L.mem_canon, mem_withImg, if_neg]
        intro hi
        exact (hmr.valid a 1 hv).2 0 (by omega) (by simpa using himgF _ hi)
    · intro loc v hmem
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      cases loc with
      | stack off =>
        simp only
        have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
          have := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
          rw [if_pos hfr, spv_enterAt, hsp0] at this
          exact this
        rw [hx29, fp_off_eq]
        refine ⟨fun k hk hf => hsav off v hmem k hk hf.1, ?_⟩
        rw [show Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w₀ =
            Arm.read_mem_bytes v.ty.bytes (spv w + BitVec.ofNat 64 off) w from
          read_mem_bytes_congr _ _ (fun k hk => by
            simp only [w₀, mem_bodyOf, mem_enterAt]
            rw [L.mem_canon, mem_withImg, if_neg (fun hi => hsav off v hmem k hk (himgF _ hi))])]
        exact hargs.2.2 off v hmem
      | reg r =>
        obtain ⟨i, hr, hv⟩ := reg_zip _ _ hi
        have hlen := hargs.2.1.1
        obtain ⟨u, hu⟩ : ∃ u, uses[i]? = some u := by
          have hi' : i < uses.length := by
            rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hv).1
          exact ⟨uses[i]'hi', List.getElem?_eq_getElem _⟩
        have hvh := hargs.2.1.2 i v u hv hu
        have hrA : r.isArgReg = true := harg r (List.mem_of_getElem? hr)
        simp only
        rw [show regVal w₀ r = regVal (placeArgs (regLocs h.sig) uses (L.withImg w)) r by
          simp only [w₀]; rw [regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA, L.regVal_canon _ _ _ hrA],
          placeArgs_regVal _ _ _ hnd harg hr hu]
        refine vHolds_setVal ?_ hvh
        have hty := hce.sig
        have hvmem : v ∈ vals := List.of_mem_zip hmem |>.2
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvmem
        have e := congrArg (·[j]?) hty
        simp only [List.getElem?_map, hj, Option.map_some] at e
        cases hp : h.sig.params[j]? with
        | none => rw [hp] at e; cases e
        | some p =>
          rw [hp] at e
          simp only [Option.map_some, Option.some.injEq] at e
          rw [e]; exact hwid p (List.mem_of_getElem? hp)
    · rw [hspw₀, hB]; omega
    · intro a ha
      rw [hspw₀] at ha
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      have hd := hdead a ⟨by omega, by omega⟩
      exact ⟨⟨hd.1, fun ⟨o1, o2⟩ => by rw [hspb] at o1; omega,
        fun ⟨o1, o2⟩ => by rw [hspb] at o1; omega⟩, hd.2⟩
    · rw [hspw₀, hB, hdrop]; omega
  obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, hrs, hall, hni⟩ :=
    ih h hh Fh vals cs w₀ m rvals cm' hWE hm
  -- the callee's live allocations after the call are outside the caller's `F`
  have hmemF : MemRel F L.syms cm' wf := by
    refine ⟨hmemR.bytes, fun a n hv => ?_, hmemR.symbols⟩
    by_cases hN : L.NeedSlots
    · exact hmr.valid a n (Clif.runLoop_allocs hL.free (hL.baseKeepsAllocs hN) Nr cs rvals cm'
        (runInv_entry hh hce) (Clif.initState_allocInv hinit) hrunN a n hv)
    have hsl1 := hsl0 hN
    have hsz1 : sz = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves := by
      obtain ⟨g, hg, hcg⟩ := hcal
      exact hL.calleeFrame g hg h hcg hsl1
    by_cases hib0 : ib = 0
    · obtain ⟨h1, h2⟩ := hmemR.valid a n hv
      exact ⟨h1, fun k hk hf => h2 k hk ⟨hf, fun ⟨o1, o2⟩ => by omega,
        fun ⟨o1, o2⟩ => by omega⟩⟩
    · obtain ⟨-, pl, hcm⟩ := initState_noSlots hpf hsl1 hinit
      have hv0 := runLoop_valid hL.free (hL.baseNoAlloc ⟨h, hh, hib0⟩) (L.slotFree hN) Nr
        cs rvals cm' (runInv_entry hh hce)
        (fun hkk => by
          have ⟨k0, hk0, hnk⟩ := hkk
          refine ⟨(hL.indScope k0 hk0 hnk).keep, fun h' hh' hs' =>
            hL.addrSlots hN ⟨h, hh, hib0⟩ hkk h' hh' ?_⟩
          rw [hcm] at hs'; rwa [← hmr.symbols]) hrunN a n hv
      rw [hcm] at hv0
      exact hmr.valid a n hv0
  -- the callee's activation from a caller state `t`
  let G : BitVec 64 → Prop :=
    fun a => F a ∧ ¬ StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a
  have hcode : ∀ t, ∀ a, CodeAddr (enterAt (L.A h) t) a → L.Img a := fun t a ha =>
    hL.imgAddr h hh a (by simpa [CodeAddr] using ha)
  have hME : ∀ t w₀', spv t = spv w → Arm.r .ERR t = .None →
      (∀ a, L.Img a → t.mem a = L.imgMem a) →
      BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' →
      L.MachEntry κ (M - 1) h Fh G (Arm.r .PC t + 4) (enterAt (L.A h) t) w₀' := by
    intro t w₀' hst herrt himgt hbw
    have hspt : spv (enterAt (L.A h) t) = spv w := by rw [spv_enterAt]; exact hst
    have hFrame : frameWG (κ (M - 1) h) ib (RAFrame.compute (L.A h).vcp (L.A h).rf).size
        (L.A h).af G (enterAt (L.A h) t) = Fh := by
      funext a
      apply propext
      rw [frameWG_out hfr (by rw [hspt, ← hdrop]; exact hroom) hib_le (size_le_frameBody hc.alloc), ← hdrop, hspt]
      constructor
      · rintro (⟨hb, hno, hns⟩ | hc | hg)
        · exact ⟨(hdead a hb).1, hno, hns⟩
        · exact ⟨himgF a (hcode t a hc), fun ho => (hout_F a ho).2 (hcode t a hc),
            fun hs => (hslot_F a hs).2 (hcode t a hc)⟩
        · exact ⟨hg.1, fun ho => hg.2 (hout_reg a ho), fun hs => hg.2 (hslot_reg a hs)⟩
      · intro ⟨hF, hno, hns⟩
        by_cases hb : StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a
        · exact .inl ⟨hb, hno, hns⟩
        · exact .inr (.inr ⟨hF, hb⟩)
    refine ⟨⟨by simp, fun k wd hk => hL.imgCode h hh _ (fun a ha => by
        rw [mem_enterAt]; exact himgt a ha) k wd hk, by simp, ?_, x30_enterAt _ _, ?_,
        hL.fits h hh⟩, ?_, fun a ha => ?_, hFrame,
      fun a ha => ⟨himgF a ha, fun hb => (hdead a hb).2 ha⟩,
      fun a ha => by rw [mem_enterAt]; exact himgt a ha, hbw⟩
    · rw [r_enterAt _ _ (by simp) (by simp)]; exact herrt
    · rw [hspt]; exact hal
    · refine stackRoom_of (by rw [hspt, ← hdrop]; exact hroom) fun a ha hb => ?_
      rw [hspt, ← hdrop] at hb
      exact (hdead a hb).2 (hcode t a ha)
    · rw [hspt]; exact ha.2
  have hpcall : ∀ t k, RaOk (L.A h) (Arm.r .PC t) →
      PostTrace (L.A h).fa (L.A h).af (L.A h).base (L.mach (M - 1) h) (enterAt (L.A h) t) k →
      ArmRet (Arm.r .PC t + 4) (enterAt (L.A h) t)
        (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) →
      (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)).program = (enterAt (L.A h) t).program →
      L.pcall M h t =
        Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program := by
    intro t k hra htrk hret hprog
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    show linkedCall _ _ _ = _
    exact linkedCall_eq hc.layout hlm hra (by rw [hdrop]; omega) (by omega) htrk
      ⟨hret.pc, hret.err, hprog.trans (program_enterAt _ _), hret.sp.trans (spv_enterAt _ _)⟩
  have hx29 : Arm.r (.GPR 29#5) w₀ = spv w - 16#64 := by
    have := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
    rw [if_pos hfr, spv_enterAt, hsp0] at this
    exact this
  -- non-interference: a caller state `t` agreeing with `w` outside `Z ⊇ F`, entered with its
  -- own body-entry world
  have key2 : L.NeedNI → ∀ (Z : BitVec 64 → Prop) (t : Arm.ArmState), (∀ a, F a → Z a) →
      SameWorld Z t w → (∀ a, L.Img a → t.mem a = L.imgMem a) →
      (∀ r ∈ regLocs h.sig, regVal t r = regVal (L.canon h uses w) r) →
      RaOk (L.A h) (Arm.r .PC t) →
      MemRel F L.syms cm t →
      (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
        t.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
          w.mem (spv w + BitVec.ofNat 64 off + BitVec.ofNat 64 k)) → ∃ k,
      L.pcall M h t =
        Arm.set_program (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) t.program ∧
      ActRet (Arm.r .PC t + 4) Z G us outs wf (enterAt (L.A h) t)
        (runX (L.mach (M - 1) h) k (enterAt (L.A h) t)) := by
    intro hN Z t hFZ hZ himgt hregt hrat hmt hstkt
    have hst : spv t = spv w := hZ.1 _ (by simp [Masked])
    have herrt : Arm.r .ERR t = .None := by rw [hZ.1 _ (by simp [Masked])]; exact herr
    let w₀' := bodyOf (L.A h).af (enterAt (L.A h) t)
    let D : BitVec 64 → Prop := fun a => Z a ∧ ¬ Fh a
    have hspw₀' : spv w₀' = spb := by
      simp only [w₀']; rw [spv_bodyOf, spv_enterAt, hst]
    have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀' :=
      ⟨spv_bodyOf _ _, x29_bodyOf _ _, fun r hr => regVal_bodyOf _ _
        (harg r (hL.entryRegs h hh r hr)), fun f hf h29 h31 => r_bodyOf _ _ h29 h31,
        fun a _ => by simp [w₀'], by simp [w₀']⟩
    have hrel' : RelW ⟨Fh, L.syms, (L.A h).af.slotBase, ib⟩ h (spv w₀) cs.frame.slots cs.mem w₀' := by
      refine hRel w₀' hspw₀' ?_ fun a b hv hb => ?_
      · simp only [w₀']
        rw [r_bodyOf _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp)]
        exact herrt
      · have := hmt.bytes a b hv hb
        simp only [Arm.read_mem, Arm.read_store, w₀', mem_bodyOf, mem_enterAt] at this ⊢
        exact this
    have hsw : SameWorld (fun a => Fh a ∨ D a) w₀ w₀' := by
      refine ⟨fun f hf => ?_, fun a ha => ?_, by simp [w₀, w₀']⟩
      · by_cases h29 : f = .GPR 29#5
        · subst h29
          have e1 := x29_bodyOf (L.A h).af (enterAt (L.A h) cn)
          have e2 := x29_bodyOf (L.A h).af (enterAt (L.A h) t)
          simp only [xreg] at e1 e2
          rw [e1, e2, spv_enterAt, spv_enterAt, hsp0, hst, if_pos hfr, if_pos hfr]
        by_cases h31 : f = .GPR 31#5
        · subst h31
          show spv w₀ = spv w₀'
          rw [hspw₀, hspw₀']
        have hpc : f ≠ .PC := by rintro rfl; exact hf trivial
        have h30 : f ≠ .GPR 30#5 := by rintro rfl; exact hf (by simp [Masked])
        rw [r_bodyOf _ _ h29 h31, r_bodyOf _ _ h29 h31, r_enterAt _ _ hpc h30, r_enterAt _ _ hpc h30,
          hcOk.world.1 f hf, hZ.1 f hf]
      · have hnZ : ¬ Z a := fun hz => by
          by_cases hf : Fh a
          · exact ha (.inl hf)
          · exact ha (.inr ⟨hz, hf⟩)
        simp only [w₀, w₀', mem_bodyOf, mem_enterAt]
        rw [hcOk.world.2.1 a (fun hf => hnZ (hFZ a hf)), hZ.2.1 a hnZ]
    have hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf h.sig).zip vals →
        regVal w₀' r = regVal w₀ r := by
      intro r v hm
      have hrl : r ∈ regLocs h.sig :=
        List.mem_filterMap.mpr ⟨.reg r, (List.of_mem_zip hm).1, rfl⟩
      have hrA := harg r hrl
      simp only [w₀, w₀']
      rw [regVal_bodyOf _ _ hrA, regVal_bodyOf _ _ hrA, regVal_enterAt _ _ hrA,
        regVal_enterAt _ _ hrA, hregt r hrl]
    have hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf h.sig).zip vals → ∀ k < v.ty.bytes,
        w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
          w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) := by
      intro off v hm k hk
      rw [hx29, fp_off_eq]
      have hnF := hsav off v hm k hk
      simp only [w₀, w₀', mem_bodyOf, mem_enterAt]
      rw [hstkt off v hm k hk, hcOk.world.2.1 _ hnF]
    obtain ⟨k, hret, htrk⟩ := hni hN D w₀' hrel' hsw hreg hstk G (Arm.r .PC t + 4)
      (enterAt (L.A h) t) (hME t w₀' hst herrt himgt hbw)
    refine ⟨k, hpcall t k hrat htrk hret.ret hret.prog, ⟨hret.ret, hret.regs, fun a ha => hret.mem a
      (fun h' => ha (h'.elim (fun h1 => hFZ a h1.1) (fun h2 => h2.1))), hret.fields, hret.gkeep,
      hret.prog⟩⟩
  refine ⟨us, outs, wf, hus, hlen, hhold, hmemF, hrs, fun t ht => ?_, key2⟩
  by_cases hN : L.NeedNI
  · refine key2 hN F t (fun _ h => h) ht.world ht.img ht.regs ht.ra ⟨fun a b hv hb => ?_,
      hmr.valid, hmr.symbols⟩ fun off v hm k hk => ht.world.2.1 _ (hsav off v hm k hk)
    rw [← hmr.bytes a b hv hb]
    simp only [Arm.read_mem, Arm.read_store]
    exact ht.world.2.1 _ (by simpa using (hmr.valid a 1 hv).2 0 (by omega))
  · -- no outgoing area: the canonical body-entry world is the actual activation's
    obtain ⟨hib0, hsz0⟩ := hib.resolve_right hN
    have hFh : Fh = F := funext fun a => propext ⟨fun h => h.1, fun h => ⟨h, fun ⟨o1, o2⟩ => by
      omega, fun ⟨o1, o2⟩ => by omega⟩⟩
    have hbw : BodyEntryW Fh (L.A h).vcp.EntryArg (L.A h).af (enterAt (L.A h) t) w₀ := by
      rw [hFh]; exact L.bodyEntryW_compatT hL hh himgF ht
    have hst : spv t = spv w := ht.world.1 _ (by simp [Masked])
    have herrt : Arm.r .ERR t = .None := by rw [ht.world.1 _ (by simp [Masked])]; exact herr
    obtain ⟨k, hret, htrk⟩ := hall G (Arm.r .PC t + 4) (enterAt (L.A h) t)
      (hME t w₀ hst herrt ht.img hbw)
    exact ⟨k, hpcall t k ht.ra htrk hret.ret hret.prog, ⟨hret.ret, hret.regs, fun a ha => hret.mem a
      (fun h' => ha h'.1), hret.fields, hret.gkeep, hret.prog⟩⟩
end LinkSys
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem X_extT (hL : L.OkT) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} {d : Option String}
    {uses : List CV} {w : Arm.ArmState} {outs : List CV} {w' : Arm.ArmState}
    (hx : (L.XT κ M g F).call d uses w = some (outs, w'))
    (herr : Arm.r .ERR w = .None) : Arm.r .ERR w' = .None ∧ w'.program = w.program := by
  cases d with
  | some n =>
    cases hpf : L.P.func? n with
    | none =>
      rw [L.XT_base hpf _ _ F] at hx
      exact hL.baseExt _ _ _ _ _ (.inr ⟨n, rfl, hpf⟩) hx herr
    | some h =>
      rw [L.XT_prog hpf _ _ F] at hx
      exact L.progXT_ext hx
  | none =>
    cases uses with
    | nil => exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
    | cons u args =>
      cases hs : symCallee L.Xb L.P (lo64 u) with
      | none =>
        rw [L.XT_none hs] at hx
        exact hL.baseExt _ _ _ _ _ (.inl rfl) hx herr
      | some h =>
        rw [L.XT_ind hs] at hx
        split at hx
        · exact L.progXT_ext hx
        · cases hx
end LinkSys
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- `K` is a budget (every frame at most `D`, `Ok.depth`). -/
theorem budget_KT (hL : L.OkT) : L.Budget fun M _ => L.K M := by
  intro M g _ h hc
  have := hL.depth h (L.callee_mem hc)
  simp only [K, Nat.mul_succ]
  omega

/-- **The core of the operand-view obligation of a call of the function `h` of `P`** (by `bl`
or `blr`) in the linked machine at depth `M` (from the linking statement at depth `M - 1`): from
a caller state `t` whose arguments are in `h`'s parameter registers (`hLu`, of either class), the
linked call gives `progXT`'s results (in `h`'s return registers by class, `hLd`) and world. -/
theorem progOsCoreT (hL : L.OkT) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h)
    {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {Lc : List (Nat × RegClass × Reg)} {Dc : List (Reg × Nat × RegClass)}
    (hLu : Lc.map (·.2.2) = regLocs h.sig)
    (hLd : (Dc.map (·.1)).take (sigRets h.sig).length = (sigRetRegs h.sig).take Dc.length)
    {info : CallInfo} (hdefs0 : info.defs = callDefsC Dc)
    {ops : Array Operand} {regs : Array Reg}
    (hdefs : ((ops.zip regs).toList.filter (·.1.isDef)) = (callDefOpsC Dc).zip (Dc.map (·.1)))
    {t w w' : Arm.ArmState} {o outs : List CV}
    (hK : κ M g ≤ (spOf t).toNat) (hG : ∀ a, G a → t.mem a = s0.mem a)
    (hra : RaOk (L.A h) (Arm.r .PC t))
    (hsw : SameWorld F t w)
    (hx : L.progXT κ M F h (Lc.map (fun q => regVal t q.2.2)) w = some (o, w'))
    (houts : ∃ n, outs = o.take n) :
    SameWorld F (L.pcall M h t) w' ∧
      FrameKeep (fun a => F a ∧ ¬ StackBelow (κ M g) (spOf t) a) t (L.pcall M h t) ∧
      (∀ p ∈ defRegs ops regs outs, regVal (L.pcall M h t) p.1.2 = p.2) ∧
      (∀ r, r.allocatable = true → (∀ p ∈ (ops.zip regs).toList, p.1.isDef = true → p.2 ≠ r) →
        r ∉ (MInst.call info).clobbers → regVal (L.pcall M h t) r = regVal t r) ∧
      (∀ r ∈ (MInst.call info).clobbers, r ∈ calleeSaved →
        ckeep r (regVal (L.pcall M h t) r) = ckeep r (regVal t r)) := by
  have hpf := func?_of_mem hL.names hh
  have hib : ((RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves) ∨ L.NeedNI := by
    by_cases h0 : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0
    · by_cases h1 : (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves
      · exact .inl ⟨h0, h1⟩
      · exact .inr ⟨g, hg, h, hcallee, .inr h1⟩
    · exact .inr ⟨g, hg, h, hcallee, .inl h0⟩
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  generalize huses : Lc.map (fun q => regVal t q.2.2) = uses at hx
  unfold progXT at hx
  have hcond : L.Cond κ M F h uses w ∧
      Arm.r .ERR (L.pcall M h (L.canon h uses w)) = .None :=
    Classical.byContradiction fun hc => by rw [if_neg hc] at hx; cases hx
  rw [if_pos hcond] at hx
  obtain ⟨⟨hM, herrw, halw, hroom, hdead, vals, cm, cs, rvals, cm', hmr, hargs, hsav, hpl, hinit,
    hrun⟩,
    -⟩ := hcond
  simp only [Option.some.injEq, Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨us, outsV, wf, hus, hlen, hhold, hmemR, hrs, hcall, -⟩ :=
    L.progCallT hL hM (ih hM) hpf ⟨g, hg, hcallee⟩ hib himgF herrw halw hroom hdead hmr hargs hsav hpl
      hinit hrun
  -- the caller state is compatible with the canonical one
  have hcOk : L.CallerOk F h uses w t := by
    refine ⟨hsw, fun a ha => (hG a (himgG a ha)).trans (himgS a ha), fun r hr => ?_,
      hra⟩
    rw [← hLu] at hr
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hrA : r.isArgReg = true := harg r (by rw [← hLu]; exact List.mem_of_getElem? hj)
    have hu : uses[j]? = some (regVal t r) := by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hj
      obtain ⟨q, hq, rfl⟩ := hj
      simp [← huses, hq]
    rw [L.regVal_canon _ _ _ hrA, placeArgs_regVal _ _ _ hnd harg (by rw [← hLu]; exact hj) hu,
      setVal_regVal]
  obtain ⟨ks, hs_eq, hs_ret⟩ := hcall t hcOk
  obtain ⟨kc, hc_eq, hc_ret⟩ := hcall _ (L.callerOk_canonT hL hh himgF uses w)
  -- the allocated call
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the world
    rw [hs_eq, hc_eq]
    refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
    · rw [r_set_program, r_set_program]
      by_cases h29 : f = .GPR 29#5
      · subst h29
        have e1 := hs_ret.ret.savedX 29 (by decide)
        have e2 := hc_ret.ret.savedX 29 (by decide)
        simp only [xreg] at e1 e2
        rw [show (BitVec.ofNat 5 29) = 29#5 from rfl] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          (L.callerOk_canonT hL hh himgF uses w).world.1 _ hf, hsw.1 _ hf]
      by_cases h31 : f = .GPR 31#5
      · subst h31
        have e1 := hs_ret.ret.sp
        have e2 := hc_ret.ret.sp
        simp only [spv] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          (L.callerOk_canonT hL hh himgF uses w).world.1 _ hf, hsw.1 _ hf]
      · rw [hs_ret.fields f hf h29 h31, hc_ret.fields f hf h29 h31]
    · simp only [mem_set_program]
      rw [hs_ret.mem a ha, hc_ret.mem a ha]
    · simp only [program_set_program]
      rw [hsw.2.2, L.program_canon]
  · -- the frame outside the dead stack
    rw [hs_eq]
    refine ⟨?_, fun a ⟨ha, hb⟩ => ?_, ?_⟩
    · show spv (Arm.set_program _ _) = spv t
      simp only [spv]; rw [r_set_program]
      have := hs_ret.ret.sp
      simp only [spv] at this
      rw [this, r_enterAt _ _ (by simp) (by simp)]
    · rw [mem_set_program, hs_ret.gkeep a ⟨ha, fun hb' => hb ?_⟩, mem_enterAt]
      have hsp : spv w = spOf t := (hsw.1 (.GPR 31#5) (by simp [Masked])).symm
      rw [hsp] at hb'
      exact stackBelow_mono hb' (L.budget_step hκ hM hg hcallee)
    · rw [r_set_program]
      exact (hs_ret.ret.savedX 29 (by simp [calleeSavedX]; exact ⟨10, by omega, rfl⟩)).trans
        (r_enterAt _ _ (by simp) (by simp))
  · -- the results
    intro p hp
    obtain ⟨⟨op, r⟩, x⟩ := p
    rw [defRegs] at hp
    obtain ⟨n, rfl⟩ := houts
    replace hp := mem_zip_of_mem_zip_take hp
    rw [hdefs] at hp
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hp
    simp only [List.getElem?_zip_eq_some] at hj
    obtain ⟨⟨-, hr⟩, hx⟩ := hj
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨r', hr'd, rfl⟩ := hx
    have hjd : j < h.sig.returns.length := by
      have := (List.getElem?_eq_some_iff.mp hr'd).1; rwa [declRetRegs_length] at this
    have hjr : j < (sigRets h.sig).length := Nat.lt_of_lt_of_le hjd (returns_le_sigRets _)
    have hr' : (sigRetRegs h.sig)[j]? = some r' := by
      rw [← hr'd, declRetRegs_eq_take, List.getElem?_take, if_pos hjd]
    have hjL : j < Dc.length := by
      have := (List.getElem?_eq_some_iff.mp hr).1; simpa using this
    have e1 : ((Dc.map (·.1)).take (sigRets h.sig).length)[j]? = (Dc.map (·.1))[j]? := by
      rw [List.getElem?_take]; simp [hjr]
    have e2 : ((sigRetRegs h.sig).take Dc.length)[j]? = (sigRetRegs h.sig)[j]? := by
      rw [List.getElem?_take]; simp [hjL]
    rw [← e1, hLd, e2, hr', Option.some.injEq] at hr
    subst hr
    show regVal _ r' = regVal _ r'
    rw [hs_eq, regVal_set_program, hc_eq, regVal_set_program]
    -- the `j`-th result register is a return register of the callee
    obtain ⟨Nr, hrunN⟩ := hR.runs M cs _ hrun (.inl ⟨_, _, rfl⟩)
    have hrt := Clif.runLoop_returned_tys hL.free Nr cs rvals cm'
      (runInv_entry hh (clifEntry_initState hpf hinit)) hrunN
    have hbot : cs.bottom = h := by
      have hce := clifEntry_initState (f := h) hpf hinit
      simp [Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    have hlr : (sigRets h.sig).length ≤ us.length := by
      cases hsr : h.sig.params.any (·.purpose == .sret) with
      | true => exact hL.sretRets h hh hsr us hrs
      | false =>
        rw [sigRets_of_noSret hsr, hlen]
        have := congrArg List.length hrt
        simp only [List.length_map, Clif.AbiParam.tys] at this
        rw [← this]; exact hhold.1
    have hju : j < us.length := by omega
    have hus_j : us[j]? = some ((us[j]'hju).1, r') := hus.reg_at hrt hjd hju hr'
    have hoj : outsV[j]? = some (outsV[j]'(by omega)) := List.getElem?_eq_getElem _
    rw [hs_ret.regs j _ _ _ hus_j hoj, hc_ret.regs j _ _ _ hus_j hoj]
  · -- the registers the callee preserves
    intro r hr hnd' hnc
    rw [hs_eq, regVal_set_program]
    have hnotd : r ∉ Dc.map (·.1) := by
      intro hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      have hmem : (⟨⟨q.2.1, q.2.2, .def, .late, .fixed q.1⟩, q.1⟩ : Operand × Reg) ∈
          (ops.zip regs).toList := by
        have h1 : (⟨⟨q.2.1, q.2.2, .def, .late, .fixed q.1⟩, q.1⟩ : Operand × Reg) ∈
            (callDefOpsC Dc).zip (Dc.map (·.1)) := List.mem_iff_getElem?.mpr (by
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
          exact ⟨i, by simp [callDefOpsC, List.getElem?_zip_eq_some, hi]⟩)
        rw [← hdefs] at h1
        exact (List.mem_filter.mp h1).1
      exact hnd' _ hmem rfl rfl
    have hnD : r ∉ defaultAapcsClobbers := by
      intro hm
      apply hnc
      simp only [MInst.clobbers, List.mem_filter, hm, true_and, hdefs0, callDefsC]
      simp only [List.any_map, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
      exact fun q hq e => hnotd (List.mem_map.mpr ⟨q, hq, by simpa using e⟩)
    rcases allocatable_cases hr with ⟨m, rfl, hm, h16, h17, h18⟩ | ⟨m, rfl, hm⟩
    · have h19 : 19 ≤ m :=
        Classical.byContradiction fun hc => hnD (by simp [defaultAapcsClobbers]; omega)
      have e := hs_ret.ret.savedX m (by simp [calleeSavedX]; exact ⟨m - 19, by omega, by omega⟩)
      simp only [xreg] at e
      simp only [regVal]
      rw [show rnum m = BitVec.ofNat 5 m from rfl, e, r_enterAt _ _ (by simp) (fun e' => by
        have := congrArg (fun f => match f with | Arm.StateField.GPR i => i.toNat | _ => 0) e'
        simp [rnum_toNat (show m < 32 by omega)] at this; omega)]
    · exact absurd (by simp [defaultAapcsClobbers]; omega) hnD
  · -- the callee-saved registers the call clobbers: the low halves of v8–v15
    intro r hr hcs
    rw [hs_eq, regVal_set_program]
    have hrD : r ∈ defaultAapcsClobbers := (List.mem_filter.mp hr).1
    simp only [calleeSaved, List.mem_append, List.mem_map, List.mem_range] at hcs
    rcases hcs with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact absurd hrD (by simp [defaultAapcsClobbers]; omega)
    · have e := hs_ret.ret.savedV (8 + i) (by omega) (by omega)
      simp only [ckeep, regVal]
      rw [show rnum (8 + i) = BitVec.ofNat 5 (8 + i) from rfl, e,
        r_enterAt _ _ (by simp) (by simp)]

/-- A `blr` target that is the address of the function `h` of `P` and of the symbol `n` (a call
through `n`'s GOT entry) is `h` named `n`. -/
theorem got_targetT (hL : L.OkT) {a : BitVec 64} {h : Clif.Function} {n : String}
    (hs : symCallee L.Xb L.P a = some h) (e : a = L.Xb.sym n 0) : n = h.name := by
  have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
  have := List.find?_some hs
  simp only [beq_iff_eq] at this
  exact hL.symInj h hh n (this.trans e)

/-- **The operand-view obligation of a call (`bl`) of a function of `P`** in the linked machine at
depth `M` (from the linking statement at depth `M - 1`). -/
theorem progOsT (hL : L.OkT) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} {h : Clif.Function} (hsite : L.ProgSite g info h) (ctx : FnCtx) :
    CallSoundCtlG F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XT κ M g F)) (.call info) .next := by
  have ⟨_, n, hdest, hpf⟩ := hsite
  obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
  subst hname
  obtain ⟨n', Lc, Dc, hinfo, hLu, hLd⟩ := hL.callRegs g hg info h hsite
  subst hinfo
  cases hdest
  intro t hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  replace hsem := csemV_sub hsem
  rw [operands_call_symC] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  have hregs := callRegs_eqC (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  rw [call_useValsC hregs] at hsem
  obtain ⟨o, hx, hout⟩ : ∃ o, L.progXT κ M F h (Lc.map (fun q => regVal t q.2.2)) w =
      some (o, w') ∧ outs = o.take (callDefsC Dc).length := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    rw [L.XT_prog hpf] at hx
    exact ⟨o, hx, rfl⟩
  obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
  exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_some hpf],
    L.progOsCoreT hL hκ ih hg hh (.inl ⟨_, hsite⟩) himgF himgG himgS hLu hLd rfl (call_defsC hregs) hK hG
      (hL.raCall g hg _ h hsite _ hP.callPc) hsw hx ⟨_, hout⟩⟩

/-- **The operand-view obligation of a `blr` call** in the linked machine at depth `M`: the
target register holds the address of a function of `P` that `g` declares (the linked call of it,
`progOsCoreT`), of another function of `P` (`X` undefined), or of no function of `P` (the
base's). -/
theorem progOsRegT (hL : L.OkT) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {s0 : Arm.ArmState} (himgF : ∀ a, L.Img a → F a)
    (himgG : ∀ a, L.Img a → G a) (himgS : ∀ a, L.Img a → s0.mem a = L.imgMem a)
    {info : CallInfo} (hsite : (L.A g).vcp.CallSite info) (hreg : ∀ n, info.dest ≠ .sym n)
    (ctx : FnCtx) :
    CallSoundCtlG F (κ M g) G s0 (CallAt (L.A g).fa (L.A g).base) (callExec (L.hooks M))
      (csemV (GotV (L.A g).vcp) F ctx (L.XT κ M g F)) (.call info) .next := by
  obtain ⟨tv, Lc, Dc, rfl, hregs⟩ := hL.blrRegs g hg info hsite hreg
  intro t hK hD hG c wh ops regs i' w outs w' hops hst hasg hP hsw hal herr hsem
  have hguard := csemV_guard hsem
  replace hsem := csemV_sub hsem
  have hops0 := hops
  rw [operands_call_regC] at hops
  cases hops
  obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
  obtain ⟨r0, hregs0⟩ := callRegs_eq_regC (regs := regs) (by simpa using hsz')
    (fun p hp r hr => (hloc p hp).2 r hr)
  -- the target register: an allocatable X register
  obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
    have hmem : (tgtOp tv, Loc.reg r0) ∈
        (((tgtOp tv :: (retOpsC Lc ++ callDefOpsC Dc)).toArray).zip (regs.map Loc.reg)).toList := by
      simp [Array.toList_zip, Array.toList_map, hregs0]
    obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
    exact ⟨n, hn, h29, h16⟩
  rw [call_useVals_regC hregs0] at hsem
  -- the allocated call: `blr x n0`
  obtain ⟨r1, us', ds', hr1, rfl⟩ := assign_call_reg hasg
  have h0 : regs[0]? = some (.x n0) := by
    rw [← Array.getElem?_toList, hregs0]; rfl
  rw [h0] at hr1
  cases hr1
  -- the target the machine reads
  have hc := hL.compiled g hg
  obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
  have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
    obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
    simp only [MInst.callInsn?, Option.some.injEq] at hx
    subst hx
    rw [lo64_regVal_x]
    exact blrTarget_of hc.layout hlm hj hn0 hpc
      (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (himgG a ha)).trans (himgS a ha)) k wd hk)
  -- the external semantics' call
  obtain ⟨o, hx, hout⟩ : ∃ o, (L.XT κ M g F).call none
      (regVal t (.x n0) :: Lc.map (fun q => regVal t q.2.2)) w =
      some (o, w') ∧ outs = o.take (callDefsC Dc).length := by
    simp only [csem, Option.map_eq_some_iff, Prod.mk.injEq] at hsem
    obtain ⟨⟨o, w2⟩, hx, rfl, rfl, -⟩ := hsem
    exact ⟨o, hx, rfl⟩
  cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
  | none =>
    -- no function of `P` at the target: the base's contract
    have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
    rw [L.XT_none hs] at hx
    have hsem' : csem F ctx L.Xb (.call ⟨.reg (.vreg tv .int), argPairsC Lc, callDefsC Dc⟩)
        (useVals (tgtOp tv :: (retOpsC Lc ++ callDefOpsC Dc)).toArray regs t) w =
        some (outs, w', .next) := by
      rw [call_useVals_regC hregs0, hout]; simp [csem, hx]
    obtain ⟨s', hex, rest⟩ := hL.baseOs g hg _ hsite (.inl rfl) F (κ M g) G s0
      (CallAt (L.A g).fa (L.A g).base) ctx t hK hD hG c wh _ regs _ w outs w' hops0 hst hasg hP hsw
      hal herr hsem'
    refine ⟨s', ?_, rest⟩
    simp only [callExec] at hex ⊢
    rw [L.hooks_base (.inl rfl) t (fun _ => hb)]
    exact hex
  | some h =>
    rw [L.XT_ind hs] at hx
    split at hx
    · rename_i hdecl
      have hh : h ∈ L.P.funcs := List.mem_of_find?_eq_some hs
      have hgot : ∀ n, GotV (L.A g).vcp tv n → n = h.name := by
        intro n hn
        have e := hguard tv n _ rfl hn (operands_call_regC tv Lc Dc) (by simp [tgtOp, Operand.isUse])
        rw [call_useVals_regC hregs0] at e
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at e
        exact L.got_targetT hL hs e
      obtain ⟨hLu, hLd⟩ := hregs h hh ⟨hdecl.1, hgot⟩ (by rw [← hdecl.2, List.length_map])
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = some h := by rw [htgt]; exact hs
      exact ⟨L.pcall M h t, by simp only [callExec, hal, ↓reduceIte, L.hooks_none hb],
        L.progOsCoreT hL hκ ih hg hh (.inr (.inr ⟨hh, hdecl.1.1⟩)) himgF himgG himgS hLu hLd rfl
          (call_defs_regC hregs0) hK hG
          (hL.raBlr g hg _ hsite hreg h hh hdecl.1.1 _ hP.callPc) hsw hx ⟨_, hout⟩⟩
    · cases hx
end LinkSys
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

theorem calleeOkT (hL : L.OkT) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) :
    CalleeOkG F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XT κ M g F) (L.hooks M)
      (L.A g).vcp.CallSite (GotV (L.A g).vcp) where
  os ctx info hsite := by
    cases hd : info.dest with
    | reg r =>
      exact L.progOsRegT hL hκ ih hg he.imgF he.imgG he.imgS hsite (fun n => by rw [hd]; simp) ctx
    | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h => exact L.progOsT hL hκ ih hg he.imgF he.imgG he.imgS ⟨hsite, n, hdest, hpf⟩ ctx
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      have h0 := hL.baseOs g hg info hsite hb F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) ctx
      intro t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.call ⟨.sym n, us, ds⟩) (useVals ops regs t) w =
          some (outs, w', .next) := by
        rw [← csemV_sub hsem]; simp [csem, L.XT_base hpf _ _ F]
      obtain ⟨s', hex, rest⟩ :=
        h0 t h1 h2 h3 c wh ops regs i' w outs w' hops hst hasg h4 hsw hal herr hsem'
      refine ⟨s', ?_, rest⟩
      obtain ⟨us', ds', rfl⟩ := assign_call_sym hasg
      simp only [callExec] at hex ⊢
      rw [L.hooks_base (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
      exact hex
  pc d u herr hal := by
    cases d with
    | none =>
      cases hb : (blrTarget u).bind (symCallee L.Xb L.P) with
      | none =>
        rw [L.hooks_base (.inl rfl) u (fun _ => hb)]; exact hL.basePc _ _ (.inl rfl) herr hal
      | some h => rw [L.hooks_none hb]; exact (L.pcall_pc M h u).2
    | some n =>
      cases hpf : L.P.func? n with
      | none =>
        rw [L.hooks_base (.inr ⟨n, rfl, hpf⟩) u (fun h => by cases h)]
        exact hL.basePc _ _ (.inr ⟨n, rfl, hpf⟩) herr hal
      | some h => rw [L.hooks_some hpf]; exact (L.pcall_pc M h u).2
  ext _ _ _ _ _ hx herr := L.X_extT hL hx herr

/-- **The `try_call` contract of the linked machine at depth `M`** for an activation of `g`: at
a `try_call` of a function of `P` (`bl`, or `blr` of the address of a declared one) the plain
call's contract (`calleeOkT`; `csem` defines a `try_call` only where the callee returns at least
its results); at a `try_call` of an extern outside `P` the base's. -/
theorem calleeTryOkT (hL : L.OkT) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F G : BitVec 64 → Prop} {ra : BitVec 64} {s w₀ : Arm.ArmState}
    (he : L.MachEntry κ M g F G ra s w₀) :
    CalleeTryOkG F (κ M g) G s (CallAt (L.A g).fa (L.A g).base) (L.XT κ M g F) (L.hooks M)
      (L.A g).vcp.TrySite (GotV (L.A g).vcp) := by
  intro ctx info ti hsite
  cases hd : info.dest with
  | sym n =>
    have hdest := hd
    cases hpf : L.P.func? n with
    | some h =>
      exact calleeTryOkG_of_call (S := fun i t => i = info ∧ t = ti)
        (fun ctx' i t ⟨e1, _⟩ => e1 ▸ (L.calleeOkT hL hκ ih hg he).os ctx' info hsite.callSite)
        (fun _ _ _ h => callAt_tryCall_call h)
        (fun i t ⟨_, e2⟩ => e2 ▸ trySite_clobberAll (hL.compiled g hg).alloc hsite)
        ctx info ti ⟨rfl, rfl⟩
    | none =>
      have hb : L.BaseDest (destOf info) := .inr ⟨n, by simp [destOf, hdest], hpf⟩
      intro c wh ops regs i' t w outs w' s' _ _ _ hops hst hasg _ hsw hal herr hsem hex
      obtain ⟨d, us, ds⟩ := info
      simp only at hdest
      subst hdest
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.sym n, us, ds⟩ ti) (useVals ops regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← csemV_sub hsem]; simp [csem, L.XT_base hpf _ _ F]
      obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall _ regs).2 ti i' hasg
      obtain ⟨us', ds', hic⟩ := assign_call_sym hasg'
      cases hic
      have hex' : callExec L.Hb (.tryCall ⟨.sym n, us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inr ⟨n, rfl, hpf⟩) t (fun h => by cases h)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, hb⟩ c wh ops regs _ t w outs w' s' hops hst hasg
        hsw hal herr hsem' hex'
  | reg r =>
    obtain ⟨tv, Lc, Dc, hinfo, -⟩ := hL.blrRegs g hg info hsite.callSite (fun n => by rw [hd]; simp)
    subst hinfo
    intro c wh ops regs i' t w outs w' s' hK hD hG hops hst hasg hP hsw hal herr hsem hex
    have hcl := trySite_clobberAll (hL.compiled g hg).alloc hsite
    have hopsC : (MInst.call ⟨.reg (.vreg tv .int), argPairsC Lc, callDefsC Dc⟩).operands = .ok ops := by
      rw [← operands_tryCall_call _ ti]; exact hops
    have hops1 := hopsC
    rw [operands_call_regC] at hops1
    cases hops1
    obtain ⟨hsz', hloc, -, -⟩ := checkStatic_facts hst
    obtain ⟨r0, hregs0⟩ := callRegs_eq_regC (regs := regs)
      (by have := hsz'; simp only [Array.size_map] at this ⊢; simpa using this)
      (fun p hp r hr => (hloc p hp).2 r hr)
    obtain ⟨n0, rfl, hn0, -⟩ : ∃ n, r0 = .x n ∧ n < 29 ∧ n ≠ 16 := by
      have hmem : (tgtOp tv, Loc.reg r0) ∈
          (((tgtOp tv :: (retOpsC Lc ++ callDefOpsC Dc)).toArray).zip (regs.map Loc.reg)).toList := by
        simp [Array.toList_zip, Array.toList_map, hregs0]
      obtain ⟨n, hn, h29, h16, -⟩ := locOk_int (hloc _ hmem).1
      exact ⟨n, hn, h29, h16⟩
    obtain ⟨ic, rfl, hasg'⟩ := (assign_call_tryCall _ regs).2 ti i' hasg
    obtain ⟨r1, us', ds', hr1, hic⟩ := assign_call_reg hasg'
    cases hic
    have h0 : regs[0]? = some (.x n0) := by
      rw [← Array.getElem?_toList, hregs0]; rfl
    rw [h0] at hr1
    cases hr1
    have hc := hL.compiled g hg
    obtain ⟨lm, hlm⟩ := FnAsm.layout_labelOffsets hc.layout
    have htgt : blrTarget t = some (lo64 (regVal t (.x n0))) := by
      obtain ⟨j, x, tt, hj, hx, hpc⟩ := hP
      simp only [MInst.callInsn?, Option.some.injEq] at hx
      subst hx
      rw [lo64_regVal_x]
      exact blrTarget_of hc.layout hlm hj hn0 hpc
        (fun k wd hk => hL.imgCode g hg t (fun a ha => (hG a (he.imgG a ha)).trans (he.imgS a ha)) k wd hk)
    have huv := call_useVals_regC (tv := tv) (s := t) hregs0
    cases hs : symCallee L.Xb L.P (lo64 (regVal t (.x n0))) with
    | none =>
      have hb : (blrTarget t).bind (symCallee L.Xb L.P) = none := by rw [htgt]; exact hs
      have hsem' : csem F ctx L.Xb (.tryCall ⟨.reg (.vreg tv .int), argPairsC Lc, callDefsC Dc⟩ ti)
          (useVals (tgtOp tv :: (retOpsC Lc ++ callDefOpsC Dc)).toArray regs t) w =
          some (outs, w', .goto ti.handlers.length) := by
        rw [← csemV_sub hsem, huv]; simp [csem, L.XT_none hs]
      have hex' : callExec L.Hb (.tryCall ⟨.reg (.x n0), us', ds'⟩ ti) t = some s' := by
        simp only [callExec] at hex ⊢
        rw [← L.hooks_base (M := M) (.inl rfl) t (fun _ => hb)]
        exact hex
      exact hL.baseTry g hg F ctx _ ti ⟨hsite, .inl rfl⟩ c wh _ regs _ t w outs w' s' hops hst
        hasg hsw hal herr hsem' hex'
    | some h =>
      exact calleeTry_at ((L.calleeOkT hL hκ ih hg he).os ctx _ hsite.callSite)
        (fun _ _ h => callAt_tryCall_call h) hcl hK hD hG hops hst hasg hP hsw hal herr hsem hex

theorem find_symT (hL : L.OkT) (n : String) :
    (∀ h, L.P.func? n = some h → L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) = some h) ∧
    (L.P.func? n = none → L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) = none) := by
  constructor
  · intro h hpf
    cases hf : L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) with
    | none =>
      obtain ⟨hh, rfl⟩ := Clif.Program.func?_some hpf
      have := List.find?_eq_none.mp hf h hh
      simp at this
    | some h' =>
      have hh' := List.mem_of_find?_eq_some hf
      have he := List.find?_some hf
      simp only [beq_iff_eq] at he
      have := hL.symInj h' hh' n he
      subst this
      rw [func?_of_mem hL.names hh'] at hpf
      cases hpf; rfl
  · intro hn
    cases hf : L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == L.Xb.sym n 0) with
    | none => rfl
    | some h' =>
      have hh' := List.mem_of_find?_eq_some hf
      have he := List.find?_some hf
      simp only [beq_iff_eq] at he
      have := hL.symInj h' hh' n he
      subst this
      rw [func?_of_mem hL.names hh'] at hn
      cases hn

/-- **A call of a function `h` of `P` that `g` declares, from a world of `g`** (the callee's
run at depth `M`, `crun M`, returning): `progXT` is defined and gives the callee's CLIF results
(from its return registers by class) and memory in `g`'s relation. -/
theorem progResultT (hL : L.OkT) [hR : L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) {g h : Clif.Function}
    (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat) (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a)
    (halign : c.toNat % 16 = 0)
    {sl : List (Clif.SlotId × Nat)} {cm : Clif.Mem} {w : Arm.ArmState} {args : List CV}
    {vals rvals : List Clif.Val} {cm' : Clif.Mem} {cs : Clif.State}
    (hargs : ArgsAt h.sig vals args w) (hsav : StackArgsAvoid F h.sig vals w)
    (hmr : RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
      g c sl cm w)
    (hpl : L.NeedSlots → L.PlaceAt cm c) (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hret : L.crun M cs = .returned rvals cm') :
    ∃ outs w', L.progXT κ M F h args w = some (outs, w') ∧ outs.length = h.sig.returns.length ∧
      PrefixHold rvals outs ∧
      RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c sl cm' w' := by
  have hpf := func?_of_mem hL.names hh
  have hM : 0 < M := by
    cases M with
    | zero => exact absurd hret (hR.zero cs rvals cm')
    | succ M => omega
  obtain ⟨Nr, hretN⟩ := hR.runs M cs _ hret (.inl ⟨_, _, rfl⟩)
  obtain ⟨⟨hmemR0, hslot, hout⟩, hsp, herrw⟩ := hmr
  have hroom' : frameDrop (L.A h).af + κ (M - 1) h ≤ (spv w).toNat := by
    rw [hsp]; have := L.budget_step hκ hM hg hcallee; omega
  have hdead' : ∀ a, StackBelow (frameDrop (L.A h).af + κ (M - 1) h) (spv w) a →
      F a ∧ ¬ L.Img a := fun a ha =>
    hdead a (by rw [← hsp]; exact stackBelow_mono ha (L.budget_step hκ hM hg hcallee))
  have hib : ((RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0 ∧
      (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves) ∨ L.NeedNI := by
    by_cases h0 : (RAFrame.compute (L.A h).vcp (L.A h).rf).intBase = 0
    · by_cases h1 : (RAFrame.compute (L.A h).vcp (L.A h).rf).size = (L.A h).af.frameSize - clobberBytes (L.A h).af.saves
      · exact .inl ⟨h0, h1⟩
      · exact .inr ⟨g, hg, h, hcallee, .inr h1⟩
    · exact .inr ⟨g, hg, h, hcallee, .inl h0⟩
  have hplw : L.NeedSlots → L.PlaceAt cm (spv w) := fun hN => by rw [hsp]; exact hpl hN
  obtain ⟨us, outsV, wf, hus, hlen, hhold, hmemR, -, hcall, -⟩ :=
    L.progCallT hL hM (ih hM) hpf ⟨g, hg, hcallee⟩ hib himgF herrw (by rw [hsp]; exact halign)
      hroom' hdead' hmemR0 hargs hsav hplw hinit hret
  obtain ⟨kc, hc_eq, hc_ret⟩ := hcall _ (L.callerOk_canonT hL hh himgF args w)
  have hcond : L.Cond κ M F h args w ∧ Arm.r .ERR (L.pcall M h (L.canon h args w)) = .None := by
    refine ⟨⟨hM, herrw, by rw [hsp]; exact halign, hroom', hdead', vals, cm, cs, rvals, cm',
      hmemR0, hargs, hsav, hplw, hinit, hret⟩, ?_⟩
    rw [hc_eq, r_set_program]; exact hc_ret.ret.err
  have hspT : spv (L.pcall M h (L.canon h args w)) = spv w := by
    rw [hc_eq]
    simp only [spv]
    rw [r_set_program]
    have := hc_ret.ret.sp
    simp only [spv] at this
    rw [this, r_enterAt _ _ (by simp) (by simp)]
    exact (L.callerOk_canonT hL hh himgF args w).world.1 _ (by simp [Masked])
  have hce := clifEntry_initState (f := h) hpf hinit
  have hrt : rvals.map (·.ty) = Clif.AbiParam.tys h.sig.returns := by
    have hrt := Clif.runLoop_returned_tys hL.free Nr cs rvals cm' (runInv_entry hh hce) hretN
    have hbot : cs.bottom = h := by simp [Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    exact hrt
  have hlr : rvals.length = h.sig.returns.length := by
    have := congrArg List.length hrt
    simpa only [List.length_map, Clif.AbiParam.tys] using this
  refine ⟨_, _, by rw [progXT, if_pos hcond], ?_, ⟨by simp [declRetRegs_length, hlr],
    fun j v x hv hx => ?_⟩,
    ⟨⟨⟨fun a b hv hb => ?_, hmemR.valid, hmemR.symbols⟩, ?_, ?_⟩, ?_, hcond.2⟩⟩
  · rw [List.length_map, declRetRegs_length]
  · -- the results
    have hjr : j < rvals.length := (List.getElem?_eq_some_iff.mp hv).1
    have hju : j < us.length := by have := hhold.1; omega
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hr' : (sigRetRegs h.sig)[j]? = some r := by
      rw [← hr, declRetRegs_eq_take, List.getElem?_take, if_pos (by omega)]
    have hus_j : us[j]? = some ((us[j]'hju).1, r) := hus.reg_at hrt (by omega) hju hr'
    have hoj : outsV[j]? = some (outsV[j]'(by omega)) := List.getElem?_eq_getElem _
    rw [hc_eq, regVal_set_program, hc_ret.regs j _ _ _ hus_j hoj]
    exact hhold.2 j v _ hv hoj
  · -- the bytes of the live allocations
    rw [← hmemR.bytes a b hv hb]
    simp only [Arm.read_mem, Arm.read_store]
    rw [hc_eq, mem_set_program, hc_ret.mem _ (by simpa using (hmemR.valid a 1 hv).2 0 (by omega))]
  · simpa [Rel.slotReg, hspT] using hslot
  · -- the caller's outgoing area: the callee's run creates no allocation there
    by_cases hib0 : (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase = 0
    · rw [hib0]; exact outRel_zero _ _ _
    · refine ⟨hout.1, by rw [hspT]; exact hout.2.1, fun a n hv k hk j hj => ?_⟩
      rw [hspT]
      by_cases hN : L.NeedSlots
      · exact hout.2.2 a n (Clif.runLoop_allocs hL.free (hL.baseKeepsAllocs hN) Nr cs rvals cm'
          (runInv_entry hh hce) (Clif.initState_allocInv hinit) hretN a n hv) k hk j hj
      have hsl : h.slots = [] := Classical.byContradiction fun hne =>
        hN ⟨g, hg, h, hcallee, hne⟩
      obtain ⟨-, pl, hcs⟩ := initState_noSlots hpf hsl hinit
      have hv0 := runLoop_valid hL.free (hL.baseNoAlloc ⟨g, hg, hib0⟩) (L.slotFree hN) Nr
        cs rvals cm' (runInv_entry hh hce)
        (fun hkk => by
          have ⟨k0, hk0, hnk⟩ := hkk
          refine ⟨(hL.indScope k0 hk0 hnk).keep, fun h' hh' hs' => hL.addrSlots hN ⟨g, hg, hib0⟩ hkk h' hh' ?_⟩
          rw [hcs] at hs'; simpa [hmemR0.symbols] using hs') hretN a n hv
      rw [hcs] at hv0
      exact hout.2.2 a n hv0 k hk j hj
  · rw [hspT, hsp]

/-- **The external contract of an activation of `g` at depth `M`** under its environment
(`envOf`: the linked environment, program callees running at most `M` steps): the base
environment's for the externs outside `P`, and for a function of `P` the linked machine's call
from the canonical state (from the linking statement at depth `M - 1`). -/
theorem xCallsOkT (hL : L.OkT) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsOk (L.envOf M g c) (g.externs.map (·.2))
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.XT κ M g F) := by
  intro ext hin gsem sl cm w d uses args vals rvals cm' hgs hd hargs hmr hret hrl
  rcases L.envOf_some hgs with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, G0, hgs, hG0⟩
  · obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseX g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c ext
      (List.mem_filter.mpr ⟨hin, by simp [hpf]⟩) gsem sl cm w d uses args vals rvals cm' hgs hd
      hargs hmr hret hrl
    refine ⟨outs, w', ?_, h1, h2, h3⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, -, rfl⟩
    · rw [L.XT_base hpf _ _ F]; exact hx
    · rw [L.XT_none (by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = none
        rw [lo64_ofX]; exact (L.find_symT hL ext.name).2 hpf)]
      exact hx
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    have hsig := hL.declSig g hg ext hin h hpf
    obtain ⟨hpl, hret⟩ := hG0 _ _ _ _ hret
    rw [Clif.linkEnvR_some hpf] at hgs
    cases hgs
    -- the callee's whole-program run
    simp only at hret
    cases hinit : Clif.initState L.P ext.name vals cm with
    | trap c' => rw [hinit] at hret; cases hret
    | stuck m' => rw [hinit] at hret; cases hret
    | ok cs =>
    rw [hinit] at hret
    simp only at hret
    rw [hsig] at hargs
    have hout := hmr.1.2.2
    have hsp := hmr.2.1
    -- the stack-passed arguments are in the caller's outgoing area, outside `F`
    have hsav : StackArgsAvoid F h.sig vals w := by
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
      have hav : Avoids F (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase (spv w) := hout.2.1
      exact hav (off + k) (by omega)
    rw [← hname] at hinit
    obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
      L.progResultT hL hκ ih hg hh (.inr (.inl ⟨ext, hin, hpf⟩)) himgF hroom hdead halign hargs hsav
        hmr hpl hinit hret
    refine ⟨outs, w', ?_, by rw [hol, hsig], hho, hmr'⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, hcol, rfl⟩
    · rw [L.XT_prog hpf]; exact hx
    · have hs : symCallee L.Xb L.P (lo64 (ofX ((L.XT κ M g F).sym ext.name 0))) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 (ofX (L.Xb.sym ext.name 0))) = some h
        rw [lo64_ofX]; exact (L.find_symT hL ext.name).1 h hpf
      have hto : L.IndTo g h := by
        refine ⟨by rw [hname]; exact hdecl, ?_⟩
        rcases hdecl with hdn | ⟨-, -, hall⟩
        · exact .inl ⟨by rw [hname]; exact hdn, ext, hin, hname.symm, hcol⟩
        · obtain ⟨sig, hs, hm⟩ := hall h hpf
          exact .inr ⟨sig, hs, hm, hm.returns_length⟩
      rw [L.XT_ind hs, if_pos ⟨hto, argsAt_regLocs hargs⟩]
      exact hx

/-- **The indirect-call contract of an activation of `g` at depth `M`** under its environment: an
indirect call reaching an extern outside `P` is the base's; one reaching a function of `P` that
`g` may reach (`MayCall`: declared or not) is, the call-site signature matching the callee's
(`envOf`'s `sigOf`), the linked machine's call from the canonical state (its parameters are in
registers, `indSig`). -/
theorem xCallsIndOkT (hL : L.OkT) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) {g : Clif.Function}
    (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop} (himgF : ∀ a, L.Img a → F a) {c : BitVec 64}
    (hroom : κ M g ≤ c.toNat)
    (hdead : ∀ a, StackBelow (κ M g) c a → F a ∧ ¬ L.Img a) (halign : c.toNat % 16 = 0) :
    XCallsIndOk (L.envOf M g c) (indSigs g)
      (RelW ⟨F, L.syms, (L.A g).af.slotBase, (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase⟩
        g c) (L.XT κ M g F) := by
  intro sig hsig n gsem sl cm w u args vals rvals cm' hgs hsg hu hl8 hall hmr hret hrl hty
  rcases L.envOf_some hgs with ⟨hpf, hgs⟩ | ⟨h, hpf, hdecl, G0, hgs, hG0⟩
  · have hs : symCallee L.Xb L.P (lo64 u) = none := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
      rw [hu]; exact (L.find_symT hL n).2 hpf
    obtain ⟨outs, w', hx, h1, h2, h3⟩ := hL.baseXI g hg F (L.A g).af.slotBase
      (RAFrame.compute (L.A g).vcp (L.A g).rf).intBase c sig hsig n gsem sl cm w u args vals rvals
      cm' hgs (fun _ h => nomatch h) hu hl8 hall hmr hret hrl hty
    exact ⟨outs, w', by rw [L.XT_none hs]; exact hx, h1, h2, h3⟩
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    have hnf : ¬ Clif.IndFree g := fun hif => by
      rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
    have hdeclS := hL.indSig g hg hnf
    have hs : symCallee L.Xb L.P (lo64 u) = some h := by
      show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
      rw [hu]; exact (L.find_symT hL h.name).1 h hpf
    obtain ⟨hpl, hret⟩ := hG0 _ _ _ _ hret
    rw [Clif.linkEnvR_some hpf] at hgs
    cases hgs
    simp only at hret
    cases hinit : Clif.initState L.P h.name vals cm with
    | trap c' => rw [hinit] at hret; cases hret
    | stuck m' => rw [hinit] at hret; cases hret
    | ok cs =>
    rw [hinit] at hret
    simp only at hret
    have hce := clifEntry_initState (f := h) hpf hinit
    have hvl : vals.length = h.sig.params.length := by
      have := congrArg List.length hce.sig
      simpa using this
    -- the call site's signature matches `h`'s (`Clif.callExternAt` checks it against `sigOf`)
    have hm : IndSigMatch sig h :=
      hsg h.sig (by simp only [envOf, Clif.linkEnvR_sigOf, hpf, Option.map_some])
    obtain ⟨bytes, hb, hb8⟩ := hdeclS h hh hdecl (.inl ⟨sig, hsig, hm⟩)
    have hargs : ArgsAt h.sig vals args w := (argsAt_iff_of_regs hb hb8 hvl).mpr hall
    have hsav : StackArgsAvoid F h.sig vals w := by
      intro off v hm
      obtain ⟨r, hr⟩ := (locsOf_small hb hb8).2 _ (List.of_mem_zip hm).1
      cases hr
    obtain ⟨outs, w', hx, hol, hho, hmr'⟩ :=
      L.progResultT hL hκ ih hg hh (.inr (.inr ⟨hh, hdecl⟩)) himgF hroom hdead halign hargs hsav
        hmr hpl hinit hret
    refine ⟨outs, w', ?_, ?_, hho, hmr'⟩
    · rw [L.XT_ind hs, if_pos ⟨⟨hdecl, .inr ⟨sig, hsig, hm, hm.returns_length⟩⟩,
        argsAt_regLocs hargs⟩]
      exact hx
    · rw [hol]
      exact hm.returns_length

/-- The canonical states of a call from two worlds have the same parameter registers. -/
theorem regVal_canon_eqT (hL : L.OkT) {h : Clif.Function} (hh : h ∈ L.P.funcs) {args : List CV}
    (hlen : args.length = (regLocs h.sig).length) (w w' : Arm.ArmState) :
    ∀ r ∈ regLocs h.sig, regVal (L.canon h args w') r = regVal (L.canon h args w) r := by
  intro r hr
  obtain ⟨hnd, harg, -⟩ := hL.argRegs h hh
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  have hjl : j < args.length := by have := (List.getElem?_eq_some_iff.mp hj).1; omega
  rw [L.regVal_canon _ _ _ (harg r hr), L.regVal_canon _ _ _ (harg r hr),
    placeArgs_regVal _ _ _ hnd harg hj (List.getElem?_eq_getElem hjl),
    placeArgs_regVal _ _ _ hnd harg hj (List.getElem?_eq_getElem hjl)]

/-- **Non-interference of a call of a function `h` of `P`** that `g` declares (when the linking
needs it): from two worlds that agree outside `Z ⊇ F`, related to the same CLIF memory, with the
arguments where `h`'s ABI puts them in both, on which the callee's run (`crun M`) returns,
the two calls (`progXT`) give the same results and worlds that agree outside `Z`. -/
theorem progX_niT (hL : L.OkT) [hR : L.CrunOk] (hN : L.NeedNI) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1))
    {g h : Clif.Function} (hg : g ∈ L.P.funcs) (hh : h ∈ L.P.funcs)
    (hcallee : L.Callee g h) {F Z : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (hFZ : ∀ a, F a → Z a) {w w' : Arm.ArmState}
    (hsw : SameWorld Z w w') {cm : Clif.Mem} {vals : List Clif.Val} {args : List CV}
    (hm : MemRel F L.syms cm w) (hm' : MemRel F L.syms cm w') (ha : ArgsAt h.sig vals args w)
    (ha' : ArgsAt h.sig vals args w') {cs : Clif.State} {rvals : List Clif.Val} {cm' : Clif.Mem}
    (hpl : L.NeedSlots → L.PlaceAt cm (spv w)) (hinit : Clif.initState L.P h.name vals cm = .ok cs)
    (hrun : L.crun M cs = .returned rvals cm') {o o' : List CV}
    {x x' : Arm.ArmState} (hx : L.progXT κ M F h args w = some (o, x))
    (hx' : L.progXT κ M F h args w' = some (o', x')) : o = o' ∧ SameWorld Z x x' := by
  have hpf := func?_of_mem hL.names hh
  unfold progXT at hx hx'
  split at hx
  case isFalse => cases hx
  rename_i hc
  split at hx'
  case isFalse => cases hx'
  simp only [Option.some.injEq, Prod.mk.injEq] at hx hx'
  obtain ⟨rfl, rfl⟩ := hx
  obtain ⟨rfl, rfl⟩ := hx'
  obtain ⟨⟨hM, herr, hal, hroom, hdead, vals1, cm1, cs1, rvals1, cm1', -, -, hsav1, -, hinit1, -⟩,
    -⟩ :=
    hc
  have hty : vals.map (·.ty) = vals1.map (·.ty) := by
    rw [(clifEntry_initState hpf hinit).sig, (clifEntry_initState hpf hinit1).sig]
  have hsav := stackArgsAvoid_tys hsav1 hty
  obtain ⟨us, outs, wf, hus, hlen, hhold, -, hrs, hall, hni⟩ :=
    L.progCallT hL hM (ih hM) hpf ⟨g, hg, hcallee⟩ (.inr hN) himgF herr hal hroom hdead hm ha
      hsav hpl hinit hrun
  have hc0 := L.callerOk_canonT hL hh himgF args w
  have hc1 := L.callerOk_canonT hL hh himgF args w'
  have hsp' : spv w' = spv w := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨k, heq, hret⟩ := hall _ hc0
  obtain ⟨k', heq', hret'⟩ := hni hN Z (L.canon h args w') hFZ
    ((SameWorld.mono hFZ hc1.world).trans hsw.symm) hc1.img
    (L.regVal_canon_eqT hL hh (argsAt_regLocs ha) w w') hc1.ra (L.memRel_canon himgF hm' h args)
    (fun off v hmz j hj => by
      rw [L.mem_canon, mem_withImg, if_neg (fun hi => hsav off v hmz j hj (himgF _ hi))]
      exact stackArgs_bytes ha.2.2 ha'.2.2 hsp' off v hmz j hj)
  -- the callee's declared results are among the defs of its return site
  have hrt : rvals.map (·.ty) = Clif.AbiParam.tys h.sig.returns := by
    have hce := clifEntry_initState hpf hinit
    obtain ⟨Nr, hrunN⟩ := hR.runs M cs _ hrun (.inl ⟨_, _, rfl⟩)
    have hrt := Clif.runLoop_returned_tys hL.free Nr cs rvals cm' (runInv_entry hh hce) hrunN
    have hbot : cs.bottom = h := by simp [Clif.State.bottom, hce.callers, hce.func]
    rw [hbot] at hrt
    exact hrt
  have hsr : h.sig.returns.length ≤ us.length := by
    have e := congrArg List.length hrt
    simp only [List.length_map, Clif.AbiParam.tys] at e
    rw [← e]
    have := hhold.1
    omega
  have hres : ∀ (u : Arm.ArmState) (kk : Nat) (Y : BitVec 64 → Prop) (G : BitVec 64 → Prop),
      ActRet (Arm.r .PC u + 4) Y G us outs wf (enterAt (L.A h) u)
        (runX (L.mach (M - 1) h) kk (enterAt (L.A h) u)) →
      ∀ j (hj : j < (declRetRegs h.sig).length),
        regVal (Arm.set_program (runX (L.mach (M - 1) h) kk (enterAt (L.A h) u)) u.program)
          ((declRetRegs h.sig)[j]'hj) =
            outs[j]'(by rw [declRetRegs_length] at hj; omega) := by
    intro u kk Y G hr j hj
    have hj' : j < h.sig.returns.length := by rwa [declRetRegs_length] at hj
    have hju : j < us.length := by omega
    have hr' : (sigRetRegs h.sig)[j]? = some ((declRetRegs h.sig)[j]'hj) := by
      rw [← List.getElem?_eq_getElem hj, declRetRegs_eq_take, List.getElem?_take, if_pos hj']
    have hus_j : us[j]? = some ((us[j]'hju).1, (declRetRegs h.sig)[j]'hj) :=
      hus.reg_at hrt hj' hju hr'
    rw [regVal_set_program, hr.regs j _ _ _ hus_j (List.getElem?_eq_getElem _)]
  refine ⟨?_, ?_⟩
  · rw [heq, heq']
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map]
    simp only [List.length_map] at h1
    rw [hres _ k _ _ hret j h1, hres _ k' _ _ hret' j h1]
  · rw [heq, heq']
    refine ⟨fun f hf => ?_, fun a ha => ?_, ?_⟩
    · rw [r_set_program, r_set_program]
      by_cases h29 : f = .GPR 29#5
      · subst h29
        have e1 := hret.ret.savedX 29 (by unfold calleeSavedX; decide)
        have e2 := hret'.ret.savedX 29 (by unfold calleeSavedX; decide)
        simp only [xreg] at e1 e2
        rw [show (BitVec.ofNat 5 29) = 29#5 from rfl] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hc0.world.1 _ hf, hc1.world.1 _ hf, hsw.1 _ hf]
      by_cases h31 : f = .GPR 31#5
      · subst h31
        have e1 := hret.ret.sp
        have e2 := hret'.ret.sp
        simp only [spv] at e1 e2
        rw [e1, e2, r_enterAt _ _ (by simp) (by simp), r_enterAt _ _ (by simp) (by simp),
          hc0.world.1 _ hf, hc1.world.1 _ hf, hsw.1 _ hf]
      rw [hret.fields f hf h29 h31, hret'.fields f hf h29 h31]
    · rw [mem_set_program, mem_set_program, hret.mem a (fun hf => ha (hFZ a hf)), hret'.mem a ha]
    · rw [program_set_program, program_set_program, L.program_canon, L.program_canon]
      exact hsw.2.2

/-- **Non-interference of the external semantics of an activation of `g`** at its calls (when
the linking needs it): the base externs' (`baseNI`), and for a function of `P` that `g` declares
`progX_niT` (a direct call has the arguments in the callee's ABI, its declaration having the
callee's signature, `declSig`; an indirect call's callee takes register arguments, `indSig`). -/
theorem xniT (hL : L.OkT) [L.CrunOk] (hN : L.NeedNI) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1))
    {g : Clif.Function} (hg : g ∈ L.P.funcs) {F : BitVec 64 → Prop}
    (himgF : ∀ a, L.Img a → F a) (c : BitVec 64) :
    XNI F L.syms (g.externs.map (·.2)) (indSigs g) c
      (CallLg (L.envOf M g c) (g.externs.map (·.2)) (indSigs g)) (L.XT κ M g F) := by
  intro n sig vals cm args d uses Z w w' o x o' x' hlg hd hFZ hsw hm hm' hc1 hc2 hA hx hx'
  obtain ⟨hkind, G, rv, cm'', hG, hGo⟩ := hlg
  rcases L.envOf_some hG with ⟨hpf, hb⟩ | ⟨h, hpf, hdecl, G0, hGl, hG0⟩
  · have hbase := hL.baseNI hN g hg F c n sig vals cm args d uses Z w w' o x o' x'
      ⟨hpf, hkind, G, rv, cm'', hb, hGo⟩ hd hFZ hsw hm hm' hc1 hc2 hA
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.XT_base hpf] at hx hx'
      exact hbase hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = none := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = none
        rw [hu]; exact (L.find_symT hL n).2 hpf
      rw [L.XT_none hs] at hx hx'
      exact hbase hx hx'
  · obtain ⟨hh, hname⟩ := Clif.Program.func?_some hpf
    subst hname
    obtain ⟨hpl, hGo⟩ := hG0 _ _ _ _ hGo
    have hplw : L.NeedSlots → L.PlaceAt cm (spv w) := fun hS => hc1 ▸ hpl hS
    rw [Clif.linkEnvR_some hpf] at hGl
    cases hGl
    simp only at hGo
    cases hinit : Clif.initState L.P h.name vals cm with
    | trap c' => rw [hinit] at hGo; cases hGo
    | stuck m' => rw [hinit] at hGo; cases hGo
    | ok cs =>
    rw [hinit] at hGo
    simp only at hGo
    have hce := clifEntry_initState (f := h) hpf hinit
    have hvl : vals.length = h.sig.params.length := by
      have := congrArg List.length hce.sig
      simpa using this
    have hcallee : L.Callee g h := .inr (.inr ⟨hh, hdecl⟩)
    have hAA : ArgsAt h.sig vals args w ∧ ArgsAt h.sig vals args w' := by
      rcases hA with ⟨⟨e', he', hen', hes⟩, h1, h2⟩ | ⟨hsig, h8, hall⟩
      · have := hL.declSig g hg e' he' h (by rw [hen']; exact hpf)
        rw [← hes, this] at h1 h2
        exact ⟨h1, h2⟩
      · have hnf : ¬ Clif.IndFree g := fun hif => by
          rw [indSigs_nil_of_indFree hif] at hsig; cases hsig
        have hdeclS := hL.indSig g hg hnf
        -- the call entered `h`: its parameter types are the call's signature's
        have hmatch : IndTyMatch sig h := by
          rcases hkind with ⟨e', he', hen', hes⟩ | ⟨-, hty⟩
          · have := hL.declSig g hg e' he' h (by rw [hen']; exact hpf)
            rw [← hes, this]
            rfl
          · exact hce.sig.symm.trans hty
        obtain ⟨bytes, hb, hb8⟩ := hdeclS h hh hdecl (L.indReach hpf hdecl hsig hmatch)
        exact ⟨(argsAt_iff_of_regs hb hb8 hvl).mpr hall, (argsAt_iff_of_regs hb hb8 hvl).mpr hall⟩
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, u, rfl, hu⟩
    · rw [L.XT_prog hpf] at hx hx'
      exact L.progX_niT hL hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hplw hinit hGo hx hx'
    · have hs : symCallee L.Xb L.P (lo64 u) = some h := by
        show L.P.funcs.find? (fun h' => L.Xb.sym h'.name 0 == lo64 u) = some h
        rw [hu]; exact (L.find_symT hL h.name).1 h hpf
      rw [L.XT_ind hs] at hx hx'
      split at hx
      · rename_i hif
        rw [if_pos hif] at hx'
        exact L.progX_niT hL hN ih hg hh hcallee himgF hFZ hsw hm hm' hAA.1 hAA.2 hplw hinit hGo hx
          hx'
      · cases hx

/-- The TLSDESC flags of an activation's external semantics are the base's. -/
theorem xTlsT (hL : L.OkT) (hN : L.NeedNI) {M : Nat} {g : Clif.Function} {F : BitVec 64 → Prop} :
    XTls F (L.XT κ M g F) :=
  fun Z n w w' hFZ hsw => hL.baseTlsNI hN F Z n w w' hFZ hsw
end LinkSys
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- The run of `P.bare` under `linkEnvR` keeps `ActInv`: it stays in its frame
(`Clif.step_bare_callers`) and its externs keep (when program callees have slots) the oracle. -/
theorem actInv_stepT (hL : L.OkT) [hR : L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs) {c : BitVec 64}
    {s s1 : Clif.State} (hJ : L.ActInv g c s)
    (hs : Clif.step (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare s = .next s1) :
    L.ActInv g c s1 := by
  obtain ⟨hI, hc, hpl⟩ := hJ
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  have hc1 := Clif.step_bare_callers hPf hI.1 hc hs
  refine ⟨(Clif.step_next_linv hPf hI hs (fun _ h => by simp at h)).1, hc1, fun hN => ?_⟩
  obtain ⟨sps, hp⟩ := hpl hN
  refine ⟨sps, ?_⟩
  rcases Clif.step_next_cases hPf hI hs with ⟨-, -, ⟨hpl', -⟩ | ⟨n, G, vals, rv, hG, hr⟩⟩ |
    ⟨cc, hcc, -⟩ | ⟨cc, hcc, -⟩
  · rw [hpl', hp]
  · rw [Clif.linkEnvR_keepsPlace0 (hR.runs M) hL.free (hL.baseKeepsPlace hN) n G hG vals s.mem rv
      s1.mem (fun pl h => by rw [hp] at h; cases h; rfl) hr, hp]
  · rw [hc1] at hcc; cases hcc
  · rw [hc] at hcc; cases hcc

/-- A step of an activation of `g` under `envOf` that is not stuck is its step under
`linkEnvR` (`envOf` is `envR` there, a restriction of `linkEnvR`). -/
theorem step_envOf_linkT (hL : L.OkT) {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {s : Clif.State} (hJ : L.ActInv g c s) {r : Clif.StepResult}
    (hs : Clif.step (L.envOf M g c) L.P.bare s = r) (hr : ∀ m, r ≠ .stuck m) :
    Clif.step (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare s = r := by
  have hPf : ∀ f ∈ (L.P.only g).funcs, Clif.LinkFree f := fun f hf => by
    simp only [Clif.Program.only, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact hL.free f hg
  rw [L.step_envOf (hL.free g hg) hJ.1.1 hJ.2.2] at hs
  exact step_of_restrict L.envR_restricts hPf hJ.1.1 hs hr

theorem runLoop_envOfT (hL : L.OkT) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} :
    ∀ (n : Nat) (s : Clif.State), L.ActInv g c s →
      Clif.runLoop (L.envOf M g c) L.P.bare n s = Clif.runLoop (L.envR M g) L.P.bare n s
  | 0, _, _ => rfl
  | n + 1, s, hJ => by
    rw [Clif.runLoop_succ', Clif.runLoop_succ', L.step_envOf (hL.free g hg) hJ.1.1 hJ.2.2]
    cases hs : Clif.step (L.envR M g) L.P.bare s with
    | next s1 =>
      have hs' := L.step_envOf_linkT hL hg hJ
        ((L.step_envOf (hL.free g hg) hJ.1.1 hJ.2.2).trans hs) (fun _ h => nomatch h)
      exact runLoop_envOfT hL hg n s1 (L.actInv_stepT hL hg hJ hs')
    | _ => rfl

theorem reach_envOfT (hL : L.OkT) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {cs s : Clif.State} (hr : Reach (L.envOf M g c) L.P.bare cs s)
    (hJ : L.ActInv g c cs) :
    Reach (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs s ∧ L.ActInv g c s := by
  induction hr with
  | refl => exact ⟨.refl _, hJ⟩
  | step hs _ ih =>
    have hs' := L.step_envOf_linkT hL hg hJ hs (fun _ h => nomatch h)
    obtain ⟨h1, h2⟩ := ih (L.actInv_stepT hL hg hJ hs')
    exact ⟨.step hs' h1, h2⟩

/-- The run premises of `P.bare` under `linkEnvR` are those under `envOf`. -/
theorem trapsExplicit_envOfT (hL : L.OkT) [L.CrunOk] {M : Nat} {g : Clif.Function} (hg : g ∈ L.P.funcs)
    {c : BitVec 64} {cs : Clif.State} (hJ : L.ActInv g c cs)
    (h : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) :
    TrapsExplicit (L.envOf M g c) L.P.bare cs where
  stmt := fun s c st rest hr hs hb => by
    obtain ⟨hr', hJs⟩ := L.reach_envOfT hL hg hr hJ
    exact h.stmt s c st rest hr' (L.step_envOf_linkT hL hg hJs hs (fun _ h => nomatch h)) hb
  tryCall := fun s c fn args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reach_envOfT hL hg hr hJ
    exact h.tryCall s c fn args et hr' (L.step_envOf_linkT hL hg hJs hs (fun _ h => nomatch h)) hb ht
  tryCallInd := fun s c callee args et hr hs hb ht => by
    obtain ⟨hr', hJs⟩ := L.reach_envOfT hL hg hr hJ
    exact h.tryCallInd s c callee args et hr'
      (L.step_envOf_linkT hL hg hJs hs (fun _ h => nomatch h)) hb ht
  indirect := fun s st rest sig callee args hr hb hi hst =>
    h.indirect s st rest sig callee args (L.reach_envOfT hL hg hr hJ).1 hb hi hst
  tryIndirect := fun s callee args et hr hb ht hB =>
    h.tryIndirect s callee args et (L.reach_envOfT hL hg hr hJ).1 hb ht hB
end LinkSys
namespace LinkSys
variable (L : LinkSys)
variable {κ : Nat → Clif.Function → Nat}

/-- **The induction step**: the linking statement at depth `M` from the one at depth `M - 1`. -/
theorem thm_ofT (hL : L.OkT) [L.CrunOk] (hκ : L.Budget κ) {M : Nat} (ih : 0 < M → L.ThmT κ (M - 1)) : L.ThmT κ M := by
  intro g hg F vals cs w₀ fuel rvals cm' hWE hrun
  have hc := hL.compiled g hg
  have hI : Clif.LInv (L.P.only g) cs := runInv_entry (by simp [Clif.Program.only]) hWE.clif
  have hJ : L.ActInv g (spv w₀) cs := ⟨hI, hWE.clif.callers, hWE.place⟩
  have hrun' : Clif.runLoop (L.envOf M g (spv w₀)) L.P.bare fuel cs = .returned rvals cm' := by
    rw [L.runLoop_envOfT hL hg fuel cs hJ]; exact hrun
  have hAE : ∀ G ra s w₀', L.MachEntry κ M g F G ra s w₀' →
      ActEntry (L.A g).vcp (L.A g).rf (L.A g).af (L.A g).fa (L.A g).fb (κ M g) F G (L.XT κ M g F)
        (L.hooks M) (L.A g).base ra s w₀' := fun G ra s w₀' hME =>
    ⟨hME.abi, hME.stack, hME.gfree, hME.hF, L.calleeOkT hL hκ ih hg hME,
      fun _ => L.calleeTryOkT hL hκ ih hg hME,
      fun ht => L.tlsOk_hooksT (hL.baseTls g hg (hasTls_of_vcode_pipelineAnyTS hc ht) F (κ M g)), hME.body⟩
  have hX := L.xCallsOkT hL hκ ih hg hWE.img hWE.room hWE.dead hWE.align
  have hXI := L.xCallsIndOkT hL hκ ih hg hWE.img hWE.room hWE.dead hWE.align
  -- the typed world theorem (with the proven control families)
  have hT := backend_correct_world_ni_pipelineAnyTS (hL.subset g hg) hc typedRules_program
    (X := L.XT κ M g F) (syms := L.syms)
    (env := L.envOf M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
    hX hXI (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
    (trapsExplicit_of_returned hrun') fuel
  cases hsr : g.sig.params.any (·.purpose == .sret) with
  | false =>
    obtain ⟨us, outs, wf, hus, -, hlen, hhold, hmem, hrs, hall, hni⟩ := hT rvals cm' hrun'
    refine ⟨us, outs, wf, ⟨hus, fun h => absurd (hsr.symm.trans h) (by decide)⟩, hlen, hhold, hmem,
      hrs, fun G ra s hME => hall (L.hooks M) G (L.A g).base ra s (hAE G ra s w₀ hME),
      fun hN D w₀' hrel' hsw hreg hstk G ra s hME => ?_⟩
    exact hni (L.xniT hL hN ih hg hWE.img (spv w₀)) (L.xTlsT hL hN) D w₀' hrel' hsw hreg hstk
      (L.hooks M) G (L.A g).base ra s (hAE G ra s w₀' hME)
  | true =>
    rcases hL.sretE g hg hsr with ⟨hsubE, hcE⟩ | hx
    · -- an `sret` function in subset E: the integer world theorem (its returns pinned by
      -- `RetPins`: the struct pointer in x8, #587)
      have h := backend_correct_world_ni_pipeline hsubE hcE
        (X := L.XT κ M g F) (syms := L.syms)
        (env := L.envOf M g (spv w₀)) (K := κ M g) (F := F) (c := spv w₀) (hL.covered g hg)
        hX hXI (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
        (trapsExplicit_of_returned hrun') fuel
      obtain ⟨-, -, -, -, htys, -⟩ := hT rvals cm' hrun'
      obtain ⟨us, outs, wf, hus, hlen, hhold, hmem, hrs, hall, hni⟩ := h rvals cm' hrun'
      have hint : ∀ v ∈ rvals, v.ty.isInt = true := by
        intro v hv
        have hm : v.ty ∈ Clif.AbiParam.tys g.sig.returns := htys ▸ List.mem_map_of_mem hv
        obtain ⟨q, hq, hqt⟩ := List.mem_map.mp hm
        have hE := hsubE.subsetE
        simp only [Compile.functionE, Compile.sigE, Bool.and_eq_true, List.all_eq_true] at hE
        have := hE.1.1.1.2 q hq
        simp only [Compile.tyE, Bool.and_eq_true] at this
        rw [← hqt]; exact this.1
      refine ⟨us, outs, wf, ⟨retRegsOk_of_retPins hus hint (by have := hhold.1; omega),
        fun _ => hus⟩,
        hlen, hhold, hmem, hrs, fun G ra s hME => hall (L.hooks M) G (L.A g).base ra s
        (hAE G ra s w₀ hME), fun hN D w₀' hrel' hsw hreg hstk G ra s hME => ?_⟩
      exact hni (L.xniT hL hN ih hg hWE.img (spv w₀)) (L.xTlsT hL hN) D w₀' hrel' hsw hreg hstk
        (L.hooks M) G (L.A g).base ra s (hAE G ra s w₀' hME)
    · -- #722: any `sret` function whose returns are in their `retX` registers (`RetsX`): the
      -- typed world theorem
      obtain ⟨us, outs, wf, hus, htys, hlen, hhold, hmem, hrs, hall, hni⟩ := hT rvals cm' hrun'
      have hrl : rvals.length = g.sig.returns.length := by
        have := congrArg List.length htys; simpa [Clif.AbiParam.tys] using this
      have hp : RetPins rvals us := by unfold RetPins; rw [hrl]; exact hx us hrs
      refine ⟨us, outs, wf, ⟨hus, fun _ => hp⟩, hlen, hhold, hmem, hrs,
        fun G ra s hME => hall (L.hooks M) G (L.A g).base ra s (hAE G ra s w₀ hME),
        fun hN D w₀' hrel' hsw hreg hstk G ra s hME => ?_⟩
      exact hni (L.xniT hL hN ih hg hWE.img (spv w₀)) (L.xTlsT hL hN) D w₀' hrel' hsw hreg hstk
        (L.hooks M) G (L.A g).base ra s (hAE G ra s w₀' hME)

/-- **The linking statement at every depth.** -/
theorem thmT (hL : L.OkT) [L.CrunOk] (hκ : L.Budget κ) : ∀ M, L.ThmT κ M
  | 0 => L.thm_ofT hL hκ fun h => absurd h (Nat.lt_irrefl 0)
  | M + 1 => L.thm_ofT hL hκ fun _ => thmT hL hκ M
end LinkSys
namespace LinkSys
variable (L : LinkSys)

/-- The premises of the linked program do not read the callee runs. -/
theorem OkT.withCrun {L : LinkSys} (hL : L.OkT) (c : Nat → Clif.State → Clif.Outcome) :
    (L.withCrun c).OkT := by
  cases hL; constructor <;> assumption

/-- **The default callee runs** (whole-program runs of at most `M` steps, `Clif.runLoop_linkN`). -/
theorem crunOk_stdT (hL : L.OkT) : L.std.CrunOk where
  runs M := Clif.runsOf_runLoop L.base L.P M
  zero _ _ _ h := by simp [std, withCrun] at h
  link M hM _ hf s hI hIf hsy _ hEn hEs hEb hEp hst hof :=
    Clif.runLoop_linkN (base := L.base) (syms := L.syms) (M - 1) hL.names hf hL.free
      (hL.indScope _ hf) hEn hEs hEb hEp M s (by omega) hI hIf hsy hst hof

/-- **The callee runs of fuel `F` and bounded depth** (`Clif.runD`, `Clif.runLoop_linkD`): a
complete callee run at depth `M` has at most `M - 1` callers of its own, so its callees run at
depth `M - 1`. -/
theorem crunOk_peakT (hL : L.OkT) (F : Nat) : (L.peak F).CrunOk where
  runs M := Clif.runsOf_runD L.base L.P F M
  zero _ _ _ h := by simp [peak, withCrun, Clif.runD] at h
  link M _ _ hf s hI hIf hsy _ hEn hEs hEb hEp hst hof := by
    have hd : 0 < M ∧ Clif.DepthLe L.base L.P (M - 1) s := by
      refine Classical.byContradiction fun hc => hof ?_
      show Clif.runD L.base L.P F M s = _
      simp only [Clif.runD, hc, ↓reduceIte]
    have he : Clif.runD L.base L.P F M s = Clif.runLoop L.base L.P F s := by
      simp only [Clif.runD, hd, and_self, ↓reduceIte]
    obtain ⟨m, hm⟩ := Clif.runLoop_linkD (base := L.base) (syms := L.syms) F (M - 1) hL.names hf
      hL.free (hL.indScope _ hf) hEn hEs hEb hEp F s (by omega) hd.2 hI hIf hsy
      (by rw [← he]; exact hst) (by rw [← he]; exact hof)
    exact ⟨m, hm.trans he.symm⟩
end LinkSys

/-- **The whole-program theorem for any callee runs** (`LinkSys.CrunOk`): for an outcome `o` of
`f`'s activation that, when it returns or traps, is a run of the program without functions under
`envR M f` (the callee runs at depth `M`), the linked machine of depth `M` refines `o`. -/
theorem backend_correct_program_coreT (L : LinkSys) (hL : L.OkT) [L.CrunOk]
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvR L.P L.base (L.crun M)) L.P.bare cs) {o : Clif.Outcome}
    (hlink : ((∃ vals cm, o = .returned vals cm) ∨ ∃ c, o = .trapped c) →
      ∃ m, Clif.runLoop (L.envR M f) L.P.bare m cs = o) :
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s o := by
  have hc := hL.compiled f hf
  have hfr := lowerRFunc_frame hc.alloc
  have hst := hres
  obtain ⟨hB, hK⟩ := spBody_toNat hres
  have hd : frameDrop (L.A f).af = (L.A f).af.frameSize + 16 := by simp [frameDrop, hfr]
  -- the world side
  have hWE : L.WorldEntry κ M f L.F args cs w₀ := by
    refine ⟨hcs, ⟨hrel, rfl, ?_⟩, ?_, ?_, ?_, ?_, hL.imgF, hpl⟩
    · rw [hbe.other .ERR (by simp [Masked]) (by simp) (by simp)]; exact hent.err
    · refine argsAtEntry_bodyT hfr hc.entryRegs hbe hargs
        fun off v hm k hk hk' => ?_
      rw [hF] at hk'
      rcases hk' with hw | hi
      · exact stackArgsAvoid_frameW_of_alloc hc.alloc hres hent hargs off v hm k hk hw
      · exact hsav off v hm k hk hi
    · rw [hbe.sp, hB]; omega
    · intro a ha
      rw [hbe.sp] at ha
      refine ⟨by rw [hF]; exact .inl (.inr ha), fun hi => hgfree a hi ?_⟩
      obtain ⟨h1, h2⟩ := ha
      rw [hB] at h1 h2
      exact ⟨by omega, by omega⟩
    · rw [hbe.sp, hB, hd]
      have := hent.spAligned
      have := L.frameSize_modT hL hf
      omega
  -- the machine side
  have hME : L.MachEntry κ M f L.F L.Img ra s w₀ :=
    ⟨hent.toCall, hres, hgfree, hF.symm, fun _ h => h, himg,
      hbe.w L.F fun r ⟨_, _, hvb, hi, _, hv⟩ =>
        ((ctlCheck_args (lowerRFunc_ok hc.alloc).2.2 hvb hi).2.2 _ hv).2⟩
  -- the whole-program run is a run of the program without functions
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  cases o with
  | stuck m => trivial
  | outOfFuel => trivial
  | returned vals cm =>
    obtain ⟨m, hm⟩ := hlink (.inl ⟨_, _, rfl⟩)
    obtain ⟨us, outs, wf, hus, hlen, hhold, hmemR, -, hall, -⟩ :=
      L.thmT hL hκ M f hf L.F args cs w₀ m vals cm hWE hm
    obtain ⟨n, hret, -⟩ := hall L.Img ra s hME
    exact armRefinesT_of_actRet hus.1 hlen hhold hmemR hret
  | trapped c =>
    obtain ⟨m, hm⟩ := hlink (.inr ⟨_, rfl⟩)
    have ih : 0 < M → L.ThmT κ (M - 1) := fun _ => L.thmT hL hκ (M - 1)
    have hJ : L.ActInv f (spv w₀) cs := ⟨hIf, hcs.callers, hpl⟩
    have hm' : Clif.runLoop (L.envOf M f (spv w₀)) L.P.bare m cs = .trapped c := by
      rw [L.runLoop_envOfT hL hf m cs hJ]; exact hm
    have h := backend_correct_world_pipelineAnyTS (hL.subset f hf) hc typedRules_program
      (X := L.XT κ M f L.F) (syms := L.syms)
      (env := L.envOf M f (spv w₀)) (K := κ M f) (F := L.F) (c := spv w₀) (hL.covered f hf)
      (L.xCallsOkT hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (L.xCallsIndOkT hL hκ ih hf hL.imgF hWE.room hWE.dead hWE.align)
      (fun n b hn => hL.symOk n b hn) rfl hWE.clif hWE.rel hWE.args
      (L.trapsExplicit_envOfT hL hf hJ htr) m
    exact h.2 c hm' (L.hooks M) L.Img (L.A f).base ra s ⟨hME.abi, hME.stack, hME.gfree, hME.hF,
      L.calleeOkT hL hκ ih hf hME,
      fun _ => L.calleeTryOkT hL hκ ih hf hME,
      fun ht => L.tlsOk_hooksT (hL.baseTls f hf (hasTls_of_vcode_pipelineAnyTS hc ht) L.F (κ M f)), hME.body⟩

/-- **`backend_correct_program` with a per-function stack budget** `κ` (`LinkSys.Budget`): the
stack premises and the world's exterior `L.F` use `κ M f` (the callees' stack of the entry
activation) instead of `L.K M`. `backend_correct_programT` is the budget `fun M _ => L.K M`; a
program without recursion has a depth-independent one (`FV/E2E/StackBound.lean`). The program
callees run at most `M` steps (`LinkSys.std`, `Clif.runLoop_linkN`). -/
theorem backend_correct_program_budgetT (L : LinkSys) (hL : L.OkT)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) := by
  haveI := L.crunOk_stdT hL
  rw [← L.mach_std]
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  refine backend_correct_program_coreT L.std (hL.withCrun _) hκ hf M hent hres hF hgfree himg hbe
    hargs hcs hsav hrel hpl htr fun ho => ?_
  exact Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf) (E := L.std.envR M f)
    rfl rfl (fun _ hn => L.std.envR_of (.inl hn))
    (L.std.envR_link hL.names) (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun _ h => nomatch h)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun h => nomatch h)

/-- **The whole-program theorem for the run's peak call depth** (L1d): `backend_correct_program_budget`
with the linked machine of depth `d`, the peak call depth of the whole-program CLIF run of at most
`F + 1` steps (`Clif.DepthLe`: every state it reaches has at most `d` callers) instead of its fuel:
the stack premises use `κ d f`, and the program callees run with fuel `F` and at most `d - 1`
callers of their own (`TrapsExplicit` under `Clif.linkEnvD`; `LinkSys.peak`,
`Clif.runLoop_linkD`). -/
theorem backend_correct_program_peakT (L : LinkSys) (hL : L.OkT)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (F d : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ d f) (L.A f).af s)
    (hF : L.F = frameWG (κ d f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ d f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (hd : Clif.DepthLe L.base L.P d cs)
    (htr : TrapsExplicit (Clif.linkEnvD L.P L.base F d) L.P.bare cs) :
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach d f) s (Clif.runLoop L.base L.P (F + 1) cs) := by
  haveI := L.crunOk_peakT hL F
  rw [← L.mach_peak F]
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  refine backend_correct_program_coreT (L.peak F) (hL.withCrun _) hκ hf d hent hres hF hgfree himg
    hbe hargs hcs hsav hrel hpl htr fun ho => ?_
  exact Clif.runLoop_linkD (base := L.base) (syms := L.syms) F d hL.names hf hL.free
    (hL.indScope f hf) (E := (L.peak F).envR d f)
    rfl rfl (fun _ hn => (L.peak F).envR_of (.inl hn))
    ((L.peak F).envR_link hL.names) (F + 1) cs (Nat.le_refl _) hd (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun _ h => nomatch h)
    (by rcases ho with ⟨_, _, ho⟩ | ⟨_, ho⟩ <;> rw [ho] <;> exact fun h => nomatch h)

/-- **The backend's end-to-end theorem for a linked program** (`docs/contracts/e2e.md`,
"Linking at the Arm level"): for a function `f` of a program `P` whose functions are compiled
and laid out as `L` describes (`L.OkT`), the Arm machine whose calls of the program's functions
run their compiled code (`L.mach M f`: the linked hooks of depth `M`, `LinkSys.hooks`) refines
the **whole-program** CLIF run of at most `M + 1` steps, from an ABI entry state with the code
image loaded and stack for `M` call levels. The addresses outside the world `L.F` are the entry
activation's frame, its callees' stack and the code (`hF`). The program callees' contracts are
discharged (by induction on the depth, `LinkSys.thmT`); the premises left are the base
environment's contracts, the scope and the link layout (`LinkSys.OkT`), and the entry. The run
premise `TrapsExplicit` is about the run of `f`'s activation in the program without functions
(`P.bare`: every program callee, `f` included, an atomic whole-program run): it has no
indirect-call clause left. When a program callee has stack slots (`NeedSlots`), the CLIF entry
memory's slot-placement oracle (`Clif.Mem.place`) has the body's `sp` and the program's compiled
frames (`hpl`): CLIF leaves stack-slot addresses unspecified, and this picks the run that places
them where the compiled code does. -/
theorem backend_correct_programT (L : LinkSys) (hL : L.OkT) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    (htr : TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs) :
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (Clif.runLoop L.base L.P (M + 1) cs) :=
  backend_correct_program_budgetT L hL (κ := fun M _ => L.K M) (L.budget_KT hL) hf M hent hres hF
    hgfree himg hbe hargs hcs hsav hrel hpl htr

/-- **The returning runs**: `backend_correct_program_budget` without the run premise `TrapsExplicit`
(a returning run satisfies it, `trapsExplicit_of_returned`). -/
theorem backend_correct_program_returned_budgetT (L : LinkSys) (hL : L.OkT)
    {κ : Nat → Clif.Function → Nat} (hκ : L.Budget κ) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (κ M f) (L.A f).af s)
    (hF : L.F = frameWG (κ M f) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + κ M f) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf)
    (E := Clif.linkEnvN L.P L.base M) rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hrel.1.symbols) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  rw [← hrun]
  exact backend_correct_program_budgetT L hL hκ hf M hent hres hF hgfree himg hbe hargs hcs hsav hrel hpl
    (trapsExplicit_of_returned hm)

/-- **The returning runs**: `backend_correct_program` without the run premise `TrapsExplicit`
(a returning run satisfies it, `trapsExplicit_of_returned`). -/
theorem backend_correct_program_returnedT (L : LinkSys) (hL : L.OkT) {f : Clif.Function}
    (hf : f ∈ L.P.funcs) (M : Nat) {ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State}
    (hent : AbiEntry (L.A f).fb (L.A f).base ra s) (hres : StackAvail (L.K M) (L.A f).af s)
    (hF : L.F = frameWG (L.K M) (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase
      (RAFrame.compute (L.A f).vcp (L.A f).rf).size (L.A f).af L.Img s)
    (hgfree : ∀ a, L.Img a → ¬ StackBelow (frameDrop (L.A f).af + L.K M) (spv s) a)
    (himg : ∀ a, L.Img a → s.mem a = L.imgMem a)
    (hbe : BodyEntry (L.A f).af s w₀) (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hsav : StackArgsAvoid L.Img f.sig args s)
    (hrel : Rel.holds ⟨L.F, L.syms, (L.A f).af.slotBase,
      (RAFrame.compute (L.A f).vcp (L.A f).rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (hpl : L.NeedSlots → L.PlaceAt cs.mem (spv w₀))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    ArmRefinesT (L.A f).fb (L.A f).base ra (L.mach M f) s (.returned vals cm) :=
  backend_correct_program_returned_budgetT L hL (κ := fun M _ => L.K M) (L.budget_KT hL) hf M hent
    hres hF hgfree himg hbe hargs hcs hsav hrel hpl hrun
end E2E
